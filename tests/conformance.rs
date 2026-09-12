//! The module recipe as one test: `ikigai-conformance` walks `urn:shacl:validate`
//! and reports every violation of the recipe at once.
//!
//! ## Why this module needs two walks
//!
//! `shapes` is a union — inline Turtle, or a resource IRI sourced through the
//! kernel — and the two shapes give the endpoint two different *cacheability*
//! truths from one body of code (conformance PENDING #18/#30/#47/#109):
//!
//! - **Inline** ([`inline`]): validation is a pure function of two by-value
//!   documents. Nothing is read but the arguments, so the result rightly carries
//!   an empty golden-thread set. Declared `pure` + `cacheable`.
//! - **By reference** ([`referenced`]): `inv.source` folds the shapes resource's
//!   expiry and threads into the result, so the report is exactly as cacheable as
//!   the shapes graph and never more — a cut of the shapes' thread recomputes it.
//!   Declared `cacheable` only; declaring it `pure` there would be a lie, and
//!   [`the_two_shapes_forms_have_two_different_thread_sets`] pins the difference
//!   the declarations are making.
//!
//! ## Fixtures, and why they are not optional here
//!
//! The suite's minimal sample for an `xsd:string` input is `x`, which is neither a
//! Turtle document nor a SHACL shapes graph, so without a [`Fixture`] every
//! invoking check reports "did not resolve with the minimal inputs" (PENDING #33).
//! The fixture data graph is deliberately **non-conforming**: a conforming run
//! emits a two-triple report with no `sh:ValidationResult` at all, and SKOLEM-RDF
//! and VOCABULARY would pass over a graph carrying none of the structure that can
//! break them (PENDING #26/#142).
//!
//! ## What the suite cannot see, pinned by hand below
//!
//! - **Declared outputs vs served media types**, both directions, driven from
//!   `as`'s `one_of` — 0.1.0 has no OUTPUTS check, and the RDF checks only probe a
//!   face once it is DECLARED, so `application/json` was served under `as=` and
//!   undeclared for this crate's whole life (PENDING #11/#31/#79/#85).
//! - **The skolem scheme itself**: that the report graph names every node under a
//!   content address of the report, that the naming is deterministic, and that two
//!   different reports never collide.
//!
//! No opt-outs. No module namespace: the report graph is `sh:` and `rdf:`, both
//! well-known, so this module invents no term and needs nothing from the
//! vocabulary. NAMES runs — `shacl-validate` is already kebab-case.

use std::sync::Arc;

use ikigai_conformance::{rdf, Fixture, Suite};
use ikigai_core::{
    ArgRef, ArgSpec, Capability, Description, Exact, FnEndpoint, Iri, Kernel, ReprType,
    Representation, Request, Verb,
};

/// The one description this module binds.
const ID: &str = "shacl-validate";
const IRI: &str = "urn:shacl:validate";

/// The IRI the fixture serves a shapes graph at, and the golden thread it declares —
/// the thread a host would cut when the shapes file changes.
const SHAPES_IRI: &str = "urn:data:conformance-shapes";
const SHAPES_THREAD: &str = "urn:file:conformance-shapes.ttl";
/// The fixture shapes endpoint's own description id (it is walked too: PENDING #17).
const SHAPES_ID: &str = "conformance-shapes";

const TURTLE: &str = "text/turtle";
const JSON: &str = "application/json";

/// A shapes graph that produces a violation with a `sh:value`, a `sh:resultPath`
/// and a blank-node `sh:sourceShape` — one of each thing the skolemizer has to
/// name.
const SHAPES: &str = r#"@prefix sh: <http://www.w3.org/ns/shacl#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix : <http://example.org/> .
:PersonShape a sh:NodeShape ;
  sh:targetClass :Person ;
  sh:property [ sh:path :name ; sh:minCount 1 ; sh:datatype xsd:string ;
                sh:message "{?value} is not a string" ] ."#;

/// The same shapes with the property shape NAMED, for the fixture endpoint to
/// serve. The suite walks a fixture endpoint as a module endpoint (PENDING #17), so
/// its declared `text/turtle` face is held to SKOLEM-RDF too — and [`SHAPES`]'s
/// `sh:property [ … ]` is a blank node. Inline it is an argument and nobody checks
/// it; served it is a face, and a face has no blank nodes.
const NAMED_SHAPES: &str = r#"@prefix sh: <http://www.w3.org/ns/shacl#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix : <http://example.org/> .
:PersonShape a sh:NodeShape ;
  sh:targetClass :Person ;
  sh:property :NameShape .
:NameShape a sh:PropertyShape ;
  sh:path :name ; sh:minCount 1 ; sh:datatype xsd:string ;
  sh:message "{?value} is not a string" ."#;

/// Deliberately non-conforming, so the report graph carries results (PENDING #26).
const DATA: &str = r#"@prefix : <http://example.org/> .
:carol a :Person ; :name 42 .
:bob a :Person ."#;

/// A second data graph with a different violation — for the collision half of
/// [`the_report_graph_is_skolemized_under_a_content_address`].
const OTHER_DATA: &str = r#"@prefix : <http://example.org/> .
:dave a :Person ; :name 7 ."#;

/// The kernel for the inline walk: this module's space and nothing else.
fn inline_kernel() -> Kernel {
    Kernel::new(Arc::new(ikigai_shacl::space()))
}

/// The kernel for the by-reference walk: the module's space plus one endpoint
/// serving [`NAMED_SHAPES`] at [`SHAPES_IRI`], cacheable under [`SHAPES_THREAD`]. It is
/// itself walked by the suite, so it declares a kebab id, one verb, no untyped
/// input, and a thread.
fn referenced_kernel() -> Kernel {
    let shapes = FnEndpoint::new(SHAPES_ID, |_| {
        Ok(
            Representation::new(ReprType::new(TURTLE), NAMED_SHAPES.as_bytes().to_vec())
                .cacheable()
                .depends_on(SHAPES_THREAD),
        )
    })
    .with_description(
        Description::new(SHAPES_ID)
            .title("Conformance shapes")
            .summary("the SHACL shapes graph the by-reference walk validates against")
            .verb(Verb::Source)
            .verb(Verb::Meta)
            .output("text/turtle"),
    );
    Kernel::new(Arc::new(
        ikigai_shacl::space().bind(Exact::new(SHAPES_IRI), shapes),
    ))
}

/// The fixture every walk uses, with `shapes` supplied by the caller.
fn fixture(shapes: &str) -> Fixture {
    Fixture::new(ID, Verb::Source)
        .arg("data", DATA)
        .arg("shapes", shapes)
}

/// Inline shapes: a pure function of two by-value documents.
#[test]
fn inline() {
    let report = Suite::new()
        .fixture(fixture(SHAPES))
        .pure(ID)
        .cacheable(ID)
        .run_blocking(&inline_kernel());
    eprintln!("== inline shapes ==\n{report}");
    assert!(report.is_clean(), "{report}");
    assert_eq!(report.endpoints, 1, "one endpoint: {report}");
    assert_eq!(report.actions, 1, "one Source action: {report}");
    assert_eq!(
        report.checks.skipped().count(),
        0,
        "every check runs: {report}"
    );
}

/// Shapes by reference: as cacheable as the shapes resource, and no more. Not
/// `pure` — the report is a function of a resource that can change under it.
#[test]
fn referenced() {
    let report = Suite::new()
        .fixture(fixture(SHAPES_IRI))
        .cacheable(ID)
        .cacheable(SHAPES_ID)
        .run_blocking(&referenced_kernel());
    eprintln!("== shapes by reference ==\n{report}");
    assert!(report.is_clean(), "{report}");
    assert_eq!(
        report.endpoints, 2,
        "this module's endpoint and the fixture's: {report}"
    );
    assert_eq!(report.actions, 2, "one Source action each: {report}");
    assert_eq!(
        report.checks.skipped().count(),
        0,
        "every check runs: {report}"
    );
}

/// The declarations above are a claim about golden threads; this is the claim.
/// Inline, the report depends on nothing. By reference, it inherits the shapes
/// resource's thread — so cutting it recomputes the report, which is the whole
/// reason a shapes graph is taken by reference.
#[test]
fn the_two_shapes_forms_have_two_different_thread_sets() {
    let inline = resolve(
        &inline_kernel(),
        source(&[("data", DATA), ("shapes", SHAPES)]),
    );
    assert!(
        inline.threads().is_empty(),
        "inline shapes read nothing: {:?}",
        inline.threads()
    );

    let kernel = referenced_kernel();
    let request = source(&[("data", DATA), ("shapes", SHAPES_IRI)]);
    let referenced = resolve(&kernel, request.clone());
    let threads: Vec<&str> = referenced.threads().iter().map(|t| t.as_str()).collect();
    assert_eq!(
        threads,
        [SHAPES_THREAD],
        "the report inherits the shapes resource's thread"
    );

    // And the thread is live: the kernel serves the report from cache until it is cut.
    assert!(
        kernel.is_cached(&request, &Capability::root()),
        "the report is cached"
    );
    kernel.cut(SHAPES_THREAD);
    assert!(
        !kernel.is_cached(&request, &Capability::root()),
        "cutting the shapes thread invalidates the report"
    );
}

/// Every media type `as` accepts is a declared output, every declared output is
/// reachable through `as`, and each one is what the resolution actually serves —
/// including the default with `as` omitted. The suite has no OUTPUTS check at
/// 0.1.0, and an undeclared face is a face its RDF checks never see.
#[test]
fn declared_outputs_are_the_media_types_served() {
    let kernel = inline_kernel();
    let description = kernel
        .describe(&Iri::parse(IRI).expect("a valid IRI"))
        .expect("urn:shacl:validate describes itself");
    let spec = description
        .action_specs()
        .into_iter()
        .find(|a| a.verb == Verb::Source)
        .expect("Source is declared");

    let declared: Vec<String> = spec
        .outputs
        .iter()
        .map(|o| rdf::bare_media_type(o))
        .collect();
    let faces: Vec<String> = spec
        .inputs
        .iter()
        .find(|i| i.name == "as")
        .expect("`as` is declared")
        .one_of
        .clone();
    assert_eq!(faces, declared, "`as` lists exactly the declared outputs");
    assert_eq!(faces, [TURTLE, JSON], "and both faces are the ones served");

    let default = resolve(&kernel, source(&[("data", DATA), ("shapes", SHAPES)]));
    assert_eq!(
        rdf::bare_media_type(&default.repr_type.media_type),
        TURTLE,
        "the report graph is the default face"
    );
    for face in &faces {
        let served = resolve(
            &kernel,
            source(&[("data", DATA), ("shapes", SHAPES), ("as", face)]),
        );
        assert_eq!(
            rdf::bare_media_type(&served.repr_type.media_type),
            *face,
            "as={face}"
        );
    }
}

/// The skolem contract, which SKOLEM-RDF can only half-see: it proves there is no
/// blank node, not that what replaced one is stable or unique. Every node is named
/// under `urn:ikigai:shacl:report:<content id>:`, the same report mints the same
/// names twice, and a different report mints different ones.
#[test]
fn the_report_graph_is_skolemized_under_a_content_address() {
    let kernel = inline_kernel();
    let turtle = |data: &str| {
        String::from_utf8(
            resolve(&kernel, source(&[("data", data), ("shapes", SHAPES)]))
                .bytes
                .clone(),
        )
        .expect("the report face is UTF-8")
    };

    let report = turtle(DATA);
    assert!(
        !report.contains("_:"),
        "no blank node survives skolemization:\n{report}"
    );
    let scheme = scheme_of(&report);
    assert!(
        scheme.starts_with("urn:ikigai:shacl:report:b3:"),
        "the scheme is a content address: {scheme}"
    );

    // Deterministic: the same data and shapes name the same nodes.
    assert_eq!(scheme, scheme_of(&turtle(DATA)), "same report, same names");
    // And distinct: a different report can never reuse another's node IRIs.
    assert_ne!(
        scheme,
        scheme_of(&turtle(OTHER_DATA)),
        "a different report is a different content address"
    );

    // The nodes the report is made of are all under it, including the one the
    // shapes graph contributed (a blank-node `sh:sourceShape`).
    for needle in [
        "a sh:ValidationReport",
        "a sh:ValidationResult",
        "sh:sourceShape",
    ] {
        assert!(report.contains(needle), "missing `{needle}`:\n{report}");
    }
    assert_eq!(
        report.matches(&scheme).count(),
        report.matches("urn:ikigai:shacl").count(),
        "every minted IRI is under the one scheme:\n{report}"
    );
}

// --- helpers ---------------------------------------------------------------

fn source(args: &[(&str, &str)]) -> Request {
    args.iter().fold(
        Request::new(Verb::Source, Iri::parse(IRI).expect("a valid IRI")),
        |request, (name, value)| request.with_arg(*name, ArgRef::Inline(value.as_bytes().to_vec())),
    )
}

fn resolve(kernel: &Kernel, request: Request) -> Representation {
    futures::executor::block_on(kernel.issue(request, &Capability::root()))
        .expect("urn:shacl:validate resolves")
}

/// The skolem scheme a report graph was minted under: the common
/// `urn:ikigai:shacl:report:<content id>:` prefix of its node IRIs.
fn scheme_of(turtle: &str) -> String {
    let start = turtle
        .find("urn:ikigai:shacl:report:")
        .unwrap_or_else(|| panic!("no skolem IRI in:\n{turtle}"));
    let rest = &turtle[start..];
    let end = rest
        .find(['>', ' ', '\n'])
        .unwrap_or_else(|| panic!("unterminated IRI in:\n{turtle}"));
    let iri = &rest[..end];
    // Everything up to and including the separator after the content id.
    let label = iri.rfind(':').expect("a label follows the content id");
    iri[..=label].to_string()
}

/// A `Fixture` whose id matches no description is silently inert (PENDING #57),
/// and this crate's `name()` and description id happen to agree — so the trap is
/// one rename away. Pin it.
#[test]
fn the_fixture_id_is_the_description_id() {
    let description = inline_kernel()
        .describe(&Iri::parse(IRI).expect("a valid IRI"))
        .expect("urn:shacl:validate describes itself");
    assert_eq!(description.id, ID, "the fixture keys on the description id");
    // And the inputs the fixture sets are the ones the manifold declares.
    let declared: Vec<&str> = description.inputs.iter().map(|i| i.name.as_str()).collect();
    assert_eq!(declared, ["data", "shapes", "as"]);
    assert!(
        description
            .inputs
            .iter()
            .all(|i| !i.class.as_deref().unwrap_or("").is_empty()),
        "every input carries a class: {:?}",
        description.inputs
    );
    // `as` is the only optional one, and its default is one of its values.
    let as_spec: &ArgSpec = description
        .inputs
        .iter()
        .find(|i| i.name == "as")
        .expect("`as` is declared");
    assert!(!as_spec.required, "`as` defaults to the report graph");
    assert_eq!(as_spec.default.as_deref(), Some(TURTLE));
}
