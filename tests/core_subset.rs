//! The subset validator (`ikigai_shacl::core_shacl`, ledger #1176) on its own: what it refuses,
//! that it never recurses over either graph, and that its SPARQL runs behind the same guards as
//! the rudof path's. It runs in every build; `tests/differential.rs` holds it to rudof's
//! verdicts where both are compiled. The time-budget test is NOT here: it leaves an overdue
//! evaluation running that refuses every later validation in its process, so it lives in
//! `tests/time_budget.rs`, a process of its own (see there).
//!
//! ★ A bound refuses, it never truncates. Every refusal below is checked to be a typed
//! `InvalidArgument` on `shapes` (or `data`) that NAMES what it refused, so a shapes graph the
//! subset cannot apply in full is never reported as conforming.
//!
//! The depth probes run in a CHILD PROCESS (this test binary re-executed with the probe named in
//! its environment) on a 2 MiB thread, a tokio worker's stack, as `tests/sparql_stack.rs` does
//! for the rudof path: a stack overflow aborts a process and cannot be caught, so in-process it
//! would read as a crashed test runner rather than a failed assertion.

use std::process::Command;
use std::sync::Arc;

use futures::executor::block_on;
use ikigai_core::{ArgRef, Capability, Error, Iri, Kernel, Request, Verb};
use ikigai_shacl::core_shacl::{validate_report, validate_turtle};

const HEAD: &str = "@prefix sh: <http://www.w3.org/ns/shacl#> .\n\
                    @prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n\
                    @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .\n\
                    @prefix ex: <http://example.org/> .\n";

const DATA: &str = "@prefix ex: <http://example.org/> .\n\
                    ex:a a ex:Person ; ex:name \"Alice\" ; ex:knows ex:b .\n\
                    ex:b a ex:Person ; ex:name \"Bob\" .\n";

fn shapes(body: &str) -> String {
    format!("{HEAD}{body}")
}

/// The refusal for `body` (a shapes graph after the prefixes), which must name `needle`.
fn refused(body: &str, needle: &str) {
    match validate_report(DATA, &shapes(body)) {
        Err(Error::InvalidArgument { name, detail }) => {
            assert_eq!(name, "shapes", "{detail}");
            assert!(detail.contains(needle), "`{needle}` not named in: {detail}");
        }
        other => panic!("not refused (`{needle}`): {other:?}\n{body}"),
    }
}

#[test]
fn every_shacl_term_outside_the_subset_is_refused_by_name() {
    // Constraint components the subset does not implement: each would change a verdict.
    for (term, body) in [
        ("sh:or", "ex:S sh:targetClass ex:Person ; sh:or ( [ sh:class ex:A ] [ sh:class ex:B ] ) ."),
        ("sh:and", "ex:S sh:targetClass ex:Person ; sh:and ( [ sh:class ex:A ] ) ."),
        ("sh:not", "ex:S sh:targetClass ex:Person ; sh:not [ sh:class ex:A ] ."),
        ("sh:xone", "ex:S sh:targetClass ex:Person ; sh:xone ( [ sh:class ex:A ] ) ."),
        ("sh:equals", "ex:S sh:targetClass ex:Person ; sh:property [ sh:path ex:name ; sh:equals ex:label ] ."),
        ("sh:disjoint", "ex:S sh:targetClass ex:Person ; sh:property [ sh:path ex:name ; sh:disjoint ex:label ] ."),
        ("sh:lessThan", "ex:S sh:targetClass ex:Person ; sh:property [ sh:path ex:name ; sh:lessThan ex:label ] ."),
        ("sh:languageIn", "ex:S sh:targetClass ex:Person ; sh:property [ sh:path ex:name ; sh:languageIn ( \"en\" ) ] ."),
        ("sh:uniqueLang", "ex:S sh:targetClass ex:Person ; sh:property [ sh:path ex:name ; sh:uniqueLang true ] ."),
        ("sh:qualifiedValueShape", "ex:S sh:targetClass ex:Person ; sh:property [ sh:path ex:knows ; sh:qualifiedValueShape ex:T ; sh:qualifiedMinCount 1 ] ."),
        // Parameters that change how a result is counted or whether a shape applies at all.
        ("sh:severity", "ex:S sh:targetClass ex:Person ; sh:severity sh:Warning ; sh:class ex:A ."),
        ("sh:deactivated", "ex:S sh:targetClass ex:Person ; sh:deactivated true ; sh:class ex:A ."),
        // Targets the subset does not implement.
        ("sh:target", "ex:S sh:target [ sh:select \"SELECT ?this WHERE { ?this ?p ?o }\" ] ; sh:class ex:A ."),
        // SPARQL-based constraint components, and an ASK validator.
        ("sh:ask", "ex:S sh:targetClass ex:Person ; sh:sparql [ sh:ask \"ASK { FILTER(false) }\" ] ."),
        ("sh:ConstraintComponent", "ex:C a sh:ConstraintComponent .\nex:S sh:targetClass ex:Person ; sh:class ex:Person ."),
        ("sh:parameter", "ex:C sh:parameter [ sh:path ex:max ] .\nex:S sh:targetClass ex:Person ; sh:class ex:Person ."),
        // A class from the SHACL namespace, even with nothing else unknown.
        ("sh:SPARQLTarget", "ex:T a sh:SPARQLTarget .\nex:S sh:targetClass ex:Person ; sh:class ex:Person ."),
    ] {
        refused(body, &format!("`{term}`"));
    }
}

#[test]
fn a_complex_path_is_refused() {
    for path in [
        "[ sh:inversePath ex:knows ]",
        "( ex:knows ex:name )",
        "[ sh:zeroOrMorePath ex:knows ]",
        "[ sh:alternativePath ( ex:knows ex:name ) ]",
    ] {
        let body = format!(
            "ex:S sh:targetClass ex:Person ; sh:property [ sh:path {path} ; sh:minCount 1 ] ."
        );
        match validate_report(DATA, &shapes(&body)) {
            Err(Error::InvalidArgument { name, detail }) => {
                assert_eq!(name, "shapes");
                assert!(
                    detail.contains("complex property path") || detail.contains("Path`"),
                    "{path}: {detail}"
                );
            }
            other => panic!("{path} not refused: {other:?}"),
        }
    }
}

#[test]
fn a_recursive_shape_is_refused() {
    // The shape ledger #1326 found aborting rudof along a long chain, and a ring of two.
    refused(
        "ex:S sh:targetNode ex:a ; sh:property [ sh:path ex:knows ; sh:node ex:S ] .",
        "recursive shape",
    );
    refused(
        "ex:S sh:targetNode ex:a ; sh:node ex:T .\nex:T sh:node ex:S .",
        "recursive shape",
    );
    refused(
        "ex:S sh:targetNode ex:a ; sh:node ex:S .",
        "recursive shape",
    );
}

#[test]
fn malformed_parameters_are_refused() {
    for (body, needle) in [
        (
            "ex:S sh:targetClass ex:Person ; sh:in ( \"a\" \"b\" .",
            "parse error",
        ),
        (
            "ex:S sh:targetClass ex:Person ; sh:in ex:notAList .",
            "well-formed RDF list",
        ),
        (
            "ex:S sh:targetClass ex:Person ; sh:minCount 1 .",
            "property shape",
        ),
        (
            "ex:S sh:targetClass ex:Person ; sh:property [ sh:path ex:name ; sh:minCount -1 ] .",
            "non-negative",
        ),
        (
            "ex:S sh:targetClass ex:Person ; sh:property [ sh:path ex:name ; sh:minCount \"1\" ] .",
            "xsd:integer",
        ),
        (
            "ex:S sh:targetClass ex:Person ; sh:nodeKind sh:Thing .",
            "node kinds",
        ),
        (
            "ex:S sh:targetClass ex:Person ; sh:nodeKind \"IRI\" .",
            "node kinds",
        ),
        ("ex:S sh:targetClass \"Person\" .", "must be an IRI"),
        (
            "ex:S sh:targetClass ex:Person ; sh:class \"A\" .",
            "must be an IRI",
        ),
        (
            "ex:S sh:targetClass ex:Person ; sh:node \"T\" .",
            "must name a shape",
        ),
        (
            "ex:S sh:targetClass ex:Person ; sh:property [ sh:path ex:name , ex:label ] .",
            "more than one `sh:path`",
        ),
        (
            "ex:S sh:targetClass ex:Person ; sh:pattern \"a\" , \"b\" ; sh:flags \"i\" .",
            "sh:flags",
        ),
        (
            "ex:S sh:targetClass ex:Person ; sh:pattern \"a\" ; sh:flags \"z\" .",
            "XPath flags",
        ),
        (
            "ex:S sh:targetClass ex:Person ; sh:pattern \"(\" .",
            "does not compile",
        ),
    ] {
        match validate_report(DATA, &shapes(body)) {
            Err(Error::InvalidArgument { name, detail }) => {
                assert_eq!(name, "shapes", "{body}: {detail}");
                assert!(
                    detail.contains(needle),
                    "`{needle}` not in: {detail}\n{body}"
                );
            }
            Err(Error::Endpoint(detail)) if needle == "parse error" => {
                assert!(detail.contains(needle), "{detail}");
            }
            other => panic!("not refused (`{needle}`): {other:?}\n{body}"),
        }
    }
}

/// The malformed SHACL-SPARQL parameters, which only a build with `sparql` reads far enough to
/// find malformed (without it, `sh:sparql` itself is refused: `tests/core_only.rs`).
#[cfg(feature = "sparql")]
#[test]
fn malformed_sparql_parameters_are_refused() {
    for (body, needle) in [
        ("ex:S sh:targetClass ex:Person ; sh:sparql [ sh:message \"m\" ] .", "no `sh:select`"),
        ("ex:S sh:targetClass ex:Person ; sh:sparql [ sh:select \"ASK { }\" ] .", "SELECT query"),
        ("ex:S sh:targetClass ex:Person ; sh:sparql [ sh:select \"SELECT nonsense\" ] .", "does not parse"),
        (
            "ex:S sh:targetClass ex:Person ; sh:sparql [ sh:prefixes ex:d ; sh:select \"SELECT $this WHERE { }\" ] .\n\
             ex:d sh:declare [ sh:prefix \"p\" ; sh:namespace \"urn:a:\"^^xsd:anyURI ] , \
             [ sh:prefix \"p\" ; sh:namespace \"urn:b:\"^^xsd:anyURI ] .",
            "two namespaces",
        ),
        (
            "ex:S sh:targetClass ex:Person ; sh:sparql [ sh:prefixes ex:d ; sh:select \"SELECT $this WHERE { }\" ] .\n\
             ex:d sh:declare [ sh:prefix \"p\" ] .",
            "exactly one `sh:prefix` and one `sh:namespace`",
        ),
    ] {
        refused(body, needle);
    }
}

#[cfg(feature = "sparql")]
#[test]
fn a_service_anywhere_in_a_select_is_refused_and_nothing_is_sent() {
    for select in [
        "SELECT $this WHERE { SERVICE <http://127.0.0.1:9/sparql> { ?s ?p ?o } }",
        "SELECT $this WHERE { SERVICE SILENT <http://127.0.0.1:9/sparql> { ?s ?p ?o } }",
        "SELECT $this WHERE { { SELECT ?s WHERE { SERVICE <http://127.0.0.1:9/> { ?s ?p ?o } } } }",
        "SELECT $this WHERE { FILTER EXISTS { SERVICE <http://127.0.0.1:9/> { ?s ?p ?o } } }",
    ] {
        let body = format!(
            "ex:S sh:targetClass ex:Person ; sh:sparql [ sh:select \"\"\"{select}\"\"\" ] ."
        );
        refused(&body, "`SERVICE` is not available here");
    }
}

#[cfg(feature = "sparql")]
#[test]
fn caller_sparql_is_bounded_before_it_is_parsed() {
    // Nesting past `MAX_SPARQL_NESTING`, as at every store door.
    let deep = format!(
        "ex:S sh:targetClass ex:Person ; sh:sparql [ sh:select \"SELECT $this WHERE {{ FILTER({}false{}) }}\" ] .",
        "(".repeat(65),
        ")".repeat(65)
    );
    refused(&deep, "MAX_SPARQL_NESTING");
    // And the algebra, before oxigraph plans it.
    let join = (0..200)
        .map(|i| format!("?s{i} ?p{i} ?o{i} ."))
        .collect::<String>();
    let wide = format!(
        "ex:S sh:targetClass ex:Person ; sh:sparql [ sh:select \"SELECT $this WHERE {{ {join} }}\" ] ."
    );
    match validate_report(DATA, &shapes(&wide)) {
        Err(Error::InvalidArgument { name, .. }) => assert_eq!(name, "shapes"),
        other => panic!("a 200-operand join was not refused: {other:?}"),
    }
}

#[test]
fn rdf_lists_and_subclass_chains_are_walked_without_recursion() {
    // A 50,000-member `sh:in` and a 50,000-class `rdfs:subClassOf` chain in the data, both of
    // which a recursive walk would carry one frame per element.
    let members: String = (0..50_000).map(|i| format!("\"v{i}\" ")).collect();
    let body =
        format!("ex:S sh:targetClass ex:C0 ; sh:property [ sh:path ex:v ; sh:in ( {members}) ] .");
    let chain: String = (0..50_000)
        .map(|i| format!("ex:C{} rdfs:subClassOf ex:C{i} .\n", i + 1))
        .collect();
    let data = format!(
        "@prefix ex: <http://example.org/> .\n\
         @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .\n\
         ex:a a ex:C50000 ; ex:v \"v49999\" .\nex:b a ex:C2 ; ex:v \"w\" .\n{chain}"
    );
    let report = validate_report(&data, &shapes(&body)).unwrap();
    assert!(!report.conforms);
    assert_eq!(report.violations.len(), 1, "{report:?}");
    assert_eq!(report.violations[0].focus_node, "http://example.org/b");
}

#[test]
fn a_shape_message_resolves_its_template_on_both_faces() {
    let body = "ex:S sh:targetClass ex:Person ; sh:property [ sh:path ex:name ; \
                sh:datatype xsd:integer ; sh:message \"{?this} has name {$value} at {?path}\"@en ] .";
    let report = validate_report(DATA, &shapes(body)).unwrap();
    let messages: Vec<String> = report
        .violations
        .iter()
        .map(|v| serde_json::to_string(&v.message).unwrap())
        .collect();
    assert!(
        messages.iter().any(|m| m
            .contains("http://example.org/a has name Alice at http://example.org/name")
            && m.contains("\"xml:lang\":\"en\"")),
        "{messages:?}"
    );
    let turtle = validate_turtle(DATA, &shapes(body)).unwrap();
    assert!(
        turtle.contains("\"http://example.org/b has name Bob at http://example.org/name\"@en"),
        "{turtle}"
    );
    assert!(
        !turtle.contains("_:"),
        "no blank node in the report graph:\n{turtle}"
    );
}

#[test]
fn the_cheap_neighbors_work() {
    let body = "ex:S sh:targetNode ex:a , ex:zed ; sh:nodeKind sh:IRI .\n\
                ex:T sh:targetSubjectsOf ex:knows ; sh:property [ sh:path ex:name ; sh:minLength 6 ; sh:maxLength 9 ] .\n\
                ex:U sh:targetObjectsOf ex:knows ; sh:property [ sh:path ex:name ; sh:hasValue \"Robert\" ] .\n\
                ex:Person a rdfs:Class , sh:NodeShape ; sh:property [ sh:path ex:age ; sh:maxCount 0 ] .\n\
                ex:V sh:targetNode 7 , 12 ; sh:datatype xsd:integer ; sh:minExclusive 7 ; sh:maxInclusive 12 .";
    let data = format!("{DATA}ex:b ex:age 40 .\n");
    let report = validate_report(&data, &shapes(body)).unwrap();
    let mut got: Vec<(String, String)> = report
        .violations
        .iter()
        .map(|v| {
            (
                v.focus_node.clone(),
                v.component.rsplit('#').next().unwrap().to_string(),
            )
        })
        .collect();
    got.sort();
    let want = [
        (
            "\"7\"^^<http://www.w3.org/2001/XMLSchema#integer>",
            "MinExclusiveConstraintComponent",
        ),
        ("http://example.org/a", "MinLengthConstraintComponent"),
        ("http://example.org/b", "HasValueConstraintComponent"),
        ("http://example.org/b", "MaxCountConstraintComponent"),
    ];
    assert_eq!(
        got,
        want.iter()
            .map(|(a, b)| (a.to_string(), b.to_string()))
            .collect::<Vec<_>>()
    );
}

#[test]
fn ill_formed_literals_fail_their_datatype() {
    let body = "ex:S sh:targetSubjectsOf ex:v ; sh:property [ sh:path ex:v ; sh:datatype xsd:integer ] .\n\
                ex:B sh:targetSubjectsOf ex:b ; sh:property [ sh:path ex:b ; sh:datatype xsd:boolean ] .\n\
                ex:D sh:targetSubjectsOf ex:d ; sh:property [ sh:path ex:d ; sh:datatype xsd:dateTime ] .\n\
                ex:Y sh:targetSubjectsOf ex:y ; sh:property [ sh:path ex:y ; sh:datatype xsd:byte ] .";
    let data = "@prefix ex: <http://example.org/> .\n\
                @prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n\
                ex:ok ex:v 3 ; ex:b true ; ex:d \"2026-10-12T00:00:00Z\"^^xsd:dateTime ; ex:y \"-128\"^^xsd:byte .\n\
                ex:bad ex:v \"three\"^^xsd:integer ; ex:b \"yes\"^^xsd:boolean ; \
                ex:d \"yesterday\"^^xsd:dateTime ; ex:y \"128\"^^xsd:byte .";
    let report = validate_report(data, &shapes(body)).unwrap();
    assert_eq!(report.violations.len(), 4, "{report:?}");
    assert!(report
        .violations
        .iter()
        .all(|v| v.focus_node == "http://example.org/bad"));
}

// ---------------------------------------------------------------------------------- the kernel

fn issue(kernel: &Kernel, data: &str, shapes: &str, as_type: &str) -> ikigai_core::Result<String> {
    let req = Request::new(Verb::Source, Iri::parse("urn:shacl:validate").unwrap())
        .with_arg("data", ArgRef::Inline(data.as_bytes().to_vec()))
        .with_arg("shapes", ArgRef::Inline(shapes.as_bytes().to_vec()))
        .with_arg("as", ArgRef::Inline(as_type.as_bytes().to_vec()));
    block_on(kernel.issue(req, &Capability::root()))
        .map(|rep| String::from_utf8_lossy(&rep.bytes).into_owned())
}

#[test]
fn the_plan_shapes_validate_through_the_endpoint_in_this_build() {
    // Whichever validator this build serves `urn:shacl:validate` from, a plan door's request
    // (ikigai-cli's plan_space: the plan as `data`, ikigai_vocab::SHAPES inline, Turtle back)
    // answers with a report graph that says whether the plan conforms. The plan shapes carry
    // `sh:select` constraints, so a build without `sparql` refuses them, naming the feature.
    let kernel = Kernel::new(Arc::new(ikigai_shacl::space()));
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/plans");
    for (name, conforms) in [("ok-plan-linkcheck", true), ("bad-cli-two-feeds", false)] {
        let plan = std::fs::read_to_string(format!("{dir}/{name}.ttl")).unwrap();
        let report = issue(&kernel, &plan, ikigai_vocab::SHAPES, "text/turtle");
        if !cfg!(feature = "sparql") {
            let err = report.expect_err("a build without `sparql` answered the plan shapes");
            assert!(
                matches!(&err, Error::InvalidArgument { name, detail }
                    if name == "shapes" && detail.contains("`sparql` feature")),
                "{err:?}"
            );
            continue;
        }
        let report = report.unwrap();
        assert!(report.contains("sh:ValidationReport"), "{report}");
        assert!(
            report.contains(&format!("sh:conforms {conforms}")),
            "{name}: {report}"
        );
    }
}

// ---------------------------------------------------------------------- depth, in a child process

const PROBE: &str = "IKIGAI_SHACL_CORE_PROBE";

/// `(data, shapes)` for one probe, named so the child can rebuild it.
fn case(name: &str, n: usize) -> (String, String) {
    match name {
        // Ledger #1326's case: a shape that follows itself along `ex:next`, over a chain of `n`
        // links. rudof walked it one call per link and aborted at ~2,500; the subset refuses the
        // recursive shape, as a value, whatever the data.
        "data-chain" => (
            format!(
                "@prefix ex: <http://example.org/> .\n{}",
                (0..n)
                    .map(|i| format!("ex:n{i} ex:next ex:n{} .\n", i + 1))
                    .collect::<String>()
            ),
            shapes("ex:S a sh:NodeShape ; sh:targetNode ex:n0 ;\n  sh:property [ sh:path ex:next ; sh:node ex:S ] .\n"),
        ),
        // The same depth with no recursive shape: `n` shapes, each following `ex:next` into the
        // next, over a chain of `n` links. Every level is a nested validation, and the subset
        // validates it to the end; a recursive walk would carry one frame (and more) per level.
        // (rudof refuses it at MAX_SHAPE_DEPTH, 64; before that bound, 300 nested shapes
        // aborted it, ledger #992.)
        "shape-chain" => (
            format!(
                "@prefix ex: <http://example.org/> .\n{}ex:n{n} ex:last true .\n",
                (0..n)
                    .map(|i| format!("ex:n{i} ex:next ex:n{} .\n", i + 1))
                    .collect::<String>()
            ),
            shapes(&format!(
                "ex:S0 sh:targetNode ex:n0 .\n{}ex:S{n} sh:property [ sh:path ex:last ; sh:minCount 1 ] .\n",
                (0..n)
                    .map(|i| format!(
                        "ex:S{i} sh:property [ sh:path ex:next ; sh:minCount 1 ; sh:node ex:S{} ] .\n",
                        i + 1
                    ))
                    .collect::<String>()
            )),
        ),
        // Property shapes nested in property shapes, `n` deep, over a chain one link longer: the
        // walk that finds value nodes goes `n + 1` levels into the data.
        "property-nest" => (
            format!(
                "@prefix ex: <http://example.org/> .\n{}",
                (0..=n)
                    .map(|i| format!("ex:n{i} ex:next ex:n{} .\n", i + 1))
                    .collect::<String>()
            ),
            shapes(&format!(
                "ex:S sh:targetNode ex:n0 ; sh:property {}[ sh:path ex:next ; sh:nodeKind sh:Literal ]{} .\n",
                "[ sh:path ex:next ; sh:property ".repeat(n),
                " ]".repeat(n)
            )),
        ),
        other => panic!("no probe named {other}"),
    }
}

/// The child's half: inert unless a parent named a probe. Runs it on a 2 MiB thread through the
/// subset validator, prints the outcome and exits before the harness can.
#[test]
fn probe_child() {
    let Ok(spec) = std::env::var(PROBE) else {
        return;
    };
    let (name, n) = spec.split_once(':').unwrap();
    let (data, shapes) = case(name, n.parse().unwrap());
    let outcome = std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(move || match validate_report(&data, &shapes) {
            Ok(report) => format!(
                "ok conforms={} violations={}",
                report.conforms,
                report.violations.len()
            ),
            Err(e) => format!("err {}", e.to_string().replace('\n', " ")),
        })
        .unwrap()
        .join()
        .unwrap();
    println!("\nOUTCOME {outcome}");
    std::process::exit(0);
}

/// Run one probe in a child; an abort is the defect.
fn probe(name: &str, n: usize) -> String {
    let out = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "probe_child", "--nocapture", "--test-threads=1"])
        .env(PROBE, format!("{name}:{n}"))
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "the `{name}` probe at {n} did not survive a 2 MiB thread: {} — {}",
        out.status,
        stderr
            .lines()
            .find(|l| l.contains("overflow"))
            .unwrap_or(&stderr)
    );
    let at = stdout
        .find("\nOUTCOME ")
        .unwrap_or_else(|| panic!("the `{name}` probe reported nothing: {stdout}"));
    stdout[at + "\nOUTCOME ".len()..]
        .lines()
        .next()
        .unwrap_or("")
        .to_string()
}

#[test]
fn a_recursive_shape_over_a_long_chain_is_refused_not_aborted() {
    // 30,000 links: ledger #1118's tenfold row, which aborted rudof in 0.3.3.
    let outcome = probe("data-chain", 30_000);
    assert!(
        outcome.starts_with("err ") && outcome.contains("recursive shape"),
        "{outcome}"
    );
}

#[test]
fn deep_nesting_validates_on_a_2_mib_thread() {
    // 20,000 nested validations each, along a 20,000-link chain. The last node of `shape-chain`
    // has its `ex:last`, so it conforms; break the chain's end and it reports one result.
    let outcome = probe("shape-chain", 20_000);
    assert_eq!(outcome, "ok conforms=true violations=0");
    let outcome = probe("property-nest", 20_000);
    // The innermost property shape requires a literal where the chain has an IRI.
    assert_eq!(outcome, "ok conforms=false violations=1");
}
