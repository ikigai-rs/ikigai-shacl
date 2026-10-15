//! `ikigai-shacl` — SHACL validation as an ikigai resource.
//!
//! `urn:shacl:validate` validates a piped RDF `data` graph against a SHACL `shapes` graph. The
//! validation **report is itself an RDF graph**: the default `text/turtle` output is the SHACL
//! ValidationReport (conforms + a node per violation), skolemized under a content address of the
//! report so it carries no blank node (every one is named under [`REPORT_SCHEME`]), and
//! `application/json` gives a structured
//! [`Report`] — `{conforms, violations: [{focus_node, path, component, message, value}]}` —
//! content-negotiated structured errors for free. Both faces carry the same facts: the
//! `sh:resultMessage` with its `{?value}`-style template resolved, the offending `sh:value`,
//! and the `sh:resultPath`.
//!
//! `shapes` is taken **by reference** (the ROC-idiomatic form: a shapes graph is a resource
//! you point at, sourced through the kernel — cacheable, golden-threaded); inline Turtle is
//! also accepted. So the endpoint is `async` (the one await is the shapes resolution).
//!
//! ## Two validators, one resource (ledger #1176)
//!
//! - **`rudof`** (the default feature): rudof's consolidated `shacl` crate, all of SHACL Core
//!   and SHACL-SPARQL's `sh:select`, behind the bounds in `rudof_engine`. A heavy dependency
//!   tree, and one that cannot be built without a network stack on native (rudof's IRI crate
//!   links reqwest, and its RDF crate turns on oxigraph's `http-client`).
//! - **[`core_shacl`]**, always compiled: a subset validator with no rudof, no network stack and
//!   no recursion over either graph, for a host that turns `rudof` off. It covers what
//!   `ikigai_vocab::SHAPES` uses and a few cheap neighbors, and REFUSES, by name, every SHACL
//!   term outside that subset rather than skip a constraint it does not understand.
//!
//! With both compiled the endpoint uses rudof; `tests/differential.rs` runs both over one corpus
//! and requires the same verdicts. The `module` feature (a lazy-loadable WASM module) implies
//! `rudof`. The JavaScript `shacl-engine` remains a third implementation of the same
//! `urn:shacl:validate` resource, held to the parity corpus (see `js-parity/`).

#![forbid(unsafe_code)]

use async_trait::async_trait;
use ikigai_core::{
    space_iri, ArgRef, ArgSpec, Description, Endpoint, EndpointSpace, Error, Exact, Invocation,
    Iri, ReprType, Representation, Request, Result, Verb,
};

pub mod core_shacl;
mod depth;
#[cfg(feature = "rudof")]
mod rudof_engine;
pub use depth::{MAX_DATA_RECURSION, MAX_SHAPE_DEPTH, MAX_TURTLE_NESTING};

/// The name [`space`] claims: `urn:iki:space:shacl`.
pub const SPACE_ID: &str = "urn:iki:space:shacl";

/// The space binding `urn:shacl:validate`. It is configuration-free (no parameters, nothing
/// read while building it), so it names itself [`SPACE_ID`]; the name goes on LAST, because
/// binding a door after naming drops the name (core 0.1.89).
pub fn space() -> EndpointSpace {
    EndpointSpace::new()
        .bind(Exact::new("urn:shacl:validate"), ValidateEndpoint)
        .named(space_iri("shacl"))
}

/// The argument every refusal names: the SPARQL arrived inside the shapes graph.
pub(crate) const SHAPES_ARG: &str = "shapes";

/// Is `s` an inline Turtle shapes graph rather than a resource reference? Turtle opens with
/// `@prefix`/`@base`, a `<…>` IRI, a `_:` blank node, or a `#` comment — or spans lines; a
/// bare `urn:`/`http(s)` IRI with no whitespace is the by-reference case.
fn is_inline_shapes(s: &str) -> bool {
    let t = s.trim_start();
    t.starts_with('@')
        || t.starts_with('<')
        || t.starts_with('#')
        || t.starts_with("_:")
        || t.chars().any(char::is_whitespace)
}

/// Resolve a `shapes` reference through the kernel — `urn:`/`file:` via `inv.source`, http(s)
/// via `urn:httpGet` — recording it as a dependency so a result is cacheable and invalidates
/// when the shapes change. (Mirrors the jsonld compact context-by-reference.)
async fn resolve_shapes(inv: &Invocation<'_>, uri: &str) -> Result<Representation> {
    if uri.starts_with("http://") || uri.starts_with("https://") {
        let get = Iri::parse("urn:httpGet").expect("urn:httpGet is a valid IRI");
        let request = Request::new(Verb::Source, get)
            .with_arg("url", ArgRef::Inline(uri.as_bytes().to_vec()));
        inv.issue(request).await
    } else {
        let iri = Iri::parse(uri).map_err(|e| {
            Error::Endpoint(format!("urn:shacl:validate: bad shapes IRI `{uri}`: {e}"))
        })?;
        inv.source(&iri).await
    }
}

/// One conformance violation, reduced to its **implementation-independent signature** — the
/// spec-defined parts every SHACL validator agrees on. (Deliberately omits `sh:resultMessage`
/// and blank-node ids, which legitimately differ between validators.) This is the cross-impl
/// **parity contract**: rudof (native) and shacl-engine (browser) must produce the same set.
/// The endpoint's JSON face is the richer [`ReportResult`]; a signature is its first three
/// keys.
#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct Violation {
    /// The focus node that failed (IRI / blank-node id).
    pub focus_node: String,
    /// The `sh:resultPath`, if any, rendered as [`ReportResult::path`] says: an IRI only for a
    /// predicate path, and otherwise a path expression that is not an IRI.
    pub path: Option<String>,
    /// The `sh:sourceConstraintComponent` IRI (e.g. `…#MinCountConstraintComponent`).
    pub component: String,
}

/// The portable validation outcome: `conforms` + the sorted violation signatures. This is
/// the parity contract in `tests/corpus/*/expected.json` (see `tests/parity.rs`); the
/// endpoint's `application/json` face is the richer [`Report`].
#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, Clone, Debug)]
pub struct ValidationOutcome {
    pub conforms: bool,
    pub violations: Vec<Violation>,
}

/// An RDF term in the SPARQL 1.1 Query Results JSON encoding — `{"type": "uri" | "bnode" |
/// "literal", "value": …}`, a literal carrying `"xml:lang"` when language-tagged and
/// `"datatype"` when typed (a plain `xsd:string` carries neither, as in that spec). An
/// RDF-star quoted triple is `{"type": "triple", "value": {subject, predicate, object}}`
/// (the SPARQL 1.2 form).
#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
#[serde(tag = "type", rename_all = "lowercase")]
pub enum Term {
    Uri {
        value: String,
    },
    Bnode {
        value: String,
    },
    Literal {
        value: String,
        #[serde(rename = "xml:lang", default, skip_serializing_if = "Option::is_none")]
        lang: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        datatype: Option<String>,
    },
    Triple {
        value: Box<QuotedTriple>,
    },
}

/// The value of a [`Term::Triple`]: an RDF-star quoted triple.
#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct QuotedTriple {
    pub subject: Term,
    pub predicate: Term,
    pub object: Term,
}

impl Term {
    /// The string a SHACL message template substitutes for this term (spec §5.3.2 / §6.5.3
    /// semantics): an IRI as itself, a literal as its lexical form, a blank node as `_:id`.
    pub fn lexical(&self) -> String {
        match self {
            Term::Uri { value } | Term::Literal { value, .. } => value.clone(),
            Term::Bnode { value } => format!("_:{value}"),
            Term::Triple { value } => format!(
                "<< {} {} {} >>",
                value.subject.lexical(),
                value.predicate.lexical(),
                value.object.lexical()
            ),
        }
    }
}

pub(crate) const XSD_STRING: &str = "http://www.w3.org/2001/XMLSchema#string";

/// The two faces of the report, which are also the two values `as` accepts and the
/// two declared outputs — one list, so `as`'s `one_of` and `outputs` cannot drift.
pub(crate) const TURTLE: &str = "text/turtle";
pub(crate) const JSON: &str = "application/json";

/// One validation result as the `application/json` face reports it. The first three keys are
/// the parity [`Violation`] signature and keep their names and order; `message` and `value`
/// follow. Sorted by these fields in this order, so a report is deterministic.
#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct ReportResult {
    /// The focus node that failed (IRI / blank-node id).
    pub focus_node: String,
    /// The `sh:resultPath`, if the result has one, as a string. A constraint on a **node**
    /// shape has none unless it binds `?path` itself — a `sh:sparql` on a node shape reports
    /// `null` here by the SHACL spec, not by omission.
    ///
    /// **It is an IRI only when the path is a single predicate** (ledger #204):
    ///
    /// - A predicate path is its IRI, bare: `http://example.org/name`.
    /// - Any other path is rudof's rendering of the path expression, which is **not an IRI**
    ///   and not SPARQL either, since its IRIs are unbracketed: every compound is in
    ///   parentheses, an alternative `(a | b)`, a sequence `(a / b)`, an inverse `^(a)`, and
    ///   `(a)*`, `(a)+`, `(a)?` for zero-or-more, one-or-more and zero-or-one, nesting as the
    ///   path does. A predicate IRI never begins with `(` or `^`, so that tells the two apart.
    /// - With the `rudof` feature off, the subset validator refuses a shapes graph whose path
    ///   is not a predicate, so it only ever reports the first form.
    ///
    /// The parity case `tests/corpus/complex-paths` holds shacl-engine to the same strings, and
    /// this pins both forms, so a rudof release that renders a path differently fails here:
    ///
    /// ```
    /// let shapes = r#"@prefix sh: <http://www.w3.org/ns/shacl#> .
    /// @prefix : <http://example.org/> .
    /// :S a sh:NodeShape ; sh:targetNode :dave ;
    ///   sh:property [ sh:path :name ; sh:minCount 1 ] ;
    ///   sh:property [ sh:path [ sh:alternativePath ( :email :phone ) ] ; sh:minCount 1 ] ;
    ///   sh:property [ sh:path ( :employer :name ) ; sh:minCount 1 ] ;
    ///   sh:property [ sh:path [ sh:inversePath :member ] ; sh:minCount 1 ] ."#;
    ///
    /// let report = ikigai_shacl::validate_report("", shapes);
    /// if cfg!(feature = "rudof") {
    ///     let paths: Vec<String> = report
    ///         .unwrap()
    ///         .violations
    ///         .into_iter()
    ///         .map(|v| v.path.unwrap())
    ///         .collect();
    ///     assert_eq!(
    ///         paths,
    ///         [
    ///             "(http://example.org/email | http://example.org/phone)",
    ///             "(http://example.org/employer / http://example.org/name)",
    ///             "^(http://example.org/member)",
    ///             "http://example.org/name",
    ///         ]
    ///     );
    /// } else {
    ///     assert!(report.is_err(), "the subset refuses a complex path");
    /// }
    /// ```
    pub path: Option<String>,
    /// The `sh:sourceConstraintComponent` IRI (e.g. `…#MinCountConstraintComponent`).
    pub component: String,
    /// The `sh:resultMessage`, with `{?value}`/`{$value}`, `{?this}` and `{?path}` resolved
    /// against this result (SHACL §6.5.3 semantics). Language-tagged when the shape's
    /// `sh:message` is. The shape's own message beats the validator's default, which is
    /// never tagged; among several tagged messages the lowest language tag is reported.
    pub message: Option<Term>,
    /// The `sh:value` — the offending value node — as a term.
    pub value: Option<Term>,
}

impl ReportResult {
    /// The parity signature: this result minus what legitimately differs between validators.
    pub fn signature(&self) -> Violation {
        Violation {
            focus_node: self.focus_node.clone(),
            path: self.path.clone(),
            component: self.component.clone(),
        }
    }
}

/// The `application/json` face of `urn:shacl:validate`: `conforms` + one [`ReportResult`]
/// per `sh:result`, sorted. The exact shape, pinned — this is what a consumer parses:
///
/// ```
/// let shapes = r#"@prefix sh: <http://www.w3.org/ns/shacl#> .
/// @prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
/// @prefix : <http://example.org/> .
/// :PersonShape a sh:NodeShape ;
///   sh:targetClass :Person ;
///   sh:property [ sh:path :name ; sh:datatype xsd:string ;
///                 sh:message "{?value} is not a string"@en ] ."#;
/// let data = r#"@prefix : <http://example.org/> .
/// :carol a :Person ; :name 42 ."#;
///
/// let report = ikigai_shacl::validate_report(data, shapes).unwrap();
/// assert_eq!(
///     serde_json::to_string_pretty(&report).unwrap(),
///     r#"{
///   "conforms": false,
///   "violations": [
///     {
///       "focus_node": "http://example.org/carol",
///       "path": "http://example.org/name",
///       "component": "http://www.w3.org/ns/shacl#DatatypeConstraintComponent",
///       "message": {
///         "type": "literal",
///         "value": "42 is not a string",
///         "xml:lang": "en"
///       },
///       "value": {
///         "type": "literal",
///         "value": "42",
///         "datatype": "http://www.w3.org/2001/XMLSchema#integer"
///       }
///     }
///   ]
/// }"#
/// );
/// ```
#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, Clone, Debug)]
pub struct Report {
    pub conforms: bool,
    pub violations: Vec<ReportResult>,
}

impl Report {
    /// Reduce to the parity [`ValidationOutcome`] (sorted signatures).
    pub fn outcome(&self) -> ValidationOutcome {
        let mut violations: Vec<Violation> = self
            .violations
            .iter()
            .map(ReportResult::signature)
            .collect();
        violations.sort();
        ValidationOutcome {
            conforms: self.conforms,
            violations,
        }
    }
}

/// Validate `data_ttl` against `shapes_ttl`, returning the full [`Report`] — what the
/// `application/json` face serializes. rudof with the `rudof` feature, else [`core_shacl`].
pub fn validate_report(data_ttl: &str, shapes_ttl: &str) -> Result<Report> {
    #[cfg(feature = "rudof")]
    {
        rudof_engine::validate_report(data_ttl, shapes_ttl)
    }
    #[cfg(not(feature = "rudof"))]
    {
        core_shacl::validate_report(data_ttl, shapes_ttl)
    }
}

/// Validate `data_ttl` against `shapes_ttl`, returning the portable [`ValidationOutcome`] —
/// the parity contract.
pub fn validate_outcome(data_ttl: &str, shapes_ttl: &str) -> Result<ValidationOutcome> {
    Ok(validate_report(data_ttl, shapes_ttl)?.outcome())
}

/// Validate `data_ttl` against `shapes_ttl`, returning the report graph as Turtle — what the
/// default `text/turtle` face serves. rudof with the `rudof` feature, else [`core_shacl`].
pub fn validate_turtle(data_ttl: &str, shapes_ttl: &str) -> Result<String> {
    #[cfg(feature = "rudof")]
    {
        rudof_engine::validate_turtle(data_ttl, shapes_ttl)
    }
    #[cfg(not(feature = "rudof"))]
    {
        core_shacl::validate_turtle(data_ttl, shapes_ttl)
    }
}

/// Validate, rendering per `as_type`: `application/json` → the [`Report`]; else the SHACL
/// report graph as Turtle (the report *is* RDF). Same results, same resolved messages, on
/// both faces. `capability` is the caller's, which decides the time budget the subset
/// validator's SPARQL runs under.
fn validate(
    data_ttl: &str,
    shapes_ttl: &str,
    as_type: &str,
    capability: &ikigai_core::Capability,
) -> Result<Representation> {
    #[cfg(feature = "rudof")]
    {
        let _ = capability;
        rudof_engine::validate(data_ttl, shapes_ttl, as_type)
    }
    #[cfg(not(feature = "rudof"))]
    {
        core_shacl::validate(data_ttl, shapes_ttl, as_type, capability)
    }
}

/// The prefix every node of the report graph is named under:
/// `urn:ikigai:shacl:report:<content id of the report graph>:<blank-node label>`. A
/// consumer can recognize a node this crate minted by this prefix, and nothing else in
/// a report carries it.
pub const REPORT_SCHEME: &str = "urn:ikigai:shacl:report:";

/// Percent-encode a blank-node label down to the URN-safe set. RDF 1.1 admits `:`,
/// `.` and non-ASCII in a label; this crate's minted IRIs stay in
/// `[A-Za-z0-9._-]` so a consumer can split the scheme from the label on `:`.
pub(crate) fn encode_label(label: &str) -> String {
    label
        .bytes()
        .map(|b| match b {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'_' | b'.' => (b as char).to_string(),
            _ => format!("%{b:02X}"),
        })
        .collect()
}

/// One triple as a canonical, escaping-safe line: the JSON encoding of its three
/// terms. Used only to content-address a report graph, so what matters is that equal
/// graphs render equally and unequal ones do not — [`Term`]'s field order is fixed
/// by its `serde` derive. Both engines name their report nodes through it.
pub(crate) fn canonical_line(subject: &Term, predicate: &str, object: &Term) -> String {
    serde_json::to_string(&(subject, predicate, object)).expect("a Term is always serializable")
}

/// A representation from a media type + body.
pub(crate) fn repr(media: &str, body: String) -> Representation {
    Representation::new(
        ReprType::new(media).with_param("charset", "utf-8"),
        body.into_bytes(),
    )
    .cacheable()
}

/// `urn:shacl:validate` — async because `shapes` may be a resource to resolve (inline Turtle
/// is used directly). Validates the piped `data` graph against it.
struct ValidateEndpoint;

#[async_trait]
impl Endpoint for ValidateEndpoint {
    async fn invoke(&self, inv: &Invocation<'_>) -> Result<Representation> {
        // Core's own refusal, unchanged: `MissingArgument` when the argument is absent,
        // `InvalidArgument` when it is not inline or not UTF-8. These used to be rewritten as an
        // untyped `Error::Endpoint` with a friendlier sentence, which made a caller's omission
        // indistinguishable from a failure of the endpoint (ikigai-conformance's REQUIRED). The
        // sentence lives on in the ArgSpecs: `data` is the Turtle graph, usually piped in;
        // `shapes` is inline Turtle or a resolvable resource IRI.
        let data = inv.inline_str("data")?.to_string();
        let shapes_arg = inv.inline_str("shapes")?;
        let as_type = inv.inline_str("as").unwrap_or(TURTLE).to_string();

        // Inline Turtle used directly; anything else is a resource reference resolved through
        // the kernel (the one await — no rudof value is live across it).
        let shapes_ttl = if is_inline_shapes(shapes_arg) {
            shapes_arg.to_string()
        } else {
            let repr = resolve_shapes(inv, shapes_arg).await?;
            String::from_utf8(repr.bytes).map_err(|e| {
                Error::Endpoint(format!("urn:shacl:validate: shapes not UTF-8: {e}"))
            })?
        };

        validate(&data, &shapes_ttl, &as_type, inv.capability)
    }

    fn name(&self) -> &str {
        "shacl-validate"
    }

    fn describe(&self) -> Description {
        Description::new("shacl-validate")
            .title("SHACL validate")
            .summary(
                "Validate an RDF data graph against a SHACL shapes graph. The report is itself \
                 a graph (text/turtle) — or application/json {conforms, violations: \
                 [{focus_node, path, component, message, value}]}.",
            )
            .verb(Verb::Source)
            .verb(Verb::Meta)
            // ⚠ All three inputs are `xsd:string`, and for two of them that is the type
            // of the WIRE, not of the value. `data` and `shapes` are RDF *documents*;
            // `shapes` is additionally a union (inline Turtle OR a resource IRI, told
            // apart by `is_inline_shapes`). An `ArgSpec` has `class`, `one_of` and
            // `default` and no `example`, `pattern` or `any_of`, so the only class that
            // is TRUE of every accepted value is the string the wire carries. Reported
            // for ikigai-core (conformance PENDING #7/#25).
            .input(
                ArgSpec::new("data")
                    .summary(
                        "the RDF data graph to validate, as Turtle — piped in: with `shapes` \
                         named it is the sole unnamed required input, which is where the engine \
                         routes a piped value",
                    )
                    .class(XSD_STRING),
            )
            .input(
                ArgSpec::new("shapes")
                    .summary(
                        "the SHACL shapes graph: inline Turtle, or a resolvable resource IRI \
                         sourced through the kernel (the report is then as cacheable as it is)",
                    )
                    .class(XSD_STRING),
            )
            .input(
                ArgSpec::new("as")
                    .summary(
                        "report representation: text/turtle (default, the report graph) or \
                         application/json",
                    )
                    .class(XSD_STRING)
                    .one_of([TURTLE, JSON])
                    .default_value(TURTLE)
                    .optional(),
            )
            .output("text/turtle;charset=utf-8")
            .output("application/json;charset=utf-8")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SHAPES: &str = r#"@prefix sh: <http://www.w3.org/ns/shacl#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix : <http://example.org/> .
:PersonShape a sh:NodeShape ;
  sh:targetClass :Person ;
  sh:property [ sh:path :name ; sh:minCount 1 ; sh:datatype xsd:string ] ."#;

    fn json(data: &str, shapes: &str) -> String {
        String::from_utf8(
            validate(
                data,
                shapes,
                "application/json",
                &ikigai_core::Capability::root(),
            )
            .unwrap()
            .bytes,
        )
        .unwrap()
    }

    #[test]
    fn conforming_data_conforms() {
        let data = r#"@prefix : <http://example.org/> .
:alice a :Person ; :name "Alice" ."#;
        let body = json(data, SHAPES);
        assert!(body.contains("\"conforms\": true"), "{body}");
    }

    #[test]
    fn violating_data_reports() {
        // :bob is a Person with no :name → violates sh:minCount 1.
        let data = r#"@prefix : <http://example.org/> .
:bob a :Person ."#;
        let body = json(data, SHAPES);
        assert!(body.contains("\"conforms\": false"), "{body}");
    }

    #[test]
    fn report_is_a_turtle_graph() {
        let data = r#"@prefix : <http://example.org/> .
:bob a :Person ."#;
        let ttl = String::from_utf8(
            validate(
                data,
                SHAPES,
                "text/turtle",
                &ikigai_core::Capability::root(),
            )
            .unwrap()
            .bytes,
        )
        .unwrap();
        // The SHACL report is itself RDF — it carries the shacl namespace.
        assert!(
            ttl.contains("shacl#") || ttl.contains("sh:"),
            "report graph: {ttl}"
        );
    }

    /// The shape the ikigai-core process vocabulary authors: a `sh:sparql` on a NODE shape
    /// with a `{?value}` message template. The report must name the value; the path is
    /// `null` because a node-shape constraint has none (the spec, not a dropped field).
    const KNOWS_SHAPES: &str = r#"@prefix sh: <http://www.w3.org/ns/shacl#> .
@prefix : <http://example.org/> .
:PersonShape a sh:NodeShape ;
  sh:targetClass :Person ;
  sh:sparql [
    sh:message "{?this} knows itself via {?value}" ;
    sh:prefixes <http://example.org/> ;
    sh:select """
      PREFIX : <http://example.org/>
      SELECT $this ?value WHERE { $this :knows ?value . FILTER(?value = $this) }
    """ ] ."#;

    const KNOWS_DATA: &str = r#"@prefix : <http://example.org/> .
:bob a :Person ; :knows :bob ."#;

    #[test]
    fn sparql_node_constraint_resolves_the_message_and_carries_the_value() {
        let report = validate_report(KNOWS_DATA, KNOWS_SHAPES).unwrap();
        assert!(!report.conforms);
        assert_eq!(report.violations.len(), 1, "{report:?}");
        let r = &report.violations[0];
        assert_eq!(r.focus_node, "http://example.org/bob");
        assert_eq!(r.path, None, "a node-shape sh:sparql has no sh:resultPath");
        assert_eq!(
            r.component,
            "http://www.w3.org/ns/shacl#SPARQLConstraintComponent"
        );
        assert_eq!(
            r.message,
            Some(Term::Literal {
                value: "http://example.org/bob knows itself via http://example.org/bob".into(),
                lang: None,
                datatype: None,
            })
        );
        assert_eq!(
            r.value,
            Some(Term::Uri {
                value: "http://example.org/bob".into()
            })
        );
    }

    #[test]
    fn sparql_constraint_that_binds_path_fills_path() {
        let shapes = KNOWS_SHAPES.replace(
            "SELECT $this ?value WHERE {",
            "SELECT $this ?value ?path WHERE { BIND(:knows AS ?path)",
        );
        let report = validate_report(KNOWS_DATA, &shapes).unwrap();
        assert_eq!(report.violations.len(), 1, "{report:?}");
        assert_eq!(
            report.violations[0].path.as_deref(),
            Some("http://example.org/knows"),
            "a bound ?path becomes sh:resultPath"
        );
    }

    #[test]
    fn sparql_constraint_without_a_message_reports_null_message() {
        let shapes =
            KNOWS_SHAPES.replace("sh:message \"{?this} knows itself via {?value}\" ;\n", "");
        let report = validate_report(KNOWS_DATA, &shapes).unwrap();
        assert_eq!(report.violations.len(), 1, "{report:?}");
        assert_eq!(report.violations[0].message, None);
    }

    #[test]
    fn tagged_shape_message_beats_the_validator_default_and_lowest_tag_wins() {
        // Core-constraint results carry rudof's own untagged default message merged with the
        // shape's; a shape author's tagged message must be what the JSON reports.
        let shapes = SHAPES.replace(
            "sh:datatype xsd:string ]",
            "sh:datatype xsd:string ; sh:message \"nom {?value} invalide\"@fr, \
             \"name {?value} is not a string\"@en ]",
        );
        let data = r#"@prefix : <http://example.org/> .
:carol a :Person ; :name 42 ."#;
        let report = validate_report(data, &shapes).unwrap();
        assert_eq!(report.violations.len(), 1, "{report:?}");
        assert_eq!(
            report.violations[0].message,
            Some(Term::Literal {
                value: "name 42 is not a string".into(),
                lang: Some("en".into()),
                datatype: None,
            })
        );
    }

    #[test]
    fn json_keeps_the_signature_keys_first_and_in_order() {
        let body = json(KNOWS_DATA, KNOWS_SHAPES);
        let keys: Vec<usize> = [
            "\"focus_node\"",
            "\"path\"",
            "\"component\"",
            "\"message\"",
            "\"value\"",
        ]
        .iter()
        .map(|k| {
            body.find(k)
                .unwrap_or_else(|| panic!("{k} missing in {body}"))
        })
        .collect();
        assert!(keys.windows(2).all(|w| w[0] < w[1]), "key order in {body}");
        // And the JSON face round-trips through the public type.
        let parsed: Report = serde_json::from_str(&body).unwrap();
        assert_eq!(parsed, validate_report(KNOWS_DATA, KNOWS_SHAPES).unwrap());
    }

    #[test]
    fn turtle_face_carries_the_same_resolved_message_value_and_path() {
        let shapes = SHAPES.replace(
            "sh:datatype xsd:string ]",
            "sh:datatype xsd:string ; sh:message \"{?value} is not a string\" ]",
        );
        let data = r#"@prefix : <http://example.org/> .
:carol a :Person ; :name 42 ."#;
        let ttl = String::from_utf8(
            validate(
                data,
                &shapes,
                "text/turtle",
                &ikigai_core::Capability::root(),
            )
            .unwrap()
            .bytes,
        )
        .unwrap();
        for needle in [
            "sh:resultMessage \"42 is not a string\"",
            "sh:value 42",
            "sh:resultPath <http://example.org/name>",
            "sh:focusNode <http://example.org/carol>",
        ] {
            assert!(
                ttl.contains(needle),
                "missing `{needle}` in report graph:\n{ttl}"
            );
        }
        // The template is resolved on this face too — not copied through verbatim.
        assert!(!ttl.contains("{?value}"), "unresolved template in:\n{ttl}");
    }

    #[test]
    fn inline_shapes_detected() {
        assert!(is_inline_shapes("@prefix : <x> .\n:S a sh:NodeShape ."));
        assert!(is_inline_shapes("<http://x> a sh:NodeShape ."));
        assert!(!is_inline_shapes("urn:data:shapes"));
        assert!(!is_inline_shapes("https://example.org/shapes.ttl"));
    }

    /// A call missing a required input, or carrying one that is not UTF-8, is refused with
    /// core's TYPED error naming the input, never an untyped `Error::Endpoint`: a caller (an
    /// agent, `urn:kernel:validate`) must be able to tell its own omission from a failure of
    /// the endpoint. ikigai-conformance's REQUIRED check walks the same drops.
    #[test]
    fn a_missing_or_undecodable_input_is_refused_typed() {
        let kernel = ikigai_core::Kernel::new(std::sync::Arc::new(space()));
        let call = |args: &[(&str, &[u8])]| {
            let request = args.iter().fold(
                Request::new(
                    Verb::Source,
                    Iri::parse("urn:shacl:validate").expect("a valid IRI"),
                ),
                |request, (name, value)| request.with_arg(*name, ArgRef::Inline(value.to_vec())),
            );
            futures::executor::block_on(kernel.issue(request, &ikigai_core::Capability::root()))
                .expect_err("the call is refused")
        };
        let data: &[u8] = b"@prefix : <http://example.org/> .\n:bob a :Person .";

        let err = call(&[("shapes", SHAPES.as_bytes())]);
        assert!(
            matches!(&err, Error::MissingArgument(name) if name == "data"),
            "{err:?}"
        );
        let err = call(&[("data", data)]);
        assert!(
            matches!(&err, Error::MissingArgument(name) if name == "shapes"),
            "{err:?}"
        );
        let err = call(&[("data", &[0xff, 0xfe]), ("shapes", SHAPES.as_bytes())]);
        assert!(
            matches!(&err, Error::InvalidArgument { name, .. } if name == "data"),
            "{err:?}"
        );
        let err = call(&[("data", data), ("shapes", &[0xff, 0xfe])]);
        assert!(
            matches!(&err, Error::InvalidArgument { name, .. } if name == "shapes"),
            "{err:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// This library *as* a dynamically-loadable WASM module (`--features module`).
// ---------------------------------------------------------------------------
#[cfg(feature = "module")]
ikigai_module::wasm_module!(crate::space);

/// Surface a Rust panic in the browser console (module builds only).
#[cfg(feature = "module")]
#[wasm_bindgen::prelude::wasm_bindgen(start)]
pub fn __module_start() {
    console_error_panic_hook::set_once();
}
