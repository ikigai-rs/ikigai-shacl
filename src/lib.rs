//! `ikigai-shacl` — SHACL validation as an ikigai resource.
//!
//! `urn:shacl:validate` validates a piped RDF `data` graph against a SHACL `shapes` graph,
//! via rudof's consolidated [`shacl`] crate (in-memory, no rocksdb). The validation **report
//! is itself an RDF graph**: the default `text/turtle` output is the SHACL ValidationReport
//! (conforms + a node per violation), and `application/json` gives a structured
//! `{conforms, results}` — content-negotiated structured errors for free.
//!
//! `shapes` is taken **by reference** (the ROC-idiomatic form: a shapes graph is a resource
//! you point at, sourced through the kernel — cacheable, golden-threaded); inline Turtle is
//! also accepted. So the endpoint is `async` (the one await is the shapes resolution).
//!
//! Heavy dependency tree (the rudof stack), so this is a standalone crate rather than
//! something the host links unconditionally. It is **native-linked**: rudof gates
//! `shacl::validator` off wasm, so the `module` (lazy-loadable WASM) face does not build —
//! in the browser the same `urn:shacl:validate` resource is served by the JavaScript
//! `shacl-engine`, held to the same parity corpus (see `js-parity/`).

#![forbid(unsafe_code)]

use async_trait::async_trait;
use ikigai_core::{
    ArgRef, ArgSpec, Description, Endpoint, EndpointSpace, Error, Exact, Invocation, Iri, ReprType,
    Representation, Request, Result, Verb,
};
use rudof_rdf::rdf_core::{BuildRDF, RDFFormat};
use rudof_rdf::rdf_impl::{OxigraphInMemory, ReaderMode};
use shacl::ir::IRSchema;
use shacl::rdf::ShaclParser;
use shacl::validator::processor::{DataValidation, ShaclProcessor};
use shacl::validator::report::ValidationReport;
use shacl::validator::{ShaclConfig, ShaclValidationMode};
use sparql_service::RdfData;

/// The space binding `urn:shacl:validate`.
pub fn space() -> EndpointSpace {
    EndpointSpace::new().bind(Exact::new("urn:shacl:validate"), ValidateEndpoint)
}

/// Parse a Turtle graph into rudof's in-memory `RdfData`.
fn parse_data(ttl: &str, role: &str) -> Result<RdfData> {
    RdfData::from_str(ttl, &RDFFormat::Turtle, None, &ReaderMode::default())
        .map_err(|e| Error::Endpoint(format!("urn:shacl:validate: {role} graph parse error: {e}")))
}

/// Parse + compile a SHACL shapes Turtle graph into the validator's IR schema.
fn compile_shapes(ttl: &str) -> Result<IRSchema> {
    let shapes = parse_data(ttl, "shapes")?;
    let ast = ShaclParser::new(shapes)
        .parse()
        .map_err(|e| Error::Endpoint(format!("urn:shacl:validate: shapes parse error: {e}")))?;
    ast.try_into()
        .map_err(|e| Error::Endpoint(format!("urn:shacl:validate: shapes compile error: {e}")))
}

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
#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct Violation {
    /// The focus node that failed (IRI / blank-node id).
    pub focus_node: String,
    /// The `sh:resultPath` (a property-path predicate IRI), if any.
    pub path: Option<String>,
    /// The `sh:sourceConstraintComponent` IRI (e.g. `…#MinCountConstraintComponent`).
    pub component: String,
}

/// The portable validation outcome: `conforms` + the sorted violation signatures. Serialized
/// as the `application/json` output AND used as the parity contract in tests.
#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, Clone, Debug)]
pub struct ValidationOutcome {
    pub conforms: bool,
    pub violations: Vec<Violation>,
}

/// Strip a term's surrounding `<…>`/quotes to a bare IRI/lexical string, so rudof's and
/// shacl-engine's term renderings normalize to the same form.
fn bare(s: &str) -> String {
    let s = s.trim();
    s.strip_prefix('<')
        .and_then(|s| s.strip_suffix('>'))
        .unwrap_or(s)
        .to_string()
}

/// Validate `data_ttl` against `shapes_ttl`, returning the portable [`ValidationOutcome`] —
/// the parity contract. Sync: no rudof value crosses an await.
pub fn validate_outcome(data_ttl: &str, shapes_ttl: &str) -> Result<ValidationOutcome> {
    let report = run(data_ttl, shapes_ttl)?;
    let mut violations: Vec<Violation> = report
        .results()
        .iter()
        .map(|r| Violation {
            focus_node: bare(&r.focus_node().to_string()),
            path: r.path().map(|p| bare(&p.to_string())),
            component: bare(&r.constraint_component().to_string()),
        })
        .collect();
    violations.sort();
    Ok(ValidationOutcome {
        conforms: report.conforms(),
        violations,
    })
}

/// Run the validator: data graph + compiled shapes → rudof ValidationReport.
fn run(data_ttl: &str, shapes_ttl: &str) -> Result<ValidationReport> {
    let schema = compile_shapes(shapes_ttl)?;
    let data = parse_data(data_ttl, "data")?;
    let mut validator: DataValidation = data.into();
    // `config` is the third argument as of shacl 0.3.17 (added in a PATCH release — see the
    // upper bounds in Cargo.toml). The defaults are the pre-0.3.17 behavior: violations kept,
    // conformance evidence off, cautious/LFP recursion semantics.
    let config = ShaclConfig::default();
    validator
        .validate(&schema, &ShaclValidationMode::Native, &config)
        .map_err(|e| Error::Endpoint(format!("urn:shacl:validate: validation error: {e}")))
}

/// Validate, rendering per `as_type`: `application/json` → the portable [`ValidationOutcome`];
/// else the SHACL report graph as Turtle (the report *is* RDF).
fn validate(data_ttl: &str, shapes_ttl: &str, as_type: &str) -> Result<Representation> {
    if as_type.split(';').next().unwrap_or("").trim() == "application/json" {
        let outcome = validate_outcome(data_ttl, shapes_ttl)?;
        Ok(repr(
            "application/json",
            serde_json::to_string_pretty(&outcome)
                .map_err(|e| Error::Endpoint(format!("urn:shacl:validate: json error: {e}")))?,
        ))
    } else {
        Ok(repr(
            "text/turtle",
            report_turtle(&run(data_ttl, shapes_ttl)?)?,
        ))
    }
}

/// Serialize the SHACL ValidationReport as a Turtle graph (the report *is* RDF).
fn report_turtle(report: &ValidationReport) -> Result<String> {
    let mut out = OxigraphInMemory::empty();
    report
        .to_rdf(&mut out)
        .map_err(|e| Error::Endpoint(format!("urn:shacl:validate: report to RDF error: {e}")))?;
    let mut buf = Vec::new();
    out.serialize(&RDFFormat::Turtle, &mut buf)
        .map_err(|e| Error::Endpoint(format!("urn:shacl:validate: report serialize error: {e}")))?;
    String::from_utf8(buf)
        .map_err(|e| Error::Endpoint(format!("urn:shacl:validate: report not UTF-8: {e}")))
}

/// A representation from a media type + body.
fn repr(media: &str, body: String) -> Representation {
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
        let data = inv
            .inline_str("data")
            .map_err(|_| {
                Error::Endpoint(
                    "urn:shacl:validate needs a `data` RDF (Turtle) graph — usually piped in"
                        .to_string(),
                )
            })?
            .to_string();
        let shapes_arg = inv.inline_str("shapes").map_err(|_| {
            Error::Endpoint(
                "urn:shacl:validate needs a `shapes` SHACL graph: inline Turtle or a resolvable \
                 resource IRI"
                    .to_string(),
            )
        })?;
        let as_type = inv.inline_str("as").unwrap_or("text/turtle").to_string();

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

        validate(&data, &shapes_ttl, &as_type)
    }

    fn name(&self) -> &str {
        "shacl-validate"
    }

    fn describe(&self) -> Description {
        Description::new("shacl-validate")
            .title("SHACL validate")
            .summary(
                "Validate an RDF data graph against a SHACL shapes graph. The report is itself \
                 a graph (text/turtle) — or application/json {conforms, results}.",
            )
            .verb(Verb::Source)
            .verb(Verb::Meta)
            .input(ArgSpec::new("data").summary("the RDF data graph to validate — usually piped in"))
            .input(ArgSpec::new("shapes").summary(
                "the SHACL shapes graph: inline Turtle or a resolvable resource IRI",
            ))
            .input(ArgSpec::new("as").summary(
                "report representation: text/turtle (default, the report graph) or application/json",
            ))
            .output("text/turtle;charset=utf-8")
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
        String::from_utf8(validate(data, shapes, "application/json").unwrap().bytes).unwrap()
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
        let ttl = String::from_utf8(validate(data, SHAPES, "text/turtle").unwrap().bytes).unwrap();
        // The SHACL report is itself RDF — it carries the shacl namespace.
        assert!(
            ttl.contains("shacl#") || ttl.contains("sh:"),
            "report graph: {ttl}"
        );
    }

    #[test]
    fn inline_shapes_detected() {
        assert!(is_inline_shapes("@prefix : <x> .\n:S a sh:NodeShape ."));
        assert!(is_inline_shapes("<http://x> a sh:NodeShape ."));
        assert!(!is_inline_shapes("urn:data:shapes"));
        assert!(!is_inline_shapes("https://example.org/shapes.ttl"));
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
