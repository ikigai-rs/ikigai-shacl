//! `ikigai-shacl` — SHACL validation as an ikigai resource.
//!
//! `urn:shacl:validate` validates a piped RDF `data` graph against a SHACL `shapes` graph,
//! via rudof's consolidated [`shacl`] crate (in-memory, no rocksdb). The validation **report
//! is itself an RDF graph**: the default `text/turtle` output is the SHACL ValidationReport
//! (conforms + a node per violation), skolemized under a content address of the report so it
//! carries no blank node (every one is named under [`REPORT_SCHEME`]), and `application/json`
//! gives a structured
//! [`Report`] — `{conforms, violations: [{focus_node, path, component, message, value}]}` —
//! content-negotiated structured errors for free. Both faces carry the same facts: the
//! `sh:resultMessage` with its `{?value}`-style template resolved, the offending `sh:value`,
//! and the `sh:resultPath`.
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
    ArgRef, ArgSpec, ContentId, Description, Endpoint, EndpointSpace, Error, Exact, Invocation,
    Iri, ReprType, Representation, Request, Result, Verb,
};
use rudof_rdf::rdf_core::term::literal::ConcreteLiteral;
use rudof_rdf::rdf_core::term::{IriOrBlankNode, Object, Triple as RdfTriple};
use rudof_rdf::rdf_core::{BuildRDF, NeighsRDF, RDFFormat, Rdf};
use rudof_rdf::rdf_impl::{OxigraphInMemory, ReaderMode};
use shacl::ir::IRSchema;
use shacl::rdf::ShaclParser;
use shacl::types::MessageMap;
use shacl::validator::processor::{DataValidation, ShaclProcessor};
use shacl::validator::report::{ValidationReport, ValidationResult};
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
/// The endpoint's JSON face is the richer [`ReportResult`]; a signature is its first three
/// keys.
#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct Violation {
    /// The focus node that failed (IRI / blank-node id).
    pub focus_node: String,
    /// The `sh:resultPath` (a property-path predicate IRI), if any.
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

const XSD_STRING: &str = "http://www.w3.org/2001/XMLSchema#string";

/// The two faces of the report, which are also the two values `as` accepts and the
/// two declared outputs — one list, so `as`'s `one_of` and `outputs` cannot drift.
const TURTLE: &str = "text/turtle";
const JSON: &str = "application/json";

/// rudof's `Object` → [`Term`]. Matched by variant rather than `Display`ed: `Object`'s
/// `Display` is `todo!()` for quoted triples, and a report face must not panic on data.
fn term(o: &Object) -> Term {
    match o {
        Object::Iri(iri) => Term::Uri {
            value: iri.as_str().to_string(),
        },
        Object::BlankNode(id) => Term::Bnode { value: id.clone() },
        Object::Literal(lit) => literal_term(lit),
        Object::Triple {
            subject,
            predicate,
            object,
        } => Term::Triple {
            value: Box::new(QuotedTriple {
                subject: match subject.as_ref() {
                    IriOrBlankNode::Iri(iri) => Term::Uri {
                        value: iri.as_str().to_string(),
                    },
                    IriOrBlankNode::BlankNode(id) => Term::Bnode { value: id.clone() },
                },
                predicate: Term::Uri {
                    value: predicate.as_str().to_string(),
                },
                object: term(object),
            }),
        },
    }
}

/// A literal as a [`Term::Literal`]: language tag when tagged, else the datatype unless it is
/// the plain-literal default `xsd:string`.
fn literal_term(lit: &ConcreteLiteral) -> Term {
    let lang = lit.lang().map(|l| l.as_str().to_string());
    let datatype = match lang {
        Some(_) => None,
        None => Some(lit.datatype().to_string()).filter(|dt| dt != XSD_STRING),
    };
    Term::Literal {
        value: lit.lexical_form(),
        lang,
        datatype,
    }
}

/// One validation result as the `application/json` face reports it. The first three keys are
/// the parity [`Violation`] signature and keep their names and order; `message` and `value`
/// follow. Sorted by these fields in this order, so a report is deterministic.
#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct ReportResult {
    /// The focus node that failed (IRI / blank-node id).
    pub focus_node: String,
    /// The `sh:resultPath` (a property-path predicate IRI), if the result has one. A
    /// constraint on a **node** shape has none unless it binds `?path` itself — a
    /// `sh:sparql` on a node shape reports `null` here by the SHACL spec, not by omission.
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

    /// Project a (message-resolved) rudof report.
    fn from_report(report: &ValidationReport) -> Self {
        let mut violations: Vec<ReportResult> = report
            .results()
            .iter()
            .map(|r| ReportResult {
                focus_node: bare(&r.focus_node().to_string()),
                path: r.path().map(|p| bare(&p.to_string())),
                component: bare(&r.constraint_component().to_string()),
                message: message_term(r.message()),
                value: r.value().map(term),
            })
            .collect();
        violations.sort();
        Report {
            conforms: report.conforms(),
            violations,
        }
    }
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

/// The one message the JSON face reports: tagged beats untagged (rudof's own default message
/// is untagged, a shape author's may not be), then the lowest language tag. `None` when the
/// result carries no message at all (a `sh:sparql` constraint without `sh:message`).
fn message_term(messages: &MessageMap) -> Option<Term> {
    let mut all: Vec<(bool, Option<String>, &String)> = messages
        .iter()
        .map(|(lang, text)| {
            let lang = lang.as_ref().map(|l| l.as_str().to_string());
            (lang.is_none(), lang, text)
        })
        .collect();
    all.sort();
    let (_, lang, text) = all.into_iter().next()?;
    Some(Term::Literal {
        value: text.clone(),
        lang,
        datatype: None,
    })
}

/// Resolve a `sh:message` template against one result: `{?this}`/`{$this}` → the focus node,
/// `{?value}`/`{$value}` → the value node, `{?path}`/`{$path}` → the result path (SHACL
/// §6.5.3, the bindings a result carries). rudof copies the template through verbatim; the
/// report is where the author's `{?value}` finally names the value. A placeholder whose
/// variable this result does not carry is left as written.
fn resolve_template(text: &str, r: &ValidationResult) -> String {
    let bindings = [
        ("this", Some(term(r.focus_node()).lexical())),
        ("value", r.value().map(|v| term(v).lexical())),
        ("path", r.path().map(|p| bare(&p.to_string()))),
    ];
    let mut out = text.to_string();
    for (name, bound) in bindings {
        if let Some(bound) = bound {
            for sigil in ['?', '$'] {
                out = out.replace(&format!("{{{sigil}{name}}}"), &bound);
            }
        }
    }
    out
}

/// Rewrite every result's messages with their templates resolved, so the Turtle face and
/// the JSON face carry the same `sh:resultMessage`.
fn resolve_messages(report: ValidationReport) -> ValidationReport {
    let results: Vec<ValidationResult> = report
        .results()
        .iter()
        .map(|r| {
            let resolved = r
                .message()
                .iter()
                .fold(MessageMap::new(), |map, (lang, text)| {
                    map.with_message(lang.clone(), resolve_template(text, r))
                });
            r.clone().with_message(resolved)
        })
        .collect();
    report.with_results(results)
}

/// Validate `data_ttl` against `shapes_ttl`, returning the full [`Report`] — what the
/// `application/json` face serializes. Sync: no rudof value crosses an await.
pub fn validate_report(data_ttl: &str, shapes_ttl: &str) -> Result<Report> {
    Ok(Report::from_report(&resolve_messages(run(
        data_ttl, shapes_ttl,
    )?)))
}

/// Validate `data_ttl` against `shapes_ttl`, returning the portable [`ValidationOutcome`] —
/// the parity contract. Sync: no rudof value crosses an await.
pub fn validate_outcome(data_ttl: &str, shapes_ttl: &str) -> Result<ValidationOutcome> {
    Ok(validate_report(data_ttl, shapes_ttl)?.outcome())
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

/// Validate, rendering per `as_type`: `application/json` → the [`Report`]; else the SHACL
/// report graph as Turtle (the report *is* RDF). Same results, same resolved messages, on
/// both faces.
fn validate(data_ttl: &str, shapes_ttl: &str, as_type: &str) -> Result<Representation> {
    let report = resolve_messages(run(data_ttl, shapes_ttl)?);
    if as_type.split(';').next().unwrap_or("").trim() == JSON {
        Ok(repr(
            JSON,
            serde_json::to_string_pretty(&Report::from_report(&report))
                .map_err(|e| Error::Endpoint(format!("urn:shacl:validate: json error: {e}")))?,
        ))
    } else {
        Ok(repr(TURTLE, report_turtle(&report)?))
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
fn encode_label(label: &str) -> String {
    label
        .bytes()
        .map(|b| match b {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'_' | b'.' => (b as char).to_string(),
            _ => format!("%{b:02X}"),
        })
        .collect()
}

/// An [`IriOrBlankNode`] as the [`Object`] carrying the same term — so subjects and
/// objects go through one rewrite and one canonical rendering.
fn subject_object(subject: &IriOrBlankNode) -> Object {
    match subject {
        IriOrBlankNode::Iri(iri) => Object::iri(iri.clone()),
        IriOrBlankNode::BlankNode(label) => Object::bnode(label.clone()),
    }
}

/// One triple as a canonical, escaping-safe line: the JSON encoding of its three
/// terms. Used only to content-address the graph, so what matters is that equal
/// graphs render equally and unequal ones do not — [`Term`]'s field order is fixed
/// by its `serde` derive and its `Display`-free rendering never panics (see
/// [`term`]).
fn canonical_line(subject: &Object, predicate: &str, object: &Object) -> String {
    serde_json::to_string(&(term(subject), predicate, term(object)))
        .expect("a Term is always serializable")
}

/// Replace every blank node in `object` with its skolem IRI under `scheme`.
fn skolemize_object(object: Object, scheme: &str) -> Result<Object> {
    match object {
        Object::BlankNode(label) => skolem_iri(scheme, &label),
        Object::Triple {
            subject,
            predicate,
            object,
        } => {
            // An RDF-star quoted triple: its subject may be a blank node too.
            let subject = match skolemize_object(subject_object(&subject), scheme)? {
                Object::Iri(iri) => IriOrBlankNode::Iri(iri),
                other => {
                    return Err(Error::Endpoint(format!(
                        "urn:shacl:validate: quoted-triple subject is not a node: {other}"
                    )))
                }
            };
            Ok(Object::Triple {
                subject: Box::new(subject),
                predicate,
                object: Box::new(skolemize_object(*object, scheme)?),
            })
        }
        iri_or_literal => Ok(iri_or_literal),
    }
}

/// The skolem IRI for one blank-node label — **parsed**, not merely formatted, so a
/// label this crate failed to encode is an error rather than a malformed graph.
fn skolem_iri(scheme: &str, label: &str) -> Result<Object> {
    let iri = format!("{scheme}{}", encode_label(label));
    let parsed = Object::parse(&iri, None)
        .map_err(|e| Error::Endpoint(format!("urn:shacl:validate: bad skolem IRI `{iri}`: {e}")))?;
    match parsed {
        Object::Iri(_) => Ok(parsed),
        _ => Err(Error::Endpoint(format!(
            "urn:shacl:validate: skolem IRI `{iri}` did not parse as an IRI"
        ))),
    }
}

/// Give every blank node in the report graph a stable IRI — the recipe's
/// "skolemize; no blank nodes", which is what makes a report diffable, unionable
/// and SPARQL-able instead of isomorphism-compared.
///
/// rudof's `to_rdf` mints a blank node for the report, one per result, and passes
/// through whatever the shapes graph gave it (`sh:sourceShape`, and the RDF-list
/// structure of a complex `sh:path`). Each becomes
///
/// ```text
/// urn:ikigai:shacl:report:<content-id of the whole report graph>:<blank-node label>
/// ```
///
/// **What that buys and what it costs, stated because the code cannot.** The
/// content address makes the name a pure function of the report, so two runs over
/// the same data and shapes mint the same IRIs and two different reports can never
/// collide — which is the failure a bare `_:1`-style counter has. The cost is the
/// other direction: a report that differs *anywhere* is a different content id, so
/// every node in it is renamed. Nodes are aligned across reports by their content
/// (`sh:focusNode`, `sh:resultPath`, `sh:sourceConstraintComponent`, `sh:value`),
/// not by their IRI — the `application/json` face's sorted [`Report`] is the
/// aligned view.
///
/// The label after the content id is the source graph's, which is only ever unique
/// *within* one document — that is exactly the scope the content id supplies.
fn skolemize(graph: &OxigraphInMemory) -> Result<OxigraphInMemory> {
    type Sub = <OxigraphInMemory as Rdf>::Subject;
    type Pred = <OxigraphInMemory as Rdf>::IRI;

    let bad = |e: String| Error::Endpoint(format!("urn:shacl:validate: report graph: {e}"));
    let mut triples: Vec<(Object, Pred, Object)> = Vec::new();
    for triple in graph.triples().map_err(|e| bad(e.to_string()))? {
        let (subject, predicate, object) = triple.into_components();
        // Infallible for this store (an RDF subject IS an IRI or a blank node), which is
        // why this one is `into` and the object below is not: a term may also be a
        // literal, and the trait bound is only `TryInto`.
        let subject: IriOrBlankNode = subject.into();
        let object: Object = object
            .try_into()
            .map_err(|_| bad("an object is not an RDF term".to_string()))?;
        triples.push((subject_object(&subject), predicate, object));
    }

    // The content address of the graph: canonical lines, sorted, so it does not
    // depend on the store's iteration order.
    let mut lines: Vec<String> = triples
        .iter()
        .map(|(s, p, o)| canonical_line(s, p.as_str(), o))
        .collect();
    lines.sort();
    let scheme = format!(
        "{REPORT_SCHEME}{}:",
        ContentId::of(lines.join("\n").as_bytes())
    );

    let mut out = OxigraphInMemory::empty();
    out.set_prefix_map(graph.prefixmap().clone());
    for (subject, predicate, object) in triples {
        let subject = Sub::try_from(skolemize_object(subject, &scheme)?)
            .map_err(|_| bad("a skolemized subject is not a subject".to_string()))?;
        out.add_triple(subject, predicate, skolemize_object(object, &scheme)?)
            .map_err(|e| bad(e.to_string()))?;
    }
    Ok(out)
}

/// Serialize the SHACL ValidationReport as a Turtle graph (the report *is* RDF),
/// skolemized: see [`skolemize`] for the IRI every node is minted under.
fn report_turtle(report: &ValidationReport) -> Result<String> {
    let mut graph = OxigraphInMemory::empty();
    report
        .to_rdf(&mut graph)
        .map_err(|e| Error::Endpoint(format!("urn:shacl:validate: report to RDF error: {e}")))?;
    let out = skolemize(&graph)?;
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
        let ttl = String::from_utf8(validate(data, &shapes, "text/turtle").unwrap().bytes).unwrap();
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
