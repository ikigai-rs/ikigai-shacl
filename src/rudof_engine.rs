//! The rudof engine behind `urn:shacl:validate` (the `rudof` feature, on by default).
//!
//! rudof's consolidated [`shacl`] crate (in-memory, no rocksdb) validates; everything here
//! bounds what a caller can make it do first, and projects its report onto the faces the crate
//! root defines ([`crate::Report`], and the skolemized report graph under
//! [`crate::REPORT_SCHEME`]). Without this feature the crate serves the same resource from
//! [`crate::core_shacl`], which is held to the same verdicts by `tests/differential.rs`.

use crate::depth;
use crate::{
    canonical_line, encode_label, repr, QuotedTriple, Report, ReportResult, Term, JSON,
    REPORT_SCHEME, SHAPES_ARG, TURTLE, XSD_STRING,
};
use ikigai_core::{ContentId, Error, Representation, Result};
use rudof_rdf::rdf_core::term::literal::ConcreteLiteral;
use rudof_rdf::rdf_core::term::{IriOrBlankNode, Object, Triple as RdfTriple};
use rudof_rdf::rdf_core::{BuildRDF, NeighsRDF, RDFFormat, Rdf, SHACLPath};
use rudof_rdf::rdf_impl::{OxigraphInMemory, ReaderMode};
use shacl::ir::components::BasicSparql;
use shacl::ir::{IRComponent, IRSchema};
use shacl::rdf::ShaclParser;
use shacl::types::MessageMap;
use shacl::validator::processor::{DataValidation, ShaclProcessor};
use shacl::validator::report::{ValidationReport, ValidationResult};
use shacl::validator::{ShaclConfig, ShaclValidationMode};
use sparql_service::RdfData;

/// Parse a Turtle graph into rudof's in-memory `RdfData`, refusing first any triple-term
/// nesting past [`MAX_TURTLE_NESTING`], and then any IRI no SPARQL query can hold (see
/// [`check_iris`]). `role` is the argument the text arrived in.
fn parse_data(ttl: &str, role: &str) -> Result<RdfData> {
    depth::check_turtle_nesting(ttl, role)?;
    let graph =
        RdfData::from_str(ttl, &RDFFormat::Turtle, None, &ReaderMode::default()).map_err(|e| {
            Error::Endpoint(format!("urn:shacl:validate: {role} graph parse error: {e}"))
        })?;
    check_iris(&graph, role)?;
    Ok(graph)
}

/// Parse + compile a SHACL shapes Turtle graph into the validator's IR schema, refusing any
/// SPARQL literal in it past the bounds, and any structure nested past [`MAX_SHAPE_DEPTH`],
/// before rudof's parser sees the graph. Recursive in rudof even within the bounds (an RDF
/// list is parsed one call per element), so [`run`] calls it on a sized stack. Also returns
/// what the structural walk found, for bounding the recursion that follows the data
/// ([`depth::data_recursion`]).
fn compile_shapes(ttl: &str) -> Result<(IRSchema, depth::Structure)> {
    let shapes = parse_data(ttl, SHAPES_ARG)?;
    bound_literals(&shapes)?;
    let structure = depth::check_shapes_structure(&shapes)?;
    let ast = ShaclParser::new(shapes)
        .parse()
        .map_err(|e| Error::Endpoint(format!("urn:shacl:validate: shapes parse error: {e}")))?;
    let schema = ast
        .try_into()
        .map_err(|e| Error::Endpoint(format!("urn:shacl:validate: shapes compile error: {e}")))?;
    Ok((schema, structure))
}

// ---------------------------------------------------------------------------
// Caller SPARQL is bounded before rudof parses it (ledger #963).
//
// A `sh:select` is caller text, and rudof hands it to oxigraph's SPARQL parser and evaluator
// once per focus node, inside `validate`. Both recurse, and a stack overflow aborts the WHOLE
// process, not one request: 300 nested parentheses, or a 300-term `||` chain, killed a 2 MiB
// thread through `urn:shacl:validate` (tests/sparql_stack.rs). So, as at the store's doors:
//
// 1. every SPARQL-carrying literal in the shapes graph is checked with
//    `ikigai_store::limits::check_sparql` before rudof compiles anything ([`bound_literals`]);
// 2. the query rudof will actually BUILD from each constraint is reconstructed and checked too
//    ([`bound_queries`]), because two of its pieces are not in any `sh:select` literal: the
//    shape's `sh:path`, rendered into `$PATH`, and the `sh:declare` prefixes, written into a
//    `PREFIX` header unescaped. A deep path or a prefix name carrying brackets nests the query
//    the literal check never saw. It also refuses a select whose text before `WHERE` changes
//    byte length when uppercased, where rudof's own assembly would panic or misplace `?this`
//    ([`where_offset_holds`], ledger #1102);
// 3. validation runs on `limits::on_sparql_stack`, a thread sized for the longest of those
//    queries, because nesting is not the only recursion (a flat `||` chain is not refused and
//    must still fit), and rudof's validator inside it on a one-thread rayon pool of the same
//    size ([`on_rudof_pool`]), because rudof hands a level of two or more shapes to rayon's
//    2 MiB workers (ledger #1102).
//
// ⚠ Step 2 mirrors rudof's private query assembly (`basic_validator.rs` and
// `inject_values_into_where`/`path_to_sparql` in `shacl::validator::constraints::sparql`, 0.3.24),
// and step 3 rests on rudof's `ShaclProcessor::validate` using `par_iter_mut`. The rudof upper
// bound in Cargo.toml is what keeps both true; raising it means re-reading those four functions
// (tests/rudof_traps.rs has a control for each trap).
//
// ---------------------------------------------------------------------------
// Caller SPARQL never reaches the network (ledger #1099, #1083).
//
// rudof_rdf turns `oxigraph/http-client` on for every native target, so in this crate's own
// build, and in every host linking it, oxigraph's `SparqlEvaluator::new()` installs an HTTP
// service handler. rudof evaluates each `sh:select` through exactly that constructor, built
// privately inside `OxigraphInMemory::query_select`, so no refusing handler
// (`ikigai_store::service::evaluator`) can be put on it: `SERVICE <http://…>` in a shapes graph
// was an outbound request no `urn:cap:net:*` gates (tests/service_egress.rs). The guard is
// therefore entirely BEFORE rudof sees the text:
//
// 4. every query step 2 reconstructs is parsed with spargebra (oxigraph's own parser) and walked
//    with `ikigai_store::service::has_service` ([`refuse_service_in`]). A query the mirror
//    cannot parse is refused too, so a divergence from rudof's assembly fails closed. This also
//    covers what no literal shows: a `SERVICE` written into an `sh:declare` PREFIX NAME, which
//    rudof copies into the header unescaped;
// 5. the one piece the mirror replaces with a placeholder is the focus node, which rudof writes
//    into `VALUES ?this { … }` with oxrdf's `Display`. A literal's lexical form is escaped there,
//    and a blank-node label is lexed, but rudof's LENIENT Turtle reader keeps an IRI holding `>`
//    in a literal's datatype or inside a triple term (it re-validates only plain subject,
//    predicate and object IRIs), and that `>` ends the IRI in the query. So every IRI in both
//    graphs is checked for the characters a SPARQL IRI cannot hold ([`check_iris`]).
//
// Only `sh:sparql`/`sh:select` is evaluated by rudof 0.3.24 (natively, in `ShaclValidationMode::
// Native`); SPARQL-based targets (`sh:SPARQLTarget`), SPARQL-based constraint components
// (`sh:ask`/`sh:validator`) and `owl:imports` are not parsed or fetched at all, and the egress
// test pins that, so a rudof release that starts evaluating them fails it. `LOAD` cannot reach
// rudof's evaluator: it only ever parses a QUERY.
// ---------------------------------------------------------------------------

/// The SHACL predicates whose literal object is a SPARQL query. rudof 0.3.24 runs only
/// `sh:select`; `sh:ask` is bounded as well because it is the other SPARQL text SHACL defines
/// (SPARQL-based constraint components), and refusing it costs nothing.
const SPARQL_PREDICATES: [&str; 2] = [
    "http://www.w3.org/ns/shacl#select",
    "http://www.w3.org/ns/shacl#ask",
];

/// Refuse any SPARQL literal in the shapes graph past `limits::check_sparql`'s bounds.
fn bound_literals(shapes: &RdfData) -> Result<()> {
    let bad = |e: String| Error::Endpoint(format!("urn:shacl:validate: shapes graph: {e}"));
    for triple in shapes.triples().map_err(|e| bad(e.to_string()))? {
        let (_, predicate, object) = triple.into_components();
        if !SPARQL_PREDICATES.contains(&predicate.as_str()) {
            continue;
        }
        if let Ok(Object::Literal(lit)) = RdfData::term_as_object(&object) {
            ikigai_store::limits::check_sparql(&lit.lexical_form(), SHAPES_ARG)?;
        }
    }
    Ok(())
}

/// Reconstruct every query rudof will build from `schema` and refuse any past the bounds. The
/// focus node rudof splices into `VALUES` is data, a single term, and stands here as a short
/// placeholder ([`check_iris`] is what keeps the real one a single term).
fn bound_queries(schema: &IRSchema) -> Result<Vec<String>> {
    let mut queries = Vec::new();
    for (_, shape) in schema.iter() {
        for component in shape.components() {
            let IRComponent::BasicSparql(sparql) = component else {
                continue;
            };
            let query = rudof_query(sparql, shape.path())?;
            ikigai_store::limits::check_sparql(&query, SHAPES_ARG)?;
            queries.push(query);
        }
    }
    Ok(queries)
}

/// Refuse a reconstructed query that holds a `SERVICE` anywhere, or that does not parse (so a
/// mirror that has drifted from rudof's assembly fails closed rather than open). Parsing
/// recurses, so this runs on the thread sized for the longest query, after its bounds.
fn refuse_service_in(query: &str) -> Result<()> {
    let parsed = spargebra::SparqlParser::new()
        .parse_query(query)
        .map_err(|e| Error::InvalidArgument {
            name: SHAPES_ARG.to_string(),
            detail: format!(
                "the query rudof assembles from a `sh:sparql` constraint (its `sh:prefixes` \
                 header, `sh:select` and `$PATH`) does not parse as SPARQL, so it cannot be \
                 checked for a `SERVICE`. Nothing was evaluated: {e}"
            ),
        })?;
    // The store's walk, with this endpoint's own first sentence (which constraint, assembled how)
    // before the store's shared consumer text (`SERVICE_REFUSAL`, matchable across the
    // ecosystem), and this endpoint's remedy after it. Never the store's own refusal, whose
    // `urn:iki:store:load` advice is wrong inside a shape (ledger #1108).
    if ikigai_store::service::has_service(&parsed) {
        return Err(Error::InvalidArgument {
            name: SHAPES_ARG.to_string(),
            detail: format!(
                "a `sh:sparql` constraint's query, as rudof assembles it (its `sh:prefixes` \
                 header, `sh:select` and `$PATH`), contains a `SERVICE`. {} Fetch remote data \
                 through the kernel, where the net capability applies, and validate it as `data`.",
                ikigai_store::service::SERVICE_REFUSAL
            ),
        });
    }
    Ok(())
}

/// A character no SPARQL `IRIREF` may hold: `<>"{}|^`\` and every code point up to the space.
fn forbidden_in_iri(c: char) -> bool {
    matches!(c, '<' | '>' | '"' | '{' | '}' | '|' | '^' | '`' | '\\') || c <= ' '
}

/// The first IRI in `term` (a named node, a literal's datatype, or any part of a triple term)
/// holding a character no IRI may hold. Recursion is bounded by [`MAX_TURTLE_NESTING`], checked
/// before the graph was parsed.
fn bad_iri_in(term: &oxrdf::Term) -> Option<&str> {
    let check = |iri: &str| iri.chars().any(forbidden_in_iri);
    match term {
        oxrdf::Term::NamedNode(n) => check(n.as_str()).then_some(n.as_str()),
        oxrdf::Term::BlankNode(_) => None,
        oxrdf::Term::Literal(l) => check(l.datatype().as_str()).then(|| l.datatype().as_str()),
        oxrdf::Term::Triple(t) => bad_iri_in_triple(t),
    }
}

/// [`bad_iri_in`] over every position of a triple.
fn bad_iri_in_triple(t: &oxrdf::Triple) -> Option<&str> {
    let check = |iri: &str| iri.chars().any(forbidden_in_iri);
    let subject = match &t.subject {
        oxrdf::NamedOrBlankNode::NamedNode(n) => check(n.as_str()).then_some(n.as_str()),
        oxrdf::NamedOrBlankNode::BlankNode(_) => None,
    };
    subject
        .or_else(|| check(t.predicate.as_str()).then_some(t.predicate.as_str()))
        .or_else(|| bad_iri_in(&t.object))
}

/// Refuse a graph holding an IRI that no SPARQL query can hold, as `InvalidArgument` on `role`.
///
/// rudof parses Turtle leniently and re-validates only a triple's own subject, predicate and
/// object IRIs, so `"v"^^<…>…>` or an IRI inside a triple term keeps a `>`. rudof then writes
/// a focus node into the query it runs for a `sh:sparql` constraint with oxrdf's `Display`,
/// unescaped, where that `>` ends the IRI and the rest is query text: a `SERVICE` included. Such
/// an IRI is not an IRI at all, so it is refused in every graph, whatever the shapes hold.
fn check_iris(graph: &RdfData, role: &str) -> Result<()> {
    let triples = graph
        .triples()
        .map_err(|e| Error::Endpoint(format!("urn:shacl:validate: {role} graph: {e}")))?;
    for triple in triples {
        if let Some(iri) = bad_iri_in_triple(&triple) {
            let shown: String = iri.chars().take(120).collect();
            return Err(Error::InvalidArgument {
                name: role.to_string(),
                detail: format!(
                    "the {role} graph holds an IRI with a character no IRI may hold ({shown:?}). \
                     rudof's lenient Turtle reader keeps it in a literal's datatype or inside a \
                     triple term, and writes it unescaped into the SPARQL it runs for a \
                     `sh:sparql` constraint, where it would end the IRI and inject query text, a \
                     `SERVICE` included. Nothing was evaluated"
                ),
            });
        }
    }
    Ok(())
}

/// The query rudof's `BasicSparql::validate_sparql` issues for one focus node: a `PREFIX`
/// header from `sh:prefixes`, the `sh:select` with `$PATH` replaced by the shape's path, and a
/// `VALUES ?this` clause injected after the first `{` following `WHERE`.
fn rudof_query(sparql: &BasicSparql, path: Option<&SHACLPath>) -> Result<String> {
    let header: String = sparql
        .prefixes()
        .map(|p| {
            p.iter()
                .map(|(prefix, iri)| format!("PREFIX {prefix}: <{iri}>\n"))
                .collect()
        })
        .unwrap_or_default();
    let select = if sparql.select().contains("$PATH") {
        let rendered = match path {
            Some(path) => path_to_sparql(path, 0)?,
            None => String::new(),
        };
        sparql.select().replace("$PATH", &rendered)
    } else {
        sparql.select().clone()
    };
    let values = "VALUES ?this { <urn:ikigai:shacl:focus> }";
    let at = match select.to_uppercase().find("WHERE") {
        Some(at) => {
            where_offset_holds(&select, at)?;
            select[at..].find('{').map(|brace| at + brace + 1)
        }
        None => None,
    };
    let body = match at {
        Some(at) => format!("{} {values}{}", &select[..at], &select[at..]),
        None => format!("{values} {select}"),
    };
    Ok(format!("{header}{body}"))
}

/// Refuse a select whose text before `WHERE` changes byte length when uppercased (ledger #1102).
///
/// rudof finds `WHERE` at byte `at` of the UPPERCASED select and slices the ORIGINAL select at
/// that offset. The two agree only while everything before it uppercases to the same number of
/// bytes, and `ı` (two bytes) uppercases to `I` (one): off a character boundary rudof's slice
/// PANICS, and on one it injects `VALUES ?this` wherever the offset landed, into a comment for
/// instance, so the constraint runs unbound and reports nodes that are not focus nodes. Since
/// uppercasing maps each character on its own, `select[..at]` uppercasing to exactly `at` bytes
/// is the exact condition for the offset to be the original's `WHERE`.
fn where_offset_holds(select: &str, at: usize) -> Result<()> {
    if select.get(..at).map(|before| before.to_uppercase().len()) == Some(at) {
        return Ok(());
    }
    Err(Error::InvalidArgument {
        name: SHAPES_ARG.to_string(),
        detail: "a `sh:select` has text before its `WHERE` that changes byte length when \
                 uppercased (`ı` uppercases to `I`, one byte shorter): rudof finds `WHERE` in \
                 the uppercased query and cuts the original at that offset, where it would \
                 panic mid-character or bind `?this` in the wrong place. Nothing was evaluated. \
                 Write that text (a comment, a variable name, a string) without such characters"
            .to_string(),
    })
}

/// A SHACL path as rudof renders it into `$PATH`. Every level but a predicate adds a
/// parenthesis, so a path deeper than `MAX_SPARQL_NESTING` can only make a query the bound
/// refuses — and this refuses it there, which also keeps this recursion shallow.
fn path_to_sparql(path: &SHACLPath, depth: usize) -> Result<String> {
    use ikigai_store::limits::MAX_SPARQL_NESTING;
    if depth > MAX_SPARQL_NESTING {
        return Err(Error::InvalidArgument {
            name: SHAPES_ARG.to_string(),
            detail: format!(
                "a `sh:select` uses `$PATH`, and the `sh:path` it stands for nests deeper than \
                 {MAX_SPARQL_NESTING} (MAX_SPARQL_NESTING): rudof writes every level of it into \
                 the query as a parenthesis, and the SPARQL parser recurses once per level, where \
                 a stack overflow aborts the whole host. Flatten the path"
            ),
        });
    }
    let all = |paths: &[SHACLPath], sep: &str| -> Result<String> {
        let parts = paths
            .iter()
            .map(|p| path_to_sparql(p, depth + 1))
            .collect::<Result<Vec<_>>>()?;
        Ok(format!("({})", parts.join(sep)))
    };
    Ok(match path {
        SHACLPath::Predicate { pred } => format!("<{pred}>"),
        SHACLPath::Alternative { paths } => all(paths, "|")?,
        SHACLPath::Sequence { paths } => all(paths, "/")?,
        SHACLPath::Inverse { path } => format!("^({})", path_to_sparql(path, depth + 1)?),
        SHACLPath::ZeroOrMore { path } => format!("({})*", path_to_sparql(path, depth + 1)?),
        SHACLPath::OneOrMore { path } => format!("({})+", path_to_sparql(path, depth + 1)?),
        SHACLPath::ZeroOrOne { path } => format!("({})?", path_to_sparql(path, depth + 1)?),
    })
}

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

/// Strip a term's surrounding `<…>`/quotes to a bare IRI/lexical string, so rudof's and
/// shacl-engine's term renderings normalize to the same form.
fn bare(s: &str) -> String {
    let s = s.trim();
    s.strip_prefix('<')
        .and_then(|s| s.strip_suffix('>'))
        .unwrap_or(s)
        .to_string()
}

/// Project a (message-resolved) rudof report onto the JSON face.
fn report_from(report: &ValidationReport) -> Report {
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

/// Validate `data_ttl` against `shapes_ttl` with rudof, returning the full [`Report`].
pub(crate) fn validate_report(data_ttl: &str, shapes_ttl: &str) -> Result<Report> {
    Ok(report_from(&resolve_messages(run(data_ttl, shapes_ttl)?)))
}

/// Validate `data_ttl` against `shapes_ttl` with rudof, returning the report graph as Turtle.
pub(crate) fn validate_turtle(data_ttl: &str, shapes_ttl: &str) -> Result<String> {
    report_turtle(&resolve_messages(run(data_ttl, shapes_ttl)?))
}

/// Run the validator: data graph + compiled shapes → rudof ValidationReport. Every query
/// rudof will parse is bounded first (see [`bound_queries`]), and so is every depth the
/// caller's Turtle can reach (see the `depth` module). Then both halves run on sized stacks,
/// because LENGTH recurses too, and length is not refused: compiling on a thread sized from
/// the shapes text (rudof parses an RDF list one call per element), and checking every query
/// for a `SERVICE` ([`refuse_service_in`]), parsing the data and validating on one sized for the
/// longest query, with rudof's validator on a one-thread pool of that size ([`on_rudof_pool`]),
/// grown by what the recursion that follows the data can reach once the data is parsed
/// ([`depth::data_recursion`], ledger #1326). On wasm there is no thread and both run inline.
fn run(data_ttl: &str, shapes_ttl: &str) -> Result<ValidationReport> {
    let (schema, structure, queries) = ikigai_store::limits::on_sparql_stack(shapes_ttl, || {
        let (schema, structure) = compile_shapes(shapes_ttl)?;
        let queries = bound_queries(&schema)?;
        Ok((schema, structure, queries))
    })?;
    let longest = queries.iter().max_by_key(|q| q.len()).cloned();
    ikigai_store::limits::on_sparql_stack(longest.as_deref().unwrap_or(""), move || {
        // No `SERVICE` reaches rudof's evaluator: "Caller SPARQL never reaches the network".
        for query in &queries {
            refuse_service_in(query)?;
        }
        let data = parse_data(data_ttl, "data")?;
        // A shape that refers back to itself along a path is validated one call per link of
        // the data: refuse past the bound, and grow the validator's stack for what it admits.
        let levels = depth::data_recursion(&data, &structure)?;
        let mut validator: DataValidation = data.into();
        // `config` is the third argument as of shacl 0.3.17 (added in a PATCH release — see
        // the upper bounds in Cargo.toml). The defaults are the pre-0.3.17 behavior:
        // violations kept, conformance evidence off, cautious/LFP recursion semantics.
        let config = ShaclConfig::default();
        // The pool's thread is sized like this one, for the longest query, plus the recursion
        // the data admits.
        let longest = queries
            .iter()
            .max_by_key(|q| q.len())
            .map_or("", String::as_str);
        let stack = ikigai_store::limits::sparql_stack_size(longest)
            .saturating_add(depth::recursion_stack(levels));
        on_rudof_pool(stack, || {
            validator
                .validate(&schema, &ShaclValidationMode::Native, &config)
                .map_err(|e| Error::Endpoint(format!("urn:shacl:validate: validation error: {e}")))
        })
    })
}

/// Run rudof's validator on a ONE-thread rayon pool whose thread has `stack` bytes (at least
/// `limits::sparql_stack_size` of the longest query, the size `on_sparql_stack` gives), rather
/// than on rayon's global pool (ledger #1102).
///
/// rudof validates each topological level of shapes with `par_iter_mut`. A level of one shape
/// is not split and runs on the calling thread, already sized; a level of two or more is, and
/// every shape in it then runs on a global-pool worker with the default 2 MiB stack, where a
/// flat `||` chain the sized thread holds aborts the whole process (tests/rudof_traps.rs). From
/// inside this pool's worker, rudof's `par_iter_mut` uses THIS pool, so the whole level runs on
/// the one sized thread, in sequence. That gives up rudof's parallelism across the shapes of a
/// level, which it only ever had for levels of two or more. ⚠ It works only because `rayon` here
/// is the same `rayon-core` rudof's `par_iter_mut` resolves (see Cargo.toml). On wasm there is no
/// thread, as for `on_sparql_stack`, and the work runs inline.
fn on_rudof_pool<T, F>(stack: usize, work: F) -> Result<T>
where
    T: Send,
    F: FnOnce() -> Result<T> + Send,
{
    #[cfg(not(target_family = "wasm"))]
    {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .stack_size(stack)
            .thread_name(|_| "ikigai-shacl-validate".to_string())
            .build()
            .map_err(|e| {
                Error::Unavailable(format!(
                    "urn:shacl:validate: could not start a {} MiB thread to validate on: {e}",
                    stack >> 20
                ))
            })?;
        pool.install(work)
    }
    #[cfg(target_family = "wasm")]
    {
        let _ = stack;
        work()
    }
}

/// Validate, rendering per `as_type`: `application/json` → the [`Report`]; else the SHACL
/// report graph as Turtle (the report *is* RDF). Same results, same resolved messages, on
/// both faces.
pub(crate) fn validate(data_ttl: &str, shapes_ttl: &str, as_type: &str) -> Result<Representation> {
    let report = resolve_messages(run(data_ttl, shapes_ttl)?);
    if as_type.split(';').next().unwrap_or("").trim() == JSON {
        Ok(repr(
            JSON,
            serde_json::to_string_pretty(&report_from(&report))
                .map_err(|e| Error::Endpoint(format!("urn:shacl:validate: json error: {e}")))?,
        ))
    } else {
        Ok(repr(TURTLE, report_turtle(&report)?))
    }
}

/// An [`IriOrBlankNode`] as the [`Object`] carrying the same term — so subjects and
/// objects go through one rewrite and one canonical rendering.
fn subject_object(subject: &IriOrBlankNode) -> Object {
    match subject {
        IriOrBlankNode::Iri(iri) => Object::iri(iri.clone()),
        IriOrBlankNode::BlankNode(label) => Object::bnode(label.clone()),
    }
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
        .map(|(s, p, o)| canonical_line(&term(s), p.as_str(), &term(o)))
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

#[cfg(test)]
mod tests {
    use super::*;

    const SHAPES: &str = r#"@prefix sh: <http://www.w3.org/ns/shacl#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix : <http://example.org/> .
:PersonShape a sh:NodeShape ;
  sh:targetClass :Person ;
  sh:property [ sh:path :name ; sh:minCount 1 ; sh:datatype xsd:string ] ."#;

    /// The mirror of rudof's query assembly, pinned on every piece it copies: the PREFIX header
    /// from `sh:declare`, every SHACL path operator rendered into `$PATH`, and the `VALUES`
    /// clause injected after the first `{` following `WHERE` (found case-insensitively).
    #[test]
    fn the_query_mirror_assembles_what_rudof_assembles() {
        let shapes = r#"@prefix sh: <http://www.w3.org/ns/shacl#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix : <http://example.org/> .
:S a sh:NodeShape ; sh:targetClass :Person ; sh:property :P .
:P sh:path ( [ sh:inversePath :p ] [ sh:zeroOrMorePath [ sh:alternativePath ( :q [ sh:oneOrMorePath :r ] [ sh:zeroOrOnePath :s ] ) ] ] ) ;
  sh:sparql [ sh:prefixes :decls ;
    sh:select "SELECT $this ?value where { $this $PATH ?value }" ] .
:decls sh:declare [ sh:prefix "ex" ; sh:namespace "http://example.org/"^^xsd:anyURI ] ."#;
        let queries = bound_queries(&compile_shapes(shapes).unwrap().0).unwrap();
        assert_eq!(
            queries,
            ["PREFIX ex: <http://example.org/>\n\
             SELECT $this ?value where { VALUES ?this { <urn:ikigai:shacl:focus> } $this \
             (^(<http://example.org/p>)/((<http://example.org/q>|(<http://example.org/r>)+|\
             (<http://example.org/s>)?))*) ?value }"]
        );
        // And the mirror's output is SPARQL oxigraph's parser accepts, with no `SERVICE`.
        refuse_service_in(&queries[0]).unwrap();
    }

    #[test]
    fn a_path_is_refused_one_level_past_the_bound_and_rendered_at_it() {
        // A predicate path, taken from a compiled shape (rudof's `IriS` is not re-exported).
        let schema = compile_shapes(SHAPES).unwrap().0;
        let mut path = schema
            .iter()
            .find_map(|(_, shape)| shape.path().cloned())
            .unwrap();
        for _ in 0..ikigai_store::limits::MAX_SPARQL_NESTING {
            path = SHACLPath::ZeroOrOne {
                path: Box::new(path),
            };
        }
        // 64 operators around a predicate: the predicate sits at depth 64, which renders.
        assert!(path_to_sparql(&path, 0).is_ok());
        let path = SHACLPath::ZeroOrOne {
            path: Box::new(path),
        };
        let err = path_to_sparql(&path, 0).unwrap_err();
        assert!(
            matches!(&err, Error::InvalidArgument { name, .. } if name == "shapes"),
            "{err}"
        );
    }
}
