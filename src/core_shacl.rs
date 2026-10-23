//! A SHACL subset validator with no rudof, no network stack and no recursion (ledger #1176).
//!
//! rudof cannot be built without a network stack on native (`rudof_iri` links reqwest, and
//! `rudof_rdf`'s native target turns on oxigraph's `http-client` and tokio), and its validator
//! recurses along both graphs. A host that only needs the shapes it ships, such as a plan door
//! validating against `ikigai_vocab::SHAPES`, turns the `rudof` feature off and is served from
//! here instead, under the same name and with the same report.
//!
//! # The subset
//!
//! - **Targets**: `sh:targetClass` (instances through `rdfs:subClassOf*`), implicit class
//!   targets (a shape that is also an `rdfs:Class`), `sh:targetNode`, `sh:targetSubjectsOf`,
//!   `sh:targetObjectsOf`.
//! - **Shapes**: node shapes, and property shapes whose `sh:path` is a single predicate IRI;
//!   `sh:property`, `sh:node`, `sh:message`, and `sh:closed` with `sh:ignoredProperties`.
//! - **Constraints**: `sh:class`, `sh:datatype`, `sh:nodeKind`, `sh:minCount`, `sh:maxCount`,
//!   `sh:in`, `sh:hasValue`, `sh:pattern` (with `sh:flags`), `sh:minLength`, `sh:maxLength`,
//!   `sh:minInclusive`, `sh:maxInclusive`, `sh:minExclusive`, `sh:maxExclusive`.
//! - **SHACL-SPARQL**, with the `sparql` feature only: `sh:sparql` with `sh:select`,
//!   `sh:message`, `sh:prefixes` (through `sh:declare`, `sh:prefix`, `sh:namespace` and
//!   `owl:imports`), `$this` pre-bound and `$PATH` written as the shape's predicate. Without the
//!   feature (a build with default features off, ledger #2107), `sh:sparql` and `sh:select` are
//!   REFUSED, naming the construct and the feature, and the prefix declarations, which change no
//!   verdict on their own, are accepted and ignored.
//! - **Annotations** that never change a verdict: `sh:name`, `sh:description`, `sh:order`,
//!   `sh:group`.
//!
//! ★ **A bound refuses, it never truncates.** Every other term in the SHACL namespace, as a
//! predicate or as a class, is REFUSED by name before anything is validated, and so is a
//! complex property path, a malformed parameter and a cycle of shape references. A constraint
//! this validator skipped would make data look conforming when it is not, which is the one
//! answer a validator must never give by accident.
//!
//! # No recursion
//!
//! Nothing here recurses over either graph: shape references are checked for cycles with an
//! explicit work list, conformance to a `sh:node` shape is computed bottom-up from a stack
//! (each shape strictly below the one that refers to it, since a cycle is refused), and
//! subclass closures and RDF lists are walked iteratively with a visited set. The only
//! recursion left is the RDF and SPARQL libraries' own: a triple term is copied once per level
//! (bounded by [`crate::MAX_TURTLE_NESTING`] before parsing), and each `sh:select` is parsed and
//! evaluated by oxigraph (bounded by `ikigai_store::limits` and run on a stack sized for it).
//!
//! # The work bound (a build without `sparql`)
//!
//! A build without the `sparql` feature has no ikigai-store, and so no time budget. It is bounded
//! by WORK instead: [`MAX_VALIDATION_WORK`] units, a unit being one triple parsed, one shape
//! compiled, one value node, focus node or class visited, one value checked against one
//! constraint, one `sh:in` member compared, one triple a closed shape scanned or one byte of the
//! text `sh:pattern`, `sh:minLength` or `sh:maxLength` reads (with the compiled pattern capped at
//! [`MAX_PATTERN_SIZE`], so that a byte stands for a bounded cost). Past it the
//! validation is refused with a typed `InvalidArgument` on `data` (or on `shapes`, while the
//! shapes graph is still being parsed) and no report, partial or otherwise. The count is a
//! function of the two graphs alone, so the same inputs are refused alike on every machine. The
//! nesting bound ([`crate::MAX_TURTLE_NESTING`], ikigai-rdf's) applies in every build.
//!
//! With `sparql` the work is still counted and never refused: the time budget below is the
//! bound there, as it was through 0.3.x.
//!
//! # SPARQL
//!
//! With the `sparql` feature, every `sh:select` passes the guards the rudof path applies, before it is parsed or run:
//! `limits::check_sparql` (size and nesting), `budget::check_query` (the algebra), and
//! `service::has_service` (no `SERVICE`, ledger #1099). Each is then evaluated over an
//! in-memory store through `ikigai_store::service::evaluator()`, which refuses any service it
//! is asked for, with `$this` substituted rather than spliced into the text. The whole
//! validation runs inside an `EvaluationBudget` (ledger #1327): past the caller's time budget
//! the caller is answered with a timeout, and the evaluation is told to stop.

use std::collections::{HashMap, HashSet};
#[cfg(feature = "sparql")]
use std::sync::OnceLock;

use ikigai_core::{Capability, Error, Representation, Result};
#[cfg(feature = "sparql")]
use ikigai_store::budget::{
    check_query, default_max_overdue, EvaluationBudget, TimeBudget, DEFAULT_BUDGET,
};
#[cfg(feature = "sparql")]
use oxigraph::sparql::{CancellationToken, QueryResults, Variable};
#[cfg(feature = "sparql")]
use oxigraph::store::Store;
use oxrdf::vocab::{rdf, rdfs, xsd};
use oxrdf::{
    BlankNode, Graph, Literal, NamedNode, NamedOrBlankNode, Term as RdfTerm, TermRef, Triple,
};
#[cfg(feature = "sparql")]
use oxrdf::{GraphNameRef, QuadRef};
#[cfg(feature = "sparql")]
use spargebra::Query;

use crate::{naming, repr, Report, ReportResult, Term, JSON, SHAPES_ARG, TURTLE};

const SH: &str = "http://www.w3.org/ns/shacl#";
#[cfg(feature = "sparql")]
const OWL_IMPORTS: &str = "http://www.w3.org/2002/07/owl#imports";

/// The most WORK one validation may take in a build without the `sparql` feature, which has no
/// time budget (see the module docs for what a unit is). Ten million units: the case in
/// `tests/core_only.rs` that reaches it (a 50,000-member `sh:in` checked against 300 values)
/// is refused in under half a second in a native release build and under three in a debug one
/// (measured 2026-10-22), so no caller can hold a thread for minutes, while a validation of the
/// size a request carries (thousands of triples, tens of shapes) uses a small fraction of it.
pub const MAX_VALIDATION_WORK: u64 = 10_000_000;

/// The largest compiled `sh:pattern` a build without `sparql` takes, in the regex crate's own
/// measure of a compiled program (`RegexBuilder::size_limit`, whose default is ten times this).
/// A pattern past it is refused, as one that does not compile. Applied only without `sparql`,
/// where the time budget is not there to bound a match.
pub const MAX_PATTERN_SIZE: usize = 1 << 20;

/// The work one validation has taken so far, in the units [`MAX_VALIDATION_WORK`] counts.
#[derive(Default)]
struct Work {
    used: u64,
}

impl Work {
    /// Take `n` more units on behalf of `role` (the argument the refusal names). Refused past
    /// [`MAX_VALIDATION_WORK`] without `sparql`; only counted with it, where the time budget is
    /// the bound.
    fn charge(&mut self, n: u64, role: &str) -> Result<()> {
        self.used = self.used.saturating_add(n);
        #[cfg(not(feature = "sparql"))]
        if self.used > MAX_VALIDATION_WORK {
            return Err(Error::InvalidArgument {
                name: role.to_string(),
                detail: format!(
                    "validating this data against these shapes takes more than \
                     MAX_VALIDATION_WORK ({MAX_VALIDATION_WORK}) units of work, the bound a build \
                     without ikigai-shacl's `sparql` feature validates under in place of a time \
                     budget. It was refused rather than answered in part: no report was produced"
                ),
            });
        }
        #[cfg(feature = "sparql")]
        let _ = role;
        Ok(())
    }
}

/// The SHACL-SPARQL terms a build without the `sparql` feature refuses, as predicates, naming
/// the feature: each would change a verdict, and that build has nothing to evaluate it with.
#[cfg(not(feature = "sparql"))]
const SPARQL_PREDICATES: &[&str] = &["sparql", "select"];

/// The SHACL-SPARQL class a build without `sparql` refuses, as the object of `rdf:type`.
#[cfg(not(feature = "sparql"))]
const SPARQL_CLASSES: &[&str] = &["SPARQLConstraint"];

/// The SHACL predicates this validator implements, by local name. Anything else in the SHACL
/// namespace used as a predicate is refused by name ([`check_vocabulary`]).
const SUPPORTED_PREDICATES: &[&str] = &[
    // targets
    "targetClass",
    "targetNode",
    "targetSubjectsOf",
    "targetObjectsOf",
    // shapes
    "property",
    "path",
    "node",
    "message",
    "closed",
    "ignoredProperties",
    // core constraints
    "class",
    "datatype",
    "nodeKind",
    "minCount",
    "maxCount",
    "in",
    "hasValue",
    "pattern",
    "flags",
    "minLength",
    "maxLength",
    "minInclusive",
    "maxInclusive",
    "minExclusive",
    "maxExclusive",
    // SHACL-SPARQL
    "sparql",
    "select",
    "prefixes",
    "declare",
    "prefix",
    "namespace",
    // non-validating annotations: they never change a verdict
    "name",
    "description",
    "order",
    "group",
];

/// The SHACL classes a shapes graph may type its nodes with here. Anything else in the SHACL
/// namespace as the object of `rdf:type` is refused by name: `sh:SPARQLTarget`,
/// `sh:ConstraintComponent`, `sh:SPARQLAskValidator` and the rest each change what is checked.
const SUPPORTED_CLASSES: &[&str] = &[
    "Shape",
    "NodeShape",
    "PropertyShape",
    "SPARQLConstraint",
    "PrefixDeclaration",
];

/// The predicates whose presence makes their subject a shape (beside `rdf:type sh:NodeShape` /
/// `sh:PropertyShape` and being the object of `sh:node` or `sh:property`).
const SHAPE_PREDICATES: &[&str] = &[
    "targetClass",
    "targetNode",
    "targetSubjectsOf",
    "targetObjectsOf",
    "property",
    "path",
    "node",
    "closed",
    "class",
    "datatype",
    "nodeKind",
    "minCount",
    "maxCount",
    "in",
    "hasValue",
    "pattern",
    "flags",
    "minLength",
    "maxLength",
    "minInclusive",
    "maxInclusive",
    "minExclusive",
    "maxExclusive",
    "sparql",
];

fn sh(local: &str) -> NamedNode {
    NamedNode::new_unchecked(format!("{SH}{local}"))
}

/// A refusal of the shapes graph, as `InvalidArgument` on `shapes`.
fn refuse(detail: impl Into<String>) -> Error {
    Error::InvalidArgument {
        name: SHAPES_ARG.to_string(),
        detail: detail.into(),
    }
}

/// The refusal for a SHACL term this validator does not implement.
fn unsupported(what: &str) -> Error {
    refuse(format!(
        "the shapes graph uses {what}, which the SHACL subset validator does not implement (this \
         build has no rudof). It refuses a shapes graph it cannot apply in full rather than skip \
         a constraint, which would make data look conforming when it is not; nothing was \
         validated. The subset is described in the ikigai-shacl README"
    ))
}

/// The refusal for a SHACL-SPARQL term in a build without the `sparql` feature.
#[cfg(not(feature = "sparql"))]
fn needs_sparql(what: &str) -> Error {
    refuse(format!(
        "the shapes graph uses {what}, a SHACL-SPARQL construct, and this build of ikigai-shacl \
         has no SPARQL engine: it was built without its `sparql` feature (enable `sparql`, or \
         `rudof`, to validate it). It refuses a shapes graph it cannot apply in full rather than \
         skip a constraint, which would make data look conforming when it is not; nothing was \
         validated"
    ))
}

// ---------------------------------------------------------------------------------------------
// The compiled shapes graph.
// ---------------------------------------------------------------------------------------------

type ShapeId = usize;

/// A shapes graph, compiled: every shape, and which of them have targets.
struct Compiled {
    shapes: Vec<Shape>,
    /// The shapes with at least one target, in a deterministic order.
    roots: Vec<ShapeId>,
    /// Whether any shape carries a `sh:sparql` constraint (only then is a store built).
    #[cfg(feature = "sparql")]
    has_sparql: bool,
    /// The longest query text, which sizes the stack validation runs on.
    #[cfg(feature = "sparql")]
    longest_query: String,
}

struct Shape {
    /// The shape's node in the shapes graph: `sh:sourceShape`.
    node: NamedOrBlankNode,
    /// A property shape's predicate path.
    path: Option<NamedNode>,
    targets: Vec<Target>,
    constraints: Vec<Constraint>,
    properties: Vec<ShapeId>,
    messages: Vec<Literal>,
}

enum Target {
    Class(NamedNode),
    Node(RdfTerm),
    SubjectsOf(NamedNode),
    ObjectsOf(NamedNode),
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum NodeKind {
    Iri,
    BlankNode,
    Literal,
    BlankNodeOrIri,
    BlankNodeOrLiteral,
    IriOrLiteral,
}

#[derive(Clone, Copy)]
enum Range {
    MinInclusive,
    MaxInclusive,
    MinExclusive,
    MaxExclusive,
}

enum Constraint {
    Class(NamedNode),
    Datatype(NamedNode),
    NodeKind(NodeKind),
    MinCount(u64),
    MaxCount(u64),
    In(Vec<RdfTerm>),
    HasValue(RdfTerm),
    Pattern(regex::Regex),
    MinLength(u64),
    MaxLength(u64),
    Range(Range, Literal),
    Node(ShapeId),
    #[cfg(feature = "sparql")]
    Sparql(Box<SparqlConstraint>),
    /// `sh:closed true`: the predicates a value node may have, which are the paths of the
    /// shape's own `sh:property` shapes and its `sh:ignoredProperties`.
    Closed(HashSet<NamedNode>),
}

#[cfg(feature = "sparql")]
struct SparqlConstraint {
    query: Query,
    messages: Vec<Literal>,
}

impl Constraint {
    /// The `sh:sourceConstraintComponent` local name.
    fn component(&self) -> &'static str {
        match self {
            Constraint::Class(_) => "ClassConstraintComponent",
            Constraint::Datatype(_) => "DatatypeConstraintComponent",
            Constraint::NodeKind(_) => "NodeKindConstraintComponent",
            Constraint::MinCount(_) => "MinCountConstraintComponent",
            Constraint::MaxCount(_) => "MaxCountConstraintComponent",
            Constraint::In(_) => "InConstraintComponent",
            Constraint::HasValue(_) => "HasValueConstraintComponent",
            Constraint::Pattern(_) => "PatternConstraintComponent",
            Constraint::MinLength(_) => "MinLengthConstraintComponent",
            Constraint::MaxLength(_) => "MaxLengthConstraintComponent",
            Constraint::Range(Range::MinInclusive, _) => "MinInclusiveConstraintComponent",
            Constraint::Range(Range::MaxInclusive, _) => "MaxInclusiveConstraintComponent",
            Constraint::Range(Range::MinExclusive, _) => "MinExclusiveConstraintComponent",
            Constraint::Range(Range::MaxExclusive, _) => "MaxExclusiveConstraintComponent",
            Constraint::Node(_) => "NodeConstraintComponent",
            #[cfg(feature = "sparql")]
            Constraint::Sparql(_) => "SPARQLConstraintComponent",
            Constraint::Closed(_) => "ClosedConstraintComponent",
        }
    }
}

/// Parse caller Turtle strictly, refusing first any triple-term nesting past
/// [`crate::MAX_TURTLE_NESTING`], and charging one unit of `work` per triple. `role` is the
/// argument the text arrived in, and names the graph's blank nodes (see
/// [`naming::by_appearance`]).
fn parse_turtle(ttl: &str, role: &str, work: &mut Work) -> Result<Vec<Triple>> {
    crate::depth::check_turtle_nesting(ttl, role)?;
    let triples = oxttl::TurtleParser::new()
        .for_slice(ttl.as_bytes())
        .map(|triple| {
            work.charge(1, role)?;
            triple.map_err(|e| {
                Error::Endpoint(format!("urn:shacl:validate: {role} graph parse error: {e}"))
            })
        })
        .collect::<Result<Vec<_>>>()?;
    // RDF 1.2 triple terms parse only where some crate in the build turns on oxrdf's `rdf-12`;
    // the subset has no constraint over them, so they are refused rather than half-handled.
    if let Some(t) = triples
        .iter()
        .find(|t| !(t.object.is_named_node() || t.object.is_blank_node() || t.object.is_literal()))
    {
        return Err(Error::InvalidArgument {
            name: role.to_string(),
            detail: format!(
                "the {role} graph holds an RDF 1.2 triple term ({t}), which the SHACL subset \
                 validator does not take (this build has no rudof); nothing was validated"
            ),
        });
    }
    // The parser's label for a `[ … ]` is random, and a blank node reaches the report: label
    // every one by where it first appears instead (`data.b0`, `shapes.b0`; ledger #1565).
    naming::by_appearance(triples, role)
}

fn graph_of(triples: &[Triple]) -> Graph {
    let mut graph = Graph::new();
    for triple in triples {
        graph.insert(triple);
    }
    graph
}

/// A term as a node that can be a subject, if it is one.
fn as_node(term: TermRef<'_>) -> Option<NamedOrBlankNode> {
    match term {
        TermRef::NamedNode(n) => Some(n.into_owned().into()),
        TermRef::BlankNode(b) => Some(b.into_owned().into()),
        _ => None,
    }
}

/// Short form of a node for a refusal: `<iri>` or `_:label`.
fn shown(node: &NamedOrBlankNode) -> String {
    node.to_string()
}

/// The SHACL local name of `t`'s predicate, and of its object when `t` is an `rdf:type` of a
/// SHACL class.
fn sh_terms(t: &Triple) -> (Option<&str>, Option<&str>) {
    let predicate = t.predicate.as_str().strip_prefix(SH);
    let class = match &t.object {
        RdfTerm::NamedNode(class) if t.predicate.as_ref() == rdf::TYPE => {
            class.as_str().strip_prefix(SH)
        }
        _ => None,
    };
    (predicate, class)
}

/// Refuse any term of the SHACL namespace this validator does not implement, used as a
/// predicate or as the class of an `rdf:type`. Two passes: a term no build implements is named
/// first, so its refusal never tells a caller to enable a feature that would not help; then,
/// without `sparql`, the SHACL-SPARQL terms that feature implements.
fn check_vocabulary(triples: &[Triple]) -> Result<()> {
    for t in triples {
        let (predicate, class) = sh_terms(t);
        if let Some(local) = predicate.filter(|l| !SUPPORTED_PREDICATES.contains(l)) {
            return Err(unsupported(&format!("`sh:{local}`")));
        }
        if let Some(local) = class.filter(|l| !SUPPORTED_CLASSES.contains(l)) {
            return Err(unsupported(&format!("the class `sh:{local}`")));
        }
    }
    #[cfg(not(feature = "sparql"))]
    for t in triples {
        let (predicate, class) = sh_terms(t);
        if let Some(local) = predicate.filter(|l| SPARQL_PREDICATES.contains(l)) {
            return Err(needs_sparql(&format!("`sh:{local}`")));
        }
        if let Some(local) = class.filter(|l| SPARQL_CLASSES.contains(l)) {
            return Err(needs_sparql(&format!("the class `sh:{local}`")));
        }
    }
    Ok(())
}

/// The members of the RDF list headed by `head`, walked iteratively. A list that branches,
/// loops or ends anywhere but `rdf:nil` is refused.
fn list_members(graph: &Graph, head: TermRef<'_>, what: &str) -> Result<Vec<RdfTerm>> {
    let bad = || refuse(format!("{what} is not a well-formed RDF list"));
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    let mut cell = head.into_owned();
    loop {
        if cell == RdfTerm::NamedNode(rdf::NIL.into_owned()) {
            return Ok(out);
        }
        let node = as_node(cell.as_ref()).ok_or_else(bad)?;
        if !seen.insert(node.clone()) {
            return Err(bad());
        }
        let firsts: Vec<_> = graph
            .objects_for_subject_predicate(&node, rdf::FIRST)
            .collect();
        let rests: Vec<_> = graph
            .objects_for_subject_predicate(&node, rdf::REST)
            .collect();
        let ([first], [rest]) = (firsts.as_slice(), rests.as_slice()) else {
            return Err(bad());
        };
        out.push(first.into_owned());
        cell = rest.into_owned();
    }
}

/// The single literal value of `predicate` on `node`, if any; more than one, or a non-literal,
/// is refused.
fn one_literal(graph: &Graph, node: &NamedOrBlankNode, local: &str) -> Result<Option<Literal>> {
    let p = sh(local);
    let values: Vec<_> = graph
        .objects_for_subject_predicate(node, &p)
        .map(TermRef::into_owned)
        .collect();
    match values.as_slice() {
        [] => Ok(None),
        [RdfTerm::Literal(l)] => Ok(Some(l.clone())),
        [_] => Err(refuse(format!(
            "`sh:{local}` of {} is not a literal",
            shown(node)
        ))),
        _ => Err(refuse(format!(
            "{} has more than one `sh:{local}`",
            shown(node)
        ))),
    }
}

/// The value of a count parameter (`sh:minCount`, …): a non-negative `xsd:integer`.
fn count(literal: &Literal, local: &str) -> Result<u64> {
    if literal.datatype() != xsd::INTEGER {
        return Err(refuse(format!(
            "`sh:{local}` must be an xsd:integer, not {literal}"
        )));
    }
    literal.value().trim().parse::<u64>().map_err(|_| {
        refuse(format!(
            "`sh:{local}` must be a non-negative integer, not {literal}"
        ))
    })
}

/// Compile the shapes graph, refusing anything outside the subset, and charging `work` for the
/// triples parsed and one unit per shape.
fn compile(shapes_ttl: &str, work: &mut Work) -> Result<Compiled> {
    let triples = parse_turtle(shapes_ttl, SHAPES_ARG, work)?;
    check_vocabulary(&triples)?;
    let graph = graph_of(&triples);

    // Which nodes are shapes.
    let mut nodes: Vec<NamedOrBlankNode> = Vec::new();
    let mut seen: HashSet<NamedOrBlankNode> = HashSet::new();
    let mut add = |node: NamedOrBlankNode, nodes: &mut Vec<NamedOrBlankNode>| {
        if seen.insert(node.clone()) {
            nodes.push(node);
        }
    };
    for t in &triples {
        let local = t.predicate.as_str().strip_prefix(SH);
        let typed_shape = t.predicate.as_ref() == rdf::TYPE
            && matches!(&t.object, RdfTerm::NamedNode(c)
                if c.as_str() == format!("{SH}NodeShape") || c.as_str() == format!("{SH}PropertyShape"));
        if typed_shape || local.is_some_and(|l| SHAPE_PREDICATES.contains(&l)) {
            add(t.subject.clone(), &mut nodes);
        }
        if matches!(local, Some("node" | "property")) {
            let target = as_node(t.object.as_ref()).ok_or_else(|| {
                refuse(format!(
                    "`sh:{}` of {} must name a shape (an IRI or a blank node), not {}",
                    local.unwrap_or_default(),
                    shown(&t.subject),
                    t.object
                ))
            })?;
            add(target, &mut nodes);
        }
    }
    // A deterministic order, so the report is too.
    nodes.sort_by_key(|n| n.to_string());
    let ids: HashMap<NamedOrBlankNode, ShapeId> = nodes
        .iter()
        .enumerate()
        .map(|(i, n)| (n.clone(), i))
        .collect();

    work.charge(nodes.len() as u64, SHAPES_ARG)?;
    let mut shapes = Vec::with_capacity(nodes.len());
    #[cfg(feature = "sparql")]
    let mut has_sparql = false;
    #[cfg(feature = "sparql")]
    let mut longest_query = String::new();
    for node in &nodes {
        let objects = |local: &str| -> Vec<RdfTerm> {
            graph
                .objects_for_subject_predicate(node, &sh(local))
                .map(TermRef::into_owned)
                .collect()
        };
        let iri = |term: &RdfTerm, local: &str| -> Result<NamedNode> {
            match term {
                RdfTerm::NamedNode(n) => Ok(n.clone()),
                other => Err(refuse(format!(
                    "`sh:{local}` of {} must be an IRI, not {other}",
                    shown(node)
                ))),
            }
        };

        // The path: a single predicate IRI, or nothing (a node shape).
        let path = match objects("path").as_slice() {
            [] => None,
            [RdfTerm::NamedNode(p)] => Some(p.clone()),
            [_] => {
                return Err(unsupported(&format!(
                    "a complex property path (the `sh:path` of {} is not a predicate IRI)",
                    shown(node)
                )))
            }
            _ => {
                return Err(refuse(format!(
                    "{} has more than one `sh:path`",
                    shown(node)
                )))
            }
        };

        let mut targets = Vec::new();
        for t in objects("targetClass") {
            targets.push(Target::Class(iri(&t, "targetClass")?));
        }
        // An implicit class target: a shape that is also a class.
        if graph
            .objects_for_subject_predicate(node, rdf::TYPE)
            .any(|c| c == rdfs::CLASS.into())
        {
            if let NamedOrBlankNode::NamedNode(n) = node {
                targets.push(Target::Class(n.clone()));
            }
        }
        for t in objects("targetNode") {
            targets.push(Target::Node(t));
        }
        for t in objects("targetSubjectsOf") {
            targets.push(Target::SubjectsOf(iri(&t, "targetSubjectsOf")?));
        }
        for t in objects("targetObjectsOf") {
            targets.push(Target::ObjectsOf(iri(&t, "targetObjectsOf")?));
        }

        let mut constraints = Vec::new();
        for t in objects("class") {
            constraints.push(Constraint::Class(iri(&t, "class")?));
        }
        for t in objects("datatype") {
            constraints.push(Constraint::Datatype(iri(&t, "datatype")?));
        }
        for t in objects("nodeKind") {
            let kind = match &t {
                RdfTerm::NamedNode(n) => match n.as_str().strip_prefix(SH) {
                    Some("IRI") => Some(NodeKind::Iri),
                    Some("BlankNode") => Some(NodeKind::BlankNode),
                    Some("Literal") => Some(NodeKind::Literal),
                    Some("BlankNodeOrIRI") => Some(NodeKind::BlankNodeOrIri),
                    Some("BlankNodeOrLiteral") => Some(NodeKind::BlankNodeOrLiteral),
                    Some("IRIOrLiteral") => Some(NodeKind::IriOrLiteral),
                    _ => None,
                },
                _ => None,
            };
            constraints.push(Constraint::NodeKind(kind.ok_or_else(|| {
                refuse(format!(
                    "`sh:nodeKind` of {} must be one of the six SHACL node kinds, not {t}",
                    shown(node)
                ))
            })?));
        }
        for (local, make) in [
            ("minCount", Constraint::MinCount as fn(u64) -> Constraint),
            ("maxCount", Constraint::MaxCount),
        ] {
            for t in objects(local) {
                if path.is_none() {
                    return Err(refuse(format!(
                        "`sh:{local}` applies to a property shape, and {} has no `sh:path`",
                        shown(node)
                    )));
                }
                let RdfTerm::Literal(l) = &t else {
                    return Err(refuse(format!("`sh:{local}` must be an integer, not {t}")));
                };
                constraints.push(make(count(l, local)?));
            }
        }
        for (local, make) in [
            ("minLength", Constraint::MinLength as fn(u64) -> Constraint),
            ("maxLength", Constraint::MaxLength),
        ] {
            for t in objects(local) {
                let RdfTerm::Literal(l) = &t else {
                    return Err(refuse(format!("`sh:{local}` must be an integer, not {t}")));
                };
                constraints.push(make(count(l, local)?));
            }
        }
        for t in objects("in") {
            let members = list_members(&graph, t.as_ref(), "`sh:in`")?;
            constraints.push(Constraint::In(members));
        }
        for t in objects("hasValue") {
            constraints.push(Constraint::HasValue(t));
        }
        let flags = one_literal(&graph, node, "flags")?;
        let patterns = objects("pattern");
        if flags.is_some() && patterns.len() != 1 {
            return Err(refuse(format!(
                "{} has `sh:flags` and {} `sh:pattern` values: the flags cannot be told which \
                 pattern they belong to",
                shown(node),
                patterns.len()
            )));
        }
        for t in patterns {
            let RdfTerm::Literal(l) = &t else {
                return Err(refuse(format!("`sh:pattern` must be a string, not {t}")));
            };
            constraints.push(Constraint::Pattern(pattern(
                l.value(),
                flags.as_ref().map(Literal::value),
            )?));
        }
        for (local, range) in [
            ("minInclusive", Range::MinInclusive),
            ("maxInclusive", Range::MaxInclusive),
            ("minExclusive", Range::MinExclusive),
            ("maxExclusive", Range::MaxExclusive),
        ] {
            for t in objects(local) {
                let RdfTerm::Literal(l) = t else {
                    return Err(refuse(format!(
                        "`sh:{local}` of {} must be a literal",
                        shown(node)
                    )));
                };
                constraints.push(Constraint::Range(range, l));
            }
        }
        for t in objects("node") {
            let target = as_node(t.as_ref()).expect("checked when the shapes were collected");
            constraints.push(Constraint::Node(ids[&target]));
        }
        // `sh:closed`, with `sh:ignoredProperties`: a value node may have only the predicates of
        // the shape's own property shapes, and those it ignores. `sh:ignoredProperties` is
        // checked whether or not the shape is closed, so a malformed one is never silent.
        let closed = match one_literal(&graph, node, "closed")? {
            None => false,
            Some(l) => match (l.datatype() == xsd::BOOLEAN, l.value()) {
                (true, "true" | "1") => true,
                (true, "false" | "0") => false,
                _ => {
                    return Err(refuse(format!(
                        "`sh:closed` of {} must be an xsd:boolean, not {l}",
                        shown(node)
                    )))
                }
            },
        };
        let mut allowed = HashSet::new();
        for t in objects("ignoredProperties") {
            for member in list_members(&graph, t.as_ref(), "`sh:ignoredProperties`")? {
                allowed.insert(iri(&member, "ignoredProperties")?);
            }
        }
        if closed {
            for t in objects("property") {
                let property = as_node(t.as_ref()).expect("checked when the shapes were collected");
                // A complex path is refused when that property shape is compiled.
                allowed.extend(
                    graph
                        .objects_for_subject_predicate(&property, &sh("path"))
                        .filter_map(|p| match p {
                            TermRef::NamedNode(n) => Some(n.into_owned()),
                            _ => None,
                        }),
                );
            }
            constraints.push(Constraint::Closed(allowed));
        }
        // Without `sparql`, `check_vocabulary` has already refused every `sh:sparql`.
        #[cfg(feature = "sparql")]
        for t in objects("sparql") {
            let constraint = sparql_constraint(&graph, &t, path.as_ref())?;
            has_sparql = true;
            if constraint.1.len() > longest_query.len() {
                longest_query = constraint.1.clone();
            }
            constraints.push(Constraint::Sparql(Box::new(constraint.0)));
        }

        let properties = objects("property")
            .iter()
            .map(|t| ids[&as_node(t.as_ref()).expect("checked when the shapes were collected")])
            .collect();
        let messages = objects("message")
            .into_iter()
            .map(|t| match t {
                RdfTerm::Literal(l) => Ok(l),
                other => Err(refuse(format!(
                    "`sh:message` of {} must be a literal, not {other}",
                    shown(node)
                ))),
            })
            .collect::<Result<Vec<_>>>()?;

        shapes.push(Shape {
            node: node.clone(),
            path,
            targets,
            constraints,
            properties,
            messages,
        });
    }

    refuse_reference_cycles(&shapes)?;
    let roots = (0..shapes.len())
        .filter(|&i| !shapes[i].targets.is_empty())
        .collect();
    Ok(Compiled {
        shapes,
        roots,
        #[cfg(feature = "sparql")]
        has_sparql,
        #[cfg(feature = "sparql")]
        longest_query,
    })
}

/// `sh:pattern` with `sh:flags` (the XPath flags SPARQL's `REGEX` takes), compiled.
fn pattern(source: &str, flags: Option<&str>) -> Result<regex::Regex> {
    let flags = flags.unwrap_or_default();
    // Quote before configuring the builder so `q` preserves the other flags.
    let quoted;
    let expression = if flags.contains('q') {
        quoted = regex::escape(source);
        &quoted
    } else {
        source
    };
    let mut builder = regex::RegexBuilder::new(expression);
    for flag in flags.chars() {
        match flag {
            'i' => {
                builder.case_insensitive(true);
            }
            's' => {
                builder.dot_matches_new_line(true);
            }
            'm' => {
                builder.multi_line(true);
            }
            'x' => {
                builder.ignore_whitespace(true);
            }
            'q' => {}
            other => {
                return Err(refuse(format!(
                "`sh:flags` holds `{other}`, which is not one of the XPath flags (i, s, m, x, q)"
            )))
            }
        }
    }
    // Without `sparql` the work bound charges a match by the length of the text it reads, which
    // stands for its cost only while the compiled pattern is small: so it is capped too.
    #[cfg(not(feature = "sparql"))]
    builder.size_limit(MAX_PATTERN_SIZE);
    builder
        .build()
        .map_err(|e| refuse(format!("`sh:pattern` {source:?} does not compile: {e}")))
}

/// Compile one `sh:sparql` constraint: its `sh:select` with `$PATH` written as the shape's
/// predicate, parsed with its declared prefixes, and every guard applied. Returns the
/// constraint and the query text (which sizes the stack it runs on).
#[cfg(feature = "sparql")]
fn sparql_constraint(
    graph: &Graph,
    term: &RdfTerm,
    path: Option<&NamedNode>,
) -> Result<(SparqlConstraint, String)> {
    let node = as_node(term.as_ref()).ok_or_else(|| {
        refuse(format!(
            "`sh:sparql` must name a constraint node, not {term}"
        ))
    })?;
    let select = one_literal(graph, &node, "select")?.ok_or_else(|| {
        refuse(format!(
            "the `sh:sparql` constraint {} has no `sh:select`",
            shown(&node)
        ))
    })?;
    let messages = graph
        .objects_for_subject_predicate(&node, &sh("message"))
        .map(|t| match t {
            TermRef::Literal(l) => Ok(l.into_owned()),
            other => Err(refuse(format!(
                "`sh:message` of {} must be a literal, not {other}",
                shown(&node)
            ))),
        })
        .collect::<Result<Vec<_>>>()?;

    // `$PATH` as rudof writes it: the shape's path, or nothing on a node shape.
    let text = select.value().replace(
        "$PATH",
        &path
            .map(|p| format!("<{}>", p.as_str()))
            .unwrap_or_default(),
    );
    ikigai_store::limits::check_sparql(&text, SHAPES_ARG)?;

    // The declared prefixes go to the parser as prefixes, never into the text.
    let mut parser = spargebra::SparqlParser::new();
    let mut declared: HashMap<String, String> = HashMap::new();
    for (prefix, namespace) in prefixes(graph, &node)? {
        match declared.get(&prefix) {
            Some(existing) if existing != &namespace => {
                return Err(refuse(format!(
                    "the prefix `{prefix}` is declared for two namespaces, <{existing}> and \
                     <{namespace}>"
                )))
            }
            Some(_) => continue,
            None => {}
        }
        parser = parser.with_prefix(&prefix, &namespace).map_err(|e| {
            refuse(format!(
                "the namespace declared for `{prefix}` is not an IRI ({namespace:?}): {e}"
            ))
        })?;
        declared.insert(prefix, namespace);
    }
    // The parser and both walks recurse: on a thread sized for this query, after its bounds.
    let query = ikigai_store::limits::on_sparql_stack(&text, || {
        let query = parser.parse_query(&text).map_err(|e| {
            refuse(format!(
                "a `sh:select` does not parse as SPARQL (with its `sh:prefixes` and `$PATH`): {e}"
            ))
        })?;
        if !matches!(query, Query::Select { .. }) {
            return Err(refuse("a `sh:select` must hold a SELECT query".to_string()));
        }
        check_query(&query, SHAPES_ARG)?;
        if ikigai_store::service::has_service(&query) {
            return Err(refuse(format!(
                "a `sh:sparql` constraint's query (its `sh:prefixes`, `sh:select` and `$PATH`) \
                 contains a `SERVICE`. {} Fetch remote data through the kernel, where the net \
                 capability applies, and validate it as `data`.",
                ikigai_store::service::SERVICE_REFUSAL
            )));
        }
        Ok(query)
    })?;
    Ok((SparqlConstraint { query, messages }, text))
}

/// The prefix declarations a `sh:sparql` constraint's `sh:prefixes` reach: each value's
/// `sh:declare`, and those of everything it reaches through `owl:imports`, walked iteratively.
#[cfg(feature = "sparql")]
fn prefixes(graph: &Graph, constraint: &NamedOrBlankNode) -> Result<Vec<(String, String)>> {
    let imports = NamedNode::new_unchecked(OWL_IMPORTS);
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    let mut todo: Vec<NamedOrBlankNode> = graph
        .objects_for_subject_predicate(constraint, &sh("prefixes"))
        .filter_map(as_node)
        .collect();
    while let Some(node) = todo.pop() {
        if !seen.insert(node.clone()) {
            continue;
        }
        for decl in graph.objects_for_subject_predicate(&node, &sh("declare")) {
            let decl = as_node(decl).ok_or_else(|| {
                refuse("a `sh:declare` must name a prefix declaration node".to_string())
            })?;
            let prefix = one_literal(graph, &decl, "prefix")?;
            let namespace = one_literal(graph, &decl, "namespace")?;
            let (Some(prefix), Some(namespace)) = (prefix, namespace) else {
                return Err(refuse(format!(
                    "the prefix declaration {} needs exactly one `sh:prefix` and one \
                     `sh:namespace`",
                    shown(&decl)
                )));
            };
            out.push((prefix.value().to_string(), namespace.value().to_string()));
        }
        todo.extend(
            graph
                .objects_for_subject_predicate(&node, &imports)
                .filter_map(as_node),
        );
    }
    out.sort();
    Ok(out)
}

/// Refuse a cycle of shape references (`sh:node`, `sh:property`), found by Kahn's algorithm
/// over an explicit queue. A caller cannot supply shapes on the plan path, so a recursive shape
/// is refused here rather than bounded: the rudof path is the one that validates those.
fn refuse_reference_cycles(shapes: &[Shape]) -> Result<()> {
    let edges = |s: &Shape| -> Vec<ShapeId> {
        s.constraints
            .iter()
            .filter_map(|c| match c {
                Constraint::Node(t) => Some(*t),
                _ => None,
            })
            .chain(s.properties.iter().copied())
            .collect()
    };
    let mut indegree = vec![0usize; shapes.len()];
    for s in shapes {
        for t in edges(s) {
            indegree[t] += 1;
        }
    }
    let mut ready: Vec<ShapeId> = (0..shapes.len()).filter(|&i| indegree[i] == 0).collect();
    let mut done = 0;
    while let Some(i) = ready.pop() {
        done += 1;
        for t in edges(&shapes[i]) {
            indegree[t] -= 1;
            if indegree[t] == 0 {
                ready.push(t);
            }
        }
    }
    if done == shapes.len() {
        return Ok(());
    }
    let on_cycle = (0..shapes.len())
        .find(|&i| indegree[i] > 0)
        .map(|i| shown(&shapes[i].node))
        .unwrap_or_default();
    Err(unsupported(&format!(
        "a recursive shape (a cycle of `sh:node` / `sh:property` references through \
         {on_cycle})"
    )))
}

// ---------------------------------------------------------------------------------------------
// Validation.
// ---------------------------------------------------------------------------------------------

/// One validation result.
struct Res {
    focus: RdfTerm,
    path: Option<NamedNode>,
    component: &'static str,
    source: NamedOrBlankNode,
    value: Option<RdfTerm>,
    messages: Vec<Literal>,
}

/// The default message for a result whose shape has no `sh:message`.
fn default_message(constraint: &Constraint) -> String {
    match constraint {
        Constraint::Class(c) => format!("Class constraint not satisfied for class {c}"),
        Constraint::Datatype(d) => format!("Expected Datatype: {d}"),
        Constraint::NodeKind(_) => "NodeKind constraint not satisfied".to_string(),
        Constraint::MinCount(n) => format!("MinCount({n}) not satisfied"),
        Constraint::MaxCount(n) => format!("MaxCount({n}) not satisfied"),
        Constraint::In(_) => "In constraint not satisfied".to_string(),
        Constraint::HasValue(v) => format!("HasValue({v}) not satisfied"),
        Constraint::Pattern(p) => format!("Pattern({}) not satisfied", p.as_str()),
        Constraint::MinLength(n) => format!("MinLength({n}) not satisfied"),
        Constraint::MaxLength(n) => format!("MaxLength({n}) not satisfied"),
        Constraint::Range(_, l) => format!("Range constraint not satisfied for {l}"),
        Constraint::Node(_) => "Node constraint not satisfied".to_string(),
        #[cfg(feature = "sparql")]
        Constraint::Sparql(_) => String::new(),
        Constraint::Closed(_) => "Closed constraint not satisfied".to_string(),
    }
}

/// The string a message template substitutes for a term (SHACL §6.5.3): an IRI as itself, a
/// literal as its lexical form, a blank node as `_:id`.
fn lexical(term: &RdfTerm) -> String {
    term_json(term).lexical()
}

/// Resolve `{?name}` / `{$name}` in `text` for each binding.
fn interpolate(text: &str, bindings: &[(&str, Option<String>)]) -> String {
    let mut out = text.to_string();
    for (name, bound) in bindings {
        if let Some(bound) = bound {
            for sigil in ['?', '$'] {
                out = out.replace(&format!("{{{sigil}{name}}}"), bound);
            }
        }
    }
    out
}

/// A literal with `text` and `template`'s language tag, if it has one.
fn message_like(template: &Literal, text: String) -> Literal {
    match template.language() {
        Some(lang) => Literal::new_language_tagged_literal_unchecked(text, lang),
        None => Literal::new_simple_literal(text),
    }
}

/// One validation, over a parsed data graph.
struct Run<'a> {
    compiled: &'a Compiled,
    data: Graph,
    #[cfg(feature = "sparql")]
    store: Option<Store>,
    #[cfg(feature = "sparql")]
    token: CancellationToken,
    /// The work taken so far, data parse included.
    work: Work,
    /// Each class's subclasses (itself included), computed once.
    subclasses: HashMap<NamedNode, HashSet<RdfTerm>>,
    /// Whether a node conforms to a shape, for `sh:node`: filled bottom-up by [`Run::prepare`].
    conforms: HashMap<(RdfTerm, ShapeId), bool>,
}

impl Run<'_> {
    /// Past the time budget (with `sparql`), the evaluation is told to stop here.
    #[cfg(feature = "sparql")]
    fn canceled(&self) -> Result<()> {
        if self.token.is_cancelled() {
            return Err(Error::Endpoint(
                "urn:shacl:validate: validation canceled (past its time budget)".to_string(),
            ));
        }
        Ok(())
    }

    /// Without `sparql` there is no time budget to stop at: the work bound is the one bound.
    #[cfg(not(feature = "sparql"))]
    fn canceled(&self) -> Result<()> {
        Ok(())
    }

    /// Take `n` units of work for the data graph.
    fn charge(&mut self, n: usize) -> Result<()> {
        self.work.charge(n as u64, "data")
    }

    /// The value nodes of `shape` at `focus`: the focus itself for a node shape, its values
    /// along the predicate for a property shape. One unit of work each, and one for the walk.
    fn values(&mut self, focus: &RdfTerm, shape: &Shape) -> Result<Vec<RdfTerm>> {
        let values: Vec<RdfTerm> = match &shape.path {
            None => vec![focus.clone()],
            Some(p) => match as_node(focus.as_ref()) {
                Some(node) => self
                    .data
                    .objects_for_subject_predicate(&node, p)
                    .map(TermRef::into_owned)
                    .collect(),
                None => Vec::new(),
            },
        };
        self.charge(values.len() + 1)?;
        Ok(values)
    }

    /// `class` and every class below it through `rdfs:subClassOf`, walked iteratively, one unit
    /// of work per class visited.
    fn subclasses(&mut self, class: &NamedNode) -> Result<&HashSet<RdfTerm>> {
        if !self.subclasses.contains_key(class) {
            let mut seen: HashSet<RdfTerm> = HashSet::new();
            let mut todo = vec![RdfTerm::NamedNode(class.clone())];
            while let Some(c) = todo.pop() {
                self.work.charge(1, "data")?;
                if !seen.insert(c.clone()) {
                    continue;
                }
                todo.extend(
                    self.data
                        .subjects_for_predicate_object(rdfs::SUB_CLASS_OF, &c)
                        .map(|s| RdfTerm::from(s.into_owned())),
                );
            }
            self.subclasses.insert(class.clone(), seen);
        }
        Ok(&self.subclasses[class])
    }

    /// Is `node` a SHACL instance of `class` (`rdf:type/rdfs:subClassOf*`)? One unit of work
    /// per type it has.
    fn is_instance(&mut self, node: &RdfTerm, class: &NamedNode) -> Result<bool> {
        let Some(subject) = as_node(node.as_ref()) else {
            return Ok(false);
        };
        let types: Vec<RdfTerm> = self
            .data
            .objects_for_subject_predicate(&subject, rdf::TYPE)
            .map(TermRef::into_owned)
            .collect();
        self.charge(types.len())?;
        let below = self.subclasses(class)?;
        Ok(types.iter().any(|t| below.contains(t)))
    }

    /// The focus nodes of a shape's targets, deduplicated, in a deterministic order. One unit
    /// of work per node a target finds.
    fn focus_nodes(&mut self, shape: ShapeId) -> Result<Vec<RdfTerm>> {
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        let compiled = self.compiled;
        for target in &compiled.shapes[shape].targets {
            let found: Vec<RdfTerm> = match target {
                Target::Node(n) => vec![n.clone()],
                Target::Class(c) => {
                    let classes: Vec<RdfTerm> = self.subclasses(c)?.iter().cloned().collect();
                    classes
                        .iter()
                        .flat_map(|cls| {
                            self.data
                                .subjects_for_predicate_object(rdf::TYPE, cls)
                                .map(|s| RdfTerm::from(s.into_owned()))
                        })
                        .collect()
                }
                Target::SubjectsOf(p) => self
                    .data
                    .triples_for_predicate(p)
                    .map(|t| RdfTerm::from(t.subject.into_owned()))
                    .collect(),
                Target::ObjectsOf(p) => self
                    .data
                    .triples_for_predicate(p)
                    .map(|t| t.object.into_owned())
                    .collect(),
            };
            self.charge(found.len())?;
            let mut found = found;
            found.sort_by_key(|t| t.to_string());
            for f in found {
                if seen.insert(f.clone()) {
                    out.push(f);
                }
            }
        }
        Ok(out)
    }

    /// The `(node, shape)` pairs a validation of `shape` at `focus` asks `sh:node` about,
    /// through its property shapes (an explicit work list, not a recursion).
    fn node_questions(
        &mut self,
        focus: &RdfTerm,
        shape: ShapeId,
    ) -> Result<Vec<(RdfTerm, ShapeId)>> {
        let compiled = self.compiled;
        let mut out = Vec::new();
        let mut todo = vec![(focus.clone(), shape)];
        while let Some((v, x)) = todo.pop() {
            let s = &compiled.shapes[x];
            let values = self.values(&v, s)?;
            for c in &s.constraints {
                if let Constraint::Node(t) = c {
                    out.extend(values.iter().map(|w| (w.clone(), *t)));
                }
            }
            for &p in &s.properties {
                todo.extend(values.iter().map(|w| (w.clone(), p)));
            }
        }
        Ok(out)
    }

    /// Answer every `sh:node` question a validation of `shape` at `focus` will ask, bottom-up
    /// from an explicit stack. Each question's shape sits strictly below the shape asking it
    /// (a cycle of references was refused), so this ends, and when a pair is finished every
    /// question it asks is already answered.
    fn prepare(&mut self, focus: &RdfTerm, shape: ShapeId) -> Result<()> {
        let mut stack: Vec<(RdfTerm, ShapeId, bool)> = self
            .node_questions(focus, shape)?
            .into_iter()
            .map(|(v, s)| (v, s, false))
            .collect();
        while let Some((v, s, expanded)) = stack.pop() {
            self.charge(1)?;
            if self.conforms.contains_key(&(v.clone(), s)) {
                continue;
            }
            if expanded {
                self.canceled()?;
                let mut results = Vec::new();
                self.evaluate(&v, s, &mut results)?;
                self.conforms.insert((v, s), results.is_empty());
            } else {
                let questions = self.node_questions(&v, s)?;
                stack.push((v, s, true));
                stack.extend(
                    questions
                        .into_iter()
                        .filter(|q| !self.conforms.contains_key(q))
                        .map(|(w, t)| (w, t, false)),
                );
            }
        }
        Ok(())
    }

    /// Validate `focus` against `shape`, appending its results: the shape's own constraints,
    /// and those of its property shapes at its value nodes (an explicit work list). Every
    /// `sh:node` question must already be answered ([`Run::prepare`]).
    fn evaluate(&mut self, focus: &RdfTerm, shape: ShapeId, out: &mut Vec<Res>) -> Result<()> {
        let compiled = self.compiled;
        let mut todo = vec![(focus.clone(), shape)];
        while let Some((v, x)) = todo.pop() {
            let s = &compiled.shapes[x];
            let values = self.values(&v, s)?;
            for c in &s.constraints {
                self.apply(c, s, &v, &values, out)?;
            }
            for &p in s.properties.iter().rev() {
                todo.extend(values.iter().rev().map(|w| (w.clone(), p)));
            }
        }
        Ok(())
    }

    /// One constraint of `shape` at `focus`, whose value nodes are `values`.
    fn apply(
        &mut self,
        c: &Constraint,
        shape: &Shape,
        focus: &RdfTerm,
        values: &[RdfTerm],
        out: &mut Vec<Res>,
    ) -> Result<()> {
        // Each failure's value, and its result path: the shape's own, except for `sh:closed`.
        let mut failed: Vec<(Option<RdfTerm>, Option<NamedNode>)> = Vec::new();
        match c {
            Constraint::MinCount(n) => {
                if (values.len() as u64) < *n {
                    failed.push((None, shape.path.clone()));
                }
            }
            Constraint::MaxCount(n) => {
                if (values.len() as u64) > *n {
                    failed.push((None, shape.path.clone()));
                }
            }
            Constraint::HasValue(t) => {
                if !values.contains(t) {
                    failed.push((None, shape.path.clone()));
                }
            }
            #[cfg(feature = "sparql")]
            Constraint::Sparql(q) => return self.sparql(q, shape, focus, out),
            // One result per triple whose predicate is not allowed, with that predicate as the
            // result path and its object as the value (SHACL §4.8.1, and rudof's report).
            Constraint::Closed(allowed) => {
                for w in values {
                    let Some(node) = as_node(w.as_ref()) else {
                        continue;
                    };
                    let mut scanned = 0;
                    for t in self.data.triples_for_subject(&node) {
                        scanned += 1;
                        let predicate = t.predicate.into_owned();
                        if !allowed.contains(&predicate) {
                            failed.push((Some(t.object.into_owned()), Some(predicate)));
                        }
                    }
                    self.charge(scanned)?;
                }
            }
            _ => {
                for w in values {
                    if !self.holds(c, w)? {
                        failed.push((Some(w.clone()), shape.path.clone()));
                    }
                }
            }
        }
        for (value, path) in failed {
            let messages = if shape.messages.is_empty() {
                vec![Literal::new_simple_literal(default_message(c))]
            } else {
                shape.messages.clone()
            };
            let bindings = [
                ("this", Some(lexical(focus))),
                ("value", value.as_ref().map(lexical)),
                ("path", path.as_ref().map(|p| p.as_str().to_string())),
            ];
            let messages = messages
                .iter()
                .map(|m| message_like(m, interpolate(m.value(), &bindings)))
                .collect();
            out.push(Res {
                focus: focus.clone(),
                path,
                component: c.component(),
                source: shape.node.clone(),
                value,
                messages,
            });
        }
        Ok(())
    }

    /// Whether value node `w` satisfies the per-value constraint `c`. One unit of work, one more
    /// per `sh:in` member compared, and one per byte of the text `sh:pattern`, `sh:minLength` or
    /// `sh:maxLength` reads.
    fn holds(&mut self, c: &Constraint, w: &RdfTerm) -> Result<bool> {
        self.charge(1)?;
        Ok(match c {
            Constraint::Class(class) => {
                !matches!(w, RdfTerm::Literal(_)) && self.is_instance(w, class)?
            }
            Constraint::Datatype(d) => match w {
                RdfTerm::Literal(l) => l.datatype() == d.as_ref() && well_formed(l),
                _ => false,
            },
            Constraint::NodeKind(kind) => {
                let (iri, blank, literal) = (w.is_named_node(), w.is_blank_node(), w.is_literal());
                match kind {
                    NodeKind::Iri => iri,
                    NodeKind::BlankNode => blank,
                    NodeKind::Literal => literal,
                    NodeKind::BlankNodeOrIri => blank || iri,
                    NodeKind::BlankNodeOrLiteral => blank || literal,
                    NodeKind::IriOrLiteral => iri || literal,
                }
            }
            Constraint::In(members) => {
                self.charge(members.len())?;
                members.contains(w)
            }
            Constraint::Pattern(re) => match string_of(w) {
                Some(s) => {
                    self.charge(s.len())?;
                    re.is_match(&s)
                }
                None => false,
            },
            Constraint::MinLength(n) => match string_of(w) {
                Some(s) => {
                    self.charge(s.len())?;
                    s.chars().count() as u64 >= *n
                }
                None => false,
            },
            Constraint::MaxLength(n) => match string_of(w) {
                Some(s) => {
                    self.charge(s.len())?;
                    s.chars().count() as u64 <= *n
                }
                None => false,
            },
            Constraint::Range(range, bound) => match w {
                RdfTerm::Literal(l) => match compare(l, bound) {
                    Some(order) => match range {
                        Range::MinInclusive => order.is_ge(),
                        Range::MaxInclusive => order.is_le(),
                        Range::MinExclusive => order.is_gt(),
                        Range::MaxExclusive => order.is_lt(),
                    },
                    None => false,
                },
                _ => false,
            },
            Constraint::Node(t) => *self.conforms.get(&(w.clone(), *t)).ok_or_else(|| {
                Error::Endpoint(
                    "urn:shacl:validate: a `sh:node` question was not answered before it \
                         was asked (a defect in the subset validator)"
                        .to_string(),
                )
            })?,
            Constraint::MinCount(_)
            | Constraint::MaxCount(_)
            | Constraint::HasValue(_)
            | Constraint::Closed(_) => true,
            #[cfg(feature = "sparql")]
            Constraint::Sparql(_) => true,
        })
    }

    /// A `sh:sparql` constraint at `focus`: one result per solution, as SHACL-SPARQL defines
    /// (and rudof reports): `?this` (else the focus) is the focus node, `?path` (an IRI, else the
    /// shape's path) the result path, `?value` (else the focus) the value, and `?message` or the
    /// constraint's `sh:message`, with every `{?var}` resolved from the solution, the message.
    /// A solution binding `?failure` to true is a failure of the validation itself.
    #[cfg(feature = "sparql")]
    fn sparql(
        &mut self,
        q: &SparqlConstraint,
        shape: &Shape,
        focus: &RdfTerm,
        out: &mut Vec<Res>,
    ) -> Result<()> {
        let store = self.store.as_ref().ok_or_else(|| {
            Error::Endpoint("urn:shacl:validate: no store for a SPARQL constraint".to_string())
        })?;
        let failed = |e: &dyn std::fmt::Display| {
            Error::Endpoint(format!(
                "urn:shacl:validate: a `sh:sparql` constraint failed to evaluate: {e}"
            ))
        };
        let results = ikigai_store::service::evaluator()
            .with_cancellation_token(self.token.clone())
            .for_query(q.query.clone())
            .on_store(store)
            .substitute_variable(Variable::new_unchecked("this"), focus.clone())
            .execute()
            .map_err(|e| failed(&e))?;
        let QueryResults::Solutions(solutions) = results else {
            return Err(failed(&"the query is not a SELECT"));
        };
        let variables: Vec<Variable> = solutions.variables().to_vec();
        for solution in solutions {
            let solution = solution.map_err(|e| failed(&e))?;
            if let Some(RdfTerm::Literal(l)) = solution.get("failure") {
                if l.datatype() == xsd::BOOLEAN && matches!(l.value(), "true" | "1") {
                    return Err(failed(&"the constraint reported ?failure"));
                }
            }
            let this = solution
                .get("this")
                .cloned()
                .unwrap_or_else(|| focus.clone());
            let path = match solution.get("path") {
                Some(RdfTerm::NamedNode(p)) => Some(p.clone()),
                _ => shape.path.clone(),
            };
            let value = solution
                .get("value")
                .cloned()
                .unwrap_or_else(|| focus.clone());
            let messages = match solution.get("message") {
                Some(RdfTerm::Literal(l)) => vec![l.clone()],
                Some(other) => vec![Literal::new_simple_literal(other.to_string())],
                None => {
                    let mut bindings: Vec<(&str, Option<String>)> = variables
                        .iter()
                        .map(|v| (v.as_str(), solution.get(v.as_str()).map(lexical)))
                        .collect();
                    if solution.get("this").is_none() {
                        bindings.push(("this", Some(lexical(focus))));
                    }
                    q.messages
                        .iter()
                        .map(|m| message_like(m, interpolate(m.value(), &bindings)))
                        .collect()
                }
            };
            out.push(Res {
                focus: this,
                path,
                component: "SPARQLConstraintComponent",
                source: shape.node.clone(),
                value: Some(value),
                messages,
            });
        }
        Ok(())
    }
}

/// The string `sh:pattern`, `sh:minLength` and `sh:maxLength` read: an IRI or a literal's
/// lexical form; a blank node (or a triple term) has none, and fails them.
fn string_of(term: &RdfTerm) -> Option<String> {
    match term {
        RdfTerm::NamedNode(n) => Some(n.as_str().to_string()),
        RdfTerm::Literal(l) => Some(l.value().to_string()),
        _ => None,
    }
}

const INTEGER_TYPES: &[(&str, Option<i128>, Option<i128>)] = &[
    ("integer", None, None),
    ("nonPositiveInteger", None, Some(0)),
    ("negativeInteger", None, Some(-1)),
    ("nonNegativeInteger", Some(0), None),
    ("positiveInteger", Some(1), None),
    ("long", Some(i64::MIN as i128), Some(i64::MAX as i128)),
    ("int", Some(i32::MIN as i128), Some(i32::MAX as i128)),
    ("short", Some(i16::MIN as i128), Some(i16::MAX as i128)),
    ("byte", Some(i8::MIN as i128), Some(i8::MAX as i128)),
    ("unsignedLong", Some(0), Some(u64::MAX as i128)),
    ("unsignedInt", Some(0), Some(u32::MAX as i128)),
    ("unsignedShort", Some(0), Some(u16::MAX as i128)),
    ("unsignedByte", Some(0), Some(u8::MAX as i128)),
];

const XSD: &str = "http://www.w3.org/2001/XMLSchema#";

/// Is `literal`'s lexical form in its datatype's lexical space? Checked for the XSD numeric,
/// boolean, date and time and duration types; any other datatype is taken as well-formed.
fn well_formed(literal: &Literal) -> bool {
    use std::str::FromStr;
    let value = literal.value();
    let Some(local) = literal.datatype().as_str().strip_prefix(XSD) else {
        return true;
    };
    if let Some((_, min, max)) = INTEGER_TYPES.iter().find(|(name, _, _)| *name == local) {
        let digits = value.strip_prefix(['+', '-']).unwrap_or(value);
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return false;
        }
        let negative = value.starts_with('-') && digits.bytes().any(|b| b != b'0');
        return match value.parse::<i128>() {
            Ok(n) => min.is_none_or(|m| n >= m) && max.is_none_or(|m| n <= m),
            // Beyond i128: within every unbounded type whose sign it has.
            Err(_) => match local {
                "integer" => true,
                "nonNegativeInteger" | "positiveInteger" => !negative,
                "nonPositiveInteger" | "negativeInteger" => negative,
                _ => false,
            },
        };
    }
    match local {
        "decimal" => oxsdatatypes::Decimal::from_str(value).is_ok(),
        "double" => oxsdatatypes::Double::from_str(value).is_ok(),
        "float" => oxsdatatypes::Float::from_str(value).is_ok(),
        "boolean" => matches!(value, "true" | "false" | "1" | "0"),
        "dateTime" => oxsdatatypes::DateTime::from_str(value).is_ok(),
        "date" => oxsdatatypes::Date::from_str(value).is_ok(),
        "time" => oxsdatatypes::Time::from_str(value).is_ok(),
        "duration" => oxsdatatypes::Duration::from_str(value).is_ok(),
        "dayTimeDuration" => oxsdatatypes::DayTimeDuration::from_str(value).is_ok(),
        "yearMonthDuration" => oxsdatatypes::YearMonthDuration::from_str(value).is_ok(),
        _ => true,
    }
}

/// A literal's value where SPARQL's `<` compares it: a number, a string, or a date/time.
enum Comparable {
    Decimal(oxsdatatypes::Decimal),
    Double(oxsdatatypes::Double),
    String(String),
    DateTime(oxsdatatypes::DateTime),
    Date(oxsdatatypes::Date),
    Time(oxsdatatypes::Time),
}

fn comparable(literal: &Literal) -> Option<Comparable> {
    use std::str::FromStr;
    if !well_formed(literal) {
        return None;
    }
    let value = literal.value();
    let datatype = literal.datatype();
    if datatype == xsd::STRING {
        return Some(Comparable::String(value.to_string()));
    }
    let local = datatype.as_str().strip_prefix(XSD)?;
    if INTEGER_TYPES.iter().any(|(name, _, _)| *name == local) || local == "decimal" {
        return oxsdatatypes::Decimal::from_str(value.trim_start_matches('+'))
            .ok()
            .map(Comparable::Decimal);
    }
    match local {
        "double" => oxsdatatypes::Double::from_str(value)
            .ok()
            .map(Comparable::Double),
        "float" => oxsdatatypes::Float::from_str(value)
            .ok()
            .map(|f| Comparable::Double(f.into())),
        "dateTime" => oxsdatatypes::DateTime::from_str(value)
            .ok()
            .map(Comparable::DateTime),
        "date" => oxsdatatypes::Date::from_str(value)
            .ok()
            .map(Comparable::Date),
        "time" => oxsdatatypes::Time::from_str(value)
            .ok()
            .map(Comparable::Time),
        _ => None,
    }
}

/// How `a` compares to `b` under SPARQL's operators, or `None` when they are incomparable (which
/// fails every range constraint, as SHACL says).
fn compare(a: &Literal, b: &Literal) -> Option<std::cmp::Ordering> {
    use Comparable::*;
    match (comparable(a)?, comparable(b)?) {
        (Decimal(x), Decimal(y)) => Some(x.cmp(&y)),
        (Decimal(x), Double(y)) => oxsdatatypes::Double::from(x).partial_cmp(&y),
        (Double(x), Decimal(y)) => x.partial_cmp(&oxsdatatypes::Double::from(y)),
        (Double(x), Double(y)) => x.partial_cmp(&y),
        (String(x), String(y)) => Some(x.cmp(&y)),
        (DateTime(x), DateTime(y)) => x.partial_cmp(&y),
        (Date(x), Date(y)) => x.partial_cmp(&y),
        (Time(x), Time(y)) => x.partial_cmp(&y),
        _ => None,
    }
}

/// The one budget every validation in the process shares, by either validator (the rudof path
/// runs in it too since ledger #1735), so its overdue count caps the cores runaway validations
/// can hold (`EvaluationBudget`: "make ONE per host and clone it"). The store's time defaults:
/// 5 s for an ordinary caller, more only by a `urn:cap:store:budget:<ms>` grant, the 120 s
/// ceiling for root. The overdue cap is this crate's own: [`MAX_OVERDUE_FLOOR`] (ledger
/// #1510), and so are the reserve and the caller share (ledger #1002), see
/// [`caller_share`].
#[cfg(feature = "sparql")]
pub(crate) fn budget() -> &'static EvaluationBudget {
    static BUDGET: OnceLock<EvaluationBudget> = OnceLock::new();
    BUDGET.get_or_init(|| {
        EvaluationBudget::new(
            TimeBudget::new(DEFAULT_BUDGET)
                .with_max_overdue(max_overdue())
                .with_reserve(0)
                .with_caller_share(caller_share()),
        )
    })
}

/// The budget's reserve and per-caller share, stated so that the overdue cap means what it
/// meant through ikigai-store 0.2.23: NO slot reserved for the host, and each caller may use
/// the whole cap ([`max_overdue`], at least [`MAX_OVERDUE_FLOOR`]).
///
/// ★ Why this crate states them (ledger #1002, after #1500/#1510). ikigai-store 0.2.24 split a
/// budget's cap: a RESERVE only root and `urn:cap:store:reserve` may use (default 1), and of
/// what is left, a SHARE per caller (default half, at least 1), where every capability that
/// names no principal, every library call and anonymous request among them, is ONE caller. At
/// this crate's cap of 2 those defaults leave a caller one slot, so one runaway `sh:select`
/// refused every later validation by the same caller, which on a small host was everyone again:
/// the failure [`MAX_OVERDUE_FLOOR`] exists to prevent, back through a new door
/// (`tests/one_runaway.rs` went red on a fresh resolve the day 0.2.24 shipped). Brian's rule
/// stands: the store's defaults stay, and a consumer states its own.
///
/// No reserve, because the reserve keeps room for a host's OWN reads of a store (its backup,
/// its jobs), and this budget is this crate's own and only ever runs validations: a reserve
/// here would keep one of two cores idle for a root validation. The whole cap as the share,
/// because the cap was sized (the measurement on [`MAX_OVERDUE_FLOOR`]) as what ONE caller
/// needs to keep answering through one runaway, and `tests/rudof_time_budget.rs` pins that a
/// caller may fill the cap and only the one past it is refused. A smaller share per principal
/// (so that one caller's runaways cannot crowd out another's) is a new policy, not this fix.
#[cfg(feature = "sparql")]
fn caller_share() -> usize {
    max_overdue()
}

/// The fewest validations that may be in flight, and so overdue, at once: TWO, so one
/// runaway `sh:select` cannot refuse every later validation in the process (ledger #1510).
///
/// ★ Why this crate states its own cap. The store's default is a quarter of the machine's
/// available parallelism, at least one, and since ikigai-store 0.2.21 (ledger #1427) a budget
/// at its cap refuses every new evaluation with `Unavailable` while that many are overdue. On
/// any host with fewer than 8 cores that cap is ONE, so a single caller's slow shapes graph
/// (a cross product oxigraph cannot cancel, minutes of work) disabled SHACL for every caller
/// until it ended (ledger #1500). Brian's call there: the store default stays, and a consumer
/// states its own.
///
/// Why two, measured 2026-10-14 (debug build, this crate's subset validator, one runaway
/// six-way cross product left overdue, then 16 concurrent ordinary validations, each a typed
/// node, one property shape and a cheap `sh:select`): at a cap of 1, which is what a four-core
/// CI runner gets, 0 of 16 answered; at 2, 16 of 16, the slowest in 4.8 ms; at 3 and 4, 16 of
/// 16 again, at most 2.4 ms sooner. An ordinary validation takes milliseconds, so one free slot
/// is plenty, and more slots buy only tolerance for MORE runaways, each pinning a core: at 3 on
/// a four-core host, three runaways would hold three of its four cores. Two is the least that
/// keeps validation answering through one runaway, and at most half of a four-core host. Two
/// runaways at a cap of 2 refuse again (0 of 16, measured), and that bound is the point: the
/// cap is what stops each new request pinning another core.
///
/// What it costs: the cap is also how many validations RUN at once (the store reserves a slot
/// per evaluation), so a small host now validates two at a time instead of one; and on a one-
/// or two-core host two runaways can hold every core, where the store's default held one.
/// Above 8 cores the store's own default is already at least 2, and it is kept, so a large
/// host is unchanged.
#[cfg(feature = "sparql")]
const MAX_OVERDUE_FLOOR: usize = 2;

/// [`MAX_OVERDUE_FLOOR`], or the store's default when that is larger.
#[cfg(feature = "sparql")]
fn max_overdue() -> usize {
    default_max_overdue().max(MAX_OVERDUE_FLOOR)
}

/// Validate: compile the shapes (iteratively, on the caller's thread, each `sh:select` parsed
/// on a thread sized for it), then validate the data inside the time budget, on a thread sized
/// for the longest query, and return the results.
#[cfg(feature = "sparql")]
fn run(data_ttl: &str, shapes_ttl: &str, capability: &Capability) -> Result<(bool, Vec<Res>)> {
    let mut work = Work::default();
    let compiled = compile(shapes_ttl, &mut work)?;
    let longest = compiled.longest_query.clone();
    let data_ttl = data_ttl.to_string();
    budget().run(&longest, capability, None, move |token| {
        let triples = parse_turtle(&data_ttl, "data", &mut work)?;
        let store = if compiled.has_sparql {
            let store = Store::new().map_err(|e| {
                Error::Endpoint(format!("urn:shacl:validate: could not open a store: {e}"))
            })?;
            for t in &triples {
                store
                    .insert(QuadRef::new(
                        t.subject.as_ref(),
                        t.predicate.as_ref(),
                        t.object.as_ref(),
                        GraphNameRef::DefaultGraph,
                    ))
                    .map_err(|e| Error::Endpoint(format!("urn:shacl:validate: data graph: {e}")))?;
            }
            Some(store)
        } else {
            None
        };
        let run = Run {
            compiled: &compiled,
            data: graph_of(&triples),
            store,
            token: token.clone(),
            work,
            subclasses: HashMap::new(),
            conforms: HashMap::new(),
        };
        validate_all(run)
    })
}

/// Validate without `sparql`: on the caller's thread (nothing here recurses), within
/// [`MAX_VALIDATION_WORK`] rather than a time budget, so `capability` decides nothing.
#[cfg(not(feature = "sparql"))]
fn run(data_ttl: &str, shapes_ttl: &str, _capability: &Capability) -> Result<(bool, Vec<Res>)> {
    let mut work = Work::default();
    let compiled = compile(shapes_ttl, &mut work)?;
    let triples = parse_turtle(data_ttl, "data", &mut work)?;
    let run = Run {
        compiled: &compiled,
        data: graph_of(&triples),
        work,
        subclasses: HashMap::new(),
        conforms: HashMap::new(),
    };
    validate_all(run)
}

/// Every focus node of every shape with a target, in a deterministic order.
fn validate_all(mut run: Run<'_>) -> Result<(bool, Vec<Res>)> {
    let compiled = run.compiled;
    let mut results = Vec::new();
    for &root in &compiled.roots {
        for focus in run.focus_nodes(root)? {
            run.canceled()?;
            run.prepare(&focus, root)?;
            run.evaluate(&focus, root, &mut results)?;
        }
    }
    Ok((results.is_empty(), results))
}

// ---------------------------------------------------------------------------------------------
// The two faces.
// ---------------------------------------------------------------------------------------------

/// An RDF term as the report's [`Term`]. Never a triple term: [`parse_turtle`] refuses those.
///
/// ⚠ Written with `if let` rather than one `match`, and so is every other test of a term's kind
/// here: oxrdf's `Term::Triple` exists only under its `rdf-12` feature, which any crate in the
/// final graph can turn on (rudof does), so an exhaustive match fails to compile in one build or
/// the other.
fn term_json(term: &RdfTerm) -> Term {
    if let RdfTerm::NamedNode(n) = term {
        Term::Uri {
            value: n.as_str().to_string(),
        }
    } else if let RdfTerm::BlankNode(b) = term {
        Term::Bnode {
            value: b.as_str().to_string(),
        }
    } else if let RdfTerm::Literal(l) = term {
        let lang = l.language().map(str::to_string);
        let datatype = match lang {
            Some(_) => None,
            None => Some(l.datatype().as_str().to_string()).filter(|dt| dt != xsd::STRING.as_str()),
        };
        Term::Literal {
            value: l.value().to_string(),
            lang,
            datatype,
        }
    } else {
        Term::Uri {
            value: term.to_string(),
        }
    }
}

/// A focus node as the JSON face names it: an IRI bare, a blank node as `_:id`.
fn focus_string(term: &RdfTerm) -> String {
    match term {
        RdfTerm::NamedNode(n) => n.as_str().to_string(),
        other => other.to_string(),
    }
}

/// The one message the JSON face reports: tagged beats untagged, then the lowest tag (the rule
/// the rudof path applies).
fn message_term(messages: &[Literal]) -> Option<Term> {
    let mut all: Vec<(bool, Option<&str>, &str)> = messages
        .iter()
        .map(|m| (m.language().is_none(), m.language(), m.value()))
        .collect();
    all.sort();
    let (_, lang, text) = all.into_iter().next()?;
    Some(Term::Literal {
        value: text.to_string(),
        lang: lang.map(str::to_string),
        datatype: None,
    })
}

fn report(conforms: bool, results: &[Res]) -> Report {
    let mut violations: Vec<ReportResult> = results
        .iter()
        .map(|r| ReportResult {
            focus_node: focus_string(&r.focus),
            path: r.path.as_ref().map(|p| p.as_str().to_string()),
            component: format!("{SH}{}", r.component),
            message: message_term(&r.messages),
            value: r.value.as_ref().map(term_json),
        })
        .collect();
    violations.sort();
    Report {
        conforms,
        violations,
    }
}

/// The report graph, skolemized as the rudof path's is (see [`crate::REPORT_SCHEME`]): the
/// nodes this module mints, `report` and `result.N` (results in the validator's own order,
/// which is deterministic), and those passed through from the shapes and data graphs, already
/// labeled `shapes.bN`/`data.bN` as they were parsed, so no two sources' labels collide.
fn report_graph(conforms: bool, results: &[Res]) -> Vec<Triple> {
    let report_node = BlankNode::new_unchecked("report");
    let mut triples: Vec<Triple> = vec![
        Triple::new(
            report_node.clone(),
            rdf::TYPE.into_owned(),
            sh("ValidationReport"),
        ),
        Triple::new(report_node.clone(), sh("conforms"), Literal::from(conforms)),
    ];
    for (i, r) in results.iter().enumerate() {
        let node = BlankNode::new_unchecked(format!("result.{i}"));
        triples.push(Triple::new(report_node.clone(), sh("result"), node.clone()));
        let mut push = |p: NamedNode, o: RdfTerm| triples.push(Triple::new(node.clone(), p, o));
        push(rdf::TYPE.into_owned(), sh("ValidationResult").into());
        push(sh("focusNode"), r.focus.clone());
        push(sh("sourceConstraintComponent"), sh(r.component).into());
        push(sh("resultSeverity"), sh("Violation").into());
        for m in &r.messages {
            push(sh("resultMessage"), m.clone().into());
        }
        push(sh("sourceShape"), r.source.clone().into());
        if let Some(p) = &r.path {
            push(sh("resultPath"), p.clone().into());
        }
        if let Some(v) = &r.value {
            push(sh("value"), v.clone());
        }
    }
    triples
}

/// The report graph as Turtle, skolemized and sorted (see [`crate::naming`]).
fn turtle(conforms: bool, results: &[Res]) -> Result<String> {
    naming::turtle(&naming::skolemize(report_graph(conforms, results))?)
}

/// The capability a library call (no invocation) validates under: none, so the base budget.
pub(crate) fn library_capability() -> Capability {
    Capability::scoped(Vec::<String>::new())
}

/// Validate `data_ttl` against `shapes_ttl` with the subset validator, returning the full
/// [`Report`] (the `application/json` face) — the same shape, field for field, as the rudof
/// path's. With the `sparql` feature it runs within the base time budget; without it, within
/// [`MAX_VALIDATION_WORK`].
pub fn validate_report(data_ttl: &str, shapes_ttl: &str) -> Result<Report> {
    let (conforms, results) = run(data_ttl, shapes_ttl, &library_capability())?;
    Ok(report(conforms, &results))
}

/// Validate with the subset validator, returning the skolemized report graph as Turtle (the
/// `text/turtle` face).
pub fn validate_turtle(data_ttl: &str, shapes_ttl: &str) -> Result<String> {
    let (conforms, results) = run(data_ttl, shapes_ttl, &library_capability())?;
    turtle(conforms, &results)
}

/// The endpoint's rendering, for a build without rudof: `capability` is the caller's, and
/// decides the time budget (with `sparql`; without it, the work bound applies to every caller).
// With rudof compiled the endpoint uses rudof, so this is reached only from a build without it.
#[cfg_attr(feature = "rudof", allow(dead_code))]
pub(crate) fn validate(
    data_ttl: &str,
    shapes_ttl: &str,
    as_type: &str,
    capability: &Capability,
) -> Result<Representation> {
    let (conforms, results) = run(data_ttl, shapes_ttl, capability)?;
    if as_type.split(';').next().unwrap_or("").trim() == JSON {
        Ok(repr(
            JSON,
            serde_json::to_string_pretty(&report(conforms, &results))
                .map_err(|e| Error::Endpoint(format!("urn:shacl:validate: json error: {e}")))?,
        ))
    } else {
        Ok(repr(TURTLE, turtle(conforms, &results)?))
    }
}
