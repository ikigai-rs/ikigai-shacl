//! Caller RDF is bounded in DEPTH before anything recursive touches it (ledger #992).
//!
//! Ledger #963 bounded the SPARQL a shapes graph carries. What it left open is depth that is
//! not SPARQL at all, and each of these aborted the whole process from a small input through
//! `urn:shacl:validate` (reproduced in a child process, `tests/sparql_stack.rs`):
//!
//! - **rudof compiles shapes recursively.** `IRSchema::register_shape` recurses once per
//!   nested shape (`sh:not`, `sh:and`, `sh:or`, `sh:xone`, `sh:node`, `sh:property`,
//!   `sh:qualifiedValueShape`, `sh:reifierShape`): 300 levels of `sh:not` (about 3 KB) or a
//!   300-shape `sh:node` chain aborted a 2 MiB thread in a debug build.
//! - **rudof parses a `sh:path` recursively and keeps no visited set**, so one blank node that
//!   is its own operand (`_:p sh:inversePath _:p`) recursed until the stack ran out, and a
//!   3000-level path did the same.
//! - **rudof follows `sh:prefixes` along `owl:imports` recursively**: a 3000-link chain aborted.
//! - **oxrdf clones a nested RDF 1.2 triple term recursively**, inside oxttl's Turtle parser:
//!   3000 levels of `<<( … )>>` aborted, in `data` and `shapes` alike.
//!
//! So, as for SPARQL, two layers:
//!
//! 1. [`check_turtle_nesting`] scans caller Turtle for `<<` nesting BEFORE it is parsed, and
//!    [`check_shapes_structure`] walks the parsed shapes graph, iteratively, BEFORE rudof's
//!    shape parser sees it. Each refuses past its bound as a typed `InvalidArgument` naming
//!    the argument.
//! 2. Compiling the shapes runs on a sized stack as validation already did (see `run` in the
//!    crate root), because LENGTH recurses too: rudof parses an RDF list one call per
//!    element, and a 3000-element `sh:in` aborted a 2 MiB thread. Length is what real data
//!    has, so it is not refused; the stack grows with the text instead.
//!
//! ⚠ The walk mirrors rudof 0.3.24's recursion sites (`ir/schema.rs`, `ir/component.rs`,
//! `ir/node_shape.rs`, `ir/property_shape.rs`, `ir/reifier_info.rs`, rudof_rdf's
//! `constructors/shacl.rs` and `sparql/basic.rs`'s `collect_prefixes`). The rudof upper bound
//! in Cargo.toml is what keeps that mirror true; raising it means re-reading those.
//!
//! ⚠ Not bounded here: validation that recurses along the DATA. A recursive shape
//! (`sh:property [ sh:path ex:next ; sh:node ex:S ]`) over a data chain recurses once per link
//! at validation time; that is a property of the data, not of the shapes graph's structure.

use ikigai_core::{Error, Result};
use rudof_rdf::rdf_core::term::{Object, Triple as _};
use rudof_rdf::rdf_core::{NeighsRDF, Rdf};
use sparql_service::RdfData;
use std::collections::{HashMap, HashSet};

/// How deep caller Turtle may nest RDF 1.2 triple terms and reified triples (`<<( … )>>`,
/// `<< … >>`), counted per `<<`. The same number as `ikigai_store::limits::MAX_SPARQL_NESTING`:
/// one bound on caller nesting across the doors. Real data nests these a handful deep; a
/// debug build survived 300 levels on a 2 MiB thread and aborted at 3000.
pub const MAX_TURTLE_NESTING: usize = 64;

/// How deep the shapes graph may nest, counted in NODES along the longest chain of shape
/// references and path operators, a recursive group counting all its shapes. The same 64, and
/// far from both ends: the deepest shapes graphs in the ecosystem measure 5 (ikigai-vocab's
/// `shapes.ttl` and ikigai-core's `fn.shape.ttl`, 2026-10-10, by the ignored `measure` test;
/// this crate's parity corpus is 3), while a debug build compiled 100 levels of `sh:not` on a
/// 2 MiB thread and aborted at 300, and compiling now runs on 16 MiB or more.
pub const MAX_SHAPE_DEPTH: usize = 64;

/// Refuse caller Turtle that nests `<<` deeper than [`MAX_TURTLE_NESTING`], without parsing it.
///
/// The scan reads the text as oxttl 0.2's lexer does (`lexer.rs`), in the parts that decide
/// what is code: strings in all four quote forms, closing at the FIRST unescaped delimiter (a
/// long string at the first triple, a short one even across a line end), `<…>` IRIs as
/// everything up to the first `>`, `#` comments to the line end, and `\`-escapes. So a `<<`
/// inside a literal, an IRI or a comment is text, not nesting. Where the text is not Turtle the reading may differ from the
/// parser's, and that is safe: rudof's `ReaderMode::Strict` stops at the parser's first
/// error, so only the text before it is ever built into terms, and there the two agree.
pub fn check_turtle_nesting(text: &str, arg: &str) -> Result<()> {
    let b = text.as_bytes();
    let at = |i: usize| b.get(i).copied();
    let mut depth = 0usize;
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'#' => {
                while i < b.len() && b[i] != b'\n' && b[i] != b'\r' {
                    i += 1;
                }
            }
            q @ (b'"' | b'\'') => {
                if at(i + 1) == Some(q) && at(i + 2) == Some(q) {
                    // A long string: ends at the first unescaped triple quote.
                    i += 3;
                    while i < b.len() {
                        if b[i] == b'\\' {
                            i += 2;
                        } else if b[i] == q && at(i + 1) == Some(q) && at(i + 2) == Some(q) {
                            i += 3;
                            break;
                        } else {
                            i += 1;
                        }
                    }
                } else {
                    // A short string: ends at the quote, and NOT at a line end, which Turtle
                    // forbids but oxttl's `lenient()` lexer (lexer.rs:674) reads straight
                    // through. Stopping there would take the real closing quote for an
                    // opening one and hide what follows it.
                    i += 1;
                    while i < b.len() {
                        match b[i] {
                            b'\\' => i += 2,
                            c if c == q => {
                                i += 1;
                                break;
                            }
                            _ => i += 1,
                        }
                    }
                }
            }
            b'<' if at(i + 1) == Some(b'<') => {
                depth += 1;
                if depth > MAX_TURTLE_NESTING {
                    return Err(Error::InvalidArgument {
                        name: arg.to_string(),
                        detail: format!(
                            "this Turtle nests RDF 1.2 triple terms (`<<( … )>>`) or reified \
                             triples (`<< … >>`) deeper than {MAX_TURTLE_NESTING} \
                             (MAX_TURTLE_NESTING): the RDF library copies a nested triple term \
                             recursively, once per level, where a stack overflow aborts the \
                             whole host"
                        ),
                    });
                }
                i += 2;
            }
            b'<' => {
                // An IRI, read as oxttl reads it: everything up to the first `>`, a `\` escaping
                // what follows. NOT only IRIREF's characters: rudof parses `lenient()`, and then
                // oxttl validates nothing inside the brackets, so `<x"> , <<( …` is one IRI and
                // then real nesting, which a stricter reading would mistake for a string.
                let mut j = i + 1;
                while j < b.len() && b[j] != b'>' {
                    j += if b[j] == b'\\' { 2 } else { 1 };
                }
                if j >= b.len() {
                    // Never closed: the parser fails here, and builds nothing after it.
                    break;
                }
                i = j + 1;
            }
            b'>' if at(i + 1) == Some(b'>') => {
                depth = depth.saturating_sub(1);
                i += 2;
            }
            // `\` outside a string is a prefixed name's escape (`ex:a\#b`): skip what it escapes.
            b'\\' => i += 2,
            _ => i += 1,
        }
    }
    Ok(())
}

const SH: &str = "http://www.w3.org/ns/shacl#";
const RDF_FIRST: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#first";
const RDF_REST: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest";
const OWL_IMPORTS: &str = "http://www.w3.org/2002/07/owl#imports";

/// What following one edge costs rudof, which decides what a CYCLE through it means.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Edge {
    /// A shape reference (or a prefix declaration's `owl:imports`). rudof records a shape
    /// before compiling it and `collect_prefixes` keeps a visited set, so a cycle is cut: it
    /// costs at most the nodes on it.
    Shape,
    /// A path operator. rudof's path parser keeps NO visited set, so a cycle never ends.
    Path,
}

/// What a predicate means to the walk.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Role {
    /// `rdf:first` / `rdf:rest`: a list cell.
    First,
    Rest,
    /// A shape reference to its object, or to each member of the list it names.
    Shape,
    ShapeList,
    /// `sh:path`: from a shape to its path.
    Path,
    /// A path operator, which rudof follows only from a BLANK path node: to its operand, or to
    /// each member of the list it names (`sh:alternativePath`).
    Operator,
    OperatorList,
}

/// The [`Role`] of `predicate`, or `None` when the walk ignores it.
fn role(predicate: &str) -> Option<Role> {
    match predicate {
        RDF_FIRST => return Some(Role::First),
        RDF_REST => return Some(Role::Rest),
        OWL_IMPORTS => return Some(Role::Shape),
        _ => {}
    }
    Some(match predicate.strip_prefix(SH)? {
        "not"
        | "node"
        | "property"
        | "qualifiedValueShape"
        | "reifierShape"
        | "sparql"
        | "prefixes" => Role::Shape,
        "and" | "or" | "xone" => Role::ShapeList,
        "path" => Role::Path,
        "inversePath" | "zeroOrMorePath" | "oneOrMorePath" | "zeroOrOnePath" => Role::Operator,
        "alternativePath" => Role::OperatorList,
        _ => return None,
    })
}

/// Refuse a shapes graph whose shape references and paths nest deeper than
/// [`MAX_SHAPE_DEPTH`], or whose paths form a cycle — walking it iteratively, before rudof's
/// recursive parser and compiler see it.
///
/// The edges are rudof's recursion sites: from any node, `sh:not`, `sh:node`, `sh:property`,
/// `sh:qualifiedValueShape`, `sh:reifierShape`, `sh:sparql`, `sh:prefixes` and `owl:imports`
/// to their object, `sh:and`/`sh:or`/`sh:xone` to each member of their list, and `sh:path` to
/// the path; from a BLANK path node (rudof reads an IRI as a plain predicate and goes no
/// further) the four unary path operators to their operand, `sh:alternativePath` to each
/// member, and a sequence (the node is a list) to each member. A list's members are children
/// of the node that names the list, one level down, however long the list is: rudof's list
/// recursion is LENGTH, which the sized compile stack carries. (rudof also registers a
/// qualified value shape's SIBLINGS from inside it; they are the qualified shapes of the
/// sibling property shapes, so they sit at the same depth by the walk's own edges.)
///
/// Depth is the longest chain of nodes. rudof's own recursion is a depth-first walk that skips
/// a shape it has already seen, so how deep it goes inside a recursive group depends on the
/// order it meets the shapes in. The bound is order-free: a strongly connected group counts as
/// all of its nodes, which no walk of it can exceed. A cycle through a path edge is refused
/// outright, since rudof would never leave it.
pub fn check_shapes_structure(shapes: &RdfData) -> Result<()> {
    let depth = shapes_depth(shapes)?;
    if depth > MAX_SHAPE_DEPTH {
        return Err(Error::InvalidArgument {
            name: "shapes".to_string(),
            detail: format!(
                "this shapes graph nests {depth} deep, past {MAX_SHAPE_DEPTH} (MAX_SHAPE_DEPTH), \
                 counting the nodes along a chain of shape references (`sh:not`, `sh:and`, \
                 `sh:or`, `sh:xone`, `sh:node`, `sh:property`, `sh:qualifiedValueShape`, \
                 `sh:reifierShape`, `sh:sparql`, `sh:prefixes`, `owl:imports`) and path \
                 operators, a recursive group counting all of its shapes: the SHACL compiler \
                 recurses once per level, where a stack overflow aborts the whole host"
            ),
        });
    }
    Ok(())
}

/// The depth [`check_shapes_structure`] bounds: the most nodes on any chain, a strongly
/// connected group counting all of its nodes. A cycle through a path edge is an error here.
pub(crate) fn shapes_depth(shapes: &RdfData) -> Result<usize> {
    let bad = |e: String| Error::Endpoint(format!("urn:shacl:validate: shapes graph: {e}"));

    // Name every IRI or blank node once.
    let mut ids: HashMap<Object, usize> = HashMap::new();
    let mut blank: Vec<bool> = Vec::new();
    let mut id = |o: Object| -> usize {
        let next = ids.len();
        *ids.entry(o.clone()).or_insert_with(|| {
            blank.push(matches!(o, Object::BlankNode(_)));
            next
        })
    };

    // One pass over the triples: list cells, and the structural triples to resolve after.
    let mut first: HashMap<usize, usize> = HashMap::new();
    let mut rest: HashMap<usize, usize> = HashMap::new();
    let mut raw: Vec<(usize, Role, usize)> = Vec::new();
    for triple in shapes.triples().map_err(|e| bad(e.to_string()))? {
        let (subject, predicate, object) = triple.into_components();
        let Some(role) = role(predicate.as_str()) else {
            continue;
        };
        // Only an IRI or a blank node can carry structure; a literal or a triple term is a leaf.
        let object = match RdfData::term_as_object(&object) {
            Ok(o @ (Object::Iri(_) | Object::BlankNode(_))) => o,
            _ => continue,
        };
        let subject = RdfData::subject_as_node(&subject).map_err(|e| bad(e.to_string()))?;
        let (s, o) = (id(subject), id(object));
        match role {
            Role::First => {
                first.insert(s, o);
            }
            Role::Rest => {
                rest.insert(s, o);
            }
            role => raw.push((s, role, o)),
        }
    }
    let n = ids.len();

    // A list's members, walked iteratively; a cyclic `rdf:rest` ends the walk (rudof refuses
    // such a list itself).
    let members = |head: usize| -> Vec<usize> {
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        let mut cell = head;
        while seen.insert(cell) {
            match first.get(&cell) {
                Some(&m) => out.push(m),
                None => break,
            }
            match rest.get(&cell) {
                Some(&next) => cell = next,
                None => break,
            }
        }
        out
    };

    let mut adj: Vec<Vec<(usize, Edge)>> = vec![Vec::new(); n];
    let mut path_nodes: Vec<usize> = Vec::new();
    for &(s, role, o) in &raw {
        let (edge, targets) = match role {
            Role::Shape => (Edge::Shape, vec![o]),
            Role::ShapeList => (Edge::Shape, members(o)),
            Role::Path => (Edge::Path, vec![o]),
            // rudof reads an IRI path node as a predicate and looks no further.
            Role::Operator if blank[s] => (Edge::Path, vec![o]),
            Role::OperatorList if blank[s] => (Edge::Path, members(o)),
            _ => continue,
        };
        for t in targets {
            adj[s].push((t, edge));
            if edge == Edge::Path {
                path_nodes.push(t);
            }
        }
    }
    // A blank path node that is a list is a sequence path: its members are path nodes too.
    let mut expanded = HashSet::new();
    while let Some(p) = path_nodes.pop() {
        if !blank[p] || !first.contains_key(&p) || !expanded.insert(p) {
            continue;
        }
        for m in members(p) {
            adj[p].push((m, Edge::Path));
            path_nodes.push(m);
        }
    }

    let (comp, count) = strongly_connected(&adj);
    let mut size = vec![0usize; count];
    let mut by_comp: Vec<Vec<usize>> = vec![Vec::new(); count];
    for v in 0..n {
        size[comp[v]] += 1;
        by_comp[comp[v]].push(v);
    }
    // Tarjan numbers a component after every component it reaches, so ascending order sees
    // each component's successors first.
    let mut height = vec![0usize; count];
    for c in 0..count {
        let mut below = 0;
        for &v in &by_comp[c] {
            for &(w, edge) in &adj[v] {
                if comp[w] == c {
                    if edge == Edge::Path {
                        return Err(Error::InvalidArgument {
                            name: "shapes".to_string(),
                            detail: "a `sh:path` contains itself (a blank path node is reached \
                                     again through its own path operators): the SHACL path \
                                     parser follows a path without remembering where it has \
                                     been, so it would recurse until the stack overflowed and \
                                     aborted the whole host"
                                .to_string(),
                        });
                    }
                } else {
                    below = below.max(height[comp[w]]);
                }
            }
        }
        height[c] = size[c] + below;
    }
    Ok(height.into_iter().max().unwrap_or(0))
}

/// Strongly connected components of `adj` by Tarjan's algorithm, run with an explicit stack
/// (a recursive walk here would be the very failure this module exists to stop). Returns each
/// node's component number and the number of components; a component is numbered after every
/// component reachable from it.
fn strongly_connected(adj: &[Vec<(usize, Edge)>]) -> (Vec<usize>, usize) {
    const UNSEEN: usize = usize::MAX;
    let n = adj.len();
    let mut index = vec![UNSEEN; n];
    let mut low = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut comp = vec![UNSEEN; n];
    let mut next = 0usize;
    let mut count = 0usize;
    for root in 0..n {
        if index[root] != UNSEEN {
            continue;
        }
        index[root] = next;
        low[root] = next;
        next += 1;
        stack.push(root);
        on_stack[root] = true;
        let mut call: Vec<(usize, usize)> = vec![(root, 0)];
        while let Some(top) = call.last_mut() {
            let v = top.0;
            if top.1 < adj[v].len() {
                let w = adj[v][top.1].0;
                top.1 += 1;
                if index[w] == UNSEEN {
                    index[w] = next;
                    low[w] = next;
                    next += 1;
                    stack.push(w);
                    on_stack[w] = true;
                    call.push((w, 0));
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
            } else {
                call.pop();
                if let Some(&(u, _)) = call.last() {
                    low[u] = low[u].min(low[v]);
                }
                if low[v] == index[v] {
                    while let Some(w) = stack.pop() {
                        on_stack[w] = false;
                        comp[w] = count;
                        if w == v {
                            break;
                        }
                    }
                    count += 1;
                }
            }
        }
    }
    (comp, count)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rudof_rdf::rdf_core::RDFFormat;
    use rudof_rdf::rdf_impl::ReaderMode;

    const HEAD: &str = "@prefix sh: <http://www.w3.org/ns/shacl#> .\n\
                        @prefix ex: <http://example.org/> .\n";

    fn graph(ttl: &str) -> RdfData {
        RdfData::from_str(ttl, &RDFFormat::Turtle, None, &ReaderMode::default()).unwrap()
    }

    fn depth(body: &str) -> Result<usize> {
        shapes_depth(&graph(&format!("{HEAD}{body}")))
    }

    fn nested(n: usize) -> String {
        format!("{}ex:o{}", "<<( ex:s ex:p ".repeat(n), " )>>".repeat(n))
    }

    #[test]
    fn triple_terms_are_refused_one_past_the_bound_and_pass_at_it() {
        let at = format!("ex:a ex:p {} .", nested(MAX_TURTLE_NESTING));
        assert!(check_turtle_nesting(&at, "data").is_ok());
        let over = format!("ex:a ex:p {} .", nested(MAX_TURTLE_NESTING + 1));
        let err = check_turtle_nesting(&over, "data").unwrap_err();
        assert!(
            matches!(&err, Error::InvalidArgument { name, .. } if name == "data"),
            "{err}"
        );
    }

    #[test]
    fn closed_triple_terms_do_not_accumulate() {
        // Many triple terms one after another are shallow, however many there are.
        let flat = format!("ex:a ex:p {} .", vec![nested(2); 500].join(", "));
        assert!(check_turtle_nesting(&flat, "data").is_ok());
    }

    #[test]
    fn brackets_in_strings_iris_comments_and_escapes_are_not_nesting() {
        let deep = "<<".repeat(200);
        for text in [
            format!("ex:a ex:p \"{deep}\" ."),
            format!("ex:a ex:p '{deep}' ."),
            format!("ex:a ex:p \"\"\"x\"\"{deep}\n\"\"\" ."),
            format!("ex:a ex:p '''{deep}''' ."),
            format!("ex:a ex:p \"\\\"{deep}\" ."),
            format!("# {deep}\nex:a ex:p ex:b ."),
            // An IRI may hold `'` and `#`: neither opens anything inside it.
            format!("ex:a ex:p <http://x/a'b#c> . # {deep}\n"),
            // A prefixed name may escape a quote: it opens no string.
            format!("ex:a\\' ex:p ex:b . # {deep}\n"),
            // oxttl closes a long string at its first triple quote (lexer.rs:738), so the
            // fourth `"` here OPENS a string, and what follows is inside it.
            format!("ex:a ex:p \"\"\"a\"\"\"\", {deep}"),
            // An IRI that never closes: the parser fails there and builds nothing after it.
            format!("ex:a ex:p <http://x/ {deep}"),
        ] {
            assert!(check_turtle_nesting(&text, "data").is_ok(), "{text}");
        }
    }

    #[test]
    fn nesting_after_a_string_or_iri_is_still_counted() {
        let over = nested(MAX_TURTLE_NESTING + 1);
        for text in [
            format!("ex:a ex:p \"<<\", '''>>''', <http://x/#>, {over} ."),
            format!("ex:a ex:p \"\"\"a\"\" b\"\"\", {over} ."),
            // oxttl parses `lenient()`, which reads an IRI to the first `>` whatever is inside
            // it: `<x">` is an IRI, not the start of a string that hides what follows.
            format!("ex:a ex:p <x\">, {over} . # \""),
            format!("ex:a ex:p <x '#>, {over} ."),
            // And a short string runs across a line end under `lenient()`.
            format!("ex:a ex:p \"x\n\", {over} ."),
            format!("ex:a ex:p 'x\r\n', {over} ."),
        ] {
            assert!(check_turtle_nesting(&text, "data").is_err(), "{text}");
        }
    }

    #[test]
    fn a_shape_nest_is_counted_in_nodes() {
        // ex:S, then `n` blank `sh:not` shapes, then the innermost shape.
        let not = |n: usize| {
            format!(
                "ex:S a sh:NodeShape ; sh:not {}[ sh:class ex:C ]{} .",
                "[ sh:not ".repeat(n),
                " ]".repeat(n)
            )
        };
        assert_eq!(depth(&not(0)).unwrap(), 2);
        assert_eq!(depth(&not(10)).unwrap(), 12);
        assert_eq!(depth(&not(MAX_SHAPE_DEPTH - 2)).unwrap(), MAX_SHAPE_DEPTH);
        let graph_over = graph(&format!("{HEAD}{}", not(MAX_SHAPE_DEPTH - 1)));
        let err = check_shapes_structure(&graph_over).unwrap_err();
        assert!(
            matches!(&err, Error::InvalidArgument { name, .. } if name == "shapes"),
            "{err}"
        );
    }

    #[test]
    fn list_members_are_one_level_down_however_long_the_list() {
        let or = format!(
            "ex:S a sh:NodeShape ; sh:or ( {} ) .",
            "[ sh:class ex:C ] ".repeat(1000)
        );
        assert_eq!(depth(&or).unwrap(), 2);
        let and = "ex:S sh:and ( [ sh:xone ( [ sh:or ( ex:T ) ] ) ] ) . ex:T sh:class ex:C .";
        assert_eq!(depth(and).unwrap(), 4);
    }

    #[test]
    fn paths_are_followed_through_operators_sequences_and_alternatives() {
        let path = "ex:S sh:property [ sh:path ( [ sh:inversePath ex:p ] \
                    [ sh:zeroOrMorePath [ sh:alternativePath ( ex:q [ sh:oneOrMorePath ex:r ] ) ] ] ) ] .";
        // S → property → sequence → zeroOrMore → alternative → oneOrMore → ex:r
        assert_eq!(depth(path).unwrap(), 7);
    }

    #[test]
    fn a_recursive_shape_is_accepted_and_counts_its_whole_group() {
        let knows = "ex:P a sh:NodeShape ; sh:property [ sh:path ex:knows ; sh:node ex:P ] .";
        // {ex:P, the property shape} plus the predicate path below it.
        assert_eq!(depth(knows).unwrap(), 3);
        let ring = (0..10)
            .map(|i| format!("ex:S{i} sh:node ex:S{} .\n", (i + 1) % 10))
            .collect::<String>();
        assert_eq!(depth(&ring).unwrap(), 10);
    }

    #[test]
    fn a_path_cycle_is_refused_and_an_iri_path_is_not_followed() {
        let cycle = "ex:S sh:property [ sh:path _:p ] . _:p sh:inversePath _:p .";
        let err = depth(cycle).unwrap_err();
        assert!(
            matches!(&err, Error::InvalidArgument { name, detail } if name == "shapes" && detail.contains("contains itself")),
            "{err}"
        );
        let through_a_list = "ex:S sh:property [ sh:path _:seq ] . \
                              _:seq rdf:first [ sh:zeroOrOnePath _:seq ] ; rdf:rest rdf:nil .";
        let ttl = format!(
            "@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .\n{HEAD}{through_a_list}"
        );
        assert!(shapes_depth(&graph(&ttl)).is_err());
        // An IRI path node is a predicate to rudof, whatever triples it carries.
        let iri = "ex:S sh:property [ sh:path ex:p ] . ex:p sh:inversePath ex:p .";
        assert_eq!(depth(iri).unwrap(), 3);
    }

    #[test]
    fn prefix_imports_are_followed() {
        let chain = (0..20)
            .map(|i| {
                format!(
                    "ex:o{i} <http://www.w3.org/2002/07/owl#imports> ex:o{} .\n",
                    i + 1
                )
            })
            .collect::<String>();
        let body = format!("ex:S sh:sparql [ sh:prefixes ex:o0 ] .\n{chain}");
        // S → constraint → o0 … o20
        assert_eq!(depth(&body).unwrap(), 23);
    }

    #[test]
    fn the_parity_corpus_is_far_inside_the_bound() {
        let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/corpus");
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path().join("shapes.ttl");
            let ttl = std::fs::read_to_string(&path).unwrap();
            check_turtle_nesting(&ttl, "shapes").unwrap();
            let d = shapes_depth(&graph(&ttl)).unwrap();
            assert!(d <= 8, "{}: {d}", path.display());
        }
    }

    /// The measurement behind [`MAX_SHAPE_DEPTH`]: the depth of every shapes graph named in
    /// `IKIGAI_SHACL_MEASURE` (colon-separated paths). Not an assertion.
    ///
    ///     IKIGAI_SHACL_MEASURE=a.ttl:b.ttl cargo test --lib -- --ignored --nocapture measure
    #[test]
    #[ignore]
    fn measure() {
        let Ok(paths) = std::env::var("IKIGAI_SHACL_MEASURE") else {
            return;
        };
        for path in paths.split(':') {
            let ttl = std::fs::read_to_string(path).unwrap();
            println!("{path}: depth {:?}", shapes_depth(&graph(&ttl)));
        }
    }
}
