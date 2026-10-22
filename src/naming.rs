//! How the report graph is named, so that it is one function of the inputs (ledger #1565).
//!
//! `urn:shacl:validate` is `.cacheable()`, so its answer must be the same bytes on every run.
//! Three things made it differ, and each is fixed where it arises:
//!
//! 1. **The parser's blank-node labels.** The Turtle parser (oxttl, which oxigraph's `io` wraps)
//!    mints a random label for every `[ … ]`, and those labels are the report's: a blank
//!    `sh:property` shape is a `sh:sourceShape`, a blank data node a `sh:focusNode`. So each
//!    input graph is relabeled as it is parsed, by order of first appearance in the document:
//!    `{role}.b{n}`, where `role` is `data` or `shapes` ([`by_appearance`]). That is a function of the input text, costs
//!    one pass, and keeps the two graphs' labels apart.
//! 2. **The nodes rudof mints.** rudof's `to_rdf` numbers the report, its results and each
//!    complex `sh:resultPath` from a counter, in the order its results came back, which varies.
//!    [`name_minted`] renames them by content instead.
//! 3. **The serialization order**, which followed the store's iteration. [`skolemize`] sorts.
//!
//! What it does NOT do is canonicalize the graph (RDFC-1.0): that is exponential on ordinary
//! reports (500 blank focus nodes failing two blank property shapes did not finish in a
//! minute), and naming at the source makes it unnecessary. The cost is that the names follow
//! the input TEXT, not just its graph: the same graph written in another order may name its
//! blank nodes differently, while the same text always names them alike.

use std::collections::HashMap;

use ikigai_core::{ContentId, Error, Result};
use oxrdf::{BlankNode, NamedNode, NamedOrBlankNode, Triple};
use oxttl::TurtleSerializer;

use crate::REPORT_SCHEME;

const SH: &str = "http://www.w3.org/ns/shacl#";

/// Relabel the blank nodes of `triples`, which arrive in document order, by order of first
/// appearance: the first one met is `{role}.b0`, the next `{role}.b1`, and so on. Every
/// label carries a `.`, which no label rudof mints does (a hexadecimal counter), and that is how
/// [`name_minted`] tells the two apart.
pub(crate) fn by_appearance(
    triples: impl IntoIterator<Item = Triple>,
    role: &str,
) -> Result<Vec<Triple>> {
    let mut labels: HashMap<String, BlankNode> = HashMap::new();
    let mut label = |b: &BlankNode| -> Result<oxrdf::Term> {
        let next = labels.len();
        Ok(labels
            .entry(b.as_str().to_string())
            .or_insert_with(|| BlankNode::new_unchecked(format!("{role}.b{next}")))
            .clone()
            .into())
    };
    triples
        .into_iter()
        .map(|t| map_triple(&t, &mut label))
        .collect()
}

/// Whether a blank node came from an input graph ([`by_appearance`]) rather than being minted.
#[cfg(feature = "rudof")]
fn from_input(b: &BlankNode) -> bool {
    b.as_str().contains('.')
}

/// Rename every blank node rudof's `to_rdf` minted (any label without a `.`) by content. (The
/// subset validator mints `report` and `result.N` in a fixed order, and does not need this.)
///
/// The minted nodes form a tree hanging from the report node: the report, its results, and
/// each result's own `sh:resultPath` structure. Each node's CONTENT hash covers its outgoing
/// triples, a minted child by its own content hash (so identical subtrees hash alike), and its
/// NAME is given top-down: the root is `report`, and a child is named from its parent's name,
/// the predicate, its content hash and its rank among identical siblings. Identical siblings
/// are identical subtrees, so which one gets which rank cannot change the output.
///
/// A minted node with two parents, or a cycle among them, would make that ambiguous, so either
/// is refused rather than named arbitrarily.
#[cfg(feature = "rudof")]
pub(crate) fn name_minted(triples: Vec<Triple>) -> Result<Vec<Triple>> {
    let mut outgoing: HashMap<String, Vec<usize>> = HashMap::new();
    let mut parent: HashMap<String, String> = HashMap::new();
    for (i, t) in triples.iter().enumerate() {
        if let NamedOrBlankNode::BlankNode(s) = &t.subject {
            if !from_input(s) {
                outgoing.entry(s.as_str().to_string()).or_default().push(i);
                if let oxrdf::Term::BlankNode(o) = &t.object {
                    if !from_input(o) {
                        let had = parent.insert(o.as_str().to_string(), s.as_str().to_string());
                        if had.is_some_and(|p| p != s.as_str()) {
                            return Err(shared(o.as_str()));
                        }
                    }
                }
            }
        }
    }

    // Content hashes, bottom-up (memoized; the depth is the deepest `sh:resultPath`).
    let mut hashes: HashMap<String, String> = HashMap::new();
    let mut nodes: Vec<&String> = outgoing.keys().collect();
    nodes.sort_unstable();
    for node in nodes {
        content_hash(node, &triples, &outgoing, &mut hashes, 0)?;
    }

    // Roots: minted nodes with no minted parent. One report, normally.
    let mut roots: Vec<&String> = outgoing
        .keys()
        .filter(|n| !parent.contains_key(*n))
        .collect();
    roots.sort_unstable_by_key(|n| &hashes[*n]);
    let mut names: HashMap<String, String> = HashMap::new();
    let mut queue: Vec<String> = Vec::new();
    for (k, root) in roots.iter().enumerate() {
        let name = if k == 0 {
            "report".to_string()
        } else {
            format!("report-{k}")
        };
        names.insert((*root).clone(), name);
        queue.push((*root).clone());
    }
    while let Some(node) = queue.pop() {
        let mut children: Vec<(String, String, String)> = outgoing
            .get(&node)
            .into_iter()
            .flatten()
            .filter_map(|&i| match &triples[i].object {
                oxrdf::Term::BlankNode(o) if !from_input(o) => Some((
                    triples[i].predicate.as_str().to_string(),
                    hashes.get(o.as_str()).cloned().unwrap_or_default(),
                    o.as_str().to_string(),
                )),
                _ => None,
            })
            .collect();
        children.sort_unstable_by(|a, b| (&a.0, &a.1).cmp(&(&b.0, &b.1)));
        let mut rank: HashMap<(String, String), usize> = HashMap::new();
        for (predicate, hash, child) in children {
            let k = rank.entry((predicate.clone(), hash.clone())).or_default();
            let name = short_hash(&format!("{}\n{predicate}\n{hash}\n{k}", names[&node]));
            *k += 1;
            names.insert(child.clone(), name);
            queue.push(child);
        }
    }

    let mut rename = |b: &BlankNode| -> Result<oxrdf::Term> {
        if from_input(b) {
            return Ok(b.clone().into());
        }
        names
            .get(b.as_str())
            .map(|n| BlankNode::new_unchecked(n).into())
            .ok_or_else(|| shared(b.as_str()))
    };
    triples.iter().map(|t| map_triple(t, &mut rename)).collect()
}

/// The content hash of minted node `node`: its outgoing triples, sorted, with a minted child
/// standing for its own content hash.
#[cfg(feature = "rudof")]
fn content_hash(
    node: &str,
    triples: &[Triple],
    outgoing: &HashMap<String, Vec<usize>>,
    hashes: &mut HashMap<String, String>,
    depth: usize,
) -> Result<String> {
    if let Some(h) = hashes.get(node) {
        return Ok(h.clone());
    }
    // Deeper than any report can be: the tree is a report, its results, and a path nested at
    // most `MAX_SHAPE_DEPTH` deep, so this is a cycle.
    if depth > crate::MAX_SHAPE_DEPTH + 4 {
        return Err(shared(node));
    }
    let mut lines: Vec<String> = Vec::new();
    for &i in outgoing.get(node).into_iter().flatten() {
        let t = &triples[i];
        let object = match &t.object {
            oxrdf::Term::BlankNode(o) if !from_input(o) => format!(
                "minted:{}",
                content_hash(o.as_str(), triples, outgoing, hashes, depth + 1)?
            ),
            other => other.to_string(),
        };
        lines.push(format!("{} {object}", t.predicate));
    }
    lines.sort_unstable();
    let h = short_hash(&lines.join("\n"));
    hashes.insert(node.to_string(), h.clone());
    Ok(h)
}

/// Sixteen hex digits of BLAKE3: a blank-node label, so it only has to be unique within one
/// report.
#[cfg(feature = "rudof")]
fn short_hash(text: &str) -> String {
    let id = ContentId::of(text.as_bytes()).to_string();
    let hex = id.rsplit(':').next().unwrap_or(&id);
    hex.chars().take(16).collect()
}

#[cfg(feature = "rudof")]
fn shared(label: &str) -> Error {
    Error::Endpoint(format!(
        "urn:shacl:validate: the report graph's node `_:{label}` is shared or cyclic, so it \
         has no stable name"
    ))
}

/// Skolemize the report graph: every blank node becomes
/// [`REPORT_SCHEME`]`<content id>:<label>`, where the content id is that of the graph's sorted
/// N-Triples lines, and the triples come back sorted. The labels must already be stable
/// ([`by_appearance`], [`name_minted`]); this only names them.
pub(crate) fn skolemize(triples: Vec<Triple>) -> Result<Vec<Triple>> {
    let mut lines: Vec<String> = triples.iter().map(Triple::to_string).collect();
    lines.sort_unstable();
    lines.dedup();
    let scheme = format!(
        "{REPORT_SCHEME}{}:",
        ContentId::of(lines.join("\n").as_bytes())
    );
    let mut skolem = |b: &BlankNode| -> Result<oxrdf::Term> {
        let iri = format!("{scheme}{}", encode_label(b.as_str()));
        NamedNode::new(&iri).map(oxrdf::Term::from).map_err(|e| {
            Error::Endpoint(format!("urn:shacl:validate: bad skolem IRI `{iri}`: {e}"))
        })
    };
    let mut out: Vec<Triple> = triples
        .iter()
        .map(|t| map_triple(t, &mut skolem))
        .collect::<Result<_>>()?;
    out.sort_by_cached_key(Triple::to_string);
    out.dedup();
    Ok(out)
}

/// The report graph as Turtle: the `sh:` prefix, and the triples in the order given.
pub(crate) fn turtle(triples: &[Triple]) -> Result<String> {
    let bad = |e: &dyn std::fmt::Display| {
        Error::Endpoint(format!("urn:shacl:validate: report serialize error: {e}"))
    };
    let mut writer = TurtleSerializer::new()
        .with_prefix("sh", SH)
        .map_err(|e| bad(&e))?
        .for_writer(Vec::new());
    for t in triples {
        writer.serialize_triple(t).map_err(|e| bad(&e))?;
    }
    let bytes = writer.finish().map_err(|e| bad(&e))?;
    String::from_utf8(bytes).map_err(|e| bad(&e))
}

/// Percent-encode a blank-node label down to the URN-safe set. RDF 1.1 admits `:`, `.` and
/// non-ASCII in a label; a minted IRI stays in `[A-Za-z0-9._-]` and `%XX`, so a consumer can
/// split the scheme from the label on the last `:`.
fn encode_label(label: &str) -> String {
    label
        .bytes()
        .map(|b| match b {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'_' | b'.' => (b as char).to_string(),
            _ => format!("%{b:02X}"),
        })
        .collect()
}

/// `t` with every blank node replaced by `f` of it: the subject, the object, and the parts of a
/// triple term.
fn map_triple(t: &Triple, f: &mut dyn FnMut(&BlankNode) -> Result<oxrdf::Term>) -> Result<Triple> {
    let subject: NamedOrBlankNode = match &t.subject {
        NamedOrBlankNode::BlankNode(b) => match f(b)? {
            oxrdf::Term::NamedNode(n) => n.into(),
            oxrdf::Term::BlankNode(b) => b.into(),
            other => {
                return Err(Error::Endpoint(format!(
                    "urn:shacl:validate: a subject became {other}"
                )))
            }
        },
        named => named.clone(),
    };
    let object = map_term(&t.object, f)?;
    Ok(Triple::new(subject, t.predicate.clone(), object))
}

fn map_term(
    term: &oxrdf::Term,
    f: &mut dyn FnMut(&BlankNode) -> Result<oxrdf::Term>,
) -> Result<oxrdf::Term> {
    // Not an exhaustive `match`: oxrdf's `Term::Triple` exists only under its `rdf-12` feature,
    // which the `rudof` feature turns on (Cargo.toml), and another crate in a host's graph could
    // turn it on in a build without rudof. There the subset validator refuses a triple term at
    // parse time, so none reaches here.
    if let oxrdf::Term::BlankNode(b) = term {
        return f(b);
    }
    #[cfg(feature = "rudof")]
    if let oxrdf::Term::Triple(t) = term {
        return Ok(map_triple(t, f)?.into());
    }
    Ok(term.clone())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(feature = "rudof")]
    use oxrdf::Literal;

    #[cfg(feature = "rudof")]
    fn sh(local: &str) -> NamedNode {
        NamedNode::new_unchecked(format!("{SH}{local}"))
    }

    fn ex(local: &str) -> NamedNode {
        NamedNode::new_unchecked(format!("http://example.org/{local}"))
    }

    /// A report as rudof mints it: counter labels, results in the order given, and a shape
    /// passed through from the shapes graph.
    #[cfg(feature = "rudof")]
    fn minted(order: [&str; 2]) -> Vec<Triple> {
        let report = BlankNode::new_unchecked("1");
        let shape = BlankNode::new_unchecked("shapes.b0");
        let mut out = vec![Triple::new(
            report.clone(),
            sh("conforms"),
            Literal::from(false),
        )];
        for (i, focus) in order.into_iter().enumerate() {
            let result = BlankNode::new_unchecked(format!("{}", i + 2));
            out.push(Triple::new(report.clone(), sh("result"), result.clone()));
            out.push(Triple::new(result.clone(), sh("focusNode"), ex(focus)));
            out.push(Triple::new(result, sh("sourceShape"), shape.clone()));
        }
        out
    }

    #[test]
    #[cfg(feature = "rudof")]
    fn minted_nodes_are_named_by_content_not_by_their_order() {
        let one = skolemize(name_minted(minted(["carol", "bob"])).unwrap()).unwrap();
        let two = skolemize(name_minted(minted(["bob", "carol"])).unwrap()).unwrap();
        assert_eq!(turtle(&one).unwrap(), turtle(&two).unwrap());
        let text = turtle(&one).unwrap();
        assert!(text.contains(":report>"), "{text}");
        assert!(
            text.contains(":shapes.b0>"),
            "an input label is kept: {text}"
        );
        assert!(!text.contains("_:"), "{text}");
    }

    #[test]
    #[cfg(feature = "rudof")]
    fn identical_siblings_keep_their_count() {
        // Two results with the same content stay two nodes.
        let named = name_minted(minted(["bob", "bob"])).unwrap();
        let results = named.iter().filter(|t| t.predicate == sh("result")).count();
        assert_eq!(results, 2);
        let distinct: std::collections::BTreeSet<String> = named
            .iter()
            .filter(|t| t.predicate == sh("result"))
            .map(|t| t.object.to_string())
            .collect();
        assert_eq!(distinct.len(), 2, "{named:?}");
    }

    #[test]
    #[cfg(feature = "rudof")]
    fn a_shared_minted_node_is_refused() {
        let mut graph = minted(["carol", "bob"]);
        // A second parent for result `2`.
        graph.push(Triple::new(
            BlankNode::new_unchecked("3"),
            sh("detail"),
            BlankNode::new_unchecked("2"),
        ));
        assert!(name_minted(graph).is_err());
    }

    #[test]
    fn input_labels_follow_the_document() {
        let a = BlankNode::new_unchecked("f00d");
        let b = BlankNode::new_unchecked("beef");
        let triples = vec![
            Triple::new(a.clone(), ex("p"), b.clone()),
            Triple::new(b, ex("p"), a),
        ];
        let named = by_appearance(triples, "data").unwrap();
        assert_eq!(
            named.iter().map(Triple::to_string).collect::<Vec<_>>(),
            [
                "_:data.b0 <http://example.org/p> _:data.b1",
                "_:data.b1 <http://example.org/p> _:data.b0",
            ]
        );
    }
}
