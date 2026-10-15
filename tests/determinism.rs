//! `urn:shacl:validate` is `.cacheable()`, so every face must be a pure function of its
//! inputs: the same data and shapes give the same BYTES on any kernel, not just on the one
//! whose cache already holds the first answer (ledger #1565). A cache hit can only repeat
//! itself, so these resolve on a FRESH kernel each time, the way a recomputation after a
//! thread cut does (ikigai-conformance's RECOMPUTE).
//!
//! Before the fix, the Turtle face differed on every run: the report graph's blank nodes
//! carried the random labels oxigraph's Turtle parser and rudof's `to_rdf` mint, those labels
//! fed the content id the skolem IRIs are minted under, and the store's iteration order fed
//! the serialization. Six runs gave six outputs.

use std::collections::BTreeSet;
use std::sync::Arc;

use ikigai_core::{ArgRef, Capability, Iri, Kernel, Request, Verb};

/// How many fresh kernels each case is resolved on.
const RUNS: usize = 8;

/// A violation with a `sh:value`, a `sh:resultPath` and a blank-node `sh:sourceShape`, two
/// focus nodes, and a message template: one of each thing the report graph names.
const SHAPES: &str = r#"@prefix sh: <http://www.w3.org/ns/shacl#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix : <http://example.org/> .
:PersonShape a sh:NodeShape ;
  sh:targetClass :Person ;
  sh:property [ sh:path :name ; sh:minCount 1 ; sh:datatype xsd:string ;
                sh:message "{?value} is not a string" ] ."#;

const DATA: &str = r#"@prefix : <http://example.org/> .
:carol a :Person ; :name 42 .
:bob a :Person ."#;

/// Every shape a blank node, and every `sh:path` a complex one: the RDF-list structure of
/// a sequence and an alternative path is passed through into the report graph. (rudof only:
/// the subset validator refuses a complex path.)
#[cfg(feature = "rudof")]
const COMPLEX_SHAPES: &str = include_str!("corpus/complex-paths/shapes.ttl");
#[cfg(feature = "rudof")]
const COMPLEX_DATA: &str = include_str!("corpus/complex-paths/data.ttl");

/// A blank-node FOCUS node in the data graph, which the report names too.
const BLANK_FOCUS_DATA: &str = r#"@prefix : <http://example.org/> .
[] a :Person ; :name 1 .
[] a :Person .
_:alice a :Person ; :name 2 ."#;

/// A message template naming the focus node, which a blank focus node has no stable name for.
const THIS_SHAPES: &str = r#"@prefix sh: <http://www.w3.org/ns/shacl#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix : <http://example.org/> .
:PersonShape a sh:NodeShape ;
  sh:targetClass :Person ;
  sh:property [ sh:path :name ; sh:minCount 1 ; sh:datatype xsd:string ;
                sh:message "{$this} has a bad name {?value}" ] ."#;

fn resolve(data: &str, shapes: &str, as_type: Option<&str>) -> Vec<u8> {
    let kernel = Kernel::new(Arc::new(ikigai_shacl::space()));
    let mut request = Request::new(
        Verb::Source,
        Iri::parse("urn:shacl:validate").expect("a valid IRI"),
    )
    .with_arg("data", ArgRef::Inline(data.as_bytes().to_vec()))
    .with_arg("shapes", ArgRef::Inline(shapes.as_bytes().to_vec()));
    if let Some(as_type) = as_type {
        request = request.with_arg("as", ArgRef::Inline(as_type.as_bytes().to_vec()));
    }
    futures::executor::block_on(kernel.issue(request, &Capability::root()))
        .expect("urn:shacl:validate resolves")
        .bytes
}

/// Resolve on `RUNS` fresh kernels and require one answer.
fn assert_one_answer(case: &str, data: &str, shapes: &str, as_type: Option<&str>) {
    let answers: BTreeSet<Vec<u8>> = (0..RUNS).map(|_| resolve(data, shapes, as_type)).collect();
    if answers.len() != 1 {
        let shown: Vec<String> = answers
            .iter()
            .take(2)
            .map(|a| String::from_utf8_lossy(a).into_owned())
            .collect();
        panic!(
            "{case} ({}): {} distinct answers in {RUNS} fresh kernels; the first two:\n{}\n----\n{}",
            as_type.unwrap_or("text/turtle"),
            answers.len(),
            shown[0],
            shown[1]
        );
    }
}

#[test]
fn the_turtle_face_is_the_same_bytes_on_every_fresh_kernel() {
    assert_one_answer("blank property shape", DATA, SHAPES, None);
    #[cfg(feature = "rudof")]
    assert_one_answer("complex paths", COMPLEX_DATA, COMPLEX_SHAPES, None);
    assert_one_answer("blank focus nodes", BLANK_FOCUS_DATA, SHAPES, None);
    assert_one_answer(
        "a template naming a blank focus",
        BLANK_FOCUS_DATA,
        THIS_SHAPES,
        None,
    );
}

#[test]
fn the_json_face_is_the_same_bytes_on_every_fresh_kernel() {
    let json = Some("application/json");
    assert_one_answer("blank property shape", DATA, SHAPES, json);
    #[cfg(feature = "rudof")]
    assert_one_answer("complex paths", COMPLEX_DATA, COMPLEX_SHAPES, json);
    assert_one_answer("blank focus nodes", BLANK_FOCUS_DATA, SHAPES, json);
    assert_one_answer(
        "a template naming a blank focus",
        BLANK_FOCUS_DATA,
        THIS_SHAPES,
        json,
    );
}

/// The library calls behind the faces, held to the same rule.
#[test]
fn the_library_report_is_the_same_on_every_call() {
    let cases = [
        (DATA, SHAPES),
        (BLANK_FOCUS_DATA, SHAPES),
        (BLANK_FOCUS_DATA, THIS_SHAPES),
        #[cfg(feature = "rudof")]
        (COMPLEX_DATA, COMPLEX_SHAPES),
    ];
    for (data, shapes) in cases {
        let turtle: BTreeSet<String> = (0..RUNS)
            .map(|_| ikigai_shacl::validate_turtle(data, shapes).unwrap())
            .collect();
        assert_eq!(turtle.len(), 1, "validate_turtle: {turtle:#?}");
        let report: BTreeSet<String> = (0..RUNS)
            .map(|_| {
                serde_json::to_string(&ikigai_shacl::validate_report(data, shapes).unwrap())
                    .unwrap()
            })
            .collect();
        assert_eq!(report.len(), 1, "validate_report: {report:#?}");
    }
}

/// The two faces name a blank node the same way, by where it first appears in its document:
/// the JSON face's `_:data.b0` is the label the Turtle face's skolem IRI ends in, and the label
/// a `sh:message` template renders. An explicit `_:alice` is renamed alike: a parser-minted
/// label cannot be told from an author's.
#[test]
fn both_faces_name_a_blank_focus_node_by_appearance() {
    let json: serde_json::Value = serde_json::from_slice(&resolve(
        BLANK_FOCUS_DATA,
        THIS_SHAPES,
        Some("application/json"),
    ))
    .unwrap();
    let turtle = String::from_utf8(resolve(BLANK_FOCUS_DATA, THIS_SHAPES, None)).unwrap();
    let focus: Vec<&str> = json["violations"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v["focus_node"].as_str().unwrap())
        .collect();
    // The first `[]`, the second (no name at all), and `_:alice`.
    assert_eq!(focus, ["_:data.b0", "_:data.b1", "_:data.b2"], "{json:#}");
    for label in ["data.b0", "data.b1", "data.b2"] {
        assert!(turtle.contains(&format!(":{label}>")), "{label}:\n{turtle}");
    }
    for message in ["_:data.b0 has a bad name 1", "_:data.b2 has a bad name 2"] {
        assert!(
            turtle.contains(&format!("\"{message}\"")),
            "{message}:\n{turtle}"
        );
        assert!(json.to_string().contains(message), "{message}: {json:#}");
    }
}
