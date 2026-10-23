//! The core-only build (`default-features = false`, ledger #2107): the subset validator's core
//! constraints with no SPARQL engine, no store and no time budget, which is what an in-page wasm
//! kernel links. CI's `no default features` job runs this file in that build, and lints its
//! wasm32 lib; most tests here exist only there (`cfg(not(feature = "sparql"))`).
//!
//! What it pins:
//!
//! - a SHACL-SPARQL construct is REFUSED, naming the construct and the feature that enables it,
//!   never skipped (a bound refuses, it never truncates);
//! - a term no build implements is still named as that, so the refusal never tells a caller to
//!   enable a feature that would not help;
//! - closed shapes and the core constraints validate, with no SPARQL in the build;
//! - the work bound, the core-only build's stand-in for ikigai-store's time budget, refuses
//!   rather than answers in part.

use ikigai_shacl::core_shacl::validate_report;
use ikigai_shacl::Report;

const HEAD: &str = "@prefix sh: <http://www.w3.org/ns/shacl#> .\n\
                    @prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n\
                    @prefix ex: <http://example.org/> .\n";

fn shapes(body: &str) -> String {
    format!("{HEAD}{body}")
}

#[test]
fn quoted_patterns_preserve_case_insensitive_flags() {
    for flags in ["iq", "qi"] {
        let body = shapes(&format!(
            "ex:S sh:targetNode ex:a ; sh:property [ sh:path ex:v ; \
             sh:pattern \"alice.smith\" ; sh:flags \"{flags}\" ] ."
        ));
        for (value, conforms) in [("AlIcE.SmItH", true), ("AlIcExSmItH", false)] {
            let data = format!("{HEAD}ex:a ex:v \"{value}\" .");
            let report = validate_report(&data, &body).unwrap();
            assert_eq!(
                report.conforms, conforms,
                "flags={flags}, value={value}: {report:?}"
            );
        }
    }
    let body = shapes(
        "ex:S sh:targetNode ex:a ; sh:property [ sh:path ex:v ; \
         sh:pattern \"alice.smith\" ; sh:flags \"q\" ] .",
    );
    let report = validate_report(&format!("{HEAD}ex:a ex:v \"AlIcE.SmItH\" ."), &body).unwrap();
    assert!(!report.conforms, "q alone must remain case sensitive");
}

/// The components of `report`'s results, sorted, by local name.
fn components(report: &Report) -> Vec<String> {
    let mut got: Vec<String> = report
        .violations
        .iter()
        .map(|v| v.component.rsplit('#').next().unwrap().to_string())
        .collect();
    got.sort();
    got
}

/// The core constraints and a closed shape, on the build every other test file also runs in.
/// Without `sparql` this is the whole validator; with it, the same answers.
#[test]
fn closed_shapes_and_the_core_constraints_validate() {
    let body = "ex:PersonShape a sh:NodeShape ; sh:targetClass ex:Person ; sh:closed true ;\n\
                  sh:ignoredProperties ( <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> ) ;\n\
                  sh:property [ sh:path ex:name ; sh:datatype xsd:string ; sh:minCount 1 ; sh:maxCount 1 ;\n\
                                sh:minLength 2 ; sh:maxLength 10 ; sh:pattern \"^[A-Z]\" ] ;\n\
                  sh:property [ sh:path ex:role ; sh:in ( \"admin\" \"user\" ) ] ;\n\
                  sh:property [ sh:path ex:home ; sh:nodeKind sh:IRI ] .";
    let good = "@prefix ex: <http://example.org/> .\n\
                ex:a a ex:Person ; ex:name \"Alice\" ; ex:role \"admin\" ; ex:home <urn:x> .";
    let report = validate_report(good, &shapes(body)).unwrap();
    assert!(report.conforms, "{report:?}");

    // One violation of each: a second name, too short and lower-case, a role outside `sh:in`, a
    // literal home, and a predicate the closed shape does not list.
    let bad = "@prefix ex: <http://example.org/> .\n\
               ex:b a ex:Person ; ex:name \"b\" , \"Bob\" ; ex:role \"root\" ; ex:home \"here\" ;\n\
                    ex:shoe 9 .";
    let report = validate_report(bad, &shapes(body)).unwrap();
    assert!(!report.conforms);
    assert_eq!(
        components(&report),
        [
            "ClosedConstraintComponent",
            "InConstraintComponent",
            "MaxCountConstraintComponent",
            "MinLengthConstraintComponent",
            "NodeKindConstraintComponent",
            "PatternConstraintComponent",
        ],
        "{report:?}"
    );
}

/// A shapes graph that only DECLARES prefixes (an ontology's `sh:declare`) changes no verdict,
/// so the core-only build accepts it and validates the rest.
#[test]
fn prefix_declarations_alone_are_accepted() {
    let body = "ex:onto sh:declare [ sh:prefix \"ex\" ; sh:namespace \"http://example.org/\"^^xsd:anyURI ] .\n\
                ex:S sh:targetNode ex:a ; sh:nodeKind sh:IRI .";
    let report = validate_report("", &shapes(body)).unwrap();
    assert!(report.conforms, "{report:?}");
}

#[cfg(not(feature = "sparql"))]
mod without_sparql {
    use super::*;
    use ikigai_core::Error;
    use ikigai_shacl::core_shacl::{MAX_PATTERN_SIZE, MAX_VALIDATION_WORK};

    /// The refusal for `body`, which must be a typed `InvalidArgument` on `shapes` naming `term`
    /// and the `sparql` feature.
    fn refused_for_sparql(body: &str, term: &str) {
        match validate_report("", &shapes(body)) {
            Err(Error::InvalidArgument { name, detail }) => {
                assert_eq!(name, "shapes", "{detail}");
                assert!(detail.contains(term), "`{term}` not named in: {detail}");
                assert!(
                    detail.contains("`sparql` feature"),
                    "the feature not named in: {detail}"
                );
                assert!(detail.contains("nothing was validated"), "{detail}");
            }
            other => panic!("not refused ({term}): {other:?}\n{body}"),
        }
    }

    #[test]
    fn a_sparql_constraint_is_refused_naming_the_feature() {
        refused_for_sparql(
            "ex:S sh:targetNode ex:a ; sh:sparql [ sh:select \"SELECT $this WHERE { }\" ] .",
            "`sh:s",
        );
        // Each construct on its own: a `sh:select` that no `sh:sparql` reaches, and the class.
        refused_for_sparql(
            "ex:C sh:select \"SELECT $this WHERE { }\" .\nex:S sh:targetNode ex:a ; sh:nodeKind sh:IRI .",
            "`sh:select`",
        );
        refused_for_sparql(
            "ex:C a sh:SPARQLConstraint .\nex:S sh:targetNode ex:a ; sh:nodeKind sh:IRI .",
            "the class `sh:SPARQLConstraint`",
        );
    }

    #[test]
    fn a_term_no_build_implements_is_not_blamed_on_the_feature() {
        // `sh:ask` and `sh:target` beside a `sh:select`: no feature would validate them, so the
        // refusal names them as outside the subset, whatever order the triples came in.
        for (term, body) in [
            ("`sh:ask`", "ex:S sh:targetNode ex:a ; sh:sparql [ sh:ask \"ASK { }\" ] ."),
            (
                "`sh:target`",
                "ex:S sh:target [ sh:select \"SELECT ?this WHERE { ?this ?p ?o }\" ] ; sh:class ex:A .",
            ),
        ] {
            match validate_report("", &shapes(body)) {
                Err(Error::InvalidArgument { name, detail }) => {
                    assert_eq!(name, "shapes");
                    assert!(detail.contains(term), "{term} not named in: {detail}");
                    assert!(
                        detail.contains("which the SHACL subset validator does not implement"),
                        "{detail}"
                    );
                    assert!(!detail.contains("`sparql` feature"), "{detail}");
                }
                other => panic!("{term} not refused: {other:?}"),
            }
        }
    }

    #[test]
    fn past_the_work_bound_validation_is_refused_not_answered_in_part() {
        // A 50,000-member `sh:in` checked against 300 values: 15 million comparisons, past the
        // bound, from a few kilobytes of data.
        let members: String = (0..50_000).map(|i| format!("\"v{i}\" ")).collect();
        let body = format!(
            "ex:S sh:targetNode ex:a ; sh:property [ sh:path ex:v ; sh:in ( {members}) ] ."
        );
        let values: Vec<String> = (0..300).map(|i| format!("\"w{i}\"")).collect();
        let data = format!(
            "@prefix ex: <http://example.org/> .\nex:a ex:v {} .",
            values.join(" , ")
        );
        let started = std::time::Instant::now();
        let outcome = validate_report(&data, &shapes(&body));
        let took = started.elapsed();
        match outcome {
            Err(Error::InvalidArgument { name, detail }) => {
                assert_eq!(name, "data");
                assert!(detail.contains("MAX_VALIDATION_WORK"), "{detail}");
                assert!(
                    detail.contains(&MAX_VALIDATION_WORK.to_string()),
                    "{detail}"
                );
                assert!(detail.contains("no report was produced"), "{detail}");
            }
            other => panic!("not refused: {other:?}"),
        }
        // The bound stands in for a time budget: it is reached in seconds, not minutes, even in
        // a debug build.
        assert!(
            took < std::time::Duration::from_secs(30),
            "the refusal took {took:?}"
        );

        // A tenth of the values is well inside it, and answers.
        let data = format!(
            "@prefix ex: <http://example.org/> .\nex:a ex:v {} .",
            values[..30].join(" , ")
        );
        let report = validate_report(&data, &shapes(&body)).unwrap();
        assert_eq!(report.violations.len(), 30);
    }

    #[test]
    fn a_pattern_past_the_size_cap_is_refused() {
        // Each Unicode `\w` compiles to thousands of bytes; a few hundred of them pass the cap.
        let body = format!(
            "ex:S sh:targetNode ex:a ; sh:property [ sh:path ex:v ; sh:pattern \"{}\" ] .",
            r"\\w".repeat(400)
        );
        match validate_report("", &shapes(&body)) {
            Err(Error::InvalidArgument { name, detail }) => {
                assert_eq!(name, "shapes");
                assert!(detail.contains("does not compile"), "{detail}");
            }
            other => panic!("a pattern past {MAX_PATTERN_SIZE} bytes compiled: {other:?}"),
        }
    }
}
