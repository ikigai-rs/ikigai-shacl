//! One runaway `sh:select` does not stop validation for everyone else (ledger #1510).
//!
//! ★ Its own test binary, like `tests/time_budget.rs`, because the budget is per PROCESS: the
//! runaway this test leaves behind is still evaluating (oxigraph cannot stop a cross product
//! partway) when the test ends, and it holds one of the subset validator's overdue slots until
//! the process exits.
//!
//! Through shacl 0.3.6 the subset validator used ikigai-store's default cap, a quarter of the
//! machine's available parallelism and at least one. On any host with fewer than eight cores,
//! a four-core CI runner among them, that is ONE, so the second validation below was refused
//! with `Unavailable` ("1 SPARQL evaluations ... are still running") for as long as the runaway
//! ran: minutes, for every caller in the process (ledger #1500). The validator now states its
//! own cap, at least two (`core_shacl::MAX_OVERDUE_FLOOR`).
//!
//! ⚠ On a host with eight or more cores the store's default was already at least two, so this
//! test passes there either way: it is CI's four-core runner that tells the two apart.
//!
//! Only a build with the `sparql` feature has a time budget (and a `sh:select` to run past it),
//! so this binary is empty without it.
#![cfg(feature = "sparql")]

use ikigai_core::Error;
use ikigai_shacl::core_shacl::validate_report;

const HEAD: &str = "@prefix sh: <http://www.w3.org/ns/shacl#> .\n\
                    @prefix ex: <http://example.org/> .\n";

#[test]
fn a_second_validation_answers_while_one_runaway_is_overdue() {
    // The runaway: a six-way cross product over a few dozen triples, inside every size, nesting
    // and algebra bound and minutes of work (the shape `tests/time_budget.rs` uses). Its caller
    // is answered with a timeout at the 5 s base budget, and the evaluation keeps running.
    let data: String = (0..40)
        .map(|i| format!("<urn:s{i}> <urn:p> <urn:o{i}> .\n"))
        .chain(std::iter::once(
            "<urn:x> a <http://example.org/Person> .\n".to_string(),
        ))
        .collect();
    let runaway = "ex:S sh:targetClass ex:Person ; sh:sparql [ sh:select \"\"\"SELECT $this (COUNT(*) AS ?n) WHERE { \
                   ?a ?b ?c . ?d ?e ?f . ?g ?h ?i . ?j ?k ?l . ?m ?n0 ?o . ?q ?r ?t } GROUP BY $this\"\"\" ] .";
    let outcome = validate_report(&data, &format!("{HEAD}{runaway}"));
    assert!(matches!(outcome, Err(Error::Timeout(_))), "{outcome:?}");

    // Another caller's ordinary validation, with SPARQL of its own, while the runaway is overdue:
    // it is answered, with the verdict its data earns.
    let shapes = format!(
        "{HEAD}ex:E sh:targetClass ex:Entry ; \
         sh:property [ sh:path ex:text ; sh:minCount 1 ] ; \
         sh:sparql [ sh:select \"\"\"SELECT $this WHERE {{ $this <http://example.org/by> ?w . FILTER(!isIRI(?w)) }}\"\"\" ] ."
    );
    let good = "<urn:e1> a <http://example.org/Entry> ; <http://example.org/text> \"hello\" ; \
                <http://example.org/by> <urn:who> .\n";
    let bad = "<urn:e2> a <http://example.org/Entry> ; <http://example.org/by> \"who\" .\n";
    let report = validate_report(good, &shapes).expect("answered while one runaway is overdue");
    assert!(report.conforms, "{report:?}");
    let report = validate_report(bad, &shapes).expect("answered while one runaway is overdue");
    assert!(!report.conforms, "{report:?}");
    assert_eq!(report.violations.len(), 2, "{report:?}");
}
