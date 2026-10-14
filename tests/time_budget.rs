//! The subset validator's time budget, in a test binary of its own.
//!
//! ★ Why its own binary: the timed-out evaluation is still running when the caller is answered,
//! because oxigraph cannot always stop one partway. Every subset validation in a process shares
//! one `EvaluationBudget` (`core_shacl::budget`), and since ikigai-store 0.2.21 (ledger #1427)
//! that budget reserves one of `default_max_overdue()` slots per evaluation (a quarter of the
//! machine's available parallelism, at least one) and refuses every new evaluation with
//! `Unavailable` while that many are overdue. On a four-core CI runner that is ONE slot, so the
//! straggler this test leaves behind refused every later validation in the same process: in
//! `tests/core_subset.rs` it turned four or five unrelated tests red with "1 SPARQL evaluations
//! on this store are still running", on CI and never on an 18-core laptop, where the cap is four.
//! A separate test binary is a separate process, and so a separate budget.
//!
//! What a HOST sees is the same thing, and that is the store's design rather than a defect
//! here: after one runaway `sh:select`, the subset validator refuses (transiently, typed) until
//! the straggler ends, rather than letting each request pin another core.

use ikigai_core::Error;
use ikigai_shacl::core_shacl::validate_report;

const HEAD: &str = "@prefix sh: <http://www.w3.org/ns/shacl#> .\n\
                    @prefix ex: <http://example.org/> .\n";

#[test]
fn a_slow_select_is_answered_at_the_time_budget() {
    // A six-way cross product over a few dozen triples: inside every size, nesting and algebra
    // bound, and minutes of work (ikigai-store's budget module measures the shape). The caller
    // is answered with a typed timeout at the base budget (5 s), never with a partial report.
    let data: String = (0..40)
        .map(|i| format!("<urn:s{i}> <urn:p> <urn:o{i}> .\n"))
        .chain(std::iter::once(
            "<urn:x> a <http://example.org/Person> .\n".to_string(),
        ))
        .collect();
    let body = "ex:S sh:targetClass ex:Person ; sh:sparql [ sh:select \"\"\"SELECT $this (COUNT(*) AS ?n) WHERE { \
                ?a ?b ?c . ?d ?e ?f . ?g ?h ?i . ?j ?k ?l . ?m ?n0 ?o . ?q ?r ?t } GROUP BY $this\"\"\" ] .";
    let started = std::time::Instant::now();
    let outcome = validate_report(&data, &format!("{HEAD}{body}"));
    let took = started.elapsed();
    assert!(matches!(outcome, Err(Error::Timeout(_))), "{outcome:?}");
    assert!(
        took < std::time::Duration::from_secs(30),
        "answered after {took:?}"
    );
}
