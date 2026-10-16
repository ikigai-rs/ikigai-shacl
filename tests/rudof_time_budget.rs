//! The rudof path's time budget (ledger #1735), in a test binary of its own.
//!
//! `urn:shacl:validate` on the rudof path (the default feature) used to validate synchronously
//! with no time budget at all, so a caller with a large data graph held a thread, and a core,
//! for as long as rudof took. `ikigai_vocab::SHAPES` is quadratic on a chain of piped steps
//! (its `edge-cycle` shape follows each step's upstream chain to its head): measured 2026-10-16
//! in release, 1,600 steps 0.96 s, 3,200 steps 3.6 s, 6,400 steps 13.5 s, and so about two
//! minutes for the 20,000-step plan of ikigai-cli's `plan_size.rs` (ledger #1733), with no
//! refusal. The subset validator already ran under the store's `EvaluationBudget`; now rudof
//! runs in the same one, with the same grants.
//!
//! ★ Why its own binary, like `tests/time_budget.rs` and `tests/one_runaway.rs`: rudof cannot be
//! stopped partway, so every runaway below is still validating when this test ends, holding a
//! core and one of the process's overdue slots until the process exits. And this test fills
//! every slot on purpose, after which every validation in the process is refused.
//!
//! Nothing here is a stopwatch. A `Timeout` only ever comes from the budget, and the budget it
//! names comes from the caller's capability; the cap is shown by WHICH answer each call gets,
//! counted against the cap the crate states.
#![cfg(feature = "rudof")]

use std::sync::Arc;

use futures::executor::block_on;
use ikigai_core::{ArgRef, Capability, Error, Iri, Kernel, Representation, Request, Result, Verb};
use ikigai_store::budget::{cap_budget, default_max_overdue};

/// Steps in the runaway plan, chosen for two margins at once (measured 2026-10-16 on an 18-core
/// laptop): rudof validating it against `ikigai_vocab::SHAPES` takes 62 s in release (under
/// root's 120 s ceiling), ten times the 6 s the larger budget below allows, and longer in
/// debug; while the premise (parsing it and validating it against a linear shapes graph) takes
/// 0.25 s in release and 1.3 s in debug, inside the 5 s base budget with room for a slower
/// machine. (ikigai-cli's 20,000-step plan widens the first margin, and spends half the budget
/// on the second in debug.)
const STEPS: usize = 10_000;

/// A plan of `n` steps, each piping from the one before (`plan_size.rs`'s `chain`): `5n + 1`
/// triples, plus one naming `tag`, so no two runaways send the same request and no layer can
/// answer two of them with one evaluation.
fn chain(n: usize, tag: &str) -> String {
    let mut out = String::from(
        "@prefix ik: <https://ikigai-rs.dev/ns#> .\n\
         @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .\n\n\
         <urn:plan:long> a ik:Process ;\n",
    );
    out.push_str(&format!("    rdfs:comment \"{tag}\" ;\n"));
    let steps: Vec<String> = (1..=n)
        .map(|i| format!("<urn:plan:long:step:{i}>"))
        .collect();
    out.push_str(&format!(
        "    ik:step {} ;\n    ik:result <urn:plan:long:step:{n}> .\n",
        steps.join(" , ")
    ));
    for i in 1..=n {
        out.push_str(&format!(
            "\n<urn:plan:long:step:{i}> a ik:Step ;\n    ik:verb \"Source\" ;\n    \
             ik:resolves <urn:echo>"
        ));
        if i > 1 {
            out.push_str(&format!(
                " ;\n    ik:pipeFrom <urn:plan:long:step:{}>",
                i - 1
            ));
        }
        out.push_str(" .\n");
    }
    out
}

/// A shapes graph linear in the plan: one property shape per step.
const CHEAP: &str = "@prefix sh: <http://www.w3.org/ns/shacl#> .\n\
                     @prefix ik: <https://ikigai-rs.dev/ns#> .\n\
                     <urn:shape:step> a sh:NodeShape ; sh:targetClass ik:Step ;\n\
                     sh:property [ sh:path ik:verb ; sh:minCount 1 ; sh:maxCount 1 ] .";

/// `urn:shacl:validate` through the kernel, as `caller`, for the JSON face.
fn validate(
    kernel: &Kernel,
    data: &str,
    shapes: &str,
    caller: &Capability,
) -> Result<Representation> {
    let request = Request::new(
        Verb::Source,
        Iri::parse("urn:shacl:validate").expect("a valid IRI"),
    )
    .with_arg("data", ArgRef::Inline(data.as_bytes().to_vec()))
    .with_arg("shapes", ArgRef::Inline(shapes.as_bytes().to_vec()))
    .with_arg("as", ArgRef::Inline(b"application/json".to_vec()));
    block_on(kernel.issue(request, caller))
}

fn conforms(answer: &Representation) -> bool {
    let report: ikigai_shacl::Report =
        serde_json::from_slice(&answer.bytes).expect("the JSON face parses");
    report.conforms
}

#[test]
fn a_runaway_validation_is_answered_at_its_budget_and_the_abandoned_work_is_capped() {
    let kernel = Kernel::new(Arc::new(ikigai_shacl::space()));
    // No grants: the base budget, 5 s.
    let anonymous = Capability::scoped(Vec::<String>::new());

    // 1. An ordinary validation is answered as before, and, as the PREMISE of what follows,
    //    the runaway's own data parses and validates against a linear shapes graph inside the
    //    base budget. So a timeout below is spent in the validation, not in the parse; were the
    //    parse alone past the budget, the timeouts would prove nothing about rudof, and this
    //    fails here instead of passing there.
    let answer = validate(&kernel, &chain(STEPS, "premise"), CHEAP, &anonymous)
        .expect("the runaway's data, against a linear shapes graph, is answered");
    assert!(conforms(&answer));
    let bad = "@prefix ik: <https://ikigai-rs.dev/ns#> .\n<urn:s> a ik:Step .";
    let answer = validate(&kernel, bad, CHEAP, &anonymous).expect("an ordinary validation");
    assert!(!conforms(&answer), "a step with no verb violates the shape");

    // 2. The runaways: `ikigai_vocab::SHAPES`, the shapes the plan doors validate with, over
    //    the 10,000-step plan, ONE MORE than the process's cap (the crate's stated floor of two,
    //    `core_shacl::MAX_OVERDUE_FLOOR`, or the store's default when larger), all at once.
    //    `cap` of them take a slot and are answered with a typed timeout naming the budget
    //    THEIR capability gets; the one left over waits for a slot within its own budget, none
    //    comes free, and it is refused `Unavailable` without ever starting. The first two hold
    //    a 6 s grant and the rest none, so at least one 6 s timeout is always seen, whichever
    //    request is left over. This is what the in-flight cap of ikigai-store 0.2.21 buys (the
    //    floor in Cargo.toml): before it, all `cap + 1` started, and all could outlive their
    //    callers. A cap computed wrong here fails too: too high and two are refused, too low and
    //    none is.
    let cap = default_max_overdue().max(2);
    let granted = Capability::scoped([cap_budget(6_000)]);
    let outcomes: Vec<(u128, Result<Representation>)> = std::thread::scope(|scope| {
        let runs: Vec<_> = (0..=cap)
            .map(|k| {
                let kernel = &kernel;
                let (caller, millis) = if k < 2 {
                    (granted.clone(), 6_000)
                } else {
                    (anonymous.clone(), 5_000)
                };
                scope.spawn(move || {
                    let plan = chain(STEPS, &format!("runaway {k}"));
                    (
                        millis,
                        validate(kernel, &plan, ikigai_vocab::SHAPES, &caller),
                    )
                })
            })
            .collect();
        runs.into_iter()
            .map(|run| run.join().expect("a runaway's caller"))
            .collect()
    });
    let (mut timeouts, mut granted_timeouts, mut refused) = (0, 0, 0);
    for (millis, outcome) in &outcomes {
        match outcome {
            Err(Error::Timeout(sentence)) => {
                assert!(
                    sentence.contains(&format!("time budget of {millis} ms")),
                    "the timeout names the {millis} ms its capability gets: {sentence}"
                );
                timeouts += 1;
                granted_timeouts += usize::from(*millis == 6_000);
            }
            Err(Error::Unavailable(_)) => refused += 1,
            other => panic!("expected a timeout at {millis} ms or Unavailable, got {other:?}"),
        }
    }
    assert_eq!(
        (timeouts, refused),
        (cap, 1),
        "{cap} validations run at once, and the one more is refused: {outcomes:?}"
    );
    assert!(
        granted_timeouts >= 1,
        "a 6 s grant is honored: {outcomes:?}"
    );

    // 3. Every slot now holds a validation still running after its caller was answered, so the
    //    next one, however small, is refused at once with a transient `Unavailable` rather than
    //    started: abandoned rudof work can hold at most `cap` cores. (A request step 1 did not
    //    send: the kernel caches that one's answer, and would serve it without validating.)
    let fresh = "@prefix ik: <https://ikigai-rs.dev/ns#> .\n<urn:t> a ik:Step .";
    match validate(&kernel, fresh, CHEAP, &anonymous) {
        Err(Error::Unavailable(sentence)) => {
            assert!(sentence.contains("still running"), "{sentence}")
        }
        other => panic!("expected Unavailable with {cap} validations overdue, got {other:?}"),
    }
}
