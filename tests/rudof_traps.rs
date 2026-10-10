//! Two traps in rudof's validator that a shapes graph can spring (ledger #1102), each with a
//! CONTROL that runs rudof directly, with no guard of ours, so the refusal or the fix beside it
//! is shown to answer something real. If a control ever stops reproducing, a rudof release has
//! changed the code it describes: re-derive the guard rather than delete the control.
//!
//! 1. **WHERE found in uppercased text.** rudof's `inject_values_into_where` (shacl 0.3.24,
//!    `validator/constraints/sparql/mod.rs`) finds `WHERE` in `query.to_uppercase()` and slices
//!    the ORIGINAL query at that byte offset. Uppercasing changes byte length for some
//!    characters (`ı` U+0131, two bytes, uppercases to `I`, one), so text before `WHERE` moves the
//!    offset: off a character boundary it PANICS, and on one it splices the `VALUES ?this`
//!    binding somewhere else (into a comment, here), so the constraint runs unbound and reports
//!    nodes that are not focus nodes. `urn:shacl:validate` refuses such a select by name.
//! 2. **SPARQL evaluated on rayon's workers.** rudof validates each topological level of
//!    shapes with `par_iter_mut`. A level of ONE shape is not split and runs on the caller's
//!    thread, but a level of two or more is, and then every shape in it runs on rayon's global
//!    pool, whose threads have the default 2 MiB stack, not on the thread `urn:shacl:validate`
//!    sized for the longest query (ledger #963). A flat `||` chain that the sized thread holds
//!    then aborts the whole process. Validation now runs on a one-thread pool of that size.
//!
//! The process-killing probes run in a CHILD PROCESS (this test binary re-executed with the
//! probe named in its environment), as in `tests/sparql_stack.rs`, so an abort is a failed
//! assertion here rather than a dead test binary.

use futures::executor::block_on;
use ikigai_core::{ArgRef, Capability, Error, Iri, Kernel, Request, Verb};
use rudof_rdf::rdf_core::RDFFormat;
use rudof_rdf::rdf_impl::ReaderMode;
use shacl::ir::IRSchema;
use shacl::rdf::ShaclParser;
use shacl::validator::processor::{DataValidation, ShaclProcessor};
use shacl::validator::report::ValidationReport;
use shacl::validator::{ShaclConfig, ShaclValidationMode};
use sparql_service::RdfData;
use std::process::Command;
use std::sync::{Arc, Mutex};

const PROBE: &str = "IKIGAI_SHACL_RUDOF_TRAP";

/// `ex:a` is the only focus node (the only `ex:Person`); `ex:c` has an `ex:p` too.
const DATA: &str = "@prefix ex: <http://example.org/> .\n\
                    ex:a a ex:Person ; ex:p ex:b .\n\
                    ex:c ex:p ex:d .\n";

/// Two dotless i (one byte shorter each, uppercased) before a three-byte arrow: the offset rudof
/// finds lands two bytes early, inside the arrow, and the slice panics.
const PANICS: &str =
    "SELECT $this # \u{131}\u{131}\u{2192}\nWHERE { $this <http://example.org/p> ?o }";

/// Two dotless i before a `{` in the comment: the offset lands two bytes early, ON that `{`,
/// so rudof injects `VALUES ?this { … }` into the comment and the select runs unbound.
const MISPLACES: &str = "SELECT $this # \u{131}\u{131}{\nWHERE { $this <http://example.org/p> ?o }";

/// Non-ASCII that uppercases to the same byte length (`é` → `É`, `ß` → `SS`): nothing moves.
const SAME_LENGTH: &str =
    "SELECT $this # \u{e9}t\u{e9} stra\u{df}e\nWHERE { $this <http://example.org/p> ?o }";

/// A node shape on `ex:Person` with one `sh:select`, plus (when `second`) another node shape
/// with a target, so the first topological level holds two shapes and rayon splits it.
fn shapes(select: &str, second: bool) -> String {
    let mut ttl = format!(
        "@prefix sh: <http://www.w3.org/ns/shacl#> .\n@prefix ex: <http://example.org/> .\n\
         ex:S a sh:NodeShape ; sh:targetClass ex:Person ;\n  \
         sh:sparql [ sh:select \"\"\"{select}\"\"\" ] .\n"
    );
    if second {
        ttl.push_str("ex:T a sh:NodeShape ; sh:targetClass ex:Person ; sh:nodeKind sh:IRI .\n");
    }
    ttl
}

/// rudof alone: parse, compile and validate with none of `urn:shacl:validate`'s guards.
fn rudof_direct(data: &str, shapes: &str) -> Result<ValidationReport, String> {
    let read = |ttl: &str| {
        RdfData::from_str(ttl, &RDFFormat::Turtle, None, &ReaderMode::default()).unwrap()
    };
    let schema: IRSchema = ShaclParser::new(read(shapes))
        .parse()
        .unwrap()
        .try_into()
        .unwrap();
    let mut validator: DataValidation = read(data).into();
    validator
        .validate(
            &schema,
            &ShaclValidationMode::Native,
            &ShaclConfig::default(),
        )
        .map_err(|e| e.to_string())
}

fn through_endpoint(data: &str, shapes: &str) -> ikigai_core::Result<String> {
    let kernel = Kernel::new(Arc::new(ikigai_shacl::space()));
    let request = Request::new(Verb::Source, Iri::parse("urn:shacl:validate").unwrap())
        .with_arg("data", ArgRef::Inline(data.as_bytes().to_vec()))
        .with_arg("shapes", ArgRef::Inline(shapes.as_bytes().to_vec()))
        .with_arg("as", ArgRef::Inline(b"application/json".to_vec()));
    block_on(kernel.issue(request, &Capability::root()))
        .map(|rep| String::from_utf8_lossy(&rep.bytes).into_owned())
}

fn refused_for_uppercasing(result: &ikigai_core::Result<String>) -> bool {
    matches!(result, Err(Error::InvalidArgument { name, detail })
        if name == "shapes" && detail.contains("uppercase") && detail.contains("Nothing was evaluated"))
}

// ------------------------------------------------------------------ 1. WHERE in uppercased text

#[test]
fn control_rudof_panics_on_an_offset_found_in_uppercased_text() {
    let joined = std::thread::spawn(|| rudof_direct(DATA, &shapes(PANICS, false))).join();
    assert!(
        joined.is_err(),
        "rudof no longer panics on a `WHERE` found in uppercased text, so the refusal below \
         answers nothing: re-read `inject_values_into_where` ({:?})",
        joined.map(|r| r.map(|r| r.results().len()))
    );
}

#[test]
fn control_rudof_misplaces_values_when_the_offset_lands_on_a_boundary() {
    // Right: one result, for `ex:a`, the only focus node. rudof binds nothing and reports `ex:c`.
    let right = rudof_direct(
        DATA,
        &shapes(
            "SELECT $this WHERE { $this <http://example.org/p> ?o }",
            false,
        ),
    )
    .unwrap();
    let wrong = rudof_direct(DATA, &shapes(MISPLACES, false)).unwrap();
    let focus = |r: &ValidationReport| {
        let mut nodes: Vec<String> = r
            .results()
            .iter()
            .map(|r| r.focus_node().to_string())
            .collect();
        nodes.sort();
        nodes
    };
    assert_eq!(focus(&right), ["http://example.org/a"]);
    assert_eq!(
        focus(&wrong),
        ["http://example.org/a", "http://example.org/c"],
        "rudof no longer misplaces `VALUES`: re-read `inject_values_into_where`"
    );
}

#[test]
fn the_endpoint_refuses_a_select_that_uppercasing_resizes_before_where() {
    for (name, select) in [("panics", PANICS), ("misplaces", MISPLACES)] {
        let result = through_endpoint(DATA, &shapes(select, false));
        assert!(refused_for_uppercasing(&result), "{name}: {result:?}");
        // Wherever the shape sits: a level of two shapes reaches rudof the same way.
        let result = through_endpoint(DATA, &shapes(select, true));
        assert!(
            refused_for_uppercasing(&result),
            "{name} (two shapes): {result:?}"
        );
    }
}

#[test]
fn non_ascii_that_keeps_its_length_still_validates() {
    let result = through_endpoint(DATA, &shapes(SAME_LENGTH, false)).unwrap();
    assert!(result.contains("http://example.org/a"), "{result}");
    assert!(!result.contains("http://example.org/c"), "{result}");
}

// ------------------------------------------------------------------ 2. rayon's workers

/// The child's half: inert unless a parent named a probe. Prints one `OUTCOME` line and exits.
#[test]
fn probe_child() {
    let Ok(spec) = std::env::var(PROBE) else {
        return;
    };
    let outcome = match spec.as_str() {
        // Which thread rudof runs a two-shape level's constraint on: the panic of trap 1
        // carries the thread's name out through a panic hook.
        "which-thread" => {
            let seen = Arc::new(Mutex::new(Vec::<String>::new()));
            let record = Arc::clone(&seen);
            std::panic::set_hook(Box::new(move |_| {
                let name = std::thread::current()
                    .name()
                    .unwrap_or("<unnamed>")
                    .to_string();
                record.lock().unwrap().push(name);
            }));
            let _ = std::thread::Builder::new()
                .name("caller".into())
                .spawn(|| rudof_direct(DATA, &shapes(PANICS, true)))
                .unwrap()
                .join();
            let _ = std::panic::take_hook();
            let names = seen.lock().unwrap().clone();
            format!("panicked on {names:?}")
        }
        // A flat `||` chain, through the endpoint, in a level of two shapes, from a 2 MiB
        // caller thread (a tokio worker's size).
        "chain-two-shapes" => std::thread::Builder::new()
            .stack_size(2 << 20)
            .spawn(|| {
                let select = format!(
                    "SELECT $this WHERE {{ FILTER(false{}) }}",
                    "||false".repeat(30_000)
                );
                match through_endpoint(DATA, &shapes(&select, true)) {
                    Ok(text) => format!("ok {}", text.replace('\n', " ")),
                    Err(e) => format!("err {e}"),
                }
            })
            .unwrap()
            .join()
            .unwrap(),
        other => panic!("no probe named {other}"),
    };
    println!("\nOUTCOME {outcome}");
    std::process::exit(0);
}

/// Run one probe in a child: `Ok(what it said)`, or `Err(how it died)`.
fn probe(name: &str) -> Result<String, String> {
    let out = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "probe_child", "--nocapture", "--test-threads=1"])
        .env(PROBE, name)
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    if !out.status.success() {
        let why = stderr
            .lines()
            .find(|l| l.contains("overflow"))
            .unwrap_or(&stderr);
        return Err(format!("{} — {why}", out.status));
    }
    let at = stdout
        .find("\nOUTCOME ")
        .unwrap_or_else(|| panic!("the `{name}` probe reported nothing: {stdout}"));
    Ok(stdout[at + "\nOUTCOME ".len()..]
        .lines()
        .next()
        .unwrap_or("")
        .to_string())
}

#[test]
fn control_rudof_runs_a_level_of_two_shapes_off_the_calling_thread() {
    let said = probe("which-thread").unwrap();
    assert!(
        said.starts_with("panicked on [") && !said.contains("\"caller\""),
        "rudof ran a two-shape level on the calling thread, so the pool around it is no longer \
         what keeps SPARQL on a sized stack: re-read rudof's `ShaclProcessor::validate` ({said})"
    );
}

#[test]
fn a_level_of_two_shapes_validates_on_the_sized_stack() {
    // 3,000 terms already aborted a rayon worker in a debug build before the fix; a lone shape
    // (not split, so on the sized thread) runs 140,000.
    let said = probe("chain-two-shapes")
        .unwrap_or_else(|died| panic!("a two-shape level did not survive: {died}"));
    assert!(said.starts_with("ok "), "{said}");
}
