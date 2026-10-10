//! Caller-supplied SPARQL inside a shapes graph is bounded before rudof parses it, and
//! validation runs on a stack sized for what it will parse (ledger #963).
//!
//! The claim: a `sh:select` nested or chained past what a 2 MiB thread holds aborts the
//! whole process, because oxigraph's SPARQL parser and evaluator are recursive and Rust
//! aborts on a stack overflow, on any thread. rudof parses each `sh:select` once per focus
//! node, inside `validate`, so nothing the caller gets back can carry the failure. Every
//! reproduction here therefore runs in a CHILD PROCESS (this test binary re-executed with one
//! probe named in its environment) on a 2 MiB thread, the size of a tokio worker's, and the
//! parent asserts on the child's exit: an abort kills the child, never this binary, and reads
//! as a failure with the signal named.
//!
//! These tests use only the API that predates the fix (`space()` through a kernel), so they
//! compile, and fail with the child aborted, against 0.2.0.

use futures::executor::block_on;
use ikigai_core::{ArgRef, Capability, Iri, Kernel, Request, Verb};
use std::process::Command;
use std::sync::Arc;

const PROBE: &str = "IKIGAI_SHACL_STACK_PROBE";
/// The nesting bound, restated so these tests compile against 0.2.0, which has no constant to
/// name. A unit test in `src/limits.rs` pins `MAX_SPARQL_NESTING` to the same number.
const BOUND: usize = 64;

const HEAD: &str = "@prefix sh: <http://www.w3.org/ns/shacl#> .\n\
                    @prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n\
                    @prefix ex: <http://example.org/> .\n";

const DATA: &str = "@prefix ex: <http://example.org/> .\n\
                    ex:a a ex:Person ; ex:p ex:b .\n";

/// A node shape with one `sh:select`.
fn select_shape(select: &str) -> String {
    format!(
        "{HEAD}ex:S a sh:NodeShape ; sh:targetClass ex:Person ;\n  \
         sh:sparql [ sh:select \"\"\"{select}\"\"\" ] .\n"
    )
}

/// A SHACL path `depth` levels deep: `sh:zeroOrOnePath` around `sh:zeroOrOnePath` … around
/// `ex:p`. rudof renders it into a `sh:select`'s `$PATH` as `((…(<p>)?…)?)?`.
fn nested_path(depth: usize) -> String {
    format!(
        "{}ex:p{}",
        "[ sh:zeroOrOnePath ".repeat(depth),
        " ]".repeat(depth)
    )
}

/// `(data, shapes)` for one probe, named so a child can rebuild it.
fn case(name: &str, n: usize) -> (String, String) {
    match name {
        // The claim's own shape: brackets, one byte a level.
        "select-parens" => (
            DATA.to_string(),
            select_shape(&format!(
                "SELECT $this WHERE {{ FILTER({}false{}) }}",
                "(".repeat(n),
                ")".repeat(n)
            )),
        ),
        // Not nesting: a FLAT `||` chain the evaluator still recurses over once per term,
        // and a shape a generated constraint may really have. Nothing refuses it; it runs on
        // the stack validation is given.
        "select-or-chain" => (
            DATA.to_string(),
            select_shape(&format!(
                "SELECT $this WHERE {{ FILTER(false{}) }}",
                "||false".repeat(n)
            )),
        ),
        // Nesting that is NOT in any `sh:select` literal: rudof substitutes the shape's path
        // for `$PATH`, so a deep `sh:path` nests the query it builds.
        "path-sparql" => (
            DATA.to_string(),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetClass ex:Person ;\n  \
                 sh:property ex:P .\n\
                 ex:P sh:path {} ;\n  \
                 sh:sparql [ sh:select \"\"\"SELECT $this ?value WHERE {{ $this $PATH ?value . FILTER(false) }}\"\"\" ] .\n",
                nested_path(n)
            ),
        ),
        // The same deep path with no SPARQL at all: rudof's own path parse and evaluation.
        "path-plain" => (
            DATA.to_string(),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetClass ex:Person ;\n  \
                 sh:property [ sh:path {} ; sh:minCount 1 ] .\n",
                nested_path(n)
            ),
        ),
        // Nesting from a PREFIX NAME: rudof writes each `sh:declare` into a `PREFIX p: <ns>`
        // header unescaped, so a prefix name can carry a whole query of its own, which the
        // parser recurses through before it fails on what follows.
        "prefix-inject" => (
            DATA.to_string(),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetClass ex:Person ;\n  \
                 sh:sparql [ sh:prefixes ex:decls ;\n    \
                 sh:select \"\"\"SELECT $this WHERE {{ FILTER(false) }}\"\"\" ] .\n\
                 ex:decls sh:declare [ sh:namespace \"urn:ns:\"^^xsd:anyURI ;\n  \
                 sh:prefix \"x: <urn:a> SELECT * WHERE {{ FILTER({}1{}) }} #\" ] .\n",
                "(".repeat(n),
                ")".repeat(n)
            ),
        ),
        // A shape nested in shapes: `sh:not [ sh:not [ … ] ]`.
        "not-nest" => (
            DATA.to_string(),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetClass ex:Person ;\n  sh:not {}[ sh:class ex:Nothing ]{} .\n",
                "[ sh:not ".repeat(n),
                " ]".repeat(n)
            ),
        ),
        // A data graph whose value node is an RDF 1.2 triple term nested `n` deep, reported
        // as a violation's `sh:value`: rudof writes the focus node into the query's VALUES.
        "data-triple-term" => (
            format!(
                "@prefix ex: <http://example.org/> .\n\
                 ex:a a ex:Person ; ex:p {}ex:o{} .\n",
                "<<( ex:s ex:p ".repeat(n),
                " )>>".repeat(n)
            ),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetClass ex:Person ;\n  \
                 sh:property [ sh:path ex:p ;\n    \
                 sh:sparql [ sh:select \"\"\"SELECT $this WHERE {{ }}\"\"\" ] ] .\n"
            ),
        ),
        // Data nesting the Turtle parser handles itself: nested collections.
        "data-collections" => (
            format!(
                "@prefix ex: <http://example.org/> .\n\
                 ex:a a ex:Person ; ex:p {}{} .\n",
                "(".repeat(n),
                ")".repeat(n)
            ),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetClass ex:Person ;\n  \
                 sh:property [ sh:path ex:p ; sh:minCount 1 ] .\n"
            ),
        ),
        other => panic!("no probe named {other}"),
    }
}

fn issue(kernel: &Kernel, data: String, shapes: String) -> ikigai_core::Result<String> {
    let req = Request::new(Verb::Source, Iri::parse("urn:shacl:validate").unwrap())
        .with_arg("data", ArgRef::Inline(data.into_bytes()))
        .with_arg("shapes", ArgRef::Inline(shapes.into_bytes()))
        .with_arg("as", ArgRef::Inline(b"application/json".to_vec()));
    block_on(kernel.issue(req, &Capability::root()))
        .map(|rep| String::from_utf8_lossy(&rep.bytes).into_owned())
}

fn kernel() -> Kernel {
    Kernel::new(Arc::new(ikigai_shacl::space()))
}

/// The child's half: inert unless a parent named a probe. Runs it on a 2 MiB thread, a tokio
/// worker's stack, prints the outcome, and exits before the harness can.
#[test]
fn probe_child() {
    let Ok(spec) = std::env::var(PROBE) else {
        return;
    };
    let (name, n) = spec.split_once(':').unwrap();
    let (data, shapes) = case(name, n.parse().unwrap());
    let outcome = std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(move || match issue(&kernel(), data, shapes) {
            Ok(text) => format!("ok {}", text.replace('\n', " ")),
            Err(e) => format!("err {}", e.to_string().replace('\n', " ")),
        })
        .unwrap()
        .join()
        .unwrap();
    println!("\nOUTCOME {outcome}");
    std::process::exit(0);
}

/// Run one probe in a child: `Ok(what it said)`, or `Err(how it died)`.
fn try_probe(name: &str, n: usize) -> Result<String, String> {
    let out = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "probe_child", "--nocapture", "--test-threads=1"])
        .env(PROBE, format!("{name}:{n}"))
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    if !out.status.success() {
        return Err(format!(
            "{} — {}",
            out.status,
            stderr
                .lines()
                .find(|l| l.contains("overflow"))
                .unwrap_or(&stderr)
        ));
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

/// The parent's half: an abort is the defect.
fn probe(name: &str, n: usize) -> String {
    try_probe(name, n).unwrap_or_else(|died| {
        panic!("the `{name}` probe at {n} did not survive a 2 MiB thread: {died}")
    })
}

/// Every probe at several sizes, printed: the evidence table in the PR. Not an assertion.
///
/// ⚠ Four rows still DIE at 300 or 3000 after ledger #963, and none of them is SPARQL:
/// `path-plain` (rudof's recursive `sh:path` parser), `not-nest` (rudof's recursive shape
/// compiler, ~76 levels of `sh:not` on 2 MiB in a debug build), `path-sparql` at 3000 (the same
/// path parser, before any query exists) and `data-triple-term` (oxrdf's recursive `Clone` of a
/// nested RDF 1.2 triple term, inside the Turtle parser). They are reported, not fixed here.
///
///     cargo test --test sparql_stack -- --ignored --nocapture survey
#[test]
#[ignore]
fn survey() {
    for name in [
        "select-parens",
        "select-or-chain",
        "path-sparql",
        "path-plain",
        "prefix-inject",
        "not-nest",
        "data-triple-term",
        "data-collections",
    ] {
        for n in [50, 300, 3000] {
            let line = match try_probe(name, n) {
                Ok(said) => said.chars().take(160).collect::<String>(),
                Err(died) => format!("DIED {}", died.chars().take(160).collect::<String>()),
            };
            println!("{name:>18} {n:>5}: {line}");
        }
    }
}

fn refused(outcome: &str) -> bool {
    outcome.starts_with("err invalid argument `shapes`") && outcome.contains("deeper than 64")
}

// ------------------------------------------------------------------ the reproduction

#[test]
fn deep_parentheses_in_a_select_are_refused_and_abort_nothing() {
    // 300 aborted a 2 MiB thread through this endpoint in a debug build; 3000 is the store's
    // reproduction size.
    for n in [300, 3000] {
        let outcome = probe("select-parens", n);
        assert!(refused(&outcome), "{n}: {outcome}");
    }
}

#[test]
fn a_long_flat_chain_runs_on_the_stack_validation_is_given() {
    // Not nesting, so nothing refuses it, and 300 terms aborted a 2 MiB thread. It runs.
    let outcome = probe("select-or-chain", 3000);
    assert!(outcome.starts_with("ok "), "{outcome}");
}

#[test]
fn a_deep_path_written_into_dollar_path_is_refused() {
    // No `sh:select` literal here nests at all: the depth arrives through the shape's path.
    let outcome = probe("path-sparql", 300);
    assert!(
        outcome.starts_with("err invalid argument `shapes`") && outcome.contains("$PATH"),
        "{outcome}"
    );
}

#[test]
fn a_prefix_name_carrying_a_query_is_refused() {
    // Nor here: the depth arrives through a `sh:prefix`, written into the PREFIX header.
    let outcome = probe("prefix-inject", 3000);
    assert!(refused(&outcome), "{outcome}");
}

// ------------------------------------------------------------------ at and under the bound

fn validate_inline(shapes: &str) -> ikigai_core::Result<String> {
    issue(&kernel(), DATA.to_string(), shapes.to_string())
}

#[test]
fn a_select_at_the_bound_runs_and_one_past_it_is_refused() {
    // `WHERE { FILTER(` is two levels (the injected `VALUES ?this { … }` closes before it), so
    // `BOUND - 2` more brings the query rudof parses to exactly the bound.
    let at = |n: usize| {
        select_shape(&format!(
            "SELECT $this WHERE {{ FILTER({}false{}) }}",
            "(".repeat(n),
            ")".repeat(n)
        ))
    };
    let ok = validate_inline(&at(BOUND - 2)).unwrap();
    assert!(ok.contains("\"conforms\": true"), "{ok}");
    let over = validate_inline(&at(BOUND - 1)).unwrap_err();
    assert!(
        matches!(&over, ikigai_core::Error::InvalidArgument { name, .. } if name == "shapes"),
        "{over}"
    );
}

#[test]
fn every_sparql_literal_is_bounded_even_one_rudof_never_runs() {
    // rudof 0.3.24 does not evaluate `sh:ask`; it is still SPARQL text SHACL defines, and it is
    // refused before rudof compiles anything.
    let shapes = format!(
        "{HEAD}ex:S a sh:NodeShape ; sh:targetClass ex:Person .\n\
         ex:C sh:ask \"ASK {{ FILTER({}1{}) }}\" .\n",
        "(".repeat(100),
        ")".repeat(100)
    );
    let err = validate_inline(&shapes).unwrap_err().to_string();
    assert!(
        err.contains("`shapes`") && err.contains("deeper than 64"),
        "{err}"
    );
}

#[test]
fn brackets_in_strings_and_comments_of_a_select_are_not_nesting() {
    let deep = "(".repeat(500);
    let shapes = select_shape(&format!(
        "SELECT $this WHERE {{ FILTER(\"{deep}\" != '{deep}') # {deep}\n }}"
    ));
    let ok = validate_inline(&shapes).unwrap();
    assert!(ok.contains("\"violations\""), "{ok}");
}
