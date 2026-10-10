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
//! Ledger #992 extended the same harness past SPARQL: nested shapes, deep and cyclic paths,
//! `owl:imports` chains and nested RDF 1.2 triple terms aborted the process the same way, from
//! rudof's shape compiler and path parser and from oxrdf, and are refused now (`src/depth.rs`).
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
        // ---- ledger #992: depth that is not SPARQL at all.
        //
        // The same nested triple term, in the SHAPES argument: oxttl parses both alike.
        "shapes-triple-term" => (
            DATA.to_string(),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetClass ex:Person ;\n  \
                 sh:property [ sh:path ex:p ; sh:minCount 1 ] .\n\
                 ex:S ex:note {}ex:o{} .\n",
                "<<( ex:s ex:p ".repeat(n),
                " )>>".repeat(n)
            ),
        ),
        // RDF 1.2 reified triples nested in subject position: `<< << … >> ex:p ex:o >>`.
        "data-reified" => (
            format!(
                "@prefix ex: <http://example.org/> .\n\
                 ex:a a ex:Person ; ex:p ex:b .\n\
                 {}ex:s{} ex:q ex:r .\n",
                "<< ".repeat(n),
                " ex:p ex:o >>".repeat(n)
            ),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetClass ex:Person ;\n  \
                 sh:property [ sh:path ex:p ; sh:minCount 1 ] .\n"
            ),
        ),
        // RDF 1.2 annotations nested in annotations: `{| ex:p ex:o {| … |} |}`.
        "data-annotation" => (
            format!(
                "@prefix ex: <http://example.org/> .\n\
                 ex:a a ex:Person ; ex:p ex:b {}{}.\n",
                "{| ex:p ex:o ".repeat(n),
                "|} ".repeat(n)
            ),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetClass ex:Person ;\n  \
                 sh:property [ sh:path ex:p ; sh:minCount 1 ] .\n"
            ),
        ),
        // A path that is its own operand: rudof's path parser keeps no visited set.
        "path-cycle" => (
            DATA.to_string(),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetClass ex:Person ;\n  \
                 sh:property [ sh:path _:pp ; sh:minCount 1 ] .\n\
                 _:pp sh:inversePath _:pp .\n"
            ),
        ),
        // Named shapes chained by `sh:node`, the last pointing at none (`n` > 0).
        "node-chain" => (
            DATA.to_string(),
            format!(
                "{HEAD}ex:S0 a sh:NodeShape ; sh:targetClass ex:Person .\n{}",
                (0..n)
                    .map(|i| format!("ex:S{i} sh:node ex:S{} .\n", i + 1))
                    .collect::<String>()
            ),
        ),
        // The same chain closed into a ring: the last shape points back at the first.
        "node-ring" => (
            DATA.to_string(),
            format!(
                "{HEAD}ex:S0 a sh:NodeShape ; sh:targetClass ex:Person .\n{}",
                (0..n)
                    .map(|i| format!("ex:S{i} sh:node ex:S{} .\n", (i + 1) % n))
                    .collect::<String>()
            ),
        ),
        // A long RDF list: rudof's list parser recurses once per element.
        "list-in" => (
            DATA.to_string(),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetClass ex:Person ;\n  \
                 sh:property [ sh:path ex:p ; sh:in ( {}ex:b ) ] .\n",
                "ex:v ".repeat(n)
            ),
        ),
        // A long `sh:or`: a list whose members are shapes.
        "list-or" => (
            DATA.to_string(),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetClass ex:Person ;\n  \
                 sh:or ( {}[ sh:class ex:Person ] ) .\n",
                "[ sh:class ex:Nothing ] ".repeat(n)
            ),
        ),
        // A recursive shape over a data chain `n` long: depth that lives in the DATA.
        "data-chain" => (
            format!(
                "@prefix ex: <http://example.org/> .\n{}",
                (0..n)
                    .map(|i| format!("ex:n{i} ex:next ex:n{} .\n", i + 1))
                    .collect::<String>()
            ),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetNode ex:n0 ;\n  \
                 sh:property [ sh:path ex:next ; sh:node ex:S ] .\n"
            ),
        ),
        // `sh:prefixes` followed along an `owl:imports` chain.
        "imports-chain" => (
            DATA.to_string(),
            format!(
                "{HEAD}@prefix owl: <http://www.w3.org/2002/07/owl#> .\n\
                 ex:S a sh:NodeShape ; sh:targetClass ex:Person ;\n  \
                 sh:sparql [ sh:prefixes ex:o0 ;\n    \
                 sh:select \"\"\"SELECT $this WHERE {{ FILTER(false) }}\"\"\" ] .\n{}",
                (0..n)
                    .map(|i| format!("ex:o{i} owl:imports ex:o{} .\n", i + 1))
                    .collect::<String>()
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
/// Ledger #992 added the rows below `data-collections`, and with them the depth that is not
/// SPARQL: nested shapes, deep and cyclic paths, `owl:imports` chains and nested triple terms
/// are refused now, and long lists run on the sized compile stack. ⚠ One row still DIES, by
/// design of this arc rather than oversight: `data-chain`, a recursive shape over a 3000-link
/// chain in the DATA, which rudof's validator follows one call per link (it dies in a release
/// build too). That depth is the data's, not the shapes graph's, and is reported, not fixed.
/// ⚠ And in a DEBUG build `list-in` at 30,000 elements dies on the sized stack; a release
/// build runs it. Length is carried by the stack, which is a release-build guarantee (see
/// `ikigai_store::limits`).
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
        "shapes-triple-term",
        "data-reified",
        "data-annotation",
        "path-cycle",
        "node-chain",
        "node-ring",
        "list-in",
        "list-or",
        "data-chain",
        "imports-chain",
    ] {
        let sizes: &[usize] = match name {
            "path-cycle" => &[1],
            "not-nest" => &[50, 70, 76, 80, 100, 300],
            "list-in" | "list-or" | "data-chain" => &[50, 300, 3000, 30000],
            _ => &[50, 300, 3000],
        };
        for &n in sizes {
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
    // Since ledger #992 the structural walk refuses it before any query is built (it counts
    // the shape and the property shape too, so it is the stricter of the two); the `$PATH`
    // guard behind it stays, pinned by the unit test on `path_to_sparql`.
    let outcome = probe("path-sparql", 300);
    assert!(
        outcome.starts_with("err invalid argument `shapes`")
            && (outcome.contains("$PATH") || outcome.contains("MAX_SHAPE_DEPTH")),
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

// ------------------------------------------------------------------ ledger #992: not SPARQL

fn refused_as(outcome: &str, arg: &str, needle: &str) -> bool {
    outcome.starts_with(&format!("err invalid argument `{arg}`")) && outcome.contains(needle)
}

#[test]
fn nested_shapes_are_refused_and_abort_nothing() {
    // 300 levels of `sh:not`, and a 300-shape `sh:node` chain or ring, each aborted a 2 MiB
    // thread in rudof's shape compiler.
    for name in ["not-nest", "node-chain", "node-ring"] {
        let outcome = probe(name, 300);
        assert!(
            refused_as(&outcome, "shapes", "MAX_SHAPE_DEPTH"),
            "{name}: {outcome}"
        );
    }
}

#[test]
fn shapes_at_the_depth_bound_compile_and_validate() {
    // ex:S, 62 blank `sh:not` shapes and the innermost: 64 nodes, compiled and validated on a
    // 2 MiB caller thread. 63 negations around a failing `sh:class ex:Nothing`: it conforms.
    let outcome = probe("not-nest", 62);
    assert!(outcome.contains("\"conforms\": true"), "{outcome}");
    let over = probe("not-nest", 63);
    assert!(refused_as(&over, "shapes", "MAX_SHAPE_DEPTH"), "{over}");
}

#[test]
fn deep_and_cyclic_paths_are_refused() {
    for n in [300, 3000] {
        let outcome = probe("path-plain", n);
        assert!(
            refused_as(&outcome, "shapes", "MAX_SHAPE_DEPTH"),
            "{n}: {outcome}"
        );
    }
    // At 3000 this aborted in the path parser before any query existed.
    let outcome = probe("path-sparql", 3000);
    assert!(
        outcome.starts_with("err invalid argument `shapes`"),
        "{outcome}"
    );
    // One blank node that is its own operand: the parser never left it.
    let outcome = probe("path-cycle", 1);
    assert!(
        refused_as(&outcome, "shapes", "contains itself"),
        "{outcome}"
    );
}

#[test]
fn a_long_imports_chain_is_refused() {
    let outcome = probe("imports-chain", 3000);
    assert!(
        refused_as(&outcome, "shapes", "MAX_SHAPE_DEPTH"),
        "{outcome}"
    );
}

#[test]
fn nested_triple_terms_are_refused_in_either_argument() {
    let outcome = probe("data-triple-term", 3000);
    assert!(
        refused_as(&outcome, "data", "MAX_TURTLE_NESTING"),
        "{outcome}"
    );
    let outcome = probe("shapes-triple-term", 3000);
    assert!(
        refused_as(&outcome, "shapes", "MAX_TURTLE_NESTING"),
        "{outcome}"
    );
}

#[test]
fn long_lists_run_on_the_compile_stack() {
    // Length, not depth: a 3000-member `sh:in` or `sh:or` aborted the 2 MiB caller thread, and
    // is not refused; it runs on the stack compiling is given.
    for name in ["list-in", "list-or"] {
        let outcome = probe(name, 3000);
        assert!(outcome.starts_with("ok "), "{name}: {outcome}");
    }
}
