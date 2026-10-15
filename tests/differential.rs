//! The two validators, held to the same verdicts (ledger #1176).
//!
//! With the `rudof` feature on (the default build, which CI tests), `urn:shacl:validate` is
//! rudof; with it off, it is the subset validator in `src/core_shacl.rs`. A host that switches
//! must not be able to tell, so this suite runs BOTH over one corpus and requires the same
//! answer from each:
//!
//! - `sh:conforms`, and
//! - the results as a multiset of (focus node, result path, constraint component, severity,
//!   value, source shape), read back from each engine's `text/turtle` report graph, so the
//!   graph each one serves is checked as well as its verdict.
//!
//! Two things are compared with a normalization, and nothing else is: a node either engine
//! minted under the report's skolem scheme (`urn:ikigai:shacl:report:<content id>:<label>`)
//! compares as "a blank node", because the content id covers the whole report and so differs
//! with every message; and `sh:resultMessage` is not compared at all, because the wording of a
//! default message (a constraint with no `sh:message`) is each engine's own. Messages a shape
//! authors itself are compared in `the_authored_messages_agree`.
//!
//! The corpus is `tests/plans/` (valid plans copied from ikigai-vocab's fixtures and
//! ikigai-cli's plan tests, and a plan that breaks each shape and each SPARQL constraint of
//! `ikigai_vocab::SHAPES`, every file naming its source and what it expects) against
//! `ikigai_vocab::SHAPES`, plus every case of the parity corpus `tests/corpus/`.

#![cfg(feature = "rudof")]

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use ikigai_shacl::{core_shacl, REPORT_SCHEME};
use oxigraph::io::{RdfFormat, RdfParser};
use oxrdf::{Term, Triple};

const SH: &str = "http://www.w3.org/ns/shacl#";
const RDF_TYPE: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";

/// One result, as both engines must agree on it.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Sig {
    focus: String,
    path: Option<String>,
    component: String,
    severity: String,
    value: Option<String>,
    source: Option<String>,
}

/// A report graph's verdict and results.
#[derive(Debug, PartialEq, Eq)]
struct Verdict {
    conforms: bool,
    results: Vec<Sig>,
}

/// A term as it is compared: a skolemized blank node is any blank node.
fn shown(term: &Term) -> String {
    match term {
        Term::NamedNode(n) if n.as_str().starts_with(REPORT_SCHEME) => "_:blank".to_string(),
        Term::NamedNode(n) => format!("<{}>", n.as_str()),
        other => other.to_string(),
    }
}

/// Read a `text/turtle` report graph back into its [`Verdict`].
fn verdict(turtle: &str) -> Verdict {
    let triples: Vec<Triple> = RdfParser::from_format(RdfFormat::Turtle)
        .for_slice(turtle.as_bytes())
        .map(|q| Triple::from(q.expect("the report graph parses")))
        .collect();
    let objects = |subject: &Term, predicate: &str| -> Vec<Term> {
        triples
            .iter()
            .filter(|t| &Term::from(t.subject.clone()) == subject)
            .filter(|t| t.predicate.as_str() == predicate)
            .map(|t| t.object.clone())
            .collect()
    };
    let reports: Vec<Term> = triples
        .iter()
        .filter(|t| t.predicate.as_str() == RDF_TYPE)
        .filter(|t| matches!(&t.object, Term::NamedNode(c) if c.as_str() == format!("{SH}ValidationReport")))
        .map(|t| Term::from(t.subject.clone()))
        .collect();
    assert_eq!(reports.len(), 1, "one sh:ValidationReport in:\n{turtle}");
    let report = &reports[0];
    let conforms = objects(report, &format!("{SH}conforms"));
    assert_eq!(conforms.len(), 1, "one sh:conforms in:\n{turtle}");
    let conforms = matches!(&conforms[0], Term::Literal(l) if l.value() == "true");
    let one = |node: &Term, local: &str| -> Option<String> {
        let found = objects(node, &format!("{SH}{local}"));
        assert!(found.len() <= 1, "more than one sh:{local} in:\n{turtle}");
        found.first().map(shown)
    };
    let mut results: Vec<Sig> = objects(report, &format!("{SH}result"))
        .iter()
        .map(|r| Sig {
            focus: one(r, "focusNode").expect("a result has a sh:focusNode"),
            path: one(r, "resultPath"),
            component: one(r, "sourceConstraintComponent").expect("a component"),
            severity: one(r, "resultSeverity").expect("a severity"),
            value: one(r, "value"),
            source: one(r, "sourceShape"),
        })
        .collect();
    results.sort();
    Verdict { conforms, results }
}

/// A corpus case: its name, data and shapes, and what its file says to expect.
struct Case {
    name: String,
    data: String,
    shapes: String,
    expect: Option<String>,
}

fn dir(rel: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(rel)
}

fn plan_cases() -> Vec<Case> {
    let mut cases: Vec<Case> = fs::read_dir(dir("tests/plans"))
        .expect("tests/plans")
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "ttl"))
        .map(|p| {
            let data = fs::read_to_string(&p).unwrap();
            let expect = data
                .lines()
                .find_map(|l| l.strip_prefix("# expect: "))
                .map(str::to_string);
            Case {
                name: p.file_stem().unwrap().to_string_lossy().into_owned(),
                data,
                shapes: ikigai_vocab::SHAPES.to_string(),
                expect,
            }
        })
        .collect();
    cases.sort_by(|a, b| a.name.cmp(&b.name));
    cases
}

fn parity_cases() -> Vec<Case> {
    let mut cases: Vec<Case> = fs::read_dir(dir("tests/corpus"))
        .expect("tests/corpus")
        .map(|e| e.unwrap().path())
        .filter(|p| p.is_dir())
        .map(|p| Case {
            name: format!("corpus/{}", p.file_name().unwrap().to_string_lossy()),
            data: fs::read_to_string(p.join("data.ttl")).unwrap(),
            shapes: fs::read_to_string(p.join("shapes.ttl")).unwrap(),
            expect: None,
        })
        .collect();
    cases.sort_by(|a, b| a.name.cmp(&b.name));
    cases
}

/// The cases rudof cannot validate at all, and why. Each is a plan whose `ik:Process`,
/// `ik:Step` or `ik:Fork` is a BLANK node, under a shape with a `sh:sparql` constraint: rudof
/// binds `$this` by writing the focus node into `VALUES ?this { _:b0 }`, and SPARQL does not
/// allow a blank node there, so its query fails to parse and validation fails with an error
/// (shacl 0.3.24, `BasicSparql::validate_sparql`). The subset validator substitutes `$this`
/// rather than writing it into the text, so it validates these, and reports each one as not
/// conforming (the `sh:nodeKind sh:IRI` the same shapes declare). For a plan door the two
/// answers come to the same thing, as neither lets the plan run; they are listed so a rudof
/// release that fixes this, or a corpus case that starts tripping it, is noticed.
const RUDOF_FAILS: &[&str] = &[
    "bad-fork-not-iri",
    "bad-process-not-iri",
    "bad-step-not-iri",
];

/// The parity cases the subset validator refuses, by name, because their shapes use a SHACL
/// term outside its subset: `corpus/complex-paths` exists to pin how rudof and shacl-engine
/// render a path that is not a predicate IRI (ledger #204), and the subset takes only a
/// predicate path. Refusing is that validator's contract, so here it must refuse, never answer.
const CORE_REFUSES: &[&str] = &["corpus/complex-paths"];

/// Both engines over one case: their verdicts, which must be equal. A case in [`RUDOF_FAILS`]
/// must fail in rudof, and not conform in the subset validator; a case in [`CORE_REFUSES`]
/// must validate in rudof and be refused by the subset validator. Either is returned as `None`.
fn both(case: &Case) -> Option<(Verdict, Verdict)> {
    let rudof = ikigai_shacl::validate_turtle(&case.data, &case.shapes);
    if CORE_REFUSES.contains(&case.name.as_str()) {
        rudof.unwrap_or_else(|e| panic!("[{}] rudof: {e}", case.name));
        let err = core_shacl::validate_turtle(&case.data, &case.shapes)
            .expect_err(&format!("[{}] the subset validator answered", case.name));
        assert!(
            err.to_string()
                .contains("which the SHACL subset validator does not implement"),
            "[{}] {err}",
            case.name
        );
        return None;
    }
    let core = core_shacl::validate_turtle(&case.data, &case.shapes)
        .unwrap_or_else(|e| panic!("[{}] the subset validator: {e}", case.name));
    let core = verdict(&core);
    if RUDOF_FAILS.contains(&case.name.as_str()) {
        let err = rudof.expect_err(&format!("[{}] rudof no longer fails here", case.name));
        assert!(
            err.to_string().contains("expected UNDEF"),
            "[{}] {err}",
            case.name
        );
        assert!(
            !core.conforms,
            "[{}] the subset validator: {core:#?}",
            case.name
        );
        return None;
    }
    let rudof = rudof.unwrap_or_else(|e| panic!("[{}] rudof: {e}", case.name));
    Some((verdict(&rudof), core))
}

#[test]
fn both_validators_agree_on_every_plan() {
    let cases = plan_cases();
    assert!(
        cases.len() >= 70,
        "the plan corpus has {} cases",
        cases.len()
    );
    let mut disagreements = Vec::new();
    for case in &cases {
        let Some((rudof, core)) = both(case) else {
            continue;
        };
        if rudof != core {
            disagreements.push(format!(
                "[{}]\n  rudof: {rudof:#?}\n  core:  {core:#?}",
                case.name
            ));
        }
    }
    assert!(
        disagreements.is_empty(),
        "{} of {} plans disagree:\n{}",
        disagreements.len(),
        cases.len(),
        disagreements.join("\n")
    );
}

#[test]
fn every_plan_breaks_what_it_says_it_breaks() {
    // An agreement is only worth something if the case tests what it was written for: a valid
    // plan conforms, and a broken one reports the shape and component its file names.
    for case in plan_cases() {
        let expect = case
            .expect
            .as_deref()
            .unwrap_or_else(|| panic!("[{}] names no `# expect:`", case.name));
        let core = verdict(&core_shacl::validate_turtle(&case.data, &case.shapes).unwrap());
        if expect == "conforms" {
            assert!(core.conforms, "[{}] does not conform: {core:#?}", case.name);
            assert!(case.name.starts_with("ok-"), "[{}] conforms", case.name);
            continue;
        }
        assert!(
            case.name.starts_with("bad-"),
            "[{}] expects a result",
            case.name
        );
        let (shape, component) = expect.split_once(' ').expect("`<shape> <component>`");
        assert!(!core.conforms, "[{}] conforms", case.name);
        assert!(
            core.results
                .iter()
                .any(|r| r.source.as_deref() == Some(&format!("<{shape}>"))
                    && r.component == format!("<{SH}{component}>")),
            "[{}] has no {component} from <{shape}>: {core:#?}",
            case.name
        );
    }
}

#[test]
fn both_validators_agree_on_the_parity_corpus() {
    // Every case of the parity corpus but those in CORE_REFUSES uses only the supported
    // subset; `both` holds the subset validator to refusing those, and to agreeing on the rest.
    let cases = parity_cases();
    assert!(
        cases.len() >= 5,
        "the parity corpus has {} cases",
        cases.len()
    );
    for case in &cases {
        let Some((rudof, core)) = both(case) else {
            assert!(
                CORE_REFUSES.contains(&case.name.as_str()),
                "[{}]",
                case.name
            );
            continue;
        };
        assert_eq!(rudof, core, "[{}]", case.name);
    }
}

#[test]
fn the_json_faces_agree_too() {
    // The JSON face is the same projection on both sides: compare it whole, message aside.
    for case in plan_cases().iter().chain(parity_cases().iter()) {
        if RUDOF_FAILS.contains(&case.name.as_str()) || CORE_REFUSES.contains(&case.name.as_str()) {
            continue;
        }
        let rudof = ikigai_shacl::validate_report(&case.data, &case.shapes).unwrap();
        let core = core_shacl::validate_report(&case.data, &case.shapes).unwrap();
        let strip = |r: &ikigai_shacl::Report| -> Vec<(String, Option<String>, String, String)> {
            r.violations
                .iter()
                .map(|v| {
                    (
                        v.focus_node.clone(),
                        v.path.clone(),
                        v.component.clone(),
                        serde_json::to_string(&v.value).unwrap(),
                    )
                })
                .collect()
        };
        assert_eq!(rudof.conforms, core.conforms, "[{}]", case.name);
        assert_eq!(strip(&rudof), strip(&core), "[{}]", case.name);
    }
}

#[test]
fn the_authored_messages_agree() {
    // Every shape in ikigai_vocab::SHAPES that can report a result carries a `sh:message`, so on
    // the plan corpus the JSON face's message is the shape's own, template resolved, on both.
    let mut by_case: BTreeMap<String, usize> = BTreeMap::new();
    for case in plan_cases() {
        if RUDOF_FAILS.contains(&case.name.as_str()) {
            continue;
        }
        let rudof = ikigai_shacl::validate_report(&case.data, &case.shapes).unwrap();
        let core = core_shacl::validate_report(&case.data, &case.shapes).unwrap();
        for (r, c) in rudof.violations.iter().zip(&core.violations) {
            // rudof's `sh:node` result carries only its own default message, never the shape's
            // (shacl 0.3.24 `Node::validate`): the one place the authored message is not used.
            if r.component.ends_with("#NodeConstraintComponent") {
                continue;
            }
            assert_eq!(r.message, c.message, "[{}] {}", case.name, r.component);
            *by_case.entry(case.name.clone()).or_default() += 1;
        }
    }
    assert!(by_case.values().sum::<usize>() > 60, "{by_case:?}");
}
