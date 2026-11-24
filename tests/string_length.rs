//! `sh:minLength` and `sh:maxLength` count characters, not UTF-8 bytes (ledger #3837).
//!
//! SHACL Core §4.4.1 and §4.4.2 define both as the string length of the value node's lexical
//! form (or IRI), as XPath `fn:string-length` counts it: one per character, which is one per
//! Unicode code point. So "文" (3 UTF-8 bytes), "é" (2) and "😀" (4, outside the BMP, and one
//! code point though UTF-16 needs two code units for it) each count 1.
//!
//! Both validators count characters, and every build runs both cases: the subset validator
//! (`core_shacl`) always has, and rudof, which serves `urn:shacl:validate` in the default
//! build, does from `shacl` 0.3.42. Through 0.3.39 its native validators compared `str::len()`,
//! the byte count (`validator/constraints/core/string_based/{min,max}_length.rs`), so 3,333
//! "文" (9,999 bytes) failed `sh:maxLength 3333` and 3 "文" (9 bytes) passed `sh:minLength 5`
//! (https://github.com/rudof-project/rudof/issues/963, fixed upstream in 0.3.40; `shacl`'s next
//! release on crates.io was 0.3.42). ikigai-shacl moved its rudof bounds to 0.3.42 for it
//! (ledger #4195), and the tripwire that asserted the byte count failed there first.

use ikigai_shacl::{core_shacl, Report};

const SH: &str = "http://www.w3.org/ns/shacl#";

fn shapes(constraint: &str, n: usize) -> String {
    format!(
        "@prefix sh: <{SH}> .\n@prefix ex: <http://example.org/> .\n\
         ex:S a sh:NodeShape ; sh:targetNode ex:a ;\n\
           sh:property [ sh:path ex:text ; sh:{constraint} {n} ] .\n"
    )
}

fn data(text: &str) -> String {
    format!("@prefix ex: <http://example.org/> .\nex:a ex:text \"{text}\" .\n")
}

type Engine = fn(&str, &str) -> ikigai_core::Result<Report>;

/// `n` copies of `unit` against `sh:{constraint} limit`, which must give `conforms`; a
/// violation names the component.
fn check(engine: Engine, unit: &str, n: usize, constraint: &str, limit: usize, conforms: bool) {
    let text = unit.repeat(n);
    let report = engine(&data(&text), &shapes(constraint, limit)).expect("validates");
    assert_eq!(
        report.conforms,
        conforms,
        "{n} x {unit:?} ({} bytes) against sh:{constraint} {limit}: {:?}",
        text.len(),
        report.violations.first().map(|v| &v.component)
    );
    if !conforms {
        let component = format!(
            "{SH}{}{}ConstraintComponent",
            constraint[..1].to_uppercase(),
            &constraint[1..]
        );
        assert_eq!(report.violations.len(), 1, "{report:?}");
        assert_eq!(report.violations[0].component, component, "{report:?}");
    }
}

/// The units: a 3-byte CJK character, a 2-byte Latin one, and a 4-byte emoji outside the BMP.
const UNITS: &[&str] = &["文", "é", "😀"];

fn max_length_admits_n_characters(engine: Engine) {
    for unit in UNITS {
        check(engine, unit, 3333, "maxLength", 3333, true);
        check(engine, unit, 5, "maxLength", 5, true);
    }
}

fn max_length_refuses_one_character_more(engine: Engine) {
    for unit in UNITS {
        check(engine, unit, 3334, "maxLength", 3333, false);
        check(engine, unit, 6, "maxLength", 5, false);
    }
}

fn min_length_refuses_fewer_characters(engine: Engine) {
    for unit in UNITS {
        // 3 characters are 6 to 12 bytes: at least 5 bytes, but fewer than 5 characters.
        check(engine, unit, 3, "minLength", 5, false);
        check(engine, unit, 4, "minLength", 5, false);
    }
}

fn min_length_admits_n_characters(engine: Engine) {
    for unit in UNITS {
        check(engine, unit, 5, "minLength", 5, true);
        check(engine, unit, 9, "minLength", 5, true);
    }
}

fn an_iri_counts_characters_too(engine: Engine) {
    let shapes = format!(
        "@prefix sh: <{SH}> .\n@prefix ex: <http://example.org/> .\n\
         ex:S a sh:NodeShape ; sh:targetNode ex:a ;\n\
           sh:property [ sh:path ex:link ; sh:maxLength 10 ; sh:minLength 10 ] .\n"
    );
    // "urn:x:文文文文" is 10 characters and 18 bytes.
    let data = "@prefix ex: <http://example.org/> .\nex:a ex:link <urn:x:文文文文> .\n";
    let report = engine(data, &shapes).expect("validates");
    assert!(report.conforms, "{report:?}");
}

fn all(engine: Engine) {
    max_length_admits_n_characters(engine);
    max_length_refuses_one_character_more(engine);
    min_length_refuses_fewer_characters(engine);
    min_length_admits_n_characters(engine);
    an_iri_counts_characters_too(engine);
}

#[test]
fn the_subset_validator_counts_characters() {
    all(core_shacl::validate_report);
}

/// What `urn:shacl:validate` answers in this build: rudof by default, the subset without it.
#[test]
fn the_served_validator_counts_characters() {
    all(ikigai_shacl::validate_report);
}
