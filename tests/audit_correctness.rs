//! Exact SHACL Recommendation cases from the correctness audit (#3435).
use ikigai_shacl::{core_shacl, Report};

const PREFIX: &str = "@prefix sh: <http://www.w3.org/ns/shacl#> .\n@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .\n@prefix : <http://example.org/> .\n";

fn check(data: &str, body: &str, expected: bool) -> Vec<Report> {
    let shapes = format!("{PREFIX}:S a sh:NodeShape ; sh:targetNode :n ; {body} .");
    let data = format!("{PREFIX}{data}");
    let reports = vec![
        core_shacl::validate_report(&data, &shapes).unwrap(),
        #[cfg(feature = "rudof")]
        ikigai_shacl::validate_report(&data, &shapes).unwrap(),
    ];
    for (i, report) in reports.iter().enumerate() {
        assert_eq!(
            report.conforms, expected,
            "engine {i}: {body}, {data}: {report:#?}"
        );
    }
    reports
}

#[test]
fn exact_core_constraints() {
    for (data, body, expected) in [
        (":n a :C .", "sh:closed true", false),
        (
            ":n a :C .",
            "sh:closed true ; sh:ignoredProperties ( rdf:type )",
            true,
        ),
        (
            ":n :p \"hello\"@en .",
            "sh:property [ sh:path :p ; sh:datatype xsd:string ]",
            false,
        ),
        (
            ":n :p \"hello\"@en .",
            "sh:property [ sh:path :p ; sh:datatype rdf:langString ]",
            true,
        ),
        (
            ":n :p \"http://example.org/v\" .",
            "sh:property [ sh:path :p ; sh:in ( :v ) ]",
            false,
        ),
        (
            ":n :p :v .",
            "sh:property [ sh:path :p ; sh:in ( \"http://example.org/v\" ) ]",
            false,
        ),
        (
            ":n :p :v .",
            "sh:property [ sh:path :p ; sh:in ( \"http://example.org/v\" :v ) ]",
            true,
        ),
        (
            ":n :p \"ABC\" .",
            "sh:property [ sh:path :p ; sh:pattern \"^abc$\" ; sh:flags \"i\" ]",
            true,
        ),
        (
            ":n :p \"ABC\" .",
            "sh:property [ sh:path :p ; sh:pattern \"^abc$\" ]",
            false,
        ),
        ("", "sh:property [ sh:path :p ; sh:minCount 1 ]", false),
        (
            ":n :p :v, :w .",
            "sh:property [ sh:path :p ; sh:maxCount 1 ]",
            false,
        ),
        (
            ":n :p :v .",
            "sh:property [ sh:path :p ; sh:nodeKind sh:Literal ]",
            false,
        ),
        (
            ":n :p [] .",
            "sh:property [ sh:path :p ; sh:nodeKind sh:BlankNodeOrIRI ]",
            true,
        ),
    ] {
        check(data, body, expected);
    }
}

#[test]
fn exact_decimal_lexical_space() {
    // https://www.w3.org/TR/shacl/#DatatypeConstraintComponent
    // https://www.w3.org/TR/xmlschema11-2/#decimal (lexical space)
    let shapes = format!("{PREFIX}:S a sh:NodeShape ; sh:targetNode :n ; sh:property [ sh:path :p ; sh:datatype xsd:decimal ] .");
    for (value, expected) in [
        ("12345678901234567890123456789012345678901234567890", true),
        (
            "-12345678901234567890123456789012345678901234567890.5",
            true,
        ),
        ("0.12345678901234567890123456789012345678901234567890", true),
        ("+.5", true),
        ("-0.", true),
        ("+12", true),
        ("", false),
        (".", false),
        ("+", false),
        ("-.", false),
        ("1.2.3", false),
        ("1e2", false),
        ("NaN", false),
        ("INF", false),
        ("１２", false),
        ("1-2", false),
    ] {
        let data = format!("{PREFIX}:n :p \"{value}\"^^xsd:decimal .");
        let report = core_shacl::validate_report(&data, &shapes).unwrap();
        assert_eq!(report.conforms, expected, "{value}: {report:#?}");
        assert_eq!(report.violations.len(), usize::from(!expected));
    }
}

#[cfg(feature = "rudof")]
#[test]
fn exact_logical_constraints_and_paths() {
    for (data, body, expected) in [
        (
            "",
            "sh:or ( [ sh:nodeKind sh:IRI ] [ sh:nodeKind sh:Literal ] )",
            true,
        ),
        (
            "",
            "sh:and ( [ sh:nodeKind sh:IRI ] [ sh:in ( :other ) ] )",
            false,
        ),
        ("", "sh:not [ sh:nodeKind sh:IRI ]", false),
        (
            ":v :p :n .",
            "sh:property [ sh:path [ sh:inversePath :p ] ; sh:hasValue :v ; sh:maxCount 1 ]",
            true,
        ),
        (
            ":n :p :v . :v :q :w .",
            "sh:property [ sh:path ( :p :q ) ; sh:hasValue :w ; sh:maxCount 1 ]",
            true,
        ),
        (
            ":n :p :v, :other . :v :q :w . :other :q :w .",
            "sh:property [ sh:path ( :p :q ) ; sh:maxCount 1 ]",
            true,
        ),
    ] {
        let shapes = format!("{PREFIX}:S a sh:NodeShape ; sh:targetNode :n ; {body} .");
        let r = ikigai_shacl::validate_report(&format!("{PREFIX}{data}"), &shapes).unwrap();
        assert_eq!(r.conforms, expected, "{body}: {r:#?}");
    }
}

#[test]
fn exact_targets_and_report_fields() {
    for target in [
        "sh:targetNode :n",
        "sh:targetClass :C",
        "sh:targetSubjectsOf :p",
        "sh:targetObjectsOf :q",
    ] {
        let shapes = format!("{PREFIX}:S a sh:NodeShape ; {target} ; sh:property [ sh:path :p ; sh:datatype xsd:string ] .");
        let data = format!("{PREFIX}:n a :C ; :p :v . :other :q :n .");
        let reports = vec![
            core_shacl::validate_report(&data, &shapes).unwrap(),
            #[cfg(feature = "rudof")]
            ikigai_shacl::validate_report(&data, &shapes).unwrap(),
        ];
        for r in reports {
            assert!(!r.conforms);
            assert_eq!(r.violations.len(), 1, "{target}: {r:#?}");
            let v = &r.violations[0];
            assert_eq!(v.focus_node, "http://example.org/n");
            assert_eq!(v.path.as_deref(), Some("http://example.org/p"));
            assert_eq!(v.value.as_ref().unwrap().lexical(), "http://example.org/v");
            assert!(v.component.ends_with("#DatatypeConstraintComponent"));
        }
    }
}

#[test]
fn integer_leading_zeros_do_not_change_its_value_space() {
    check(":n :p \"00000000000000000000000000000000000000000000000000000000000000000000000000000001\"^^xsd:byte .", "sh:property [ sh:path :p ; sh:datatype xsd:byte ]", true);
}

#[cfg(feature = "rudof")]
#[test]
#[ignore = "upstream shacl 0.3.24 rejects valid decimals outside its numeric range; reproduction for #3435"]
fn rudof_decimal_lexical_space() {
    let shapes = format!("{PREFIX}:S a sh:NodeShape ; sh:targetNode :n ; sh:property [ sh:path :p ; sh:datatype xsd:decimal ] .");
    let data = format!(
        "{PREFIX}:n :p \"12345678901234567890123456789012345678901234567890\"^^xsd:decimal ."
    );
    assert!(
        ikigai_shacl::validate_report(&data, &shapes)
            .unwrap()
            .conforms
    );
}

#[test]
fn an_absent_target_node_still_has_a_min_count_result() {
    for report in check("", "sh:property [ sh:path :p ; sh:minCount 1 ]", false) {
        assert_eq!(report.violations.len(), 1);
        let v = &report.violations[0];
        assert_eq!(v.focus_node, "http://example.org/n");
        assert_eq!(v.path.as_deref(), Some("http://example.org/p"));
        assert_eq!(v.value, None);
        assert!(v.component.ends_with("#MinCountConstraintComponent"));
    }
}

#[cfg(feature = "sparql")]
#[test]
fn sparql_reports_bound_focus_path_value_and_failure() {
    let shapes = format!(
        r#"{PREFIX}:S a sh:NodeShape ; sh:targetNode :n ; sh:sparql [ sh:select "SELECT $this ?path ?value WHERE {{ $this ?path ?value }}" ] ."#
    );
    let data = format!("{PREFIX}:n :p :v .");
    let reports = vec![
        core_shacl::validate_report(&data, &shapes).unwrap(),
        #[cfg(feature = "rudof")]
        ikigai_shacl::validate_report(&data, &shapes).unwrap(),
    ];
    for r in reports {
        assert!(!r.conforms);
        assert_eq!(r.violations.len(), 1);
        let v = &r.violations[0];
        assert_eq!(v.focus_node, "http://example.org/n");
        assert_eq!(v.path.as_deref(), Some("http://example.org/p"));
        assert_eq!(v.value.as_ref().unwrap().lexical(), "http://example.org/v");
        assert!(v.component.ends_with("#SPARQLConstraintComponent"));
    }
    let failure = shapes.replace(
        "SELECT $this ?path ?value WHERE { $this ?path ?value }",
        "SELECT $this ?failure WHERE { BIND(true AS ?failure) }",
    );
    assert!(core_shacl::validate_report(&data, &failure).is_err());
    #[cfg(feature = "rudof")]
    assert!(ikigai_shacl::validate_report(&data, &failure).is_err());
}

#[test]
fn xpath_extended_pattern_flags() {
    // https://www.w3.org/TR/xpath-functions/#flags
    for (value, pattern, flags, expected) in [
        ("a", "^a#b$", "x", false),
        ("a#b", "^a#b$", "x", true),
        ("ab", "^a b$", "x", true),
        ("a b", "^a[ ]b$", "x", true),
        ("ab", "^a[ ]b$", "x", false),
        ("a#b", "^a[#]b$", "x", true),
        ("a b", "^a b$", "x", true), // Nonbreaking space is not XML whitespace.
        ("ab", "^a b$", "x", false),
        ("a b", "a b", "qx", true),
        ("ab", "a b", "qx", false),
        ("A#B", "^a#b$", "xi", true),
        ("a[b", r"^a\[ b$", "x", true),
        ("a b", r"^a\ sb$", "x", true),
    ] {
        let shapes = format!(
            r#"{PREFIX}:S a sh:NodeShape ; sh:targetNode :n ; sh:property [ sh:path :p ; sh:pattern {pattern} ; sh:flags "{flags}" ] ."#,
            pattern = serde_json::to_string(pattern).unwrap()
        );
        let data = format!("{PREFIX}:n :p {} .", serde_json::to_string(value).unwrap());
        let r = core_shacl::validate_report(&data, &shapes).unwrap();
        assert_eq!(
            r.conforms, expected,
            "{value:?}, {pattern:?}, {flags}: {r:#?}"
        );
    }
}

#[cfg(feature = "rudof")]
#[test]
#[ignore = "upstream shacl 0.3.24 uses Rust extended regex semantics; reproduction for #3435"]
fn rudof_extended_pattern_flag_preserves_literal_hash() {
    let shapes = format!(
        r#"{PREFIX}:S a sh:NodeShape ; sh:targetNode :n ; sh:property [ sh:path :p ; sh:pattern "^a#b$" ; sh:flags "x" ] ."#
    );
    let data = format!(r#"{PREFIX}:n :p "a" ."#);
    assert!(
        !ikigai_shacl::validate_report(&data, &shapes)
            .unwrap()
            .conforms
    );
}

#[test]
fn all_six_node_kinds_distinguish_iris_blank_nodes_and_literals() {
    for (kind, expected) in [
        ("IRI", [true, false, false]),
        ("BlankNode", [false, true, false]),
        ("Literal", [false, false, true]),
        ("BlankNodeOrIRI", [true, true, false]),
        ("BlankNodeOrLiteral", [false, true, true]),
        ("IRIOrLiteral", [true, false, true]),
    ] {
        for (value, conforms) in [":v", "[]", "\"v\""].into_iter().zip(expected) {
            check(
                &format!(":n :p {value} ."),
                &format!("sh:property [ sh:path :p ; sh:nodeKind sh:{kind} ]"),
                conforms,
            );
        }
    }
}

#[test]
fn duplicate_triples_do_not_increase_cardinality() {
    check(
        ":n :p :v . :n :p :v .",
        "sh:property [ sh:path :p ; sh:minCount 2 ]",
        false,
    );
}

#[test]
fn json_ld_is_refused_by_the_turtle_only_api() {
    let shapes = r#"{"@context":{"sh":"http://www.w3.org/ns/shacl#"},"@id":"http://example.org/S","@type":"sh:NodeShape","sh:targetNode":{"@id":"http://example.org/n"},"sh:nodeKind":{"@id":"sh:Literal"}}"#;
    assert!(core_shacl::validate_report("", shapes).is_err());
    assert!(ikigai_shacl::validate_report("", shapes).is_err());
}
