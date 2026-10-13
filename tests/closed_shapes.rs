//! `sh:closed` and `sh:ignoredProperties` in the subset validator, over the shapes ikigai-layers
//! ships. It runs in every build; with `rudof` compiled, rudof is held to the same answers.
//!
//! ikigai-layers refuses an open node shape (its `src/config.rs` requires `sh:closed true` on
//! every one), so a host that links the subset could not validate a single layer's shapes until
//! the subset implemented the two. The fixtures are copied VERBATIM from ikigai-rs/ikigai-layers
//! at main (`gateway/layers/`, last changed in ikigai-rs/ikigai-layers#16), so their git blob ids
//! still name the source: `gateway.shapes.ttl` is 7fde4f35cc16601a03a5777a11ffca920b0a9892 and
//! `gateway-events.shapes.ttl` is 840c1d647ba7c3ee0ca4958a1b1e923d9a289b7e
//! (`git hash-object tests/fixtures/layers/*.ttl` against the layers repo's own).
//!
//! The four small cases `tests/corpus/closed-*` hold rudof, shacl-engine and (through
//! `tests/differential.rs`) the subset to the same verdicts on the construct alone.

use ikigai_core::Error;
use ikigai_shacl::core_shacl;
use ikigai_shacl::Report;

const GATEWAY: &str = include_str!("fixtures/layers/gateway.shapes.ttl");
const EVENTS: &str = include_str!("fixtures/layers/gateway-events.shapes.ttl");

const PREFIXES: &str = "@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n\
                        @prefix dcterms: <http://purl.org/dc/terms/> .\n\
                        @prefix prov: <http://www.w3.org/ns/prov#> .\n\
                        @prefix ik: <https://ikigai-rs.dev/ns#> .\n\
                        @prefix gw: <urn:layers:gateway:> .\n";

/// The host's three stamps, which every closed shape here lists as a property.
const STAMPS: &str = "prov:wasAttributedTo <urn:example:participant:a> ; \
                      dcterms:created \"2026-10-12T00:00:00Z\"^^xsd:dateTime";

fn request(extra: &str) -> String {
    format!(
        "{PREFIXES}<urn:layer:gw:request:c1> a gw:Request ; gw:correlation \"c1\" ; \
         gw:resource <urn:example:greeting> ; ik:verb \"Source\" ; gw:argument \"name=world\" ; \
         {STAMPS} ; ik:seq 1 {extra}.\n"
    )
}

fn answers() -> String {
    format!(
        "{PREFIXES}<urn:layer:gw:reply:c1> a gw:Reply ; ik:offer <urn:layer:gw:request:c1> ; \
         ik:addressedTo <urn:example:participant:a> ; gw:correlation \"c1\" ; \
         ik:mediaType \"text/plain\" ; gw:bytes \"aGVsbG8=\"^^xsd:base64Binary ; {STAMPS} ; \
         ik:seq 2 .\n\
         <urn:layer:gw:reply:c2> a gw:Failure ; ik:offer <urn:layer:gw:request:c2> ; \
         ik:addressedTo <urn:example:participant:a> ; gw:correlation \"c2\" ; \
         gw:errorKind \"unresolved\" ; gw:message \"nothing is bound there\" ; \
         gw:target <urn:example:missing> ; {STAMPS} ; ik:seq 3 .\n"
    )
}

fn invalidation(extra: &str) -> String {
    format!(
        "{PREFIXES}<urn:layer:new> a gw:Invalidation ; gw:resource <urn:example:greeting> ; \
         gw:reason \"changed\" ; {STAMPS} ; ik:seq 4 {extra}.\n"
    )
}

/// A result as both engines must agree on it: focus node, path, component, value (as JSON).
#[cfg(feature = "rudof")]
type Sig = (String, Option<String>, String, String);

fn report(data: &str, shapes: &str) -> Report {
    let core = core_shacl::validate_report(data, shapes)
        .unwrap_or_else(|e| panic!("the subset validator refused: {e}"));
    #[cfg(feature = "rudof")]
    {
        // rudof, over the same graphs, must say the same thing (message wording aside).
        let rudof = ikigai_shacl::validate_report(data, shapes).expect("rudof validates it");
        let strip = |r: &Report| -> (bool, Vec<Sig>) {
            let mut v: Vec<_> = r
                .violations
                .iter()
                .map(|v| {
                    (
                        v.focus_node.clone(),
                        v.path.clone(),
                        v.component.clone(),
                        serde_json::to_string(&v.value).unwrap(),
                    )
                })
                .collect();
            v.sort();
            (r.conforms, v)
        };
        assert_eq!(strip(&rudof), strip(&core));
    }
    core
}

#[test]
fn every_layer_shape_the_gateway_ships_is_applied_and_its_tuples_conform() {
    // Before the subset implemented `sh:closed`, both graphs were refused outright, by name.
    for (what, data, shapes) in [
        ("a request", request(""), GATEWAY),
        ("a reply and a failure", answers(), GATEWAY),
        ("an invalidation", invalidation(""), EVENTS),
    ] {
        let r = report(&data, shapes);
        assert!(r.conforms, "{what}: {:#?}", r.violations);
    }
}

#[test]
fn a_predicate_a_closed_shape_does_not_list_is_one_result_per_triple() {
    let r = report(
        &request("; gw:asker <urn:example:participant:b> ; gw:note \"x\", \"y\" "),
        GATEWAY,
    );
    assert!(!r.conforms);
    let mut got: Vec<(String, Option<String>, String)> = r
        .violations
        .iter()
        .map(|v| {
            (
                v.path.clone().unwrap_or_default(),
                v.value.as_ref().map(|t| t.lexical()),
                v.component.clone(),
            )
        })
        .collect();
    got.sort();
    let closed = "http://www.w3.org/ns/shacl#ClosedConstraintComponent".to_string();
    assert_eq!(
        got,
        vec![
            (
                "urn:layers:gateway:asker".to_string(),
                Some("urn:example:participant:b".to_string()),
                closed.clone()
            ),
            (
                "urn:layers:gateway:note".to_string(),
                Some("x".to_string()),
                closed.clone()
            ),
            (
                "urn:layers:gateway:note".to_string(),
                Some("y".to_string()),
                closed
            ),
        ]
    );
    for v in &r.violations {
        assert_eq!(v.focus_node, "urn:layer:gw:request:c1");
    }
}

#[test]
fn rdf_type_passes_only_because_it_is_ignored() {
    // The layers' shapes list `rdf:type` in `sh:ignoredProperties`; without that, the class a
    // tuple is targeted by would itself be a predicate the closed shape does not allow.
    let without = EVENTS.replace("sh:ignoredProperties ( rdf:type ) ;", "");
    assert_ne!(without, EVENTS, "the fixture still ignores rdf:type");
    let r = report(&invalidation(""), &without);
    assert!(!r.conforms);
    assert_eq!(r.violations.len(), 1, "{:#?}", r.violations);
    assert_eq!(
        r.violations[0].path.as_deref(),
        Some("http://www.w3.org/1999/02/22-rdf-syntax-ns#type")
    );
}

#[test]
fn ignored_properties_without_closed_change_nothing_and_closed_false_is_open() {
    for shapes in [
        EVENTS.replace("sh:closed true ;", ""),
        EVENTS.replace("sh:closed true ;", "sh:closed false ;"),
    ] {
        let r = report(&invalidation("; gw:extra \"allowed\" "), &shapes);
        assert!(r.conforms, "{:#?}", r.violations);
    }
}

#[test]
fn a_malformed_closed_is_refused_by_name() {
    for (bad, needle) in [
        ("sh:closed \"yes\" ;", "`sh:closed`"),
        ("sh:closed true, false ;", "`sh:closed`"),
        (
            "sh:closed true ; sh:ignoredProperties ( \"type\" ) ;",
            "`sh:ignoredProperties`",
        ),
        (
            "sh:closed true ; sh:ignoredProperties <urn:example:not-a-list> ;",
            "`sh:ignoredProperties`",
        ),
    ] {
        let shapes = EVENTS.replace("sh:closed true ;", bad);
        match core_shacl::validate_report(&invalidation(""), &shapes) {
            Err(Error::InvalidArgument { name, detail }) => {
                assert_eq!(name, "shapes", "{detail}");
                assert!(detail.contains(needle), "`{needle}` not named in: {detail}");
            }
            other => panic!("not refused ({bad}): {other:?}"),
        }
    }
}
