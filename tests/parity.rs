//! Cross-implementation parity corpus. Each `tests/corpus/<case>/` holds `data.ttl`,
//! `shapes.ttl`, and `expected.json` (a [`ikigai_shacl::ValidationOutcome`] — `conforms` +
//! sorted violation signatures). This suite asserts the **native rudof** validator produces
//! the expected outcome; a sibling Node suite (`js-parity/`) asserts **shacl-engine** (the
//! browser validator) produces the *same* `expected.json`. Same corpus, same expected ⇒ both
//! implementations agree by construction.

use ikigai_shacl::{validate_outcome, ValidationOutcome};
use std::fs;
use std::path::Path;

fn corpus_dir() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus")
}

/// Run a case through the native validator.
fn outcome(case: &Path) -> ValidationOutcome {
    let data = fs::read_to_string(case.join("data.ttl")).expect("data.ttl");
    let shapes = fs::read_to_string(case.join("shapes.ttl")).expect("shapes.ttl");
    validate_outcome(&data, &shapes).expect("validation")
}

#[test]
fn native_validator_matches_the_parity_corpus() {
    let mut checked = 0;
    for entry in fs::read_dir(corpus_dir()).expect("corpus dir") {
        let case = entry.unwrap().path();
        if !case.is_dir() {
            continue;
        }
        let name = case.file_name().unwrap().to_string_lossy().to_string();
        let got = outcome(&case);

        let expected_path = case.join("expected.json");
        if !expected_path.exists() {
            // Bootstrap: write the rudof outcome so it can be reviewed + committed as the
            // shared contract. Fails the run so a missing expected isn't a silent pass.
            fs::write(&expected_path, serde_json::to_string_pretty(&got).unwrap()).unwrap();
            panic!("[{name}] wrote bootstrap expected.json — review + re-run");
        }
        let expected: ValidationOutcome =
            serde_json::from_str(&fs::read_to_string(&expected_path).unwrap()).unwrap();
        assert_eq!(got, expected, "[{name}] native outcome != expected.json");
        checked += 1;
    }
    assert!(
        checked >= 5,
        "expected at least 5 corpus cases, ran {checked}"
    );
}
