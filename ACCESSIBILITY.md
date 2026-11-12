# Accessibility

What `ikigai-shacl` emits that people read, the rules that output follows, how it is tested, and
how to report a barrier. Its main output is a SHACL validation report, which people read to find
out why their data does not conform; it also writes the text of its errors. It writes no HTML,
SVG or terminal output of its own. It is not a conformance claim. Adapted from the
[ACCESSIBILITY.md template](https://github.com/mgifford/ACCESSIBILITY.md) (MIT).

| Field | Value |
|---|---|
| Target | WCAG 2.2 Level AA, for any page that presents this output; this repository writes text only |
| Status | Evaluation in progress. No conformance claim. |
| Owner | the maintainers of this repository |
| Report a barrier | [a GitHub issue](https://github.com/ikigai-rs/ikigai-shacl/issues/new?labels=accessibility) with the `accessibility` label; anything security-sensitive through [private vulnerability reporting](https://github.com/ikigai-rs/ikigai-shacl/security/advisories/new) |
| Last reviewed | 2026-11-12 |

## What it emits that people read

- **The validation report** from `urn:shacl:validate`, in two faces: `as=text/turtle` (the
  default), the SHACL `ValidationReport` graph; and `as=application/json`, `{conforms,
  violations: [{focus_node, path, component, message, value}]}` (`Report` in `src/lib.rs`). Each
  result's `message` is the shape author's `sh:message` with its `{?this}`, `{?value}` and
  `{?path}` placeholders resolved, or, when the shape has none, the validator's default message:
  rudof's own wording in the default build (`src/rudof_engine.rs`), and wording such as
  `MinCount(1) not satisfied` from the subset validator (`default_message` in
  `src/core_shacl.rs`).
- **Error and refusal messages**: the `InvalidArgument` details that refuse a shapes or data
  graph (`src/core_shacl.rs`, `src/rudof_engine.rs`, `src/depth.rs`) and the
  `Error::Endpoint` sentences, most of which begin `urn:shacl:validate:`, which a host shows to
  whoever made the request.

Not this repository's: the page, error page or terminal a host shows a report or an error in.

## The rules that output follows

Followed by reading the source:

- A shape author's message is what a reader sees: it beats the validator's default, its
  placeholders are resolved on both faces so the message names the value, and a
  language-tagged message keeps its tag in the JSON face.
- A refusal names what it refuses and why, and is typed on the argument it is about (`shapes` or
  `data`): the SHACL term the subset validator does not implement, the `sparql` feature a
  SHACL-SPARQL constraint needs, the malformed parameter and the shape it is on, the bound and
  its number (`MAX_SHAPE_DEPTH`, `MAX_DATA_RECURSION`, `MAX_VALIDATION_WORK`). A refusal never
  stands in for a partial report: nothing is validated, and the refusal says so where it can.
- Nothing is written in color; every answer is plain text.

## How it is tested

Every named check has a result: Pass, Fail or Blocked, with evidence. Pass covers only the
stated check, not overall accessibility. The runs below used the unchanged main source at
[d2cfb84](https://github.com/ikigai-rs/ikigai-shacl/commit/d2cfb84a8b4363a8906835e986e3f8197a7f445b)
on 2026-11-12, with Cargo 1.99.1 and
rustc 1.99.1. The commands were `cargo test --lib --tests` (default rudof build) and
`cargo test --no-default-features --lib --tests` (core-only subset build). These are functional
tests of report contents and refusals; they do not evaluate how a person reads the output.
CI repeats these tests with the `module` feature and with default features off through
[ci.yml](.github/workflows/ci.yml). Neither these runs nor CI establish WCAG conformance.

| Check | Result | Evidence |
|---|---|---|
| Authored messages, resolved placeholders, language tags and report faces | Pass | Both commands above: `src/lib.rs` tests `sparql_node_constraint_resolves_the_message_and_carries_the_value` (default build only), `tagged_shape_message_beats_the_validator_default_and_lowest_tag_wins` and `turtle_face_carries_the_same_resolved_message_value_and_path`; `tests/core_subset.rs` test `a_shape_message_resolves_its_template_on_both_faces`; default-build `tests/differential.rs` test `the_authored_messages_agree`. Covers the asserted examples, not message clarity or language suitability. |
| Refusals name unsupported terms and malformed parameters | Pass | Both commands above: `tests/core_subset.rs` tests `every_shacl_term_outside_the_subset_is_refused_by_name` and `malformed_parameters_are_refused`, and `tests/closed_shapes.rs` test `a_malformed_closed_is_refused_by_name`. Checks the named cases, not every possible error. |
| Missing SPARQL feature is named in a refusal | Pass | Core-only command above: `tests/core_only.rs` test `a_sparql_constraint_is_refused_naming_the_feature`. Checks the feature refusal, not usability of the advice. |
| SERVICE refusal carries the shared consumer advice | Pass | Default command above: `tests/service_egress.rs` test `the_refusal_carries_the_shared_consumer_text_after_its_own_sentence`. Checks sentence order and advice text, not reader comprehension. |
| SPARQL result always has an explanatory message | Fail | Default command above: `src/lib.rs` test `sparql_constraint_without_a_message_reports_null_message` passes by asserting the missing message. Confirms a barrier, not an accessible result. |
| Reader can choose the message language | Fail | Both commands above: `src/lib.rs` test `tagged_shape_message_beats_the_validator_default_and_lowest_tag_wins` confirms selection by lowest language tag. Source review of `ReportResult::message` and `core_shacl::message_term` finds no reader language preference. |
| Subset default messages explain how to fix data | Fail | Source review on 2026-11-12: `default_message` in `src/core_shacl.rs` still emits terse constraint names such as `MinCount(1) not satisfied`; no repair advice. Not a reader study. |
| Report identifiers have shorter readable labels | Fail | Source review on 2026-11-12: `ReportResult` in `src/lib.rs` and report serialization in `src/core_shacl.rs` and `src/rudof_engine.rs` expose identifiers without a shorter-label field. No listening test. |
| Error messages consistently explain recovery | Fail | Source review on 2026-11-12: `src/rudof_engine.rs` passes through library messages after `shapes compile error`, `validation error` and `json error`, without recovery advice. No reader comprehension test. |
| Output meaning does not depend on color | Pass | Source review on 2026-11-12 of report and error construction in `src/lib.rs`, `src/core_shacl.rs`, `src/rudof_engine.rs` and `src/depth.rs`: text and structured fields, no color styling. Does not test a host's presentation. |
| Default rudof message clarity | Blocked | No reader evaluation of rudof's default wording was performed for this review. Functional tests do not establish clarity. |
| Automated accessibility checker | Blocked | No automated accessibility checker has been run on this output; no host page or browser checker is configured in this repository. |
| Browser presentation, zoom, reflow and contrast | Blocked | No browser evaluation was performed; this crate supplies reports and errors for a host to present. A host presentation is needed to run these checks. |
| Manual keyboard | Blocked | No person performed a keyboard pass through a host presenting this output; no interactive host session was available for this review. |
| Screen reader | Blocked | No screen reader session was available or used on this output for this review. |
| Screen magnifier | Blocked | No screen magnifier session was available or used on this output for this review. |
| Speech input | Blocked | No speech-input session was available or used on this output for this review. |
| Switch access | Blocked | No switch-access session was available or used on this output for this review. |
| Braille display | Blocked | No braille display was available or used on this output for this review. |

## Known limitations

Rechecked against source on 2026-11-12; the table above distinguishes functional tests from
source review and unrun reader evaluations:

- The subset validator's default messages are terse and technical (`MinCount(1) not
  satisfied`, `NodeKind constraint not satisfied`, `In constraint not satisfied`, `Expected
  Datatype: …`): they name the constraint, not the focus node or the value, and say nothing about
  how to fix the data. The focus node, path and value are in the result's other fields. rudof's
  own default wording, used by the default build, has not been reviewed here.
- A SHACL-SPARQL constraint with no `sh:message` produces a result with no message at all (JSON
  `null`): the remaining fields identify the violation without an explanatory sentence.
- A reader cannot choose the message language: when a shape has messages in several languages,
  the JSON face reports the one with the lowest language tag.
- Report identifiers include IRIs and skolemized node names
  (`urn:ikigai:shacl:report:b3:…:data.b0`), which can be long to read or listen to; the report
  carries no shorter labels.
- Several errors pass a library's message through after a stage name (for example
  `urn:shacl:validate: shapes compile error: …`, `validation error: …`, `json error: …`) and say
  nothing about what to do.

## Contributing

Read this file before changing any output listed above: the report's faces, a default message,
or an error. Keep meaning in words, keep a refusal a sentence that names what it refuses and why,
and give each check in the pull request a `Check | Result | Evidence` row: Pass, Fail or
Blocked, with the command or test, tool and version, or why it could not run. Keep unrun checks
as Blocked, including assistive technology nobody used. A historical run CI does not repeat
is Blocked with its date, not Pass.

## Reporting a barrier

[Open an issue](https://github.com/ikigai-rs/ikigai-shacl/issues/new?labels=accessibility) with
the `accessibility` label (the link sets it when GitHub lets you add labels; otherwise a maintainer
adds it): what you were doing, what happened, and your terminal or browser and any assistive
technology, if you are comfortable sharing them. Anything security-sensitive goes through
[private vulnerability reporting](https://github.com/ikigai-rs/ikigai-shacl/security/advisories/new).
**We acknowledge a report within 7 days**, and promise nothing further.

## Change history

| Date | Change |
|---|---|
| 2026-10-31 | First version. |
| 2026-11-12 | Record each check as Pass, Fail or Blocked, rerun report and refusal tests on main, and distinguish functional coverage from unrun accessibility evaluations. |
