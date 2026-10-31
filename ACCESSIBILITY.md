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
| Last reviewed | 2026-10-31 |

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

- `src/lib.rs`: `sparql_node_constraint_resolves_the_message_and_carries_the_value`,
  `tagged_shape_message_beats_the_validator_default_and_lowest_tag_wins`,
  `turtle_face_carries_the_same_resolved_message_value_and_path` and
  `sparql_constraint_without_a_message_reports_null_message` pin how a result's message is chosen
  and resolved. `tests/core_subset.rs`'s `a_shape_message_resolves_its_template_on_both_faces`
  and `tests/differential.rs`'s `the_authored_messages_agree` hold both validators to the same
  authored messages.
- `tests/core_subset.rs` (`every_shacl_term_outside_the_subset_is_refused_by_name`,
  `malformed_parameters_are_refused` and others), `tests/core_only.rs`
  (`a_sparql_constraint_is_refused_naming_the_feature`), `tests/closed_shapes.rs`
  (`a_malformed_closed_is_refused_by_name`) and `tests/service_egress.rs`
  (`the_refusal_carries_the_shared_consumer_text_after_its_own_sentence`) check that refusals
  name what they refuse.
- **No automated accessibility checker, browser or assistive technology has been used on this
  output.**

## Known limitations

Found by reading the source on 2026-10-31, not by testing:

- The subset validator's default messages are terse and technical (`MinCount(1) not
  satisfied`, `NodeKind constraint not satisfied`, `In constraint not satisfied`, `Expected
  Datatype: …`): they name the constraint, not the focus node or the value, and say nothing about
  how to fix the data. The focus node, path and value are in the result's other fields. rudof's
  own default wording, used by the default build, has not been reviewed here.
- A SHACL-SPARQL constraint with no `sh:message` produces a result with no message at all (JSON
  `null`): a reader sees only IRIs.
- A reader cannot choose the message language: when a shape has messages in several languages,
  the JSON face reports the one with the lowest language tag.
- Every term in the report is an IRI or a skolemized node name
  (`urn:ikigai:shacl:report:b3:…:data.b0`), exact but long to read or listen to; the report
  carries no shorter labels.
- Several errors pass a library's message through after a stage name (for example
  `urn:shacl:validate: shapes compile error: …`, `validation error: …`, `json error: …`) and say
  nothing about what to do.

## Contributing

Read this file before changing any output listed above: the report's faces, a default message,
or an error. Keep meaning in words, keep a refusal a sentence that names what it refuses and why,
and say in the pull request what was tested, with what, and what was not.

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
