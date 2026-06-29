# ikigai-shacl

SHACL validation as an [ikigai](https://github.com/ikigai-rs) resource.

`urn:shacl:validate` validates a piped RDF **`data`** graph against a SHACL **`shapes`** graph
(given by-reference — a resolvable resource IRI — or inline Turtle). The validation **report is
itself an RDF graph**:

- `as=text/turtle` (default) → the SHACL `ValidationReport` graph (`report.to_rdf`).
- `as=application/json` → a structured `ValidationOutcome { conforms, violations: [{ focus_node, path, component }] }`.

Built on rudof's [`shacl`](https://crates.io/crates/shacl) crate. The `shacl::validator` is
native-only (gated off wasm), so this crate is **native-linked** (CLI + servers); in the
browser the same `urn:shacl:validate` resource is served by the JavaScript
[`shacl-engine`](https://www.npmjs.com/package/shacl-engine) — one resource, an implementation
per runtime.

## Parity

Both implementations are held to a single shared corpus:

- `tests/corpus/<case>/` — `data.ttl`, `shapes.ttl`, and `expected.json` (the
  implementation-independent `ValidationOutcome`: `conforms` + the spec-defined
  `(focus_node, path, sourceConstraintComponent)` violation signatures — no blank-node ids or
  messages, which legitimately differ between validators).
- `tests/parity.rs` asserts **rudof** (native) matches every `expected.json`.
- `js-parity/parity.test.mjs` asserts **shacl-engine** (browser) matches the *same*
  `expected.json`.

Same corpus, same expected ⇒ the two validators agree by construction. CI runs both.

## Test

```sh
cargo test                      # native rudof + parity corpus
cd js-parity && npm ci && npm test   # shacl-engine parity
```
