# ikigai-shacl

SHACL validation as an [ikigai](https://github.com/ikigai-rs) resource.

`urn:shacl:validate` validates a piped RDF **`data`** graph against a SHACL **`shapes`** graph
(given by-reference — a resolvable resource IRI — or inline Turtle). The validation **report is
itself an RDF graph**:

- `as=text/turtle` (default) → the SHACL `ValidationReport` graph (`report.to_rdf`).
- `as=application/json` → a structured `Report { conforms, violations: [{ focus_node, path, component, message, value }] }` — `message` is the `sh:resultMessage` with its `{?value}` template resolved (language-tagged when the shape's is), `value` the offending `sh:value`; both are terms in the SPARQL-results JSON encoding (`{type, value, datatype?, "xml:lang"?}`). The Turtle face carries the same triples.

Built on rudof's [`shacl`](https://crates.io/crates/shacl) crate. The `shacl::validator` is
native-only (gated off wasm), so this crate is **native-linked** (CLI + servers); in the
browser the same `urn:shacl:validate` resource is served by the JavaScript
[`shacl-engine`](https://www.npmjs.com/package/shacl-engine) — one resource, an implementation
per runtime.

## Dependency pins

The rudof crates are pinned with a **real upper bound** (`>=0.3.17, <0.3.19`), not a
caret. That is deliberate and it is not tidiness: rudof's 0.3 line makes breaking API
changes inside *patch* releases — 0.3.17 added a third argument to
`ShaclProcessor::validate` — and under Cargo's 0.x rules `^0.3.8` already means
`>=0.3.8, <0.4.0`, so a caret cannot exclude one. `ikigai-shacl` 0.1.0 shipped
`shacl = "0.3"` and stopped compiling for every consumer the day 0.3.17 landed. Nothing
flagged it: this repo does not commit `Cargo.lock`, so CI *would* have caught it — but CI
had not run in 67 days.

Raising the bound is a deliberate act. `.github/workflows/upstream.yml` runs daily
against the newest published rudof and says whether it is safe yet.

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
