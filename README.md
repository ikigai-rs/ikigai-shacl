# ikigai-shacl

SHACL validation as an [ikigai](https://github.com/ikigai-rs) resource.

`urn:shacl:validate` validates a piped RDF **`data`** graph against a SHACL **`shapes`** graph
(given by-reference — a resolvable resource IRI — or inline Turtle). The validation **report is
itself an RDF graph**:

- `as=text/turtle` (default) → the SHACL `ValidationReport` graph (`report.to_rdf`), **skolemized** — see below.
- `as=application/json` → a structured `Report { conforms, violations: [{ focus_node, path, component, message, value }] }` — `message` is the `sh:resultMessage` with its `{?value}` template resolved (language-tagged when the shape's is), `value` the offending `sh:value`; both are terms in the SPARQL-results JSON encoding (`{type, value, datatype?, "xml:lang"?}`). The Turtle face carries the same triples.

Both faces are declared outputs, and `as` lists exactly those two values, so an agent
reading `urn:kernel:actions` can reach either one.

## The report graph has no blank nodes

rudof's `to_rdf` mints a blank node for the report, one per result, and passes through
whatever the shapes graph gave it (a blank-node `sh:sourceShape`, the RDF-list structure
of a complex `sh:path`). A blank node has no name outside the document it arrived in, so
a report full of them cannot be unioned, diffed or SPARQL-ed against anything. Every one
is therefore given a stable IRI:

```text
urn:ikigai:shacl:report:<content id of the whole report graph>:<blank-node label>
```

The content id (`b3:…`, BLAKE3 over the graph's canonical, sorted triples) makes the name
a pure function of the report: two runs over the same data and shapes mint the same IRIs,
and two *different* reports can never collide — which is exactly what a bare `_:1`-style
counter cannot promise. The cost is the other direction, and it is deliberate: a report
that differs anywhere is a different content id, so every node in it is renamed. Results
are aligned across reports by their content — `sh:focusNode`, `sh:resultPath`,
`sh:sourceConstraintComponent`, `sh:value` — not by their IRI; the `application/json`
face's sorted `violations` is that aligned view.

## Conformance

`tests/conformance.rs` runs [`ikigai-conformance`](https://crates.io/crates/ikigai-conformance)
over the module: ArgSpecs, capability enforcement, the RDF faces, cacheability, pipeline
citizenship and naming, every finding at once. It walks **twice**, because `shapes` is a
union and the two forms are two different truths about caching from one body of code:
inline shapes make the result a *pure* function of two by-value documents (an empty
golden-thread set is correct); shapes by reference make the report exactly as cacheable
as the shapes resource, inheriting its thread, so cutting that thread recomputes the
report. Both walks are clean.

Built on rudof's [`shacl`](https://crates.io/crates/shacl) crate. It links natively (CLI +
servers), and with the `module` feature it also builds as a lazy-loadable WASM module:

```text
cargo build --release --lib --features module --target wasm32-unknown-unknown
```

That build is possible since rudof 0.3.22, which removed the gate that kept
`shacl::validator` off wasm. CI type-checks it on wasm32 on every change (clippy, which
does not link); nothing here yet *loads* it in a browser or other wasm runtime. The JavaScript
[`shacl-engine`](https://www.npmjs.com/package/shacl-engine) remains a second implementation
of the same `urn:shacl:validate` resource, held to the same corpus (see Parity below).

## Caller SPARQL is bounded before rudof parses it

A shapes graph is caller text, and its `sh:select` constraints are SPARQL that rudof hands
to oxigraph's parser and evaluator once per focus node. Both recurse, and a stack overflow
aborts the whole process rather than failing one request: 300 nested parentheses in a
`sh:select`, or a 300-term `||` chain, killed a 2 MiB thread through `urn:shacl:validate`
(ledger #963). So, with the bounds and wording of `ikigai-store`'s `limits` module:

- every `sh:select` and `sh:ask` literal is checked before rudof compiles the shapes graph,
  and refused with a typed `InvalidArgument` on `shapes` past 1 MiB or 64 levels of nesting;
- the query rudof will actually build from each constraint is reconstructed and checked too,
  because two of its pieces are in no literal: the shape's `sh:path`, written into `$PATH`,
  and the `sh:declare` prefix names, written into a `PREFIX` header unescaped;
- validation runs on a thread sized for the longest of those queries (16 MiB plus 512 bytes
  per byte of query), so a long flat chain the nesting bound does not refuse still fits. On
  wasm there is no thread, and only the bound applies.

The reconstruction mirrors rudof's private query assembly, which is one more reason the rudof
upper bound below is deliberate: raising it means re-reading that code.

⚠ **Not bounded yet: recursion that is not SPARQL.** rudof parses a nested `sh:path` and
compiles nested shapes (`sh:not [ sh:not [ … ] ]`) recursively, and oxrdf clones a nested
RDF 1.2 triple term recursively while the Turtle is parsed. Deep enough input in `shapes` or
`data` still overflows the caller's stack. `cargo test --test sparql_stack -- --ignored
--nocapture survey` prints every case.

## Dependency pins

The rudof crates are pinned with a **real upper bound** (`>=0.3.22, <0.3.25`), not a
caret. That is deliberate and it is not tidiness: rudof's 0.3 line makes breaking API
changes inside *patch* releases — 0.3.17 added a third argument to
`ShaclProcessor::validate` — and under Cargo's 0.x rules `^0.3.8` already means
`>=0.3.8, <0.4.0`, so a caret cannot exclude one. `ikigai-shacl` 0.1.0 shipped
`shacl = "0.3"` and stopped compiling for every consumer the day 0.3.17 landed. Nothing
flagged it: this repo does not commit `Cargo.lock`, so CI *would* have caught it — but CI
had not run in 67 days.

The floor, 0.3.22, is the first release whose validator builds for wasm (and whose
`rudof_rdf` requires a `prefixmap` new enough that the direct constraint 0.1.3 carried is no
longer needed). The ceiling is the newest release tested: both ends were resolved from
scratch, built, and tested.

Raising the bound is a deliberate act. The daily build against the newest published
rudof — and the shacl-engine half of the parity contract against the newest npm — runs
from `upstream-watch.yml` in the private `ikigai-devtools` repo, not here: a per-repo
cron is disabled by GitHub after 60 days of repo inactivity, which silences it on
exactly the quiet repos that need it. devtools is the one repo that is never inactive.

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
cargo test                      # native rudof, the parity corpus, and the conformance walks
cd js-parity && npm ci && npm test   # shacl-engine parity
```
