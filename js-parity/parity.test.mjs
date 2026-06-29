// Cross-implementation parity: the BROWSER validator (shacl-engine) must produce the same
// outcome as the native rudof validator for every case in ../tests/corpus/. Both are asserted
// against the SAME expected.json (conforms + the {focus_node, path, component} violation
// signatures), so the two implementations agree by construction. This is the JS half; the
// Rust half is ../tests/parity.rs.

import test from 'node:test'
import assert from 'node:assert/strict'
import { readFileSync, readdirSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { dirname, join } from 'node:path'
import rdf from '@zazuko/env'
import { Parser } from 'n3'
import Validator from 'shacl-engine/Validator.js'

// Exactly the stack the browser loader (web-demo dist/shacl-loader.js) uses — @zazuko/env +
// n3 + shacl-engine — so this CI suite guards the real browser implementation, not a proxy.
const corpus = join(dirname(fileURLToPath(import.meta.url)), '..', 'tests', 'corpus')

function parse (ttl) {
  return rdf.dataset(new Parser({ factory: rdf }).parse(ttl))
}

// shacl-engine report → the portable ValidationOutcome (same shape as ikigai_shacl's).
function outcome (report) {
  const violations = report.results.map(r => ({
    focus_node: r.focusNode?.term?.value ?? null,
    path: r.path?.[0]?.predicates?.[0]?.value ?? null,
    component: r.constraintComponent?.value ?? null
  }))
  return { conforms: report.conforms, violations }
}

// Order-independent signature set + the conforms flag — the parity contract.
function canonical (o) {
  return {
    conforms: o.conforms,
    sigs: o.violations.map(v => JSON.stringify([v.focus_node, v.path ?? null, v.component])).sort()
  }
}

for (const name of readdirSync(corpus, { withFileTypes: true }).filter(d => d.isDirectory()).map(d => d.name)) {
  test(`shacl-engine matches expected for ${name}`, async () => {
    const dir = join(corpus, name)
    const data = await parse(readFileSync(join(dir, 'data.ttl'), 'utf8'))
    const shapes = await parse(readFileSync(join(dir, 'shapes.ttl'), 'utf8'))
    const report = await new Validator(shapes, { factory: rdf }).validate({ dataset: data })
    const expected = JSON.parse(readFileSync(join(dir, 'expected.json'), 'utf8'))
    assert.deepStrictEqual(canonical(outcome(report)), canonical(expected),
      `shacl-engine outcome for ${name} != expected.json (native rudof)`)
  })
}
