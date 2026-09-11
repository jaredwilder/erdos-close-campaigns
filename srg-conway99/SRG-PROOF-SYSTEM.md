# SRG proof-producing bridge

This is the first proof-oriented vertical slice beyond graph connectivity.

## Components

- `oracle/kbk/engine/srg_spec.py` — typed SRG parameters, canonical labels, formal statement shape,
  and necessary-condition obligations.
- `oracle/kbk/engine/srg_semantic_index.py` — deterministic Mathlib concept index over the live theorem
  graph (`srg`, `construction`, `complement`, `parameters`, `matrix`, `diameter`, `open_goal`, and
  `existence`).
- `oracle/kbk/engine/srg_proof_search.py` — candidate search with three non-conflated states:
  `PROVED`, `REFUTED`, and `STILL_OPEN`.
- `oracle/kbk/engine/srg_lean_bridge.py` — Lean source emitter and compiler boundary. The complete-graph
  route emits `SimpleGraph.IsSRGWith.top` and was compiled successfully under the local Mathlib project.
- `oracle/kbk/engine/srg_result_import.py` — receipt importer that rejects missing certificates and
  refuses to attach certificates to `STILL_OPEN` results.

## Verified checks

The independent checker accepts the explicit `K5` construction as SRG(5,4,3,0). Its emitted Lean
theorem compiles. The parameter obstruction for `(5,2,0,2)` produces `REFUTED` using the SRG necessary
equation. Conway `(99,14,1,2)` produces `STILL_OPEN`: it is feasible, but no verified construction or
refutation certificate is present.

The three receipts import as exactly:

```json
{"PROVED": 1, "REFUTED": 1, "STILL_OPEN": 1}
```

This system does not claim that a finite checker receipt is automatically a Lean proof. Routes without
a compiled family-specific Lean emitter retain their independent-checker certificate and explicitly say
that Lean closure is still required.
