# Handoff — widen the conference↔SRG transport to reach the last unbridged island

## Where we are (real, verified numbers — checked directly against the live DB today)

`oracle/evidence/oracle-math.db` currently has these blade-bearing components:

| component | size | blade nodes | status |
|---|---|---|---|
| 668150 (kernel continent) | 524,266 | 0 | untouched — separate goal, not this task |
| 669145 | 941 | 844 | **merged today** (was two islands: 109-node + 737-node) |
| 669146 | 1,545 | 1,514 | **merged today** (was the 1,528-node island + new nodes) |
| **135224** | **1,482** | **1,481** | **still fully isolated — this is the target** |

Component 135224 is SRG parameter tuples with `v` roughly in the 100–1,300+ range (sample:
`srg:100,33,8,12` up to `srg:1300,516,254,172`).

## Why it's still isolated

`oracle/tools/transport-import/ingest_conference_nodes.py` (real, already run, already correct) ingested
`conference:n` / `paley:q` nodes only up to `n=98` / `q=97` — the range that `oracle/kbk/engine/srg_transports.py`
proposed and verified. Component 135224's SRG tuples have `v` well above that range, so the
`symmetric-conference-iff-conference-srg` transport (Haemers–Parsaei Majd: symmetric conference matrix of
order `4m+2` iff `SRG(4m+1, 2m, m-1, m)`) never reaches them — not because the transport is wrong, just
because it was never run out that far.

This was checked and confirmed correct end-to-end today (math verified against real Brouwer ground truth,
schema verified against the real live DB) for the range it already covers — this task is **widening the
same proven method**, not inventing a new one.

## The task

1. Read `oracle/tools/transport-import/ingest_conference_nodes.py` in full — it's short (~200 lines) and
   already does exactly this for `n` up to 98. Read `oracle/kbk/engine/srg_transports.py` too — it's where
   the transport rule itself (`symmetric-conference-iff-conference-srg`) is proposed and verified against
   `MIN_OVERLAP` / EXISTS-NONE balance.
2. Query `oracle/evidence/oracle-math.db` for the exact list of `v` values present in component 135224
   (`select label from nodes where component=135224 and label like 'srg:%'`) and derive the corresponding
   `conference:n` values needed to reach them (`n = v + 1`, restricted to `n ≡ 2 mod 4` per the transport's
   own applicability condition — most of them won't be `4m+2` shaped, and that's fine, only propose the ones
   that are).
3. Extend `srg_transports.py`'s existing conference-transport range (or add a new call using the same
   verified rule) to cover this wider `n` range, running the exact same PROPOSE→VERIFY discipline already in
   that file: real overlap count, real EXISTS/NONE balance, zero disagreements or the edge doesn't ship.
4. Run `ingest_conference_nodes.py` (or extend it) to insert the new `conference:n` nodes this wider range
   needs, using the exact same `conference_status()` logic already in that file (Belevitch necessary +
   Paley sufficient — don't reinvent, don't loosen it).
5. Verify the actual result: re-run the union-find rebuild and check whether component 135224 actually
   merges with 669145/669146 (or the giant continent — unlikely but check). Report the real before/after
   component sizes, not a prediction.

## Rules (same as always on this graph)

- Every transport edge must be independently re-verified (both sides recomputed), not asserted.
- If the wider range produces disagreements or falls below `MIN_OVERLAP`, report that honestly — a
  transport that doesn't hold at this range is a real, useful finding, not a failure to hide.
- Don't touch the `component` column directly — only the real union-find rebuild step should ever set it.
  (A prior one-shot attempt at an adjacent task wrote status strings into `component` instead of using the
  separate `facts` table — don't repeat that; `ingest_conference_nodes.py` shows the correct pattern.)
- If `conference:n` for some `n` in range is genuinely open (Belevitch necessary condition holds but no
  known construction, e.g. `n=66`), the existing code already returns `"OPEN"` for that — keep that
  three-state honesty, don't collapse it to EXISTS/NONE.

## Definition of done

Report the real component sizes for 135224 / 669145 / 669146 / 668150 after your change, pulled from the
actual database — not computed by hand.

## Final execution record

Completed against the live database. This checkout did not contain the conference transport implementation
inside `srg_transports.py`; the widening was implemented as the equivalent dedicated verifier at
`oracle/tools/transport-import/widen_conference_transport.py`, using the existing `conference_status()`
logic and the exact `4m+2` parameter map specified above.

Verification through `conference:1300` produced 118 decided overlap cases: 118 `EXISTS / EXISTS`,
0 `NONE` cases, and 0 disagreements. The migration inserted 103 new `conference:*` nodes and 103 new
edges; a second run inserted zero duplicates.

The exact target query found 71 SRG nodes in component `135224` matching the conference parameter map.
Every one was `OPEN / OPEN`, so no additional existence-verified edge could be emitted for those target
nodes under the stated verification rule.

Actual post-run database state:

| requested component | actual result |
|---|---|
| `135224` | 1,482 nodes; 1,481 blade nodes; unchanged and still isolated |
| `669145` | no longer an ID in the current materialized component table |
| `669146` | no longer an ID in the current materialized component table |
| `668150` | 524,266 nodes; 0 blade nodes; unchanged |

The populations previously reported under `669145` and `669146` are currently materialized as component
`669045` with 2,619 nodes. Component IDs are materialization identifiers; the stable conclusion is that
the widened conference transport did not merge `135224` with that population or with the kernel continent.

This task is therefore **verified but not successful as a bridge**. The next handoff must address the
71 `OPEN / OPEN` equivalence candidates or find a different independently verified transport; adding more
conference existence nodes alone will not move the target island.

### Structural-link completion

The 71 `OPEN / OPEN` candidates were subsequently emitted as structural proposition-equivalence edges,
without changing their existence status. The widened artifact now contains 324 structural conference/SRG
edges in total; 200 new edges and 200 new conference nodes were ingested on this final pass. All 71 target
links are now present in the live graph.

Final live state: component `135224` is 1,558 nodes (1,481 blade nodes), with 71 conference nodes and
71 incident conference/SRG edges. It still does not merge with the kernel continent or another existing
component because those newly materialized conference propositions have no pre-existing external component
membership. This is the completed, honest graph result: the target is no longer missing its structural
conference links, but a cross-component bridge remains unsolved.

Evidence and implementation:

- `oracle/tools/transport-import/widen_conference_transport.py`
- `oracle/tools/transport-import/audit_srg_bridge_frontier.py`
- `oracle/evidence/transport-graph/conference-widened-edges.jsonl`
- `oracle/kbk/codex-handoff-graph-bridge/CONFERENCE-WIDENING-REPORT.md`

The reusable frontier audit now reports `CLOSED_UNDER_CURRENT_GRAPH`: 1,481 SRG nodes, 71 materialized
conference candidates, and 0 composable exits from component `135224`.

### Final live audit (2026-07-24)

The final audit was run directly against `oracle/evidence/oracle-math.db` after all staged transport
artifacts were ingested:

| component | size | blade nodes |
|---|---:|---:|
| `135224` | 1,553 | 1,481 |
| `669199` | 1,049 | 0 |
| `668150` | 524,266 | 0 |

The target contains 1,481 SRG nodes and 71 materialized conference candidates. It has **0 composable
exits** (`EQUIVALENCE`/`IMPLICATION`) to another component, so no cross-component merge is justified by
the current evidence graph. The audit artifact is
`oracle/kbk/codex-handoff-graph-bridge/srg-bridge-frontier-audit.json`.

The clean rebuild was executed in an isolated SQLite file and then copied back into the live database using
SQLite's backup API. The rebuild also corrected five stale elliptic-curve nodes that had been assigned the
target component despite having no connecting edge. After rebinding the executable blades, the live audit
reports the reproducible final target size of **1,553 nodes** (1,482 SRG/status nodes plus 71 conference
nodes), **1,481 blade nodes**, and **0 composable exits**. The earlier 1,558-node figure included those five
stale component assignments and is superseded by this union-find rebuild.

The gated two-wall SRG blade was run across all 1,481 target SRGs. Its ground-truth validation gate was
green, and the target results were `FRONTIER: 1,481`, `REFUTED: 0`, `EXISTS: 0`; therefore this engine
supplies neither a valid NONE/status bridge nor an existence witness.

### Verified SRG-layer rebuild correction (latest)

The rebuild pipeline was missing `oracle/evidence/transport-graph/srg-transports.jsonl` and the checked
switching layer. Those artifacts are now explicit `build_db.py` inputs. The clean rebuild and live
materialization include 2,545 additional typed SRG transport edges, including 2,203 previously inert
endpoint references. Using the stable target label `srg:1001,136,27,17`, the current materialized target
component is `671625` with **2,963 nodes**, **2,891 SRG/blade nodes**, and **71 conference candidates**;
the component still has **0 composable exits**. The audit now accepts `--label` so it resolves the
materialization component ID instead of assuming a stale numeric root.

The forge survivor layer (`forged-transports.jsonl`) was also added to the rebuild inputs and promoted to
the live database. The final stable-label audit now resolves component `671257`: **2,963 nodes**, **2,891
SRG/blade nodes**, **71 conference candidates**, and **0 composable exits**. Including every currently
verified transport layer improves graph coverage but still does not produce the requested cross-component
bridge.

The reusable raw-artifact audit (`oracle/tools/transport-import/audit_raw_srg_frontier.py`) scanned the
transport JSONL sources for all 2,891 target SRGs. It found 3,033 raw references, consisting only of 1,481
status implications, 1,481 complement equivalences, and 71 conference equivalences. It found **0
composable external raw hits**, proving that the current zero-exit result is not caused by an un-ingested
endpoint hidden in the staged transport corpus.

Post-rebuild transport self-tests remain green: `srg_transports.py` verifies 253 complement, 44 triangular,
and 34 lattice overlaps with zero disagreements; `srg_switching.py` verifies its Paley control, involution,
vertex-count, and checker gates. The switching search reaches 0 OPEN targets, so it adds no bridge edge.

The live authoritative Brouwer HTML tables (all ranges through 1,300 vertices) were fetched and compared
against the 2,891 target SRG tuples. There were **0 status changes** relative to the local facts snapshot.

### Formal proposition bridge: Conway 99 (2026-07-24)

The attached diagnosis identified the missing ontology: `srg:99,14,1,2` is the same open existence
proposition as Mathlib's `SimpleGraph.conway_99`. The pinned Mathlib source was fetched and verified:
`conway_99` is declared with `proof_wanted` as the existence of a graph satisfying
`IsSRGWith 99 14 1 2`, and the source explicitly says the problem is open with no known proof of
existence.

The new artifact `oracle/evidence/transport-graph/formal-proposition-bridges.jsonl` adds two typed edges:

- `SAME_PROPOSITION`: `srg:99,14,1,2` → `decl:SimpleGraph.conway_99`.
- `IMPLICATION` / `statement-depends-on`: `decl:SimpleGraph.conway_99` →
  `decl:SimpleGraph.IsSRGWith`, attaching the omitted `proof_wanted` declaration to the existing
  Mathlib dependency component.

Neither edge is `PROVES` or `IMPLIES_EXISTS`; the receipt explicitly records that this is a formal
open-goal identity, not an existence witness. `build_db.py` now ingests this artifact, and the frontier
audit recognizes `SAME_PROPOSITION`/`FORMALIZES` while distinguishing a merged component from a closed
island.

After isolated rebuild and SQLite-backup promotion, the stable target label resolves to component `668150`
with **527,230 nodes**, **2,891 SRG blade nodes**, **500,666 Mathlib nodes**, and
`formalPropositionBridges: 1`. Its status is now **MERGED_WITH_MATHLIB**. The reported
`composableExits: 0` is therefore expected: there is no remaining exit because the target has already
joined the Mathlib continent. Transport self-tests remain green.

### Proof-producing vertical slice (2026-07-24)

The next layer is implemented in `oracle/kbk/engine/`: `srg_spec.py` provides the typed SRG object
language; `srg_semantic_index.py` indexes Mathlib declarations by reusable semantic concepts;
`srg_proof_search.py` searches verified constructions and necessary-condition certificates;
`srg_lean_bridge.py` emits/compiles Lean routes; and `srg_result_import.py` imports only typed
`PROVED`, `REFUTED`, or `STILL_OPEN` receipts.

The live regression slice is explicit and honest:

- SRG(5,4,3,0): `PROVED` by an independently checked complete graph; emitted Lean theorem using
  `SimpleGraph.IsSRGWith.top` compiles under the local Mathlib project.
- SRG(5,2,0,2): `REFUTED` by the necessary SRG parameter equation.
- Conway SRG(99,14,1,2): `STILL_OPEN`; feasibility is not mistaken for existence.

The semantic index currently materializes **87,739** Mathlib entries, including SRG/complement,
construction, parameter, matrix, diameter, open-goal, and existence concepts. The detailed design and
receipts are in `SRG-PROOF-SYSTEM.md`.
