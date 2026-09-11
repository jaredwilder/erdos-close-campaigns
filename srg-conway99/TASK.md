# The Task — bridge blade-bearing islands into the kernel continent

## The real, measured numbers (live query, 2026-07-24 — see `reference/live-db-snapshot-2026-07-24.json`)

```
total nodes in graph:        669,153
total edges:                 7,408,220
total connected components:  73,937
giant "kernel continent":    524,266 nodes  (component id 668150)
total blade-bound nodes:     3,865   <- nodes with at least one attached executable blade
blade nodes IN the giant continent:  0
```

Every one of those 3,865 blade-bound nodes sits on one of these islands instead:

| component id | blade nodes | island size | node family (sampled) |
|---|---|---|---|
| 668272 | 1,514 | 1,528 | `srg:*` — mid-size SRG parameter tuples (e.g. `srg:21,10,4,5`, `srg:50,21,4,12`) |
| 135224 | 1,481 | 1,482 | `srg:*` — large SRG parameter tuples (e.g. `srg:1001,300,103,84`) |
| 668209 | 736 | 737 | `srg:*` — small-to-mid SRG tuples (e.g. `srg:37,18,8,9`) |
| 135185 | 108 | 109 | `srg:*` — smallest SRG tuples (e.g. `srg:5,2,0,1`, `srg:10,3,0,1`) |
| ~40+ more | 2 each | 2 each | isolated `steiner:2,3,n` + `srg:*` pairs, one per n |

The giant continent (524,266 nodes) is almost entirely `oeis:*` and `mathlib:*` declarations (see
`giant_continent_samples` in the snapshot file) — it was built by mining `Iff` theorems out of Mathlib
(`reference/mathlib_armory.py`). **Mathlib has essentially no formalized design/SRG theory to mine**
(verbatim file-count audit from this project's own history: `ProjectivePlane` 1 file, `Hadamard` 6,
`SteinerSystem` 0, `BlockDesign` 0, `Fisher` 0, difference-set 0) — so the mining approach that built the
giant continent structurally cannot reach these islands. A different bridging mechanism is required:
**hand-proposed, machine-verified classical design-theory equivalences**, exactly the pattern in
`reference/design_transports.py`.

## What edges mean here (so your proposals are the right shape)

Schema: `edges(src, dst, type, tier, source, rule)`. Only `type IN ('EQUIVALENCE', 'IMPLICATION')` edges
count for connectivity — `ANALOGY` edges are stored but never traversed (see `reference/oracle_db.py`,
`COMPOSABLE` constant). Node labels are family-prefixed strings: `srg:v,k,lambda,mu` (a strongly-regular-
graph parameter tuple), `steiner:t,k,v` (a Steiner system), `plane:n` (projective plane of order n),
`hadamard:n` (Hadamard matrix order n), `decl:...` (Mathlib Lean declaration), `A######` (OEIS sequence).

## The specific, already-attempted, still-open sub-problem

`reference/design_transports.py` already merged one island by proving `plane:n <-> steiner:2,n+1,n²+n+1`
(16 EXISTS/0 NONE — flagged `[ONE-SIDED]`, see `DOCTRINE.md`) and one implication
(`steiner-triple-system-block-graph-is-srg`). Per this project's own log
(`oracle/brain/ORACLE-IOU-MASTER-2026-07-07.md`, "Still open" line): **the SRG island (the 1,481/1,482 and
1,514/1,528-node components above) remains unbridged — no correct cross-family transport into it has been
verified yet.** A file `reference/srg_transports.py` exists in the live repo and is the freshest
transport-graph file (modified same day as this measurement) — read it first; it may already contain a
partial attempt. Do not assume it's finished or correct — verify it yourself against `DOCTRINE.md`'s bar.

## Your job, concretely

1. **Read `reference/srg_transports.py` first.** Determine what it already proposes/verifies, and whether
   its verification is honest (real `computed_truth` calls, real overlap, real disagreement reporting) or
   whether it's a stub/partial. Report this regardless of what else you do.
2. **Propose real, checkable transports that touch the SRG islands.** Known classical equivalences worth
   checking (these are real mathematical facts to verify point-by-point, not to assume):
   - Conference-matrix / SRG connections: a symmetric conference matrix of order `n` exists iff a specific
     SRG family exists (check the exact parameter relation — do not guess it, derive or cite it precisely).
   - Paley graph constructions: `srg:(q, (q-1)/2, (q-5)/4, (q-1)/4)` for prime power `q ≡ 1 mod 4` — this is
     a *construction* (existence proof), not just a parameter check; verify it actually produces a graph
     with those exact parameters for several real `q` values, not just that the arithmetic is consistent.
   - Steiner-system-to-SRG block graphs at parameters beyond what `design_transports.py` already covers
     (check its `range` — extend only where you can independently verify, don't just widen the range and
     assume it still holds).
   - Any other real, citable classical design-theory <-> SRG equivalence you know of — cite it, then verify
     it the same way, honestly reporting disagreements if any.
3. **For each proposed transport: run PROPOSE/VERIFY exactly per `DOCTRINE.md`.** Report the real overlap
   count, the real EXISTS/NONE balance, and any disagreements found — even if that means reporting the
   transport doesn't hold and explaining why.
4. **If you cannot find a real bridging transport for one of these islands, say so explicitly** and name
   what's actually missing (a specific unformalized theorem, a specific missing data source, a specific
   parameter regime where the classical theory itself is open) — this is a legitimate and valuable outcome,
   not a failure to hide.

## Definition of done

- At minimum: an honest, verified report on `srg_transports.py`'s current state.
- Ideally: one or more new `EQUIVALENCE`/`IMPLICATION` edge proposals, each with a `selftest()` (see
  `reference/run_selftests.py` convention) that independently re-derives and checks the transport against a
  known ground-truth case (e.g. a specific SRG parameter tuple known to exist/not-exist from Brouwer's
  table), and a real verification run showing overlap count + disagreement count for the actual claimed
  parameter range.
- Explicitly report the before/after: how many of the 3,865 blade-bound nodes would move into (or bridge
  toward) the 524,266-node giant continent if your edges were accepted — compute this honestly from the
  transport's actual verified scope, not the full island size, unless the transport genuinely covers the
  whole island.
