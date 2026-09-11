# Codex Handoff — Bridge the Marooned Blade Islands (Kernel-Continent Connectivity)

**Start here, in this order:**

1. **`DOCTRINE.md`** — non-negotiable rules. Read in full before writing any code. The short version: every
   edge you propose must be independently verified by real computation, not asserted from memory or by an
   LLM at runtime. A false "verified" edge here is worse than no edge — it corrupts every future query that
   trusts this graph.
2. **`TASK.md`** — the actual ask, with the real measured numbers, real file paths, and a concrete
   definition of done.
3. **`ACCEPTANCE-CONTRACT.md`** — exactly how your submission gets checked before anything is merged.
4. **`reference/`** — real files pulled directly from the live repository (you have no repo access; this
   folder IS your repo access):
   - `build_db.py`, `blades.py`, `oracle_db.py`, `mathlib_armory.py`, `armory.py` — the actual graph
     construction and query layer (`oracle/tools/transport-import/`).
   - `design_transports.py`, `srg_transports.py`, `two_wall_engine.py` — the actual bridge-attempt code and
     blade entrypoints (`oracle/kbk/engine/` and `oracle/scripts/frontier_math_printer/`).
   - `run_selftests.py` — the test-harness convention every tool follows.
   - `live-db-snapshot-2026-07-24.json` — a REAL query dump taken today against the live 669,153-node,
     7,408,220-edge SQLite graph: exact component sizes, exact blade-node counts per island, and real sample
     node labels from each island and from the giant continent. Not a description — the actual data.
   - `live-db-schema.txt` — the exact live `CREATE TABLE` statements for every table in the graph DB.

## What this project is (context, briefly)

"The Oracle" is a $0, deterministic scientific-discovery system built by a solo operator + an AI coding
assistant (Claude). This subsystem specifically maintains a single graph of ~669k mathematical objects
(OEIS sequences, Mathlib Lean declarations, strongly-regular-graph parameter tuples, Steiner systems,
Hadamard matrices, projective planes...) connected by machine-verified `EQUIVALENCE`/`IMPLICATION` edges.
Executable "blades" (real solvers — SAT, exact search, computed-truth lookups) attach to specific node
patterns. The value of the whole graph is that a blade's answer can propagate along verified edges to
every equivalent/implied node — turning one computation into many answers.

**The problem:** the blades and the graph never actually met. Every blade-bearing node sits on a small
isolated island; the 524,266-node giant "continent" (built from Mathlib) has zero blades on it. You're
being asked to build real, verified transport edges that reduce this gap — not to fake a merge.

## Return format

Return each transport/bridge tool as a complete, standalone Python file matching the `selftest()`
convention (see `reference/run_selftests.py` and the examples in `TASK.md`). A short cover note per file
(2-4 sentences: what edge family it proposes, what it verified against, what it explicitly refused to
claim) is worth more than a long README. Include the raw verification output (which node pairs passed,
which failed, the overlap count) — not just a pass/fail summary.

**Honesty over volume.** A single genuinely verified edge that merges two real islands is worth more than
100 proposed edges that "look plausible." If you can't find a real bridging transport for a given island,
say so explicitly and explain what would be needed (a specific missing theorem, a specific missing data
source) — that's a valid and valuable deliverable too.
