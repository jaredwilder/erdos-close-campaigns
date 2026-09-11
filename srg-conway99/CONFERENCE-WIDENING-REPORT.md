# Widened conference transport

The widened pass was run against the live `oracle/evidence/oracle-math.db` through order 1300.
It used the existing `conference_status()` implementation and the exact map
`conference:n ↔ SRG(n−1, 2m, m−1, m)` for `n = 4m+2`.

Verification result:

- 118 decided overlap cases.
- 118 `EXISTS / EXISTS`; 0 `NONE` cases.
- 0 disagreements.
- 118 edges emitted; 103 new edges and 103 new `conference:*` nodes were inserted.
- A second verification emitted the same 118 edges; the migration inserted 0 duplicates.

The target component did not merge. Actual post-run state:

- component `135224`: 1,482 nodes, 1,481 blade nodes.
- kernel component `668150`: 524,266 nodes, 0 blade nodes.
- The handoff’s prior IDs `669145` and `669146` are no longer component IDs in this live
  snapshot; their previously merged populations are now component `669045` with 2,619 nodes.

Thus the wider range is verified and load-bearing, but it does not reach component `135224`:
the 118 emitted conference/SRG matches already terminate inside that same SRG component.
No claim of a merge is made.

## Structural completion

The 71 target `OPEN / OPEN` proposition equivalences were then emitted as structural graph links,
without promoting either side to an existence claim. The final widened artifact contains 324 structural
conference/SRG edges. The final migration inserted 200 new edges and 200 new conference nodes.

Component `135224` is now 1,558 nodes with 1,481 blade nodes; 71 of those nodes are conference propositions
and all 71 target conference/SRG links are present. No component merge occurred because the new conference
propositions had no existing external component membership. The graph is structurally complete for this
transport range, but the cross-component bridge remains unresolved.

Artifacts:

- `oracle/tools/transport-import/widen_conference_transport.py`
- `oracle/evidence/transport-graph/conference-widened-edges.jsonl`
