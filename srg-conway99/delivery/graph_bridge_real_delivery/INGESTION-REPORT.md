# Verified design-transport ingestion

The verified delivery has been ingested into the live `oracle/evidence/oracle-math.db` using
`oracle/tools/transport-import/ingest_verified_design_nodes.py`.

## Result

- 141 composable delivery edges read; 141 inserted.
- 112 missing endpoint nodes inserted; all 211 distinct delivery endpoints now resolve.
- Newly materialized families: `conference` (21), `latin-square` (7), `lattice` (8),
  `paley` (15), `steiner` (4), and `triangular` (10).
- Live totals after ingestion: 669,265 nodes, 7,408,361 edges, 73,936 components.
- Re-running the migration inserted 0 edges and 0 nodes.
- The migration preserves existing node IDs, facts, blade bindings, and unrelated edges.

The five sampled nodes previously used to characterize component `668272` now resolve to
the same live 1,545-node component (`669146` in this DB snapshot), and each remains blade-bound
where applicable. Component IDs are database materializations and may differ between rebuilds;
labels and component membership are the stable claims.

## Reproduce

```powershell
python oracle/tools/transport-import/ingest_verified_design_nodes.py `
  --db oracle/evidence/oracle-math.db `
  --edges oracle/kbk/codex-handoff-graph-bridge/delivery/graph_bridge_real_delivery/verified-edges.jsonl

python oracle/kbk/codex-handoff-graph-bridge/delivery/graph_bridge_real_delivery/connectivity_impact.py
```

The connectivity analyzer remains a pre-state impact tool: after ingestion, its proposed
edges are already represented in the DB, so a second run reports no additional movement.
