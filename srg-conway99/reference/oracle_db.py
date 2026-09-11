"""oracle_db.py — the query layer. This is what the engine calls; nothing else touches the store.

Every function answers a question the machine actually needs to act on. Composability is enforced here:
ANALOGY edges are stored but NEVER traversed, per the transport algebra.
"""
from __future__ import annotations
import io, os, sqlite3, sys

# NOTE: never reassign sys.stdout at import time — the wrapper closes the real stdout when it is
# garbage-collected, breaking every module that imports this one. Encoding is the caller's job.
DB = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "evidence", "oracle-math.db")
DB = os.path.normpath(DB)
COMPOSABLE = "type IN ('EQUIVALENCE','IMPLICATION')"


def _c() -> sqlite3.Connection:
    con = sqlite3.connect(DB)
    con.row_factory = sqlite3.Row
    return con


def overview() -> dict:
    with _c() as con:
        q = lambda s: con.execute(s).fetchone()[0]
        return {
            "edges": q("SELECT COUNT(*) FROM edges"),
            "composable": q(f"SELECT COUNT(*) FROM edges WHERE {COMPOSABLE}"),
            "nodes": q("SELECT COUNT(*) FROM nodes"),
            "components": q("SELECT COUNT(*) FROM components"),
            "giant": q("SELECT MAX(size) FROM components"),
            "targets": q("SELECT COUNT(*) FROM targets"),
            "facts": q("SELECT COUNT(*) FROM facts"),
            "kernelEdges": q("SELECT COUNT(*) FROM edges WHERE tier='kernel-verified'"),
        }


def component_of(label: str) -> dict | None:
    """Which component does this object live in, and how big is it?"""
    with _c() as con:
        r = con.execute("""SELECT n.label, n.ns, n.component, c.size, n.degree
                           FROM nodes n JOIN components c ON c.component=n.component
                           WHERE n.label=?""", (label,)).fetchone()
        return dict(r) if r else None


def neighbours(label: str, limit: int = 25) -> list[dict]:
    """Composable neighbours only — ANALOGY is never traversed."""
    with _c() as con:
        return [dict(r) for r in con.execute(f"""
            SELECT m.label AS other, e.type, e.tier, e.source, e.rule
            FROM nodes n JOIN edges e ON e.src=n.id JOIN nodes m ON m.id=e.dst
            WHERE n.label=? AND {COMPOSABLE}
            UNION ALL
            SELECT m.label, e.type, e.tier, e.source, e.rule
            FROM nodes n JOIN edges e ON e.dst=n.id JOIN nodes m ON m.id=e.src
            WHERE n.label=? AND {COMPOSABLE}
            LIMIT ?""", (label, label, limit))]


def bridge_candidates(limit: int = 20) -> list[dict]:
    """THE money query. Which component pairs would a single verified bridge fuse?
    Ranked by the size of the merge — this is where a dollar buys the most reach."""
    with _c() as con:
        comps = [dict(r) for r in con.execute("""
            SELECT c.component, c.size,
                   (SELECT ns FROM nodes WHERE component=c.component
                    GROUP BY ns ORDER BY COUNT(*) DESC LIMIT 1) AS ns
            FROM components c WHERE c.size > 1 ORDER BY c.size DESC LIMIT 60""")]
        out = []
        for i, a in enumerate(comps):
            for b in comps[i + 1:]:
                if a["ns"] == b["ns"]:
                    continue                       # same-corpus merges are cheap; cross-corpus is the prize
                out.append({"from_ns": a["ns"], "from_size": a["size"],
                            "to_ns": b["ns"], "to_size": b["size"],
                            "merge_gain": a["size"] + b["size"],
                            "from_component": a["component"], "to_component": b["component"]})
        out.sort(key=lambda x: -x["merge_gain"])
        return out[:limit]


def stranded_rich(ns: str | None = None, limit: int = 20) -> list[dict]:
    """Nodes with real machinery attached but almost no composable connections — build transports here."""
    with _c() as con:
        sql = """SELECT n.label, n.ns, n.degree, c.size AS component_size
                 FROM nodes n JOIN components c ON c.component=n.component
                 WHERE n.degree BETWEEN 1 AND 3 AND c.size < 50"""
        args: tuple = ()
        if ns:
            sql += " AND n.ns=?"; args = (ns,)
        sql += " ORDER BY n.degree DESC, c.size ASC LIMIT ?"
        return [dict(r) for r in con.execute(sql, args + (limit,))]


def facts(family: str, status: str | None = None, limit: int = 50) -> list[dict]:
    with _c() as con:
        if status:
            return [dict(r) for r in con.execute(
                "SELECT * FROM facts WHERE family=? AND status=? LIMIT ?", (family, status, limit))]
        return [dict(r) for r in con.execute("SELECT * FROM facts WHERE family=? LIMIT ?", (family, limit))]


def targets(source: str | None = None, limit: int = 25) -> list[dict]:
    with _c() as con:
        if source:
            return [dict(r) for r in con.execute(
                "SELECT * FROM targets WHERE source=? LIMIT ?", (source, limit))]
        return [dict(r) for r in con.execute("SELECT * FROM targets LIMIT ?", (limit,))]


def ns_census() -> list[dict]:
    with _c() as con:
        return [dict(r) for r in con.execute(
            "SELECT ns, COUNT(*) AS nodes, SUM(degree) AS degree FROM nodes GROUP BY ns ORDER BY nodes DESC")]


if __name__ == "__main__":
    import json
    print("OVERVIEW:", json.dumps(overview(), indent=1))
    print("\nNAMESPACES:")
    for r in ns_census():
        print(f"   {r['ns']:12s} {r['nodes']:>9,} nodes")
    print("\nFIBONACCI:", json.dumps(component_of("A000045")))
    print("\nTOP CROSS-CORPUS BRIDGE CANDIDATES (where one edge buys the most reach):")
    for b in bridge_candidates(8):
        print(f"   {b['from_ns']:10s}({b['from_size']:>7,}) <-> {b['to_ns']:10s}({b['to_size']:>7,})  gain {b['merge_gain']:>8,}")
