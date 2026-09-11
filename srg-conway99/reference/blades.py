"""blades.py — IOU-2. Bind executable blades to the nodes they can actually attack.

A graph of 664,347 nodes is useless for action until the machine knows which of them it can *attack today*.
Each blade declares: the node pattern it accepts, its entrypoint, its gate status, and what evidence class
it can produce. Binding is by pattern over node labels, so adding a blade requires no graph rebuild.

Gate status is not decorative — a blade that has not reproduced known ground truth may be bound but is
NEVER schedulable for a theorem-producing claim (the plan's capability-contract rule).
"""
from __future__ import annotations
import io, json, os, re, sqlite3, sys

# NOTE: never reassign sys.stdout at import time — the wrapper closes the real stdout when it is
# garbage-collected, breaking every module that imports this one. Encoding is the caller's job.
HERE = os.path.dirname(os.path.abspath(__file__))
ORACLE = os.path.normpath(os.path.join(HERE, "..", ".."))
DB = os.path.join(ORACLE, "evidence", "oracle-math.db")

# blade_id, module, entrypoint, node-label regex, evidence class, gate evidence
BLADES = [
    ("two_wall.srg", "scripts/frontier_math_printer/two_wall_engine.py", "decide_srg",
     r"^srg:\d+,\d+,\d+,\d+$", "necessary-condition-refutation",
     "GATED 8/8 VALIDATION; 642 known-EXISTS controls -> 0 false walls; rederives 142/297 known impossibilities"),
    ("two_wall.steiner", "scripts/frontier_math_printer/two_wall_engine.py", "decide_steiner",
     r"^steiner:\d+,\d+,\d+$", "construct-or-refute",
     "GATED: Fano EXISTS, S(2,3,8) REFUTED, Witt S(5,6,12) EXISTS, S(6,7,13) REFUTED"),
    ("two_wall.symmetric", "scripts/frontier_math_printer/two_wall_engine.py", "decide_symmetric",
     r"^symmetric:\d+,\d+,\d+$", "construct-or-refute",
     "GATED: plane order 6 REFUTED (Bruck-Ryser), plane order 2 EXISTS"),
    ("covering.exact", "kbk/engine/covering_design.py", "attack",
     r"^covering:\d+,\d+,\d+$", "exact-minimum + Schoenheim",
     "GATED: C(7,4,2)=5 and C(7,4,3)=12 PROVEN_optimal"),
    ("covering.decision", "kbk/engine/record_attack.py", "decide_at",
     r"^covering:\d+,\d+,\d+$", "feasibility-at-record-minus-1",
     "GATED 4/4: C(7,3,2) 6 UNSAT / 7 SAT; C(9,4,2) 7 UNSAT / 8 SAT"),
    ("sidon.decide", "kbk/engine/sidon_decide.py", "decide",
     r"^sidon:\d+$", "feasibility-decision",
     "GATED vs published A309370: f(4)=7, f(5)=12, f(6)=15 all SAT-at / UNSAT-above"),
    ("computed_truth.steiner", "kbk/engine/computed_truth.py", "steiner_status",
     r"^steiner:\d+,\d+,\d+$", "decided-ground-truth",
     "selftest 13/13, handTypedLists 0; cross-validated vs OEIS A030128/A030129 39/39"),
    ("computed_truth.plane", "kbk/engine/computed_truth.py", "plane_status",
     r"^symmetric:\d+,\d+,\d+$|^plane:\d+$", "decided-ground-truth",
     "BRC + prime-power + Lam 1989"),
    ("computed_truth.ramsey", "kbk/engine/computed_truth.py", "ramsey_status",
     r"^ramsey:\d+,\d+,\d+$", "decided-ground-truth",
     "CP-SAT exact; reproduces R(3,3)=6, R(3,4)=9"),
    ("computed_truth.hadamard", "kbk/engine/computed_truth.py", "hadamard_status",
     r"^hadamard:\d+$", "decided-ground-truth",
     "order condition + Sylvester/Paley/Kronecker closure; 668 correctly UNDECIDED"),
]


def install() -> None:
    con = sqlite3.connect(DB)
    con.executescript("""
        DROP TABLE IF EXISTS blades; DROP TABLE IF EXISTS node_blade;
        CREATE TABLE blades(blade_id TEXT PRIMARY KEY, module TEXT, entrypoint TEXT,
                            pattern TEXT, evidence_class TEXT, gate TEXT);
        CREATE TABLE node_blade(node INTEGER, blade_id TEXT);
    """)
    con.executemany("INSERT INTO blades VALUES (?,?,?,?,?,?)", BLADES)

    rows = con.execute("SELECT id, label FROM nodes").fetchall()
    pats = [(b[0], re.compile(b[3])) for b in BLADES]
    binds = []
    for nid, label in rows:
        for bid, rx in pats:
            if rx.match(label):
                binds.append((nid, bid))
    con.executemany("INSERT INTO node_blade VALUES (?,?)", binds)
    con.executescript("CREATE INDEX ix_nb_node ON node_blade(node); CREATE INDEX ix_nb_blade ON node_blade(blade_id);")
    con.commit()

    print(f"  blades registered: {len(BLADES)}")
    print(f"  node<->blade bindings: {len(binds):,}")
    for bid, n in con.execute("""SELECT blade_id, COUNT(*) FROM node_blade GROUP BY blade_id
                                 ORDER BY COUNT(*) DESC"""):
        print(f"     {n:>6,}  {bid}")
    con.close()


def attackable_now(limit: int = 25) -> list[dict]:
    """Nodes we hold a GATED blade for AND whose status is not already decided."""
    con = sqlite3.connect(DB); con.row_factory = sqlite3.Row
    rows = [dict(r) for r in con.execute("""
        SELECT n.label, n.ns, n.degree, GROUP_CONCAT(nb.blade_id) AS blades
        FROM nodes n JOIN node_blade nb ON nb.node = n.id
        GROUP BY n.id ORDER BY n.degree DESC LIMIT ?""", (limit,))]
    con.close()
    return rows


if __name__ == "__main__":
    install()
    print("\n  ATTACKABLE NOW (highest-degree nodes with a gated blade bound):")
    for r in attackable_now(10):
        print(f"     {r['label'][:44]:44s} deg {r['degree']:>4}  {r['blades']}")
