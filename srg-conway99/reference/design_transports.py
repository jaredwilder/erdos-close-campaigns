"""design_transports.py — the classical design-theory equivalences, PROPOSED here and VERIFIED by the engine.

WHY THIS IS THE ASSEMBLY. Measured 2026-07-23: 0 of 3,714 blade-bound nodes sit in the 524,266-node
kernel continent. Every executable blade we own is marooned on five tiny islands (1,158 / 1,482 / 702 /
268 / 109 nodes) — only 0.56% of the graph shares a component with any blade. Mathlib cannot bridge them:
it has ONE file mentioning ProjectivePlane and zero for Steiner systems, block designs or Fisher. Formalized
mathematics has not formalized design theory, so the bridge has to come from design theory's own classical
equivalences. That import is what merges the islands, and merging is superlinear: a blade on either side of
a verified transport becomes available to both.

THE HONESTY RULE THAT MAKES THIS LEGITIMATE. I can state these equivalences from the literature, but a
statement from a model is not evidence — that is the entire threat model of this system. So the roles are
split, and the split is enforced by the code below:

    PROPOSE (me)   a parameter map between two families, e.g. plane(n) <-> S(2, n+1, n^2+n+1).
    VERIFY (engine) run BOTH sides through `computed_truth` on every instance where both are decided.
                    Total agreement across the whole overlap, or the transport is REJECTED.

A transport that disagrees anywhere is discarded, not patched. And a disagreement is not merely a failed
import — it means one of two independently-written verdict functions is WRONG, which is a finding in its own
right and is reported as one.

DEGENERATE-TRANSPORT GUARD. A map verified on an overlap of one or two instances is coincidence, not
evidence; MIN_OVERLAP instances must be decided on both sides before agreement counts for anything. This is
the same lesson that killed 6.96M partial-product edges and 87 OEIS pattern-matches: agreement that carries
no information is worse than no agreement, because it looks like proof.
"""
from __future__ import annotations
import io, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ORACLE = os.path.normpath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)
OUT = os.path.join(ORACLE, "evidence", "transport-graph", "design-transports.jsonl")

MIN_OVERLAP = 5          # instances decided on BOTH sides before agreement is evidence of anything


def _node(fam: str, params) -> str:
    return f"{fam}:{','.join(str(x) for x in params)}" if isinstance(params, (list, tuple)) else f"{fam}:{params}"


# Each transport: a name, the two family endpoints as functions of a free parameter, the parameter range,
# the transport TYPE, and a literature receipt. Nothing here is trusted until the engine agrees.
TRANSPORTS = [
    {
        "name": "projective-plane-is-steiner-2-design",
        "receipt": "Handbook of Combinatorial Designs, Part II (projective planes as S(2,n+1,n^2+n+1))",
        "type": "EQUIVALENCE",
        "range": range(2, 31),
        "left": lambda n: ("plane", (n,)),
        "right": lambda n: ("steiner", (2, n + 1, n * n + n + 1)),
    },
    {
        "name": "affine-plane-is-steiner-2-design",
        "receipt": "Handbook of Combinatorial Designs, Part II (affine planes as S(2,n,n^2))",
        "type": "EQUIVALENCE",
        "range": range(2, 31),
        "left": lambda n: ("plane", (n,)),
        "right": lambda n: ("steiner", (2, n, n * n)),
    },
    {
        # THE BRIDGE TO THE SRG ISLAND — and it was DERIVED, not recalled. A deterministic search over
        # Steiner block-graph parameters against Brouwer's decided set returned 13 exact hits, all EXISTS,
        # with lambda = (v+3)/2 and mu = 9 falling out of the data rather than out of my memory. That is
        # the same seat my impossible Hadamard<->SRG guess occupied, filled correctly by search instead.
        #
        # IMPLICATION, not EQUIVALENCE: the block graph of an STS(v) IS an SRG with these parameters, but
        # an SRG with these parameters need not arise from a Steiner system. Claiming the converse would be
        # the type-collapse the transport algebra exists to forbid.
        "name": "steiner-triple-system-block-graph-is-srg",
        "receipt": "Block graph of S(2,3,v) is SRG(v(v-1)/6, 3(v-3)/2, (v+3)/2, 9) — parameters DERIVED by "
                   "deterministic search, cross-checked against Brouwer's curated table",
        "type": "IMPLICATION",
        "tier": "curated-database",
        "range": range(7, 60),
        "left": lambda v: ("steiner", (2, 3, v)),
        "right": lambda v: ("srg", (v * (v - 1) // 6, 3 * (v - 3) // 2, (v + 3) // 2, 9)),
    },
    {
        # The bridge to the LARGEST marooned island (SRG, 1,482 nodes). Proposed by me from the literature,
        # so it is checked against Brouwer's curated table rather than a kernel proof — and tiered
        # `curated-database` to say exactly that. If the engine finds one disagreement it is discarded.
        "name": "hadamard-matrix-is-hadamard-srg",
        "receipt": "PROPOSED: Hadamard matrix of order 4t <-> SRG(4t-1, 2t-1, t-1, t-1); "
                   "cross-checked against Brouwer's table, NOT kernel-verified",
        "type": "EQUIVALENCE",
        "tier": "curated-database",
        "range": range(1, 40),
        "left": lambda t: ("hadamard", (4 * t,)),
        "right": lambda t: ("srg", (4 * t - 1, 2 * t - 1, t - 1, t - 1)),
    },
]


_SRG = None


def _srg_status(v: int, k: int, lam: int, mu: int) -> str:
    """SRG ground truth from Brouwer's table as loaded into the graph DB (950 decided, 1,481 open).

    The SRG island is the largest marooned blade component (1,482 nodes), and computed_truth has no SRG
    verdict function — so a transport touching it can only be checked against the curated table. That is a
    weaker tier than a kernel proof and is labelled as such; it is not laundered into 'published-proof'."""
    global _SRG
    if _SRG is None:
        import sqlite3
        db = os.path.join(ORACLE, "evidence", "oracle-math.db")
        _SRG = {}
        try:
            con = sqlite3.connect(db)
            for pr, st in con.execute("SELECT params,status FROM facts WHERE family='srg'"):
                _SRG[pr] = "EXISTS" if st.startswith("EXISTS") else st
            con.close()
        except Exception:
            _SRG = {}
    return _SRG.get(f"{v},{k},{lam},{mu}", "UNDECIDED")


def _status(fam: str, params) -> str:
    import computed_truth as ct
    if fam == "srg":
        return _srg_status(*params)
    if fam == "plane":
        return ct.plane_status(params[0])
    if fam == "steiner":
        return ct.steiner_status(*params)
    if fam == "hadamard":
        return ct.hadamard_status(params[0])
    return "UNDECIDED"


def verify(t: dict) -> dict:
    """Run both endpoints through the engine on every instance where both are decided."""
    agree, disagree, overlap = [], [], 0
    for n in t["range"]:
        lf, lp = t["left"](n)
        rf, rp = t["right"](n)
        try:
            ls, rs = _status(lf, lp), _status(rf, rp)
        except Exception:
            continue
        if ls not in ("EXISTS", "NONE") or rs not in ("EXISTS", "NONE"):
            continue
        overlap += 1
        # The violation condition depends on the transport TYPE. An EQUIVALENCE is broken by ANY
        # difference. An IMPLICATION (A exists => B exists) is broken ONLY by A=EXISTS with B=NONE:
        # A=NONE says nothing whatsoever about B, and counting that as a disagreement would reject
        # perfectly sound one-directional transports. Treating the two types alike is the type-collapse
        # the transport algebra exists to forbid.
        bad = (ls != rs) if t["type"] == "EQUIVALENCE" else (ls == "EXISTS" and rs == "NONE")
        (disagree if bad else agree).append({"n": n, "left": f"{_node(lf,lp)}={ls}",
                                             "right": f"{_node(rf,rp)}={rs}"})
    ex = sum(1 for a in agree if a["left"].endswith("EXISTS"))
    no = len(agree) - ex
    ok = overlap >= MIN_OVERLAP and not disagree
    # BALANCE IS REPORTED, ALWAYS. An all-positive overlap means the engine only ever confirmed the map
    # where BOTH sides exist — it never once saw the map correctly predict an impossibility. That is far
    # weaker evidence than "16/16 agree" sounds, and hiding it is how a one-sided check gets mistaken for a
    # two-sided proof. The literature receipt, not this check, is what carries such a transport.
    return {"name": t["name"], "verified": ok, "overlap": overlap, "exists": ex, "none": no,
            "oneSided": no == 0 or ex == 0,
            "agreements": len(agree), "disagreements": disagree,
            "reason": ("verified" if ok else
                       f"only {overlap} decided on both sides (need {MIN_OVERLAP})" if overlap < MIN_OVERLAP
                       else f"{len(disagree)} DISAGREEMENT(S) — one of the two verdict functions is wrong")}


def build(write: bool = True) -> dict:
    results, edges = [], []
    for t in TRANSPORTS:
        v = verify(t)
        results.append(v)
        if not v["verified"]:
            continue
        for n in t["range"]:
            lf, lp = t["left"](n)
            rf, rp = t["right"](n)
            edges.append({"from": _node(lf, lp), "to": _node(rf, rp), "type": t["type"],
                          "tier": t.get("tier", "published-proof"), "source": "handbook-designs",
                          "rule": t["name"], "receipt": t["receipt"]})
    if write and edges:
        os.makedirs(os.path.dirname(OUT), exist_ok=True)
        with io.open(OUT, "w", encoding="utf-8") as fh:
            for e in edges:
                fh.write(json.dumps(e, ensure_ascii=False) + "\n")
    return {"transports": results, "edges": len(edges),
            "verified": sum(1 for r in results if r["verified"])}


def selftest() -> tuple[bool, list]:
    """A deliberately false transport must be REFUSED — the guard has to be shown working, not assumed."""
    bogus = {"name": "bogus", "receipt": "none", "type": "EQUIVALENCE", "range": range(2, 31),
             "left": lambda n: ("plane", (n,)), "right": lambda n: ("steiner", (2, 3, n))}
    v = verify(bogus)
    c = [("refuses_false_transport", not v["verified"]),
         ("reports_disagreements", len(v["disagreements"]) > 0 or v["overlap"] < MIN_OVERLAP)]
    return all(x[1] for x in c), c


if __name__ == "__main__":
    ok, checks = selftest()
    for n, p in checks:
        print(f"  [{'PASS' if p else 'FAIL'}] {n}")
    r = build()
    print(f"\n  transports proposed: {len(r['transports'])}   VERIFIED BY THE ENGINE: {r['verified']}   edges: {r['edges']:,}\n")
    for t in r["transports"]:
        mark = "VERIFIED" if t["verified"] else "REJECTED"
        print(f"  [{mark}] {t['name']}")
        warn = "  [ONE-SIDED: never tested against an impossibility]" if t.get("oneSided") else ""
        print(f"       overlap {t['overlap']} ({t.get('exists',0)} EXISTS / {t.get('none',0)} NONE), "
              f"{t['agreements']} agree — {t['reason']}{warn}")
        for d in t["disagreements"][:6]:
            print(f"       *** n={d['n']}: {d['left']}  vs  {d['right']}")
    if r["edges"]:
        print(f"\n  out: {os.path.relpath(OUT, ORACLE)}")
