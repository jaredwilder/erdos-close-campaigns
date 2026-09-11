"""armory.py — the machine's own view of its assembly. One manifest, every source, measured not assumed.

THE PROBLEM THIS SOLVES. The doctrine names a dozen curated databases whose assembly into one graph with
executable blades IS the invention. Nothing measured which of them are actually there. The graph reports
7.4M edges and looks assembled; the disk tells a different story:

    houseofgraphs/graphs.json   1,600 entries that are BARE INTEGERS — a degenerate pull, no structure
    polydb/collections.json     an empty list — the pull failed and nothing said so
    lmfdb/ec_curves.json        500 real elliptic curves, structured — and imported nowhere

A big edge count from three healthy sources hides seven missing ones. So this file asks every source the
same four questions and answers them from the filesystem and the database, never from a config claiming
what ought to be there:

    PRESENT?   does the corpus exist on disk
    REAL?      does it carry structured records, or is it a stub/degenerate pull
    IMPORTED?  do edges with that source actually appear in the graph
    SURFACE?   which crystallisation surface it feeds — 1 ground truth, 2 falsifier, 3 transport

WHY THE `REAL?` COLUMN IS THE LOAD-BEARING ONE. A file that exists and parses looks identical to a working
import until someone reads its contents. `houseofgraphs` passes "present" and "parses" and is still
useless: a list of integers cannot be a counterexample corpus. Counting files, or trusting a manifest,
would have scored it as done. Only reading the records catches it.

SURFACE 2 IS THE UNTOUCHED ONE. Ground truth (1) and transports (3) both have real imports. The falsifier
corpus — banked counterexamples that kill whole classes of proposal before a solver runs — has NONE, and
the one source meant to supply it is the degenerate pull above. That is the honest headline of the assembly.
"""
from __future__ import annotations
import io, json, os, sqlite3, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ORACLE = os.path.normpath(os.path.join(HERE, "..", ".."))
EV = os.path.join(ORACLE, "evidence")
DB = os.path.join(EV, "oracle-math.db")

# Every source the doctrine names, with where it should live and what it is FOR.
SOURCES = [
    # key            path (relative to evidence/)              surface  what it gives
    ("mathlib",      "transport-graph/mathlib-armory.jsonl",    3, "kernel-verified Iff transports"),
    ("mathlib-depgraph", "transport-graph/mathlib-depgraph.jsonl", 3, "declaration dependency edges"),
    ("oeis",         "oeis/stripped.gz",                        3, "sequence cross-references / formulas"),
    ("brouwer-srg",  "brouwer",                                 1, "SRG parameter table with status"),
    ("isgci",        "isgci",                                   3, "graph-class inclusions + inference"),
    ("pibase",       "pibase",                                  2, "spaces x properties, deduction engine"),
    ("findstat",     "findstat",                                3, "combinatorial statistics + maps"),
    ("handbook-designs", "transport-graph/design-transports.jsonl", 3, "classical design equivalences"),
    ("formal-conjectures", "formal-conjectures",                1, "Lean-formalised open conjectures"),
    ("houseofgraphs", "houseofgraphs/graphs.json",              2, "curated COUNTEREXAMPLES + invariants"),
    ("falsifier",    "falsifier-corpus.json",                   2, "the machine's OWN banked refusals"),
    ("lmfdb",        "lmfdb/ec_curves.json",                    1, "elliptic curves, modular forms"),
    ("polydb",       "polydb/collections.json",                 1, "polytope database"),
    ("covering-firehose", "covering-firehose.jsonl",            1, "our OWN proven covering numbers"),
    ("mardi",        "mardi",                                   3, "mathematical research data interlink"),
]

SURFACE_NAME = {1: "ground truth", 2: "FALSIFIER", 3: "transport"}


def _records(path: str) -> tuple[int, str]:
    """(count, verdict). Reads actual records — 'exists and parses' is not 'real'."""
    if not os.path.exists(path):
        return 0, "absent"
    if os.path.isdir(path):
        n = sum(1 for _d, _s, fs in os.walk(path) for f in fs)
        return n, ("real" if n else "empty-dir")
    if path.endswith(".gz"):
        try:
            import gzip
            with gzip.open(path, "rt", encoding="utf-8", errors="replace") as fh:
                n = sum(1 for _ in fh)
            return n, ("real" if n > 10 else "stub")
        except Exception:
            return 0, "unreadable"
    if path.endswith(".jsonl"):
        try:
            n = sum(1 for _ in io.open(path, encoding="utf-8"))
            return n, ("real" if n > 10 else "stub")
        except Exception:
            return 0, "unreadable"
    try:
        d = json.load(io.open(path, encoding="utf-8"))
    except Exception:
        return 0, "unreadable"
    if isinstance(d, list):
        if not d:
            return 0, "EMPTY — pull failed"
        # A corpus of scalars is not a corpus. This is the check that catches a pull which "worked".
        if not isinstance(d[0], (dict, list)):
            return len(d), "DEGENERATE — scalars, no structure"
        return len(d), "real"
    if isinstance(d, dict):
        return len(d), ("real" if d else "EMPTY — pull failed")
    return 0, "unreadable"


def _falsifier_classes(key: str) -> int:
    """Surface 2's contribution is executable refutation classes actually consulted by the ladder."""
    if key == "falsifier":
        try:
            import importlib.util
            spec = importlib.util.spec_from_file_location(
                "fz", os.path.join(ORACLE, "kbk", "engine", "falsifier.py"))
            m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
            return len(m.CLASSES)
        except Exception:
            return 0
    if key == "pibase":
        con = sqlite3.connect(DB) if os.path.exists(DB) else None
        if not con:
            return 0
        try:
            n = con.execute("SELECT COUNT(*) FROM edges WHERE source LIKE 'pibase%'").fetchone()[0]
        except Exception:
            n = 0
        con.close()
        return n
    return 0


def audit() -> dict:
    imported = {}
    if os.path.exists(DB):
        con = sqlite3.connect(DB)
        try:
            imported = dict(con.execute("SELECT source, COUNT(*) FROM edges GROUP BY source"))
        except Exception:
            pass
        con.close()
    rows = []
    for key, rel, surface, what in SOURCES:
        n, verdict = _records(os.path.join(EV, rel))
        edges = sum(v for k, v in imported.items() if k and k.startswith(key))
        # USABILITY IS PER-SURFACE. Scoring every source by edge count was wrong: a falsifier corpus
        # contributes REFUSALS, not edges, so measuring it by edges marked a working Surface-2 store as
        # "not contributing". Each surface is asked for the thing it actually produces.
        if surface == 2:
            contrib = _falsifier_classes(key)
            unit = "classes"
        else:
            contrib, unit = edges, "edges"
        rows.append({"source": key, "surface": surface, "records": n, "state": verdict,
                     "contributes": contrib, "unit": unit, "edgesInGraph": edges, "gives": what,
                     "usable": verdict == "real" and contrib > 0})
    return {"sources": rows,
            "usable": sum(1 for r in rows if r["usable"]),
            "total": len(rows),
            "bySurface": {s: sum(1 for r in rows if r["surface"] == s and r["usable"])
                          for s in (1, 2, 3)}}


if __name__ == "__main__":
    a = audit()
    print("=" * 96)
    print("  ARMORY ASSEMBLY AUDIT — measured from disk + database, not from any manifest")
    print("=" * 96)
    print(f"\n  {'source':<20s}{'surf':<12s}{'records':>10s}   {'state':<26s}{'edges in graph':>15s}")
    print("  " + "-" * 92)
    for r in sorted(a["sources"], key=lambda x: (x["surface"], -x["contributes"])):
        flag = "" if r["usable"] else "   <-- NOT CONTRIBUTING"
        print(f"  {r['source']:<20s}{SURFACE_NAME[r['surface']]:<12s}{r['records']:>10,}   "
              f"{r['state']:<26s}{r['contributes']:>10,} {r['unit']:<8s}{flag}")
    print(f"\n  USABLE SOURCES: {a['usable']} of {a['total']}")
    for s in (1, 2, 3):
        tot = sum(1 for r in a["sources"] if r["surface"] == s)
        print(f"     surface {s} ({SURFACE_NAME[s]:<12s}): {a['bySurface'][s]} of {tot} usable")
    if not a["bySurface"][2]:
        print("\n  *** SURFACE 2 (FALSIFIER) IS EMPTY. Not one banked counterexample. Every refuted")
        print("      proposal is being forgotten, so the same class gets re-proposed forever and")
        print("      'proposals per newly-decided case' can never fall. This is the assembly's hole. ***")
    json.dump(a, io.open(os.path.join(EV, "armory-audit.json"), "w", encoding="utf-8"), indent=1)
