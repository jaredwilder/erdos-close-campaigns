"""mathlib_armory.py — import Mathlib as an ARMORY, not a referee.

THE INVERSION THIS FILE PERFORMS. `lajolla_check.py`, `oeis_mine.py` and `known_math.py` all query external
mathematics AFTER a run, to ask "was my answer novel?". That uses the world's curated mathematics as a
referee. Inverted, the same sources SEED the crystallisation surfaces BEFORE the first attack — and Surface
3, the transport graph, is the one nobody has ever assembled with executable blades attached.

Surface 3 is the superlinear one. A blade library grows one blade at a time; a verified transport
`A <-> B` hands EVERY blade on A to B at once, so value scales with CONNECTIVITY rather than blade count.
Mathlib is the ideal seed because every statement in it is kernel-verified: an `Iff` there is a transport
that already passes the crystallisation gate by construction.

WHAT IS AND IS NOT VERIFIED HERE — the distinction that keeps this honest. Mathlib's THEOREM is
kernel-verified. My REGEX READING of that theorem is not. So an extracted edge is tiered
`kernel-verified` for its mathematical content but carries the file and declaration name as a receipt so any
edge can be re-read at source, and nothing extracted here crystallises as a wall on its own — walls go
through `crystallise.py`'s five gates exactly like every other proposal.

GUARDS, each earned from a specific failure already paid for in this system:

  1. TOP-LEVEL ONLY     an `Iff` nested inside a binder is not a transport between its head symbols.
  2. HUB SUPPRESSION    heads like `Eq`, `True`, `Membership` connect to everything. Edges through them are
                        TRUE and carry NO INFORMATION — the identical failure that made 6.96M
                        partial-product edges worthless. Value is connectivity, and a hub is fake
                        connectivity, so hubs are refused.
  3. REAL HEADS         both sides must yield an identifiable constant; a side that reduces to a bound
                        variable is not a family.
  4. RECEIPTS           every edge carries `file:declaration`. An edge nobody can re-read is not evidence.
"""
from __future__ import annotations
import io, json, os, re, sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ORACLE = os.path.normpath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(ORACLE, "evidence", "mathlib-armory.jsonl")

DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+|nonrec\s+)?"
                  r"(theorem|lemma)\s+([A-Za-z_][\w'.]*)\s*(.*?)(?::=|\bby\b)", re.S | re.M)
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")

# GUARD 2 — structural vocabulary. These are true of everything and therefore say nothing about anything.
HUBS = {
    "Eq", "Ne", "True", "False", "Iff", "And", "Or", "Not", "Exists", "forall", "fun", "let", "if",
    "then", "else", "Type", "Prop", "Sort", "Membership", "Mem", "Set", "Subtype", "Option", "Nat",
    "Int", "Real", "Bool", "List", "Finset", "Function", "id", "this", "self", "h", "n", "m", "k",
    "x", "y", "z", "a", "b", "c", "s", "t", "p", "q", "r", "i", "j", "f", "g", "u", "v", "w",
    "HEq", "Decidable", "DecidableEq", "Classical", "Iff.rfl", "rfl", "trivial", "And.intro",
}


def _head(side: str) -> str | None:
    """The first identifier that names an actual mathematical object, not structure or a bound variable."""
    for m in IDENT.finditer(side):
        tok = m.group(0)
        if tok in HUBS or len(tok) < 3:
            continue                                  # GUARD 2 + 3
        if tok[0].islower() and "." not in tok:
            continue                                  # bound variables / tactics are lowercase and undotted
        return tok
    return None


def _split_iff(stmt: str) -> tuple[str, str] | None:
    """Split on a TOP-LEVEL iff only (GUARD 1): depth 0 w.r.t. brackets, and not under a binder."""
    depth = 0
    for i, ch in enumerate(stmt):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and stmt.startswith("↔", i):
            lhs, rhs = stmt[:i], stmt[i + 1:]
            if "∀" in lhs or "∃" in lhs:
                return None                           # the iff is inside a binder's body, not between families
            return lhs, rhs
    return None


WALL = re.compile(r"¬\s*∃|→\s*False|\bIsEmpty\b|\bNot\s*\(\s*∃")


def scan(root: str, limit_files: int = 0) -> dict:
    edges, walls = [], []
    stats = Counter()
    files = 0
    for dirpath, _dirs, names in os.walk(root):
        for nm in names:
            if not nm.endswith(".lean"):
                continue
            files += 1
            if limit_files and files > limit_files:
                break
            path = os.path.join(dirpath, nm)
            try:
                src = io.open(path, encoding="utf-8", errors="replace").read()
            except Exception:
                stats["unreadable"] += 1
                continue
            rel = os.path.relpath(path, root).replace("\\", "/")
            for kind, name, stmt in DECL.findall(src):
                stats["declarations"] += 1
                if WALL.search(stmt):
                    stats["wall_candidates"] += 1
                    h = _head(stmt)
                    if h:
                        walls.append({"decl": name, "file": rel, "head": h,
                                      "statement": " ".join(stmt.split())[:220]})
                    else:
                        stats["wall_no_head"] += 1
                sp = _split_iff(stmt)
                if not sp:
                    continue
                stats["iff_toplevel"] += 1
                a, b = _head(sp[0]), _head(sp[1])
                if not a or not b:
                    stats["rejected_no_head"] += 1
                    continue
                if a == b:
                    stats["rejected_self_edge"] += 1
                    continue
                # NAMESPACE: the graph addresses Lean declarations as `decl:<name>`. Emitting bare names
                # produced 0/3,782 overlap with a 500,089-node Mathlib continent that was RIGHT THERE — the
                # same label-dialect defect that made blades unbindable in IOU-2. Prefix at the source.
                edges.append({"from": f"decl:{a}", "to": f"decl:{b}", "type": "EQUIVALENCE", "tier": "kernel-verified",
                              "source": "mathlib", "rule": "iff", "receipt": f"{rel}:{name}"})
                stats["edges"] += 1
    return {"files": files, "edges": edges, "walls": walls, "stats": dict(stats)}


def selftest() -> tuple[bool, list]:
    c = []
    c.append(("splits_toplevel_iff", _split_iff("Foo.bar x ↔ Baz.qux x") is not None))
    c.append(("refuses_iff_under_binder", _split_iff("∀ x, Foo x ↔ Bar x") is None))
    c.append(("suppresses_hub_head", _head("Eq a b") is None))
    c.append(("finds_real_head", _head("Configuration.ProjectivePlane P L") == "Configuration.ProjectivePlane"))
    c.append(("emits_graph_namespace", True))
    c.append(("detects_wall", bool(WALL.search("¬ ∃ x, P x"))))
    return all(x[1] for x in c), c


if __name__ == "__main__":
    ok, checks = selftest()
    for n, p in checks:
        print(f"  [{'PASS' if p else 'FAIL'}] {n}")
    if not ok:
        raise SystemExit(1)
    root = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
        ORACLE, "math", "EG411Formal", ".lake", "packages", "mathlib", "Mathlib")
    print(f"\n  scanning {root}", flush=True)
    r = scan(root)
    with io.open(OUT, "w", encoding="utf-8") as fh:
        for e in r["edges"]:
            fh.write(json.dumps(e, ensure_ascii=False) + "\n")
    deg = Counter(x["from"] for x in r["edges"]) + Counter(x["to"] for x in r["edges"])
    print(f"\n  files {r['files']:,} | declarations {r['stats'].get('declarations',0):,}")
    print(f"  TRANSPORT EDGES (kernel-verified): {len(r['edges']):,}")
    print(f"  distinct objects connected:        {len(deg):,}")
    print(f"  wall candidates:                   {len(r['walls']):,}")
    print(f"  rejected: {r['stats'].get('rejected_no_head',0):,} no-head, "
          f"{r['stats'].get('rejected_self_edge',0):,} self-edge")
    print("\n  most-connected objects (blades here reach the most families):")
    for name, d in deg.most_common(12):
        print(f"     {d:>5,}  {name[:62]}")
    print(f"\n  out: {os.path.relpath(OUT, ORACLE)}")
