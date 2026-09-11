"""build_db.py — the relational core. Turns the flat evidence pile into a queryable machine.

Everything imported so far lives in append-only JSONL: 7.4M edges, 2,295 targets, SRG facts, corpora.
A pile is not a machine. This builds the SQLite store the Oracle actually queries:

  nodes(id, ns, label, component, degree)      — every object, its namespace, its component
  edges(src, dst, type, tier, source, rule)    — the typed transport graph
  targets(target_id, source, decl, kind, statement)   — formalized open problems
  facts(family, params, status, source, tier)  — decided ground truth (Brouwer SRG, …)
  components(component, size)                  — materialized connectivity

Composability is enforced at query time, not at write time: ANALOGY edges are stored but excluded from
reachability, exactly as the transport algebra requires.
"""
from __future__ import annotations
import io, json, os, sqlite3, sys, time

# NOTE: never reassign sys.stdout at import time — the wrapper closes the real stdout when it is
# garbage-collected, breaking every module that imports this one. Encoding is the caller's job.
HERE = os.path.dirname(os.path.abspath(__file__))
ORACLE = os.path.normpath(os.path.join(HERE, "..", ".."))
EV = os.path.join(ORACLE, "evidence")
DB = os.path.join(EV, "oracle-math.db")

EDGE_FILES = [os.path.join(EV, "transport-graph", "edges.jsonl"),
              os.path.join(EV, "transport-graph", "mathlib-depgraph.jsonl"),
              # Surface 3 seed: kernel-verified `Iff` transports mined from Mathlib source. Dependency
              # edges say "A is used to prove B"; these say "A and B are the SAME question", which is the
              # only edge type that hands one family's blades to another.
              os.path.join(EV, "transport-graph", "mathlib-armory.jsonl"),
              # The island-merge seed: classical design-theory equivalences, each VERIFIED by running both
              # endpoints through computed_truth on every instance decided on both sides. These are the only
              # edges that touch the blade-bound nodes, which sit outside the kernel continent entirely.
              os.path.join(EV, "transport-graph", "design-transports.jsonl"),
              # Surface 1 + the machine's own output. The covering firehose proved 69 exact values and
              # none were in the graph — a compounding engine that drops its own results is not compounding.
              os.path.join(EV, "transport-graph", "armory-facts.jsonl")]


def ns_of(x: str) -> str:
    if x.startswith("decl:"):
        return "mathlib"
    if len(x) >= 7 and x[0] == "A" and x[1:7].isdigit():
        return "oeis"
    for p, n in (("gc_", "isgci"), ("class:", "isgci"), ("problem:", "isgci"), ("param:", "isgci"),
                 ("speed:", "isgci"), ("coll:", "findstat"), ("stat:", "findstat"),
                 ("srg:", "brouwer"), ("status:", "brouwer"), ("msc:", "msc"),
                 ("mardi:", "mardi"), ("mathlib-area:", "mathlib"),
                 ("counterexamples:", "mathlib"), ("archive:", "mathlib")):
        if x.startswith(p):
            return n
    if x and x[0] == "P" and x[1:].split("=")[0].isdigit():
        return "pibase"
    if x and x[0] == "S" and x[1:].split("=")[0].isdigit():
        return "pibase"
    return "other"


def build() -> None:
    if os.path.exists(DB):
        os.remove(DB)
    con = sqlite3.connect(DB)
    con.executescript("""
        PRAGMA journal_mode=OFF; PRAGMA synchronous=OFF;
        CREATE TABLE nodes(id INTEGER PRIMARY KEY, label TEXT UNIQUE, ns TEXT, component INTEGER, degree INTEGER DEFAULT 0);
        CREATE TABLE edges(src INTEGER, dst INTEGER, type TEXT, tier TEXT, source TEXT, rule TEXT);
        CREATE TABLE targets(target_id TEXT PRIMARY KEY, source TEXT, decl TEXT, kind TEXT, statement TEXT);
        CREATE TABLE facts(family TEXT, params TEXT, status TEXT, source TEXT, tier TEXT);
        CREATE TABLE components(component INTEGER PRIMARY KEY, size INTEGER);
    """)
    ids: dict[str, int] = {}
    par: list[int] = []

    def nid(lbl: str) -> int:
        v = ids.get(lbl)
        if v is None:
            v = len(par); ids[lbl] = v; par.append(v)
        return v

    def find(x: int) -> int:
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x

    t0 = time.time()
    edges = []
    for f in EDGE_FILES:
        if not os.path.exists(f):
            continue
        for line in open(f, encoding="utf-8"):
            try:
                d = json.loads(line)
            except Exception:
                continue
            a, b = nid(d["from"]), nid(d["to"])
            edges.append((a, b, d["type"], d.get("tier", ""), d.get("source", ""), d.get("rule", "")))
            if d["type"] != "ANALOGY":                 # algebra: ANALOGY never joins components
                ra, rb = find(a), find(b)
                if ra != rb:
                    par[ra] = rb
    print(f"  edges loaded {len(edges):,}  nodes {len(ids):,}  ({time.time()-t0:.0f}s)", flush=True)

    con.executemany("INSERT INTO edges VALUES (?,?,?,?,?,?)", edges)
    con.executemany("INSERT INTO nodes(id,label,ns,component) VALUES (?,?,?,?)",
                    ((i, lbl, ns_of(lbl), find(i)) for lbl, i in ids.items()))
    con.executescript("""
        CREATE INDEX ix_e_src ON edges(src); CREATE INDEX ix_e_dst ON edges(dst);
        CREATE INDEX ix_e_type ON edges(type); CREATE INDEX ix_e_tier ON edges(tier);
        CREATE INDEX ix_e_source ON edges(source);
        CREATE INDEX ix_n_ns ON nodes(ns); CREATE INDEX ix_n_comp ON nodes(component);
    """)
    con.execute("INSERT INTO components SELECT component, COUNT(*) FROM nodes GROUP BY component")
    con.execute("""UPDATE nodes SET degree = (SELECT COUNT(*) FROM edges e
                   WHERE e.src=nodes.id OR e.dst=nodes.id)
                   WHERE id IN (SELECT src FROM edges UNION SELECT dst FROM edges)""")

    tf = os.path.join(EV, "formal-conjectures", "targets.jsonl")
    if os.path.exists(tf):
        rows = []
        for line in open(tf, encoding="utf-8"):
            d = json.loads(line)
            rows.append((d["targetId"], d.get("source"), d.get("decl"), d.get("kind"), d.get("statement")))
        con.executemany("INSERT OR REPLACE INTO targets VALUES (?,?,?,?,?)", rows)
        print(f"  targets {len(rows):,}", flush=True)

    sf = os.path.join(EV, "brouwer", "srg-parameters.json")
    if os.path.exists(sf):
        MAP = {"?": "OPEN", "+": "EXISTS", "-": "NONE", "!": "EXISTS_UNIQUE"}
        rows = []
        for r in json.load(open(sf, encoding="utf-8")):
            mk = r["marker"].strip()
            st = MAP.get(mk) or ("EXISTS_UNIQUE" if mk.endswith("!") else None)
            if st:
                rows.append(("srg", f"{r['v']},{r['k']},{r['lambda']},{r['mu']}", st, "brouwer", "curated-database"))
        con.executemany("INSERT INTO facts VALUES (?,?,?,?,?)", rows)
        con.execute("CREATE INDEX ix_f ON facts(family,status)")
        print(f"  facts {len(rows):,}", flush=True)

    con.commit(); con.close()
    print(f"  -> {os.path.relpath(DB, ORACLE)}  ({os.path.getsize(DB)/1e6:.0f} MB)  in {time.time()-t0:.0f}s")


def _rebind():
    """A rebuild DROPS every table it does not create, and `node_blade` is owned by blades.py — so a plain
    rebuild silently destroys the blade bindings and the selector then reports zero schedulable targets with
    no error anywhere. Rebinding here makes the invariant structural instead of a thing to remember."""
    try:
        import blades
        blades.install()
        print("  rebound blades (node_blade restored)")
    except Exception as exc:
        print(f"  WARNING: blade rebind failed ({type(exc).__name__}: {exc}) — run blades.py manually")


if __name__ == "__main__":
    build()
    _rebind()
