#!/usr/bin/env python3
"""
r3_exact.py — independent $0 deterministic exact solver for r_3(n) (OEIS A003002).

r_3(n) = largest cardinality of a subset of {1,...,n} containing no non-trivial
3-term arithmetic progression.  (Equivalently Mathlib's `rothNumberNat n`, which
uses the translate {0,...,n-1}.)

Method: depth-first branch and bound over the ground set in increasing order.
At each node we hold a partial 3AP-free set S and a frontier index i.  Bound:
|S| + (n - i + 1) <= best  =>  prune.  Extension legality is checked directly
against S (x completes a 3-AP with two chosen elements iff 2*x - s in S for some
s in S with 2*x - s != x, or x is the midpoint of two chosen elements).

NOTHING here is a proof.  It is a tool run whose output is (a) cross-checked
against the published OEIS A003002 b-file values embedded below, and (b) used
only to produce WITNESSES, which are then re-verified independently by the Lean
kernel.  Upper bounds asserted by this script are UNPROVED in the formal sense.

Usage:  python r3_exact.py --nmax 40 --out receipt.json
"""

import argparse
import json
import sys
import time
import hashlib
import platform

# OEIS A003002, a(n) for n = 0..64 (a(0)=0).  Source: OEIS b-file A003002.
# Used ONLY as an external cross-check of this solver, never as an input.
A003002 = [
    0, 1, 2, 2, 3, 4, 4, 4, 4, 5, 5, 6, 6, 7, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9,
    10, 10, 11, 11, 11, 12, 12, 13, 13, 13, 13, 14, 14, 14, 14, 14, 15, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19,
    20, 20, 20, 20, 20,
]


def is_ap3_free(s):
    """Direct O(k^3) re-verification, deliberately naive."""
    lst = sorted(s)
    st = set(lst)
    for a in lst:
        for b in lst:
            if a == b:
                continue
            c = 2 * b - a
            if c != a and c in st:
                return False
    return True


def r3(n):
    """Exact r_3(n) with an extremal witness, by DFS branch and bound."""
    if n == 0:
        return 0, []
    best = 0
    best_set = []
    chosen = []
    chosen_set = set()

    def legal(x):
        # x must not close a 3-AP with two already chosen elements.
        for s in chosen:
            # x is the largest term:  s, (s+x)/2, x
            if (s + x) % 2 == 0 and (s + x) // 2 in chosen_set and (s + x) // 2 != x:
                return False
            # x is the middle term: cannot happen, all chosen are < x
            # x is the right term of s, m, x already covered above.
            # x with two smaller s1 < s2 where 2*s2 - s1 == x
            if 2 * s - x in chosen_set and 2 * s - x != s:
                return False
        return True

    def dfs(i):
        nonlocal best, best_set
        if len(chosen) + (n - i + 1) <= best:
            return
        if i > n:
            if len(chosen) > best:
                best = len(chosen)
                best_set = list(chosen)
            return
        # branch: take i
        if legal(i):
            chosen.append(i)
            chosen_set.add(i)
            if len(chosen) > best:
                best = len(chosen)
                best_set = list(chosen)
            dfs(i + 1)
            chosen.pop()
            chosen_set.discard(i)
        # branch: skip i
        dfs(i + 1)

    sys.setrecursionlimit(10000)
    dfs(1)
    return best, best_set


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=40)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    rows = []
    t_all = time.time()
    for n in range(0, args.nmax + 1):
        t0 = time.time()
        v, w = r3(n)
        dt = time.time() - t0
        assert is_ap3_free(w), f"witness for n={n} is NOT 3AP-free"
        assert all(1 <= x <= n for x in w)
        assert len(w) == v
        oeis = A003002[n] if n < len(A003002) else None
        rows.append({
            "n": n,
            "r3": v,
            "witness": w,
            "seconds": round(dt, 4),
            "oeis_A003002": oeis,
            "matches_oeis": (oeis is None or oeis == v),
        })
        print(f"n={n:3d}  r3={v:3d}  oeis={oeis}  match={oeis is None or oeis==v}  {dt:8.3f}s",
              flush=True)

    mismatches = [r for r in rows if not r["matches_oeis"]]
    total = time.time() - t_all

    # density-seed ranking: theta = ln(r3(m)) / ln(2m-1) is the exponent the
    # supermultiplicative product lemma delivers from the seed m.
    import math
    seeds = []
    for r in rows:
        m, c = r["n"], r["r3"]
        if m >= 2 and c >= 2:
            seeds.append({"m": m, "r3": c, "theta": math.log(c) / math.log(2 * m - 1)})
    seeds.sort(key=lambda d: -d["theta"])

    receipt = {
        "tool": "r3_exact.py",
        "tool_sha256": hashlib.sha256(open(__file__, "rb").read()).hexdigest(),
        "python": sys.version.split()[0],
        "platform": platform.platform(),
        "nmax": args.nmax,
        "wall_seconds": round(total, 3),
        "rows": rows,
        "oeis_mismatches": mismatches,
        "oeis_crosscheck": "PASS" if not mismatches else "FAIL",
        "best_product_seeds_by_theta": seeds[:15],
        "status_note": (
            "Upper bounds here are TOOL OUTPUT, not proofs. Only the witnesses "
            "(lower bounds) are re-checked by the Lean kernel downstream."
        ),
    }
    if args.out:
        with open(args.out, "w") as f:
            json.dump(receipt, f, indent=2)
        print(f"\nwrote {args.out}")
    print(f"\nOEIS cross-check: {receipt['oeis_crosscheck']}  ({len(mismatches)} mismatches)")
    print("top product seeds (theta = ln r3(m) / ln(2m-1)):")
    for s in seeds[:10]:
        print(f"   m={s['m']:3d} r3={s['r3']:3d} theta={s['theta']:.5f}")


if __name__ == "__main__":
    main()
