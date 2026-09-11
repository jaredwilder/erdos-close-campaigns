#!/usr/bin/env python3
"""Falsifier + sharpness receipt for the Erdos-143 packing theorem.

THE CLAIM UNDER ATTACK (kernel-checked in E143.lean as `ncard_le_half`):

    A subset of (1, inf) with   |k*x - y| >= 1  for all x != y in A, all int k >= 1
    satisfies                   |A cap (1, Y)| <= Y/2 + 1   for every Y > 0.

FALSIFY: MEASURE  max over all constructed well-separated sets S of
         ( |S cap (1,Y)| - (Y/2 + 1) ).
         THE CLAIM IS DEAD IF that maximum is > 0 for any constructed S.

SHARPNESS: MEASURE  max over N of  |A_N cap (1,2N)| / (2N)  where
           A_N = {N, N+1, ..., 2N-1}.  Recorded value must be exactly 1/2.

Everything is exact integer arithmetic on the lattice (1/q)Z: an element is the
integer X standing for the real X/q, and the separation condition
|k*(X/q) - (Y/q)| >= 1 becomes the integer condition |k*X - Y| >= q.

Stdlib only.  No LLM, no network.
"""
from __future__ import annotations

import json
import random
import sys
from fractions import Fraction


def separated(pool: list[int], q: int, cap: int) -> bool:
    """Exhaustively verify the separation predicate on the scaled set `pool`.

    `cap` is an upper bound on the scaled values; k only needs to range while
    k*X - Y can still be within q of zero, i.e. k <= (cap + q) / X.
    """
    for x in pool:
        for y in pool:
            if x == y:
                continue
            kmax = (cap + q) // x + 1
            for k in range(1, kmax + 1):
                if abs(k * x - y) < q:
                    return False
    return True


def greedy(cands: list[int], q: int, cap: int) -> list[int]:
    """Greedily grow a well-separated set from `cands` in the given order."""
    chosen: list[int] = []
    for c in cands:
        ok = True
        for s in chosen:
            kmax = (cap + q) // min(c, s) + 1
            for k in range(1, kmax + 1):
                if abs(k * c - s) < q or abs(k * s - c) < q:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            chosen.append(c)
    return chosen


def run() -> dict:
    out: dict = {"arms": []}

    # ---- ARM 1: sharpness witness A_N = {N,...,2N-1}, exhaustively verified.
    sharp = []
    worst_ratio = Fraction(0)
    for N in range(2, 121):
        pool = list(range(N, 2 * N))          # q = 1, so these ARE the reals
        assert separated(pool, 1, 2 * N), f"A_{N} is not well separated"
        ratio = Fraction(len(pool), 2 * N)     # |A cap (1,2N)| / (2N)
        worst_ratio = max(worst_ratio, ratio)
        sharp.append([N, len(pool), str(ratio)])
    out["arms"].append({
        "arm": "SHARPNESS",
        "family": "A_N = {N,...,2N-1}, q=1, N in [2,120]",
        "verified_well_separated": True,
        "max_count_over_2N": str(worst_ratio),
        "note": "equals 1/2 exactly, so the constant 1/2 in the theorem is optimal",
        "sample": sharp[:5] + sharp[-3:],
    })

    # ---- ARM 2: falsifier.  Try hard to build a well-separated set that
    #      exceeds Y/2 + 1 on the lattice (1/q)Z, over many orders and q.
    rng = random.Random(20260905)
    worst_excess = Fraction(-10**9)
    worst_cfg = None
    trials = 0
    for q in (1, 2, 3, 4, 6):
        for Ynum in (12, 20, 30, 40, 60):
            cap = q * Ynum                     # scaled Y
            universe = list(range(q + 1, cap))  # reals strictly between 1 and Y
            if not universe:
                continue
            orders = [
                list(universe),
                list(reversed(universe)),
            ]
            for _ in range(6):
                shuffled = list(universe)
                rng.shuffle(shuffled)
                orders.append(shuffled)
            for order in orders:
                trials += 1
                S = greedy(order, q, cap)
                assert separated(S, q, cap), "greedy produced a non-separated set"
                excess = Fraction(len(S)) - (Fraction(Ynum, 2) + 1)
                if excess > worst_excess:
                    worst_excess = excess
                    worst_cfg = {
                        "q": q, "Y": Ynum, "count": len(S),
                        "bound": str(Fraction(Ynum, 2) + 1),
                        "set_scaled": S[:40],
                    }
    out["arms"].append({
        "arm": "FALSIFIER",
        "measure": "max over constructed well-separated sets of |S cap (1,Y)| - (Y/2 + 1)",
        "dead_if": "> 0",
        "trials": trials,
        "max_excess": str(worst_excess),
        "verdict": "KILLED" if worst_excess > 0 else "SURVIVED",
        "worst_config": worst_cfg,
    })

    # ---- ARM 3: the two-scale corollary, sanity.  |A cap (1,Y)| <= Y/2 + 1
    #      implies sum_{a in A, a < n} 1/a <= (1/2) log n + O(1).  Recorded as
    #      a numeric consistency check on the sharpness family only.
    out["arms"].append({
        "arm": "NOTE",
        "text": "Arm 3 intentionally absent: the log-sum corollary is analytic, "
                "not a finite computation, and is NOT receipted here.",
    })
    return out


if __name__ == "__main__":
    res = run()
    json.dump(res, sys.stdout, indent=1)
    sys.stdout.write("\n")
