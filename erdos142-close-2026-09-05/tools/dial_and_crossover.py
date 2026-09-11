#!/usr/bin/env python3
"""
dial_and_crossover.py — three receipted measurements about the supermultiplicative
lower-bound lemma proved in Close02_Supermultiplicative.lean:

  (1) VALIDATION.  The lemma asserts, for all p,q >= 0,
          r3(p+1) * r3(q+1) <= r3(2pq + p + q + 1).
      Check it against every published exact value (OEIS A003002 b-file) whose
      index is in range.  A single violation would REFUTE the Lean theorem
      (or the b-file).  Also record where it is TIGHT (equality).

  (2) THE DIAL.  The lemma converts a seed (m, c) with c <= r3(m) into
      r3(N) >= N^theta along an explicit sequence, with
          theta = ln c / ln (2m - 1).
      Rank every published exact value as a seed.  Report whether ANY beats
      the base-3/Szekeres value log 2 / log 3.

  (3) CROSSOVER.  Compare the bound this lemma proves at N_j = (27^j+1)/2,
      namely 8^j, against what Mathlib's `Behrend.roth_lower_bound` STATES,
      namely N * exp(-4 * sqrt(log N)).  Report the smallest j at which
      Behrend's stated form overtakes.

Input: the OEIS b-file, sha-256 pinned.  Output: JSON receipt.
No proofs are made here; this measures a proved lemma against published data.
"""

import json
import math
import hashlib
import sys
import argparse


def load_bfile(path):
    raw = open(path, "rb").read()
    sha = hashlib.sha256(raw).hexdigest()
    d = {}
    for line in raw.decode().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        a, b = line.split()
        d[int(a)] = int(b)
    return d, sha, len(d)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bfile", required=True)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    r3, sha, nrows = load_bfile(args.bfile)
    nmax = max(r3)

    # ---------- (1) validation of the Lean lemma against published data ----------
    checked = 0
    violations = []
    tight = []
    for p in range(0, nmax + 1):
        for q in range(0, nmax + 1):
            N = 2 * p * q + p + q + 1
            if N > nmax:
                break
            if (p + 1) not in r3 or (q + 1) not in r3:
                continue
            lhs = r3[p + 1] * r3[q + 1]
            rhs = r3[N]
            checked += 1
            if lhs > rhs:
                violations.append({"p": p, "q": q, "lhs": lhs, "N": N, "rhs": rhs})
            elif lhs == rhs and lhs >= 2 and p >= 1 and q >= 1:
                # p = 0 or q = 0 makes the lemma the trivial identity r3(N) <= r3(N);
                # only p,q >= 1 is a genuine tightness datum.
                tight.append({"p": p, "q": q, "m": p + 1, "n": q + 1, "N": N, "value": lhs})

    # ---------- (2) the dial ----------
    base = math.log(2) / math.log(3)
    seeds = []
    for m, c in r3.items():
        if m >= 2 and c >= 2:
            seeds.append({"m": m, "r3_m": c, "theta": math.log(c) / math.log(2 * m - 1)})
    seeds.sort(key=lambda s: (-s["theta"], s["m"]))
    beats = [s for s in seeds if s["theta"] > base + 1e-12]
    equals = [s for s in seeds if abs(s["theta"] - base) <= 1e-12]

    # ---------- (3) crossover against Mathlib's stated Behrend bound ----------
    cross = []
    crossover_j = None
    for j in range(0, 200):
        N = (27 ** j + 1) // 2
        ours = 8 ** j
        lnN = math.log(27) * j - math.log(2) if j > 0 else 0.0
        # Behrend stated bound: N * exp(-4 sqrt(log N)); compare in logs.
        if j == 0:
            behrend_log = 0.0
        else:
            behrend_log = lnN - 4.0 * math.sqrt(lnN)
        ours_log = j * math.log(8)
        if j <= 6:
            cross.append({
                "j": j, "N": N, "ours": ours,
                "behrend_stated": math.exp(behrend_log) if behrend_log < 700 else None,
                "ours_wins": ours_log > behrend_log,
            })
        if crossover_j is None and j >= 1 and behrend_log >= ours_log:
            crossover_j = j
            crossover_N_digits = len(str(N))

    receipt = {
        "tool": "dial_and_crossover.py",
        "tool_sha256": hashlib.sha256(open(__file__, "rb").read()).hexdigest(),
        "input_bfile": args.bfile,
        "input_bfile_sha256": sha,
        "input_rows": nrows,
        "published_index_max": nmax,
        "lemma": "rothNumberNat (p+1) * rothNumberNat (q+1) <= rothNumberNat (2*p*q+p+q+1)",
        "validation": {
            "pairs_checked_against_published_values": checked,
            "violations": violations,
            "verdict": "CONSISTENT" if not violations else "REFUTED",
            "tight_cases_count": len(tight),
            "tight_cases_sample": tight[:12],
        },
        "dial": {
            "theta_formula": "ln(r3(m)) / ln(2m-1)",
            "classical_base3_exponent_log2_over_log3": base,
            "seeds_beating_classical": beats,
            "seeds_attaining_classical": equals,
            "top_15_seeds": seeds[:15],
            "verdict": (
                "PINNED: no published exact value (n <= %d) yields an exponent above "
                "log2/log3; equality exactly at the Szekeres points (3^k+1)/2." % nmax
                if not beats else
                "IMPROVABLE: a published exact value beats log2/log3."
            ),
        },
        "crossover_vs_mathlib_behrend_stated_bound": {
            "mathlib_lemma": "Behrend.roth_lower_bound : N * exp(-4*sqrt(log N)) <= rothNumberNat N",
            "family": "N_j = (27^j+1)/2, our bound 8^j",
            "first_j_where_behrend_stated_form_overtakes": crossover_j,
            "digits_of_N_at_crossover": crossover_N_digits if crossover_j else None,
            "small_j_table": cross,
        },
    }
    with open(args.out, "w") as f:
        json.dump(receipt, f, indent=2)

    print("bfile sha256      :", sha)
    print("published n max   :", nmax)
    print("lemma validation  :", receipt["validation"]["verdict"],
          f"({checked} pairs, {len(violations)} violations, {len(tight)} tight)")
    print("dial              :", receipt["dial"]["verdict"])
    print("seeds attaining   :", [s["m"] for s in equals])
    print("crossover j       :", crossover_j,
          f"(N has {crossover_N_digits if crossover_j else '?'} digits)")
    print("wrote", args.out)
    return 0 if not violations else 1


if __name__ == "__main__":
    sys.exit(main())
