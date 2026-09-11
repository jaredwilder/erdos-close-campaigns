#!/usr/bin/env python3
"""THE TWO-WALL ENGINE — one general decider, no per-target hand-scripts.

You hand it a target (a combinatorial existence question) and a single time budget. It runs the
two-wall convergence loop ITSELF: the N-wall lattice (necessary obstructions, weak->strong) then the
S-wall constructions (sufficient witnesses), and emits ONE honest verdict + receipt:

    REFUTED  = an N-wall fired, or a construction search proved UNSAT  (provably non-existent)
    EXISTS   = a construction produced an independently-verified witness (provably exists)
    FRONTIER = survived every necessary wall, no construction landed in budget (honestly open)

This is the thumb coming off the scale. No target is hardcoded; the engine dispatches on the target
family and composes the already-validated blades (divisibility, Bruck-Ryser, Krein/absolute,
CP-SAT exact cover). Point it at steiner:4,5,15 or srg:28,9,0,4 or symmetric:43,7,1 — same engine.

$0, deterministic, zero-LLM. Every number comes from a tool (CP-SAT / exact arithmetic), never asserted.
Before any target verdict is trusted, main() runs a GROUND-TRUTH validation set; a red validation
invalidates the run (anti-facade: the engine must reproduce known math before we believe a new answer).
"""
from __future__ import annotations
import hashlib, json, sys
from datetime import datetime, timezone
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "oracle" / "scripts"))
from frontier_math_printer.tdesign_divisibility import steiner_divisible          # noqa: E402
from frontier_math_printer.invariant_engine import symmetric_design_feasible      # noqa: E402
from frontier_math_printer.srg_krein_wall import (                                # noqa: E402
    srg_eigendata, krein_ok, absolute_ok, counting_ok)
from frontier_math_printer.steiner_tower_attack import steiner_exact_cover        # noqa: E402

OUT = ROOT / "oracle" / "runtime" / "state" / "frontier-math-two-wall-engine.json"
MAX_BLOCKS = 300_000   # size guard: refuse to enumerate an exact cover larger than this (stay honest, don't OOM)


# ----------------------------------------------------------------------------- family deciders
def decide_steiner(t, k, v, budget):
    """S(t,k,v): divisibility N-wall, then CP-SAT exact cover (SAT=exists / UNSAT=refuted),
    then a derived-child refutation fallback (S(t-1,k-1,v-1) UNSAT => parent refuted)."""
    trace = []

    # N-wall 1 — elementary divisibility (instant, necessary)
    ok, bad = steiner_divisible(t, k, v)
    trace.append({"wall": "divisibility", "passed": ok, "detail": bad})
    if not ok:
        return "REFUTED", "divisibility N-wall (a lambda_i is non-integer)", trace

    # S-wall / refutation — direct exact cover is BOTH routes at once
    nblocks = comb(v, k)
    if nblocks <= MAX_BLOCKS:
        verdict, blocks, verified = steiner_exact_cover(t, k, v, budget)
        trace.append({"wall": "exact-cover(direct)", "result": verdict, "blocks": blocks,
                      "witnessVerified": verified, "budgetSeconds": budget, "numVars": nblocks})
        if verdict == "SAT" and verified:
            return "EXISTS", f"CP-SAT constructed + independently verified ({blocks} blocks)", trace
        if verdict == "UNSAT":
            return "REFUTED", "exact-cover proven infeasible (no such system)", trace
        # UNKNOWN -> fall through to the derived-tower refutation
    else:
        trace.append({"wall": "exact-cover(direct)", "result": "SKIPPED",
                      "reason": f"C({v},{k})={nblocks} > MAX_BLOCKS", "numVars": nblocks})

    # Refutation fallback — attack the immediate derived child; UNSAT child => parent refuted (KBK, cheap)
    if t > 2:
        ct, ck, cv = t - 1, k - 1, v - 1
        if comb(cv, ck) <= MAX_BLOCKS:
            child_budget = max(30, budget // 2)
            cv_res, cblk, cver = steiner_exact_cover(ct, ck, cv, child_budget)
            trace.append({"wall": f"derived-child S({ct},{ck},{cv})", "result": cv_res,
                          "blocks": cblk, "budgetSeconds": child_budget})
            if cv_res == "UNSAT":
                return "REFUTED", f"derived child S({ct},{ck},{cv}) is non-existent => parent refuted", trace

    return "FRONTIER", "survived divisibility; construction UNKNOWN in budget (honestly open)", trace


def decide_srg(v, k, lam, mu):
    """SRG(v,k,lam,mu): counting -> integer eigenvalues -> Krein -> absolute (all necessary)."""
    trace = []
    if not counting_ok(v, k, lam, mu):
        trace.append({"wall": "counting", "passed": False})
        return "REFUTED", "counting N-wall (parameter identity fails)", trace
    trace.append({"wall": "counting", "passed": True})

    eig = srg_eigendata(v, k, lam, mu)
    if eig is None:
        # non-integer eigenvalues are only allowed in the conference case v=2k+1 etc.; else refuted
        if v != 2 * k + 1:
            trace.append({"wall": "integer-eigenvalues", "passed": False})
            return "REFUTED", "eigenvalue-integrality N-wall (multiplicities non-integer)", trace
        trace.append({"wall": "integer-eigenvalues", "passed": "conference-case", "note": "half-case, skip spectral"})
        return "FRONTIER", "conference-parameter SRG; spectral walls not applicable", trace

    r, s, f, g = eig
    trace.append({"wall": "integer-eigenvalues", "passed": True, "eig": [r, s], "mult": [f, g]})
    kr = krein_ok(k, r, s)
    trace.append({"wall": "krein", "passed": kr})
    if not kr:
        return "REFUTED", "Krein N-wall (Krein inequality violated)", trace
    ab = absolute_ok(v, f, g)
    trace.append({"wall": "absolute-bound", "passed": ab})
    if not ab:
        return "REFUTED", "absolute-bound N-wall (multiplicity too small for v)", trace
    return "FRONTIER", "survives counting + integrality + Krein + absolute (open / consistent)", trace


def decide_symmetric(v, k, lam, budget):
    """Symmetric 2-(v,k,lam) design: counting + perfect-square + Bruck-Ryser. lam=1 (a plane/STS)
    routes to the Steiner constructor so the engine can also EXHIBIT a witness."""
    trace = []
    feas = symmetric_design_feasible(v, k, lam)
    trace.append({"wall": "symmetric-feasible (counting+square+Bruck-Ryser)",
                  "verdict": feas["verdict"], "obstruction": feas.get("obstruction")})
    vu = feas["verdict"].upper()
    if vu.startswith("REFUTED") or vu.startswith("INFEASIBLE"):
        return "REFUTED", f"Bruck-Ryser / perfect-square N-wall ({feas.get('obstruction')})", trace
    if lam == 1:
        # a symmetric 2-(v,k,1) design IS the Steiner system S(2,k,v); try to construct it
        sv, sr, st = decide_steiner(2, k, v, budget)
        trace.append({"wall": "route->steiner(2,k,v)", "result": sv, "reason": st[-1] if st else None})
        return sv, f"via Steiner S(2,{k},{v}): {sr}", trace
    return "FRONTIER", "survives symmetric-design necessary walls (open / consistent)", trace


# ----------------------------------------------------------------------------- dispatch
def decide(target, budget):
    fam, params = target.split(":")
    nums = [int(x) for x in params.split(",")]
    if fam == "steiner":
        t, k, v = nums
        verdict, reason, trace = decide_steiner(t, k, v, budget)
    elif fam == "srg":
        v, k, lam, mu = nums
        verdict, reason, trace = decide_srg(v, k, lam, mu)
    elif fam == "symmetric":
        v, k, lam = nums
        verdict, reason, trace = decide_symmetric(v, k, lam, budget)
    else:
        raise ValueError(f"unknown family {fam}")
    return {"target": target, "verdict": verdict, "reason": reason, "trace": trace}


def digest(x):
    return "sha256:" + hashlib.sha256(json.dumps(x, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


# ----------------------------------------------------------------------------- ground-truth harness
VALIDATION = [
    # (target, expected_verdict, name)  -- the engine MUST reproduce these before any new verdict is trusted
    ("steiner:2,3,7",    "EXISTS",   "Fano plane S(2,3,7)"),
    ("steiner:2,3,8",    "REFUTED",  "S(2,3,8) — STS needs v=1,3 mod 6"),
    ("steiner:5,6,12",   "EXISTS",   "Witt design S(5,6,12)"),
    ("steiner:6,7,13",   "REFUTED",  "Conway divisibility S(6,7,13)"),
    ("srg:10,3,0,1",     "FRONTIER", "Petersen SRG (must NOT be refuted)"),
    ("srg:28,9,0,4",     "REFUTED",  "SRG(28,9,0,4) — Krein/absolute"),
    ("symmetric:43,7,1", "REFUTED",  "Projective plane order 6 — Bruck-Ryser"),
    ("symmetric:7,3,1",  "EXISTS",   "Projective plane order 2 = Fano"),
]


def validate_ground_truth(budget: int = 20) -> dict:
    """Run the ground-truth gate: the engine MUST reproduce known math before any new verdict is trusted.
    Returns {allGreen, cases:[{target,name,expected,got,pass}]}. A red gate INVALIDATES any chase verdict —
    callers (e.g. oracle/kbk/engine/two_wall_bridge.py) must withhold a result unless allGreen is True."""
    rows, all_green = [], True
    for tgt, expected, name in VALIDATION:
        r = decide(tgt, budget)
        ok = r["verdict"] == expected
        all_green = all_green and ok
        rows.append({"target": tgt, "name": name, "expected": expected, "got": r["verdict"], "pass": ok})
    return {"allGreen": all_green, "cases": rows}


def main():
    argv = sys.argv[1:]
    target = None
    budget = 300
    for a in argv:
        if a.startswith("--target="):
            target = a.split("=", 1)[1]
        elif a.startswith("--budget="):
            budget = int(a.split("=", 1)[1])
    if target is None:
        target = "steiner:4,5,15"   # default chase: the localized S(6,7,17) sub-frontier

    # 1) validate against ground truth (fast budgets) — one source of truth: validate_ground_truth()
    print("GROUND-TRUTH VALIDATION (engine must reproduce known math):")
    gate = validate_ground_truth(20)
    val_rows, all_green = gate["cases"], gate["allGreen"]
    for row in val_rows:
        print(f"  [{'PASS' if row['pass'] else 'FAIL'}] {row['name']:38s} expected {row['expected']:8s} got {row['got']}")
    print(f"\nVALIDATION: {'ALL GREEN — engine trustworthy' if all_green else 'RED — verdict below is INVALID'}\n")

    # 2) the actual chase — machine decides, thumb off
    print(f"CHASE: {target}  (budget {budget}s)")
    result = decide(target, budget)
    print(f"  VERDICT: {result['verdict']} — {result['reason']}")
    for step in result["trace"]:
        print(f"    · {step}")

    body = {
        "kind": "oracle-frontier-math-two-wall-engine", "version": "2026-07-22-v1",
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "purpose": "one general two-wall decider; no per-target hand-script. thumb off the scale.",
        "validation": {"allGreen": all_green, "cases": val_rows},
        "chase": result,
        "budgetSeconds": budget,
        "honesty": "verdict is trustworthy ONLY if validation.allGreen is true. REFUTED=proven impossible, "
                   "EXISTS=verified witness, FRONTIER=survived necessary walls but open in budget (UNKNOWN != verdict).",
    }
    body["receiptHash"] = digest(body)
    OUT.write_text(json.dumps(body, indent=2) + "\n", encoding="utf-8")
    print(f"\nreceipt: {OUT}")
    if target == "steiner:4,5,15" and result["verdict"] == "REFUTED":
        print("  >>> KBK: S(4,5,15) refuted => S(6,7,17) dies with it (derived-tower propagation).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
