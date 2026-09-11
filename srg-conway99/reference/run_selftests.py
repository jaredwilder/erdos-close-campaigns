"""
run_selftests.py — re-run EVERY engine tool's selftest in isolation and aggregate. This is the operator's
personal verification of agent-delivered tools: no tool is trusted on its own report; each is re-executed
here. Emits oracle/kbk/engine/SELFTEST-RECEIPT.json. Exit 0 iff all pass.
Run from repo root: python oracle/kbk/engine/run_selftests.py
"""
from __future__ import annotations
import glob
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
SELF = os.path.basename(__file__)

mods = sorted(
    os.path.basename(p) for p in glob.glob(os.path.join(HERE, "*.py"))
    if os.path.basename(p) not in (SELF, "__init__.py") and not os.path.basename(p).startswith("_")
)

results = []
for m in mods:
    rel = os.path.join("oracle", "kbk", "engine", m)
    try:
        # 300s: the cvxpy modules (sos_certificate, flag_algebra, delsarte_lp) pay a ~40-80s cold-import cost
        # on a loaded box — a real environmental floor, not test compute. 120s false-timed-out one of them.
        p = subprocess.run([sys.executable, rel], capture_output=True, text=True, cwd=REPO, timeout=300)
        line = (p.stdout.strip().splitlines() or [""])[-1]
        parsed = {}
        try:
            parsed = json.loads(line)
        except Exception:
            parsed = {}
        ok = p.returncode == 0 and parsed.get("ok") is True
        results.append({"module": m, "ok": ok, "exit": p.returncode,
                        "method": parsed.get("method", ""),
                        "stderr": (p.stderr.strip()[-300:] if not ok else "")})
    except subprocess.TimeoutExpired:
        results.append({"module": m, "ok": False, "exit": None, "method": "", "stderr": "TIMEOUT (>120s)"})

passed = sum(1 for r in results if r["ok"])
total = len(results)
receipt = {"kind": "kbk-engine-selftest", "passed": passed, "total": total, "results": results}
with open(os.path.join(HERE, "SELFTEST-RECEIPT.json"), "w", encoding="utf-8") as f:
    json.dump(receipt, f, indent=2)
    f.write("\n")

print(f"ENGINE SELFTESTS: {passed}/{total} pass")
for r in results:
    mark = "PASS" if r["ok"] else "FAIL"
    print(f"  [{mark}] {r['module']:<26} {r['method']}" + ("" if r["ok"] else f"   <- {r['stderr'][:180]}"))
sys.exit(0 if passed == total else 1)
