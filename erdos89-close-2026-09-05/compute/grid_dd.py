"""Exact distinct-distance count of the k x k integer grid (n = k^2 points).

Distances are sqrt(a^2+b^2) for 0<=a,b<=k-1, (a,b)!=(0,0); distinct distances
correspond bijectively to distinct values of a^2+b^2.  Exact integer arithmetic,
no floating point in the count.  Compared against the two benchmark shapes of
Erdos problem 89: n/sqrt(log n) (conjectured truth) and n/log n (Guth-Katz).
"""
import json, math, hashlib, sys, platform, datetime

rows = []
for k in range(2, 121):
    n = k * k
    vals = {a * a + b * b for a in range(k) for b in range(k)}
    vals.discard(0)
    D = len(vals)
    logn = math.log(n)
    rows.append({
        "k": k, "n": n, "distinct_distances_grid": D,
        "n_over_sqrt_log_n": n / math.sqrt(logn),
        "n_over_log_n": n / logn,
        "ratio_D_to_n_over_sqrt_log_n": D / (n / math.sqrt(logn)),
        "ratio_D_to_n_over_log_n": D / (n / logn),
        "sqrt_n": math.sqrt(n),
        "ratio_D_to_sqrt_n": D / math.sqrt(n),
    })

out = {
    "tool": "grid_dd.py",
    "purpose": "exact distinct-distance counts of the k x k integer grid; benchmark shapes for Erdos 89",
    "utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
    "host": platform.node(),
    "python": sys.version.split()[0],
    "arithmetic": "exact integers for the count; floats only for the benchmark ratios",
    "rows": rows,
}
txt = json.dumps(out, indent=1, sort_keys=True)
open("grid_dd_results.json", "w").write(txt)
print("SHA256_RESULTS", hashlib.sha256(txt.encode()).hexdigest())
print(f"{'k':>4} {'n':>6} {'D(grid)':>8} {'D/(n/sqrt(log n))':>18} {'D/(n/log n)':>12} {'D/sqrt(n)':>10}")
for r in rows:
    if r["k"] % 10 == 0 or r["k"] in (2, 3, 5):
        print(f"{r['k']:>4} {r['n']:>6} {r['distinct_distances_grid']:>8} "
              f"{r['ratio_D_to_n_over_sqrt_log_n']:>18.4f} "
              f"{r['ratio_D_to_n_over_log_n']:>12.4f} {r['ratio_D_to_sqrt_n']:>10.4f}")
