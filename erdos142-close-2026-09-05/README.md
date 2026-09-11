# Erdős #142 — CLOSE campaign, 2026-09-05

Restart of the crashed campaign `../erdos142-lean-2026-09-05`.

**The open problem is NOT closed and NOT advanced.** `erdos_142`,
`erdos_142.variants.upper`, `erdos_142.variants.three` remain `answer(sorry)`
holes. Nothing here bears on the $10,000 question (the Θ-order of `r_k(N)`).

Read `TERMINAL.json` for the full record. `receipts/PENDING.md` lists everything
that is **UNPROVED**, with exact launch lines.

## The one thing to know

The predecessor campaign built a **private** `r3` and hand-proved four lemmas
that **Mathlib already had** for its canonical `rothNumberNat` — and its own
TERMINAL.json recorded the correspondence as *"documented, not proven"*.
Mathlib also already contains **Roth's theorem** and **Behrend's construction**,
i.e. both sides of the bracket around the open problem.

This campaign bridges the two objects and then works in Mathlib's vocabulary.

## Sealed (exit 0, no `sorryAx`, no `native_decide`)

| file | wall | what landed |
|---|---|---|
| `lean/Close01_Bridge.lean` | 5.1 s | **`r3 n = rothNumberNat n`** — closes the predecessor's stated open obligation; Roth and Behrend transported in as corollaries |
| `lean/Close02_Supermultiplicative.lean` | 5.8 s | **`rothNumberNat (p+1) * rothNumberNat (q+1) ≤ rothNumberNat (2pq+p+q+1)`** — absent from Mathlib; the lower-side companion of `rothNumberNat_add_le`. Plus `8^j ≤ rothNumberNat (T j + 1)`, `2·T j + 1 = 27^j` |
| `lean/Close03_Exact.lean` | 1 m 59 s | **`rothNumberNat 14 = 8`, `rothNumberNat 15 = 8`** — the first exact values of Mathlib's `rothNumberNat`; plus the slice reduction and witnesses to n = 20 |
| `lean/Close04_Dial.lean` | 5.3 s | **`dial`** — any seed `c ≤ rothNumberNat (p+1)` becomes an all-`N` power law with no new mathematics; plus `tripling : 2·rothNumberNat (n+1) ≤ rothNumberNat (3n+2)` |
| `../erdos142-lean-2026-09-05/Attack05.lean` | 9.1 s | predecessor file, written but **never compiled before the crash** — now sealed (`2·r₃(n) ≤ n+8` for all n) |
| `../erdos142-lean-2026-09-05/Attack06.lean` | 4.9 s | predecessor file, likewise — the slice reduction |
| `lean/Close07_BehrendSeed.lean` | 5.3 s | **the dial turned past the classical exponent** — Mathlib's own `Behrend.bound_aux' 12 100` gives `8×10^18 ≤ rothNumberNat (199^12)`; fed to the dial this yields a family with exponent **13/20 > log 2/log 3**, certified in exact integers by `2^20 < 3^13` and `(2·199^12−1)^13 < (8×10^18)^20` |

## Findings

- **F1** The bridge is proved, so the predecessor's whole table is now a table of
  exact values of Mathlib's own object.
- **F2** Supermultiplicativity is genuinely missing from Mathlib and is now
  proved. Note plain `r₃(mn) ≥ r₃(m)r₃(n)` is **false** (`r₃(4) = 3 < 4`); the
  `2pq+p+q+1` form is correct and is **tight at 58 published instances**.
- **F3** **The elementary exponent is pinned.** Across all 211 published exact
  values (OEIS A003002 b-file, sha-256 pinned) *no* seed beats `log 2/log 3`,
  with equality at exactly the five Szekeres points `(3^k+1)/2`. **Computing more
  exact values of r₃ cannot improve this exponent** — the predecessor's stated
  frontier ("`decide` one more row") was aimed at something that provably does
  not move.
- **F4** The slice reduction is a **6× speedup / 2.4× lighter** than the
  predecessor's powerset method, and it had been proved and left unspent.
- **F5** Three-way agreement on every overlapping exact value: Lean kernel
  (n ≤ 15), an independent Python solver (n ≤ 40), the OEIS b-file (n ≤ 211).
- **F6** **The dial is not *intrinsically* pinned** — F3's pinning is a fact about
  the published *table*, not about the lemma. Feeding Mathlib's own Behrend bound
  into the dial gives a kernel-checked exponent **13/20 > log 2/log 3**
  (θ = 0.67784 vs 0.63093). The certificate is two exact integer inequalities;
  no floating point enters the proof.

## Honest placement

The exponent `log 2/log 3` is classical (Szekeres / base-3), not new mathematics,
and Behrend (1946) — already in Mathlib — is asymptotically far stronger. What is
new is the Mathlib-shaped lemma, the bridge, the first exact values, and the
*measured* fact that the finite front cannot move the elementary exponent.

`lean/Close07_BehrendSeed.lean` (sealed) turns that negative into a positive:
it does **not** improve on Behrend — Behrend gives `N^(1−o(1))`, infinitely
better — it shows the elementary machinery here can be driven past the classical
constant by a *seed* rather than by a bigger *table*.

## Layout

```
TERMINAL.json                     the full record
README.md                         this file
lean/Close0{1,2,3,4,7}*.lean      sealed
lean/Close0{5,6}*.lean            authored, UNPROVED — see receipts/PENDING.md
tools/r3_exact.py                 independent $0 exact solver for r_3(n)
tools/dial_and_crossover.py       validates the new lemma against published data
receipts/*.log, *.time            Lean compile + resource receipts
receipts/b003002-oeis.txt         OEIS A003002 b-file, n = 0..211
receipts/r3-exact-A003002.json    solver output, n = 0..40
receipts/dial-and-crossover.json  796 instances checked, 0 violations, dial PINNED
receipts/PENDING.md               everything UNPROVED, with launch lines
```
