# erdos-close-campaigns

Four Erdos close campaigns that **did not close their problems**, published for what they did land:
Mathlib-shaped lemmas, first exact values, formalized classical bounds, and gap ledgers that
measure how far short they fall.

Author: Jared Wilder. First public timestamp: 2026-09-10. Campaigns dated 2026-09-05.

## Erdos 142 — NOT closed, and the campaign says so in its own first line

> **The open problem is NOT closed and NOT advanced.** Nothing here bears on the $10,000 question,
> the Theta-order of r_k(N).

What it did land, all sealed at exit 0 with **no `sorryAx` and no `native_decide`**:

| result | note |
|---|---|
| **`r3 n = rothNumberNat n`** | bridges a private definition to Mathlib's canonical one, closing the predecessor campaign's own stated open obligation |
| **`rothNumberNat (p+1) * rothNumberNat (q+1) <= rothNumberNat (2pq+p+q+1)`** | supermultiplicativity, **absent from Mathlib**, the lower-side companion of `rothNumberNat_add_le` |
| **`rothNumberNat 14 = 8` and `rothNumberNat 15 = 8`** | the **first exact values** of Mathlib's `rothNumberNat`, plus witnesses to n = 20 |
| `2 * rothNumberNat (n+1) <= rothNumberNat (3n+2)` | tripling |
| `2 * r3(n) <= n + 8` | a predecessor file written but never compiled before a crash, now sealed |

**The lesson the campaign records about itself:** the predecessor built a *private* `r3` and
hand-proved four lemmas Mathlib already had, and its own terminal record called the correspondence
"documented, not proven." Mathlib already contained Roth's theorem and Behrend's construction,
both sides of the bracket. This campaign bridged the objects and then worked in Mathlib's
vocabulary instead.

## Erdos 89 — NOT closed, with a gap ledger that measures the shortfall

Verdict `NOT_CLOSED`, stated by the campaign. Banked: a sorry-free elementary Omega(sqrt n) lower
bound, which is **Erdos 1946**, together with a sorry-free gap ledger proving that rung is
negligible against the Guth-Katz n / log n record.

It also records why no search could ever settle it: the statement quantifies over all n-point
subsets of the plane for all large n with a uniform constant, so no finite configuration search is
evidence either way. And it lists what is explicitly **not** proved, including the Guth-Katz
variant and a grid upper bound that needs Landau-Ramanujan, which Mathlib lacks.

A grid measurement is included and labelled, in the campaign's own words, **"CONSTRUCTION
MEASUREMENT, NOT EVIDENCE for the lower bound."**

## Also here

- `erdos143-close-2026-09-05` — Ramsey number variants formalized, structural lemmas landed, not
  closed.
- `eg411-omega67-2026-09-05` — the omega capstone kernel theorem for the EG411 balance law.
- `erdos142-evidence/` — the exact-envelope campaign, the novelty searches, and the k3 citation
  corpus.
- `srg-conway99/` — strongly regular graph transports, Brouwer ground truth, an SRG(5,2,0,1)
  proof, and the **open** SRG(99,14,1,2) goal, which is Conway's 99-graph problem and is **not**
  solved here.

## License

Apache-2.0.
