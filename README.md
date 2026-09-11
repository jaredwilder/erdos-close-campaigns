# erdos-close-campaigns

**The first exact values of Mathlib's own `rothNumberNat`: `rothNumberNat 14 = 8` and
`rothNumberNat 15 = 8`**, with a supermultiplicativity lemma absent from Mathlib, no `sorryAx` and
no `native_decide`.

The repository collects four Erdős campaigns and the mathematics they actually landed: exact
values, Mathlib-shaped lemmas, a formalized classical bound, structural reductions, and explicit
gap ledgers.

Author: Jared Wilder. First public timestamp: 2026-09-10. Campaigns dated 2026-09-05.

## Erdős 142 — exact Mathlib values and structural lemmas

All results below are sealed at exit 0 with **no `sorryAx` and no `native_decide`**:

| result | note |
|---|---|
| **`r3 n = rothNumberNat n`** | bridges the campaign definition to Mathlib's canonical one, closing the predecessor campaign's stated correspondence obligation |
| **`rothNumberNat (p+1) * rothNumberNat (q+1) <= rothNumberNat (2pq+p+q+1)`** | supermultiplicativity, absent from Mathlib, the lower-side companion of `rothNumberNat_add_le` |
| **`rothNumberNat 14 = 8` and `rothNumberNat 15 = 8`** | the **first exact values** of Mathlib's `rothNumberNat`, plus witnesses to n = 20 |
| `2 * rothNumberNat (n+1) <= rothNumberNat (3n+2)` | tripling |
| `2 * r3(n) <= n + 8` | a predecessor file written but never compiled before a crash, now sealed |

The open asymptotic question for `r_k(N)` lies beyond these exact values and structural lemmas; the
campaign's gap ledger records that separation explicitly.

A useful repair in this lane was semantic rather than cosmetic: the predecessor built a private
`r3` and hand-proved lemmas Mathlib already had while leaving the correspondence merely
documented. This campaign proved the bridge and then worked in Mathlib's canonical vocabulary.

## Erdős 89 — formalized lower bound and gap ledger

The campaign banks a sorry-free elementary **Omega(sqrt n)** lower bound, corresponding to Erdős
1946, together with a sorry-free gap ledger proving that rung is negligible against the Guth–Katz
`n / log n` record.

It also records why finite configuration search cannot settle the asymptotic statement: the target
quantifies over all sufficiently large `n` with a uniform constant. The grid computation therefore
remains labelled as a construction measurement rather than evidence for a stronger universal
lower bound.

## Additional packets

- `erdos143-close-2026-09-05` — Ramsey-number variants formalized and structural lemmas landed;
- `eg411-omega67-2026-09-05` — the omega capstone kernel theorem for the EG411 balance law;
- `erdos142-evidence/` — the exact-envelope campaign, novelty searches, and `k=3` citation corpus;
- `srg-conway99/` — strongly regular graph transports, Brouwer ground truth, an SRG(5,2,0,1)
  proof, and the SRG(99,14,1,2) open target preserved separately.

## Scope

These campaigns were launched at larger Erdős targets; the public mathematical contribution here
is the exact values, lemmas, formalized bounds, structural reductions, and gap accounting listed
above. The larger targets retain their own status rather than being inferred from the campaign
names.

## License

Apache-2.0.
