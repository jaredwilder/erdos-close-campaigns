# Exact Erdős values and formalized structural lemmas

**The first exact values of Mathlib's canonical `rothNumberNat`: `rothNumberNat 14 = 8` and `rothNumberNat 15 = 8`**, together with a supermultiplicativity lemma absent from Mathlib, a formalized classical lower bound, and several structural reductions.

Author: Jared Wilder. First public timestamp: 2026-09-10. Underlying research dated 2026-09-05.

## Erdős 142 — exact `rothNumberNat` values and structural lemmas

All results below compile with **no `sorryAx` and no `native_decide`**:

| result | significance |
|---|---|
| **`r3 n = rothNumberNat n`** | identifies the project's finite `r3` definition with Mathlib's canonical one |
| **`rothNumberNat (p+1) * rothNumberNat (q+1) <= rothNumberNat (2pq+p+q+1)`** | supermultiplicativity, absent from Mathlib; a lower-side companion to `rothNumberNat_add_le` |
| **`rothNumberNat 14 = 8` and `rothNumberNat 15 = 8`** | the first exact values of Mathlib's `rothNumberNat`; explicit witnesses are also supplied through `n=20` |
| `2 * rothNumberNat (n+1) <= rothNumberNat (3n+2)` | tripling inequality |
| `2 * r3(n) <= n + 8` | an elementary finite upper bound recovered and formally checked |

The asymptotic question for `r_k(N)` is separate from these exact finite values and structural lemmas.

One useful formal repair was proving the correspondence between the project's private `r3` definition and Mathlib's canonical `rothNumberNat`. Once that equivalence was formalized, subsequent statements could be written directly in the standard Mathlib vocabulary.

## Erdős 89 — formalized lower bound

The repository includes a sorry-free elementary **`Omega(sqrt n)`** lower bound corresponding to Erdős 1946.

A companion comparison proves formally that this growth rate is asymptotically smaller than the Guth–Katz `n/log n` bound. The finite grid computations in this directory are therefore presented as constructions and checks, not as evidence for a stronger asymptotic theorem.

## Additional formal material

- `erdos143-close-2026-09-05` — Ramsey-number variants and structural lemmas;
- `eg411-omega67-2026-09-05` — an omega-bound formal theorem for the associated balance law;
- `erdos142-evidence/` — exact finite data and literature notes for the `k=3` problem;
- `srg-conway99/` — strongly regular graph transformations, reference data, an `SRG(5,2,0,1)` proof, and the separate `SRG(99,14,1,2)` target.

Historical directory names are retained for provenance.

## Mathematical scope

The contribution of this repository is the exact values, formal lemmas, classical lower bound, structural reductions, and finite computations listed above. Each result should be read at the scope of its own theorem statement rather than by the size of the larger Erdős problem that originally motivated it.

## License

Apache-2.0.