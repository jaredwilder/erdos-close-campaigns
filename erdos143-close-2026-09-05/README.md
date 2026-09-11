# erdos143-close-2026-09-05 — campaign record

**MSL_DIALECT v2.0 · MSL_PROFILE MSL-F · MSL_MODE CLOSE**
**TARGET:** Erdos problem 143 (`$500`, tag `primitive sets`, Lean-formalized in
the DeepMind formal-conjectures corpus). **TARGET NOT CLOSED.**

## What is in this directory

| file | what it is |
|---|---|
| `E143.lean` | sorry-free Lean 4 / Mathlib source, 5 theorems |
| `DERIVATION.md` | the in-record derivation, the sharpness witness, the external audit, and the named obstruction |
| `falsifier_e143.py` | exact-arithmetic falsifier + sharpness enumerator, stdlib only |
| `receipts/lean-kernel-2026-09-05.log` | `lake env lean E143.lean` output incl. `#print axioms` |
| `receipts/falsifier-2026-09-05.json` | falsifier verdict `SURVIVED`, sharpness `1/2` |

## The kernel receipt

```
host        root@51.158.234.15  (rented box; nothing heavy ran on the laptop)
toolchain   Lean 4.31.0-rc1, commit fd009949156901e6cf15b6d9bf1122294b8e697a
mathlib     /root/formalizer/proofs/.lake/packages/mathlib
file        /root/formalizer/proofs/E143.lean
sha256      ecb348266a23ec3d3e5ff5cf1672d919f7e6981f53c4944c88ec2d845df68593
            (byte-identical to E143.lean in this directory)
result      0 errors; warnings only (3x deprecated push_neg, 1x unused binder)
axioms      every one of the five theorems:
            [propext, Classical.choice, Quot.sound]      -- no sorryAx
```

## The five kernel-checked declarations

```
Erdos143Frag.one_le_dist           k = 1 gives |x - y| >= 1
Erdos143Frag.two_le_of_mem         every element of an infinite well-separated set is >= 2
Erdos143Frag.ncard_inter_Iio_le    |A cap (-inf, 2X)| <= ceil X          (the packing theorem)
Erdos143Frag.ncard_le_half         |A cap (-inf, Y)| <= Y/2 + 1
Erdos143Frag.wellSeparated_ncard_le  the same, stated on the frozen predicate
```

`WellSeparatedSet` in `E143.lean` is a transcription of `Erdos143.WellSeparatedSet`
from `oracle/evidence/targets/lean-sources/FormalConjectures__ErdosProblems__143.lean`.
BINDING = TRANSCRIPTION_CERT, not a kernel-checked equivalence: nothing here has
been checked against the upstream file by the kernel, only by eye.

## What is NOT done

`erdos_143.parts.i` (liminf density 0) and `erdos_143.parts.ii` (summability of
`1/(x log x)`) are **both untouched**. The bound proved is an **upper** density
bound of 1/2; the problem asks for lower-density / logarithmic sparsity.

**Constant 1/2 is optimal** (exhaustive receipt), so this method cannot be
sharpened — see `DERIVATION.md` §1 and §5 for why the multiplier set must be a
divisibility chain, and what is missing.

## Novelty

**PRIOR_ART_COLLISION_SUSPECTED, UNVERIFIED.** The external audit calls T1 "a
known elementary observation … the continuous analogue of the classical dyadic
pigeonhole proof". No prior-art search was executed. Nothing here is claimed new.

## Prior estate record corrected

`oracle/evidence/rapid-fire/corpus-erdos-143-operator-20260730T091939Z.json`
reads erdos:143 as "sets of integers where no element divides another" and ran
CP-SAT over integer divisibility. The frozen statement is about **real**
well-separated sets in `(1, infinity)`; the integer reading is a proper special
case, and every conclusion in that run is scoped to that special case only.
