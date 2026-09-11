/-
Erdős Problem #142 ($10,000) — CLOSE CAMPAIGN, FILE 05:
`rothNumberNat 17`, EXACT.

Continuation of Close03.  Same cardinality-slice reduction, two more rows.

MEASURED COST, so the next session does not have to guess (Close03.time):
Close03 sealed rothNumberNat 14 = 8 AND rothNumberNat 15 = 8 together —
C(14,9) + C(15,9) = 7,007 kernel-checked 9-subsets — in 1 min 59 s wall,
12.9 GB peak RSS.  The previous campaign's powerset method (Attack 03) needed
12 min 09 s and 31 GB for n = 14 ALONE and could not reach 15 at all.

  n   slice size C(n,9)   powerset 2^n
 ───  ─────────────────   ────────────
  16          11,440           65,536
  17          24,310          131,072

⛔ The slice is still exponential; this buys rows, not a frontier.  OEIS
A003002 is published to n = 211.  The point of these rows is that they are
exact values OF MATHLIB'S `rothNumberNat`, kernel-checked, which do not exist
anywhere else — not that they approach the computational record.

SPLIT FROM Close05 ON PURPOSE: one value per process, so a run of mine can never
OOM somebody else's job on this shared box.

Self-contained.  No `native_decide`.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000000

namespace Erdos142Exact17

open Finset

/-- Cardinality-slice reduction for Mathlib's `rothNumberNat` (see Close03). -/
theorem rothNumberNat_le_of_powersetCard {n k : ℕ}
    (H : ∀ T ∈ (Finset.range n).powersetCard (k + 1), ¬ ThreeAPFree (↑T : Set ℕ)) :
    rothNumberNat n ≤ k := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨t, hts, htcard, htfree⟩ := rothNumberNat_spec n
  obtain ⟨T, hTt, hTcard⟩ := Finset.exists_subset_card_eq (s := t) (n := k + 1) (by omega)
  exact H T (Finset.mem_powersetCard.mpr ⟨hTt.trans hts, hTcard⟩)
    (htfree.mono (Finset.coe_subset.mpr hTt))

/-- The base-3 no-digit-2 set below 27, independently recomputed as extremal for
n = 14…19 by `tools/r3_exact.py` and matching OEIS A003002. -/
theorem w17 : 8 ≤ rothNumberNat 17 :=
  ThreeAPFree.le_rothNumberNat {0, 1, 3, 4, 9, 10, 12, 13} (by decide) (by decide) (by decide)

/-- `rothNumberNat 17 ≤ 8`.  C(17,9) = 24,310 slice members. -/
theorem u17 : rothNumberNat 17 ≤ 8 := rothNumberNat_le_of_powersetCard (by decide)

theorem rothNumberNat_17 : rothNumberNat 17 = 8 := le_antisymm u17 w17

#print axioms u17
#print axioms rothNumberNat_17

end Erdos142Exact17
