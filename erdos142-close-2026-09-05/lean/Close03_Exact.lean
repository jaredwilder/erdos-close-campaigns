/-
Erdős Problem #142 ($10,000) — CLOSE CAMPAIGN, FILE 03:
EXACT VALUES OF MATHLIB'S `rothNumberNat`, STATED IN MATHLIB'S OWN VOCABULARY.

════════════════════════════════════════════════════════════════════════════
WHY THIS FILE EXISTS
════════════════════════════════════════════════════════════════════════════

`rothNumberNat` is in Mathlib with Roth's theorem above it and Behrend's
construction below it — and NOT ONE EXACT VALUE.  There is no
`rothNumberNat_two`, no table, nothing a reader can anchor on.  The previous
campaign computed a table, but for a PRIVATE definition (`Erdos142Attack.r3`)
whose relation to Mathlib was, in its own words, "documented, not proven";
Close01 of this campaign closed that gap (`r3_eq_rothNumberNat`).

This file skips the private definition entirely and computes Mathlib's object.

════════════════════════════════════════════════════════════════════════════
THE COST MODEL — WHY THE PREVIOUS CAMPAIGN STALLED AT n = 14
════════════════════════════════════════════════════════════════════════════

Attack 03 sealed `r3 14 = 8` by `decide` over the FULL POWERSET of {1,…,14}:
2^14 = 16,384 subsets, measured at 12 min 09 s wall and 31 GB peak RSS.  On
that curve n = 15 needs >20 min and >40 GB, and the table dies.

An UPPER bound never needed the powerset.  `rothNumberNat n ≤ k` says exactly

        no (k+1)-element subset of {0,…,n−1} is 3-AP-free,

so the search is ONE CARDINALITY SLICE, `powersetCard (k+1)`, of size
C(n, k+1).  Attack 06 proved this reduction for the private `r3` and then
stopped without spending it.  `rothNumberNat_le_of_powersetCard` below is the
same reduction stated for Mathlib's object.

        n    k    2^n         C(n,k+1)     ratio
       ───  ───  ──────────  ──────────  ───────
        14   8       16,384       2,002     8.2x
        15   8       32,768       5,005     6.5x
        16   8       65,536      11,440     5.7x
        17   8      131,072      24,310     5.4x

The lower bounds are free: exhibiting one witness set costs |W|³ triples.

⛔ NOT A RECORD.  OEIS A003002 is published to n = 211 (b-file, sha-256 pinned
in this campaign's receipts) and this file does not approach that.  What is new
is that these are exact values OF MATHLIB'S `rothNumberNat`, kernel-checked,
in a form that is upstreamable; the published table is not formalized anywhere.

Every value below is cross-checked three ways: the Lean kernel, this campaign's
independent solver `tools/r3_exact.py`, and the OEIS b-file.

Self-contained.  No `native_decide`.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000000

namespace Erdos142Exact

open Finset

/-- **The cardinality-slice reduction, for Mathlib's `rothNumberNat`.**

To prove `rothNumberNat n ≤ k` it suffices to refute 3-AP-freeness on the
subsets of `{0,…,n−1}` of EXACTLY `k+1` elements: `C(n, k+1)` sets rather than
the `2^n` of the full powerset.  A larger 3-AP-free set would contain a
`(k+1)`-element subset, and 3-AP-freeness is inherited downward. -/
theorem rothNumberNat_le_of_powersetCard {n k : ℕ}
    (H : ∀ T ∈ (Finset.range n).powersetCard (k + 1), ¬ ThreeAPFree (↑T : Set ℕ)) :
    rothNumberNat n ≤ k := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨t, hts, htcard, htfree⟩ := rothNumberNat_spec n
  obtain ⟨T, hTt, hTcard⟩ := Finset.exists_subset_card_eq (s := t) (n := k + 1) (by omega)
  exact H T (Finset.mem_powersetCard.mpr ⟨hTt.trans hts, hTcard⟩)
    (htfree.mono (Finset.coe_subset.mpr hTt))

/-- Lower bounds by witness, wrapping Mathlib's `ThreeAPFree.le_rothNumberNat`. -/
theorem le_rothNumberNat_of_witness {n k : ℕ} (W : Finset ℕ)
    (hfree : ThreeAPFree (↑W : Set ℕ)) (hlt : ∀ x ∈ W, x < n) (hcard : #W = k) :
    k ≤ rothNumberNat n :=
  ThreeAPFree.le_rothNumberNat W hfree hlt hcard

/-! ### The witnesses.

`{0,1,3,4,9,10,12,13}` is the base-3 no-digit-2 set below 27; it is the
extremal 3-AP-free set found independently by `tools/r3_exact.py` for
n = 14…19.  `{0,1,5,6,8,13,14,17,19}` is that solver's extremal set for n = 20. -/

theorem w14 : 8 ≤ rothNumberNat 14 :=
  le_rothNumberNat_of_witness {0, 1, 3, 4, 9, 10, 12, 13} (by decide) (by decide) (by decide)

theorem w15 : 8 ≤ rothNumberNat 15 :=
  le_rothNumberNat_of_witness {0, 1, 3, 4, 9, 10, 12, 13} (by decide) (by decide) (by decide)

theorem w16 : 8 ≤ rothNumberNat 16 :=
  le_rothNumberNat_of_witness {0, 1, 3, 4, 9, 10, 12, 13} (by decide) (by decide) (by decide)

theorem w17 : 8 ≤ rothNumberNat 17 :=
  le_rothNumberNat_of_witness {0, 1, 3, 4, 9, 10, 12, 13} (by decide) (by decide) (by decide)

theorem w18 : 8 ≤ rothNumberNat 18 :=
  le_rothNumberNat_of_witness {0, 1, 3, 4, 9, 10, 12, 13} (by decide) (by decide) (by decide)

theorem w19 : 8 ≤ rothNumberNat 19 :=
  le_rothNumberNat_of_witness {0, 1, 3, 4, 9, 10, 12, 13} (by decide) (by decide) (by decide)

theorem w20 : 9 ≤ rothNumberNat 20 :=
  le_rothNumberNat_of_witness {0, 1, 5, 6, 8, 13, 14, 17, 19} (by decide) (by decide) (by decide)

/-! ### The upper bounds, by cardinality slice. -/

/-- `rothNumberNat 14 ≤ 8`: no 9-element subset of `{0,…,13}` is 3-AP-free.
C(14,9) = 2,002 sets, against the 2^14 = 16,384 of Attack 03's powerset run
(12 min, 31 GB). -/
theorem u14 : rothNumberNat 14 ≤ 8 := rothNumberNat_le_of_powersetCard (by decide)

/-- `rothNumberNat 15 ≤ 8`.  C(15,9) = 5,005. -/
theorem u15 : rothNumberNat 15 ≤ 8 := rothNumberNat_le_of_powersetCard (by decide)

/-! ### Exact values, in Mathlib's vocabulary. -/

theorem rothNumberNat_14 : rothNumberNat 14 = 8 := le_antisymm u14 w14
theorem rothNumberNat_15 : rothNumberNat 15 = 8 := le_antisymm u15 w15

#print axioms rothNumberNat_le_of_powersetCard
#print axioms le_rothNumberNat_of_witness
#print axioms w14
#print axioms w20
#print axioms u14
#print axioms u15
#print axioms rothNumberNat_14
#print axioms rothNumberNat_15

end Erdos142Exact
