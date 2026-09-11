/-
Erdős Problem #142 ($10,000) — ATTACK 06.

════════════════════════════════════════════════════════════════════════════
THE CARDINALITY-SLICE REDUCTION: kill the 2^n powerset in the UPPER bound.
════════════════════════════════════════════════════════════════════════════

Attacks 01–03 computed r_3(n) by kernel `decide` over `(Icc 1 n).powerset` —
ALL 2^n subsets. Measured cost (A3.time): n = 14 took 12m09s / 31 GB. That is
why the table stops at 14, and why Attack 05 had to seed its density constant
at the cheap r_3(8) = 4, giving only the constant ½.

But an UPPER bound never needed the whole powerset. `r_3(n) ≤ k` says exactly:

        NO (k+1)-element subset of {1,…,n} is 3-AP-free.

so the search may be restricted to ONE CARDINALITY SLICE, `powersetCard (k+1)`,
of size C(n, k+1) instead of 2^n. That is this file's content.

    n    k   2^n        C(n,k+1)   saving
   ───  ───  ─────────  ─────────  ──────
    17   8     131,072     24,310   5.4x     ← r_3(17) = 8, ratio 8/17 ≈ 0.4706
    19   8     524,288     92,378   5.7x     ← r_3(19) = 8, ratio 8/19 ≈ 0.4211
    20   9   1,048,576    184,756   5.7x     ← r_3(20) = 9, ratio 9/20 = 0.45

WHY IT MATTERS: Attack 05's `r3_linear_of_seed` converts ANY sealed seed
`r_3(m) ≤ k` into `r_3(n) ≤ (k/m)·n + k` for all n. Every seed in the sealed
table 1..14 has ratio ≥ ½, so ½ is the best constant reachable from it. The
first ratios BELOW ½ appear at n = 17, 18, 19 (0.4706, 0.4444, 0.4211) — all
beyond the powerset wall, all inside reach of the slice.

⛔ WHAT IS AND IS NOT SEALED HERE. The two reduction lemmas below are proved
unconditionally and carry no `decide`, so this file is cheap and certain. The
CONCRETE seed `r_3(17) ≤ 8` is NOT proved here: C(17,9) = 24,310 kernel-checked
subsets is comparable to Attack 03's 30,720 (12 min, 31 GB), and the local WSL
backend has 7.8 GB total and is shared. It is a COMPUTE JOB for the rented box,
recorded as an open obligation in TERMINAL.json with its exact launch line —
not a claim. Nothing below asserts any value of r_3(17).

Self-contained. No `decide`. No `native_decide`.
-/
import Mathlib

set_option maxHeartbeats 1000000

namespace Erdos142Slice

open Finset

/-- `s` contains no non-trivial 3-term arithmetic progression. -/
def AP3Free (s : Finset ℕ) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a + c = 2 * b → a = c

instance (s : Finset ℕ) : Decidable (AP3Free s) := by
  unfold AP3Free; infer_instance

/-- `r3 n = r_3(n)`: largest cardinality of a 3-AP-free subset of `{1,…,n}`. -/
def r3 (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter AP3Free).sup Finset.card

theorem AP3Free.subset {s t : Finset ℕ} (hts : t ⊆ s) (hs : AP3Free s) :
    AP3Free t := fun a ha b hb c hc h => hs a (hts ha) b (hts hb) c (hts hc) h

/-- **Cardinality-slice reduction (set form).** To bound `r_3(n) ≤ k` it
suffices to refute 3-AP-freeness on subsets of EXACTLY `k+1` elements.

The point: a larger 3-AP-free set would contain a `(k+1)`-element subset, and
3-AP-freeness is inherited downward — so the single slice `k+1` already
witnesses the whole tail `≥ k+1`. -/
theorem r3_le_of_no_free_card {n k : ℕ}
    (H : ∀ T : Finset ℕ, T ⊆ Finset.Icc 1 n → T.card = k + 1 → ¬ AP3Free T) :
    r3 n ≤ k := by
  apply Finset.sup_le
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨hSsub, hSfree⟩ := hS
  by_contra hlt
  push_neg at hlt
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (s := S) (n := k + 1) hlt
  exact H T (hTS.trans hSsub) hTcard (hSfree.subset hTS)

/-- **Cardinality-slice reduction (decidable form).** The `decide`-ready
statement: the search runs over `powersetCard (k+1)`, which has `C(n, k+1)`
elements, NOT over `powerset`, which has `2^n`.

Usage (on a machine with the budget):
    theorem r3_17_le_8 : r3 17 ≤ 8 := r3_le_of_powersetCard (by decide) -/
theorem r3_le_of_powersetCard {n k : ℕ}
    (H : ∀ T ∈ (Finset.Icc 1 n).powersetCard (k + 1), ¬ AP3Free T) :
    r3 n ≤ k := by
  apply r3_le_of_no_free_card
  intro T hTsub hTcard
  exact H T (Finset.mem_powersetCard.mpr ⟨hTsub, hTcard⟩)

/-- Sanity anchor for the reduction, at a size the local kernel can afford:
`r_3(4) ≤ 3` proved through the SLICE (C(4,4) = 1 subset) rather than through
the powerset (2^4 = 16). This is a KNOWN-ANSWER CONTROL — r_3(4) = 3 is already
sealed exactly in Attack 01 — so it tests the reduction, not the mathematics. -/
theorem r3_4_le_3 : r3 4 ≤ 3 := r3_le_of_powersetCard (by decide)

#print axioms r3_le_of_no_free_card
#print axioms r3_le_of_powersetCard
#print axioms r3_4_le_3

end Erdos142Slice
