/-
Erdős Problem #142 ($10,000) — formal seals over r_3(n), the AP-free / r_3 problem.

FAITHFUL PURE-MATHLIB RECONSTRUCTION of the k = 3 case of
`Erdos142.r = Set.IsAPOfLengthFree.maxCard` (frozen spec:
FormalConjectures/ErdosProblems/142.lean). `FormalConjecturesUtil` — where
`Set.IsAPOfLengthFree` and `.maxCard` are defined — is NOT available on this
toolchain (full Mathlib only, pin 919544d4), so the object is reconstructed
here over an explicit Finset ground set and the correspondence is documented:

    r3 n  ==  Erdos142.r 3 n
            = largest size of a subset of {1,…,n} ⊆ ℕ containing no
              non-trivial 3-term arithmetic progression.

The spec's headline `erdos_142` / `variants.three` are `answer(sorry)` HOLES
(the genuine open asymptotic — Roth-territory) and are NOT targeted. What is
sealed below are lemmas that are UNCONDITIONALLY TRUE about r_3 and provable
from the exhaustive exact table (oracle/evidence/erdos142-exact-envelope).
-/
import Mathlib

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Erdos142Attack

open Finset

/-- `s` contains no non-trivial 3-term arithmetic progression: every solution
of `a + c = 2*b` with `a, b, c ∈ s` is trivial, i.e. `a = c` (which forces
`a = b = c`). This is exactly "3-AP-free" (`Set.IsAPOfLengthFree · 3`
restricted to a Finset). -/
def AP3Free (s : Finset ℕ) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a + c = 2 * b → a = c

instance (s : Finset ℕ) : Decidable (AP3Free s) := by
  unfold AP3Free; infer_instance

/-- `r3 n = r_3(n)` : the largest cardinality of a 3-AP-free subset of
`{1, …, n}`. -/
def r3 (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter AP3Free).sup Finset.card

/-- Any subset of a 3-AP-free set is 3-AP-free. -/
theorem AP3Free.subset {s t : Finset ℕ} (hts : t ⊆ s) (hs : AP3Free s) :
    AP3Free t := fun a ha b hb c hc h => hs a (hts ha) b (hts hb) c (hts hc) h

/-- **Monotonicity of r_3** : `m ≤ n → r_3(m) ≤ r_3(n)`.
A 3-AP-free subset of `{1,…,m}` is a 3-AP-free subset of `{1,…,n}`. -/
theorem r3_mono {m n : ℕ} (hmn : m ≤ n) : r3 m ≤ r3 n := by
  unfold r3
  refine Finset.sup_mono ?_
  intro s hs
  rw [Finset.mem_filter, Finset.mem_powerset] at hs ⊢
  exact ⟨hs.1.trans (Finset.Icc_subset_Icc_right hmn), hs.2⟩

/-- Successor form of monotonicity: `r_3(n) ≤ r_3(n+1)`. -/
theorem r3_le_succ (n : ℕ) : r3 n ≤ r3 (n + 1) := r3_mono (Nat.le_succ n)

/-- Lower bound from an explicit 3-AP-free witness inside `{1,…,n}`. -/
theorem r3_ge_of_witness {n : ℕ} {W : Finset ℕ} (hsub : W ⊆ Finset.Icc 1 n)
    (hfree : AP3Free W) : W.card ≤ r3 n := by
  unfold r3
  apply Finset.le_sup (f := Finset.card)
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hsub, hfree⟩

/-! ### Exact small values — kernel `decide`, BOTH directions (witness + exhaustive) -/

theorem r3_1 : r3 1 = 1 := by decide
theorem r3_2 : r3 2 = 2 := by decide
theorem r3_3 : r3 3 = 2 := by decide
theorem r3_4 : r3 4 = 3 := by decide
theorem r3_5 : r3 5 = 4 := by decide
theorem r3_6 : r3 6 = 4 := by decide

/-! ### Certified lower bounds via explicit extremal witnesses (table region) -/

theorem r3_9_ge_5 : 5 ≤ r3 9 := by
  have hle := r3_ge_of_witness (n := 9) (W := ({1, 2, 4, 8, 9} : Finset ℕ))
    (by decide) (by decide)
  rwa [show ({1, 2, 4, 8, 9} : Finset ℕ).card = 5 from by decide] at hle

theorem r3_11_ge_6 : 6 ≤ r3 11 := by
  have hle := r3_ge_of_witness (n := 11) (W := ({1, 2, 4, 5, 10, 11} : Finset ℕ))
    (by decide) (by decide)
  rwa [show ({1, 2, 4, 5, 10, 11} : Finset ℕ).card = 6 from by decide] at hle

theorem r3_13_ge_7 : 7 ≤ r3 13 := by
  have hle := r3_ge_of_witness (n := 13)
    (W := ({1, 2, 4, 5, 10, 11, 13} : Finset ℕ)) (by decide) (by decide)
  rwa [show ({1, 2, 4, 5, 10, 11, 13} : Finset ℕ).card = 7 from by decide] at hle

theorem r3_14_ge_8 : 8 ≤ r3 14 := by
  have hle := r3_ge_of_witness (n := 14)
    (W := ({1, 2, 4, 5, 10, 11, 13, 14} : Finset ℕ)) (by decide) (by decide)
  rwa [show ({1, 2, 4, 5, 10, 11, 13, 14} : Finset ℕ).card = 8 from by decide] at hle

#print axioms r3_mono
#print axioms r3_le_succ
#print axioms r3_4
#print axioms r3_5
#print axioms r3_6
#print axioms r3_9_ge_5
#print axioms r3_14_ge_8

end Erdos142Attack
