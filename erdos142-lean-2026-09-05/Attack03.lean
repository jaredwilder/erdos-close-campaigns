/-
Erdős #142 — exact-value frontier, upper region. Self-contained.
Exact r_3(n): n=11→6, 12→6, 13→7, 14→8 (exhaustive table, cross-checked).
Each theorem independent; ascending so partial completion still banks.
-/
import Mathlib

set_option maxHeartbeats 8000000
set_option maxRecDepth 400000

namespace Erdos142ProbeHi

open Finset

def AP3Free (s : Finset ℕ) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a + c = 2 * b → a = c

instance (s : Finset ℕ) : Decidable (AP3Free s) := by
  unfold AP3Free; infer_instance

def r3 (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter AP3Free).sup Finset.card

theorem r3_11 : r3 11 = 6 := by decide
theorem r3_12 : r3 12 = 6 := by decide
theorem r3_13 : r3 13 = 7 := by decide
theorem r3_14 : r3 14 = 8 := by decide

#print axioms r3_11
#print axioms r3_12
#print axioms r3_13
#print axioms r3_14

end Erdos142ProbeHi
