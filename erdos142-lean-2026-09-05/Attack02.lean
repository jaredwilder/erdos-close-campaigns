/-
Erdős #142 — exact-value frontier probe. Self-contained; raises maxRecDepth so
kernel `decide` can fold the powerset of {1,…,n} for larger n.
Exact r_3(n): n=6→4, 7→4, 8→4, 9→5, 10→5 (exhaustive table, cross-checked).
Each theorem is independent: a failure at large n does not unseal smaller n.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos142Probe

open Finset

def AP3Free (s : Finset ℕ) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a + c = 2 * b → a = c

instance (s : Finset ℕ) : Decidable (AP3Free s) := by
  unfold AP3Free; infer_instance

def r3 (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter AP3Free).sup Finset.card

theorem r3_6 : r3 6 = 4 := by decide
theorem r3_7 : r3 7 = 4 := by decide
theorem r3_8 : r3 8 = 4 := by decide
theorem r3_9 : r3 9 = 5 := by decide
theorem r3_10 : r3 10 = 5 := by decide

#print axioms r3_6
#print axioms r3_7
#print axioms r3_8
#print axioms r3_9
#print axioms r3_10

end Erdos142Probe
