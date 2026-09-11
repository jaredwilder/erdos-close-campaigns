/-
Erdős #142 — SUBADDITIVITY of r_3 (forge family F2), unconditional structural
theorem (no `decide`):

        r_3(m + n) ≤ r_3(m) + r_3(n).

Proof: an optimal 3-AP-free S ⊆ {1,…,m+n} splits at the block boundary into
S ∩ {1,…,m} and S ∩ {m+1,…,m+n}. Each is 3-AP-free (subset). The first sits in
{1,…,m}; the second, translated by −m, sits in {1,…,n} and stays 3-AP-free
(x+z = 2y is translation-invariant). Hence |S| ≤ r_3(m) + r_3(n).
Self-contained.
-/
import Mathlib

set_option maxHeartbeats 1000000

namespace Erdos142Sub

open Finset

def AP3Free (s : Finset ℕ) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a + c = 2 * b → a = c

instance (s : Finset ℕ) : Decidable (AP3Free s) := by
  unfold AP3Free; infer_instance

def r3 (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter AP3Free).sup Finset.card

theorem AP3Free.subset {s t : Finset ℕ} (hts : t ⊆ s) (hs : AP3Free s) :
    AP3Free t := fun a ha b hb c hc h => hs a (hts ha) b (hts hb) c (hts hc) h

theorem card_le_r3 {n : ℕ} {W : Finset ℕ} (hsub : W ⊆ Finset.Icc 1 n)
    (hfree : AP3Free W) : W.card ≤ r3 n := by
  unfold r3
  apply Finset.le_sup (f := Finset.card)
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hsub, hfree⟩

/-- **Subadditivity of r_3.** -/
theorem r3_subadd (a b : ℕ) : r3 (a + b) ≤ r3 a + r3 b := by
  apply Finset.sup_le
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨hSsub, hSfree⟩ := hS
  -- Lower block S ∩ {≤ a} lands in {1,…,a}.
  have h1 : (S.filter (fun x => x ≤ a)).card ≤ r3 a := by
    refine card_le_r3 ?_ (hSfree.subset (Finset.filter_subset _ _))
    intro x hx
    rw [Finset.mem_filter] at hx
    have hxIcc := hSsub hx.1
    rw [Finset.mem_Icc] at hxIcc ⊢
    exact ⟨hxIcc.1, hx.2⟩
  -- Upper block S ∩ {> a}, translated by −a, lands in {1,…,b} and stays AP-free.
  have hinj : Set.InjOn (fun x => x - a) (S.filter (fun x => ¬ x ≤ a)) := by
    intro x hx y hy h
    simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
    obtain ⟨_, hxa⟩ := hx
    obtain ⟨_, hya⟩ := hy
    dsimp only at h
    omega
  have h2 : (S.filter (fun x => ¬ x ≤ a)).card ≤ r3 b := by
    rw [← Finset.card_image_of_injOn hinj]
    refine card_le_r3 ?_ ?_
    · intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨x, hxf, rfl⟩ := hy
      rw [Finset.mem_filter] at hxf
      obtain ⟨hxS, hxa⟩ := hxf
      have hxIcc := hSsub hxS
      rw [Finset.mem_Icc] at hxIcc ⊢
      omega
    · intro a' ha' b' hb' c' hc' hAP
      rw [Finset.mem_image] at ha' hb' hc'
      obtain ⟨x, hx, rfl⟩ := ha'
      obtain ⟨y, hy, rfl⟩ := hb'
      obtain ⟨z, hz, rfl⟩ := hc'
      rw [Finset.mem_filter] at hx hy hz
      have hxz : x + z = 2 * y := by
        have hxa := hx.2; have hya := hy.2; have hza := hz.2
        omega
      have hxeqz : x = z := hSfree x hx.1 y hy.1 z hz.1 hxz
      omega
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := S) (p := fun x => x ≤ a)
  rw [← hsplit]
  exact Nat.add_le_add h1 h2

#print axioms r3_subadd

end Erdos142Sub
