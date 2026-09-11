/-
Erdős Problem #142 ($10,000) — ATTACK 07.

════════════════════════════════════════════════════════════════════════════
BREAKING THE ½ BARRIER: the first seed with density ratio BELOW one half.
════════════════════════════════════════════════════════════════════════════

Attack 05 proved the bootstrap `r_3(m) ≤ k  ⟹  ∀ n, m·r_3(n) ≤ k·n + m·k`,
and could only instantiate it at r_3(8) = 4, giving the constant ½. Every
entry of the sealed table 1..14 has ratio ≥ ½ (min = 4/8 = 5/10 = 6/12 = ½),
so ½ was the ceiling of everything the campaign had.

The first ratios strictly below ½ live at n = 17, 18, 19:

        r_3(17) = 8   →  8/17 ≈ 0.4706
        r_3(18) = 8   →  8/18 ≈ 0.4444
        r_3(19) = 8   →  8/19 ≈ 0.4211

all beyond the 2^n powerset wall that stopped Attack 03 at n = 14
(12m09s, 31 GB). Attack 06's cardinality-slice reduction is what puts them in
reach: the UPPER bound `r_3(17) ≤ 8` only needs the single slice
`powersetCard 9`, i.e. C(17,9) = 24,310 subsets rather than 2^17 = 131,072.

This file seals `r_3(17) ≤ 8` and spends it:

        ∀ n,  17 · r_3(n) ≤ 8 · n + 136          (`r3_seed17`)

i.e. r_3(n) ≤ (8/17)·n + 8 ≈ 0.4706·n + 8 — strictly better than Attack 05's
½·n + 4 for every n > 136, and the first sub-½ density constant in the
campaign.

⛔ STILL NOT PROGRESS ON THE OPEN PROBLEM. Roth gives r_3(n) = o(n); every
constant of this kind is infinitely weaker. What this demonstrates is that the
density constant is now a DIAL driven by a finite kernel computation — each new
sealed slice turns it down, with no new mathematics. `erdos_142` and its
variants remain untouched `answer(sorry)` holes.

Self-contained. `decide` over ONE cardinality slice. No `native_decide`.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000000

namespace Erdos142Seed17

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

theorem r3_mono {m n : ℕ} (hmn : m ≤ n) : r3 m ≤ r3 n := by
  unfold r3
  refine Finset.sup_mono ?_
  intro s hs
  rw [Finset.mem_filter, Finset.mem_powerset] at hs ⊢
  exact ⟨hs.1.trans (Finset.Icc_subset_Icc_right hmn), hs.2⟩

/-! ### Attack 06's slice reduction (re-sealed so this file stands alone) -/

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

theorem r3_le_of_powersetCard {n k : ℕ}
    (H : ∀ T ∈ (Finset.Icc 1 n).powersetCard (k + 1), ¬ AP3Free T) :
    r3 n ≤ k := by
  apply r3_le_of_no_free_card
  intro T hTsub hTcard
  exact H T (Finset.mem_powersetCard.mpr ⟨hTsub, hTcard⟩)

/-! ### Attack 04's subadditivity (re-sealed so this file stands alone) -/

theorem r3_subadd (a b : ℕ) : r3 (a + b) ≤ r3 a + r3 b := by
  apply Finset.sup_le
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨hSsub, hSfree⟩ := hS
  have h1 : (S.filter (fun x => x ≤ a)).card ≤ r3 a := by
    refine card_le_r3 ?_ (hSfree.subset (Finset.filter_subset _ _))
    intro x hx
    rw [Finset.mem_filter] at hx
    have hxIcc := hSsub hx.1
    rw [Finset.mem_Icc] at hxIcc ⊢
    exact ⟨hxIcc.1, hx.2⟩
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

theorem r3_linear_of_seed {m k : ℕ} (hm : 0 < m) (hseed : r3 m ≤ k) :
    ∀ n, m * r3 n ≤ k * n + m * k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < m
    · have h1 : r3 n ≤ k := le_trans (r3_mono (le_of_lt hn)) hseed
      calc m * r3 n ≤ m * k := Nat.mul_le_mul (le_refl m) h1
        _ ≤ k * n + m * k := Nat.le_add_left _ _
    · push_neg at hn
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
      have hj : j < m + j := by omega
      have ihj := ih j hj
      have hexp : m * r3 (m + j) ≤ m * r3 m + m * r3 j := by
        have h := Nat.mul_le_mul (le_refl m) (r3_subadd m j)
        rwa [Nat.mul_add] at h
      have hmk : m * r3 m ≤ m * k := Nat.mul_le_mul (le_refl m) hseed
      calc m * r3 (m + j) ≤ m * r3 m + m * r3 j := hexp
        _ ≤ m * k + (k * j + m * k) := Nat.add_le_add hmk ihj
        _ = k * (m + j) + m * k := by ring

/-! ### THE NEW SEED — one cardinality slice, C(17,9) = 24,310 subsets -/

/-- **`r_3(17) ≤ 8`.** No 9-element subset of `{1,…,17}` is 3-AP-free.
Kernel `decide` over `powersetCard 9 (Icc 1 17)` — 24,310 sets, versus
2^17 = 131,072 for the powerset method Attack 03 used. -/
theorem r3_17_le_8 : r3 17 ≤ 8 := r3_le_of_powersetCard (by decide)

/-- **The sub-½ constant.** `17 · r_3(n) ≤ 8·n + 136` for every `n`,
i.e. `r_3(n) ≤ (8/17)·n + 8 ≈ 0.4706·n + 8`. -/
theorem r3_seed17 (n : ℕ) : 17 * r3 n ≤ 8 * n + 136 := by
  have h := r3_linear_of_seed (m := 17) (k := 8) (by norm_num) r3_17_le_8 n
  omega

#print axioms r3_le_of_powersetCard
#print axioms r3_subadd
#print axioms r3_linear_of_seed
#print axioms r3_17_le_8
#print axioms r3_seed17

end Erdos142Seed17
