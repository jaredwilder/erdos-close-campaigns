/-
Erdős Problem #142 ($10,000) — ATTACK 05.

════════════════════════════════════════════════════════════════════════════
WHY A NEW ATTACK: THE `decide` LINE IS DEAD, AND THE SEALED SUBADDITIVITY
WAS NEVER SPENT.
════════════════════════════════════════════════════════════════════════════

Attacks 01–03 sealed the EXACT table r_3(1..14) by kernel `decide` over the
full powerset of {1,…,n}. That line is now DEAD as a frontier, measured, not
guessed: n = 14 cost 12m09s wall and **31 GB peak RSS** (A3.time). The cost is
2^n subsets MATERIALIZED AS KERNEL TERMS, so n = 15 needs >20 min and >40 GB
and buys exactly one more table row. A finite table, however long, never
reaches an asymptotic — and the asymptotic is the whole of Erdős #142.

Attack 04 sealed subadditivity, r_3(a+b) ≤ r_3(a) + r_3(b), and then STOPPED.
Nothing consumed it. That is the live line, and this file spends it.

════════════════════════════════════════════════════════════════════════════
THE TECHNIQUE: FEKETE-STYLE SEED BOOTSTRAP (finite fact → all-n theorem)
════════════════════════════════════════════════════════════════════════════

Subadditivity turns ONE finite computed value into a bound for EVERY n:

    r_3(m) ≤ k   ⟹   ∀ n,  m · r_3(n) ≤ k · n + m · k          (`r3_linear_of_seed`)

i.e. r_3(n) ≤ (k/m)·n + k. The upper DENSITY CONSTANT of r_3 is thereby
reduced to a finite kernel computation: any single sealed table entry with
r_3(m)/m < ½ improves the constant for free, by re-instantiating this one
theorem. No new mathematics is needed to profit from a better table — which
is precisely what the dead `decide` line could not offer.

Instantiating at the cheapest good seed, r_3(8) = 4 (2^8 = 256 subsets, sub-second):

    ∀ n,  2 · r_3(n) ≤ n + 8          (`r3_half`)        ← the headline

This is the FIRST statement in this campaign true for ALL n rather than for a
finite table. It is elementary and FAR weaker than Roth (r_3(n) = o(n)); it is
NOT progress on the open asymptotic. It is a sealed, unconditional, explicit
upper bound where the campaign previously had none.

Second line, independent of subadditivity — the deletion step:

    r_3(n+1) ≤ r_3(n) + 1             (`r3_succ_le`)
    r_3(m) ≤ c  →  m ≤ n  →  r_3(n) ≤ c + (n − m)        (`r3_le_of_anchor`)

Composed with Attack 03's sealed r_3(14) = 8 this gives r_3(n) ≤ n − 6, which
BEATS the n/2 + 4 bound for every n < 20. (Stated abstractly here: importing
the concrete r_3(14) = 8 would re-incur Attack 03's 12-minute `decide`.)

════════════════════════════════════════════════════════════════════════════
SCOPE / HONESTY
════════════════════════════════════════════════════════════════════════════
`erdos_142`, `variants.lower`, `variants.three` are `answer(sorry)` holes in
the frozen spec (FormalConjectures/ErdosProblems/142.lean) — genuinely open,
Roth/Behrend territory, NOT targeted here and NOT closed by anything below.

`r3` is a faithful pure-Mathlib reconstruction of the k = 3 case of
`Erdos142.r = Set.IsAPOfLengthFree.maxCard` over the explicit ground set
{1,…,n}. `FormalConjecturesUtil` is absent on this toolchain, so the
correspondence is DOCUMENTED, not machine-checked. The reconstruction is
cross-checked against OEIS A003002 (r_3(1..14) = 1,2,2,3,4,4,4,4,5,5,6,6,7,8),
which the sealed table of Attacks 01–03 reproduces exactly.

Self-contained. `decide` used once, on r_3(8) only. No `native_decide`.
-/
import Mathlib

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace Erdos142Boot

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

/-- Trivial ceiling: `r_3(n) ≤ n`. -/
theorem r3_le_self (n : ℕ) : r3 n ≤ n := by
  unfold r3
  apply Finset.sup_le
  intro s hs
  rw [Finset.mem_filter, Finset.mem_powerset] at hs
  have := Finset.card_le_card hs.1
  simpa using this

/-! ### Line 1 — subadditivity (Attack 04, re-sealed here so the file stands alone) -/

/-- **Subadditivity.** `r_3(a+b) ≤ r_3(a) + r_3(b)`: split an optimal set at the
block boundary; the upper block translates by `−a` into `{1,…,b}`, and
`x + z = 2y` is translation invariant. -/
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
  -- NOTE: deprecated alias deliberately retained — this exact name is the one
  -- PROVEN to compile on this toolchain (Attack04, A4.log: warning, exit 0).
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := S) (p := fun x => x ≤ a)
  rw [← hsplit]
  exact Nat.add_le_add h1 h2

/-! ### Line 2 — the deletion step and its anchored ladder -/

/-- **Deletion step.** `r_3(n+1) ≤ r_3(n) + 1`: delete `n+1` from an optimal
set; what remains is 3-AP-free inside `{1,…,n}`. -/
theorem r3_succ_le (n : ℕ) : r3 (n + 1) ≤ r3 n + 1 := by
  apply Finset.sup_le
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨hSsub, hSfree⟩ := hS
  have hEsub : S.erase (n + 1) ⊆ Finset.Icc 1 n := by
    intro x hx
    rw [Finset.mem_erase] at hx
    have hxI := hSsub hx.2
    rw [Finset.mem_Icc] at hxI ⊢
    omega
  have hEfree : AP3Free (S.erase (n + 1)) := by
    intro a ha b hb c hc h
    exact hSfree a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
      c (Finset.mem_of_mem_erase hc) h
  have hcard : (S.erase (n + 1)).card ≤ r3 n := card_le_r3 hEsub hEfree
  have hins : S ⊆ insert (n + 1) (S.erase (n + 1)) := by
    intro x hx
    by_cases hx1 : x = n + 1
    · subst hx1; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hx1, hx⟩)
  have h1 := Finset.card_le_card hins
  have h2 := Finset.card_insert_le (n + 1) (S.erase (n + 1))
  omega

/-- Slope-1 ladder: `r_3(m + j) ≤ r_3(m) + j`. -/
theorem r3_add_le (m j : ℕ) : r3 (m + j) ≤ r3 m + j := by
  induction j with
  | zero => simp
  | succ t iht =>
    have hs := r3_succ_le (m + t)
    have he : m + (t + 1) = (m + t) + 1 := by omega
    rw [he]
    omega

/-- **Anchored ladder.** An upper bound at one point propagates upward at
slope 1. With Attack 03's sealed `r_3(14) = 8` this yields `r_3(n) ≤ n − 6`. -/
theorem r3_le_of_anchor {m c : ℕ} (h : r3 m ≤ c) {n : ℕ} (hn : m ≤ n) :
    r3 n ≤ c + (n - m) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  have := r3_add_le m j
  omega

/-! ### The bootstrap — one finite seed becomes an all-`n` linear bound -/

/-- **SEED BOOTSTRAP (the reduction).** A single computed value `r_3(m) ≤ k`
bounds `r_3` linearly for EVERY `n`:  `m · r_3(n) ≤ k · n + m · k`,
i.e. `r_3(n) ≤ (k/m)·n + k`.

The upper density constant of `r_3` is thus reduced to a FINITE kernel
computation: any sealed table entry with `r_3(m)/m` smaller than the current
best improves the constant by re-instantiating this theorem alone. -/
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

/-- The cheapest seed that achieves density ½: `r_3(8) = 4`, i.e. 2^8 = 256
subsets — sub-second, against Attack 03's 12 minutes for one further row. -/
theorem r3_8_le_4 : r3 8 ≤ 4 := by decide

/-- **HEADLINE.** `2 · r_3(n) ≤ n + 8` for EVERY `n`, i.e. `r_3(n) ≤ n/2 + 4`.

The first unconditional all-`n` bound in this campaign. Elementary, and far
weaker than Roth's `r_3(n) = o(n)`; it does not touch the open asymptotic. -/
theorem r3_half (n : ℕ) : 2 * r3 n ≤ n + 8 := by
  have h := r3_linear_of_seed (m := 8) (k := 4) (by norm_num) r3_8_le_4 n
  omega

#print axioms r3_le_self
#print axioms r3_subadd
#print axioms r3_succ_le
#print axioms r3_add_le
#print axioms r3_le_of_anchor
#print axioms r3_linear_of_seed
#print axioms r3_8_le_4
#print axioms r3_half

end Erdos142Boot
