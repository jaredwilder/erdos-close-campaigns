/-
Erdős Problem 89 — rung 1: an elementary Ω(√n) lower bound for `minimalDistinctDistances`.

CANONICAL STATEMENT (erdosproblems.com/89, $500, OPEN):
  Does every set of n distinct points in ℝ² determine ≫ n/√(log n) distinct distances?

Formal target (DeepMind formal-conjectures, ErdosProblems/89.lean, `@[category research open]`):
  (fun n => n / (n:ℝ).log.sqrt) =O[atTop] (fun n => (minimalDistinctDistances n : ℝ))

THIS FILE DOES NOT PROVE THAT.  It proves the strictly weaker, elementary bound
  (fun n => Real.sqrt n) =O[atTop] (fun n => (minimalDistinctDistances n : ℝ))
i.e. minimalDistinctDistances n ≫ √n, which is the 1946 Erdős "two circles meet twice"
pigeonhole.  The best known result is Guth–Katz 2015 (≫ n/log n); the conjecture is open.

`distinctDistances` and `minimalDistinctDistances` below are transcribed VERBATIM from
FormalConjecturesForMathlib/Geometry/2d.lean so the statement is semantically bound;
`minimalDistinctDistances_eq_natSInf` discharges the ℝ-cast in the set-builder.
-/
import Mathlib

open Finset EuclideanGeometry Filter Asymptotics

noncomputable abbrev R2 := EuclideanSpace ℝ (Fin 2)

/-- VERBATIM from FormalConjecturesForMathlib/Geometry/2d.lean. -/
noncomputable def distinctDistances (points : Finset R2) : ℕ :=
  #(points.offDiag.image fun (pair : R2 × R2) => dist pair.1 pair.2)

/-- VERBATIM from FormalConjecturesForMathlib/Geometry/2d.lean. -/
noncomputable def minimalDistinctDistances (n : ℕ) : ℕ :=
  sInf {(distinctDistances points : ℝ) | (points : Finset R2) (_ : points.card = n)}

/-- Statement firewall: the ℝ-cast inside the imported set-builder is inert; the definition
is the ℕ-valued infimum one expects. -/
lemma minimalDistinctDistances_eq_natSInf (n : ℕ) :
    minimalDistinctDistances n
      = sInf {k : ℕ | ∃ points : Finset R2, #points = n ∧ distinctDistances points = k} := by
  unfold minimalDistinctDistances
  congr 1
  ext k
  simp [Nat.cast_inj]

instance : Infinite R2 := by
  obtain ⟨v, hv⟩ : ∃ v : R2, v ≠ 0 := exists_ne 0
  refine Infinite.of_injective (fun r : ℝ => r • v) ?_
  intro a b hab
  have hz : (a - b) • v = 0 := by
    rw [sub_smul]
    simp only at hab
    rw [hab, sub_self]
  rcases smul_eq_zero.mp hz with h | h
  · linarith
  · exact absurd h hv

/-- Two circles with distinct centres meet in at most two points: the fibres of
`x ↦ (dist x p, dist x q)` have at most two elements when `p ≠ q`. -/
lemma fiber_card_le_two (p q : R2) (hpq : p ≠ q) (S : Finset R2) (r s : ℝ) :
    #({a ∈ S | (dist a p, dist a q) = (r, s)}) ≤ 2 := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hcon
  simp only [Finset.mem_filter, Prod.mk.injEq] at ha hb hc
  have hfr : Module.finrank ℝ R2 = 2 := by simp
  rcases EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hfr hpq hab
      ha.2.1 hb.2.1 hc.2.1 ha.2.2 hb.2.2 hc.2.2 with h1 | h1
  · exact hac h1.symm
  · exact hbc h1.symm

/-- **Erdős 1946 (easy half), finite form.** Any finite planar point set `P` satisfies
`#P ≤ 2·(number of distinct distances)² + 2`. -/
theorem card_le_two_mul_distinctDistances_sq (P : Finset R2) :
    #P ≤ 2 * (distinctDistances P) ^ 2 + 2 := by
  by_cases hsmall : #P ≤ 2
  · omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < #P)
  set D : Finset ℝ := P.offDiag.image (fun pr : R2 × R2 => dist pr.1 pr.2) with hDdef
  have hdd : distinctDistances P = #D := rfl
  set S : Finset R2 := P \ {p, q} with hSdef
  have hmaps : ∀ a ∈ S, (dist a p, dist a q) ∈ D ×ˢ D := by
    intro a ha
    rw [hSdef, Finset.mem_sdiff] at ha
    obtain ⟨haP, hanot⟩ := ha
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hanot
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(a, p), Finset.mem_offDiag.mpr ⟨haP, hp, hanot.1⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨(a, q), Finset.mem_offDiag.mpr ⟨haP, hq, hanot.2⟩, rfl⟩
  have hfib : ∀ b ∈ D ×ˢ D, #({a ∈ S | (dist a p, dist a q) = b}) ≤ 2 := by
    rintro ⟨r, s⟩ -
    exact fiber_card_le_two p q hpq S r s
  have hcard : #S ≤ 2 * #(D ×ˢ D) :=
    Finset.card_le_mul_card_image_of_maps_to hmaps 2 hfib
  have hprod : #(D ×ˢ D) = #D * #D := Finset.card_product D D
  have hsub : ({p, q} : Finset R2) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hpq2 : #({p, q} : Finset R2) = 2 := Finset.card_pair hpq
  have hsplit : #S + 2 = #P := by
    have h := Finset.card_sdiff_add_card_eq_card hsub
    rw [hpq2] at h
    rw [hSdef]
    exact h
  rw [hdd, pow_two]
  omega

/-- The imported infimum is attained, and inherits the finite bound. -/
theorem le_two_mul_minimalDistinctDistances_sq (n : ℕ) :
    n ≤ 2 * (minimalDistinctDistances n) ^ 2 + 2 := by
  have hne : {k : ℕ | ∃ points : Finset R2, #points = n ∧ distinctDistances points = k}.Nonempty := by
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq R2 n
    exact ⟨distinctDistances s, s, hs, rfl⟩
  rw [minimalDistinctDistances_eq_natSInf]
  obtain ⟨pts, hc, hk⟩ := Nat.sInf_mem hne
  rw [← hk, ← hc]
  exact card_le_two_mul_distinctDistances_sq pts

/-- Explicit form: for `n ≥ 4`, `√n ≤ 2 · minimalDistinctDistances n`. -/
theorem sqrt_le_two_mul_minimalDistinctDistances {n : ℕ} (hn : 4 ≤ n) :
    Real.sqrt n ≤ 2 * (minimalDistinctDistances n : ℝ) := by
  have h := le_two_mul_minimalDistinctDistances_sq n
  set k := minimalDistinctDistances n with hk
  have hnat : n ≤ 4 * k ^ 2 := by
    set m := k ^ 2 with hm
    omega
  have hcast : (n : ℝ) ≤ (2 * (k : ℝ)) ^ 2 := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    nlinarith [this]
  calc Real.sqrt n ≤ Real.sqrt ((2 * (k : ℝ)) ^ 2) := Real.sqrt_le_sqrt hcast
    _ = 2 * (k : ℝ) := Real.sqrt_sq (by positivity)

/-- **Rung 1 for Erdős 89.**  `minimalDistinctDistances n ≫ √n`.
This is strictly weaker than the open conjecture (`n/√(log n)`) and strictly weaker
than Guth–Katz (`n/log n`); it is the elementary bound, formalized. -/
theorem sqrt_isBigO_minimalDistinctDistances :
    (fun n : ℕ => Real.sqrt n) =O[atTop] (fun n : ℕ => (minimalDistinctDistances n : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop 4] with n hn
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_natCast]
  exact sqrt_le_two_mul_minimalDistinctDistances hn

#print axioms sqrt_isBigO_minimalDistinctDistances
#print axioms card_le_two_mul_distinctDistances_sq
#print axioms minimalDistinctDistances_eq_natSInf
