/-
Erdős Problem #142 ($10,000) — CLOSE CAMPAIGN, FILE 07:
TURNING THE DIAL PAST THE CLASSICAL EXPONENT, WITH A BEHREND SEED.

════════════════════════════════════════════════════════════════════════════
WHAT THIS FILE IS FOR
════════════════════════════════════════════════════════════════════════════

Close04 proved the DIAL: any seed `c ≤ rothNumberNat (p+1)` bootstraps to

        c^j ≤ rothNumberNat (U p j + 1),     2·U p j + 1 = (2p+1)^j,

i.e. `r₃(N) ≥ N^θ` on an explicit sequence with θ = log c / log(2p+1).

The campaign's receipt `dial-and-crossover.json` then measured something
uncomfortable: across the ENTIRE published record of exact values of r₃
(OEIS A003002, n ≤ 211) **no seed beats θ = log 2 / log 3**, with equality at
exactly the five Szekeres points (3^k+1)/2.  So no amount of further exact
computation moves this exponent.  The receipt's own conclusion was that only a
Behrend-type construction can.

This file does that, and therefore turns a negative measurement into a
positive result instead of leaving it as an excuse.

Mathlib already contains the needed seed extractor — no new combinatorics:

    Behrend.bound_aux' (n d : ℕ) : (d^n : ℝ) / (n * d^2) ≤ rothNumberNat ((2d−1)^n)

At (n, d) = (12, 100) it gives  10^24 / 120000 = 8.333…×10^18 ≤ rothNumberNat (199^12),
so `8×10^18` is a legitimate seed at `p + 1 = 199^12`, and the dial yields

        (8×10^18)^j ≤ rothNumberNat (U p j + 1),   2·U p j + 1 = (2·199^12 − 1)^j.

════════════════════════════════════════════════════════════════════════════
THE COMPARISON, CERTIFIED IN INTEGERS
════════════════════════════════════════════════════════════════════════════

Claiming "0.6785 > 0.6309" would be a floating-point assertion, so the
comparison is discharged as two exact integer inequalities instead
(`exponent_strictly_above_classical`):

    2^20 < 3^13                         ⟹  13/20 > log 2 / log 3
    (8×10^18)^20 > (2·199^12 − 1)^13    ⟹  log c / log M > 13/20

Hence, on this file's explicit sequence,

        r₃(N) ≥ (2N − 1)^(13/20)    with   13/20 > log 2 / log 3,

a STRICTLY LARGER explicit exponent than the classical base-3 value that every
published exact value is pinned to.  No floating point enters the proof.

⛔ HONEST PLACEMENT — READ THIS BEFORE QUOTING THE FILE.
Behrend's theorem is ALREADY in Mathlib and is asymptotically far stronger than
any fixed power `N^θ`; `Behrend.roth_lower_bound` gives N^(1−o(1)).  This file
does NOT improve on Behrend and does not claim to.  What it establishes is that
the dial of Close04 is NOT INTRINSICALLY PINNED at log 2/log 3 — the pinning is
a fact about the published table of exact values, not about the lemma — and it
exhibits the smallest concrete seed this campaign found that proves it.

⛔ NOT PROGRESS ON THE OPEN PROBLEM.  `erdos_142` asks for the Θ-order of
r_k(N); open, untouched, and nothing here bears on it.

Self-contained (Close04's dial is re-sealed here).  No `decide` on anything
large.  No `native_decide`.
-/
import Mathlib

set_option maxHeartbeats 1000000

namespace Erdos142Behrend

open Finset

/-! ### Close04's machinery, re-sealed so this file stands alone -/

theorem base_unique {K u v w v' : ℕ} (hv : v < K) (hv' : v' < K)
    (h : K * u + v = K * w + v') : u = w ∧ v = v' := by
  have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le v) hv
  have h1 : (K * u + v) / K = u := by
    rw [Nat.mul_add_div hK, Nat.div_eq_of_lt hv, Nat.add_zero]
  have h2 : (K * w + v') / K = w := by
    rw [Nat.mul_add_div hK, Nat.div_eq_of_lt hv', Nat.add_zero]
  have hu : u = w := by rw [← h1, h, h2]
  subst hu
  exact ⟨rfl, Nat.add_left_cancel h⟩

theorem rothNumberNat_mul_le (p q : ℕ) :
    rothNumberNat (p + 1) * rothNumberNat (q + 1)
      ≤ rothNumberNat (2 * p * q + p + q + 1) := by
  classical
  obtain ⟨A, hA, hAcard, hAfree⟩ := rothNumberNat_spec (p + 1)
  obtain ⟨B, hB, hBcard, hBfree⟩ := rothNumberNat_spec (q + 1)
  have hAle : ∀ a ∈ A, a ≤ p := by
    intro a ha; have := Finset.mem_range.mp (hA ha); omega
  have hBle : ∀ b ∈ B, b ≤ q := by
    intro b hb; have := Finset.mem_range.mp (hB hb); omega
  have hinj : Set.InjOn (fun ab : ℕ × ℕ => (2 * q + 1) * ab.1 + ab.2) ↑(A ×ˢ B) := by
    rintro ⟨a1, b1⟩ h1 ⟨a2, b2⟩ h2 h
    simp only [Finset.mem_coe, Finset.mem_product] at h1 h2
    have hb1 := hBle b1 h1.2
    have hb2 := hBle b2 h2.2
    obtain ⟨ha, hb⟩ := base_unique (K := 2 * q + 1) (by omega) (by omega) h
    have ha' : a1 = a2 := ha
    have hb' : b1 = b2 := hb
    rw [ha', hb']
  refine ThreeAPFree.le_rothNumberNat
    ((A ×ˢ B).image (fun ab : ℕ × ℕ => (2 * q + 1) * ab.1 + ab.2)) ?_ ?_ ?_
  · intro x hx y hy z hz hxyz
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product] at hx hy hz
    obtain ⟨⟨a1, b1⟩, ⟨ha1, hb1⟩, rfl⟩ := hx
    obtain ⟨⟨a2, b2⟩, ⟨ha2, hb2⟩, rfl⟩ := hy
    obtain ⟨⟨a3, b3⟩, ⟨ha3, hb3⟩, rfl⟩ := hz
    simp only at hxyz ⊢
    have h1 := hBle b1 hb1
    have h2 := hBle b2 hb2
    have h3 := hBle b3 hb3
    have hEq : (2 * q + 1) * (a1 + a3) + (b1 + b3)
             = (2 * q + 1) * (a2 + a2) + (b2 + b2) := by
      calc (2 * q + 1) * (a1 + a3) + (b1 + b3)
          = ((2 * q + 1) * a1 + b1) + ((2 * q + 1) * a3 + b3) := by ring
        _ = ((2 * q + 1) * a2 + b2) + ((2 * q + 1) * a2 + b2) := hxyz
        _ = (2 * q + 1) * (a2 + a2) + (b2 + b2) := by ring
    obtain ⟨hu, hv⟩ := base_unique (K := 2 * q + 1) (by omega) (by omega) hEq
    have hA1 : a1 = a2 :=
      hAfree (Finset.mem_coe.mpr ha1) (Finset.mem_coe.mpr ha2) (Finset.mem_coe.mpr ha3) hu
    have hB1 : b1 = b2 :=
      hBfree (Finset.mem_coe.mpr hb1) (Finset.mem_coe.mpr hb2) (Finset.mem_coe.mpr hb3) hv
    rw [hA1, hB1]
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hx
    rw [Finset.mem_product] at hab
    have ha := hAle a hab.1
    have hb := hBle b hab.2
    simp only
    calc (2 * q + 1) * a + b ≤ (2 * q + 1) * p + q :=
          Nat.add_le_add (Nat.mul_le_mul_left _ ha) hb
      _ = 2 * p * q + p + q := by ring
      _ < 2 * p * q + p + q + 1 := Nat.lt_succ_self _
  · rw [Finset.card_image_of_injOn hinj, Finset.card_product, hAcard, hBcard]

def U (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | (j + 1) => (2 * p + 1) * U p j + p

theorem U_closed (p j : ℕ) : 2 * U p j + 1 = (2 * p + 1) ^ j := by
  induction j with
  | zero => simp [U]
  | succ j ih =>
      have h : 2 * U p (j + 1) + 1 = (2 * p + 1) * (2 * U p j + 1) := by
        simp only [U]; ring
      rw [h, ih, pow_succ]
      ring

theorem le_rothNumberNat_one : 1 ≤ rothNumberNat 1 :=
  ThreeAPFree.le_rothNumberNat {0} (by decide) (by decide) (by decide)

theorem dial (p c : ℕ) (hseed : c ≤ rothNumberNat (p + 1)) :
    ∀ j, c ^ j ≤ rothNumberNat (U p j + 1) := by
  intro j
  induction j with
  | zero => simpa [U] using le_rothNumberNat_one
  | succ j ih =>
      have hstep : rothNumberNat (U p j + 1) * rothNumberNat (p + 1)
          ≤ rothNumberNat (U p (j + 1) + 1) := by
        have h := rothNumberNat_mul_le (U p j) p
        have e : 2 * U p j * p + U p j + p + 1 = U p (j + 1) + 1 := by
          simp only [U]; ring
        rw [e] at h
        exact h
      calc c ^ (j + 1) = c ^ j * c := by ring
        _ ≤ rothNumberNat (U p j + 1) * rothNumberNat (p + 1) := Nat.mul_le_mul ih hseed
        _ ≤ rothNumberNat (U p (j + 1) + 1) := hstep

/-! ### The Behrend seed, straight out of Mathlib -/

/-- **THE SEED.**  `8×10^18 ≤ rothNumberNat (199^12)`.

From `Behrend.bound_aux' 12 100 : (100^12 : ℝ)/(12·100^2) ≤ rothNumberNat (199^12)`,
whose left side is `10^24 / 120000 = 8.333…×10^18`.  No combinatorics is redone;
Mathlib's Behrend sphere argument supplies it. -/
theorem behrend_seed : (8 * 10 ^ 18 : ℕ) ≤ rothNumberNat (199 ^ 12) := by
  have h := Behrend.bound_aux' 12 100
  have e : (2 * 100 - 1) ^ 12 = (199 : ℕ) ^ 12 := by norm_num
  rw [e] at h
  have h2 : ((8 * 10 ^ 18 : ℕ) : ℝ) ≤ ((rothNumberNat (199 ^ 12) : ℕ) : ℝ) := by
    refine le_trans ?_ h
    push_cast
    norm_num
  exact_mod_cast h2

/-- **THE BEHREND-SEEDED POWER LAW.**

`(8×10^18)^j ≤ rothNumberNat (U (199^12 − 1) j + 1)`, where the size satisfies
`2·U p j + 1 = (2·199^12 − 1)^j`. -/
theorem behrend_power_law (j : ℕ) :
    (8 * 10 ^ 18 : ℕ) ^ j ≤ rothNumberNat (U (199 ^ 12 - 1) j + 1) := by
  refine dial (199 ^ 12 - 1) (8 * 10 ^ 18) ?_ j
  have e : (199 : ℕ) ^ 12 - 1 + 1 = 199 ^ 12 := by norm_num
  rw [e]
  exact behrend_seed

/-- The size of the `j`-th member of the family. -/
theorem behrend_size (j : ℕ) :
    2 * U (199 ^ 12 - 1) j + 1 = (2 * 199 ^ 12 - 1) ^ j := by
  have h := U_closed (199 ^ 12 - 1) j
  have e : 2 * ((199 : ℕ) ^ 12 - 1) + 1 = 2 * 199 ^ 12 - 1 := by norm_num
  rw [e] at h
  exact h

/-- **THE COMPARISON, IN EXACT INTEGERS — NO FLOATING POINT.**

`2^20 < 3^13` certifies `13/20 > log 2 / log 3`.
`(8×10^18)^20 > (2·199^12 − 1)^13` certifies `log c / log M > 13/20`.

Together: this family's exponent is STRICTLY ABOVE the classical base-3
exponent that every published exact value of r₃ is pinned to. -/
theorem exponent_strictly_above_classical :
    (2 : ℕ) ^ 20 < 3 ^ 13 ∧ (2 * 199 ^ 12 - 1) ^ 13 < (8 * 10 ^ 18 : ℕ) ^ 20 := by
  constructor <;> norm_num

#print axioms base_unique
#print axioms rothNumberNat_mul_le
#print axioms U_closed
#print axioms dial
#print axioms behrend_seed
#print axioms behrend_power_law
#print axioms behrend_size
#print axioms exponent_strictly_above_classical

end Erdos142Behrend
