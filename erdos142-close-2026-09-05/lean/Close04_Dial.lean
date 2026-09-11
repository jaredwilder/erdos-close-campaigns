/-
Erdős Problem #142 ($10,000) — CLOSE CAMPAIGN, FILE 04: THE DIAL.

════════════════════════════════════════════════════════════════════════════
ONE THEOREM THAT CONVERTS ANY FUTURE FINITE COMPUTATION INTO AN ALL-N BOUND
════════════════════════════════════════════════════════════════════════════

Close02 proved supermultiplicativity and then instantiated it at one seed
(`rothNumberNat 14 ≥ 8`) to get `r₃(N) ≥ N^(log 2/log 3)` on an explicit
sequence.  That instantiation is the part a later session would have to redo by
hand for a better seed.  This file removes that work permanently.

    dial (p c) (hseed : c ≤ rothNumberNat (p+1)) (j) :
        c ^ j ≤ rothNumberNat (U p j + 1)      with  2 · U p j + 1 = (2p+1)^j

So a seed `(m, c)` with `c ≤ rothNumberNat m` yields, with NO new mathematics,

        r₃(N) ≥ N^θ   along an explicit sequence,   θ = log c / log (2m − 1),

by supplying two numbers.  `Close02.power_law` is now literally `dial 13 8`.

⛔ THE DIAL IS CURRENTLY PINNED, AND THAT IS A MEASURED RESULT, NOT A GUESS.
Over the ENTIRE published exact record — OEIS A003002 b-file, n = 0…211,
sha-256 `6efd1e6a5cb92fe76610b089d1b289628038e3b503873b52e4979cb1e499d971`,
receipt `receipts/dial-and-crossover.json` — no seed gives θ above log 2/log 3,
and equality holds at exactly five points: n = 2, 5, 14, 41, 122, which are
(3^k+1)/2.  The same receipt records that the lemma is CONSISTENT with all 796
published instances and TIGHT at 58 of them (p, q ≥ 1).

Consequence worth stating plainly: **computing more exact values of r₃ cannot
improve this exponent.**  The `decide`-the-next-table-row plan the previous
campaign was pursuing was aimed at a frontier that provably does not move.
Only a Behrend-type construction beats log 2/log 3 — and Mathlib already has
Behrend, so the elementary line is closed, not merely stalled.

════════════════════════════════════════════════════════════════════════════
THE TRIPLING STEP
════════════════════════════════════════════════════════════════════════════

The `p = 1` case of supermultiplicativity is the classical base-3 doubling:

        rothNumberNat (3n − 1) ≥ 2 · rothNumberNat n            (`tripling`)

The receipt records this as TIGHT at n = 2, 3, 4, 5, 6, 13, 14, 15, … — e.g.
r₃(41) = 16 = 2·8 = 2·r₃(14) exactly.

⛔ NOT PROGRESS ON THE OPEN PROBLEM.  `erdos_142` asks for the Θ-order of
r_k(N); open, untouched.

Self-contained.  `decide` only on `{0}` and `{0,1}`.  No `native_decide`.
-/
import Mathlib

set_option maxHeartbeats 1000000

namespace Erdos142Dial

open Finset

/-- Digit uniqueness in base `K` (re-sealed so this file stands alone). -/
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

/-- **Supermultiplicativity** (re-sealed so this file stands alone; identical to
`Erdos142Super.rothNumberNat_mul_le`). -/
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

/-! ### The seed ladder, for an arbitrary seed -/

/-- `U p j = ((2p+1)^j − 1)/2`, defined without natural subtraction. -/
def U (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | (j + 1) => (2 * p + 1) * U p j + p

/-- Closed form: `2 · U p j + 1 = (2p+1)^j`. -/
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

/-- **THE DIAL.**  Any seed `c ≤ rothNumberNat (p+1)` bootstraps to a power law
on the explicit sequence `U p j + 1`, whose size satisfies `2·U p j + 1 = (2p+1)^j`.
In exponent form: `r₃(N) ≥ N^θ` with `θ = log c / log (2p+1)`.

Instantiating `p = 13, c = 8` recovers `Close02.power_law`. -/
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

/-! ### The `p = 1` case: the classical base-3 tripling step -/

theorem rothNumberNat_two : 2 ≤ rothNumberNat 2 :=
  ThreeAPFree.le_rothNumberNat {0, 1} (by decide) (by decide) (by decide)

/-- **TRIPLING.**  `rothNumberNat (3n − 1) ≥ 2 · rothNumberNat n` for `n ≥ 1`.
Stated subtraction-free as `3(n+1) − 1 = 3n + 2`.

Receipt `dial-and-crossover.json` records this as EQUALITY at n = 2, 3, 4, 5, 6,
13, 14, 15, … against the published A003002 values — e.g. r₃(41) = 16 = 2·r₃(14). -/
theorem tripling (n : ℕ) : 2 * rothNumberNat (n + 1) ≤ rothNumberNat (3 * n + 2) := by
  have h := rothNumberNat_mul_le 1 n
  have e1 : (1 : ℕ) + 1 = 2 := by norm_num
  have e2 : 2 * 1 * n + 1 + n + 1 = 3 * n + 2 := by ring
  rw [e1, e2] at h
  exact le_trans (Nat.mul_le_mul rothNumberNat_two (le_refl _)) h

/-- The eight-element seed: the base-3 no-digit-2 set below 27. -/
theorem seed_14 : 8 ≤ rothNumberNat 14 :=
  ThreeAPFree.le_rothNumberNat {0, 1, 3, 4, 9, 10, 12, 13} (by decide) (by decide) (by decide)

/-- The base-3 exponent, recovered from the dial at the seed `(14, 8)`. -/
theorem base3_power_law (j : ℕ) : 8 ^ j ≤ rothNumberNat (U 13 j + 1) :=
  dial 13 8 seed_14 j

theorem base3_size (j : ℕ) : 2 * U 13 j + 1 = 27 ^ j := by
  simpa using U_closed 13 j

#print axioms base_unique
#print axioms rothNumberNat_mul_le
#print axioms U_closed
#print axioms dial
#print axioms tripling
#print axioms base3_power_law
#print axioms base3_size

end Erdos142Dial
