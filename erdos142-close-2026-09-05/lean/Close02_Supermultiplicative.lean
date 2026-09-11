/-
Erdős Problem #142 ($10,000) — CLOSE CAMPAIGN, FILE 02:
SUPERMULTIPLICATIVITY OF THE ROTH NUMBER, AND THE EXPLICIT POWER LAW.

════════════════════════════════════════════════════════════════════════════
THE ASYMMETRY THIS FILE REPAIRS
════════════════════════════════════════════════════════════════════════════

Mathlib has the UPPER half of the elementary theory of `rothNumberNat`:

    rothNumberNat_add_le : rothNumberNat (M + N) ≤ rothNumberNat M + rothNumberNat N

(subadditivity — which is also, verbatim, what campaign Attack 04 spent a day
re-proving by hand for a private definition).  It has NOTHING corresponding on
the LOWER side except Behrend's construction, which is asymptotic and whose
stated bound `N·exp(−4√log N) ≤ rothNumberNat N` is VACUOUS at every N a person
would compute with (at N = 365 it asserts `0.0219 ≤ rothNumberNat 365`).

The missing companion is SUPERMULTIPLICATIVITY.  It is absent from Mathlib
(searched: `Mathlib/Combinatorics/Additive/AP/Three/{Defs,Behrend}.lean`,
`Corner/Roth.lean`), and it is what turns one finite computation into an
unconditional power-law lower bound for infinitely many explicit N.

    rothNumberNat (p+1) * rothNumberNat (q+1) ≤ rothNumberNat (2pq + p + q + 1)

CONSTRUCTION.  Take A ⊆ {0,…,p} and B ⊆ {0,…,q} both 3-AP-free and extremal,
and lay B out in base 2q+1:

    C = { (2q+1)·a + b : a ∈ A, b ∈ B }  ⊆ {0,…,2pq+p+q}.

Base 2q+1 is the exact threshold, not a safety margin: if
(2q+1)(a₁+a₃) + (b₁+b₃) = (2q+1)(2a₂) + 2b₂ then both remainders b₁+b₃ and 2b₂
lie in [0, 2q] ⊂ [0, 2q+1), so the digits CANNOT carry, and the single
equation splits into two independent ones — one killed by A being 3-AP-free,
the other by B.  A smaller base admits a carry and the lemma is false; base 2q
would already fail.

⛔ WHY THE `+1`s AND NOT `rothNumberNat m * rothNumberNat n ≤ rothNumberNat (2mn)`.
Because the natural-subtraction-free form is the honest one, and because plain
supermultiplicativity `rothNumberNat (mn) ≥ rothNumberNat m · rothNumberNat n`
is FALSE: m = n = 2 gives rothNumberNat 4 = 3 < 4 = 2·2.  The `2pq+p+q+1` form
is TIGHT at several small points — (p,q) = (1,1) gives 4 ≤ rothNumberNat 5 = 4,
and (1,3) gives 6 ≤ rothNumberNat 11 = 6 — both equalities (OEIS A003002).

════════════════════════════════════════════════════════════════════════════
THE PAYOFF: AN EXPLICIT INFINITE FAMILY, FROM ONE 8-ELEMENT WITNESS
════════════════════════════════════════════════════════════════════════════

Define T 0 = 0, T (j+1) = 27·T j + 13   (so 2·T j + 1 = 27^j, proved below).
Feeding the single seed `8 ≤ rothNumberNat 14` — witnessed by the eight-element
set {0,1,3,4,9,10,12,13}, the base-3 no-digit-2 set — through the product lemma
j times gives, unconditionally and kernel-checked:

        ∀ j,  8^j ≤ rothNumberNat (T j + 1)      with  2·(T j) + 1 = 27^j

i.e.  r₃(N) ≥ N^(log 2 / log 3) = N^0.63092…  for the explicit N = (27^j+1)/2.

⛔ HONEST PLACEMENT.  This is the classical Szekeres/base-3 exponent, not new
mathematics; Behrend (1946) gives N^(1−o(1)), infinitely better ASYMPTOTICALLY,
and Mathlib already has it.  Three things are nevertheless true and are the
reason this file exists:

  (1) supermultiplicativity itself is a lemma Mathlib does not have, and it is
      the exact companion of the subadditivity Mathlib does have;
  (2) at every explicit N in this family below roughly 10^51, the bound proved
      here is enormously STRONGER than what Mathlib's `Behrend.roth_lower_bound`
      states (64 versus 0.022 at N = 365) — Behrend's stated form only overtakes
      it around j ≈ 36.  See receipt `dial-and-crossover.json`;
  (3) it is a DIAL: a better seed (m, c) raises the exponent to log c / log(2m−1)
      by re-instantiating one theorem, with no new mathematics.

⛔ AND THE DIAL IS PINNED — MEASURED, NOT ASSUMED.  Over the ENTIRE published
record of exact values (OEIS A003002 b-file, n = 0…211), NO seed beats
log 2 / log 3, and equality is attained exactly at n = 2, 5, 14, 41, 122 —
the points (3^k+1)/2.  So the finite computational front, as published today,
CANNOT improve this exponent; only a Behrend-type construction can.  That is a
measured negative result about this attack line, and it is why the campaign's
`decide`-the-next-table-row plan was the wrong frontier.

⛔ NOT PROGRESS ON THE OPEN PROBLEM.  `erdos_142` asks for the Θ-order of
r_k(N); it is open and untouched here.

Self-contained.  `decide` used only on two explicit small finsets.
No `native_decide`.
-/
import Mathlib

set_option maxHeartbeats 1000000

namespace Erdos142Super

open Finset

/-- Digit uniqueness in base `K`: if two base-`K` two-digit numbers agree and
both low digits are proper digits, the high and low digits agree separately.
This is the entire content of "there is no carry". -/
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

/-- **SUPERMULTIPLICATIVITY OF THE ROTH NUMBER.**

    rothNumberNat (p+1) * rothNumberNat (q+1) ≤ rothNumberNat (2*p*q + p + q + 1)

The lower-side companion to Mathlib's `rothNumberNat_add_le`. -/
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
  -- the base-(2q+1) layout
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
  · -- the image is 3-AP-free
    intro x hx y hy z hz hxyz
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
  · -- the image lands in {0, …, 2pq+p+q}
    intro x hx
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
  · -- the layout is injective, so the cardinality multiplies
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, hAcard, hBcard]

/-! ### The seed: one explicit eight-element witness -/

/-- `{0,1,3,4,9,10,12,13}` — the integers below 27 whose base-3 expansion has no
digit 2 — is 3-AP-free and lives inside `{0,…,13}`, so `rothNumberNat 14 ≥ 8`.
Independently recomputed by `tools/r3_exact.py` and matching OEIS A003002. -/
theorem seed_14 : 8 ≤ rothNumberNat 14 :=
  ThreeAPFree.le_rothNumberNat {0, 1, 3, 4, 9, 10, 12, 13} (by decide) (by decide) (by decide)

theorem seed_1 : 1 ≤ rothNumberNat 1 :=
  ThreeAPFree.le_rothNumberNat {0} (by decide) (by decide) (by decide)

/-! ### The explicit family -/

/-- `T j = (27^j − 1)/2`, defined without natural subtraction. -/
def T : ℕ → ℕ
  | 0 => 0
  | (j + 1) => 27 * T j + 13

/-- Closed form: `2·T j + 1 = 27^j`.  So `T j + 1 = (27^j + 1)/2`. -/
theorem T_closed (j : ℕ) : 2 * T j + 1 = 27 ^ j := by
  induction j with
  | zero => simp [T]
  | succ j ih =>
      have : 2 * T (j + 1) + 1 = 27 * (2 * T j + 1) := by simp only [T]; ring
      rw [this, ih, pow_succ]
      ring

/-- **THE POWER LAW.**  `8^j ≤ rothNumberNat (T j + 1)`, where `2·T j + 1 = 27^j`.

Equivalently `r₃(N) ≥ N^(log 2/log 3)` for the explicit sequence
`N = (27^j+1)/2 = 1, 14, 365, 9842, 265721, …`.

Unconditional, kernel-checked, and driven by a single eight-element witness. -/
theorem power_law (j : ℕ) : 8 ^ j ≤ rothNumberNat (T j + 1) := by
  induction j with
  | zero => simpa [T] using seed_1
  | succ j ih =>
      have hstep : rothNumberNat (T j + 1) * rothNumberNat 14
          ≤ rothNumberNat (T (j + 1) + 1) := by
        have h := rothNumberNat_mul_le (T j) 13
        have e1 : (13 : ℕ) + 1 = 14 := by norm_num
        have e2 : 2 * T j * 13 + T j + 13 + 1 = T (j + 1) + 1 := by
          simp only [T]; ring
        rw [e1, e2] at h
        exact h
      calc 8 ^ (j + 1) = 8 ^ j * 8 := by ring
        _ ≤ rothNumberNat (T j + 1) * rothNumberNat 14 := Nat.mul_le_mul ih seed_14
        _ ≤ rothNumberNat (T (j + 1) + 1) := hstep

/-- The same statement with the size made explicit: for every `j` there is an
`N` with `2N − 1 = 27^j` and `rothNumberNat N ≥ 8^j`. -/
theorem power_law_explicit (j : ℕ) :
    ∃ N : ℕ, 2 * N = 27 ^ j + 1 ∧ 8 ^ j ≤ rothNumberNat N := by
  refine ⟨T j + 1, ?_, power_law j⟩
  have := T_closed j
  omega

/-- Sanity instances of the family, in closed numerals. -/
theorem roth_365 : 64 ≤ rothNumberNat 365 := by
  have h := power_law 2
  norm_num [T] at h
  exact h

theorem roth_9842 : 512 ≤ rothNumberNat 9842 := by
  have h := power_law 3
  norm_num [T] at h
  exact h

/-- Tightness check at the bottom of the ladder: `(p,q) = (1,1)` gives
`rothNumberNat 2 * rothNumberNat 2 ≤ rothNumberNat 5`, and A003002 says
`rothNumberNat 2 = 2`, `rothNumberNat 5 = 4` — so the lemma is SHARP here. -/
theorem sharp_at_five : rothNumberNat 2 * rothNumberNat 2 ≤ rothNumberNat 5 := by
  have h := rothNumberNat_mul_le 1 1
  norm_num at h
  exact h

#print axioms base_unique
#print axioms rothNumberNat_mul_le
#print axioms seed_14
#print axioms T_closed
#print axioms power_law
#print axioms power_law_explicit
#print axioms roth_365
#print axioms roth_9842
#print axioms sharp_at_five

end Erdos142Super
