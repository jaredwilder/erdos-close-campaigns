/-
Erdos problem 143 -- kernel-checked fragments.

Target (frozen): oracle/evidence/targets/lean-sources/FormalConjectures__ErdosProblems__143.lean
Statement source: oracle/evidence/targets/erdos-statements.json key "erdos:143",
  fetched 2026-08-10T09:18:02 from erdosproblems.com/latex/143.

`WellSeparatedSet` below is a byte-level transcription of the frozen
DeepMind formal-conjectures definition (namespace Erdos143, lines 34-36).

WHAT IS PROVED HERE (all sorry-free):
  * `one_le_dist`        k = 1 : a well-separated set is 1-separated.
  * `two_le_of_mem`      every element of an infinite well-separated set is >= 2.
  * `ncard_inter_Iio_le` |A cap (-inf, 2X)| <= ceil X            (the packing theorem)
  * `ncard_le_half`      |A cap (-inf, Y)| <= Y/2 + 1
  * `wellSeparated_ncard_le`  the same for `WellSeparatedSet`.

WHAT IS *NOT* PROVED HERE: neither `erdos_143.parts.i` (liminf density 0) nor
`erdos_143.parts.ii` (summability of 1/(x log x)).  The bound below is an upper
density bound of 1/2; the problem asks for a *lower* density statement.
-/
import Mathlib

open Set

namespace Erdos143Frag

/-- Frozen transcription of `Erdos143.WellSeparatedSet`. -/
def WellSeparatedSet (A : Set ℝ) : Prop :=
  (A ⊆ (Set.Ioi (1 : ℝ))) ∧ Set.Infinite A ∧ Set.Countable A ∧
  (∀ x ∈ A, ∀ y ∈ A, x ≠ y → (∀ k ≥ (1 : ℕ), 1 ≤ |k * x - y|))

/-- The separation core of `WellSeparatedSet`: the only part used by the packing
theorem.  Definitionally the fourth conjunct above. -/
def Sep (A : Set ℝ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ∀ k : ℕ, 1 ≤ k → 1 ≤ |(k : ℝ) * x - y|

theorem sep_of_wellSeparated {A : Set ℝ} (h : WellSeparatedSet A) : Sep A := h.2.2.2

private lemma one_le_two_pow_real (n : ℕ) : (1 : ℝ) ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; nlinarith

private lemma nat_le_two_pow_real (n : ℕ) : (n : ℝ) ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_two_pow_real k
      push_cast
      rw [pow_succ]
      nlinarith

/-- k = 1 : a well-separated set is 1-separated. -/
theorem one_le_dist {A : Set ℝ} (hs : Sep A) {x y : ℝ} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : x ≠ y) : 1 ≤ |x - y| := by
  have h := hs x hx y hy hxy 1 le_rfl
  simpa using h

/-- Every element of an infinite well-separated set is at least 2. -/
theorem two_le_of_mem {A : Set ℝ} (h : WellSeparatedSet A) {x : ℝ} (hx : x ∈ A) :
    2 ≤ x := by
  by_contra hcon
  push_neg at hcon
  have hs : Sep A := h.2.2.2
  have hx1 : 1 < x := h.1 hx
  obtain ⟨y, hy⟩ := (h.2.1.diff (Set.finite_singleton x)).nonempty
  have hyA : y ∈ A := hy.1
  have hyx : y ≠ x := by simpa using hy.2
  have hy1 : 1 < y := h.1 hyA
  have hxpos : (0 : ℝ) < x := by linarith
  rcases lt_trichotomy y x with hc | hc | hc
  · have hd : 1 ≤ |x - y| := one_le_dist hs hx hyA hyx.symm
    have : |x - y| < 1 := by rw [abs_lt]; constructor <;> linarith
    linarith
  · exact hyx hc
  · set k : ℕ := ⌊y / x⌋₊ with hk
    have hdivpos : (0 : ℝ) < y / x := div_pos (by linarith) hxpos
    have hk1 : 1 ≤ k := by
      apply Nat.le_floor
      rw [Nat.cast_one, le_div_iff₀ hxpos, one_mul]
      linarith
    have hfl : (k : ℝ) ≤ y / x := Nat.floor_le hdivpos.le
    have hfu : y / x < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hkle : (k : ℝ) * x ≤ y := by
      rw [le_div_iff₀ hxpos] at hfl; linarith
    have hklt : y < ((k : ℝ) + 1) * x := by
      rw [div_lt_iff₀ hxpos] at hfu; linarith
    by_cases hr : y - (k : ℝ) * x < 1
    · have hd := hs x hx y hyA hyx.symm k hk1
      have : |(k : ℝ) * x - y| < 1 := by rw [abs_lt]; constructor <;> linarith
      linarith
    · push_neg at hr
      have hd := hs x hx y hyA hyx.symm (k + 1) (by omega)
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hd
      have : |((k : ℝ) + 1) * x - y| < 1 := by
        rw [abs_lt]
        constructor <;> nlinarith
      linarith

/-- THE PACKING THEOREM.  For every `X > 0`, the number of elements of a
well-separated set below `2X` is at most `⌈X⌉₊`.

Proof: send each `a ∈ A` with `a < 2X` to `2 ^ m * a` where `m` is least with
`2 ^ m * a ≥ X`.  Minimality puts the image in `[X, 2X)`.  For `a ≠ b` with
`m b ≤ m a`, `|2^(m a) * a - 2^(m b) * b| = 2^(m b) * |2^(m a - m b) * a - b| ≥ 1`
by the defining property with `k = 2 ^ (m a - m b)`.  So the image is a
1-separated subset of an interval of length `X`, and `t ↦ ⌊t - X⌋₊` embeds it in
`range ⌈X⌉₊`. -/
theorem ncard_inter_Iio_le {A : Set ℝ} (hA1 : A ⊆ Set.Ioi (1 : ℝ)) (hs : Sep A)
    {X : ℝ} (hX : 0 < X) : (A ∩ Set.Iio (2 * X)).ncard ≤ ⌈X⌉₊ := by
  classical
  set S : Set ℝ := A ∩ Set.Iio (2 * X) with hSdef
  -- every `a ∈ S` admits an exponent placing `2 ^ m * a` in `[X, 2X)`
  have key : ∀ a ∈ S, ∃ m : ℕ, X ≤ 2 ^ m * a ∧ 2 ^ m * a < 2 * X := by
    intro a ha
    have ha1 : 1 < a := hA1 ha.1
    have ha2 : a < 2 * X := ha.2
    have hex : ∃ m : ℕ, X ≤ 2 ^ m * a := by
      obtain ⟨n, hn⟩ := exists_nat_ge X
      refine ⟨n, ?_⟩
      have h1 : (n : ℝ) ≤ 2 ^ n := nat_le_two_pow_real n
      have h2 : (2 : ℝ) ^ n ≤ 2 ^ n * a := by nlinarith [one_le_two_pow_real n]
      linarith
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simpa using ha2
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.find hex = n + 1 :=
        ⟨Nat.find hex - 1, by omega⟩
      have hmin : ¬ (X ≤ 2 ^ n * a) := Nat.find_min hex (by omega)
      push_neg at hmin
      rw [hn, pow_succ]
      nlinarith
  choose mm hlow hhigh using key
  -- the packing map
  set F : ℝ → ℕ := fun a => if h : a ∈ S then ⌊2 ^ (mm a h) * a - X⌋₊ else 0 with hF
  -- separation of the images
  have hsep : ∀ (a : ℝ) (ha : a ∈ S) (b : ℝ) (hb : b ∈ S), a ≠ b →
      1 ≤ |2 ^ (mm a ha) * a - 2 ^ (mm b hb) * b| := by
    have main : ∀ (a : ℝ) (ha : a ∈ S) (b : ℝ) (hb : b ∈ S), a ≠ b →
        mm b hb ≤ mm a ha → 1 ≤ |2 ^ (mm a ha) * a - 2 ^ (mm b hb) * b| := by
      intro a ha b hb hne hle
      set d : ℕ := mm a ha - mm b hb with hd
      have hsum : mm b hb + d = mm a ha := by omega
      have hcore := hs a ha.1 b hb.1 hne (2 ^ d) (Nat.one_le_pow d 2 (by norm_num))
      have hcast : (((2 : ℕ) ^ d : ℕ) : ℝ) = (2 : ℝ) ^ d := by push_cast; ring
      rw [hcast] at hcore
      have hfac : (2 : ℝ) ^ (mm a ha) * a - 2 ^ (mm b hb) * b
          = 2 ^ (mm b hb) * ((2 : ℝ) ^ d * a - b) := by
        rw [← hsum, pow_add]; ring
      rw [hfac, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 ^ (mm b hb))]
      nlinarith [one_le_two_pow_real (mm b hb), abs_nonneg ((2 : ℝ) ^ d * a - b)]
    intro a ha b hb hne
    rcases le_total (mm b hb) (mm a ha) with h | h
    · exact main a ha b hb hne h
    · rw [abs_sub_comm]; exact main b hb a ha hne.symm h
  -- injectivity
  have hinj : Set.InjOn F S := by
    intro a ha b hb hab
    by_contra hne
    have h1 : X ≤ 2 ^ (mm a ha) * a := hlow a ha
    have h2 : 2 ^ (mm a ha) * a < 2 * X := hhigh a ha
    have h3 : X ≤ 2 ^ (mm b hb) * b := hlow b hb
    have h4 : 2 ^ (mm b hb) * b < 2 * X := hhigh b hb
    have hFa : F a = ⌊2 ^ (mm a ha) * a - X⌋₊ := by simp [hF, ha]
    have hFb : F b = ⌊2 ^ (mm b hb) * b - X⌋₊ := by simp [hF, hb]
    have heq : (⌊2 ^ (mm a ha) * a - X⌋₊ : ℕ) = ⌊2 ^ (mm b hb) * b - X⌋₊ := by
      rw [← hFa, ← hFb]; exact hab
    have hga : ((⌊2 ^ (mm a ha) * a - X⌋₊ : ℕ) : ℝ) ≤ 2 ^ (mm a ha) * a - X :=
      Nat.floor_le (by linarith)
    have hgb : ((⌊2 ^ (mm b hb) * b - X⌋₊ : ℕ) : ℝ) ≤ 2 ^ (mm b hb) * b - X :=
      Nat.floor_le (by linarith)
    have hla : 2 ^ (mm a ha) * a - X < (⌊2 ^ (mm a ha) * a - X⌋₊ : ℕ) + 1 :=
      Nat.lt_floor_add_one _
    have hlb : 2 ^ (mm b hb) * b - X < (⌊2 ^ (mm b hb) * b - X⌋₊ : ℕ) + 1 :=
      Nat.lt_floor_add_one _
    rw [heq] at hga hla
    have hclose : |2 ^ (mm a ha) * a - 2 ^ (mm b hb) * b| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    have := hsep a ha b hb hne
    linarith
  -- the image lands in `Iio ⌈X⌉₊`
  have hmem : ∀ a ∈ S, F a ∈ (Set.Iio ⌈X⌉₊ : Set ℕ) := by
    intro a ha
    have h1 : X ≤ 2 ^ (mm a ha) * a := hlow a ha
    have h2 : 2 ^ (mm a ha) * a < 2 * X := hhigh a ha
    have hFa : F a = ⌊2 ^ (mm a ha) * a - X⌋₊ := by simp [hF, ha]
    have hle : ((⌊2 ^ (mm a ha) * a - X⌋₊ : ℕ) : ℝ) ≤ 2 ^ (mm a ha) * a - X :=
      Nat.floor_le (by linarith)
    have hceil : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
    have hlt : ((⌊2 ^ (mm a ha) * a - X⌋₊ : ℕ) : ℝ) < ((⌈X⌉₊ : ℕ) : ℝ) := by
      linarith
    have : ⌊2 ^ (mm a ha) * a - X⌋₊ < ⌈X⌉₊ := by exact_mod_cast hlt
    simpa [hFa] using this
  have hfin : (Set.Iio ⌈X⌉₊ : Set ℕ).Finite := Set.finite_Iio _
  have hcard := Set.ncard_le_ncard_of_injOn F hmem hinj hfin
  simpa using hcard

/-- The counting function of a well-separated set is at most `Y/2 + 1`. -/
theorem ncard_le_half {A : Set ℝ} (hA1 : A ⊆ Set.Ioi (1 : ℝ)) (hs : Sep A)
    {Y : ℝ} (hY : 0 < Y) : ((A ∩ Set.Iio Y).ncard : ℝ) ≤ Y / 2 + 1 := by
  have h := ncard_inter_Iio_le hA1 hs (X := Y / 2) (by linarith)
  have hrw : 2 * (Y / 2) = Y := by ring
  rw [hrw] at h
  have hceil : (⌈Y / 2⌉₊ : ℝ) < Y / 2 + 1 := Nat.ceil_lt_add_one (by linarith)
  have : ((A ∩ Set.Iio Y).ncard : ℝ) ≤ (⌈Y / 2⌉₊ : ℝ) := by exact_mod_cast h
  linarith

/-- Upper density at most one half, for the frozen predicate. -/
theorem wellSeparated_ncard_le {A : Set ℝ} (h : WellSeparatedSet A) {Y : ℝ}
    (hY : 0 < Y) : ((A ∩ Set.Iio Y).ncard : ℝ) ≤ Y / 2 + 1 :=
  ncard_le_half h.1 h.2.2.2 hY

end Erdos143Frag

-- AXIOM AUDIT (s.26.3 AXIOM.DIRTY check)
#print axioms Erdos143Frag.one_le_dist
#print axioms Erdos143Frag.two_le_of_mem
#print axioms Erdos143Frag.ncard_inter_Iio_le
#print axioms Erdos143Frag.ncard_le_half
#print axioms Erdos143Frag.wellSeparated_ncard_le
