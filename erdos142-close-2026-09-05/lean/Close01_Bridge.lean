/-
Erdős Problem #142 ($10,000) — CLOSE CAMPAIGN, FILE 01: THE BRIDGE.

════════════════════════════════════════════════════════════════════════════
WHAT WAS WRONG WITH THE PREVIOUS CAMPAIGN, AND WHAT THIS FIXES
════════════════════════════════════════════════════════════════════════════

Campaign `erdos142-lean-2026-09-05` (Attacks 01–07) built a PRIVATE definition

    r3 n := sup { #S | S ⊆ Icc 1 n, S is 3-AP-free }

and then re-proved, by hand, monotonicity, the deletion step, and
subadditivity, and sealed the exact table r₃(1..14) by kernel `decide`.
Its own TERMINAL.json recorded the gap honestly:

    "machine-checked identity r3 == Set.IsAPOfLengthFree.maxCard 3 —
     correspondence is documented/faithful, NOT PROVEN"

That gap is the whole load-bearing question: an unbridged private definition
means every sealed number is a number about a definition this campaign wrote
for itself.  It is not yet a number about Erdős #142.

MEASURED FACT (this session): **Mathlib ALREADY CONTAINS the canonical object.**

    rothNumberNat : ℕ →o ℕ            Mathlib/Combinatorics/Additive/AP/Three/Defs.lean
    rothNumberNat n = addRothNumber (Finset.range n)

together with

    rothNumberNat_add_le          — subadditivity, i.e. Attack 04's `r3_subadd`
    rothNumberNat.mono            — i.e. Attack 01's `r3_mono`
    rothNumberNat_le              — i.e. Attack 05's `r3_le_self`
    ThreeAPFree.le_rothNumberNat  — i.e. Attack 01's `r3_ge_of_witness`
    Behrend.roth_lower_bound      — N·exp(−4√log N) ≤ rothNumberNat N
    rothNumberNat_isLittleO_id    — ROTH'S THEOREM, rothNumberNat N = o(N)

So Attacks 01, 04, 05 re-proved four lemmas Mathlib already had, against a
definition that was never connected to Mathlib's.  This file connects them.

════════════════════════════════════════════════════════════════════════════
THE BRIDGE
════════════════════════════════════════════════════════════════════════════

        theorem r3_eq_rothNumberNat (n : ℕ) : r3 n = rothNumberNat n

Consequences, all immediate once the bridge is sealed:

 • the campaign's kernel-`decide` table r₃(1..14) becomes a table of EXACT
   VALUES OF `rothNumberNat` — of Mathlib's own object, not of a local def;
 • Roth's theorem and Behrend's bound apply to `r3` verbatim (`r3_isLittleO_id`,
   `r3_behrend_lower` below), so the campaign inherits the two hardest results
   in the area instead of re-deriving weaker ones;
 • any future exact value can be stated in the canonical vocabulary and is
   upstreamable.

⛔ SCOPE.  This does NOT touch the open asymptotic.  `erdos_142`,
`erdos_142.variants.upper` and `erdos_142.variants.three` are `answer(sorry)`
holes in the frozen spec and remain open.  Mathlib brackets r₃ between
Behrend below and Roth above; the Θ-order asked for by #142 is unknown.

⛔ ONE RESIDUAL GAP, STATED PLAINLY.  The frozen spec phrases #142 via
`Erdos142.r = Set.IsAPOfLengthFree.maxCard`, which lives in
`FormalConjecturesUtil` — absent from this toolchain, so it cannot be imported
and the identity `rothNumberNat = Erdos142.r 3` is NOT machine-checked here.
What IS machine-checked is the bridge to Mathlib's canonical `rothNumberNat`,
which is a strictly stronger anchor than the private `r3` the campaign had.

Self-contained.  No `decide` on anything large.  No `native_decide`.
-/
import Mathlib

set_option maxHeartbeats 1000000

namespace Erdos142Bridge

open Finset

/-- The campaign's private predicate (verbatim from Attacks 01–07). -/
def AP3Free (s : Finset ℕ) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a + c = 2 * b → a = c

instance (s : Finset ℕ) : Decidable (AP3Free s) := by
  unfold AP3Free; infer_instance

/-- The campaign's private Roth number (verbatim from Attacks 01–07). -/
def r3 (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter AP3Free).sup Finset.card

/-- **Step 1.** The campaign's predicate is Mathlib's `ThreeAPFree`.

Mathlib phrases 3-AP-freeness as `a + c = b + b → a = b`; the campaign phrased
it as `a + c = 2*b → a = c`.  Over ℕ these are the same statement. -/
theorem ap3Free_iff (s : Finset ℕ) : AP3Free s ↔ ThreeAPFree (↑s : Set ℕ) := by
  constructor
  · intro h a ha b hb c hc habc
    rw [Finset.mem_coe] at ha hb hc
    have hac : a = c := h a ha b hb c hc (by omega)
    omega
  · intro h a ha b hb c hc habc
    have h1 : a = b :=
      h (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) (Finset.mem_coe.mpr hc) (by omega)
    omega

/-- **Step 2.** The campaign's `sup`-over-`powerset` construction agrees with
Mathlib's `Nat.findGreatest`-based `addRothNumber` on the ground set. -/
theorem r3_eq_addRothNumber (n : ℕ) : r3 n = addRothNumber (Finset.Icc 1 n) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro s hs
    rw [Finset.mem_filter, Finset.mem_powerset] at hs
    exact ((ap3Free_iff s).mp hs.2).le_addRothNumber hs.1
  · obtain ⟨t, hts, htcard, htfree⟩ := addRothNumber_spec (Finset.Icc 1 n)
    rw [← htcard]
    apply Finset.le_sup (f := Finset.card)
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hts, (ap3Free_iff t).mpr htfree⟩

/-- **THE BRIDGE.**  The campaign's private `r3` IS Mathlib's `rothNumberNat`.

`{1,…,n}` and `{0,…,n−1}` are translates, and `addRothNumber` is translation
invariant (`addRothNumber_Ico`). -/
theorem r3_eq_rothNumberNat (n : ℕ) : r3 n = rothNumberNat n := by
  rw [r3_eq_addRothNumber]
  have hIcc : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by ext x; simp
  rw [hIcc, addRothNumber_Ico]
  simp

/-! ### What the bridge buys, immediately -/

/-- **ROTH'S THEOREM, transported to the campaign's object.**
`r₃(N) = o(N)` — inherited from Mathlib, not re-derived. -/
theorem r3_isLittleO_id :
    (fun N => (r3 N : ℝ)) =o[Filter.atTop] (fun N => (N : ℝ)) := by
  simpa only [r3_eq_rothNumberNat] using rothNumberNat_isLittleO_id

/-- **BEHREND'S LOWER BOUND, transported to the campaign's object.**
`N·exp(−4√(log N)) ≤ r₃(N)` — inherited from Mathlib. -/
theorem r3_behrend_lower (N : ℕ) :
    (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) ≤ (r3 N : ℝ) := by
  simpa only [r3_eq_rothNumberNat] using (Behrend.roth_lower_bound (N := N))

/-- **The campaign's sealed table, transported.**  Any exact value sealed for
the private `r3` is an exact value of Mathlib's `rothNumberNat`, and conversely.
Stated hypothetically so that this file costs no `decide`: Attack 03 sealed
`r3 14 = 8` at 12 min / 31 GB, and re-running it here would buy nothing. -/
theorem rothNumberNat_of_r3 {n v : ℕ} (h : r3 n = v) : rothNumberNat n = v := by
  rw [← r3_eq_rothNumberNat]; exact h

/-- Direction actually used downstream: a sealed upper bound transports. -/
theorem rothNumberNat_le_of_r3_le {n v : ℕ} (h : r3 n ≤ v) : rothNumberNat n ≤ v := by
  rw [← r3_eq_rothNumberNat]; exact h

/-- Mathlib already has the campaign's Attack 04 (`r3_subadd`), now available
for `r3` through the bridge rather than by a hand proof. -/
theorem r3_subadd (a b : ℕ) : r3 (a + b) ≤ r3 a + r3 b := by
  simpa only [r3_eq_rothNumberNat] using rothNumberNat_add_le a b

/-- Mathlib already has the campaign's Attack 01 (`r3_mono`). -/
theorem r3_mono {m n : ℕ} (h : m ≤ n) : r3 m ≤ r3 n := by
  simpa only [r3_eq_rothNumberNat] using rothNumberNat.mono h

#print axioms ap3Free_iff
#print axioms r3_eq_addRothNumber
#print axioms r3_eq_rothNumberNat
#print axioms r3_isLittleO_id
#print axioms r3_behrend_lower
#print axioms rothNumberNat_of_r3
#print axioms rothNumberNat_le_of_r3_le
#print axioms r3_subadd
#print axioms r3_mono

end Erdos142Bridge
