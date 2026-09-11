/-
Erdős Problem 89 — the GAP LEDGER.

Rung 1 (`E89.lean`) proves `√n = O(minimalDistinctDistances n)`.
The open conjecture asks for `n/√(log n) = O(minimalDistinctDistances n)`.
This file measures the distance between the two, formally:

  * `sqrt_isBigO_target`    : √n = O(n/√(log n))      -- rung 1 is BELOW the target shape
  * `sqrt_isLittleO_target` : √n = o(n/√(log n))      -- and STRICTLY below
  * `target_implies_rung1`  : conjecture → rung 1     -- rung 1 is a necessary consequence

Consequence, stated so it cannot be misread: rung 1 is a genuine sub-statement of Erdős 89
that carries NO information about the conjecture itself.  Nothing in this campaign proves
or disproves `erdos_89`.
-/
import Mathlib

open Filter Asymptotics

/-- Rung 1 sits below the Erdős-89 target shape: `√n = O(n/√(log n))`. -/
theorem sqrt_isBigO_target :
    (fun n : ℕ => Real.sqrt n) =O[atTop] (fun n : ℕ => (n : ℝ) / Real.sqrt (Real.log n)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hL : 0 < Real.log n := Real.log_pos hn1
  have hLn : Real.log n ≤ (n : ℝ) := by
    have := Real.log_le_sub_one_of_pos hn0
    linarith
  have hsL : 0 < Real.sqrt (Real.log n) := Real.sqrt_pos.mpr hL
  rw [one_mul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ) / Real.sqrt (Real.log n)),
      le_div_iff₀ hsL, ← Real.sqrt_mul (le_of_lt hn0)]
  calc Real.sqrt ((n : ℝ) * Real.log n) ≤ Real.sqrt ((n : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = (n : ℝ) := Real.sqrt_sq (le_of_lt hn0)

/-- Rung 1 is STRICTLY below the target: `√n = o(n/√(log n))`. -/
theorem sqrt_isLittleO_target :
    (fun n : ℕ => Real.sqrt n) =o[atTop] (fun n : ℕ => (n : ℝ) / Real.sqrt (Real.log n)) := by
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (nhds 0) :=
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
  have hsq : Filter.Tendsto (fun n : ℕ => Real.sqrt (Real.log n / (n : ℝ))) atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hlog
    simpa [Function.comp_def] using h
  refine (Asymptotics.isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn hz
    exfalso
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hsL : 0 < Real.sqrt (Real.log n) := Real.sqrt_pos.mpr (Real.log_pos hn1)
    have hpos : (0:ℝ) < (n : ℝ) / Real.sqrt (Real.log n) := by positivity
    rw [hz] at hpos
    exact lt_irrefl 0 hpos
  · refine hsq.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hL : 0 < Real.log n := Real.log_pos hn1
    have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    rw [Real.sqrt_div (le_of_lt hL) (n : ℝ), div_div_eq_mul_div,
        div_eq_div_iff (ne_of_gt hsn) (ne_of_gt hn0)]
    nlinarith [Real.mul_self_sqrt (le_of_lt hn0), Real.sqrt_nonneg (Real.log (n : ℝ))]

/-- The conjecture implies rung 1, for any candidate growth function `g`.
So rung 1 is a NECESSARY consequence of Erdős 89 — never evidence for it. -/
theorem target_implies_rung1 {g : ℕ → ℝ}
    (h : (fun n : ℕ => (n : ℝ) / Real.sqrt (Real.log n)) =O[atTop] g) :
    (fun n : ℕ => Real.sqrt n) =O[atTop] g :=
  sqrt_isBigO_target.trans h

#print axioms sqrt_isBigO_target
#print axioms sqrt_isLittleO_target
#print axioms target_implies_rung1
