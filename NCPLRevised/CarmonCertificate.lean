/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.CarmonDifferentiability
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Numerical certificates for the outer Carmon chain

This closes the numerical constant in the revised paper's terminal-obstruction
and initial-gap proposition.  It depends only on the outer chain modules.
-/

namespace NCPLRevised

noncomputable section

open MeasureTheory

theorem integral_carmonGaussian :
    (∫ s : ℝ, carmonGaussian s) = Real.sqrt (2 * Real.pi) := by
  simpa [carmonGaussian, div_eq_mul_inv, mul_comm] using
    (integral_gaussian (1 / 2 : ℝ))

theorem carmonTermCap_lt_twelve : carmonTermCap < 12 := by
  rw [carmonTermCap, carmonPhiCap, integral_carmonGaussian]
  have he0 : 0 ≤ Real.exp (1 : ℝ) := (Real.exp_pos _).le
  have hp0 : 0 ≤ 2 * Real.pi := mul_nonneg (by norm_num) Real.pi_nonneg
  have hs1 : Real.sqrt (Real.exp 1) ^ 2 = Real.exp 1 :=
    Real.sq_sqrt he0
  have hs2 : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt hp0
  have he : Real.exp (1 : ℝ) < 11 / 4 := by
    exact Real.exp_one_lt_d9.trans (by norm_num)
  have hp : Real.pi < 22 / 7 := by
    exact Real.pi_lt_d4.trans (by norm_num)
  have hsq :
      (Real.exp 1 * (Real.sqrt (Real.exp 1) * Real.sqrt (2 * Real.pi))) ^ 2 <
        (12 : ℝ) ^ 2 := by
    rw [mul_pow, mul_pow, hs1, hs2]
    have hprod :
        Real.exp 1 ^ 2 * Real.exp 1 * (2 * Real.pi) <
          (11 / 4 : ℝ) ^ 2 * (11 / 4) * (2 * (22 / 7)) := by
      gcongr
    nlinarith
  have hnonneg :
      0 ≤ Real.exp 1 * (Real.sqrt (Real.exp 1) * Real.sqrt (2 * Real.pi)) := by
    positivity
  nlinarith

/-- The exact C4 constant from the revised paper. -/
theorem carmon_initial_gap_twelve (T : ℕ) :
    carmonF T 0 - sInf (Set.range (carmonF T)) ≤ 12 * (T : ℝ) := by
  have hgap := carmon_initial_gap T
  have hT : 0 ≤ (T : ℝ) := by positivity
  have hcap : carmonTermCap ≤ 12 := carmonTermCap_lt_twelve.le
  nlinarith

/-- The three analytic conclusions of Proposition 5.3 for the explicit value
function: actual Fréchet gradient, terminal obstruction, and C4 gap. -/
theorem carmon_terminal_gap_certificate (T : ℕ) (hT : 0 < T) :
    (∀ x : EVec T,
      HasCarmonFDerivAt (carmonF T) (evecDot (carmonGradient T x)) x) ∧
    (∀ x : EVec T,
      x (carmonLastIndex T hT) = 0 → 1 ≤ vecSq (carmonGradient T x)) ∧
    carmonF T 0 - sInf (Set.range (carmonF T)) ≤ 12 * (T : ℝ) := by
  exact ⟨hasEVecFDerivAt_carmonF_gradient T,
    one_le_vecSq_carmonGradient_of_terminal_zero hT,
    carmon_initial_gap_twelve T⟩

end

end NCPLRevised
