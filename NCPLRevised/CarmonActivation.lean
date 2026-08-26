/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.CarmonCertificate
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The outer scale and lifted target (Lemmas 4.5 and 4.6)

This file replaces the square root in
`rho(s) = sqrt (psi(s) + psi(-s))` by the equal sum of two flat
half-exponential gates.  This exposes genuine derivatives at the two splice
points and gives explicit global bounds.  It also verifies the exact
three-region formula and admissibility inequalities for the lifted target.
-/

namespace NCPLRevised

noncomputable section

open Filter Polynomial Real Set

/-! ## A smooth square root of the one-sided gate -/

def expNegHalfInvSqGlue (x : ℝ) : ℝ :=
  expNegInvSqGlue (Real.sqrt 2 * x)

def expNegHalfInvSqGlueDeriv (x : ℝ) : ℝ :=
  Real.sqrt 2 * expNegInvSqGlueDeriv (Real.sqrt 2 * x)

def expNegHalfInvSqGlueSecond (x : ℝ) : ℝ :=
  2 * expNegInvSqGlueSecond (Real.sqrt 2 * x)

theorem sqrt_two_pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem sqrt_two_sq : Real.sqrt (2 : ℝ) ^ 2 = 2 := by norm_num

theorem hasDerivAt_expNegHalfInvSqGlue (x : ℝ) :
    HasDerivAt expNegHalfInvSqGlue (expNegHalfInvSqGlueDeriv x) x := by
  unfold expNegHalfInvSqGlue expNegHalfInvSqGlueDeriv
  have harg : HasDerivAt (fun t : ℝ ↦ Real.sqrt 2 * t) (Real.sqrt 2) x :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul (Real.sqrt 2)
  have h := (hasDerivAt_expNegInvSqGlue (Real.sqrt 2 * x)).comp x harg
  convert h using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext t
    rfl
  · ring

theorem hasDerivAt_expNegHalfInvSqGlueDeriv (x : ℝ) :
    HasDerivAt expNegHalfInvSqGlueDeriv (expNegHalfInvSqGlueSecond x) x := by
  unfold expNegHalfInvSqGlueDeriv expNegHalfInvSqGlueSecond
  have harg : HasDerivAt (fun t : ℝ ↦ Real.sqrt 2 * t) (Real.sqrt 2) x :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul (Real.sqrt 2)
  have hcomp := (hasDerivAt_expNegInvSqGlueDeriv (Real.sqrt 2 * x)).comp x harg
  have h := hcomp.const_mul (Real.sqrt 2)
  convert h using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext t
    rfl
  · nth_rewrite 1 [← sqrt_two_sq]
    ring

theorem expNegHalfInvSqGlue_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    expNegHalfInvSqGlue x = 0 := by
  unfold expNegHalfInvSqGlue
  apply expNegInvSqGlue_of_nonpos
  exact mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) hx

theorem expNegHalfInvSqGlueDeriv_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    expNegHalfInvSqGlueDeriv x = 0 := by
  unfold expNegHalfInvSqGlueDeriv expNegInvSqGlueDeriv
  rw [if_pos (mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) hx)]
  ring

theorem expNegHalfInvSqGlue_nonneg (x : ℝ) :
    0 ≤ expNegHalfInvSqGlue x := expNegInvSqGlue_nonneg _

theorem expNegHalfInvSqGlue_le_one (x : ℝ) :
    expNegHalfInvSqGlue x ≤ 1 := expNegInvSqGlue_le_one _

theorem expNegHalfInvSqGlue_sq (x : ℝ) :
    expNegHalfInvSqGlue x ^ 2 = expNegInvSqGlue x := by
  by_cases hx : x ≤ 0
  · simp [expNegHalfInvSqGlue_of_nonpos hx, expNegInvSqGlue_of_nonpos hx]
  · have hxpos : 0 < x := lt_of_not_ge hx
    have hsx : 0 < Real.sqrt 2 * x := mul_pos sqrt_two_pos hxpos
    unfold expNegHalfInvSqGlue expNegInvSqGlue
    rw [if_neg hsx.not_ge, if_neg hx]
    rw [pow_two, ← Real.exp_add]
    congr 1
    field_simp [sqrt_two_pos.ne', hxpos.ne']
    nlinarith [sqrt_two_sq]

/-! The flat splice is in fact `C∞`.  We prove this directly, rather than
appealing only to the two displayed derivatives: multiplying the gate by
any polynomial in `x⁻¹` still tends to zero at the splice, and
differentiation preserves this family. -/

private theorem tendsto_pow_mul_exp_neg_sq_atTop_activation (n : Nat) :
    Tendsto (fun x : ℝ ↦ x ^ n * Real.exp (-(x ^ 2))) atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxx : x ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
    have he : Real.exp (-(x ^ 2)) ≤ Real.exp (-x) := by
      exact Real.exp_le_exp.mpr (by linarith)
    exact mul_le_mul_of_nonneg_left he (pow_nonneg (by linarith) _)
  · exact Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n

private theorem tendsto_inv_pow_mul_expNegInvSqGlue_zero_activation (n : Nat) :
    Tendsto (fun x : ℝ ↦ (x⁻¹) ^ n * expNegInvSqGlue x)
      (nhds 0) (nhds 0) := by
  simp only [expNegInvSqGlue, mul_ite, mul_zero]
  refine tendsto_const_nhds.if ?_
  simp only [not_le]
  have h := (tendsto_pow_mul_exp_neg_sq_atTop_activation n).comp
    tendsto_inv_nhdsGT_zero
  exact h.congr' (by filter_upwards with x using rfl)

private theorem tendsto_polynomial_inv_mul_expNegInvSqGlue_zero_activation
    (p : ℝ[X]) :
    Tendsto (fun x : ℝ ↦ p.eval x⁻¹ * expNegInvSqGlue x)
      (nhds 0) (nhds 0) := by
  induction p using Polynomial.induction_on' with
  | monomial n c =>
      simpa [eval_monomial, mul_assoc] using
        (tendsto_inv_pow_mul_expNegInvSqGlue_zero_activation n).const_mul c
  | add p q hp hq =>
      simpa [eval_add, add_mul] using hp.add hq

private theorem hasDerivAt_polynomial_inv_mul_expNegInvSqGlue_activation
    (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun x ↦ p.eval x⁻¹ * expNegInvSqGlue x)
      ((X ^ 2 * (2 * X * p - derivative p)).eval x⁻¹ *
        expNegInvSqGlue x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [expNegInvSqGlue_of_nonpos hx.le, mul_zero]
    refine (hasDerivAt_const _ 0).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    rw [expNegInvSqGlue_of_nonpos hy.le, mul_zero]
  · rw [expNegInvSqGlue_zero, mul_zero, hasDerivAt_iff_tendsto_slope]
    refine ((tendsto_polynomial_inv_mul_expNegInvSqGlue_zero_activation
      (X * p)).mono_left inf_le_left).congr fun x ↦ ?_
    simp [slope_def_field, div_eq_mul_inv, mul_right_comm]
    ring_nf
  · have hp := (p.hasDerivAt x⁻¹).comp x (hasDerivAt_inv hx.ne')
    have hf := hasDerivAt_expNegInvSqGlue x
    have h := hp.mul hf
    convert! h.congr_of_eventuallyEq _ using 1
    · simp only [eval_mul, eval_pow, eval_X, inv_pow, eval_sub, eval_ofNat,
        mul_neg, neg_mul, Function.comp_apply]
      rw [expNegInvSqGlue, if_neg hx.not_ge]
      rw [expNegInvSqGlueDeriv, if_neg hx.not_ge]
      ring_nf
    · filter_upwards [Ioi_mem_nhds hx] with y hy
      rfl

@[fun_prop] theorem contDiff_expNegInvSqGlue {n : ℕ∞} :
    ContDiff ℝ n expNegInvSqGlue := by
  have hpoly : ∀ (p : ℝ[X]), ContDiff ℝ n
      (fun x ↦ p.eval x⁻¹ * expNegInvSqGlue x) := by
    intro p
    apply contDiff_all_iff_nat.2 (fun m => ?_) n
    induction m generalizing p with
    | zero =>
      have hd : Differentiable ℝ
          (fun x ↦ p.eval x⁻¹ * expNegInvSqGlue x) :=
        fun x ↦
          (hasDerivAt_polynomial_inv_mul_expNegInvSqGlue_activation p x).differentiableAt
      exact contDiff_zero.2 hd.continuous
    | succ m ihm =>
      rw [Nat.cast_succ]
      refine contDiff_succ_iff_deriv.2 ⟨
        (fun x ↦
          (hasDerivAt_polynomial_inv_mul_expNegInvSqGlue_activation p x).differentiableAt),
          ?_, ?_⟩
      · simp
      · convert! ihm (X ^ 2 * (2 * X * p - derivative p)) using 2
        exact (hasDerivAt_polynomial_inv_mul_expNegInvSqGlue_activation p _).deriv
  simpa using hpoly 1

@[fun_prop] theorem contDiff_expNegHalfInvSqGlue {n : ℕ∞} :
    ContDiff ℝ n expNegHalfInvSqGlue := by
  unfold expNegHalfInvSqGlue
  exact contDiff_expNegInvSqGlue.comp (by fun_prop)

/-- The paper's `theta`: its square is exactly `psi`. -/
def carmonTheta (t : ℝ) : ℝ :=
  Real.sqrt (Real.exp 1) * expNegHalfInvSqGlue (2 * t - 1)

def carmonThetaDeriv (t : ℝ) : ℝ :=
  2 * Real.sqrt (Real.exp 1) * expNegHalfInvSqGlueDeriv (2 * t - 1)

def carmonThetaSecond (t : ℝ) : ℝ :=
  4 * Real.sqrt (Real.exp 1) * expNegHalfInvSqGlueSecond (2 * t - 1)

theorem carmonTheta_nonneg (t : ℝ) : 0 ≤ carmonTheta t :=
  mul_nonneg (Real.sqrt_nonneg _) (expNegHalfInvSqGlue_nonneg _)

theorem carmonTheta_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) :
    carmonTheta t = 0 := by
  unfold carmonTheta
  rw [expNegHalfInvSqGlue_of_nonpos (by linarith)]
  ring

theorem carmonThetaDeriv_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) :
    carmonThetaDeriv t = 0 := by
  unfold carmonThetaDeriv
  rw [expNegHalfInvSqGlueDeriv_of_nonpos (by linarith)]
  ring

@[simp] theorem carmonTheta_zero : carmonTheta 0 = 0 := by
  apply carmonTheta_of_le_half
  norm_num

theorem carmonTheta_sq (t : ℝ) : carmonTheta t ^ 2 = carmonPsi t := by
  unfold carmonTheta carmonPsi
  rw [mul_pow, Real.sq_sqrt (Real.exp_pos 1).le,
    expNegHalfInvSqGlue_sq]

theorem carmonTheta_mul_neg (t : ℝ) :
    carmonTheta t * carmonTheta (-t) = 0 := by
  by_cases ht : t ≤ 1 / 2
  · rw [carmonTheta_of_le_half ht]
    ring
  · have hneg : -t ≤ 1 / 2 := by linarith
    rw [carmonTheta_of_le_half hneg]
    ring

theorem hasDerivAt_carmonTheta (t : ℝ) :
    HasDerivAt carmonTheta (carmonThetaDeriv t) t := by
  unfold carmonTheta carmonThetaDeriv
  have harg : HasDerivAt (fun s : ℝ ↦ 2 * s - 1) 2 t := by
    simpa [mul_comm] using ((hasDerivAt_id t).const_mul 2 |>.sub_const 1)
  have hcomp := (hasDerivAt_expNegHalfInvSqGlue (2 * t - 1)).comp t harg
  have h := hcomp.const_mul (Real.sqrt (Real.exp 1))
  convert h using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext s
    rfl
  · ring

theorem hasDerivAt_carmonThetaDeriv (t : ℝ) :
    HasDerivAt carmonThetaDeriv (carmonThetaSecond t) t := by
  unfold carmonThetaDeriv carmonThetaSecond
  have harg : HasDerivAt (fun s : ℝ ↦ 2 * s - 1) 2 t := by
    simpa [mul_comm] using ((hasDerivAt_id t).const_mul 2 |>.sub_const 1)
  have hcomp := (hasDerivAt_expNegHalfInvSqGlueDeriv (2 * t - 1)).comp t harg
  have h := hcomp.const_mul (2 * Real.sqrt (Real.exp 1))
  convert h using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext s
    rfl
  · ring

theorem differentiable_carmonTheta : Differentiable ℝ carmonTheta :=
  fun t ↦ (hasDerivAt_carmonTheta t).differentiableAt

theorem differentiable_carmonThetaDeriv : Differentiable ℝ carmonThetaDeriv :=
  fun t ↦ (hasDerivAt_carmonThetaDeriv t).differentiableAt

@[fun_prop] theorem contDiff_carmonTheta {n : ℕ∞} :
    ContDiff ℝ n carmonTheta := by
  unfold carmonTheta
  fun_prop

theorem deriv_carmonTheta (t : ℝ) : deriv carmonTheta t = carmonThetaDeriv t :=
  (hasDerivAt_carmonTheta t).deriv

/-! ## Explicit bounds for the scale and its derivative -/

private theorem pow_four_mul_exp_neg_sq_le_two (u : ℝ) :
    u ^ 4 * Real.exp (-(u ^ 2)) ≤ 2 := by
  have h := Real.pow_div_factorial_le_exp (u ^ 2) (sq_nonneg u) 2
  norm_num [div_eq_mul_inv] at h
  have hpow : (u ^ 2) ^ 2 ≤ 2 * Real.exp (u ^ 2) := by nlinarith
  have hdiv := (div_le_iff₀ (Real.exp_pos (u ^ 2))).2 hpow
  rw [Real.exp_neg]
  change u ^ 4 * (Real.exp (u ^ 2))⁻¹ ≤ 2
  have heq : (u ^ 2) ^ 2 = u ^ 4 := by ring
  rw [heq] at hdiv
  exact hdiv

private theorem pow_six_mul_exp_neg_sq_le_six (u : ℝ) :
    u ^ 6 * Real.exp (-(u ^ 2)) ≤ 6 := by
  have h := Real.pow_div_factorial_le_exp (u ^ 2) (sq_nonneg u) 3
  norm_num [div_eq_mul_inv] at h
  have hpow : (u ^ 2) ^ 3 ≤ 6 * Real.exp (u ^ 2) := by nlinarith
  have hdiv := (div_le_iff₀ (Real.exp_pos (u ^ 2))).2 hpow
  rw [Real.exp_neg]
  change u ^ 6 * (Real.exp (u ^ 2))⁻¹ ≤ 6
  have heq : (u ^ 2) ^ 3 = u ^ 6 := by ring
  rw [heq] at hdiv
  exact hdiv

theorem abs_expNegInvSqGlueSecond_le_thirtySix (x : ℝ) :
    |expNegInvSqGlueSecond x| ≤ 36 := by
  by_cases hx : x ≤ 0
  · simp [expNegInvSqGlueSecond, hx]
  · have hxpos : 0 < x := lt_of_not_ge hx
    let u := x⁻¹
    have hu0 : 0 ≤ u := (inv_pos.mpr hxpos).le
    have h4 := pow_four_mul_exp_neg_sq_le_two u
    have h6 := pow_six_mul_exp_neg_sq_le_six u
    have he0 : 0 ≤ Real.exp (-(u ^ 2)) := (Real.exp_pos _).le
    have habs : |4 * u ^ 6 - 6 * u ^ 4| ≤ 4 * u ^ 6 + 6 * u ^ 4 := by
      calc
        |4 * u ^ 6 - 6 * u ^ 4| ≤ |4 * u ^ 6| + |6 * u ^ 4| := abs_sub _ _
        _ = 4 * u ^ 6 + 6 * u ^ 4 := by
          rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    rw [expNegInvSqGlueSecond, if_neg hx]
    change |(4 * u ^ 6 - 6 * u ^ 4) * Real.exp (-(u ^ 2))| ≤ 36
    rw [abs_mul, abs_of_nonneg he0]
    have hm := mul_le_mul_of_nonneg_right habs he0
    nlinarith

theorem abs_expNegInvSqGlueDeriv_le_four (x : ℝ) :
    |expNegInvSqGlueDeriv x| ≤ 4 := by
  by_cases hx : x ≤ 0
  · simp [expNegInvSqGlueDeriv, hx]
  · have hxpos : 0 < x := lt_of_not_ge hx
    let u := x⁻¹
    have hu0 : 0 ≤ u := (inv_pos.mpr hxpos).le
    have he0 : 0 ≤ Real.exp (-(u ^ 2)) := (Real.exp_pos _).le
    have he1 : Real.exp (-(u ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (sq_nonneg u)
    have hcore : u ^ 3 * Real.exp (-(u ^ 2)) ≤ 2 := by
      by_cases hu : u ≤ 1
      · have hu3 : u ^ 3 ≤ 1 := by
          nlinarith [sq_nonneg u, mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu)]
        have hm := mul_le_mul hu3 he1 he0 (by norm_num : (0 : ℝ) ≤ 1)
        exact hm.trans (by norm_num)
      · have hu1 : 1 ≤ u := le_of_not_ge hu
        have hp : u ^ 3 ≤ u ^ 4 := by nlinarith [sq_nonneg u, pow_nonneg hu0 3]
        have hm := mul_le_mul_of_nonneg_right hp he0
        exact hm.trans (pow_four_mul_exp_neg_sq_le_two u)
    rw [expNegInvSqGlueDeriv, if_neg hx]
    change |2 * u ^ 3 * Real.exp (-(u ^ 2))| ≤ 4
    rw [abs_of_nonneg (by positivity)]
    nlinarith

theorem sqrt_two_le_two : Real.sqrt (2 : ℝ) ≤ 2 := by
  nlinarith [sqrt_two_sq, Real.sqrt_nonneg (2 : ℝ)]

theorem sqrt_exp_one_le_two : Real.sqrt (Real.exp 1) ≤ 2 := by
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  · nlinarith [Real.exp_one_lt_three]

theorem abs_expNegHalfInvSqGlueDeriv_le_eight (x : ℝ) :
    |expNegHalfInvSqGlueDeriv x| ≤ 8 := by
  unfold expNegHalfInvSqGlueDeriv
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := abs_expNegInvSqGlueDeriv_le_four (Real.sqrt 2 * x)
  nlinarith [sqrt_two_le_two, Real.sqrt_nonneg (2 : ℝ)]

theorem abs_expNegHalfInvSqGlueSecond_le_seventyTwo (x : ℝ) :
    |expNegHalfInvSqGlueSecond x| ≤ 72 := by
  unfold expNegHalfInvSqGlueSecond
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [abs_expNegInvSqGlueSecond_le_thirtySix (Real.sqrt 2 * x)]

theorem abs_carmonThetaDeriv_le_thirtyTwo (t : ℝ) :
    |carmonThetaDeriv t| ≤ 32 := by
  unfold carmonThetaDeriv
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := abs_expNegHalfInvSqGlueDeriv_le_eight (2 * t - 1)
  nlinarith [sqrt_exp_one_le_two, Real.sqrt_nonneg (Real.exp 1)]

theorem abs_carmonThetaSecond_le_fiveSeventySix (t : ℝ) :
    |carmonThetaSecond t| ≤ 576 := by
  unfold carmonThetaSecond
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := abs_expNegHalfInvSqGlueSecond_le_seventyTwo (2 * t - 1)
  nlinarith [sqrt_exp_one_le_two, Real.sqrt_nonneg (Real.exp 1)]

/-! ## The paper's scalar scale `rho` -/

def outerRho (t : ℝ) : ℝ := carmonTheta t + carmonTheta (-t)

def outerRhoDeriv (t : ℝ) : ℝ := carmonThetaDeriv t - carmonThetaDeriv (-t)

def outerRhoSecond (t : ℝ) : ℝ := carmonThetaSecond t + carmonThetaSecond (-t)

theorem hasDerivAt_outerRho (t : ℝ) :
    HasDerivAt outerRho (outerRhoDeriv t) t := by
  unfold outerRho outerRhoDeriv
  have hp := hasDerivAt_carmonTheta t
  have hn := (hasDerivAt_carmonTheta (-t)).comp t (hasDerivAt_id t).neg
  convert hp.add hn using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext s
    rfl
  · ring

theorem hasDerivAt_outerRhoDeriv (t : ℝ) :
    HasDerivAt outerRhoDeriv (outerRhoSecond t) t := by
  unfold outerRhoDeriv outerRhoSecond
  have hp := hasDerivAt_carmonThetaDeriv t
  have hn := (hasDerivAt_carmonThetaDeriv (-t)).comp t (hasDerivAt_id t).neg
  convert hp.sub hn using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext s
    rfl
  · ring

theorem deriv_outerRho (t : ℝ) : deriv outerRho t = outerRhoDeriv t :=
  (hasDerivAt_outerRho t).deriv

theorem deriv_outerRhoDeriv (t : ℝ) : deriv outerRhoDeriv t = outerRhoSecond t :=
  (hasDerivAt_outerRhoDeriv t).deriv

theorem differentiable_outerRho : Differentiable ℝ outerRho :=
  fun t ↦ (hasDerivAt_outerRho t).differentiableAt

theorem differentiable_outerRhoDeriv : Differentiable ℝ outerRhoDeriv :=
  fun t ↦ (hasDerivAt_outerRhoDeriv t).differentiableAt

/-- Literal `C∞` smoothness from Lemma 4.5. -/
@[fun_prop] theorem contDiff_outerRho {n : ℕ∞} : ContDiff ℝ n outerRho := by
  unfold outerRho
  fun_prop

/-- The operational smoothness required later: `rho` is continuously
differentiable and its derivative is globally Lipschitz. -/
theorem outerRho_contDiff_one : ContDiff ℝ 1 outerRho := by
  rw [contDiff_one_iff_deriv]
  refine ⟨differentiable_outerRho, ?_⟩
  rw [show deriv outerRho = outerRhoDeriv by funext t; exact deriv_outerRho t]
  exact differentiable_outerRhoDeriv.continuous

theorem outerRho_nonneg (t : ℝ) : 0 ≤ outerRho t :=
  add_nonneg (carmonTheta_nonneg t) (carmonTheta_nonneg (-t))

theorem outerRho_sq_eq (t : ℝ) :
    outerRho t ^ 2 = carmonPsi t + carmonPsi (-t) := by
  unfold outerRho
  rw [add_sq, carmonTheta_sq, carmonTheta_sq]
  have hz := carmonTheta_mul_neg t
  nlinarith

theorem outerRho_eq_sqrt (t : ℝ) :
    outerRho t = Real.sqrt (carmonPsi t + carmonPsi (-t)) := by
  rw [← outerRho_sq_eq]
  exact ((Real.sqrt_sq_eq_abs _).trans
    (abs_of_nonneg (outerRho_nonneg t))).symm

theorem outerRho_le_two (t : ℝ) : outerRho t ≤ 2 := by
  have hsquares := outerRho_sq_eq t
  have hpsi : carmonPsi t + carmonPsi (-t) ≤ 3 := by
    by_cases ht : t ≤ 1 / 2
    · rw [carmonPsi_of_le_half ht]
      simpa using (carmonPsi_le_exp_one (-t)).trans Real.exp_one_lt_three.le
    · have hneg : -t ≤ 1 / 2 := by linarith
      rw [carmonPsi_of_le_half hneg, add_zero]
      exact (carmonPsi_le_exp_one t).trans Real.exp_one_lt_three.le
  nlinarith [outerRho_nonneg t]

theorem abs_outerRhoDeriv_le_sixtyFour (t : ℝ) :
    |outerRhoDeriv t| ≤ 64 := by
  unfold outerRhoDeriv
  exact (abs_sub _ _).trans (by
    nlinarith [abs_carmonThetaDeriv_le_thirtyTwo t,
      abs_carmonThetaDeriv_le_thirtyTwo (-t)])

theorem abs_outerRhoSecond_le_elevenFiftyTwo (t : ℝ) :
    |outerRhoSecond t| ≤ 1152 := by
  unfold outerRhoSecond
  exact (abs_add_le _ _).trans (by
    nlinarith [abs_carmonThetaSecond_le_fiveSeventySix t,
      abs_carmonThetaSecond_le_fiveSeventySix (-t)])

theorem outerRhoDeriv_lipschitz :
    LipschitzWith (1152 : NNReal) outerRhoDeriv := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_outerRhoDeriv
  intro t
  rw [deriv_outerRhoDeriv, ← NNReal.coe_le_coe]
  simpa [Real.norm_eq_abs] using abs_outerRhoSecond_le_elevenFiftyTwo t

theorem outerRho_of_abs_le_half {t : ℝ} (ht : |t| ≤ 1 / 2) :
    outerRho t = 0 := by
  rw [abs_le] at ht
  unfold outerRho
  rw [carmonTheta_of_le_half ht.2, carmonTheta_of_le_half (by linarith)]
  ring

theorem outerRhoDeriv_of_abs_le_half {t : ℝ} (ht : |t| ≤ 1 / 2) :
    outerRhoDeriv t = 0 := by
  rw [abs_le] at ht
  unfold outerRhoDeriv
  rw [carmonThetaDeriv_of_le_half ht.2,
    carmonThetaDeriv_of_le_half (by linarith)]
  ring

/-! ## Exact Gaussian derivative bound used in Lemma 4.6 -/

def carmonPhiSecond (t : ℝ) : ℝ :=
  -Real.sqrt (Real.exp 1) * t * carmonGaussian t

theorem hasDerivAt_carmonGaussian (t : ℝ) :
    HasDerivAt carmonGaussian (-t * carmonGaussian t) t := by
  unfold carmonGaussian
  have hinner : HasDerivAt (fun s : ℝ ↦ -(1 / 2 : ℝ) * s ^ 2) (-t) t := by
    simpa using ((hasDerivAt_id t).pow 2 |>.const_mul (-(1 / 2 : ℝ)))
  simpa [mul_comm, mul_left_comm, mul_assoc] using hinner.exp

theorem hasDerivAt_carmonPhiDeriv (t : ℝ) :
    HasDerivAt carmonPhiDeriv (carmonPhiSecond t) t := by
  unfold carmonPhiDeriv carmonPhiSecond
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (hasDerivAt_carmonGaussian t).const_mul (Real.sqrt (Real.exp 1))

theorem deriv_carmonPhiDeriv (t : ℝ) :
    deriv carmonPhiDeriv t = carmonPhiSecond t :=
  (hasDerivAt_carmonPhiDeriv t).deriv

theorem differentiable_carmonPhiDeriv : Differentiable ℝ carmonPhiDeriv :=
  fun t ↦ (hasDerivAt_carmonPhiDeriv t).differentiableAt

theorem abs_carmonPhiSecond_le_one (t : ℝ) :
    |carmonPhiSecond t| ≤ 1 := by
  have hs0 : 0 ≤ Real.sqrt (Real.exp 1) := Real.sqrt_nonneg _
  have hg0 : 0 ≤ carmonGaussian t := (carmonGaussian_pos t).le
  have hsqroot : Real.sqrt (Real.exp 1) ^ 2 = Real.exp 1 :=
    Real.sq_sqrt (Real.exp_pos _).le
  have hexpLower := Real.add_one_le_exp (t ^ 2 - 1)
  have hmul : t ^ 2 * Real.exp (1 - t ^ 2) ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right hexpLower (Real.exp_pos (1 - t ^ 2)).le
    rw [← Real.exp_add] at hm
    norm_num at hm
    exact hm
  have hsquare : |carmonPhiSecond t| ^ 2 =
      t ^ 2 * Real.exp (1 - t ^ 2) := by
    unfold carmonPhiSecond carmonGaussian
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hs0,
      abs_of_pos (Real.exp_pos _), mul_pow, mul_pow, sq_abs, hsqroot]
    calc
      Real.exp 1 * t ^ 2 * Real.exp (-(1 / 2) * t ^ 2) ^ 2 =
          t ^ 2 * (Real.exp 1 *
            (Real.exp (-(1 / 2) * t ^ 2) *
              Real.exp (-(1 / 2) * t ^ 2))) := by ring
      _ = t ^ 2 * Real.exp (1 +
          (-(1 / 2) * t ^ 2 + -(1 / 2) * t ^ 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ = t ^ 2 * Real.exp (1 - t ^ 2) := by ring_nf
  nlinarith [abs_nonneg (carmonPhiSecond t)]

theorem carmonPhiDeriv_lipschitz_one :
    LipschitzWith (1 : NNReal) carmonPhiDeriv := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_carmonPhiDeriv
  intro t
  rw [deriv_carmonPhiDeriv, ← NNReal.coe_le_coe]
  simpa [Real.norm_eq_abs] using abs_carmonPhiSecond_le_one t

theorem abs_carmonPhiDeriv_lt_two (t : ℝ) : |carmonPhiDeriv t| < 2 := by
  unfold carmonPhiDeriv
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_pos (carmonGaussian_pos t)]
  have hg := carmonGaussian_le_one t
  have hs := sqrt_exp_one_le_two
  have hs0 := Real.sqrt_nonneg (Real.exp 1)
  have hg0 := (carmonGaussian_pos t).le
  have hslt : Real.sqrt (Real.exp 1) < 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.exp_one_lt_three]
  nlinarith

theorem carmonPhiDeriv_plus_lipschitz_lt_three (t : ℝ) :
    |carmonPhiDeriv t| + 1 < 3 := by
  linarith [abs_carmonPhiDeriv_lt_two t]

theorem carmonPhi_pos (t : ℝ) : 0 < carmonPhi t := by
  have hmono := carmonPhi_monotone (show t - 1 < t by linarith)
  have hnonneg := carmonPhi_nonneg (t - 1)
  linarith

theorem carmonPhiCap_lt_five : carmonPhiCap < 5 := by
  rw [carmonPhiCap, integral_carmonGaussian]
  have he0 : 0 ≤ Real.exp (1 : ℝ) := (Real.exp_pos _).le
  have hp0 : 0 ≤ 2 * Real.pi := mul_nonneg (by norm_num) Real.pi_nonneg
  have hs1 : Real.sqrt (Real.exp 1) ^ 2 = Real.exp 1 := Real.sq_sqrt he0
  have hs2 : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt hp0
  have he : Real.exp (1 : ℝ) < 3 := Real.exp_one_lt_three
  have hp : Real.pi < 22 / 7 := Real.pi_lt_d4.trans (by norm_num)
  have hsq :
      (Real.sqrt (Real.exp 1) * Real.sqrt (2 * Real.pi)) ^ 2 < (5 : ℝ) ^ 2 := by
    rw [mul_pow, hs1, hs2]
    nlinarith
  have hnonneg :
      0 ≤ Real.sqrt (Real.exp 1) * Real.sqrt (2 * Real.pi) := by positivity
  nlinarith

theorem carmonPhi_lt_five (t : ℝ) : carmonPhi t < 5 :=
  (carmonPhi_le_cap t).trans_lt carmonPhiCap_lt_five

/-! ## Lemma 4.6: the lifted target -/

def carmonInteraction (s t : ℝ) : ℝ :=
  carmonPsi (-s) * carmonPhi (-t) - carmonPsi s * carmonPhi t

def carmonLiftedH (s t : ℝ) : ℝ :=
  5 * outerRho s ^ 2 + carmonInteraction s t

def carmonAlphaPlus (t : ℝ) : ℝ := 5 - carmonPhi t

def carmonAlphaMinus (t : ℝ) : ℝ := 5 + carmonPhi (-t)

theorem carmonAlphaPlus_pos (t : ℝ) : 0 < carmonAlphaPlus t := by
  unfold carmonAlphaPlus
  linarith [carmonPhi_lt_five t]

theorem carmonAlphaPlus_lt_ten (t : ℝ) : carmonAlphaPlus t < 10 := by
  unfold carmonAlphaPlus
  linarith [carmonPhi_pos t]

theorem carmonAlphaMinus_pos (t : ℝ) : 0 < carmonAlphaMinus t := by
  unfold carmonAlphaMinus
  linarith [carmonPhi_pos (-t)]

theorem carmonAlphaMinus_lt_ten (t : ℝ) : carmonAlphaMinus t < 10 := by
  unfold carmonAlphaMinus
  linarith [carmonPhi_lt_five (-t)]

theorem carmonLiftedH_eq_weighted_targets (s t : ℝ) :
    carmonLiftedH s t =
      carmonPsi s * carmonAlphaPlus t +
        carmonPsi (-s) * carmonAlphaMinus t := by
  unfold carmonLiftedH carmonInteraction carmonAlphaPlus carmonAlphaMinus
  rw [outerRho_sq_eq]
  ring

theorem carmonLiftedH_of_gt_half {s t : ℝ} (hs : 1 / 2 < s) :
    carmonLiftedH s t = outerRho s ^ 2 * (5 - carmonPhi t) := by
  rw [carmonLiftedH_eq_weighted_targets]
  have hneg : -s ≤ 1 / 2 := by linarith
  rw [carmonPsi_of_le_half hneg, zero_mul, add_zero, outerRho_sq_eq,
    carmonPsi_of_le_half hneg, add_zero]
  rfl

theorem carmonLiftedH_of_abs_le_half {s t : ℝ} (hs : |s| ≤ 1 / 2) :
    carmonLiftedH s t = 0 := by
  rw [carmonLiftedH_eq_weighted_targets]
  rw [abs_le] at hs
  rw [carmonPsi_of_le_half hs.2, carmonPsi_of_le_half (by linarith)]
  ring

theorem carmonLiftedH_of_lt_neg_half {s t : ℝ} (hs : s < -(1 / 2)) :
    carmonLiftedH s t = outerRho s ^ 2 * (5 + carmonPhi (-t)) := by
  rw [carmonLiftedH_eq_weighted_targets]
  have hpos : s ≤ 1 / 2 := by linarith
  rw [carmonPsi_of_le_half hpos, zero_mul, zero_add, outerRho_sq_eq,
    carmonPsi_of_le_half hpos, zero_add]
  rfl

theorem carmonLiftedH_nonneg (s t : ℝ) : 0 ≤ carmonLiftedH s t := by
  rw [carmonLiftedH_eq_weighted_targets]
  exact add_nonneg
    (mul_nonneg (carmonPsi_nonneg _) (carmonAlphaPlus_pos _).le)
    (mul_nonneg (carmonPsi_nonneg _) (carmonAlphaMinus_pos _).le)

theorem carmonLiftedH_le_ten_rho_sq (s t : ℝ) :
    carmonLiftedH s t ≤ 10 * outerRho s ^ 2 := by
  rw [carmonLiftedH_eq_weighted_targets, outerRho_sq_eq]
  have hp0 := carmonPsi_nonneg s
  have hn0 := carmonPsi_nonneg (-s)
  have hp := (carmonAlphaPlus_lt_ten t).le
  have hn := (carmonAlphaMinus_lt_ten t).le
  nlinarith

/-- All conclusions of Lemmas 4.5 and 4.6 in one machine-checkable package. -/
theorem outer_scale_and_lifted_target_certificate :
    (∀ s, 0 ≤ outerRho s ∧ outerRho s ≤ 2 ∧
      |outerRhoDeriv s| ≤ 64) ∧
    LipschitzWith (1152 : NNReal) outerRhoDeriv ∧
    (∀ s, |s| ≤ 1 / 2 → outerRho s = 0 ∧ outerRhoDeriv s = 0) ∧
    (∀ t, 0 < carmonAlphaPlus t ∧ carmonAlphaPlus t < 10 ∧
      0 < carmonAlphaMinus t ∧ carmonAlphaMinus t < 10 ∧
      |carmonPhiDeriv t| + 1 < 3) ∧
    (∀ s t, 0 ≤ carmonLiftedH s t ∧
      carmonLiftedH s t ≤ 10 * outerRho s ^ 2) := by
  exact ⟨fun s ↦ ⟨outerRho_nonneg s, outerRho_le_two s,
      abs_outerRhoDeriv_le_sixtyFour s⟩,
    outerRhoDeriv_lipschitz,
    fun s hs ↦ ⟨outerRho_of_abs_le_half hs,
      outerRhoDeriv_of_abs_le_half hs⟩,
    fun t ↦ ⟨carmonAlphaPlus_pos t, carmonAlphaPlus_lt_ten t,
      carmonAlphaMinus_pos t, carmonAlphaMinus_lt_ten t,
      carmonPhiDeriv_plus_lipschitz_lt_three t⟩,
    fun s t ↦ ⟨carmonLiftedH_nonneg s t,
      carmonLiftedH_le_ten_rho_sq s t⟩⟩

end

end NCPLRevised
