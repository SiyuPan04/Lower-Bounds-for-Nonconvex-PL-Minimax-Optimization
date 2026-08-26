/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.ZeroChain
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The exact scalar gates in the outer Carmon chain

This file formalizes the flat exponential gate and the Gaussian primitive
used in Section 6.  The auxiliary `expNegInvSqGlue` is the exact smooth
extension of `x ↦ exp (-1/x²)` by zero on the negative half-line.
-/

namespace NCPLRevised

noncomputable section

open Filter Set MeasureTheory
open scoped Topology Interval

def expNegInvSqGlue (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else Real.exp (-(x⁻¹) ^ 2)

def expNegInvSqGlueDeriv (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else
    2 * (x⁻¹) ^ 3 * Real.exp (-(x⁻¹) ^ 2)

def expNegInvSqGlueSecond (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else
    (4 * (x⁻¹) ^ 6 - 6 * (x⁻¹) ^ 4) *
      Real.exp (-(x⁻¹) ^ 2)

@[simp] theorem expNegInvSqGlue_zero : expNegInvSqGlue 0 = 0 := by
  simp [expNegInvSqGlue]

@[simp] theorem expNegInvSqGlueDeriv_zero : expNegInvSqGlueDeriv 0 = 0 := by
  simp [expNegInvSqGlueDeriv]

@[simp] theorem expNegInvSqGlueSecond_zero : expNegInvSqGlueSecond 0 = 0 := by
  simp [expNegInvSqGlueSecond]

theorem expNegInvSqGlue_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    expNegInvSqGlue x = 0 := by simp [expNegInvSqGlue, hx]

theorem expNegInvSqGlue_pos_of_pos {x : ℝ} (hx : 0 < x) :
    0 < expNegInvSqGlue x := by
  simp [expNegInvSqGlue, hx.not_ge, Real.exp_pos]

theorem expNegInvSqGlue_nonneg (x : ℝ) : 0 ≤ expNegInvSqGlue x := by
  by_cases hx : x ≤ 0
  · simp [expNegInvSqGlue, hx]
  · exact (expNegInvSqGlue_pos_of_pos (lt_of_not_ge hx)).le

theorem expNegInvSqGlue_le_one (x : ℝ) : expNegInvSqGlue x ≤ 1 := by
  by_cases hx : x ≤ 0
  · simp [expNegInvSqGlue, hx]
  · rw [expNegInvSqGlue, if_neg hx]
    exact (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg x⁻¹)))

theorem expNegInvSqGlueDeriv_nonneg (x : ℝ) :
    0 ≤ expNegInvSqGlueDeriv x := by
  by_cases hx : x ≤ 0
  · simp [expNegInvSqGlueDeriv, hx]
  · rw [expNegInvSqGlueDeriv, if_neg hx]
    have hxinv : 0 < x⁻¹ := inv_pos.mpr (lt_of_not_ge hx)
    positivity

private theorem tendsto_pow_mul_exp_neg_sq_atTop (n : Nat) :
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

private theorem tendsto_inv_pow_mul_expNegInvSqGlue_zero (n : Nat) :
    Tendsto (fun x : ℝ ↦ (x⁻¹) ^ n * expNegInvSqGlue x) (nhds 0) (nhds 0) := by
  simp only [expNegInvSqGlue, mul_ite, mul_zero]
  refine tendsto_const_nhds.if ?_
  simp only [not_le]
  have h := (tendsto_pow_mul_exp_neg_sq_atTop n).comp tendsto_inv_nhdsGT_zero
  exact h.congr' (by filter_upwards with x using rfl)

theorem hasDerivAt_expNegInvSqGlue (x : ℝ) :
    HasDerivAt expNegInvSqGlue (expNegInvSqGlueDeriv x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hzero : expNegInvSqGlueDeriv x = 0 := by
      simp [expNegInvSqGlueDeriv, hx.le]
    rw [hzero]
    refine (hasDerivAt_const x 0).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact expNegInvSqGlue_of_nonpos (le_of_lt hy)
  · rw [expNegInvSqGlueDeriv_zero, hasDerivAt_iff_tendsto_slope]
    have h := tendsto_inv_pow_mul_expNegInvSqGlue_zero 1
    refine (h.mono_left inf_le_left).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [slope_def_field, expNegInvSqGlue_zero, sub_zero]
    field_simp [hy]
  · rw [expNegInvSqGlueDeriv, if_neg hx.not_ge]
    have hinner : HasDerivAt (fun y : ℝ ↦ -(y⁻¹) ^ 2)
        (2 * (x⁻¹) ^ 3) x := by
      refine (((hasDerivAt_inv hx.ne').pow 2).neg).congr_deriv ?_
      field_simp [hx.ne']
      simp [hx.ne']
    have hexp := hinner.exp
    have hfun : HasDerivAt expNegInvSqGlue
        (Real.exp (-(x⁻¹) ^ 2) * (2 * (x⁻¹) ^ 3)) x := by
      refine hexp.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx] with y hy
      change 0 < y at hy
      simp [expNegInvSqGlue, (not_le_of_gt hy)]
    exact hfun.congr_deriv (by ring)

theorem deriv_expNegInvSqGlue (x : ℝ) :
    deriv expNegInvSqGlue x = expNegInvSqGlueDeriv x :=
  (hasDerivAt_expNegInvSqGlue x).deriv

theorem differentiable_expNegInvSqGlue : Differentiable ℝ expNegInvSqGlue :=
  fun x ↦ (hasDerivAt_expNegInvSqGlue x).differentiableAt

/-- The displayed second-derivative field is the actual derivative of the
first-derivative field, including at the flat splice point. -/
theorem hasDerivAt_expNegInvSqGlueDeriv (x : ℝ) :
    HasDerivAt expNegInvSqGlueDeriv (expNegInvSqGlueSecond x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hzero : expNegInvSqGlueSecond x = 0 := by
      simp [expNegInvSqGlueSecond, hx.le]
    rw [hzero]
    refine (hasDerivAt_const x 0).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    have hy0 : y ≤ 0 := le_of_lt hy
    simp [expNegInvSqGlueDeriv, hy0]
  · rw [expNegInvSqGlueSecond_zero, hasDerivAt_iff_tendsto_slope]
    have h' : Tendsto
        (fun y : ℝ ↦ 2 * ((y⁻¹) ^ 4 * expNegInvSqGlue y))
        (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      simpa using
        ((tendsto_inv_pow_mul_expNegInvSqGlue_zero 4).const_mul 2).mono_left
          (show nhdsWithin (0 : ℝ) {0}ᶜ ≤ nhds 0 from inf_le_left)
    refine h'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [slope_def_field, expNegInvSqGlueDeriv_zero, sub_zero]
    by_cases hypos : 0 < y
    · rw [expNegInvSqGlueDeriv, if_neg hypos.not_ge]
      rw [expNegInvSqGlue, if_neg hypos.not_ge]
      field_simp [hy]
    · have hynonpos : y ≤ 0 := le_of_not_gt hypos
      simp [expNegInvSqGlueDeriv, expNegInvSqGlue, hynonpos]
  · have hinv3 := (hasDerivAt_inv hx.ne').pow 3
    have hleft : HasDerivAt (fun y : ℝ ↦ 2 * (y⁻¹) ^ 3)
        (2 * (3 * x⁻¹ ^ (3 - 1) * -(x ^ 2)⁻¹)) x := by
      simpa only [Pi.pow_apply, Nat.cast_ofNat] using hinv3.const_mul 2
    have hprod := hleft.mul (hasDerivAt_expNegInvSqGlue x)
    have hfun : HasDerivAt expNegInvSqGlueDeriv
        (2 * (3 * x⁻¹ ^ (3 - 1) * -(x ^ 2)⁻¹) * expNegInvSqGlue x +
          2 * x⁻¹ ^ 3 * expNegInvSqGlueDeriv x) x := by
      refine hprod.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx] with y hy
      have hypos : 0 < y := hy
      unfold expNegInvSqGlueDeriv expNegInvSqGlue
      rw [if_neg hypos.not_ge]
      simp only [Pi.mul_apply]
      rw [if_neg hypos.not_ge]
    rw [expNegInvSqGlueSecond, if_neg hx.not_ge]
    refine hfun.congr_deriv ?_
    rw [expNegInvSqGlue, if_neg hx.not_ge,
      expNegInvSqGlueDeriv, if_neg hx.not_ge]
    simp only [Nat.reduceSub]
    field_simp [hx.ne']
    ring_nf

theorem deriv_expNegInvSqGlueDeriv (x : ℝ) :
    deriv expNegInvSqGlueDeriv x = expNegInvSqGlueSecond x :=
  (hasDerivAt_expNegInvSqGlueDeriv x).deriv

theorem differentiable_expNegInvSqGlueDeriv :
    Differentiable ℝ expNegInvSqGlueDeriv :=
  fun x ↦ (hasDerivAt_expNegInvSqGlueDeriv x).differentiableAt

theorem expNegInvSqGlue_monotone : Monotone expNegInvSqGlue := by
  exact monotone_of_deriv_nonneg differentiable_expNegInvSqGlue fun x ↦ by
    rw [deriv_expNegInvSqGlue]
    exact expNegInvSqGlueDeriv_nonneg x

/-! ## Carmon's exact `psi` gate -/

def carmonPsi (t : ℝ) : ℝ :=
  Real.exp 1 * expNegInvSqGlue (2 * t - 1)

def carmonPsiDeriv (t : ℝ) : ℝ :=
  2 * Real.exp 1 * expNegInvSqGlueDeriv (2 * t - 1)

def carmonPsiSecond (t : ℝ) : ℝ :=
  4 * Real.exp 1 * expNegInvSqGlueSecond (2 * t - 1)

theorem carmonPsi_eq_piecewise (t : ℝ) :
    carmonPsi t = if t ≤ 1 / 2 then 0 else
      Real.exp (1 - 1 / (2 * t - 1) ^ 2) := by
  unfold carmonPsi expNegInvSqGlue
  by_cases ht : t ≤ 1 / 2
  · rw [if_pos (by linarith), if_pos ht]
    ring
  · rw [if_neg (by linarith), if_neg ht]
    rw [Real.exp_sub, div_eq_mul_inv]
    congr 1
    rw [← Real.exp_neg]
    congr 1
    field_simp

theorem carmonPsi_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) :
    carmonPsi t = 0 := by
  unfold carmonPsi
  rw [expNegInvSqGlue_of_nonpos (by linarith)]
  ring

@[simp] theorem carmonPsi_zero : carmonPsi 0 = 0 := by
  apply carmonPsi_of_le_half
  norm_num

@[simp] theorem carmonPsi_one : carmonPsi 1 = 1 := by
  rw [carmonPsi_eq_piecewise, if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2)]
  norm_num

theorem carmonPsi_nonneg (t : ℝ) : 0 ≤ carmonPsi t := by
  unfold carmonPsi
  exact mul_nonneg (Real.exp_pos _).le (expNegInvSqGlue_nonneg _)

theorem carmonPsi_le_exp_one (t : ℝ) : carmonPsi t ≤ Real.exp 1 := by
  unfold carmonPsi
  nlinarith [Real.exp_pos (1 : ℝ), expNegInvSqGlue_le_one (2 * t - 1)]

theorem carmonPsi_monotone : Monotone carmonPsi := by
  intro s t hst
  unfold carmonPsi
  gcongr
  exact expNegInvSqGlue_monotone (by linarith)

theorem deriv_carmonPsi (t : ℝ) : deriv carmonPsi t = carmonPsiDeriv t := by
  have hfun : carmonPsi =
      (expNegInvSqGlue ∘ fun x : ℝ ↦ x * 2 - 1) * (fun _ ↦ Real.exp 1) := by
    funext x
    simp only [carmonPsi, Function.comp_apply, Pi.mul_apply]
    ring_nf
  rw [hfun]
  have hcomp := (hasDerivAt_expNegInvSqGlue (2 * t - 1)).comp t
    ((hasDerivAt_id t).const_mul 2 |>.sub_const 1)
  have hmul := (hasDerivAt_const t (Real.exp 1)).mul hcomp
  simpa only [carmonPsiDeriv, Function.comp_apply, id_eq,
    Pi.mul_apply, zero_mul, zero_add, one_mul, mul_assoc, mul_left_comm,
    mul_comm] using hmul.deriv

theorem differentiable_carmonPsi : Differentiable ℝ carmonPsi := by
  intro t
  have hcomp := (hasDerivAt_expNegInvSqGlue (2 * t - 1)).comp t
    ((hasDerivAt_id t).const_mul 2 |>.sub_const 1)
  have hmul := (hasDerivAt_const t (Real.exp 1)).mul hcomp
  have hfun : carmonPsi =
      (fun s : ℝ ↦ Real.exp 1 * expNegInvSqGlue (2 * s - 1)) := by rfl
  rw [hfun]
  exact hmul.differentiableAt

theorem carmonPsiDeriv_nonneg (t : ℝ) : 0 ≤ carmonPsiDeriv t := by
  unfold carmonPsiDeriv
  exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
    (expNegInvSqGlueDeriv_nonneg _)

theorem carmonPsiDeriv_zero : carmonPsiDeriv 0 = 0 := by
  simp [carmonPsiDeriv, expNegInvSqGlueDeriv]

theorem one_lt_carmonPsi_of_one_lt {t : ℝ} (ht : 1 < t) :
    1 < carmonPsi t := by
  rw [carmonPsi_eq_piecewise, if_neg (by linarith)]
  rw [Real.one_lt_exp_iff]
  have hden : 1 < (2 * t - 1) ^ 2 := by nlinarith [sq_nonneg (2 * t - 2)]
  have hinv : 1 / (2 * t - 1) ^ 2 < 1 := by
    exact (div_lt_one (by positivity)).2 hden
  linarith

theorem abs_le_one_of_carmonPsi_add_neg_le_one {t : ℝ}
    (h : carmonPsi t + carmonPsi (-t) ≤ 1) : |t| ≤ 1 := by
  rw [abs_le]
  constructor
  · by_contra hbad
    have hlarge : 1 < -t := by linarith
    have hone := one_lt_carmonPsi_of_one_lt hlarge
    have hnonneg := carmonPsi_nonneg t
    linarith
  · by_contra hbad
    have hlarge : 1 < t := by linarith
    have hone := one_lt_carmonPsi_of_one_lt hlarge
    have hnonneg := carmonPsi_nonneg (-t)
    linarith

/-! ## The Gaussian primitive `varphi` -/

def carmonGaussian (s : ℝ) : ℝ := Real.exp (-(1 / 2 : ℝ) * s ^ 2)

def carmonPhi (t : ℝ) : ℝ :=
  Real.sqrt (Real.exp 1) * ∫ s in Set.Iic t, carmonGaussian s

def carmonPhiDeriv (t : ℝ) : ℝ :=
  Real.sqrt (Real.exp 1) * carmonGaussian t

theorem continuous_carmonGaussian : Continuous carmonGaussian := by
  unfold carmonGaussian
  fun_prop

theorem integrable_carmonGaussian : Integrable carmonGaussian := by
  have h := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  apply h.congr
  filter_upwards with x
  unfold carmonGaussian
  congr 1

theorem carmonGaussian_pos (s : ℝ) : 0 < carmonGaussian s := by
  unfold carmonGaussian
  positivity

theorem carmonGaussian_le_one (s : ℝ) : carmonGaussian s ≤ 1 := by
  unfold carmonGaussian
  rw [Real.exp_le_one_iff]
  nlinarith [sq_nonneg s]

theorem hasDerivAt_carmonPhi (t : ℝ) :
    HasDerivAt carmonPhi (carmonPhiDeriv t) t := by
  let I : ℝ := ∫ s in Set.Iic 0, carmonGaussian s
  have hrel (u : ℝ) :
      (∫ s in Set.Iic u, carmonGaussian s) =
        I + ∫ s in (0 : ℝ)..u, carmonGaussian s := by
    have h := intervalIntegral.integral_Iic_sub_Iic (a := (0 : ℝ)) (b := u)
      (integrable_carmonGaussian.integrableOn)
      (integrable_carmonGaussian.integrableOn)
    dsimp [I]
    linarith
  have hbase : HasDerivAt
      (fun u : ℝ ↦ ∫ s in Set.Iic u, carmonGaussian s)
      (carmonGaussian t) t := by
    have hint := continuous_carmonGaussian.integral_hasStrictDerivAt 0 t
    have hfun : (fun u : ℝ ↦ ∫ s in Set.Iic u, carmonGaussian s) =
        (fun u : ℝ ↦ I + ∫ s in (0 : ℝ)..u, carmonGaussian s) := by
      funext u
      exact hrel u
    rw [hfun]
    exact hint.hasDerivAt.const_add I
  unfold carmonPhi carmonPhiDeriv
  exact hbase.const_mul _

theorem deriv_carmonPhi (t : ℝ) : deriv carmonPhi t = carmonPhiDeriv t :=
  (hasDerivAt_carmonPhi t).deriv

theorem differentiable_carmonPhi : Differentiable ℝ carmonPhi :=
  fun t ↦ (hasDerivAt_carmonPhi t).differentiableAt

theorem carmonPhiDeriv_pos (t : ℝ) : 0 < carmonPhiDeriv t := by
  unfold carmonPhiDeriv carmonGaussian
  positivity

theorem carmonGaussian_neg (t : ℝ) : carmonGaussian (-t) = carmonGaussian t := by
  unfold carmonGaussian
  congr 1
  ring

theorem carmonPhiDeriv_neg (t : ℝ) : carmonPhiDeriv (-t) = carmonPhiDeriv t := by
  unfold carmonPhiDeriv
  rw [carmonGaussian_neg]

theorem carmonPhi_nonneg (t : ℝ) : 0 ≤ carmonPhi t := by
  unfold carmonPhi
  apply mul_nonneg (Real.sqrt_nonneg _)
  exact setIntegral_nonneg measurableSet_Iic fun s _ ↦ (carmonGaussian_pos s).le

theorem carmonPhi_le_full_integral (t : ℝ) :
    carmonPhi t ≤
      Real.sqrt (Real.exp 1) * ∫ s : ℝ, carmonGaussian s := by
  unfold carmonPhi
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  exact setIntegral_le_integral integrable_carmonGaussian
    (ae_of_all _ fun s ↦ (carmonGaussian_pos s).le)

theorem one_le_carmonPhiDeriv_of_abs_le_one {t : ℝ} (ht : |t| ≤ 1) :
    1 ≤ carmonPhiDeriv t := by
  have htSq : t ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (1 - |t|), sq_abs t, abs_nonneg t]
  have hvpos := carmonPhiDeriv_pos t
  have hvsq : carmonPhiDeriv t ^ 2 = Real.exp (1 - t ^ 2) := by
    unfold carmonPhiDeriv carmonGaussian
    rw [mul_pow, Real.sq_sqrt (Real.exp_pos _).le]
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hexp : 1 ≤ Real.exp (1 - t ^ 2) := by
    exact Real.one_le_exp (by linarith)
  nlinarith

theorem carmonPhi_monotone : StrictMono carmonPhi := by
  exact strictMono_of_deriv_pos fun t ↦ by
    rw [deriv_carmonPhi]
    exact carmonPhiDeriv_pos t

end

end NCPLRevised
