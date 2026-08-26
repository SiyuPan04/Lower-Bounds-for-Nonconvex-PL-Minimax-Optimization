/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.CarmonActivation
import NCPLRevised.ScaledPerspectiveBlock

/-!
# The embedded primal--dual cell

This module fixes the exact function called `C` in Section 5 of the revised
manuscript.  In particular, the definition below is not an abstract smooth
cell: it is the scaled block from Lemma 4.4 evaluated at the exact Carmon
scale and lifted target from Lemmas 4.5--4.6.

The elementary results in the first half give the exact envelope and the
extension through the two flat interfaces.  The second half records a stable
expanded form on the active regions.  This form removes the apparent
singularity in the negative-part penalty and is the starting point for the
dimension-uniform smoothness estimate in Lemma 5.1.
-/

namespace NCPLRevised

noncomputable section

/-- The exact embedded cell `C(s,t;y)` from the revised manuscript. -/
def embeddedCell (N : ℕ) (s t : ℝ) (y : ChainPoint N) : ℝ :=
  -5 * outerRho s ^ 2 +
    scaledPerspectiveBlock N (outerRho s) (carmonLiftedH s t) y

/-- The explicit maximizing dual vector inherited from Lemma 4.4. -/
def embeddedCellMaximizer (N : ℕ) (s : ℝ) : ChainPoint N :=
  scaledPerspectiveMaximizer N (outerRho s)

/-- The parameters supplied to the scaled block are admissible. -/
theorem embeddedCell_parameters_admissible (s t : ℝ) :
    0 ≤ outerRho s ∧
      0 ≤ carmonLiftedH s t ∧
      carmonLiftedH s t ≤ 10 * outerRho s ^ 2 := by
  exact ⟨outerRho_nonneg s, carmonLiftedH_nonneg s t,
    carmonLiftedH_le_ten_rho_sq s t⟩

/-- Exact local maximization, expressed as an upper bound plus an attaining
witness so that no compactness or choice argument is hidden. -/
theorem embeddedCell_max {N : ℕ} (hN : 2 ≤ N) (s t : ℝ) :
    (∀ y : ChainPoint N, embeddedCell N s t y ≤ carmonInteraction s t) ∧
      embeddedCell N s t (embeddedCellMaximizer N s) =
        carmonInteraction s t := by
  have hadm := embeddedCell_parameters_admissible s t
  have hmax := scaledPerspectiveBlock_max hN hadm.1 hadm.2.1 hadm.2.2
  constructor
  · intro y
    have hy := hmax.1 y
    calc
      embeddedCell N s t y =
          -5 * outerRho s ^ 2 +
            scaledPerspectiveBlock N (outerRho s) (carmonLiftedH s t) y := rfl
      _ ≤ -5 * outerRho s ^ 2 + carmonLiftedH s t :=
        by gcongr
      _ = carmonInteraction s t := by
        unfold carmonLiftedH
        ring
  · have hy := hmax.2
    rw [embeddedCell, embeddedCellMaximizer, hy]
    unfold carmonLiftedH
    ring

/-- In the inactive strip the exact cell is the squared negative-part
penalty and is independent of both primal arguments. -/
theorem embeddedCell_of_abs_le_half {N : ℕ} {s t : ℝ}
    (hs : |s| ≤ 1 / 2) (y : ChainPoint N) :
    embeddedCell N s t y = zeroPerspectiveBlock y := by
  have hrho := outerRho_of_abs_le_half hs
  simp [embeddedCell, scaledPerspectiveBlock, hrho]

/-- In particular, the value on either interface is the central formula. -/
theorem embeddedCell_at_pos_half (N : ℕ) (t : ℝ) (y : ChainPoint N) :
    embeddedCell N (1 / 2) t y = zeroPerspectiveBlock y := by
  apply embeddedCell_of_abs_le_half
  norm_num

/-- In particular, the value on either interface is the central formula. -/
theorem embeddedCell_at_neg_half (N : ℕ) (t : ℝ) (y : ChainPoint N) :
    embeddedCell N (-(1 / 2)) t y = zeroPerspectiveBlock y := by
  apply embeddedCell_of_abs_le_half
  norm_num

/-! ## Stable active-region expansion -/

/-- The normalized dual point used when the outer scale is active. -/
def embeddedNormalized (N : ℕ) (s : ℝ) (y : ChainPoint N) : ChainPoint N :=
  perspectiveNormalize N (outerRho s) y

/-- The residual part of the normalized dual chain, before the
negative-part penalty is simplified. -/
def embeddedResidual (N : ℕ) (s : ℝ) (y : ChainPoint N) : ℝ :=
  outerRho s ^ 2 *
    ∑ k : Fin N,
      omega N k.1 * gateTerm (embeddedNormalized N s y) k

/-- The active terminal gate. -/
def embeddedTerminal (N : ℕ) (s : ℝ) (y : ChainPoint N) : ℝ :=
  q (chainCoord (embeddedNormalized N s y) (N - 1))

/-- Squared Euclidean norm of the coordinatewise negative part. -/
def negPartNormSq {N : ℕ} (y : ChainPoint N) : ℝ :=
  ∑ k : Fin N, negPart (y k) ^ 2

theorem negPart_div_of_pos {a b : ℝ} (hb : 0 < b) :
    negPart (a / b) = negPart a / b := by
  rcases le_total a 0 with ha | ha
  · rw [negPart_of_nonpos ha,
      negPart_of_nonpos (div_nonpos_of_nonpos_of_nonneg ha hb.le)]
    ring
  · rw [negPart_of_nonneg ha,
      negPart_of_nonneg (div_nonneg ha hb.le)]
    ring

/-- The weighted penalty becomes exactly the unweighted Euclidean penalty
after the diagonal perspective normalization.  This is the cancellation
used in the proof of Lemma 5.1. -/
theorem scaled_penalty_cancellation {N : ℕ} (hN : 0 < N)
    {eta : ℝ} (heta : 0 < eta) (y : ChainPoint N) :
    eta ^ 2 *
        (∑ k : Fin N,
          omega N (k.1 + 1) / 2 *
            negPart (perspectiveNormalize N eta y k) ^ 2) =
      (1 / 2 : ℝ) * negPartNormSq y := by
  unfold negPartNormSq
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hw : 0 < weightSqrt N k := weightSqrt_pos hN k
  have hwsq := weightSqrt_sq hN k
  unfold perspectiveNormalize
  rw [negPart_div_of_pos (mul_pos heta hw)]
  field_simp [heta.ne', hw.ne']
  nlinarith

/-- Expansion of the scaled block at positive scale. -/
theorem scaledPerspectiveBlock_expanded {N : ℕ} (hN : 0 < N)
    {eta alpha : ℝ} (heta : 0 < eta) (y : ChainPoint N) :
    scaledPerspectiveBlock N eta alpha y =
      alpha * q (chainCoord (perspectiveNormalize N eta y) (N - 1)) -
      eta ^ 2 *
        (∑ k : Fin N,
          omega N k.1 * gateTerm (perspectiveNormalize N eta y) k) -
      (1 / 2 : ℝ) * negPartNormSq y := by
  rw [scaledPerspectiveBlock, if_neg heta.ne']
  unfold coupledDual dualChain localInteraction
  rw [Finset.sum_add_distrib, mul_sub, mul_add,
    scaled_penalty_cancellation hN heta]
  have hscale :
      eta ^ 2 *
          (alpha / eta ^ 2 *
            q (chainCoord (perspectiveNormalize N eta y) (N - 1))) =
        alpha * q (chainCoord (perspectiveNormalize N eta y) (N - 1)) := by
    field_simp [heta.ne']
  rw [hscale]
  ring

/-- Stable formula for the exact cell wherever the scale is active. -/
theorem embeddedCell_expanded_of_rho_pos {N : ℕ} (hN : 0 < N)
    {s t : ℝ} (hs : 0 < outerRho s) (y : ChainPoint N) :
    embeddedCell N s t y =
      -5 * outerRho s ^ 2 +
      carmonLiftedH s t * embeddedTerminal N s y -
      embeddedResidual N s y -
      (1 / 2 : ℝ) * negPartNormSq y := by
  unfold embeddedCell embeddedTerminal embeddedResidual embeddedNormalized
  rw [scaledPerspectiveBlock_expanded hN hs]
  ring

/-- The positive outer region has exactly the paper's `C⁺` formula. -/
theorem embeddedCell_expanded_pos {N : ℕ} (hN : 0 < N)
    {s t : ℝ} (hs : 1 / 2 < s) (y : ChainPoint N) :
    embeddedCell N s t y =
      -5 * outerRho s ^ 2 +
      (outerRho s ^ 2 * carmonAlphaPlus t) * embeddedTerminal N s y -
      embeddedResidual N s y -
      (1 / 2 : ℝ) * negPartNormSq y := by
  have hrho : 0 < outerRho s := by
    unfold outerRho
    have htheta : 0 < carmonTheta s := by
      unfold carmonTheta expNegHalfInvSqGlue
      have hlinear : 0 < 2 * s - 1 := by linarith
      have harg : 0 < Real.sqrt 2 * (2 * s - 1) :=
        mul_pos sqrt_two_pos hlinear
      exact mul_pos (Real.sqrt_pos.2 (Real.exp_pos 1))
        (expNegInvSqGlue_pos_of_pos harg)
    linarith [carmonTheta_nonneg (-s)]
  rw [embeddedCell_expanded_of_rho_pos hN hrho]
  rw [carmonLiftedH_of_gt_half hs]
  rfl

/-- The negative outer region has exactly the paper's `C⁻` formula. -/
theorem embeddedCell_expanded_neg {N : ℕ} (hN : 0 < N)
    {s t : ℝ} (hs : s < -(1 / 2)) (y : ChainPoint N) :
    embeddedCell N s t y =
      -5 * outerRho s ^ 2 +
      (outerRho s ^ 2 * carmonAlphaMinus t) * embeddedTerminal N s y -
      embeddedResidual N s y -
      (1 / 2 : ℝ) * negPartNormSq y := by
  have hrho : 0 < outerRho s := by
    unfold outerRho
    have htheta : 0 < carmonTheta (-s) := by
      unfold carmonTheta expNegHalfInvSqGlue
      have hlinear : 0 < 2 * (-s) - 1 := by linarith
      have harg : 0 < Real.sqrt 2 * (2 * (-s) - 1) :=
        mul_pos sqrt_two_pos hlinear
      exact mul_pos (Real.sqrt_pos.2 (Real.exp_pos 1))
        (expNegInvSqGlue_pos_of_pos harg)
    linarith [carmonTheta_nonneg s]
  rw [embeddedCell_expanded_of_rho_pos hN hrho]
  rw [carmonLiftedH_of_lt_neg_half hs]
  rfl

/-! ## The successor-variable interface -/

/-- The actual derivative of the Carmon interaction with respect to its
second argument. -/
def carmonInteractionTDeriv (s t : ℝ) : ℝ :=
  -(carmonPsi (-s) * carmonPhiDeriv (-t) +
    carmonPsi s * carmonPhiDeriv t)

theorem hasDerivAt_carmonInteraction_right (s t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ carmonInteraction s u)
      (carmonInteractionTDeriv s t) t := by
  have hneg := (hasDerivAt_carmonPhi (-t)).comp t (hasDerivAt_id t).neg
  have hpos := hasDerivAt_carmonPhi t
  have h := hneg.const_mul (carmonPsi (-s)) |>.sub
    (hpos.const_mul (carmonPsi s))
  convert h using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext u
    simp [carmonInteraction]
  · simp [carmonInteractionTDeriv]
    ring

theorem hasDerivAt_carmonLiftedH_right (s t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ carmonLiftedH s u)
      (carmonInteractionTDeriv s t) t := by
  have h := (hasDerivAt_carmonInteraction_right s t).const_add
    (5 * outerRho s ^ 2)
  simpa only [carmonLiftedH] using h

/-- Explicit successor coordinate of the embedded-cell gradient. -/
def embeddedSuccessorGradient (N : ℕ) (s t : ℝ) (y : ChainPoint N) : ℝ :=
  if _h : outerRho s = 0 then 0 else
    q (chainCoord y (N - 1) / outerRho s) *
      carmonInteractionTDeriv s t

/-- Equation (12) after composition with the exact lifted target, including
the inactive zero-scale branch. -/
theorem hasDerivAt_embeddedCell_successor {N : ℕ} (hN : 0 < N)
    (s t : ℝ) (y : ChainPoint N) :
    HasDerivAt (fun u : ℝ ↦ embeddedCell N s u y)
      (embeddedSuccessorGradient N s t y) t := by
  by_cases hrho : outerRho s = 0
  · have hfun : (fun u : ℝ ↦ embeddedCell N s u y) =
        (fun _u : ℝ ↦ zeroPerspectiveBlock y) := by
      funext u
      simp [embeddedCell, scaledPerspectiveBlock, hrho]
    rw [hfun]
    simpa [embeddedSuccessorGradient, hrho] using
      hasDerivAt_const (x := t) (c := zeroPerspectiveBlock y)
  · have htarget := hasDerivAt_carmonLiftedH_right s t
    have hblock := hasDerivAt_scaledPerspectiveBlock_alpha_of_ne hN hrho
      (carmonLiftedH s t) y
    have hcomp := hblock.comp t htarget
    have hcell := hcomp.const_add (-5 * outerRho s ^ 2)
    convert hcell using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext u
      simp [embeddedCell, add_comm]
    · simp [embeddedSuccessorGradient, hrho]

/-- The terminal gate prevents the successor coordinate from being
revealed while the last dual coordinate is zero. -/
theorem embeddedSuccessorGradient_zero_of_terminal {N : ℕ}
    (s t : ℝ) (y : ChainPoint N)
    (hy : chainCoord y (N - 1) = 0) :
    embeddedSuccessorGradient N s t y = 0 := by
  by_cases hrho : outerRho s = 0
  · simp [embeddedSuccessorGradient, hrho]
  · simp [embeddedSuccessorGradient, hrho, hy]

theorem hasDerivAt_embeddedCell_successor_zero_of_terminal {N : ℕ}
    (hN : 0 < N) (s t : ℝ) (y : ChainPoint N)
    (hy : chainCoord y (N - 1) = 0) :
    HasDerivAt (fun u : ℝ ↦ embeddedCell N s u y) 0 t := by
  simpa [embeddedSuccessorGradient_zero_of_terminal s t y hy] using
    hasDerivAt_embeddedCell_successor hN s t y

end

end NCPLRevised
