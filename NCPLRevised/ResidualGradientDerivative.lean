/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.ResidualGradientSmoothness
import NCPLRevised.EmbeddedCellJointDerivative

/-!
# Actual dual derivative of the totalized residual chain

This module proves that `embeddedResidualYLift` is not merely a Lipschitz
auxiliary field: it represents the genuine Fréchet derivative of
`embeddedResidualAtScale` in the full dual vector.
-/

namespace NCPLRevised

noncomputable section

theorem pPerspectiveGradient_snd_eq_uLift (eta u : ℝ) :
    (quadraticPerspectiveGradient p pDeriv (eta, u)).2 =
      pPerspectiveULift eta u := by
  by_cases heta : eta = 0
  · subst eta
    simp [pPerspectiveULift, scaleClipLift]
  · rw [quadraticPerspectiveGradient, if_neg heta]
    rw [pPerspectiveULift, scaleClipLift, if_neg heta]
    rw [pPerspectiveUBase_unitClip]
    rfl

theorem qpPerspectiveFDeriv_dual_apply (eta u v hu hv : ℝ) :
    quadraticPerspectiveVecFDeriv qpGate qpGateFDeriv (eta, (u, v))
        (0, (hu, hv)) =
      qpPerspectiveULift eta u v * hu +
        qpPerspectiveVLift eta u v * hv := by
  by_cases heta : eta = 0
  · subst eta
    simp [quadraticPerspectiveVecFDeriv, qpPerspectiveULift,
      qpPerspectiveVLift, scaleClipPairLift]
  · rw [qpPerspectiveULift, qpPerspectiveVLift]
    simp only [scaleClipPairLift, if_neg heta]
    rw [qpPerspectiveUBase_unitClip, qpPerspectiveVBase_unitClip]
    simp [quadraticPerspectiveVecFDeriv, heta, qpGate, qpGateFDeriv,
      qpPerspectiveUBase, qpPerspectiveVBase, smul_eq_mul]
    field_simp [heta]

/-- Coordinate projection used by a normalized residual gate. -/
def residualNormalizedCoordCLM {N : ℕ} (k : Fin N) :
    ChainPoint N →L[ℝ] ℝ :=
  (1 / weightSqrt N k) •
    (ContinuousLinearMap.proj k : ChainPoint N →L[ℝ] ℝ)

@[simp] theorem residualNormalizedCoordCLM_apply {N : ℕ}
    (k : Fin N) (y : ChainPoint N) :
    residualNormalizedCoordCLM k y = y k / weightSqrt N k := by
  simp [residualNormalizedCoordCLM, div_eq_mul_inv, mul_comm]

/-- Continuous linear functional represented by one gate's two scattered
dual-gradient components. -/
def residualGateYFDeriv (N : ℕ) (eta : ℝ) (y : ChainPoint N)
    (k : Fin N) : ChainPoint N →L[ℝ] ℝ :=
  (residualGateCurrentLift N eta y k) •
      (ContinuousLinearMap.proj k : ChainPoint N →L[ℝ] ℝ) +
    if hk : k.1 = 0 then 0 else
      (residualGatePreviousLift N eta y k) •
        (ContinuousLinearMap.proj ⟨k.1 - 1, by omega⟩ :
          ChainPoint N →L[ℝ] ℝ)

@[simp] theorem residualGateYFDeriv_apply (N : ℕ) (eta : ℝ)
    (y h : ChainPoint N) (k : Fin N) :
    residualGateYFDeriv N eta y k h =
      residualGateCurrentLift N eta y k * h k +
        if hk : k.1 = 0 then 0 else
          residualGatePreviousLift N eta y k * h ⟨k.1 - 1, by omega⟩ := by
  by_cases hk : k.1 = 0
  · simp [residualGateYFDeriv, hk]
  · simp [residualGateYFDeriv, hk]

/-- One residual gate has the displayed two-coordinate field as its genuine
dual Fréchet derivative. -/
theorem hasFDerivAt_residualGateValue_y (N : ℕ) (eta : ℝ)
    (y : ChainPoint N) (k : Fin N) :
    HasChainFDerivAt N (fun z : ChainPoint N ↦ residualGateValue N eta z k)
      (residualGateYFDeriv N eta y k) y := by
  letI : AddCommGroup (ChainPoint N) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (ChainPoint N) := Pi.normedSpace.toModule
  letI : TopologicalSpace (ChainPoint N) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup (ℝ × ℝ) := Prod.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (ℝ × ℝ) := Prod.normedSpace.toModule
  letI : TopologicalSpace (ℝ × ℝ) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup (ℝ × (ℝ × ℝ)) :=
    Prod.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (ℝ × (ℝ × ℝ)) := Prod.normedSpace.toModule
  letI : TopologicalSpace (ℝ × (ℝ × ℝ)) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasChainFDerivAt
  by_cases hk : k.1 = 0
  · let u := y k / weightSqrt N k
    have hp := hasFDerivAt_pPerspective (eta, u)
    unfold HasPairFDerivAt at hp
    have hu : residualNormalizedCoordCLM k y = u := by simp [u]
    rw [← hu] at hp
    have hmap : HasFDerivAt
        (fun z : ChainPoint N ↦ (eta, residualNormalizedCoordCLM k z))
        ((0 : ChainPoint N →L[ℝ] ℝ).prod
          (residualNormalizedCoordCLM k)) y :=
      (hasFDerivAt_const (x := y) (c := eta)).prodMk
        (residualNormalizedCoordCLM k).hasFDerivAt
    have hcomp := hp.comp y hmap
    have hscaled := hcomp.neg.const_add (eta ^ 2) |>.const_mul (omega N k.1)
    have hfun :
        (fun z : ChainPoint N ↦ residualGateValue N eta z k) =
          (fun z ↦ omega N k.1 *
            (eta ^ 2 - pPerspective
              (eta, residualNormalizedCoordCLM k z))) := by
      funext z
      simp [residualGateValue, hk]
    rw [hfun]
    apply hscaled.congr_fderiv
    apply ContinuousLinearMap.ext
    intro h
    simp [residualGateYFDeriv_apply, hk,
      residualGateCurrentLift, pPerspectiveGradient_snd_eq_uLift,
      div_eq_mul_inv]
    ring
  · let kp : Fin N := ⟨k.1 - 1, by omega⟩
    let u := y kp / weightSqrt N kp
    let v := y k / weightSqrt N k
    have hp := hasVecPerspectiveFDerivAt qpGate qpGateFDeriv
      (fun z ↦ by
        have hz := hasFDerivAt_qpGate z
        unfold HasPairFDerivAt at hz
        exact hz)
      qpGate_nonneg qpGate_le_one (eta, (u, v))
    unfold HasVecPerspectiveFDerivAt at hp
    let pairMap : ChainPoint N →L[ℝ] (ℝ × ℝ) :=
      (residualNormalizedCoordCLM kp).prod (residualNormalizedCoordCLM k)
    have huv : pairMap y = (u, v) := by
      ext <;> simp [pairMap, u, v]
    rw [← huv] at hp
    have hmap : HasFDerivAt
        (fun z : ChainPoint N ↦ (eta, pairMap z))
        ((0 : ChainPoint N →L[ℝ] ℝ).prod pairMap) y :=
      (hasFDerivAt_const (x := y) (c := eta)).prodMk pairMap.hasFDerivAt
    have hcomp := hp.comp y hmap
    have hscaled := hcomp.neg.const_add (eta ^ 2) |>.const_mul (omega N k.1)
    have hfun :
        (fun z : ChainPoint N ↦ residualGateValue N eta z k) =
          (fun z ↦ omega N k.1 *
            (eta ^ 2 - quadraticPerspectiveVec qpGate
              (eta, pairMap z))) := by
      funext z
      simp [residualGateValue, hk, pairMap, kp]
    rw [hfun]
    apply hscaled.congr_fderiv
    apply ContinuousLinearMap.ext
    intro h
    simp [residualGateYFDeriv_apply, residualGateCurrentLift,
      residualGatePreviousLift, hk, pairMap, kp,
      qpPerspectiveFDeriv_dual_apply, div_eq_mul_inv]
    ring

/-- The full dual derivative of the residual is the sum of its scattered
two-coordinate gate derivatives. -/
def embeddedResidualYFDeriv (N : ℕ) (eta : ℝ) (y : ChainPoint N) :
    ChainPoint N →L[ℝ] ℝ :=
  ∑ k : Fin N, residualGateYFDeriv N eta y k

@[simp] theorem embeddedResidualYFDeriv_apply (N : ℕ) (eta : ℝ)
    (y h : ChainPoint N) :
    embeddedResidualYFDeriv N eta y h =
      ∑ k : Fin N, residualGateYFDeriv N eta y k h := by
  exact continuousLinearMap_sum_apply
    (fun k : Fin N ↦ residualGateYFDeriv N eta y k) h

/-- The summed gate derivative is the finite dot product represented by the
closed-form residual dual gradient. -/
theorem embeddedResidualYFDeriv_eq_finiteDotProductCLM
    (N : ℕ) (eta : ℝ) (y : ChainPoint N) :
    embeddedResidualYFDeriv N eta y =
      finiteDotProductCLM (embeddedResidualYLift N eta y) := by
  apply ContinuousLinearMap.ext
  intro h
  rw [embeddedResidualYFDeriv_apply, finiteDotProductCLM_apply]
  simp only [residualGateYFDeriv_apply]
  rw [Finset.sum_add_distrib]
  rw [sum_predecessor_eq_sum_successor
    (fun k : Fin N ↦ residualGatePreviousLift N eta y k) h]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [embeddedResidualYLift]
  split_ifs <;> ring

/-- The closed-form field `embeddedResidualYLift` is the genuine full dual
Fréchet gradient of the totalized residual, including at zero scale. -/
theorem hasFDerivAt_embeddedResidualAtScale_y (N : ℕ) (eta : ℝ)
    (y : ChainPoint N) :
    HasChainFDerivAt N (embeddedResidualAtScale N eta)
      (finiteDotProductCLM (embeddedResidualYLift N eta y)) y := by
  have hsum : HasChainFDerivAt N
      (fun z : ChainPoint N ↦
        ∑ k : Fin N, residualGateValue N eta z k)
      (embeddedResidualYFDeriv N eta y) y := by
    unfold HasChainFDerivAt embeddedResidualYFDeriv
    apply HasFDerivAt.fun_sum
    intro k _
    exact hasFDerivAt_residualGateValue_y N eta y k
  rw [embeddedResidualYFDeriv_eq_finiteDotProductCLM] at hsum
  simpa only [← embeddedResidualAtScale_eq_sum_gateValue] using hsum

end

end NCPLRevised
