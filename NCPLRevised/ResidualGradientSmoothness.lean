/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.PerspectiveGradientLipschitz
import NCPLRevised.OuterLinearAlgebra
import NCPLRevised.ScaledPerspectiveBlock

/-!
# Dimension-free smoothness of the weighted residual chain

This module assembles the totalized scalar and two-coordinate perspective
gradient kernels along the weighted path.  The weights cancel the diagonal
normalization coordinate by coordinate.  Cauchy--Schwarz controls the one
shared scale derivative, while the dual-coordinate derivatives have overlap
at most two.  Thus the final constant is independent of the chain length.
-/

namespace NCPLRevised

noncomputable section

/-- The totalized value of the weighted residual chain at an abstract
nonnegative perspective scale.  This is `eta^2 * sum omega_j d_j` with the
diagonal normalization written using scalar/vector quadratic perspectives. -/
def embeddedResidualAtScale (N : ℕ) (eta : ℝ) (y : ChainPoint N) : ℝ :=
  ∑ k : Fin N,
    if hk : k.1 = 0 then
      omega N k.1 *
        (eta ^ 2 - pPerspective (eta, y k / weightSqrt N k))
    else
      omega N k.1 *
        (eta ^ 2 - quadraticPerspectiveVec
          (fun z : ℝ × ℝ ↦ q z.1 * p z.2)
          (eta,
            (y ⟨k.1 - 1, by omega⟩ / weightSqrt N ⟨k.1 - 1, by omega⟩,
              y k / weightSqrt N k)))

/-- The same residual value in the paper's normalized-chain notation. -/
def embeddedResidualRawAtScale (N : ℕ) (eta : ℝ)
    (y : ChainPoint N) : ℝ :=
  eta ^ 2 * ∑ k : Fin N,
    omega N k.1 * gateTerm (perspectiveNormalize N eta y) k

/-- The perspective-value formula is exactly the normalized residual away
from the (separately totalized) zero-scale hyperplane. -/
theorem embeddedResidualAtScale_eq_raw_of_ne {N : ℕ} {eta : ℝ}
    (heta : eta ≠ 0) (y : ChainPoint N) :
    embeddedResidualAtScale N eta y =
      embeddedResidualRawAtScale N eta y := by
  unfold embeddedResidualAtScale embeddedResidualRawAtScale
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.1 = 0
  · simp [hk, pPerspective, quadraticPerspective, heta, gateTerm,
      perspectiveNormalize]
    field_simp [heta, (weightSqrt_pos (by omega : 0 < N) k).ne']
  · have hpred : k.1 - 1 < N := by omega
    simp [hk, hpred, quadraticPerspectiveVec, heta, gateTerm, chainPrev,
      chainCoord, perspectiveNormalize, smul_eq_mul]
    field_simp [heta,
      (weightSqrt_pos (by omega : 0 < N) k).ne',
      (weightSqrt_pos (by omega : 0 < N)
        ⟨k.1 - 1, by omega⟩).ne']

/-! ## Actual derivatives of the displayed residual field -/

theorem pPerspectiveGradient_fst_eq_etaLift (eta u : ℝ) :
    (quadraticPerspectiveGradient p pDeriv (eta, u)).1 =
      pPerspectiveEtaLift eta u := by
  by_cases heta : eta = 0
  · subst eta
    simp [pPerspectiveEtaLift, scaleClipLift]
  · rw [quadraticPerspectiveGradient, if_neg heta]
    rw [pPerspectiveEtaLift, scaleClipLift, if_neg heta]
    rw [pPerspectiveEtaBase_unitClip]
    rfl

/-- Scalar derivative predicate with the norm-induced real instances fixed,
avoiding instance diamonds when composing the product-space perspective
certificates. -/
def HasResidualDerivAt (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    _ f f' x

theorem hasDerivAt_pPerspective_scale (eta u : ℝ) :
    HasResidualDerivAt (fun e : ℝ ↦ pPerspective (e, u))
      (pPerspectiveEtaLift eta u) eta := by
  have hp := hasFDerivAt_pPerspective (eta, u)
  unfold HasPairFDerivAt at hp
  have hline : HasDerivAt (fun e : ℝ ↦ (e, u)) (1, 0) eta :=
    (hasDerivAt_id eta).prodMk (hasDerivAt_const (x := eta) (c := u))
  have hcomp := hp.comp_hasDerivAt eta hline
  unfold HasResidualDerivAt
  rw [pairGradientCLM_apply] at hcomp
  simpa [Function.comp_def, pPerspectiveGradient_fst_eq_etaLift] using hcomp

/-- The two-coordinate gate whose perspective occurs on every noninitial
residual edge. -/
def qpGate (z : ℝ × ℝ) : ℝ := q z.1 * p z.2

/-- Exact Fréchet derivative of `qpGate`. -/
def qpGateFDeriv (z : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (qDeriv z.1 * p z.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (q z.1 * pDeriv z.2) • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem qpGateFDeriv_apply (z h : ℝ × ℝ) :
    qpGateFDeriv z h =
      qDeriv z.1 * p z.2 * h.1 + q z.1 * pDeriv z.2 * h.2 := by
  simp [qpGateFDeriv]

theorem hasFDerivAt_qpGate (z : ℝ × ℝ) :
    HasPairFDerivAt qpGate (qpGateFDeriv z) z := by
  letI : AddCommGroup (ℝ × ℝ) := Prod.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (ℝ × ℝ) := Prod.normedSpace.toModule
  letI : TopologicalSpace (ℝ × ℝ) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedCommRing.toAddCommGroup
  letI : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasPairFDerivAt
  have hx : HasFDerivAt (fun w : ℝ × ℝ ↦ w.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) z :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hy : HasFDerivAt (fun w : ℝ × ℝ ↦ w.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) z :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have hq := (hasDerivAt_q z.1).hasFDerivAt.comp z hx
  have hp := (hasDerivAt_p z.2).hasFDerivAt.comp z hy
  have h := hq.mul hp
  change HasFDerivAt (fun w : ℝ × ℝ ↦ q w.1 * p w.2)
    (qpGateFDeriv z) z
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [qpGateFDeriv]
  ring

theorem qpGate_nonneg (z : ℝ × ℝ) : 0 ≤ qpGate z :=
  mul_nonneg (q_nonneg _) (p_nonneg _)

theorem qpGate_le_one (z : ℝ × ℝ) : qpGate z ≤ 1 := by
  unfold qpGate
  nlinarith [q_nonneg z.1, q_le_one z.1, p_nonneg z.2, p_le_one z.2,
    mul_nonneg (q_nonneg z.1) (sub_nonneg.mpr (p_le_one z.2)),
    mul_nonneg (p_nonneg z.2) (sub_nonneg.mpr (q_le_one z.1))]

theorem qpPerspectiveFDeriv_scale_apply (eta u v : ℝ) :
    quadraticPerspectiveVecFDeriv qpGate qpGateFDeriv (eta, (u, v))
        (1, (0, 0)) = qpPerspectiveEtaLift eta u v := by
  by_cases heta : eta = 0
  · subst eta
    simp [quadraticPerspectiveVecFDeriv, qpPerspectiveEtaLift,
      scaleClipPairLift]
  · rw [qpPerspectiveEtaLift, scaleClipPairLift, if_neg heta]
    rw [qpPerspectiveEtaBase_unitClip]
    simp [quadraticPerspectiveVecFDeriv, heta, qpGate, qpGateFDeriv,
      qpPerspectiveEtaBase, smul_eq_mul]
    field_simp [heta]
    ring

theorem hasDerivAt_qpPerspective_scale (eta u v : ℝ) :
    HasResidualDerivAt
      (fun e : ℝ ↦ quadraticPerspectiveVec qpGate (e, (u, v)))
      (qpPerspectiveEtaLift eta u v) eta := by
  letI : AddCommGroup (ℝ × ℝ) := Prod.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (ℝ × ℝ) := Prod.normedSpace.toModule
  letI : TopologicalSpace (ℝ × ℝ) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have hp := hasVecPerspectiveFDerivAt qpGate qpGateFDeriv
    (fun z ↦ by
      have hz := hasFDerivAt_qpGate z
      unfold HasPairFDerivAt at hz
      exact hz)
    qpGate_nonneg qpGate_le_one (eta, (u, v))
  unfold HasVecPerspectiveFDerivAt at hp
  have hline : HasDerivAt (fun e : ℝ ↦ (e, (u, v)))
      (1, (0, 0)) eta :=
    (hasDerivAt_id eta).prodMk
      (hasDerivAt_const (x := eta) (c := (u, v)))
  have hcomp := hp.comp_hasDerivAt eta hline
  unfold HasResidualDerivAt
  simpa [Function.comp_def, qpPerspectiveFDeriv_scale_apply] using hcomp

/-- One summand of `embeddedResidualAtScale`, exposed for derivative
assembly. -/
def residualGateValue (N : ℕ) (eta : ℝ) (y : ChainPoint N)
    (k : Fin N) : ℝ :=
  if hk : k.1 = 0 then
    omega N k.1 *
      (eta ^ 2 - pPerspective (eta, y k / weightSqrt N k))
  else
    omega N k.1 *
      (eta ^ 2 - quadraticPerspectiveVec qpGate
        (eta,
          (y ⟨k.1 - 1, by omega⟩ / weightSqrt N ⟨k.1 - 1, by omega⟩,
            y k / weightSqrt N k)))

theorem embeddedResidualAtScale_eq_sum_gateValue (N : ℕ)
    (eta : ℝ) (y : ChainPoint N) :
    embeddedResidualAtScale N eta y =
      ∑ k : Fin N, residualGateValue N eta y k := by
  rfl

/-- Scale component contributed by one residual gate. -/
def residualGateEtaLift (N : ℕ) (eta : ℝ) (y : ChainPoint N)
    (k : Fin N) : ℝ :=
  if hk : k.1 = 0 then
    omega N k.1 *
      (2 * eta - pPerspectiveEtaLift eta (y k / weightSqrt N k))
  else
    omega N k.1 *
      (2 * eta - qpPerspectiveEtaLift eta
        (y ⟨k.1 - 1, by omega⟩ / weightSqrt N ⟨k.1 - 1, by omega⟩)
        (y k / weightSqrt N k))

/-- Derivative contributed by a residual gate to its current (right)
coordinate. -/
def residualGateCurrentLift (N : ℕ) (eta : ℝ) (y : ChainPoint N)
    (k : Fin N) : ℝ :=
  if hk : k.1 = 0 then
    -(omega N k.1 / weightSqrt N k) *
      pPerspectiveULift eta (y k / weightSqrt N k)
  else
    -(omega N k.1 / weightSqrt N k) *
      qpPerspectiveVLift eta
        (y ⟨k.1 - 1, by omega⟩ / weightSqrt N ⟨k.1 - 1, by omega⟩)
        (y k / weightSqrt N k)

/-- Derivative contributed by a noninitial residual gate to its previous
(left) coordinate.  It is zero for the initial gate, whose predecessor is
the fixed boundary value `1`. -/
def residualGatePreviousLift (N : ℕ) (eta : ℝ) (y : ChainPoint N)
    (k : Fin N) : ℝ :=
  if hk : k.1 = 0 then 0 else
    -(omega N k.1 / weightSqrt N ⟨k.1 - 1, by omega⟩) *
      qpPerspectiveULift eta
        (y ⟨k.1 - 1, by omega⟩ / weightSqrt N ⟨k.1 - 1, by omega⟩)
        (y k / weightSqrt N k)

/-- The exact totalized scale component of the residual gradient. -/
def embeddedResidualEtaLift (N : ℕ) (eta : ℝ) (y : ChainPoint N) : ℝ :=
  ∑ k : Fin N, residualGateEtaLift N eta y k

/-- The exact totalized Euclidean dual component of the residual gradient.
Every coordinate receives its own gate's right derivative and, except at the
end, the next gate's left derivative. -/
def embeddedResidualYLift (N : ℕ) (eta : ℝ)
    (y : ChainPoint N) : ChainPoint N := fun j ↦
  residualGateCurrentLift N eta y j +
    if hj : j.1 + 1 < N then
      residualGatePreviousLift N eta y ⟨j.1 + 1, hj⟩
    else 0

theorem sq_add_three_le_three (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

/-- Monotonicity between the two weights adjacent to a dual coordinate. -/
theorem omega_le_succ {N : ℕ} (hN : 0 < N) (k : Fin N) :
    omega N k.1 ≤ omega N (k.1 + 1) := by
  exact omega_mono hN (Nat.le_succ _) (by omega)

/-- Squared normalized current-coordinate energy is cancelled by its gate
weight. -/
theorem omega_mul_div_weightSqrt_sq_le {N : ℕ} (hN : 0 < N)
    (k : Fin N) (a : ℝ) :
    omega N k.1 * (a / weightSqrt N k) ^ 2 ≤ a ^ 2 := by
  have hw : 0 < weightSqrt N k := weightSqrt_pos hN k
  have hsq := weightSqrt_sq hN k
  have hm := omega_le_succ hN k
  have hcoef : omega N k.1 / weightSqrt N k ^ 2 ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hw)]
    simpa [hsq] using hm
  rw [div_pow]
  calc
    omega N k.1 * (a ^ 2 / weightSqrt N k ^ 2) =
        (omega N k.1 / weightSqrt N k ^ 2) * a ^ 2 := by ring
    _ ≤ 1 * a ^ 2 := by
      exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg a)
    _ = a ^ 2 := by ring

/-- The current-coordinate output coefficient has squared size at most its
gate weight. -/
theorem omega_div_weightSqrt_sq_le {N : ℕ} (hN : 0 < N)
    (k : Fin N) :
    (omega N k.1 / weightSqrt N k) ^ 2 ≤ omega N k.1 := by
  have hw : 0 < weightSqrt N k := weightSqrt_pos hN k
  have hsq := weightSqrt_sq hN k
  rw [div_pow, div_le_iff₀ (sq_pos_of_pos hw)]
  rw [hsq]
  have hm := omega_le_succ hN k
  have hpos := omega_pos hN (j := k.1)
  nlinarith

/-- Exact cancellation for a noninitial gate and its previous coordinate. -/
theorem previous_weightSqrt_sq {N : ℕ} (hN : 0 < N)
    (k : Fin N) (hk : k.1 ≠ 0) :
    weightSqrt N ⟨k.1 - 1, by omega⟩ ^ 2 = omega N k.1 := by
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ k.1)] using
    weightSqrt_sq hN ⟨k.1 - 1, by omega⟩

/-- Reindexing estimate for the left-coordinate gate contributions. -/
theorem residual_sum_successor_sq_le_sum {N : ℕ} (a : ChainPoint N) :
    (∑ j : Fin N,
      if hj : j.1 + 1 < N then a ⟨j.1 + 1, hj⟩ ^ 2 else 0) ≤
      ∑ k : Fin N, a k ^ 2 := by
  have hreindex := sum_predecessor_eq_sum_successor
    (fun k : Fin N ↦ a k ^ 2) (fun _ : Fin N ↦ (1 : ℝ))
  have hle :
      (∑ k : Fin N, if hk : k.1 = 0 then 0 else a k ^ 2 * (1 : ℝ)) ≤
        ∑ k : Fin N, a k ^ 2 := by
    apply Finset.sum_le_sum
    intro k _
    by_cases hk : k.1 = 0
    · simp [hk, sq_nonneg]
    · simp [hk]
  calc
    (∑ j : Fin N,
        if hj : j.1 + 1 < N then a ⟨j.1 + 1, hj⟩ ^ 2 else 0) =
      ∑ k : Fin N,
        if hk : k.1 = 0 then 0 else a k ^ 2 * (1 : ℝ) := by
          simpa using hreindex.symm
    _ ≤ ∑ k : Fin N, a k ^ 2 := hle

theorem residual_sq_add_le_two (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Generic energy estimate for assembling scale/current/previous gate
components.  The scale components share one output and are controlled by
weighted Cauchy--Schwarz; each coordinate output contains at most two gate
components. -/
theorem residualGradient_assembly_energy {N : ℕ} (hN : 2 ≤ N)
    (etaPart currentPart previousPart : Fin N → ℝ) :
    (∑ k : Fin N, etaPart k) ^ 2 +
        ∑ j : Fin N,
          (currentPart j +
            if hj : j.1 + 1 < N then previousPart ⟨j.1 + 1, hj⟩ else 0) ^ 2 ≤
      3 * ∑ k : Fin N,
        (etaPart k ^ 2 / omega N k.1 +
          currentPart k ^ 2 + previousPart k ^ 2) := by
  have hNpos : 0 < N := by omega
  have hetaEnergy : 0 ≤ ∑ k : Fin N,
      etaPart k ^ 2 / omega N k.1 := by
    apply Finset.sum_nonneg
    intro k _
    exact div_nonneg (sq_nonneg _) (omega_pos hNpos).le
  have hcauchy :
      (∑ k : Fin N, etaPart k) ^ 2 ≤
        (∑ k : Fin N, omega N k.1) *
          ∑ k : Fin N, etaPart k ^ 2 / omega N k.1 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro k _
      exact (omega_pos hNpos).le
    · intro k _
      exact div_nonneg (sq_nonneg _) (omega_pos hNpos).le
    · intro k _
      rw [mul_div_cancel₀]
      exact (omega_pos hNpos).ne'
  have hsumOmega : (∑ k : Fin N, omega N k.1) < 3 := by
    have h := sum_omega_lt_three hN
    rw [← Fin.sum_univ_eq_sum_range (fun j ↦ omega N j) N] at h
    exact h
  have heta :
      (∑ k : Fin N, etaPart k) ^ 2 ≤
        3 * ∑ k : Fin N, etaPart k ^ 2 / omega N k.1 :=
    hcauchy.trans (mul_le_mul_of_nonneg_right hsumOmega.le hetaEnergy)
  let nextPart : ChainPoint N := fun j ↦
    if hj : j.1 + 1 < N then previousPart ⟨j.1 + 1, hj⟩ else 0
  have hpoint :
      (∑ j : Fin N, (currentPart j + nextPart j) ^ 2) ≤
        2 * ∑ j : Fin N, currentPart j ^ 2 +
          2 * ∑ j : Fin N, nextPart j ^ 2 := by
    calc
      (∑ j : Fin N, (currentPart j + nextPart j) ^ 2) ≤
          ∑ j : Fin N,
            (2 * currentPart j ^ 2 + 2 * nextPart j ^ 2) := by
              apply Finset.sum_le_sum
              intro j _
              exact residual_sq_add_le_two _ _
      _ = 2 * ∑ j : Fin N, currentPart j ^ 2 +
          2 * ∑ j : Fin N, nextPart j ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hnext :
      (∑ j : Fin N, nextPart j ^ 2) ≤
        ∑ k : Fin N, previousPart k ^ 2 := by
    have heq :
        (∑ j : Fin N, nextPart j ^ 2) =
          ∑ j : Fin N,
            if hj : j.1 + 1 < N then
              previousPart ⟨j.1 + 1, hj⟩ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp [nextPart]
      split_ifs <;> simp
    rw [heq]
    exact residual_sum_successor_sq_le_sum previousPart
  have hy :
      (∑ j : Fin N, (currentPart j + nextPart j) ^ 2) ≤
        2 * ∑ j : Fin N, currentPart j ^ 2 +
          2 * ∑ k : Fin N, previousPart k ^ 2 := by
    calc
      (∑ j : Fin N, (currentPart j + nextPart j) ^ 2) ≤
          2 * ∑ j : Fin N, currentPart j ^ 2 +
            2 * ∑ j : Fin N, nextPart j ^ 2 := hpoint
      _ ≤ 2 * ∑ j : Fin N, currentPart j ^ 2 +
            2 * ∑ k : Fin N, previousPart k ^ 2 := by gcongr
  change
    (∑ k : Fin N, etaPart k) ^ 2 +
        ∑ j : Fin N, (currentPart j + nextPart j) ^ 2 ≤ _
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  nlinarith [Finset.sum_nonneg (s := Finset.univ)
      (fun k _ ↦ sq_nonneg (currentPart k)),
    Finset.sum_nonneg (s := Finset.univ)
      (fun k _ ↦ sq_nonneg (previousPart k))]

/-- Squared input energy assigned to one weighted gate. -/
def residualGateInputSq (N : ℕ) (eta theta : ℝ)
    (y y' : ChainPoint N) (k : Fin N) : ℝ :=
  omega N k.1 * (eta - theta) ^ 2 + (y k - y' k) ^ 2 +
    if hk : k.1 = 0 then 0
    else (y ⟨k.1 - 1, by omega⟩ - y' ⟨k.1 - 1, by omega⟩) ^ 2

/-- Weighted output energy of one gate-gradient difference.  The inverse
weight on the shared scale component is precisely what makes the later
Cauchy--Schwarz assembly dimension-free. -/
def residualGateOutputSq (N : ℕ) (eta theta : ℝ)
    (y y' : ChainPoint N) (k : Fin N) : ℝ :=
  (residualGateEtaLift N eta y k -
      residualGateEtaLift N theta y' k) ^ 2 / omega N k.1 +
    (residualGateCurrentLift N eta y k -
      residualGateCurrentLift N theta y' k) ^ 2 +
    (residualGatePreviousLift N eta y k -
      residualGatePreviousLift N theta y' k) ^ 2

theorem sq_le_sq_of_abs_le {x r : ℝ} (hr : 0 ≤ r) (h : |x| ≤ r) :
    x ^ 2 ≤ r ^ 2 := by
  have hm := mul_nonneg (sub_nonneg.mpr h)
    (add_nonneg hr (abs_nonneg x))
  nlinarith [sq_abs x]

theorem abs_div_sub_div_weightSqrt {N : ℕ} (hN : 0 < N)
    (k : Fin N) (a b : ℝ) :
    |a / weightSqrt N k - b / weightSqrt N k| =
      |a - b| / weightSqrt N k := by
  rw [← sub_div, abs_div, abs_of_pos (weightSqrt_pos hN k)]

/-- A single weighted gate has a uniform local energy bound.  The constant
`5000` simultaneously covers the special initial `p` gate and every later
two-coordinate `q*p` gate. -/
theorem residualGateOutputSq_le {N : ℕ} (hN : 2 ≤ N)
    {eta theta : ℝ} (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (y y' : ChainPoint N) (k : Fin N) :
    residualGateOutputSq N eta theta y y' k ≤
      5000 * residualGateInputSq N eta theta y y' k := by
  have hNpos : 0 < N := by omega
  let w : ℝ := omega N k.1
  let wc : ℝ := weightSqrt N k
  let a : ℝ := |eta - theta|
  let c : ℝ := |y k - y' k|
  have hw : 0 < w := omega_pos hNpos
  have hwc : 0 < wc := weightSqrt_pos hNpos k
  have hwc_sq : wc ^ 2 = omega N (k.1 + 1) := weightSqrt_sq hNpos k
  have hw_le : w ≤ wc ^ 2 := by
    simpa [w, wc, hwc_sq] using omega_le_succ hNpos k
  have ha : 0 ≤ a := abs_nonneg _
  have hc : 0 ≤ c := abs_nonneg _
  have hcurrNorm :
      |y k / wc - y' k / wc| = c / wc := by
    simpa [wc, c] using abs_div_sub_div_weightSqrt hNpos k (y k) (y' k)
  by_cases hk : k.1 = 0
  · have hetaLip := pPerspectiveEtaLift_lipschitz
        (eta := eta) (theta := theta)
        (u := y k / wc) (v := y' k / wc) heta htheta
    have huLip := pPerspectiveULift_lipschitz
        (eta := eta) (theta := theta)
        (u := y k / wc) (v := y' k / wc) heta htheta
    rw [hcurrNorm] at hetaLip huLip
    let de : ℝ :=
      (2 * eta - pPerspectiveEtaLift eta (y k / wc)) -
        (2 * theta - pPerspectiveEtaLift theta (y' k / wc))
    let du : ℝ :=
      pPerspectiveULift eta (y k / wc) -
        pPerspectiveULift theta (y' k / wc)
    have hde : |de| ≤ 9 * a + 7 * (c / wc) := by
      have htri : |de| ≤ 2 * a +
          |pPerspectiveEtaLift eta (y k / wc) -
            pPerspectiveEtaLift theta (y' k / wc)| := by
        calc
          |de| = |2 * (eta - theta) -
              (pPerspectiveEtaLift eta (y k / wc) -
                pPerspectiveEtaLift theta (y' k / wc))| := by
                  congr 1
                  dsimp [de]
                  ring
          _ ≤ |2 * (eta - theta)| +
              |pPerspectiveEtaLift eta (y k / wc) -
                pPerspectiveEtaLift theta (y' k / wc)| := abs_sub _ _
          _ = 2 * a +
              |pPerspectiveEtaLift eta (y k / wc) -
                pPerspectiveEtaLift theta (y' k / wc)| := by
                  simp [a, abs_mul]
      exact htri.trans (by nlinarith)
    have hdu : |du| ≤ 3 * (a + c / wc) := by
      simpa [du, a] using huLip
    have hcdiv : 0 ≤ c / wc := div_nonneg hc hwc.le
    have hdeSq0 := sq_le_sq_of_abs_le
      (show 0 ≤ 9 * a + 7 * (c / wc) by positivity) hde
    have hduSq0 := sq_le_sq_of_abs_le
      (show 0 ≤ 3 * (a + c / wc) by positivity) hdu
    have hdeSq : de ^ 2 ≤
        162 * a ^ 2 + 98 * (c / wc) ^ 2 := by
      have hs := residual_sq_add_le_two (9 * a) (7 * (c / wc))
      calc
        de ^ 2 ≤ (9 * a + 7 * (c / wc)) ^ 2 := hdeSq0
        _ ≤ 2 * (9 * a) ^ 2 + 2 * (7 * (c / wc)) ^ 2 := hs
        _ = 162 * a ^ 2 + 98 * (c / wc) ^ 2 := by ring
    have hduSq : du ^ 2 ≤
        18 * a ^ 2 + 18 * (c / wc) ^ 2 := by
      have hs := residual_sq_add_le_two a (c / wc)
      calc
        du ^ 2 ≤ (3 * (a + c / wc)) ^ 2 := hduSq0
        _ = 9 * (a + c / wc) ^ 2 := by ring
        _ ≤ 9 * (2 * a ^ 2 + 2 * (c / wc) ^ 2) := by gcongr
        _ = 18 * a ^ 2 + 18 * (c / wc) ^ 2 := by ring
    have hnormCancel : w * (c / wc) ^ 2 ≤ c ^ 2 := by
      have h := omega_mul_div_weightSqrt_sq_le hNpos k (y k - y' k)
      have heq : (c / wc) ^ 2 =
          ((y k - y' k) / weightSqrt N k) ^ 2 := by
        simp only [c, wc, div_pow, sq_abs]
      rw [heq]
      have hcSq' : c ^ 2 = (y k - y' k) ^ 2 := sq_abs _
      rw [hcSq']
      simpa [w, wc] using h
    have hcoef : (w / wc) ^ 2 ≤ w := by
      simpa [w, wc] using omega_div_weightSqrt_sq_le hNpos k
    have hetaOut : (w * de) ^ 2 / w ≤
        162 * w * a ^ 2 + 98 * c ^ 2 := by
      have heq : (w * de) ^ 2 / w = w * de ^ 2 := by
        field_simp [hw.ne']
      rw [heq]
      calc
        w * de ^ 2 ≤
            w * (162 * a ^ 2 + 98 * (c / wc) ^ 2) := by gcongr
        _ = 162 * w * a ^ 2 + 98 * (w * (c / wc) ^ 2) := by ring
        _ ≤ 162 * w * a ^ 2 + 98 * c ^ 2 := by gcongr
    have hcurrOut : ((w / wc) * du) ^ 2 ≤
        18 * w * a ^ 2 + 18 * c ^ 2 := by
      have hdu0 := sq_nonneg du
      have hstep : (w / wc) ^ 2 * du ^ 2 ≤ w * du ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef hdu0
      rw [mul_pow]
      calc
        (w / wc) ^ 2 * du ^ 2 ≤ w * du ^ 2 := hstep
        _ ≤ w * (18 * a ^ 2 + 18 * (c / wc) ^ 2) := by gcongr
        _ = 18 * w * a ^ 2 + 18 * (w * (c / wc) ^ 2) := by ring
        _ ≤ 18 * w * a ^ 2 + 18 * c ^ 2 := by gcongr
    have hetaEq : residualGateEtaLift N eta y k -
        residualGateEtaLift N theta y' k = w * de := by
      simp [residualGateEtaLift, hk, w, de]
      ring
    have hcurrEq : residualGateCurrentLift N eta y k -
        residualGateCurrentLift N theta y' k = -(w / wc) * du := by
      simp [residualGateCurrentLift, hk, w, wc, du]
      ring
    have hprevEq : residualGatePreviousLift N eta y k -
        residualGatePreviousLift N theta y' k = 0 := by
      simp [residualGatePreviousLift, hk]
    rw [residualGateOutputSq, residualGateInputSq, hetaEq, hcurrEq, hprevEq]
    simp only [neg_mul, even_two, Even.neg_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      dite_eq_ite, ge_iff_le]
    rw [if_pos hk]
    have haSq : a ^ 2 = (eta - theta) ^ 2 := sq_abs _
    have hcSq : c ^ 2 = (y k - y' k) ^ 2 := sq_abs _
    have htotal : (w * de) ^ 2 / w + (w / wc * du) ^ 2 ≤
        5000 * (w * a ^ 2 + c ^ 2) := by
      calc
        (w * de) ^ 2 / w + (w / wc * du) ^ 2 ≤
            (162 * w * a ^ 2 + 98 * c ^ 2) +
              (18 * w * a ^ 2 + 18 * c ^ 2) :=
                add_le_add hetaOut hcurrOut
        _ ≤ 5000 * (w * a ^ 2 + c ^ 2) := by
          have hwa : 0 ≤ w * a ^ 2 := mul_nonneg hw.le (sq_nonneg _)
          have hc2 : 0 ≤ c ^ 2 := sq_nonneg _
          linarith
    rw [haSq, hcSq] at htotal
    simpa only [w, add_zero] using htotal
  · let kp : Fin N := ⟨k.1 - 1, by omega⟩
    let wp : ℝ := weightSqrt N kp
    let b : ℝ := |y kp - y' kp|
    have hwp : 0 < wp := weightSqrt_pos hNpos kp
    have hwp_sq : wp ^ 2 = w := by
      simpa [wp, kp, w] using previous_weightSqrt_sq hNpos k hk
    have hb : 0 ≤ b := abs_nonneg _
    have hprevNorm : |y kp / wp - y' kp / wp| = b / wp := by
      simpa [wp, b] using abs_div_sub_div_weightSqrt hNpos kp
        (y kp) (y' kp)
    have hetaLip := qpPerspectiveEtaLift_lipschitz
      (eta := eta) (theta := theta)
      (u := y kp / wp) (v := y k / wc)
      (u' := y' kp / wp) (v' := y' k / wc) heta htheta
    have huLip := qpPerspectiveULift_lipschitz
      (eta := eta) (theta := theta)
      (u := y kp / wp) (v := y k / wc)
      (u' := y' kp / wp) (v' := y' k / wc) heta htheta
    have hvLip := qpPerspectiveVLift_lipschitz
      (eta := eta) (theta := theta)
      (u := y kp / wp) (v := y k / wc)
      (u' := y' kp / wp) (v' := y' k / wc) heta htheta
    rw [hprevNorm, hcurrNorm] at hetaLip huLip hvLip
    let de : ℝ :=
      (2 * eta - qpPerspectiveEtaLift eta (y kp / wp) (y k / wc)) -
        (2 * theta - qpPerspectiveEtaLift theta (y' kp / wp) (y' k / wc))
    let du : ℝ := qpPerspectiveULift eta (y kp / wp) (y k / wc) -
      qpPerspectiveULift theta (y' kp / wp) (y' k / wc)
    let dv : ℝ := qpPerspectiveVLift eta (y kp / wp) (y k / wc) -
      qpPerspectiveVLift theta (y' kp / wp) (y' k / wc)
    have hde : |de| ≤ 31 * a + 29 * (b / wp) + 29 * (c / wc) := by
      have htri : |de| ≤ 2 * a +
          |qpPerspectiveEtaLift eta (y kp / wp) (y k / wc) -
            qpPerspectiveEtaLift theta (y' kp / wp) (y' k / wc)| := by
        calc
          |de| = |2 * (eta - theta) -
              (qpPerspectiveEtaLift eta (y kp / wp) (y k / wc) -
                qpPerspectiveEtaLift theta (y' kp / wp) (y' k / wc))| := by
                  congr 1
                  dsimp [de]
                  ring
          _ ≤ |2 * (eta - theta)| +
              |qpPerspectiveEtaLift eta (y kp / wp) (y k / wc) -
                qpPerspectiveEtaLift theta (y' kp / wp) (y' k / wc)| :=
                  abs_sub _ _
          _ = 2 * a +
              |qpPerspectiveEtaLift eta (y kp / wp) (y k / wc) -
                qpPerspectiveEtaLift theta (y' kp / wp) (y' k / wc)| := by
                  simp [a, abs_mul]
      exact htri.trans (by nlinarith)
    have hdu : |du| ≤ 18 * (a + b / wp + c / wc) := by
      simpa [du, a] using huLip
    have hdv : |dv| ≤ 7 * (a + b / wp + c / wc) := by
      simpa [dv, a] using hvLip
    have hbdiv : 0 ≤ b / wp := div_nonneg hb hwp.le
    have hcdiv : 0 ≤ c / wc := div_nonneg hc hwc.le
    have hdeSq0 := sq_le_sq_of_abs_le
      (show 0 ≤ 31 * a + 29 * (b / wp) + 29 * (c / wc) by positivity) hde
    have hduSq0 := sq_le_sq_of_abs_le
      (show 0 ≤ 18 * (a + b / wp + c / wc) by positivity) hdu
    have hdvSq0 := sq_le_sq_of_abs_le
      (show 0 ≤ 7 * (a + b / wp + c / wc) by positivity) hdv
    have hsde := sq_add_three_le_three (31 * a)
      (29 * (b / wp)) (29 * (c / wc))
    have hsbase := sq_add_three_le_three a (b / wp) (c / wc)
    have hdeSq : de ^ 2 ≤
        2883 * a ^ 2 + 2523 * (b / wp) ^ 2 +
          2523 * (c / wc) ^ 2 := by
      calc
        de ^ 2 ≤
            (31 * a + 29 * (b / wp) + 29 * (c / wc)) ^ 2 := hdeSq0
        _ ≤ 3 * ((31 * a) ^ 2 + (29 * (b / wp)) ^ 2 +
            (29 * (c / wc)) ^ 2) := hsde
        _ = 2883 * a ^ 2 + 2523 * (b / wp) ^ 2 +
            2523 * (c / wc) ^ 2 := by ring
    have hduSq : du ^ 2 ≤
        972 * (a ^ 2 + (b / wp) ^ 2 + (c / wc) ^ 2) := by
      calc
        du ^ 2 ≤ (18 * (a + b / wp + c / wc)) ^ 2 := hduSq0
        _ = 324 * (a + b / wp + c / wc) ^ 2 := by ring
        _ ≤ 324 * (3 * (a ^ 2 + (b / wp) ^ 2 + (c / wc) ^ 2)) := by
          gcongr
        _ = 972 * (a ^ 2 + (b / wp) ^ 2 + (c / wc) ^ 2) := by ring
    have hdvSq : dv ^ 2 ≤
        147 * (a ^ 2 + (b / wp) ^ 2 + (c / wc) ^ 2) := by
      calc
        dv ^ 2 ≤ (7 * (a + b / wp + c / wc)) ^ 2 := hdvSq0
        _ = 49 * (a + b / wp + c / wc) ^ 2 := by ring
        _ ≤ 49 * (3 * (a ^ 2 + (b / wp) ^ 2 + (c / wc) ^ 2)) := by
          gcongr
        _ = 147 * (a ^ 2 + (b / wp) ^ 2 + (c / wc) ^ 2) := by ring
    have hprevCancel : w * (b / wp) ^ 2 = b ^ 2 := by
      rw [div_pow, hwp_sq]
      field_simp [hw.ne']
    have hcurrCancel : w * (c / wc) ^ 2 ≤ c ^ 2 := by
      have h := omega_mul_div_weightSqrt_sq_le hNpos k (y k - y' k)
      have heq : (c / wc) ^ 2 =
          ((y k - y' k) / weightSqrt N k) ^ 2 := by
        simp only [c, wc, div_pow, sq_abs]
      rw [heq]
      have hcSq' : c ^ 2 = (y k - y' k) ^ 2 := sq_abs _
      rw [hcSq']
      simpa [w, wc] using h
    have hcurrCoef : (w / wc) ^ 2 ≤ w := by
      simpa [w, wc] using omega_div_weightSqrt_sq_le hNpos k
    have hprevCoef : (w / wp) ^ 2 = w := by
      rw [div_pow, hwp_sq]
      field_simp [hw.ne']
    have hetaOut : (w * de) ^ 2 / w ≤
        2883 * w * a ^ 2 + 2523 * b ^ 2 + 2523 * c ^ 2 := by
      have heq : (w * de) ^ 2 / w = w * de ^ 2 := by
        field_simp [hw.ne']
      rw [heq]
      calc
        w * de ^ 2 ≤ w * (2883 * a ^ 2 + 2523 * (b / wp) ^ 2 +
            2523 * (c / wc) ^ 2) := by gcongr
        _ = 2883 * w * a ^ 2 + 2523 * (w * (b / wp) ^ 2) +
            2523 * (w * (c / wc) ^ 2) := by ring
        _ = 2883 * w * a ^ 2 + 2523 * b ^ 2 +
            2523 * (w * (c / wc) ^ 2) := by rw [hprevCancel]
        _ ≤ 2883 * w * a ^ 2 + 2523 * b ^ 2 + 2523 * c ^ 2 := by gcongr
    have hprevOut : ((w / wp) * du) ^ 2 ≤
        972 * (w * a ^ 2 + b ^ 2 + c ^ 2) := by
      rw [mul_pow, hprevCoef]
      calc
        w * du ^ 2 ≤
            w * (972 * (a ^ 2 + (b / wp) ^ 2 + (c / wc) ^ 2)) := by
              gcongr
        _ = 972 * (w * a ^ 2 + w * (b / wp) ^ 2 +
            w * (c / wc) ^ 2) := by ring
        _ = 972 * (w * a ^ 2 + b ^ 2 + w * (c / wc) ^ 2) := by
          rw [hprevCancel]
        _ ≤ 972 * (w * a ^ 2 + b ^ 2 + c ^ 2) := by gcongr
    have hcurrOut : ((w / wc) * dv) ^ 2 ≤
        147 * (w * a ^ 2 + b ^ 2 + c ^ 2) := by
      rw [mul_pow]
      have hstep := mul_le_mul_of_nonneg_right hcurrCoef (sq_nonneg dv)
      calc
        (w / wc) ^ 2 * dv ^ 2 ≤ w * dv ^ 2 := hstep
        _ ≤ w * (147 * (a ^ 2 + (b / wp) ^ 2 + (c / wc) ^ 2)) := by
          gcongr
        _ = 147 * (w * a ^ 2 + w * (b / wp) ^ 2 +
            w * (c / wc) ^ 2) := by ring
        _ = 147 * (w * a ^ 2 + b ^ 2 + w * (c / wc) ^ 2) := by
          rw [hprevCancel]
        _ ≤ 147 * (w * a ^ 2 + b ^ 2 + c ^ 2) := by gcongr
    have hetaEq : residualGateEtaLift N eta y k -
        residualGateEtaLift N theta y' k = w * de := by
      simp [residualGateEtaLift, hk, w, de, kp, wp, wc]
      ring
    have hcurrEq : residualGateCurrentLift N eta y k -
        residualGateCurrentLift N theta y' k = -(w / wc) * dv := by
      simp [residualGateCurrentLift, hk, w, wc, dv, kp, wp]
      ring
    have hprevEq : residualGatePreviousLift N eta y k -
        residualGatePreviousLift N theta y' k = -(w / wp) * du := by
      simp [residualGatePreviousLift, hk, w, wp, du, kp, wc]
      ring
    rw [residualGateOutputSq, residualGateInputSq, hetaEq, hcurrEq, hprevEq]
    simp only [neg_mul, even_two, Even.neg_pow, dite_eq_ite, ge_iff_le]
    rw [if_neg hk]
    have haSq : a ^ 2 = (eta - theta) ^ 2 := sq_abs _
    have hbSq : b ^ 2 = (y kp - y' kp) ^ 2 := sq_abs _
    have hcSq : c ^ 2 = (y k - y' k) ^ 2 := sq_abs _
    have htotal :
        (w * de) ^ 2 / w + (w / wc * dv) ^ 2 + (w / wp * du) ^ 2 ≤
          5000 * (w * a ^ 2 + c ^ 2 + b ^ 2) := by
      calc
        (w * de) ^ 2 / w + (w / wc * dv) ^ 2 + (w / wp * du) ^ 2 ≤
            (2883 * w * a ^ 2 + 2523 * b ^ 2 + 2523 * c ^ 2) +
              (147 * (w * a ^ 2 + b ^ 2 + c ^ 2)) +
              (972 * (w * a ^ 2 + b ^ 2 + c ^ 2)) :=
                add_le_add (add_le_add hetaOut hcurrOut) hprevOut
        _ ≤ 5000 * (w * a ^ 2 + c ^ 2 + b ^ 2) := by
          have hwa : 0 ≤ w * a ^ 2 := mul_nonneg hw.le (sq_nonneg _)
          have hb2 : 0 ≤ b ^ 2 := sq_nonneg _
          have hc2 : 0 ≤ c ^ 2 := sq_nonneg _
          linarith
    rw [haSq, hbSq, hcSq] at htotal
    simpa only [w, wp, wc, kp] using htotal

/-- Summing the local gate inputs costs no dimension factor: scale increments
are weighted by a sequence of total mass below `3`, while each dual
coordinate occurs in at most two adjacent gates. -/
theorem sum_residualGateInputSq_le {N : ℕ} (hN : 2 ≤ N)
    (eta theta : ℝ) (y y' : ChainPoint N) :
    (∑ k : Fin N, residualGateInputSq N eta theta y y' k) ≤
      3 * ((eta - theta) ^ 2 + euclideanNormSq (y - y')) := by
  have hsumOmega : (∑ k : Fin N, omega N k.1) < 3 := by
    have h := sum_omega_lt_three hN
    rw [← Fin.sum_univ_eq_sum_range (fun j ↦ omega N j) N] at h
    exact h
  have heta :
      (∑ k : Fin N, omega N k.1 * (eta - theta) ^ 2) ≤
        3 * (eta - theta) ^ 2 := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hsumOmega.le (sq_nonneg _)
  let d : ChainPoint N := fun k ↦ y k - y' k
  have hprevEq :
      (∑ k : Fin N,
        if hk : k.1 = 0 then 0 else
          (y ⟨k.1 - 1, by omega⟩ - y' ⟨k.1 - 1, by omega⟩) ^ 2) =
        ∑ j : Fin N,
          if hj : j.1 + 1 < N then d j ^ 2 else 0 := by
    have h := sum_predecessor_eq_sum_successor
      (fun _ : Fin N ↦ (1 : ℝ)) (fun j : Fin N ↦ d j ^ 2)
    calc
      (∑ k : Fin N,
          if hk : k.1 = 0 then 0 else
            (y ⟨k.1 - 1, by omega⟩ - y' ⟨k.1 - 1, by omega⟩) ^ 2) =
          ∑ k : Fin N,
            if hk : k.1 = 0 then 0 else
              (1 : ℝ) * d ⟨k.1 - 1, by omega⟩ ^ 2 := by
                apply Finset.sum_congr rfl
                intro k _
                split_ifs <;> simp [d]
      _ = ∑ j : Fin N,
          if hj : j.1 + 1 < N then
            (1 : ℝ) * d j ^ 2 else 0 := h
      _ = ∑ j : Fin N,
          if hj : j.1 + 1 < N then d j ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro j _
            split_ifs <;> simp [d]
  have hprev :
      (∑ k : Fin N,
        if hk : k.1 = 0 then 0 else
          (y ⟨k.1 - 1, by omega⟩ - y' ⟨k.1 - 1, by omega⟩) ^ 2) ≤
        euclideanNormSq (y - y') := by
    rw [hprevEq]
    unfold euclideanNormSq
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · rfl
    · exact sq_nonneg _
  unfold residualGateInputSq
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcurr : (∑ k : Fin N, (y k - y' k) ^ 2) =
      euclideanNormSq (y - y') := by
    simp [euclideanNormSq]
  rw [hcurr]
  have hy0 : 0 ≤ euclideanNormSq (y - y') := euclideanNormSq_nonneg _
  nlinarith

/-- Dimension-uniform Euclidean Lipschitz estimate for the full residual
gradient.  `225^2` is a deliberately coarse numerical constant; most
importantly, it is independent of `N`. -/
theorem embeddedResidualGradient_lipschitz_sq {N : ℕ} (hN : 2 ≤ N)
    {eta theta : ℝ} (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (y y' : ChainPoint N) :
    (embeddedResidualEtaLift N eta y -
        embeddedResidualEtaLift N theta y') ^ 2 +
      euclideanNormSq
        (embeddedResidualYLift N eta y - embeddedResidualYLift N theta y') ≤
      (225 : ℝ) ^ 2 *
        ((eta - theta) ^ 2 + euclideanNormSq (y - y')) := by
  let e : ChainPoint N := fun k ↦
    residualGateEtaLift N eta y k - residualGateEtaLift N theta y' k
  let c : ChainPoint N := fun k ↦
    residualGateCurrentLift N eta y k - residualGateCurrentLift N theta y' k
  let p : ChainPoint N := fun k ↦
    residualGatePreviousLift N eta y k - residualGatePreviousLift N theta y' k
  have hassembly := residualGradient_assembly_energy hN e c p
  have hout :
      (∑ k : Fin N,
        (e k ^ 2 / omega N k.1 + c k ^ 2 + p k ^ 2)) ≤
        5000 * ∑ k : Fin N,
          residualGateInputSq N eta theta y y' k := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    exact residualGateOutputSq_le hN heta htheta y y' k
  have hin := sum_residualGateInputSq_le hN eta theta y y'
  have hnonneg : 0 ≤ (eta - theta) ^ 2 + euclideanNormSq (y - y') := by
    exact add_nonneg (sq_nonneg _) (euclideanNormSq_nonneg _)
  have hbound :
      3 * ∑ k : Fin N,
          (e k ^ 2 / omega N k.1 + c k ^ 2 + p k ^ 2) ≤
        (225 : ℝ) ^ 2 *
          ((eta - theta) ^ 2 + euclideanNormSq (y - y')) := by
    calc
      3 * ∑ k : Fin N,
          (e k ^ 2 / omega N k.1 + c k ^ 2 + p k ^ 2) ≤
          3 * (5000 * ∑ k : Fin N,
            residualGateInputSq N eta theta y y' k) := by gcongr
      _ ≤ 3 * (5000 *
          (3 * ((eta - theta) ^ 2 + euclideanNormSq (y - y')))) := by
            gcongr
      _ ≤ (225 : ℝ) ^ 2 *
          ((eta - theta) ^ 2 + euclideanNormSq (y - y')) := by
            norm_num
            linarith
  have hetaEq : embeddedResidualEtaLift N eta y -
      embeddedResidualEtaLift N theta y' = ∑ k : Fin N, e k := by
    unfold embeddedResidualEtaLift
    rw [← Finset.sum_sub_distrib]
  have hyEq : embeddedResidualYLift N eta y -
      embeddedResidualYLift N theta y' = fun j ↦
        c j + if hj : j.1 + 1 < N then p ⟨j.1 + 1, hj⟩ else 0 := by
    funext j
    simp only [embeddedResidualYLift, Pi.sub_apply]
    dsimp [c, p]
    split_ifs <;> ring
  rw [hetaEq, hyEq, euclideanNormSq] at *
  exact hassembly.trans hbound

/-- Pointwise bound for one scale-gradient gate. -/
theorem abs_residualGateEtaLift_le {N : ℕ} (hN : 2 ≤ N)
    {eta : ℝ} (heta : 0 ≤ eta) (y : ChainPoint N) (k : Fin N) :
    |residualGateEtaLift N eta y k| ≤
      31 * omega N k.1 * eta := by
  have hNpos : 0 < N := by omega
  have hw : 0 ≤ omega N k.1 := (omega_pos hNpos).le
  by_cases hk : k.1 = 0
  · let u := y k / weightSqrt N k
    have hlip := pPerspectiveEtaLift_lipschitz
      (eta := eta) (theta := 0) (u := u) (v := u) heta (by norm_num)
    have hzero : pPerspectiveEtaLift 0 u = 0 := by
      simp [pPerspectiveEtaLift, scaleClipLift]
    have hlip' : |pPerspectiveEtaLift eta u| ≤ 7 * eta := by
      simpa [hzero, abs_of_nonneg heta] using hlip
    have hcore : |2 * eta - pPerspectiveEtaLift eta u| ≤ 9 * eta := by
      calc
        |2 * eta - pPerspectiveEtaLift eta u| ≤
            |2 * eta| + |pPerspectiveEtaLift eta u| := abs_sub _ _
        _ ≤ 2 * eta + 7 * eta := by
          rw [abs_mul, abs_of_nonneg heta]
          norm_num
          exact hlip'
        _ = 9 * eta := by ring
    simp only [residualGateEtaLift]
    split
    · rw [abs_mul, abs_of_nonneg hw]
      have hcore' :
          |2 * eta - pPerspectiveEtaLift eta (y k / weightSqrt N k)| ≤
            9 * eta := by simpa [u] using hcore
      exact (mul_le_mul_of_nonneg_left hcore' hw).trans (by
        have heta0 := heta
        nlinarith)
    · contradiction
  · let kp : Fin N := ⟨k.1 - 1, by omega⟩
    let u := y kp / weightSqrt N kp
    let v := y k / weightSqrt N k
    have hlip := qpPerspectiveEtaLift_lipschitz
      (eta := eta) (theta := 0) (u := u) (v := v)
      (u' := u) (v' := v) heta (by norm_num)
    have hzero : qpPerspectiveEtaLift 0 u v = 0 := by
      simp [qpPerspectiveEtaLift, scaleClipPairLift]
    have hlip' : |qpPerspectiveEtaLift eta u v| ≤ 29 * eta := by
      simpa [hzero, abs_of_nonneg heta] using hlip
    have hcore : |2 * eta - qpPerspectiveEtaLift eta u v| ≤ 31 * eta := by
      calc
        |2 * eta - qpPerspectiveEtaLift eta u v| ≤
            |2 * eta| + |qpPerspectiveEtaLift eta u v| := abs_sub _ _
        _ ≤ 2 * eta + 29 * eta := by
          rw [abs_mul, abs_of_nonneg heta]
          norm_num
          exact hlip'
        _ = 31 * eta := by ring
    simp only [residualGateEtaLift]
    split
    · contradiction
    · rw [abs_mul, abs_of_nonneg hw]
      have hcore' :
          |2 * eta - qpPerspectiveEtaLift eta
            (y ⟨k.1 - 1, by omega⟩ / weightSqrt N ⟨k.1 - 1, by omega⟩)
            (y k / weightSqrt N k)| ≤ 31 * eta := by
        simpa [u, v, kp] using hcore
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hcore' hw

/-- Uniform value bound for the residual scale derivative on the scale range
used by the Carmon embedding. -/
theorem abs_embeddedResidualEtaLift_le {N : ℕ} (hN : 2 ≤ N)
    {eta : ℝ} (heta0 : 0 ≤ eta) (heta2 : eta ≤ 2)
    (y : ChainPoint N) :
    |embeddedResidualEtaLift N eta y| ≤ 186 := by
  have hsumOmega : (∑ k : Fin N, omega N k.1) < 3 := by
    have h := sum_omega_lt_three hN
    rw [← Fin.sum_univ_eq_sum_range (fun j ↦ omega N j) N] at h
    exact h
  calc
    |embeddedResidualEtaLift N eta y| =
        |∑ k : Fin N, residualGateEtaLift N eta y k| := rfl
    _ ≤ ∑ k : Fin N, |residualGateEtaLift N eta y k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin N, 31 * omega N k.1 * eta := by
      apply Finset.sum_le_sum
      intro k _
      exact abs_residualGateEtaLift_le hN heta0 y k
    _ = 31 * eta * ∑ k : Fin N, omega N k.1 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ 31 * eta * 3 := by
      exact mul_le_mul_of_nonneg_left hsumOmega.le
        (mul_nonneg (by norm_num) heta0)
    _ ≤ 186 := by nlinarith

/-- The scale component alone inherits the same dimension-free squared
Lipschitz estimate. -/
theorem embeddedResidualEtaLift_lipschitz_sq {N : ℕ} (hN : 2 ≤ N)
    {eta theta : ℝ} (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (y y' : ChainPoint N) :
    (embeddedResidualEtaLift N eta y -
        embeddedResidualEtaLift N theta y') ^ 2 ≤
      (225 : ℝ) ^ 2 *
        ((eta - theta) ^ 2 + euclideanNormSq (y - y')) := by
  have h := embeddedResidualGradient_lipschitz_sq hN heta htheta y y'
  have hy0 : 0 ≤ euclideanNormSq
      (embeddedResidualYLift N eta y - embeddedResidualYLift N theta y') :=
    euclideanNormSq_nonneg _
  linarith

/-! ## Actual derivative assembly -/

/-- The displayed scale component is the actual derivative of one
totalized gate value. -/
theorem hasDerivAt_residualGateValue (N : ℕ) (eta : ℝ)
    (y : ChainPoint N) (k : Fin N) :
    HasResidualDerivAt (fun e : ℝ ↦ residualGateValue N e y k)
      (residualGateEtaLift N eta y k) eta := by
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasResidualDerivAt
  by_cases hk : k.1 = 0
  · have hp := hasDerivAt_pPerspective_scale eta
      (y k / weightSqrt N k)
    unfold HasResidualDerivAt at hp
    have hsq := (hasDerivAt_id eta).pow 2
    have h := (hsq.sub hp).const_mul (omega N k.1)
    simpa [residualGateValue, residualGateEtaLift, hk, mul_sub] using h
  · have hp := hasDerivAt_qpPerspective_scale eta
      (y ⟨k.1 - 1, by omega⟩ / weightSqrt N ⟨k.1 - 1, by omega⟩)
      (y k / weightSqrt N k)
    unfold HasResidualDerivAt at hp
    have hsq := (hasDerivAt_id eta).pow 2
    have h := (hsq.sub hp).const_mul (omega N k.1)
    simpa [residualGateValue, residualGateEtaLift, hk, mul_sub] using h

/-- Exact actual scale derivative of the total residual value, including
the zero-scale hyperplane. -/
theorem hasDerivAt_embeddedResidualAtScale (N : ℕ)
    (eta : ℝ) (y : ChainPoint N) :
    HasResidualDerivAt (fun e : ℝ ↦ embeddedResidualAtScale N e y)
      (embeddedResidualEtaLift N eta y) eta := by
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasResidualDerivAt
  have hsum : HasDerivAt
      (fun e : ℝ ↦ ∑ k : Fin N, residualGateValue N e y k)
      (∑ k : Fin N, residualGateEtaLift N eta y k) eta := by
    apply HasDerivAt.fun_sum
    intro k _
    have hk := hasDerivAt_residualGateValue N eta y k
    unfold HasResidualDerivAt at hk
    exact hk
  simpa [embeddedResidualAtScale_eq_sum_gateValue,
    embeddedResidualEtaLift] using hsum

end

end NCPLRevised
