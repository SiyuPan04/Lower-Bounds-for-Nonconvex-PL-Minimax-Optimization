/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.DualChainDerivative

/-!
# The scaled perspective block (Lemma 4.4)

This file formalizes the diagonal normalization and perspective scaling in
Section 4.2 of *Lower Bounds for Nonconvex-PL Minimax Optimization*.

For Lean coordinate `k : Fin N`, which represents the paper coordinate
`y_{k+1}`, the diagonal entry of `W` is `sqrt (omega N (k+1))`.  The
definition below is totalized at `eta = 0` by the second branch from the
paper.  All theorems matching Lemma 4.4 retain its hypotheses
`0 <= eta`, `0 <= alpha`, and `alpha <= 10 * eta^2`.
-/

namespace NCPLRevised

noncomputable section

/-- The diagonal entry `sqrt(omega_{k+1})` of the paper's matrix `W`. -/
def weightSqrt (N : ℕ) (k : Fin N) : ℝ :=
  Real.sqrt (omega N (k.1 + 1))

/-- `W⁻¹ y / eta`, written coordinatewise. -/
def perspectiveNormalize (N : ℕ) (eta : ℝ) (y : ChainPoint N) : ChainPoint N :=
  fun k ↦ y k / (eta * weightSqrt N k)

/-- `eta W u`, the inverse coordinate change when `eta != 0`. -/
def perspectiveScale (N : ℕ) (eta : ℝ) (u : ChainPoint N) : ChainPoint N :=
  fun k ↦ eta * weightSqrt N k * u k

/-- The squared Euclidean norm on the paper's finite-dimensional space. -/
def euclideanNormSq {N : ℕ} (y : ChainPoint N) : ℝ :=
  ∑ k : Fin N, (y k) ^ 2

/-- The branch `-1/2 ||y^-||²` used at zero perspective scale. -/
def zeroPerspectiveBlock {N : ℕ} (y : ChainPoint N) : ℝ :=
  -(1 / 2 : ℝ) * ∑ k : Fin N, (negPart (y k)) ^ 2

/-- The scaled block `B(eta, alpha; y)` from Lemma 4.4. -/
def scaledPerspectiveBlock (N : ℕ) (eta alpha : ℝ) (y : ChainPoint N) : ℝ :=
  if eta = 0 then
    zeroPerspectiveBlock y
  else
    eta ^ 2 * coupledDual N (alpha / eta ^ 2) (perspectiveNormalize N eta y)

/-- The explicit Euclidean `y`-gradient of `scaledPerspectiveBlock`. -/
def scaledPerspectiveGradient (N : ℕ) (eta alpha : ℝ)
    (y : ChainPoint N) : ChainPoint N :=
  if eta = 0 then
    fun k ↦ negPart (y k)
  else
    fun k ↦ eta / weightSqrt N k *
      coupledGradient N (alpha / eta ^ 2) (perspectiveNormalize N eta y) k

/-- The normalization as a continuous linear map. -/
def perspectiveNormalizeCLM (N : ℕ) (eta : ℝ) :
    ChainPoint N →L[ℝ] ChainPoint N :=
  ContinuousLinearMap.pi fun k ↦
    (1 / (eta * weightSqrt N k)) •
      (ContinuousLinearMap.proj k : ChainPoint N →L[ℝ] ℝ)

@[simp] theorem perspectiveNormalizeCLM_apply (N : ℕ) (eta : ℝ)
    (y : ChainPoint N) :
    perspectiveNormalizeCLM N eta y = perspectiveNormalize N eta y := by
  funext k
  simp [perspectiveNormalizeCLM, perspectiveNormalize, div_eq_mul_inv,
    mul_comm]

theorem weightSqrt_pos {N : ℕ} (hN : 0 < N) (k : Fin N) :
    0 < weightSqrt N k := by
  exact Real.sqrt_pos.2 (omega_pos hN)

theorem weightSqrt_sq {N : ℕ} (hN : 0 < N) (k : Fin N) :
    weightSqrt N k ^ 2 = omega N (k.1 + 1) := by
  exact Real.sq_sqrt (omega_pos hN).le

theorem perspectiveNormalize_scale {N : ℕ} (hN : 0 < N)
    {eta : ℝ} (heta : eta ≠ 0) (u : ChainPoint N) :
    perspectiveNormalize N eta (perspectiveScale N eta u) = u := by
  funext k
  unfold perspectiveNormalize perspectiveScale
  field_simp [heta, ne_of_gt (weightSqrt_pos hN k)]

theorem perspectiveScale_normalize {N : ℕ} (hN : 0 < N)
    {eta : ℝ} (heta : eta ≠ 0) (y : ChainPoint N) :
    perspectiveScale N eta (perspectiveNormalize N eta y) = y := by
  funext k
  unfold perspectiveNormalize perspectiveScale
  field_simp [heta, ne_of_gt (weightSqrt_pos hN k)]

/-- The normalized scalar target lies in the interval required by Lemma 4.3. -/
theorem normalizedTarget_mem {eta alpha : ℝ} (heta : eta ≠ 0)
    (halpha0 : 0 ≤ alpha) (halpha10 : alpha ≤ 10 * eta ^ 2) :
    0 ≤ alpha / eta ^ 2 ∧ alpha / eta ^ 2 ≤ 10 := by
  have hetaSq : 0 < eta ^ 2 := sq_pos_of_ne_zero heta
  constructor
  · exact div_nonneg halpha0 hetaSq.le
  · exact (div_le_iff₀ hetaSq).2 (by simpa [mul_comm] using halpha10)

@[simp] theorem euclideanNormSq_nonneg {N : ℕ} (y : ChainPoint N) :
    0 ≤ euclideanNormSq y := by
  exact Finset.sum_nonneg fun k _ ↦ sq_nonneg (y k)

/-- A point attaining the maximum of the scaled block. -/
def scaledPerspectiveMaximizer (N : ℕ) (eta : ℝ) : ChainPoint N :=
  if eta = 0 then 0 else perspectiveScale N eta (fun _ ↦ 1)

private theorem alpha_eq_zero_of_eta_eq_zero {eta alpha : ℝ}
    (heta : eta = 0) (halpha0 : 0 ≤ alpha)
    (halpha10 : alpha ≤ 10 * eta ^ 2) :
    alpha = 0 := by
  subst eta
  norm_num at halpha10
  linarith

theorem zeroPerspectiveBlock_nonpos {N : ℕ} (y : ChainPoint N) :
    zeroPerspectiveBlock y ≤ 0 := by
  unfold zeroPerspectiveBlock
  have hsum : 0 ≤ ∑ k : Fin N, negPart (y k) ^ 2 :=
    Finset.sum_nonneg fun k _ ↦ sq_nonneg _
  nlinarith

@[simp] theorem zeroPerspectiveBlock_zero (N : ℕ) :
    zeroPerspectiveBlock (0 : ChainPoint N) = 0 := by
  simp [zeroPerspectiveBlock, negPart]

/-- Exact maximization statement from Lemma 4.4, represented constructively by
an upper bound and an explicit attaining point. -/
theorem scaledPerspectiveBlock_max {N : ℕ} (hN : 2 ≤ N)
    {eta alpha : ℝ} (_heta0 : 0 ≤ eta) (halpha0 : 0 ≤ alpha)
    (halpha10 : alpha ≤ 10 * eta ^ 2) :
    (∀ y : ChainPoint N, scaledPerspectiveBlock N eta alpha y ≤ alpha) ∧
      scaledPerspectiveBlock N eta alpha (scaledPerspectiveMaximizer N eta) = alpha := by
  by_cases heta : eta = 0
  · have halpha : alpha = 0 :=
      alpha_eq_zero_of_eta_eq_zero heta halpha0 halpha10
    subst eta
    subst alpha
    constructor
    · intro y
      simpa [scaledPerspectiveBlock] using zeroPerspectiveBlock_nonpos y
    · simp [scaledPerspectiveBlock, scaledPerspectiveMaximizer]
  · have htarget := normalizedTarget_mem heta halpha0 halpha10
    have hinner := coupledDual_max hN htarget.1
    have hetaSq : 0 ≤ eta ^ 2 := sq_nonneg eta
    constructor
    · intro y
      rw [scaledPerspectiveBlock, if_neg heta]
      have hupper := hinner.1 (perspectiveNormalize N eta y)
      have hmul := mul_le_mul_of_nonneg_left hupper hetaSq
      have halphaScale : eta ^ 2 * (alpha / eta ^ 2) = alpha := by
        field_simp [pow_ne_zero 2 heta]
      simpa [halphaScale] using hmul
    · rw [scaledPerspectiveMaximizer, if_neg heta]
      rw [scaledPerspectiveBlock, if_neg heta]
      rw [perspectiveNormalize_scale (by omega : 0 < N) heta]
      rw [hinner.2]
      field_simp [pow_ne_zero 2 heta]

/-- Under a nonzero perspective scale, the Euclidean gradient norm is exactly
`eta²` times the weighted dual norm of the normalized block. -/
theorem euclideanNormSq_scaledPerspectiveGradient_of_ne {N : ℕ}
    (hN : 0 < N) {eta alpha : ℝ} (heta : eta ≠ 0) (y : ChainPoint N) :
    euclideanNormSq (scaledPerspectiveGradient N eta alpha y) =
      eta ^ 2 * weightedDualNormSq N
        (coupledGradient N (alpha / eta ^ 2) (perspectiveNormalize N eta y)) := by
  unfold euclideanNormSq weightedDualNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [scaledPerspectiveGradient, if_neg heta]
  have hw : 0 < omega N (k.1 + 1) := omega_pos hN
  have hs := weightSqrt_sq hN k
  field_simp [ne_of_gt hw, ne_of_gt (weightSqrt_pos hN k)]
  nlinarith

@[simp] theorem euclideanNormSq_scaledPerspectiveGradient_zero
    (N : ℕ) (alpha : ℝ) (y : ChainPoint N) :
    euclideanNormSq (scaledPerspectiveGradient N 0 alpha y) =
      ∑ k : Fin N, negPart (y k) ^ 2 := by
  simp [euclideanNormSq, scaledPerspectiveGradient]

/-- The Euclidean dual PL inequality in Lemma 4.4. -/
theorem scaledPerspectiveBlock_PL {N : ℕ} (hN : 2 ≤ N)
    {eta alpha : ℝ} (heta0 : 0 ≤ eta) (halpha0 : 0 ≤ alpha)
    (halpha10 : alpha ≤ 10 * eta ^ 2) (y : ChainPoint N) :
    (1 / 2 : ℝ) * euclideanNormSq (scaledPerspectiveGradient N eta alpha y) ≥
      (1 / (640 * (N : ℝ))) *
        (alpha - scaledPerspectiveBlock N eta alpha y) := by
  by_cases heta : eta = 0
  · have halpha : alpha = 0 :=
      alpha_eq_zero_of_eta_eq_zero heta halpha0 halpha10
    subst eta
    subst alpha
    rw [euclideanNormSq_scaledPerspectiveGradient_zero]
    simp only [scaledPerspectiveBlock, zeroPerspectiveBlock]
    let S := ∑ k : Fin N, negPart (y k) ^ 2
    have hS : 0 ≤ S := Finset.sum_nonneg fun k _ ↦ sq_nonneg _
    have hNreal : 2 ≤ (N : ℝ) := by exact_mod_cast hN
    dsimp [S] at hS ⊢
    have hcoef : (1 / (640 * (N : ℝ)) : ℝ) ≤ 1 := by
      have hden : (1 : ℝ) ≤ 640 * (N : ℝ) := by nlinarith
      exact (div_le_one (by positivity)).2 hden
    nlinarith
  · have htarget := normalizedTarget_mem heta halpha0 halpha10
    have hinner := coupledDual_weighted_PL hN htarget.1 htarget.2
      (perspectiveNormalize N eta y)
    have hetaSq : 0 < eta ^ 2 := sq_pos_of_ne_zero heta
    have hmul := mul_le_mul_of_nonneg_left hinner hetaSq.le
    rw [euclideanNormSq_scaledPerspectiveGradient_of_ne (by omega : 0 < N) heta]
    rw [scaledPerspectiveBlock, if_neg heta]
    calc
      (1 / (640 * (N : ℝ))) *
            (alpha - eta ^ 2 *
              coupledDual N (alpha / eta ^ 2) (perspectiveNormalize N eta y)) =
          eta ^ 2 * (1 / (640 * (N : ℝ)) *
            (alpha / eta ^ 2 -
              coupledDual N (alpha / eta ^ 2) (perspectiveNormalize N eta y))) := by
            field_simp [pow_ne_zero 2 heta]
      _ ≤ eta ^ 2 * ((1 / 2 : ℝ) * weightedDualNormSq N
            (coupledGradient N (alpha / eta ^ 2) (perspectiveNormalize N eta y))) := hmul
      _ = (1 / 2 : ℝ) * (eta ^ 2 * weightedDualNormSq N
            (coupledGradient N (alpha / eta ^ 2) (perspectiveNormalize N eta y))) := by
            ring

private theorem hasDerivAt_zeroPerspectiveBlock_update {N : ℕ}
    (y : ChainPoint N) (k : Fin N) :
    HasDerivAt (fun t : ℝ ↦ zeroPerspectiveBlock (Function.update y k t))
      (negPart (y k)) (y k) := by
  have hsum0 : HasDerivAt
      (fun t : ℝ ↦ ∑ i : Fin N,
        negPart ((Function.update y k t) i) ^ 2)
      (∑ i : Fin N, if i = k then -2 * negPart (y k) else 0) (y k) := by
    apply HasDerivAt.fun_sum
    intro i _
    by_cases hi : i = k
    · subst i
      simpa using hasDerivAt_negPartSq (y k)
    · have heq :
          (fun t : ℝ ↦ negPart ((Function.update y k t) i) ^ 2) =
            (fun _t : ℝ ↦ negPart (y i) ^ 2) := by
          funext t
          simp [hi]
      rw [heq]
      simpa [hi] using hasDerivAt_const (x := y k) (c := negPart (y i) ^ 2)
  have hderiv :
      (∑ i : Fin N, if i = k then -2 * negPart (y k) else 0) =
        -2 * negPart (y k) := by
    simp
  have hsum : HasDerivAt
      (fun t : ℝ ↦ ∑ i : Fin N,
        negPart ((Function.update y k t) i) ^ 2)
      (-2 * negPart (y k)) (y k) := by
    simpa only [hderiv] using hsum0
  have hscaled := hsum.const_mul (-(1 / 2 : ℝ))
  convert hscaled using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext t
    rfl
  · ring

private theorem differentiableAt_zeroPerspectiveBlock {N : ℕ}
    (y : ChainPoint N) :
    DifferentiableAt ℝ zeroPerspectiveBlock y := by
  unfold zeroPerspectiveBlock
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.fun_sum
  intro k _
  have hcoord : DifferentiableAt ℝ (fun z : ChainPoint N ↦ z k) y := by
    fun_prop
  simpa only [Function.comp_def] using
    (hasDerivAt_negPartSq (y k)).differentiableAt.comp y hcoord

private theorem fderiv_zeroPerspectiveBlock_single {N : ℕ}
    (y : ChainPoint N) (k : Fin N) :
    fderiv ℝ zeroPerspectiveBlock y (Pi.single k (1 : ℝ)) = negPart (y k) := by
  have hF := (differentiableAt_zeroPerspectiveBlock y).hasFDerivAt
  have hy : y = Function.update y k (y k) := by
    funext i
    by_cases hi : i = k
    · subst i
      simp
    · simp [hi]
  have hline := hF.comp_hasDerivAt_of_eq (y k)
    (hasDerivAt_update y k (y k)) hy
  have hline' : HasDerivAt
      (fun t : ℝ ↦ zeroPerspectiveBlock (Function.update y k t))
      (fderiv ℝ zeroPerspectiveBlock y (Pi.single k (1 : ℝ))) (y k) := by
    simpa only [Function.comp_def] using hline
  exact hline'.unique (hasDerivAt_zeroPerspectiveBlock_update y k)

private theorem chainPoint_eq_sum_single {N : ℕ} (v : ChainPoint N) :
    v = ∑ k : Fin N, v k • Pi.single k (1 : ℝ) := by
  funext i
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji.symm]

private theorem fderiv_zeroPerspectiveBlock_eq (N : ℕ) (y : ChainPoint N) :
    fderiv ℝ zeroPerspectiveBlock y =
      finiteDotProductCLM (fun k ↦ negPart (y k)) := by
  apply ContinuousLinearMap.ext
  intro v
  calc
    fderiv ℝ zeroPerspectiveBlock y v =
        fderiv ℝ zeroPerspectiveBlock y
          (∑ k : Fin N, v k • Pi.single k (1 : ℝ)) := by
            rw [← chainPoint_eq_sum_single v]
    _ = ∑ k : Fin N, v k * negPart (y k) := by
          simp [fderiv_zeroPerspectiveBlock_single, smul_eq_mul]
    _ = finiteDotProductCLM (fun k ↦ negPart (y k)) v := by
          rw [finiteDotProductCLM_apply]
          apply Finset.sum_congr rfl
          intro k _
          ring

private theorem hasFDerivAt_zeroPerspectiveBlock {N : ℕ} (y : ChainPoint N) :
    HasFDerivAt zeroPerspectiveBlock
      (finiteDotProductCLM (fun k ↦ negPart (y k))) y :=
  (differentiableAt_zeroPerspectiveBlock y).hasFDerivAt.congr_fderiv
    (fderiv_zeroPerspectiveBlock_eq N y)

private theorem scaledDerivativeCLM_eq {N : ℕ} (hN : 0 < N)
    {eta alpha : ℝ} (heta : eta ≠ 0) (y : ChainPoint N) :
    eta ^ 2 •
        ((finiteDotProductCLM
          (coupledGradient N (alpha / eta ^ 2) (perspectiveNormalize N eta y))).comp
            (perspectiveNormalizeCLM N eta)) =
      finiteDotProductCLM (scaledPerspectiveGradient N eta alpha y) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    finiteDotProductCLM_apply, perspectiveNormalizeCLM_apply,
    perspectiveNormalize, scaledPerspectiveGradient, if_neg heta]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hw : weightSqrt N k ≠ 0 := ne_of_gt (weightSqrt_pos hN k)
  field_simp [heta, hw]

/-- The displayed vector field is the actual full Fréchet derivative with
respect to the dual variable, including the `eta = 0` splice. -/
theorem hasFDerivAt_scaledPerspectiveBlock {N : ℕ} (hN : 2 ≤ N)
    (eta alpha : ℝ) (y : ChainPoint N) :
    HasFDerivAt (scaledPerspectiveBlock N eta alpha)
      (finiteDotProductCLM (scaledPerspectiveGradient N eta alpha y)) y := by
  by_cases heta : eta = 0
  · subst eta
    rw [show scaledPerspectiveBlock N 0 alpha = zeroPerspectiveBlock by
      funext z
      simp [scaledPerspectiveBlock]]
    rw [show scaledPerspectiveGradient N 0 alpha y =
        (fun k ↦ negPart (y k)) by
      funext k
      simp [scaledPerspectiveGradient]]
    exact hasFDerivAt_zeroPerspectiveBlock y
  · have hinner := hasFDerivAt_coupledDual N (alpha / eta ^ 2)
      (perspectiveNormalize N eta y)
    have hnorm : HasFDerivAt (perspectiveNormalize N eta)
        (perspectiveNormalizeCLM N eta) y := by
      refine (perspectiveNormalizeCLM N eta).hasFDerivAt.congr_of_eventuallyEq ?_
      filter_upwards with z
      exact (perspectiveNormalizeCLM_apply N eta z).symm
    have hcomp0 := hinner.comp y hnorm
    have hcomp : HasFDerivAt
        (fun z : ChainPoint N ↦
          coupledDual N (alpha / eta ^ 2) (perspectiveNormalize N eta z))
        ((finiteDotProductCLM
          (coupledGradient N (alpha / eta ^ 2) (perspectiveNormalize N eta y))).comp
            (perspectiveNormalizeCLM N eta)) y := by
      simpa only [Function.comp_def, perspectiveNormalizeCLM_apply] using hcomp0
    have hscaled := hcomp.const_mul (eta ^ 2)
    rw [show scaledPerspectiveBlock N eta alpha =
        (fun z : ChainPoint N ↦ eta ^ 2 *
          coupledDual N (alpha / eta ^ 2) (perspectiveNormalize N eta z)) by
      funext z
      simp [scaledPerspectiveBlock, heta]]
    exact hscaled.congr_fderiv
      (scaledDerivativeCLM_eq (by omega : 0 < N) heta y)

/-- A set-theoretic version of the exact maximum statement. -/
theorem scaledPerspectiveBlock_isGreatest {N : ℕ} (hN : 2 ≤ N)
    {eta alpha : ℝ} (heta0 : 0 ≤ eta) (halpha0 : 0 ≤ alpha)
    (halpha10 : alpha ≤ 10 * eta ^ 2) :
    IsGreatest (Set.range (scaledPerspectiveBlock N eta alpha)) alpha := by
  have hmax := scaledPerspectiveBlock_max hN heta0 halpha0 halpha10
  constructor
  · exact ⟨scaledPerspectiveMaximizer N eta, hmax.2⟩
  · rintro _ ⟨y, rfl⟩
    exact hmax.1 y

theorem perspectiveNormalize_terminal {N : ℕ} (hN : 0 < N)
    (eta : ℝ) (y : ChainPoint N) :
    chainCoord (perspectiveNormalize N eta y) (N - 1) =
      chainCoord y (N - 1) / eta := by
  have hlast : N - 1 < N := by omega
  have hone : 1 ≤ N := by omega
  have hindex : N - 1 + 1 = N := Nat.sub_add_cancel hone
  simp [chainCoord, hlast, perspectiveNormalize, weightSqrt, hindex]

/-- Equation (12): for positive scale, differentiating the block with
respect to its scalar target exposes only the terminal gate. -/
theorem hasDerivAt_scaledPerspectiveBlock_alpha_of_ne {N : ℕ} (hN : 0 < N)
    {eta : ℝ} (heta : eta ≠ 0) (alpha : ℝ) (y : ChainPoint N) :
    HasDerivAt (fun a : ℝ ↦ scaledPerspectiveBlock N eta a y)
      (q (chainCoord y (N - 1) / eta)) alpha := by
  let u := perspectiveNormalize N eta y
  let terminalGate := q (chainCoord u (N - 1))
  have hlinear := (((hasDerivAt_id alpha).div_const (eta ^ 2)).mul_const terminalGate).sub_const
    (dualChain N u)
  have hscaled := hlinear.const_mul (eta ^ 2)
  have hterminal : terminalGate = q (chainCoord y (N - 1) / eta) := by
    dsimp [terminalGate, u]
    rw [perspectiveNormalize_terminal hN]
  convert hscaled using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext a
    simp only [scaledPerspectiveBlock, if_neg heta, coupledDual]
    dsimp [u, terminalGate]
  · rw [← hterminal]
    field_simp [pow_ne_zero 2 heta]

/-- Lemma 4.4 bundled with its exact maximum, PL inequality, and certified
Fréchet gradient. -/
theorem lemma4_4 {N : ℕ} (hN : 2 ≤ N)
    {eta alpha : ℝ} (heta0 : 0 ≤ eta) (halpha0 : 0 ≤ alpha)
    (halpha10 : alpha ≤ 10 * eta ^ 2) :
    IsGreatest (Set.range (scaledPerspectiveBlock N eta alpha)) alpha ∧
      (∀ y : ChainPoint N,
        (1 / 2 : ℝ) * euclideanNormSq (scaledPerspectiveGradient N eta alpha y) ≥
          (1 / (640 * (N : ℝ))) *
            (alpha - scaledPerspectiveBlock N eta alpha y)) ∧
      (∀ y : ChainPoint N,
        HasFDerivAt (scaledPerspectiveBlock N eta alpha)
          (finiteDotProductCLM (scaledPerspectiveGradient N eta alpha y)) y) := by
  exact ⟨scaledPerspectiveBlock_isGreatest hN heta0 halpha0 halpha10,
    fun y ↦ scaledPerspectiveBlock_PL hN heta0 halpha0 halpha10 y,
    hasFDerivAt_scaledPerspectiveBlock hN eta alpha⟩

end

end NCPLRevised
