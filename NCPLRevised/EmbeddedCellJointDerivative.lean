/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.EmbeddedCellSmoothness
import NCPLRevised.OuterLinearAlgebra

/-!
# Joint Fréchet derivative of the embedded cell

This module proves joint differentiability of the exact embedded cell,
including every point on the degenerate hyperplane `rho(s)=0`.  The proof at
zero scale is quantitative: after subtracting the negative-part penalty, the
whole cell is bounded by `18 rho(s)^2`.  Since `rho` is Lipschitz and flat at
the interfaces, this remainder has zero Fréchet derivative there.
-/

namespace NCPLRevised

noncomputable section

/-- Joint variables `(s,t,y)` of one embedded cell. -/
abbrev CellPoint (N : ℕ) := ℝ × (ℝ × ChainPoint N)

def embeddedCellOnPoint (N : ℕ) (z : CellPoint N) : ℝ :=
  embeddedCell N z.1 z.2.1 z.2.2

/-- Joint differentiability with the norm-topology instances fixed
explicitly, avoiding the `Prod`/norm-induced typeclass diamond. -/
def CellDifferentiableAt (N : ℕ) (f : CellPoint N → ℝ)
    (z : CellPoint N) : Prop :=
  @DifferentiableAt ℝ _ (CellPoint N)
    Prod.normedAddCommGroup.toAddCommGroup Prod.normedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace ℝ
    Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace f z

def cellSCLM (N : ℕ) : CellPoint N →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ (ℝ × ChainPoint N)

def cellTCLM (N : ℕ) : CellPoint N →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (ChainPoint N)).comp
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ChainPoint N))

def cellYCLM (N : ℕ) : CellPoint N →L[ℝ] ChainPoint N :=
  (ContinuousLinearMap.snd ℝ ℝ (ChainPoint N)).comp
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ChainPoint N))

@[simp] theorem cellSCLM_apply {N : ℕ} (z : CellPoint N) :
    cellSCLM N z = z.1 := rfl

@[simp] theorem cellTCLM_apply {N : ℕ} (z : CellPoint N) :
    cellTCLM N z = z.2.1 := rfl

@[simp] theorem cellYCLM_apply {N : ℕ} (z : CellPoint N) :
    cellYCLM N z = z.2.2 := rfl

/-- A coordinate of `ChainPoint N`, totalized in the same way as
`chainCoord`. -/
def chainCoordCLM (N j : ℕ) : ChainPoint N →L[ℝ] ℝ :=
  if hj : j < N then
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N ↦ ℝ) ⟨j, hj⟩
  else 0

@[simp] theorem chainCoordCLM_apply (N j : ℕ) (y : ChainPoint N) :
    chainCoordCLM N j y = chainCoord y j := by
  unfold chainCoordCLM chainCoord
  split_ifs <;> rfl

/-! ## Uniform quadratic control at zero scale -/

theorem gateTerm_le_one {N : ℕ} (y : ChainPoint N) (k : Fin N) :
    gateTerm y k ≤ 1 := by
  unfold gateTerm
  exact sub_le_self _ (mul_nonneg (q_nonneg _) (p_nonneg _))

theorem weighted_gate_sum_nonneg {N : ℕ} (hN : 0 < N)
    (y : ChainPoint N) :
    0 ≤ ∑ k : Fin N, omega N k.1 * gateTerm y k := by
  exact Finset.sum_nonneg fun k _ ↦
    mul_nonneg (omega_pos hN).le (gateTerm_nonneg y k)

theorem weighted_gate_sum_lt_three {N : ℕ} (hN : 2 ≤ N)
    (y : ChainPoint N) :
    (∑ k : Fin N, omega N k.1 * gateTerm y k) < 3 := by
  calc
    (∑ k : Fin N, omega N k.1 * gateTerm y k) ≤
        ∑ k : Fin N, omega N k.1 := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_of_le_one_right (omega_pos (by omega : 0 < N)).le
        (gateTerm_le_one y k)
    _ < 3 := by
      rw [Fin.sum_univ_eq_sum_range]
      exact sum_omega_lt_three hN

theorem zeroPerspectiveBlock_eq_negPartNormSq {N : ℕ} (y : ChainPoint N) :
    zeroPerspectiveBlock y = -(1 / 2 : ℝ) * negPartNormSq y := rfl

/-- The value estimate `Cnu-bound-2` needed to cross `eta=0`, with a
fully explicit numerical constant. -/
theorem embeddedCell_remainder_bound {N : ℕ} (hN : 2 ≤ N)
    (s t : ℝ) (y : ChainPoint N) :
    |embeddedCell N s t y - zeroPerspectiveBlock y| ≤
      18 * outerRho s ^ 2 := by
  by_cases hrho : outerRho s = 0
  · simp [embeddedCell, scaledPerspectiveBlock, hrho]
  · have hrhopos : 0 < outerRho s :=
      lt_of_le_of_ne (outerRho_nonneg s) (Ne.symm hrho)
    rw [embeddedCell_expanded_of_rho_pos (by omega : 0 < N) hrhopos]
    rw [zeroPerspectiveBlock_eq_negPartNormSq]
    let T := embeddedTerminal N s y
    let R := embeddedResidual N s y
    have hT0 : 0 ≤ T := q_nonneg _
    have hT1 : T ≤ 1 := q_le_one _
    have ha0 := carmonLiftedH_nonneg s t
    have ha1 := carmonLiftedH_le_ten_rho_sq s t
    have hprod0 : 0 ≤ carmonLiftedH s t * T := mul_nonneg ha0 hT0
    have hprod1 : carmonLiftedH s t * T ≤ 10 * outerRho s ^ 2 := by
      exact (mul_le_mul ha1 hT1 hT0 (by positivity)).trans_eq (by ring)
    have hsum0 := weighted_gate_sum_nonneg (by omega : 0 < N)
      (embeddedNormalized N s y)
    have hsum1 := weighted_gate_sum_lt_three hN
      (embeddedNormalized N s y)
    have hR0 : 0 ≤ R := by
      exact mul_nonneg (sq_nonneg _) hsum0
    have hR1 : R < 3 * outerRho s ^ 2 := by
      unfold R embeddedResidual
      have hsqpos : 0 < outerRho s ^ 2 := sq_pos_of_pos hrhopos
      nlinarith
    dsimp [T, R] at hT0 hT1 hprod0 hprod1 hR0 hR1 ⊢
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (outerRho s)]

/-- The derivative bound on `rho` also gives a global Lipschitz bound on
`rho` itself. -/
theorem outerRho_lipschitz_sixtyFour :
    LipschitzWith (64 : NNReal) outerRho := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_outerRho
  intro s
  rw [deriv_outerRho, ← NNReal.coe_le_coe]
  simpa [Real.norm_eq_abs] using abs_outerRhoDeriv_le_sixtyFour s

/-! ## Differentiability away from and on the flat interface -/

/-- Joint differentiability of `(alpha,y) ↦ G(alpha;y)`. -/
theorem differentiableAt_coupledDual_joint (N : ℕ)
    (z : ℝ × ChainPoint N) :
    DifferentiableAt ℝ (fun w : ℝ × ChainPoint N ↦
      coupledDual N w.1 w.2) z := by
  have ha : DifferentiableAt ℝ (fun w : ℝ × ChainPoint N ↦ w.1) z :=
    (ContinuousLinearMap.fst ℝ ℝ (ChainPoint N)).differentiableAt
  have hy : DifferentiableAt ℝ (fun w : ℝ × ChainPoint N ↦ w.2) z :=
    (ContinuousLinearMap.snd ℝ ℝ (ChainPoint N)).differentiableAt
  have hcoord : DifferentiableAt ℝ
      (fun w : ℝ × ChainPoint N ↦ chainCoord w.2 (N - 1)) z :=
    by simpa only [Function.comp_def, chainCoordCLM_apply] using
      (chainCoordCLM N (N - 1)).differentiableAt.comp z hy
  have hq : DifferentiableAt ℝ
      (fun w : ℝ × ChainPoint N ↦ q (chainCoord w.2 (N - 1))) z :=
    (differentiable_q _).comp z hcoord
  have hdual : DifferentiableAt ℝ
      (fun w : ℝ × ChainPoint N ↦ dualChain N w.2) z :=
    (hasFDerivAt_dualChain N z.2).differentiableAt.comp z hy
  unfold coupledDual
  exact (ha.mul hq).sub hdual

attribute [fun_prop] differentiable_outerRho differentiable_carmonPsi
  differentiable_carmonPhi differentiable_q differentiable_p

@[fun_prop] theorem differentiableAt_outerRho_direct (s : ℝ) :
    DifferentiableAt ℝ outerRho s := differentiable_outerRho s

@[fun_prop] theorem differentiableAt_carmonPsi_direct (s : ℝ) :
    DifferentiableAt ℝ carmonPsi s := differentiable_carmonPsi s

@[fun_prop] theorem differentiableAt_carmonPhi_direct (s : ℝ) :
    DifferentiableAt ℝ carmonPhi s := differentiable_carmonPhi s

@[fun_prop] theorem differentiableAt_q_direct (s : ℝ) :
    DifferentiableAt ℝ q s := differentiable_q s

@[fun_prop] theorem differentiableAt_p_direct (s : ℝ) :
    DifferentiableAt ℝ p s := differentiable_p s

@[fun_prop] theorem differentiableAt_chainCoord_direct (N j : ℕ)
    (y : ChainPoint N) :
    DifferentiableAt ℝ (fun u : ChainPoint N ↦ chainCoord u j) y := by
  rw [show (fun u : ChainPoint N ↦ chainCoord u j) = chainCoordCLM N j by
    funext u
    exact (chainCoordCLM_apply N j u).symm]
  exact (chainCoordCLM N j).differentiableAt

@[fun_prop] theorem differentiableAt_dualChain_direct (N : ℕ)
    (y : ChainPoint N) :
    DifferentiableAt ℝ (dualChain N) y :=
  (hasFDerivAt_dualChain N y).differentiableAt

@[fun_prop] theorem differentiableAt_carmonLiftedH_joint (z : ℝ × ℝ) :
    DifferentiableAt ℝ (fun w : ℝ × ℝ ↦ carmonLiftedH w.1 w.2) z := by
  unfold carmonLiftedH carmonInteraction
  fun_prop

/-- Away from zero scale the exact cell is an ordinary composition of
differentiable maps. -/
theorem differentiableAt_embeddedCellOnPoint_of_rho_ne {N : ℕ}
    (hN : 0 < N) (z : CellPoint N) (hrho : outerRho z.1 ≠ 0) :
    CellDifferentiableAt N (embeddedCellOnPoint N) z := by
  let active : CellPoint N → ℝ :=
      (fun w : CellPoint N ↦
        -5 * outerRho w.1 ^ 2 + outerRho w.1 ^ 2 *
          coupledDual N
            (carmonLiftedH w.1 w.2.1 / outerRho w.1 ^ 2)
            (perspectiveNormalize N (outerRho w.1) w.2.2))
  have hactive : CellDifferentiableAt N active z := by
    unfold CellDifferentiableAt active perspectiveNormalize coupledDual
    fun_prop (disch := simp [hrho, (weightSqrt_pos hN _).ne'])
  have hevent : Filter.EventuallyEq (nhds z) (embeddedCellOnPoint N)
      active := by
    have hr : ContinuousAt (fun w : CellPoint N ↦ outerRho w.1) z :=
      (differentiable_outerRho z.1).continuousAt.comp
        (cellSCLM N).continuous.continuousAt
    filter_upwards [hr.eventually_ne hrho] with w hw
    simp [embeddedCellOnPoint, embeddedCell, scaledPerspectiveBlock, active, hw]
  unfold CellDifferentiableAt at hactive ⊢
  exact hactive.congr_of_eventuallyEq hevent

/-! ## The zero-scale hyperplane -/

def embeddedCellRemainder (N : ℕ) (z : CellPoint N) : ℝ :=
  embeddedCellOnPoint N z - zeroPerspectiveBlock z.2.2

theorem abs_embeddedCellRemainder_le {N : ℕ} (hN : 2 ≤ N)
    (z : CellPoint N) :
    |embeddedCellRemainder N z| ≤ 18 * outerRho z.1 ^ 2 := by
  exact embeddedCell_remainder_bound hN z.1 z.2.1 z.2.2

theorem embeddedCellRemainder_eq_zero_of_rho_eq_zero {N : ℕ}
    {z : CellPoint N} (hz : outerRho z.1 = 0) :
    embeddedCellRemainder N z = 0 := by
  simp [embeddedCellRemainder, embeddedCellOnPoint, embeddedCell,
    scaledPerspectiveBlock, hz]

/-- The non-penalty part has zero joint derivative at every zero-scale
point, including both splice hyperplanes. -/
theorem hasCellFDerivAt_remainder_zero {N : ℕ} (hN : 2 ≤ N)
    (z : CellPoint N) (hz : outerRho z.1 = 0) :
    @HasFDerivAt ℝ _ (CellPoint N)
      Prod.normedAddCommGroup.toAddCommGroup Prod.normedSpace.toModule
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace ℝ
      Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (embeddedCellRemainder N) (0 : CellPoint N →L[ℝ] ℝ) z := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,
    Asymptotics.isLittleO_iff]
  intro c hc
  have hden : (0 : ℝ) < 73728 := by norm_num
  filter_upwards [eventually_norm_sub_lt (0 : CellPoint N) (div_pos hc hden)]
      with h hh
  have hh' : ‖h‖ < c / 73728 := by simpa using hh
  have hscoord : |h.1| ≤ ‖h‖ := by
    simpa [Real.norm_eq_abs] using norm_fst_le h
  have hrhoDist := outerRho_lipschitz_sixtyFour.dist_le_mul
    (z.1 + h.1) z.1
  have hrhoBound : outerRho (z.1 + h.1) ≤ 64 * |h.1| := by
    rw [Real.dist_eq, hz, sub_zero, abs_of_nonneg (outerRho_nonneg _)] at hrhoDist
    simpa [Real.dist_eq] using hrhoDist
  have hrem := abs_embeddedCellRemainder_le hN (z + h)
  have hzadd : (z + h).1 = z.1 + h.1 := by simp
  rw [hzadd] at hrem
  have hquad :
      |embeddedCellRemainder N (z + h)| ≤ 73728 * ‖h‖ ^ 2 := by
    have hr0 := outerRho_nonneg (z.1 + h.1)
    nlinarith [abs_nonneg h.1, norm_nonneg h]
  have hsmall : 73728 * ‖h‖ ^ 2 ≤ c * ‖h‖ := by
    nlinarith [norm_nonneg h]
  simpa [embeddedCellRemainder_eq_zero_of_rho_eq_zero hz,
    Real.norm_eq_abs] using hquad.trans hsmall

/-- The joint derivative type used below, with all topology instances fixed. -/
def HasCellFDerivAt {N : ℕ} (f : CellPoint N → ℝ)
    (f' : CellPoint N →L[ℝ] ℝ) (z : CellPoint N) : Prop :=
  @HasFDerivAt ℝ _ (CellPoint N)
    Prod.normedAddCommGroup.toAddCommGroup Prod.normedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace ℝ
    Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace f f' z

/-- The norm-topology `fderiv` with the same explicit instances. -/
def cellFDeriv {N : ℕ} (f : CellPoint N → ℝ) (z : CellPoint N) :
    CellPoint N →L[ℝ] ℝ :=
  @fderiv ℝ _ (CellPoint N)
    Prod.normedAddCommGroup.toAddCommGroup Prod.normedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace ℝ
    Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace f z

/-- The explicit derivative on the zero-scale branch. -/
def zeroScaleCellFDeriv (N : ℕ) (y : ChainPoint N) :
    CellPoint N →L[ℝ] ℝ :=
  (finiteDotProductCLM (fun k ↦ negPart (y k))).comp (cellYCLM N)

/-- A total derivative field; on the active region it is the genuine
norm-topology `fderiv`, while its zero-scale formula is fully explicit. -/
def embeddedCellJointFDeriv (N : ℕ) (z : CellPoint N) :
    CellPoint N →L[ℝ] ℝ :=
  if outerRho z.1 = 0 then zeroScaleCellFDeriv N z.2.2
  else cellFDeriv (embeddedCellOnPoint N) z

theorem hasCellFDerivAt_zeroPerspective_comp {N : ℕ} (hN : 2 ≤ N)
    (z : CellPoint N) :
    HasCellFDerivAt (fun w : CellPoint N ↦ zeroPerspectiveBlock w.2.2)
      (zeroScaleCellFDeriv N z.2.2) z := by
  have hy := hasFDerivAt_scaledPerspectiveBlock hN 0 0 z.2.2
  have hfun : scaledPerspectiveBlock N 0 0 = zeroPerspectiveBlock := by
    funext y
    simp [scaledPerspectiveBlock]
  rw [hfun] at hy
  have hy' : HasFDerivAt zeroPerspectiveBlock
      (finiteDotProductCLM (fun k ↦ negPart (z.2.2 k))) z.2.2 := by
    simpa [scaledPerspectiveGradient] using hy
  have hproj : HasFDerivAt (cellYCLM N) (cellYCLM N) z :=
    (cellYCLM N).hasFDerivAt
  unfold HasCellFDerivAt zeroScaleCellFDeriv
  simpa only [Function.comp_def, cellYCLM_apply] using hy'.comp z hproj

/-- The exact embedded cell has the displayed full joint Fréchet derivative
at every point, including `rho=0`. -/
theorem hasCellFDerivAt_embeddedCell {N : ℕ} (hN : 2 ≤ N)
    (z : CellPoint N) :
    HasCellFDerivAt (embeddedCellOnPoint N)
      (embeddedCellJointFDeriv N z) z := by
  by_cases hz : outerRho z.1 = 0
  · have hrem := hasCellFDerivAt_remainder_zero hN z hz
    have hpen := hasCellFDerivAt_zeroPerspective_comp hN z
    unfold HasCellFDerivAt at hpen ⊢
    have hadd := hrem.add hpen
    have hfun : embeddedCellRemainder N +
        (fun w : CellPoint N ↦ zeroPerspectiveBlock w.2.2) =
        embeddedCellOnPoint N := by
      funext w
      simp [embeddedCellRemainder]
    rw [hfun] at hadd
    simpa [embeddedCellJointFDeriv, hz] using hadd
  · have hdiff := differentiableAt_embeddedCellOnPoint_of_rho_ne
      (by omega : 0 < N) z hz
    unfold CellDifferentiableAt at hdiff
    unfold HasCellFDerivAt embeddedCellJointFDeriv cellFDeriv
    rw [if_neg hz]
    exact hdiff.hasFDerivAt

/-! ## Coordinate representation of the joint derivative -/

def cellSInCLM (N : ℕ) : ℝ →L[ℝ] CellPoint N :=
  ContinuousLinearMap.inl ℝ ℝ (ℝ × ChainPoint N)

def cellTInCLM (N : ℕ) : ℝ →L[ℝ] CellPoint N :=
  (ContinuousLinearMap.inr ℝ ℝ (ℝ × ChainPoint N)).comp
    (ContinuousLinearMap.inl ℝ ℝ (ChainPoint N))

def cellYInCLM (N : ℕ) : ChainPoint N →L[ℝ] CellPoint N :=
  (ContinuousLinearMap.inr ℝ ℝ (ℝ × ChainPoint N)).comp
    (ContinuousLinearMap.inr ℝ ℝ (ChainPoint N))

@[simp] theorem cellSInCLM_apply {N : ℕ} (a : ℝ) :
    cellSInCLM N a = (a, (0, 0)) := rfl

@[simp] theorem cellTInCLM_apply {N : ℕ} (a : ℝ) :
    cellTInCLM N a = (0, (a, 0)) := rfl

@[simp] theorem cellYInCLM_apply {N : ℕ} (v : ChainPoint N) :
    cellYInCLM N v = (0, (0, v)) := rfl

/-- Fréchet differentiability on the dual space with its norm-induced
instances fixed explicitly. -/
def HasChainFDerivAt (N : ℕ) (f : ChainPoint N → ℝ)
    (f' : ChainPoint N →L[ℝ] ℝ) (y : ChainPoint N) : Prop :=
  @HasFDerivAt ℝ _ (ChainPoint N)
    Pi.normedAddCommGroup.toAddCommGroup Pi.normedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace ℝ
    Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace f f' y

theorem hasFDerivAt_embeddedCell_dual_jointModule {N : ℕ} (hN : 2 ≤ N)
    (s t : ℝ) (y : ChainPoint N) :
    HasChainFDerivAt N (embeddedCell N s t)
      (finiteDotProductCLM
        (scaledPerspectiveGradient N (outerRho s) (carmonLiftedH s t) y)) y := by
  have h := hasFDerivAt_scaledPerspectiveBlock hN
    (outerRho s) (carmonLiftedH s t) y
  unfold HasChainFDerivAt
  have hfun : embeddedCell N s t =
      fun x ↦ -5 * outerRho s ^ 2 +
        scaledPerspectiveBlock N (outerRho s) (carmonLiftedH s t) x := rfl
  rw [hfun]
  exact h.const_add (-5 * outerRho s ^ 2)

theorem embeddedCellJointFDeriv_t_apply {N : ℕ} (hN : 2 ≤ N)
    (z : CellPoint N) :
    embeddedCellJointFDeriv N z (0, (1, 0)) =
      embeddedSuccessorGradient N z.1 z.2.1 z.2.2 := by
  have hjoint := hasCellFDerivAt_embeddedCell hN z
  unfold HasCellFDerivAt at hjoint
  have hline : HasDerivAt
      (fun u : ℝ ↦ ((z.1, (u, z.2.2)) : CellPoint N))
      (0, (1, 0)) z.2.1 := by
    have hs : HasDerivAt (fun _ : ℝ ↦ z.1) 0 z.2.1 :=
      hasDerivAt_const (x := z.2.1) (c := z.1)
    have ht : HasDerivAt (fun u : ℝ ↦ u) 1 z.2.1 := hasDerivAt_id z.2.1
    have hy : HasDerivAt (fun _ : ℝ ↦ z.2.2) 0 z.2.1 :=
      hasDerivAt_const (x := z.2.1) (c := z.2.2)
    exact hs.prodMk (ht.prodMk hy)
  have hcomp := hjoint.comp_hasDerivAt z.2.1 hline
  have hactual := hasDerivAt_embeddedCell_successor
    (by omega : 0 < N) z.1 z.2.1 z.2.2
  have hcomp' : HasDerivAt
      (fun u : ℝ ↦ embeddedCell N z.1 u z.2.2)
      (embeddedCellJointFDeriv N z (0, (1, 0))) z.2.1 := by
    simpa [embeddedCellOnPoint, Function.comp_def] using hcomp
  exact hcomp'.unique hactual

/-- The predecessor component of `embeddedCellGradient` is the actual scalar
derivative along the `s` line. -/
theorem hasDerivAt_embeddedCell_predecessor_joint {N : ℕ} (hN : 2 ≤ N)
    (s t : ℝ) (y : ChainPoint N) :
    HasDerivAt (fun u : ℝ ↦ embeddedCell N u t y)
      (embeddedCellJointFDeriv N (s, (t, y)) (1, (0, 0))) s := by
  have hjoint := hasCellFDerivAt_embeddedCell hN (s, (t, y))
  unfold HasCellFDerivAt at hjoint
  let base : CellPoint N := (0, (t, y))
  have hline0 : HasFDerivAt
      (fun u : ℝ ↦ base + cellSInCLM N u)
      (cellSInCLM N) s :=
    (cellSInCLM N).hasFDerivAt.const_add base
  have heq : base + cellSInCLM N s = ((s, (t, y)) : CellPoint N) := by
    ext <;> simp [base]
  rw [← heq] at hjoint
  have hcomp := hjoint.comp s hline0
  simpa [embeddedCellOnPoint, Function.comp_def, base] using hcomp.hasDerivAt

theorem embeddedCellJointFDeriv_y_comp {N : ℕ} (hN : 2 ≤ N)
    (z : CellPoint N) :
    (embeddedCellJointFDeriv N z).comp (cellYInCLM N) =
      finiteDotProductCLM
        (scaledPerspectiveGradient N (outerRho z.1)
          (carmonLiftedH z.1 z.2.1) z.2.2) := by
  have hjoint := hasCellFDerivAt_embeddedCell hN z
  unfold HasCellFDerivAt at hjoint
  let base : CellPoint N := (z.1, (z.2.1, 0))
  have hinc0 : HasFDerivAt
      (fun y : ChainPoint N ↦ base + cellYInCLM N y)
      (cellYInCLM N) z.2.2 :=
    (cellYInCLM N).hasFDerivAt.const_add base
  have hinc : HasFDerivAt
      (fun y : ChainPoint N ↦ ((z.1, (z.2.1, y)) : CellPoint N))
      (cellYInCLM N) z.2.2 := by
    convert hinc0 using 1
    funext y
    simp [base]
  have hcomp := hjoint.comp z.2.2 hinc
  have hactual := hasFDerivAt_embeddedCell_dual_jointModule hN
    z.1 z.2.1 z.2.2
  have hcomp' : HasChainFDerivAt N (embeddedCell N z.1 z.2.1)
      ((embeddedCellJointFDeriv N z).comp (cellYInCLM N)) z.2.2 := by
    unfold HasChainFDerivAt
    simpa [embeddedCellOnPoint, Function.comp_def] using hcomp
  exact hcomp'.unique hactual

/-- Coordinate vector representing the genuine full joint derivative.  The
predecessor coordinate is extracted from the certified derivative; the
successor and dual coordinates are the closed formulas used in the paper. -/
def embeddedCellGradient (N : ℕ) (z : CellPoint N) : CellPoint N :=
  (embeddedCellJointFDeriv N z (1, (0, 0)),
    (embeddedSuccessorGradient N z.1 z.2.1 z.2.2,
      scaledPerspectiveGradient N (outerRho z.1)
        (carmonLiftedH z.1 z.2.1) z.2.2))

/-- The predecessor component of the displayed gradient is the actual scalar
derivative along the predecessor line. -/
theorem hasDerivAt_embeddedCell_predecessor {N : ℕ} (hN : 2 ≤ N)
    (s t : ℝ) (y : ChainPoint N) :
    HasDerivAt (fun u : ℝ ↦ embeddedCell N u t y)
      (embeddedCellGradient N (s, (t, y))).1 s := by
  simpa [embeddedCellGradient] using
    hasDerivAt_embeddedCell_predecessor_joint hN s t y

def cellGradientCLM {N : ℕ} (g : CellPoint N) : CellPoint N →L[ℝ] ℝ :=
  g.1 • cellSCLM N + g.2.1 • cellTCLM N +
    (finiteDotProductCLM g.2.2).comp (cellYCLM N)

@[simp] theorem cellGradientCLM_apply {N : ℕ} (g h : CellPoint N) :
    cellGradientCLM g h =
      g.1 * h.1 + g.2.1 * h.2.1 +
        ∑ k : Fin N, g.2.2 k * h.2.2 k := by
  simp [cellGradientCLM, finiteDotProductCLM_apply]

theorem embeddedCellJointFDeriv_eq_gradientCLM {N : ℕ} (hN : 2 ≤ N)
    (z : CellPoint N) :
    embeddedCellJointFDeriv N z = cellGradientCLM (embeddedCellGradient N z) := by
  apply ContinuousLinearMap.ext
  intro h
  have hy := congrArg (fun L : ChainPoint N →L[ℝ] ℝ ↦ L h.2.2)
    (embeddedCellJointFDeriv_y_comp hN z)
  simp only [ContinuousLinearMap.comp_apply, cellYInCLM_apply,
    finiteDotProductCLM_apply] at hy
  have ht := embeddedCellJointFDeriv_t_apply hN z
  have hdecomp : h =
      h.1 • (1, (0, 0)) + h.2.1 • (0, (1, 0)) + (0, (0, h.2.2)) := by
    ext <;> simp
  rw [hdecomp, map_add, map_add, map_smul, map_smul, ht, hy]
  simp [embeddedCellGradient, cellGradientCLM_apply]
  ring

/-- Lemma 5.1's first requirement: the displayed coordinate field is the
actual full joint Fréchet gradient, including both splice interfaces. -/
theorem hasCellFDerivAt_embeddedCell_gradient {N : ℕ} (hN : 2 ≤ N)
    (z : CellPoint N) :
    HasCellFDerivAt (embeddedCellOnPoint N)
      (cellGradientCLM (embeddedCellGradient N z)) z := by
  rw [← embeddedCellJointFDeriv_eq_gradientCLM hN z]
  exact hasCellFDerivAt_embeddedCell hN z

end

end NCPLRevised
