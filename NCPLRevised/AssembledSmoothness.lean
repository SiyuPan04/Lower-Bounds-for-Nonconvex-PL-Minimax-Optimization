/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.ConcreteHardInstance
import NCPLRevised.ConcreteSaddleZeroChain
import NCPLRevised.EmbeddedCellJointDerivative
import NCPLRevised.EmbeddedCellLipschitz
import NCPLRevised.RevisedConstants
import NCPLRevised.RotationInvarianceCore
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Smooth assembly of the embedded cells

This file contains the dimension-free assembly argument in Proposition 5.1.
The local cell on link `i` uses `(x_{i-1},x_i,y^(i))`, with the manuscript's
convention `x₀ = 1`.  Consequently the incidence graph of the local cells is
a path and has two colours.  The proof below exposes the corresponding two
orthogonal layers: every primal coordinate receives one ``right'' derivative
and at most one ``left'' derivative, while every dual block occurs once.  The
elementary inequality `(a+b)^2 <= 2a^2+2b^2`, followed by the two exact
reindexing identities, gives the constant `2 L` and introduces no factor
depending on either `M` or `N`.
-/

namespace NCPLRevised

noncomputable section

/-! ## Generic path assembly -/

/-- Local gradient data evaluated on the `i`-th link. -/
def assembledLocalGradient {M N : ℕ}
    (cellGradient : ℝ → ℝ → ChainPoint N → LocalGradientData N)
    (x : EVec M) (y : EVec (M * N)) (i : Fin M) : LocalGradientData N :=
  cellGradient (primalPrev x i) (x i) (dualBlock y i)

/-- The primal gradient obtained by scattering the two scalar derivatives of
each cell onto the two endpoints of its link. -/
def assembledPrimalGradientFrom {M N : ℕ}
    (cellGradient : ℝ → ℝ → ChainPoint N → LocalGradientData N)
    (x : EVec M) (y : EVec (M * N)) : EVec M := fun j ↦
  (assembledLocalGradient cellGradient x y j).2.1 +
    if hj : j.1 + 1 < M then
      (assembledLocalGradient cellGradient x y ⟨j.1 + 1, hj⟩).1
    else 0

/-- The dual gradient obtained by flattening the mutually orthogonal local
dual blocks. -/
def assembledDualGradientFrom {M N : ℕ}
    (cellGradient : ℝ → ℝ → ChainPoint N → LocalGradientData N)
    (x : EVec M) (y : EVec (M * N)) : EVec (M * N) :=
  flattenDualBlocks fun i ↦ (assembledLocalGradient cellGradient x y i).2.2

/-- Squared Euclidean size of a local input increment. -/
def localInputSq {N : ℕ}
    (s t : ℝ) (y : ChainPoint N) : ℝ :=
  s ^ 2 + t ^ 2 + euclideanSq y

/-- Squared Euclidean size of a local gradient increment. -/
def localGradientSq {N : ℕ} (g : LocalGradientData N) : ℝ :=
  g.1 ^ 2 + g.2.1 ^ 2 + euclideanSq g.2.2

theorem localInputSq_nonneg {N : ℕ} (s t : ℝ) (y : ChainPoint N) :
    0 ≤ localInputSq s t y := by
  unfold localInputSq euclideanSq
  positivity

theorem localGradientSq_nonneg {N : ℕ} (g : LocalGradientData N) :
    0 ≤ localGradientSq g := by
  unfold localGradientSq euclideanSq
  positivity

/-- Exact reindexing of the predecessor contribution.  This is one of the
two colour classes of the path-incidence matrix. -/
theorem sum_successor_sq_le_sum {M : ℕ} (a : EVec M) :
    (∑ j : Fin M, if hj : j.1 + 1 < M then a ⟨j.1 + 1, hj⟩ ^ 2 else 0) ≤
      ∑ i : Fin M, a i ^ 2 := by
  have hreindex := sum_predecessor_eq_sum_successor
    (fun i : Fin M ↦ a i ^ 2) (fun _ : Fin M ↦ (1 : ℝ))
  have hle :
      (∑ i : Fin M,
        if hi : i.1 = 0 then 0 else a i ^ 2 * (1 : ℝ)) ≤
        ∑ i : Fin M, a i ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · positivity
    · simp
  calc
    (∑ j : Fin M,
        if hj : j.1 + 1 < M then a ⟨j.1 + 1, hj⟩ ^ 2 else 0) =
        ∑ i : Fin M,
          if hi : i.1 = 0 then 0 else a i ^ 2 * (1 : ℝ) := by
            simpa using hreindex.symm
    _ ≤ ∑ i : Fin M, a i ^ 2 := hle

/-- Splitting a coordinate between the two incident path colours costs
exactly the factor `2` used in the final `2 L` bound. -/
theorem sq_add_le_two_sq_add_two_sq (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Output-energy bound for a path assembly.  The right-end and left-end
pieces are the two orthogonal colour layers; dual blocks are already
orthogonal under `flattenDualBlocks`. -/
theorem assembledGradient_output_le_two_sum_local {M N : ℕ}
    (cellGradient : ℝ → ℝ → ChainPoint N → LocalGradientData N)
    (x : EVec M) (y : EVec (M * N))
    (x' : EVec M) (y' : EVec (M * N)) :
    jointEuclideanSq
        (assembledPrimalGradientFrom cellGradient x y -
          assembledPrimalGradientFrom cellGradient x' y')
        (assembledDualGradientFrom cellGradient x y -
          assembledDualGradientFrom cellGradient x' y') ≤
      2 * ∑ i : Fin M,
        localGradientSq
          (assembledLocalGradient cellGradient x y i -
            assembledLocalGradient cellGradient x' y' i) := by
  let own : EVec M := fun i ↦
    (assembledLocalGradient cellGradient x y i).2.1 -
      (assembledLocalGradient cellGradient x' y' i).2.1
  let incoming : EVec M := fun i ↦
    (assembledLocalGradient cellGradient x y i).1 -
      (assembledLocalGradient cellGradient x' y' i).1
  let next : EVec M := fun j ↦
    if hj : j.1 + 1 < M then incoming ⟨j.1 + 1, hj⟩ else 0
  have hprimal :
      euclideanSq
          (assembledPrimalGradientFrom cellGradient x y -
            assembledPrimalGradientFrom cellGradient x' y') ≤
        2 * (∑ i : Fin M, own i ^ 2) +
          2 * (∑ i : Fin M, incoming i ^ 2) := by
    have hfield :
        assembledPrimalGradientFrom cellGradient x y -
            assembledPrimalGradientFrom cellGradient x' y' =
          own + next := by
      funext j
      unfold assembledPrimalGradientFrom
      simp only [Pi.sub_apply, Pi.add_apply]
      dsimp [own, next, incoming]
      split_ifs <;> ring
    rw [hfield]
    unfold euclideanSq
    simp only [Pi.add_apply]
    have hpoint :
        (∑ j : Fin M, (own j + next j) ^ 2) ≤
          ∑ j : Fin M, (2 * own j ^ 2 + 2 * next j ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      exact sq_add_le_two_sq_add_two_sq _ _
    have hnext :
        (∑ j : Fin M, next j ^ 2) ≤ ∑ i : Fin M, incoming i ^ 2 := by
      have heq :
          (∑ j : Fin M, next j ^ 2) =
            ∑ j : Fin M,
              if hj : j.1 + 1 < M then
                incoming ⟨j.1 + 1, hj⟩ ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp [next]
        split_ifs <;> simp
      rw [heq]
      exact sum_successor_sq_le_sum incoming
    calc
      (∑ j : Fin M, (own j + next j) ^ 2) ≤
          ∑ j : Fin M, (2 * own j ^ 2 + 2 * next j ^ 2) := hpoint
      _ = 2 * (∑ i : Fin M, own i ^ 2) +
            2 * (∑ j : Fin M, next j ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * (∑ i : Fin M, own i ^ 2) +
            2 * (∑ i : Fin M, incoming i ^ 2) := by
          simpa [add_comm] using add_le_add_left
            (mul_le_mul_of_nonneg_left hnext (show (0 : ℝ) ≤ 2 by norm_num))
            (2 * ∑ i : Fin M, own i ^ 2)
  have hdual :
      euclideanSq
          (assembledDualGradientFrom cellGradient x y -
            assembledDualGradientFrom cellGradient x' y') =
        ∑ i : Fin M,
          euclideanSq
            ((assembledLocalGradient cellGradient x y i).2.2 -
              (assembledLocalGradient cellGradient x' y' i).2.2) := by
    have hflat :
        assembledDualGradientFrom cellGradient x y -
            assembledDualGradientFrom cellGradient x' y' =
          flattenDualBlocks (fun i ↦
            (assembledLocalGradient cellGradient x y i).2.2 -
              (assembledLocalGradient cellGradient x' y' i).2.2) := by
      funext k
      simp [assembledDualGradientFrom, flattenDualBlocks]
    rw [hflat]
    exact euclideanNormSq_flattenDualBlocks _
  unfold jointEuclideanSq
  rw [hdual]
  have hdual_nonneg : 0 ≤ ∑ i : Fin M,
      euclideanSq
        ((assembledLocalGradient cellGradient x y i).2.2 -
          (assembledLocalGradient cellGradient x' y' i).2.2) := by
    apply Finset.sum_nonneg
    intro i _
    unfold euclideanSq
    positivity
  calc
    euclideanSq
          (assembledPrimalGradientFrom cellGradient x y -
            assembledPrimalGradientFrom cellGradient x' y') +
        ∑ i : Fin M,
          euclideanSq
            ((assembledLocalGradient cellGradient x y i).2.2 -
              (assembledLocalGradient cellGradient x' y' i).2.2) ≤
      (2 * ∑ i : Fin M, own i ^ 2 +
          2 * ∑ i : Fin M, incoming i ^ 2) +
        ∑ i : Fin M,
          euclideanSq
            ((assembledLocalGradient cellGradient x y i).2.2 -
              (assembledLocalGradient cellGradient x' y' i).2.2) :=
        by nlinarith [hprimal]
    _ ≤ 2 * ∑ i : Fin M,
        localGradientSq
          (assembledLocalGradient cellGradient x y i -
            assembledLocalGradient cellGradient x' y' i) := by
      unfold localGradientSq
      simp only [Prod.fst_sub, Prod.snd_sub]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      dsimp [own, incoming]
      linarith

/-- The total squared input energy seen by all local cells is at most twice
the global squared input energy.  This is the input-side form of the same
two-colour path decomposition. -/
theorem sum_localInputSq_le_two_joint {M N : ℕ}
    (x x' : EVec M) (y y' : EVec (M * N)) :
    (∑ i : Fin M,
      localInputSq
        (primalPrev x i - primalPrev x' i)
        (x i - x' i)
        (dualBlock y i - dualBlock y' i)) ≤
      2 * jointEuclideanSq (x - x') (y - y') := by
  have hprev :
      (∑ i : Fin M, (primalPrev x i - primalPrev x' i) ^ 2) ≤
        euclideanSq (x - x') := by
    have hreindex := sum_predecessor_eq_sum_successor
      (fun _ : Fin M ↦ (1 : ℝ)) (fun i : Fin M ↦ (x i - x' i) ^ 2)
    have heq :
        (∑ i : Fin M, (primalPrev x i - primalPrev x' i) ^ 2) =
          ∑ j : Fin M,
            if hj : j.1 + 1 < M then (x j - x' j) ^ 2 else 0 := by
      calc
        (∑ i : Fin M, (primalPrev x i - primalPrev x' i) ^ 2) =
            ∑ i : Fin M,
              if hi : i.1 = 0 then 0
              else (1 : ℝ) * (x ⟨i.1 - 1, by omega⟩ -
                x' ⟨i.1 - 1, by omega⟩) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i.1 = 0
          · simp [primalPrev, hi]
          · simp [primalPrev, hi]
        _ = ∑ j : Fin M,
              if hj : j.1 + 1 < M then
                (1 : ℝ) * (x j - x' j) ^ 2 else 0 := hreindex
        _ = ∑ j : Fin M,
              if hj : j.1 + 1 < M then (x j - x' j) ^ 2 else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> simp
    rw [heq]
    unfold euclideanSq
    simp only [Pi.sub_apply]
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · rfl
    · positivity
  have hdual :
      (∑ i : Fin M, euclideanSq (dualBlock y i - dualBlock y' i)) =
        euclideanSq (y - y') := by
    have hflat :
        flattenDualBlocks (fun i ↦ dualBlock y i - dualBlock y' i) =
          y - y' := by
      funext k
      change
        y (finProdFinEquiv (finProdFinEquiv.symm k)) -
            y' (finProdFinEquiv (finProdFinEquiv.symm k)) =
          y k - y' k
      rw [finProdFinEquiv.apply_symm_apply]
    have hnorm := euclideanNormSq_flattenDualBlocks
      (fun i ↦ dualBlock y i - dualBlock y' i)
    rw [hflat] at hnorm
    simpa [euclideanSq, euclideanNormSq] using hnorm.symm
  unfold localInputSq jointEuclideanSq
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hdual]
  have hcurr :
      (∑ i : Fin M, (x i - x' i) ^ 2) = euclideanSq (x - x') := by
    unfold euclideanSq
    simp
  rw [hcurr]
  have hy_nonneg : 0 ≤ euclideanSq (y - y') := by
    unfold euclideanSq
    positivity
  linarith

/-- Dimension-free smoothness of the path assembly. -/
theorem assembledGradient_isJointlySmooth {M N : ℕ} {L : ℝ}
    (cellGradient : ℝ → ℝ → ChainPoint N → LocalGradientData N)
    (hlocal : ∀ s t y s' t' y',
      localGradientSq (cellGradient s t y - cellGradient s' t' y') ≤
        L ^ 2 * localInputSq (s - s') (t - t') (y - y')) :
    IsEuclideanJointlySmooth (2 * L)
      (assembledPrimalGradientFrom (M := M) cellGradient)
      (assembledDualGradientFrom (M := M) cellGradient) := by
  intro x y x' y'
  have hout := assembledGradient_output_le_two_sum_local
    cellGradient x y x' y'
  have hsum :
      (∑ i : Fin M,
        localGradientSq
          (assembledLocalGradient cellGradient x y i -
            assembledLocalGradient cellGradient x' y' i)) ≤
        L ^ 2 * ∑ i : Fin M,
          localInputSq
            (primalPrev x i - primalPrev x' i)
            (x i - x' i)
            (dualBlock y i - dualBlock y' i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact hlocal _ _ _ _ _ _
  have hin := sum_localInputSq_le_two_joint x x' y y'
  have hL : 0 ≤ L ^ 2 := sq_nonneg L
  calc
    jointEuclideanSq
        (assembledPrimalGradientFrom cellGradient x y -
          assembledPrimalGradientFrom cellGradient x' y')
        (assembledDualGradientFrom cellGradient x y -
          assembledDualGradientFrom cellGradient x' y') ≤
      2 * ∑ i : Fin M,
        localGradientSq
          (assembledLocalGradient cellGradient x y i -
            assembledLocalGradient cellGradient x' y' i) := hout
    _ ≤ 2 * (L ^ 2 * ∑ i : Fin M,
          localInputSq
            (primalPrev x i - primalPrev x' i)
            (x i - x' i)
            (dualBlock y i - dualBlock y' i)) := by gcongr
    _ ≤ 2 * (L ^ 2 * (2 * jointEuclideanSq (x - x') (y - y'))) := by
      gcongr
    _ = (2 * L) ^ 2 * jointEuclideanSq (x - x') (y - y') := by ring

/-! ## Actual Frechet derivative of the assembly -/

/-- The continuous linear functional represented by a three-part local
gradient. -/
def localGradientDotCLM {N : ℕ} (g : LocalGradientData N) :
    LocalGradientData N →L[ℝ] ℝ := by
  exact LinearMap.toContinuousLinearMap
    ({ toFun := fun h ↦
          g.1 * h.1 + g.2.1 * h.2.1 + euclideanDot g.2.2 h.2.2
       map_add' := by
         intro h k
         unfold euclideanDot
         simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
         simp_rw [mul_add]
         rw [Finset.sum_add_distrib]
         ring
       map_smul' := by
         intro c h
         unfold euclideanDot
         simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
           smul_eq_mul, RingHom.id_apply]
         have hsum :
             (∑ i : Fin N, g.2.2 i * (c * h.2.2 i)) =
               c * ∑ i : Fin N, g.2.2 i * h.2.2 i := by
           rw [Finset.mul_sum]
           apply Finset.sum_congr rfl
           intro i _
           ring
         rw [hsum]
         ring } : LocalGradientData N →ₗ[ℝ] ℝ)

@[simp] theorem localGradientDotCLM_apply {N : ℕ}
    (g h : LocalGradientData N) :
    localGradientDotCLM g h =
      g.1 * h.1 + g.2.1 * h.2.1 + euclideanDot g.2.2 h.2.2 := by
  rfl

/-- Block extraction as a continuous linear map. -/
def assembledDualBlockCLM {M N : ℕ} (i : Fin M) :
    EVec (M * N) →L[ℝ] ChainPoint N :=
  ContinuousLinearMap.pi fun j ↦ evecProj (finProdFinEquiv (i, j))

@[simp] theorem assembledDualBlockCLM_apply {M N : ℕ}
    (i : Fin M) (y : EVec (M * N)) :
    assembledDualBlockCLM i y = dualBlock y i := by
  rfl

/-- Linear part of the predecessor convention.  The first cell has constant
predecessor `1`, so its derivative is zero. -/
def primalPrevDirectionCLM {M : ℕ} (i : Fin M) : EVec M →L[ℝ] ℝ :=
  if hi : i.1 = 0 then 0 else evecProj ⟨i.1 - 1, by omega⟩

@[simp] theorem primalPrevDirectionCLM_apply {M : ℕ}
    (i : Fin M) (h : EVec M) :
    primalPrevDirectionCLM i h =
      if hi : i.1 = 0 then 0 else h ⟨i.1 - 1, by omega⟩ := by
  by_cases hi : i.1 = 0 <;> simp [primalPrevDirectionCLM, hi]

/-- The affine local-coordinate projection from global primal/dual space. -/
def assembledCellPoint {M N : ℕ}
    (p : EVec M × EVec (M * N)) (i : Fin M) : LocalGradientData N :=
  (primalPrev p.1 i, (p.1 i, dualBlock p.2 i))

/-- Derivative of `assembledCellPoint`. -/
def assembledCellPointFDeriv {M N : ℕ} (i : Fin M) :
    (EVec M × EVec (M * N)) →L[ℝ] LocalGradientData N :=
  ((primalPrevDirectionCLM i).comp
      (ContinuousLinearMap.fst ℝ (EVec M) (EVec (M * N)))).prod
    (((evecProj i).comp
        (ContinuousLinearMap.fst ℝ (EVec M) (EVec (M * N)))).prod
      ((assembledDualBlockCLM i).comp
        (ContinuousLinearMap.snd ℝ (EVec M) (EVec (M * N)))))

@[simp] theorem assembledCellPointFDeriv_apply {M N : ℕ}
    (i : Fin M) (p : EVec M × EVec (M * N)) :
    assembledCellPointFDeriv i p =
      (primalPrevDirectionCLM i p.1, (p.1 i, dualBlock p.2 i)) := by
  simp [assembledCellPointFDeriv]

/-- Global-to-local derivative predicate with the norm-induced instances
fixed explicitly. -/
def HasAssembledToCellFDerivAt {M N : ℕ}
    (f : (EVec M × EVec (M * N)) → CellPoint N)
    (f' : (EVec M × EVec (M * N)) →L[ℝ] CellPoint N)
    (p : EVec M × EVec (M * N)) : Prop :=
  @HasFDerivAt ℝ _ (EVec M × EVec (M * N))
    Prod.normedAddCommGroup.toAddCommGroup Prod.normedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (CellPoint N) Prod.normedAddCommGroup.toAddCommGroup
    Prod.normedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace f f' p

/-- Joint derivative predicate for the assembled objective, again with the
norm-induced instances fixed explicitly. -/
def HasAssembledFDerivAt {M N : ℕ}
    (f : (EVec M × EVec (M * N)) → ℝ)
    (f' : (EVec M × EVec (M * N)) →L[ℝ] ℝ)
    (p : EVec M × EVec (M * N)) : Prop :=
  @HasFDerivAt ℝ _ (EVec M × EVec (M * N))
    Prod.normedAddCommGroup.toAddCommGroup Prod.normedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    ℝ Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace f f' p

theorem hasFDerivAt_assembledCellPoint {M N : ℕ}
    (p : EVec M × EVec (M * N)) (i : Fin M) :
    HasAssembledToCellFDerivAt (fun q ↦ assembledCellPoint q i)
      (assembledCellPointFDeriv i) p := by
  have hlin : HasAssembledToCellFDerivAt
      (fun q ↦ assembledCellPointFDeriv i q)
      (assembledCellPointFDeriv i) p := by
    unfold HasAssembledToCellFDerivAt
    exact (assembledCellPointFDeriv i).hasFDerivAt
  unfold HasAssembledToCellFDerivAt at hlin ⊢
  by_cases hi : i.1 = 0
  · have h := hlin.const_add
        ((1 : ℝ), ((0 : ℝ), (0 : ChainPoint N)))
    refine h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun q ↦ ?_)
    apply Prod.ext
    · simp [assembledCellPoint, assembledCellPointFDeriv,
        primalPrevDirectionCLM, primalPrev, hi]
    · apply Prod.ext
      · simp [assembledCellPoint, assembledCellPointFDeriv,
          primalPrevDirectionCLM, primalPrev, hi]
      · funext j
        simp [assembledCellPoint, assembledCellPointFDeriv,
          primalPrevDirectionCLM, primalPrev, hi, dualBlock]
  · refine hlin.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun q ↦ ?_)
    apply Prod.ext
    · simp [assembledCellPoint, assembledCellPointFDeriv,
        primalPrevDirectionCLM, primalPrev, hi]
    · apply Prod.ext
      · simp [assembledCellPoint, assembledCellPointFDeriv,
          primalPrevDirectionCLM, primalPrev, hi]
      · funext j
        simp [assembledCellPoint, assembledCellPointFDeriv,
          primalPrevDirectionCLM, primalPrev, hi, dualBlock]

/-- The continuous linear derivative obtained by summing the composed local
derivatives. -/
def assembledGradientFDerivFrom {M N : ℕ}
    (cellGradient : ℝ → ℝ → ChainPoint N → LocalGradientData N)
    (x : EVec M) (y : EVec (M * N)) :
    (EVec M × EVec (M * N)) →L[ℝ] ℝ :=
  ∑ i : Fin M,
    (localGradientDotCLM (assembledLocalGradient cellGradient x y i)).comp
      (assembledCellPointFDeriv i)

/-- Generic chain rule for the finite path assembly. -/
theorem hasFDerivAt_assembledCells
    {M N : ℕ} {cell : ℝ → ℝ → ChainPoint N → ℝ}
    {cellGradient : ℝ → ℝ → ChainPoint N → LocalGradientData N}
    (hcell : ∀ s t y,
      HasCellFDerivAt
        (fun z : CellPoint N ↦ cell z.1 z.2.1 z.2.2)
        (localGradientDotCLM (cellGradient s t y)) (s, (t, y)))
    (x : EVec M) (y : EVec (M * N)) :
    HasAssembledFDerivAt (Function.uncurry (assembledCells cell))
      (assembledGradientFDerivFrom cellGradient x y) (x, y) := by
  have hsum : HasAssembledFDerivAt
      (fun p : EVec M × EVec (M * N) ↦
        ∑ i : Fin M, cell
          (primalPrev p.1 i) (p.1 i) (dualBlock p.2 i))
      (∑ i : Fin M,
        (localGradientDotCLM
          (assembledLocalGradient cellGradient x y i)).comp
            (assembledCellPointFDeriv i)) (x, y) := by
    unfold HasAssembledFDerivAt
    apply HasFDerivAt.fun_sum
    intro i _
    have hlocal := hcell (primalPrev x i) (x i) (dualBlock y i)
    have hproj := hasFDerivAt_assembledCellPoint (x, y) i
    unfold HasCellFDerivAt at hlocal
    unfold HasAssembledToCellFDerivAt at hproj
    exact hlocal.comp (x, y) hproj
  unfold HasAssembledFDerivAt at hsum ⊢
  change HasFDerivAt
    (fun p : EVec M × EVec (M * N) ↦ assembledCells cell p.1 p.2)
    (assembledGradientFDerivFrom cellGradient x y) (x, y)
  simpa only [assembledCells, assembledGradientFDerivFrom,
    assembledLocalGradient] using hsum

/-- The summed continuous linear map is represented by the scattered primal
gradient and the flattened dual gradient. -/
theorem assembledGradientFDerivFrom_apply {M N : ℕ}
    (cellGradient : ℝ → ℝ → ChainPoint N → LocalGradientData N)
    (x : EVec M) (y : EVec (M * N))
    (hx : EVec M) (hy : EVec (M * N)) :
    assembledGradientFDerivFrom cellGradient x y (hx, hy) =
      euclideanDot (assembledPrimalGradientFrom cellGradient x y) hx +
        euclideanDot (assembledDualGradientFrom cellGradient x y) hy := by
  let gs : EVec M := fun i ↦
    (assembledLocalGradient cellGradient x y i).1
  let gt : EVec M := fun i ↦
    (assembledLocalGradient cellGradient x y i).2.1
  let gy : Fin M → ChainPoint N := fun i ↦
    (assembledLocalGradient cellGradient x y i).2.2
  have hprev := sum_predecessor_eq_sum_successor gs hx
  have hdual :
      (∑ i : Fin M, euclideanDot (gy i) (dualBlock hy i)) =
        euclideanDot (flattenDualBlocks gy) hy := by
    unfold euclideanDot
    calc
      (∑ i : Fin M, ∑ j : Fin N, gy i j * dualBlock hy i j) =
          ∑ ij : Fin M × Fin N,
            gy ij.1 ij.2 * dualBlock hy ij.1 ij.2 :=
        (Fintype.sum_prod_type
          (fun ij : Fin M × Fin N ↦
            gy ij.1 ij.2 * dualBlock hy ij.1 ij.2)).symm
      _ = ∑ ij : Fin M × Fin N,
          flattenDualBlocks gy (finProdFinEquiv ij) *
            hy (finProdFinEquiv ij) := by
        apply Finset.sum_congr rfl
        intro ij _
        simp [flattenDualBlocks, dualBlock]
      _ = ∑ k : Fin (M * N), flattenDualBlocks gy k * hy k :=
        Equiv.sum_comp finProdFinEquiv
          (fun k : Fin (M * N) ↦ flattenDualBlocks gy k * hy k)
  unfold assembledGradientFDerivFrom
  rw [continuousLinearMap_sum_apply]
  simp only [ContinuousLinearMap.comp_apply, assembledCellPointFDeriv_apply,
    localGradientDotCLM_apply]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [primalPrevDirectionCLM_apply]
  have hprimal :
      euclideanDot (assembledPrimalGradientFrom cellGradient x y) hx =
        (∑ j : Fin M, gt j * hx j) +
          ∑ j : Fin M,
            (if hj : j.1 + 1 < M then gs ⟨j.1 + 1, hj⟩ else 0) * hx j := by
    unfold euclideanDot assembledPrimalGradientFrom
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
  change
    (∑ i : Fin M,
        gs i * (if hi : i.1 = 0 then 0 else hx ⟨i.1 - 1, by omega⟩)) +
      (∑ i : Fin M, gt i * hx i) +
      ∑ i : Fin M, euclideanDot (gy i) (dualBlock hy i) = _
  rw [hdual, hprimal]
  change
    (∑ i : Fin M,
        gs i * (if hi : i.1 = 0 then 0 else hx ⟨i.1 - 1, by omega⟩)) +
      (∑ i : Fin M, gt i * hx i) +
      euclideanDot (flattenDualBlocks gy) hy =
    ((∑ j : Fin M, gt j * hx j) +
      ∑ j : Fin M,
        (if hj : j.1 + 1 < M then gs ⟨j.1 + 1, hj⟩ else 0) * hx j) +
      euclideanDot (flattenDualBlocks gy) hy
  have hleft :
      (∑ i : Fin M,
        gs i * (if hi : i.1 = 0 then 0 else hx ⟨i.1 - 1, by omega⟩)) =
        ∑ i : Fin M,
          if hi : i.1 = 0 then 0 else gs i * hx ⟨i.1 - 1, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  have hright :
      (∑ j : Fin M,
        (if hj : j.1 + 1 < M then gs ⟨j.1 + 1, hj⟩ else 0) * hx j) =
        ∑ j : Fin M,
          if hj : j.1 + 1 < M then gs ⟨j.1 + 1, hj⟩ * hx j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [hleft, hright]
  rw [hprev]
  ring

/-- A local actual-gradient certificate assembles to an actual global
primal/dual gradient certificate. -/
theorem assembledCells_representsGradient
    {M N : ℕ} {cell : ℝ → ℝ → ChainPoint N → ℝ}
    {cellGradient : ℝ → ℝ → ChainPoint N → LocalGradientData N}
    (hcell : ∀ s t y,
      HasCellFDerivAt
        (fun z : CellPoint N ↦ cell z.1 z.2.1 z.2.2)
        (localGradientDotCLM (cellGradient s t y)) (s, (t, y))) :
    RepresentsRotatableGradient (assembledCells cell)
      (assembledPrimalGradientFrom (M := M) cellGradient)
      (assembledDualGradientFrom (M := M) cellGradient) := by
  constructor
  · intro p
    have hglobal := hasFDerivAt_assembledCells hcell p.1 p.2
    unfold HasAssembledFDerivAt at hglobal
    exact hglobal.differentiableAt
  · intro x y hx hy
    have hglobal := hasFDerivAt_assembledCells hcell x y
    unfold HasAssembledFDerivAt at hglobal
    rw [hglobal.fderiv]
    exact assembledGradientFDerivFrom_apply cellGradient x y hx hy

/-! ## Concrete gradient and its relation to Proposition 5.2 -/

theorem localGradientDotCLM_eq_cellGradientCLM {N : ℕ}
    (g : CellPoint N) :
    localGradientDotCLM g = cellGradientCLM g := by
  apply ContinuousLinearMap.ext
  intro h
  simp [localGradientDotCLM_apply, cellGradientCLM_apply, euclideanDot]

/-- The derivative-extracted local gradient agrees with the coordinate field
used in the zero-chain proof. -/
theorem embeddedCellGradient_eq_concreteCellGradient {N : ℕ}
    (hN : 2 ≤ N) (s t : ℝ) (y : ChainPoint N) :
    embeddedCellGradient N (s, (t, y)) = concreteCellGradient N s t y := by
  apply Prod.ext
  · exact (hasDerivAt_embeddedCell_predecessor hN s t y).deriv.symm
  · apply Prod.ext <;> rfl

/-- The full explicit primal gradient of the manuscript's `barF`. -/
def barPrimalGradient (M N : ℕ)
    (x : EVec M) (y : EVec (M * N)) : EVec M :=
  assembledPrimalGradientFrom (concreteCellGradient N) x y

/-- The full joint derivative as a continuous linear functional. -/
def barJointFDeriv (M N : ℕ)
    (x : EVec M) (y : EVec (M * N)) :
    (EVec M × EVec (M * N)) →L[ℝ] ℝ :=
  assembledGradientFDerivFrom (concreteCellGradient N) x y

theorem assembledDualGradientFrom_concrete_eq_barDualGradient
    (M N : ℕ) (x : EVec M) (y : EVec (M * N)) :
    assembledDualGradientFrom (concreteCellGradient N) x y =
      barDualGradient M N x y := by
  rfl

/-- Each concrete local coordinate field represents the genuine joint cell
derivative. -/
theorem hasCellFDerivAt_embeddedCell_concreteGradient {N : ℕ}
    (hN : 2 ≤ N) (s t : ℝ) (y : ChainPoint N) :
    HasCellFDerivAt
      (fun z : CellPoint N ↦ embeddedCell N z.1 z.2.1 z.2.2)
      (localGradientDotCLM (concreteCellGradient N s t y)) (s, (t, y)) := by
  rw [← embeddedCellGradient_eq_concreteCellGradient hN s t y,
    localGradientDotCLM_eq_cellGradientCLM]
  exact hasCellFDerivAt_embeddedCell_gradient hN (s, (t, y))

/-- Strong pointwise version of the actual joint derivative statement. -/
theorem hasFDerivAt_barF {M N : ℕ} (hN : 2 ≤ N)
    (x : EVec M) (y : EVec (M * N)) :
    HasAssembledFDerivAt (Function.uncurry (barF M N))
      (barJointFDeriv M N x y) (x, y) := by
  unfold barF barJointFDeriv
  exact hasFDerivAt_assembledCells
    (M := M) (cell := embeddedCell N)
    (cellGradient := concreteCellGradient N)
    (hasCellFDerivAt_embeddedCell_concreteGradient hN) x y

/-- Proposition 5.1's gradient field is the actual Fréchet gradient of the
concrete assembled objective. -/
theorem barF_representsGradient {M N : ℕ} (hN : 2 ≤ N) :
    RepresentsRotatableGradient (barF M N)
      (barPrimalGradient M N) (barDualGradient M N) := by
  have h := assembledCells_representsGradient
    (M := M) (cell := embeddedCell N)
    (cellGradient := concreteCellGradient N)
    (hasCellFDerivAt_embeddedCell_concreteGradient hN)
  unfold barF barPrimalGradient
  have hdual :
      (assembledDualGradientFrom (M := M) (concreteCellGradient N)) =
        barDualGradient M N := by
    funext x y
    exact assembledDualGradientFrom_concrete_eq_barDualGradient M N x y
  rw [← hdual]
  exact h

/-- In interleaved coordinates, the actual gradient just proved is exactly
the zero-chain field from Proposition 5.2. -/
theorem assembleOrdered_barGradient_eq_concreteOrderedSaddleGradient
    (M N : ℕ) (x : EVec M) (y : EVec (M * N)) :
    assembleOrdered (barPrimalGradient M N x y) (barDualGradient M N x y) =
      concreteOrderedSaddleGradient M N (assembleOrdered x y) := by
  funext r
  generalize hij : finProdFinEquiv.symm r = ij
  rcases ij with ⟨i, j⟩
  simp only [assembleOrdered, hij, concreteOrderedSaddleGradient,
    assembledOrderedGradientFrom, orderedPrimal_assembleOrdered,
    orderedDual_assembleOrdered]
  by_cases hj : j.1 < N
  · rw [dif_pos hj, dif_pos hj]
    change
      barDualGradient M N x y
          (finProdFinEquiv (i, ⟨j.1, hj⟩)) =
        (concreteCellGradient N (primalPrev x i) (x i)
          (dualBlock y i)).2.2 ⟨j.1, hj⟩
    change dualBlock (barDualGradient M N x y) i ⟨j.1, hj⟩ = _
    rw [dualBlock_barDualGradient M N x y i]
    rfl
  · rw [dif_neg hj, dif_neg hj]
    rfl

/-! ## Concrete dimension-free smoothness constant -/

/-- The explicit local constant used for the normalized hard instance.
The maximum records the manuscript's convention `L_C \ge 1`. -/
def concreteLC : ℝ := max 1 embeddedCellSmoothnessConstant

theorem one_le_concreteLC : 1 ≤ concreteLC := by
  exact le_max_left 1 embeddedCellSmoothnessConstant

theorem concreteLC_pos : 0 < concreteLC :=
  lt_of_lt_of_le zero_lt_one one_le_concreteLC

theorem concreteLC_eq_embeddedCellSmoothnessConstant :
    concreteLC = embeddedCellSmoothnessConstant := by
  exact max_eq_right embeddedCellSmoothnessConstant_ge_one

/-- The smoothness constant of the complete path assembly. -/
def concreteEll0 : ℝ := revisedEll0 concreteLC

theorem concreteEll0_pos : 0 < concreteEll0 :=
  revisedEll0_pos concreteLC_pos

/-- The nonsingular local field agrees with the concrete actual gradient
used by the assembled objective. -/
theorem embeddedStableCellGradient_eq_concreteCellGradient {N : ℕ}
    (hN : 2 ≤ N) (s t : ℝ) (y : ChainPoint N) :
    embeddedStableCellGradient N s t y = concreteCellGradient N s t y := by
  exact (embeddedStableCellGradient_eq_actual hN s t y).trans
    (embeddedCellGradient_eq_concreteCellGradient hN s t y)

/-- The actual concrete cell gradient has a dimension-independent Euclidean
Lipschitz constant. -/
theorem concreteCellGradient_lipschitz_sq {N : ℕ}
    (hN : 2 ≤ N) (s t : ℝ) (y : ChainPoint N)
    (s' t' : ℝ) (y' : ChainPoint N) :
    localGradientSq
        (concreteCellGradient N s t y - concreteCellGradient N s' t' y') ≤
      concreteLC ^ 2 * localInputSq (s - s') (t - t') (y - y') := by
  have h := embeddedStableCellGradient_lipschitz_sq hN s t y s' t' y'
  rw [embeddedStableCellGradient_eq_concreteCellGradient hN s t y,
    embeddedStableCellGradient_eq_concreteCellGradient hN s' t' y'] at h
  rw [concreteLC_eq_embeddedCellSmoothnessConstant]
  simpa only [cellGradientSq, localGradientSq, cellInputSq, localInputSq,
    euclideanNormSq, euclideanSq] using h

/-- Proposition 5.1's full assembled gradient is jointly smooth with the
explicit normalized constant.  The constant is independent of both chain
dimensions. -/
theorem barF_isJointlySmooth {M N : ℕ} (hN : 2 ≤ N) :
    IsEuclideanJointlySmooth concreteEll0
      (barPrimalGradient M N) (barDualGradient M N) := by
  have hassembled := assembledGradient_isJointlySmooth
    (M := M) (L := concreteLC) (concreteCellGradient N)
      (concreteCellGradient_lipschitz_sq hN)
  unfold concreteEll0 revisedEll0 barPrimalGradient
  have hdual :
      (assembledDualGradientFrom (M := M) (concreteCellGradient N)) =
        barDualGradient M N := by
    funext x y
    exact assembledDualGradientFrom_concrete_eq_barDualGradient M N x y
  rw [← hdual]
  exact hassembled

/-- Complete concrete form of Proposition 5.1.  For every admissible pair,
the displayed primal/dual fields are the genuine gradient, the objective is
jointly smooth with a numerical dimension-free constant, every inner maximum
is finite and attained with value `barPhi`, and the claimed dual PL inequality
holds with `mu0 / N`. -/
theorem proposition5_1_concrete (M N : ℕ) (_hM : 0 < M) (hN : 2 ≤ N) :
    0 < concreteEll0 ∧
    0 < revisedMu0 ∧
    RepresentsRotatableGradient (barF M N)
      (barPrimalGradient M N) (barDualGradient M N) ∧
    IsEuclideanJointlySmooth concreteEll0
      (barPrimalGradient M N) (barDualGradient M N) ∧
    (∀ x : EVec M, IsGreatest (Set.range (barF M N x)) (barPhi M x)) ∧
    ∀ (x : EVec M) (y : EVec (M * N)),
      (1 / 2 : ℝ) * barDualGradientSq M N x y ≥
        revisedMu0 / (N : ℝ) * (barPhi M x - barF M N x y) := by
  refine ⟨concreteEll0_pos, revisedMu0_pos, barF_representsGradient hN,
    barF_isJointlySmooth hN, barF_isGreatest hN, ?_⟩
  intro x y
  have h := barF_dual_PL hN x y
  have hcoef : (1 / (640 * (N : ℝ)) : ℝ) = revisedMu0 / (N : ℝ) := by
    unfold revisedMu0
    rw [div_div]
  rw [← hcoef]
  exact h

end

end NCPLRevised
