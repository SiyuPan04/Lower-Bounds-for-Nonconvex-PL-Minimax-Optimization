/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.RotationInvarianceCore

/-!
# Function-level scaling calculus for Lemma 5.2

This module records the calculus facts behind the manuscript's rescaling

`f(x,y) = a * barf(x / lambda, y / lambda)`.

Unlike the arithmetic-only certificate in `CertificateScaling`, the results
below act on the actual objective and its actual Frechet gradient.
-/

namespace NCPLRevised

noncomputable section

/-- Coordinatewise division by the positive spatial scale. -/
def scaleEVec {d : ℕ} (lambda : ℝ) (x : EVec d) : EVec d :=
  fun i ↦ x i / lambda

/-- Coordinatewise division as a continuous linear map. -/
def scaleEVecCLM (d : ℕ) (lambda : ℝ) : EVec d →L[ℝ] EVec d :=
  (lambda⁻¹) • ContinuousLinearMap.id ℝ (EVec d)

@[simp] theorem scaleEVecCLM_apply (d : ℕ) (lambda : ℝ) (x : EVec d) :
    scaleEVecCLM d lambda x = scaleEVec lambda x := by
  funext i
  simp [scaleEVecCLM, scaleEVec, div_eq_mul_inv, mul_comm]

@[simp] theorem scaleEVec_zero (d : ℕ) (lambda : ℝ) :
    scaleEVec lambda (0 : EVec d) = 0 := by
  funext i
  simp [scaleEVec]

theorem scaleEVec_sub {d : ℕ} (lambda : ℝ) (x x' : EVec d) :
    scaleEVec lambda x - scaleEVec lambda x' = scaleEVec lambda (x - x') := by
  funext i
  simp only [scaleEVec, Pi.sub_apply]
  ring

/-- Simultaneous scaling of the primal and dual coordinates. -/
def productScaleCLM (dx dy : ℕ) (lambda : ℝ) :
    (EVec dx × EVec dy) →L[ℝ] (EVec dx × EVec dy) :=
  ((scaleEVecCLM dx lambda).comp
      (ContinuousLinearMap.fst ℝ (EVec dx) (EVec dy))).prod
    ((scaleEVecCLM dy lambda).comp
      (ContinuousLinearMap.snd ℝ (EVec dx) (EVec dy)))

@[simp] theorem productScaleCLM_apply (dx dy : ℕ) (lambda : ℝ)
    (p : EVec dx × EVec dy) :
    productScaleCLM dx dy lambda p =
      (scaleEVec lambda p.1, scaleEVec lambda p.2) := by
  simp [productScaleCLM]

def scaledObjectiveGeneral {dx dy : ℕ} (a lambda : ℝ)
    (F : EVec dx → EVec dy → ℝ) (x : EVec dx) (y : EVec dy) : ℝ :=
  a * F (scaleEVec lambda x) (scaleEVec lambda y)

def scaledGradientXGeneral {dx dy : ℕ} (a lambda : ℝ)
    (gradX : EVec dx → EVec dy → EVec dx)
    (x : EVec dx) (y : EVec dy) : EVec dx :=
  fun i ↦ a / lambda * gradX (scaleEVec lambda x) (scaleEVec lambda y) i

def scaledGradientYGeneral {dx dy : ℕ} (a lambda : ℝ)
    (gradY : EVec dx → EVec dy → EVec dy)
    (x : EVec dx) (y : EVec dy) : EVec dy :=
  fun i ↦ a / lambda * gradY (scaleEVec lambda x) (scaleEVec lambda y) i

/-- The actual joint Frechet gradient obeys the scaling formula from Lemma 5.2. -/
theorem scaledObjectiveGeneral_representsGradient
    {dx dy : ℕ} {F : EVec dx → EVec dy → ℝ}
    {gradX : EVec dx → EVec dy → EVec dx}
    {gradY : EVec dx → EVec dy → EVec dy}
    (hrep : RepresentsRotatableGradient F gradX gradY)
    (a lambda : ℝ) (hlambda : lambda ≠ 0) :
    RepresentsRotatableGradient (scaledObjectiveGeneral a lambda F)
      (scaledGradientXGeneral a lambda gradX)
      (scaledGradientYGeneral a lambda gradY) := by
  constructor
  · intro p
    let P := productScaleCLM dx dy lambda
    have hP : HasFDerivAt
        (fun q : EVec dx × EVec dy ↦
          (scaleEVec lambda q.1, scaleEVec lambda q.2)) P p := by
      refine P.hasFDerivAt.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun q ↦ ?_)
      exact (productScaleCLM_apply dx dy lambda q).symm
    have hbase := (hrep.1.differentiableAt).hasFDerivAt.comp p hP
    have hscaled := hbase.const_mul a
    change DifferentiableAt ℝ
      (fun q : EVec dx × EVec dy ↦
        a * F (scaleEVec lambda q.1) (scaleEVec lambda q.2)) p
    exact hscaled.differentiableAt
  · intro x y hx hy
    let P := productScaleCLM dx dy lambda
    have hP : HasFDerivAt
        (fun q : EVec dx × EVec dy ↦
          (scaleEVec lambda q.1, scaleEVec lambda q.2)) P (x, y) := by
      refine P.hasFDerivAt.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun q ↦ ?_)
      exact (productScaleCLM_apply dx dy lambda q).symm
    have hbase : HasFDerivAt (Function.uncurry F)
        (fderiv ℝ (Function.uncurry F)
          (scaleEVec lambda x, scaleEVec lambda y))
        (scaleEVec lambda x, scaleEVec lambda y) :=
      (hrep.1 (scaleEVec lambda x, scaleEVec lambda y)).hasFDerivAt
    have hcomp := hbase.comp (x, y) hP
    have hscaled := hcomp.const_mul a
    have hfun : Function.uncurry (scaledObjectiveGeneral a lambda F) =
        fun q : EVec dx × EVec dy ↦
          a * Function.uncurry F
            (scaleEVec lambda q.1, scaleEVec lambda q.2) := by rfl
    have hscaled' : HasFDerivAt
        (Function.uncurry (scaledObjectiveGeneral a lambda F))
        (a • (fderiv ℝ (Function.uncurry F)
          (scaleEVec lambda x, scaleEVec lambda y)).comp P) (x, y) := by
      rw [hfun]
      exact hscaled
    rw [hscaled'.fderiv]
    simp only [smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul]
    rw [productScaleCLM_apply]
    rw [hrep.2 (scaleEVec lambda x) (scaleEVec lambda y)
      (scaleEVec lambda hx) (scaleEVec lambda hy)]
    unfold scaledGradientXGeneral scaledGradientYGeneral euclideanDot scaleEVec
    rw [mul_add]
    apply congrArg₂ (· + ·)
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [hlambda]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [hlambda]

/-- Scaling by a nonzero scalar preserves the coordinate support exactly. -/
theorem scaleEVec_apply_eq_zero_iff {d : ℕ} {lambda : ℝ} (hlambda : lambda ≠ 0)
    (x : EVec d) (i : Fin d) :
    scaleEVec lambda x i = 0 ↔ x i = 0 := by
  simp [scaleEVec, hlambda]

/-- Euclidean squared norm under coordinatewise division. -/
theorem euclideanSq_scaleEVec {d : ℕ} {lambda : ℝ} (hlambda : lambda ≠ 0)
    (x : EVec d) :
    euclideanSq (scaleEVec lambda x) = lambda⁻¹ ^ 2 * euclideanSq x := by
  unfold euclideanSq scaleEVec
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [hlambda]

/-- Euclidean squared norm under pointwise scalar multiplication. -/
theorem euclideanSq_const_mul {d : ℕ} (c : ℝ) (x : EVec d) :
    euclideanSq (fun i ↦ c * x i) = c ^ 2 * euclideanSq x := by
  unfold euclideanSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem jointEuclideanSq_scaleEVec {dx dy : ℕ} {lambda : ℝ}
    (hlambda : lambda ≠ 0) (x : EVec dx) (y : EVec dy) :
    jointEuclideanSq (scaleEVec lambda x) (scaleEVec lambda y) =
      lambda⁻¹ ^ 2 * jointEuclideanSq x y := by
  unfold jointEuclideanSq
  rw [euclideanSq_scaleEVec hlambda, euclideanSq_scaleEVec hlambda]
  ring

/-- Joint Euclidean smoothness rescales by `a / lambda^2`. -/
theorem scaledGradientGeneral_isJointlySmooth
    {dx dy : ℕ} {L : ℝ}
    {gradX : EVec dx → EVec dy → EVec dx}
    {gradY : EVec dx → EVec dy → EVec dy}
    (hsmooth : IsEuclideanJointlySmooth L gradX gradY)
    (a lambda : ℝ) (hlambda : lambda ≠ 0) :
    IsEuclideanJointlySmooth (a / lambda ^ 2 * L)
      (scaledGradientXGeneral a lambda gradX)
      (scaledGradientYGeneral a lambda gradY) := by
  intro x y x' y'
  let bx := scaleEVec lambda x
  let bY := scaleEVec lambda y
  let bx' := scaleEVec lambda x'
  let bY' := scaleEVec lambda y'
  let c := a / lambda
  have hbase := hsmooth bx bY bx' bY'
  have hdx :
      scaledGradientXGeneral a lambda gradX x y -
          scaledGradientXGeneral a lambda gradX x' y' =
        fun i ↦ c * (gradX bx bY i - gradX bx' bY' i) := by
    funext i
    simp only [scaledGradientXGeneral, Pi.sub_apply]
    dsimp [c, bx, bY, bx', bY']
    ring
  have hdy :
      scaledGradientYGeneral a lambda gradY x y -
          scaledGradientYGeneral a lambda gradY x' y' =
        fun i ↦ c * (gradY bx bY i - gradY bx' bY' i) := by
    funext i
    simp only [scaledGradientYGeneral, Pi.sub_apply]
    dsimp [c, bx, bY, bx', bY']
    ring
  have hinput :
      jointEuclideanSq (bx - bx') (bY - bY') =
        lambda⁻¹ ^ 2 * jointEuclideanSq (x - x') (y - y') := by
    rw [scaleEVec_sub lambda x x', scaleEVec_sub lambda y y']
    exact jointEuclideanSq_scaleEVec hlambda (x - x') (y - y')
  rw [hdx, hdy]
  unfold jointEuclideanSq
  rw [euclideanSq_const_mul, euclideanSq_const_mul]
  rw [← mul_add]
  have hmul := mul_le_mul_of_nonneg_left hbase (sq_nonneg c)
  rw [hinput] at hmul
  calc
    c ^ 2 *
        (euclideanSq (gradX bx bY - gradX bx' bY') +
          euclideanSq (gradY bx bY - gradY bx' bY'))
        ≤ c ^ 2 *
          (L ^ 2 * (lambda⁻¹ ^ 2 *
            (euclideanSq (x - x') + euclideanSq (y - y')))) := hmul
    _ = (a / lambda ^ 2 * L) ^ 2 *
          (euclideanSq (x - x') + euclideanSq (y - y')) := by
      dsimp [c]
      field_simp [hlambda]

/-- The dual PL inequality scales exactly as in Lemma 5.2. -/
theorem scaledGradientYGeneral_PL
    {dx dy : ℕ} {F : EVec dx → EVec dy → ℝ}
    {gradY : EVec dx → EVec dy → EVec dy}
    {value : EVec dx → ℝ} {mu : ℝ}
    (hPL : ∀ x y,
      (1 / 2 : ℝ) * euclideanSq (gradY x y) ≥
        mu * (value x - F x y))
    {a lambda : ℝ} (hlambda : lambda ≠ 0)
    (x : EVec dx) (y : EVec dy) :
    (1 / 2 : ℝ) *
        euclideanSq (scaledGradientYGeneral a lambda gradY x y) ≥
      (a * mu / lambda ^ 2) *
        (a * value (scaleEVec lambda x) -
          scaledObjectiveGeneral a lambda F x y) := by
  have hbase := hPL (scaleEVec lambda x) (scaleEVec lambda y)
  have hnorm :
      euclideanSq (scaledGradientYGeneral a lambda gradY x y) =
        (a / lambda) ^ 2 *
          euclideanSq (gradY (scaleEVec lambda x) (scaleEVec lambda y)) := by
    unfold scaledGradientYGeneral
    exact euclideanSq_const_mul _ _
  rw [hnorm]
  unfold scaledObjectiveGeneral
  have hmul := mul_le_mul_of_nonneg_left hbase (sq_nonneg (a / lambda))
  calc
    (a * mu / lambda ^ 2) *
        (a * value (scaleEVec lambda x) -
          a * F (scaleEVec lambda x) (scaleEVec lambda y))
        = (a / lambda) ^ 2 *
          (mu * (value (scaleEVec lambda x) -
            F (scaleEVec lambda x) (scaleEVec lambda y))) := by
          field_simp [hlambda]
    _ ≤ (a / lambda) ^ 2 *
          ((1 / 2 : ℝ) *
            euclideanSq (gradY (scaleEVec lambda x) (scaleEVec lambda y))) := hmul
    _ = (1 / 2 : ℝ) * ((a / lambda) ^ 2 *
          euclideanSq (gradY (scaleEVec lambda x) (scaleEVec lambda y))) := by ring

/-- Inverse coordinate scaling, used to transport maximizers. -/
def unscaleEVec {d : ℕ} (lambda : ℝ) (x : EVec d) : EVec d :=
  fun i ↦ lambda * x i

theorem scaleEVec_unscaleEVec {d : ℕ} {lambda : ℝ} (hlambda : lambda ≠ 0)
    (x : EVec d) : scaleEVec lambda (unscaleEVec lambda x) = x := by
  funext i
  simp [scaleEVec, unscaleEVec, hlambda]

/-- A pointwise maximum and an explicit maximizer survive positive scaling. -/
theorem scaledObjectiveGeneral_max
    {dx dy : ℕ} {F : EVec dx → EVec dy → ℝ}
    {value : EVec dx → ℝ}
    (hupper : ∀ x y, F x y ≤ value x)
    (hwitness : ∀ x, ∃ y, F x y = value x)
    {a lambda : ℝ} (ha : 0 ≤ a) (hlambda : lambda ≠ 0)
    (x : EVec dx) :
    (∀ y, scaledObjectiveGeneral a lambda F x y ≤
      a * value (scaleEVec lambda x)) ∧
    ∃ y, scaledObjectiveGeneral a lambda F x y =
      a * value (scaleEVec lambda x) := by
  constructor
  · intro y
    unfold scaledObjectiveGeneral
    exact mul_le_mul_of_nonneg_left
      (hupper (scaleEVec lambda x) (scaleEVec lambda y)) ha
  · obtain ⟨ystar, hystar⟩ := hwitness (scaleEVec lambda x)
    refine ⟨unscaleEVec lambda ystar, ?_⟩
    unfold scaledObjectiveGeneral
    rw [scaleEVec_unscaleEVec hlambda, hystar]

/-- General spatially scaled value-gradient formula. -/
theorem scaledValue_comp_hasFDerivAt
    {d : ℕ} {value : EVec d → ℝ} {g : EVec d}
    {x : EVec d} {a lambda : ℝ} (hlambda : lambda ≠ 0)
    (hvalue : HasFDerivAt value (finiteDotProductCLM g)
      (scaleEVec lambda x)) :
    HasFDerivAt (fun z : EVec d ↦ a * value (scaleEVec lambda z))
      (finiteDotProductCLM (fun i ↦ a / lambda * g i)) x := by
  have hscale : HasFDerivAt (scaleEVec lambda)
      (scaleEVecCLM d lambda) x := by
    refine (scaleEVecCLM d lambda).hasFDerivAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z ↦ ?_)
    exact (scaleEVecCLM_apply d lambda z).symm
  have hcomp := hvalue.comp x hscale
  have hmul := hcomp.const_mul a
  have hmap : a • (finiteDotProductCLM g).comp (scaleEVecCLM d lambda) =
      finiteDotProductCLM (fun i ↦ a / lambda * g i) := by
    ext h
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      finiteDotProductCLM_apply, scaleEVecCLM_apply]
    change a * (∑ i : Fin d, g i * (h i / lambda)) =
      ∑ i : Fin d, (a / lambda * g i) * h i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hlambda]
  rw [hmap] at hmul
  exact hmul

end

end NCPLRevised
