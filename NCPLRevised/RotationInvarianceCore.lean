/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.DualChainDerivative
import NCPLRevised.ZeroChain
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Rotation-invariance core for Lemma 2.1

This file formalizes the finite-dimensional linear-algebra and calculus core
of the manuscript's rotation-invariance lemma.  Since Lean's default norm on
finite function spaces is the sup norm, all metric statements below use the
explicit squared Euclidean norm `euclideanSq`.

An orthonormal family defines an isometric embedding and a contractive
transpose projection.  We then prove that objective gradients, smoothness,
the inner PL inequality, the value-function range and the initial gap are all
preserved by the two-frame lifting.  The final results identify the actual
Frechet derivative of a lifted value function and prove exact preservation of
its gradient norm.  These are the mathematical facts required to instantiate
the abstract `RotationPreservesProblem` premise in the resisting-oracle layer;
the separate packaging into that deliberately abstract model is left to the
chosen concrete notion of an algorithmic instance.
-/

namespace NCPLRevised

noncomputable section

/-- Finite Euclidean dot product, independent of the ambient function norm. -/
def euclideanDot {d : Nat} (x y : EVec d) : ℝ :=
  ∑ i : Fin d, x i * y i

/-- Explicit squared Euclidean norm. -/
def euclideanSq {d : Nat} (x : EVec d) : ℝ :=
  ∑ i : Fin d, x i ^ 2

def jointEuclideanSq {dx dy : Nat} (x : EVec dx) (y : EVec dy) : ℝ :=
  euclideanSq x + euclideanSq y

@[simp] theorem euclideanDot_self {d : Nat} (x : EVec d) :
    euclideanDot x x = euclideanSq x := by
  unfold euclideanDot euclideanSq
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem euclideanDot_comm {d : Nat} (x y : EVec d) :
    euclideanDot x y = euclideanDot y x := by
  unfold euclideanDot
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Columns of `U` form an orthonormal frame. -/
def IsEuclideanOrthonormalFrame {m D : Nat} (U : Fin m → EVec D) : Prop :=
  ∀ i j, euclideanDot (U i) (U j) = if i = j then 1 else 0

/-- Multiplication by the frame matrix. -/
def orthogonalEmbed {m D : Nat} (U : Fin m → EVec D)
    (x : EVec m) : EVec D :=
  fun k ↦ ∑ i : Fin m, x i * U i k

/-- Multiplication by the transpose of the frame matrix. -/
def orthogonalProject {m D : Nat} (U : Fin m → EVec D)
    (X : EVec D) : EVec m :=
  fun i ↦ euclideanDot (U i) X

@[simp] theorem orthogonalProject_zero {m D : Nat} (U : Fin m → EVec D) :
    orthogonalProject U (0 : EVec D) = 0 := by
  funext i
  simp [orthogonalProject, euclideanDot]

@[simp] theorem orthogonalEmbed_zero {m D : Nat} (U : Fin m → EVec D) :
    orthogonalEmbed U (0 : EVec m) = 0 := by
  funext k
  simp [orthogonalEmbed]

theorem euclideanDot_embed_left {m D : Nat}
    (U : Fin m → EVec D) (x : EVec m) (X : EVec D) :
    euclideanDot (orthogonalEmbed U x) X =
      ∑ i : Fin m, x i * euclideanDot (U i) X := by
  unfold euclideanDot orthogonalEmbed
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The transpose is a left inverse of an orthonormal embedding. -/
theorem orthogonalProject_embed {m D : Nat}
    {U : Fin m → EVec D} (hU : IsEuclideanOrthonormalFrame U)
    (x : EVec m) :
    orthogonalProject U (orthogonalEmbed U x) = x := by
  funext i
  change euclideanDot (U i) (orthogonalEmbed U x) = x i
  rw [euclideanDot_comm, euclideanDot_embed_left]
  calc
    (∑ j : Fin m, x j * euclideanDot (U j) (U i)) =
        ∑ j : Fin m, if j = i then x j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hU]
      by_cases hji : j = i <;> simp [hji]
    _ = x i := by simp

/-- An orthonormal frame is an exact Euclidean isometry. -/
theorem euclideanSq_orthogonalEmbed {m D : Nat}
    {U : Fin m → EVec D} (hU : IsEuclideanOrthonormalFrame U)
    (x : EVec m) :
    euclideanSq (orthogonalEmbed U x) = euclideanSq x := by
  rw [← euclideanDot_self, euclideanDot_embed_left]
  change (∑ i : Fin m,
    x i * orthogonalProject U (orthogonalEmbed U x) i) = euclideanSq x
  rw [orthogonalProject_embed hU]
  unfold euclideanSq
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem euclideanDot_embed_project {m D : Nat}
    {U : Fin m → EVec D} (X : EVec D) :
    euclideanDot (orthogonalEmbed U (orthogonalProject U X)) X =
      euclideanSq (orthogonalProject U X) := by
  rw [euclideanDot_embed_left]
  unfold orthogonalProject euclideanSq
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem euclideanSq_sub_expand {d : Nat} (x y : EVec d) :
    euclideanSq (x - y) =
      euclideanSq x - 2 * euclideanDot x y + euclideanSq y := by
  unfold euclideanSq euclideanDot
  simp only [Pi.sub_apply]
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [mul_assoc]

/-- The transpose of an orthonormal embedding is a Euclidean contraction. -/
theorem euclideanSq_orthogonalProject_le {m D : Nat}
    {U : Fin m → EVec D} (hU : IsEuclideanOrthonormalFrame U)
    (X : EVec D) :
    euclideanSq (orthogonalProject U X) ≤ euclideanSq X := by
  have hres : 0 ≤
      euclideanSq (X - orthogonalEmbed U (orthogonalProject U X)) := by
    unfold euclideanSq
    positivity
  rw [euclideanSq_sub_expand, euclideanDot_comm,
    euclideanDot_embed_project,
    euclideanSq_orthogonalEmbed hU] at hres
  linarith

theorem orthogonalProject_sub {m D : Nat} (U : Fin m → EVec D)
    (X X' : EVec D) :
    orthogonalProject U X - orthogonalProject U X' =
      orthogonalProject U (X - X') := by
  funext i
  unfold orthogonalProject euclideanDot
  simp only [Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem orthogonalEmbed_sub {m D : Nat} (U : Fin m → EVec D)
    (x x' : EVec m) :
    orthogonalEmbed U x - orthogonalEmbed U x' =
      orthogonalEmbed U (x - x') := by
  funext k
  unfold orthogonalEmbed
  simp only [Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The transpose projection as a continuous linear map. -/
def orthogonalProjectCLM {m D : Nat} (U : Fin m → EVec D) :
    EVec D →L[ℝ] EVec m :=
  ContinuousLinearMap.pi (fun i ↦ finiteDotProductCLM (U i))

@[simp] theorem orthogonalProjectCLM_apply {m D : Nat}
    (U : Fin m → EVec D) (X : EVec D) :
    orthogonalProjectCLM U X = orthogonalProject U X := by
  funext i
  simp [orthogonalProjectCLM, orthogonalProject, euclideanDot]

def orthogonalEmbedLM {m D : Nat} (U : Fin m → EVec D) :
    EVec m →ₗ[ℝ] EVec D where
  toFun := orthogonalEmbed U
  map_add' := by
    intro x y
    funext k
    unfold orthogonalEmbed
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  map_smul' := by
    intro c x
    funext k
    unfold orthogonalEmbed
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

def orthogonalEmbedCLM {m D : Nat} (U : Fin m → EVec D) :
    EVec m →L[ℝ] EVec D :=
  LinearMap.toContinuousLinearMap (orthogonalEmbedLM U)

@[simp] theorem orthogonalEmbedCLM_apply {m D : Nat}
    (U : Fin m → EVec D) (x : EVec m) :
    orthogonalEmbedCLM U x = orthogonalEmbed U x := rfl

/-- Orthogonal lift `f_{U,V}(X,Y)=f(UᵀX,VᵀY)`. -/
def rotatedObjective {dx dy DX DY : Nat}
    (U : Fin dx → EVec DX) (V : Fin dy → EVec DY)
    (F : EVec dx → EVec dy → ℝ) (X : EVec DX) (Y : EVec DY) : ℝ :=
  F (orthogonalProject U X) (orthogonalProject V Y)

def rotatedGradientX {dx dy DX DY : Nat}
    (U : Fin dx → EVec DX) (V : Fin dy → EVec DY)
    (gradX : EVec dx → EVec dy → EVec dx)
    (X : EVec DX) (Y : EVec DY) : EVec DX :=
  orthogonalEmbed U (gradX (orthogonalProject U X) (orthogonalProject V Y))

def rotatedGradientY {dx dy DX DY : Nat}
    (U : Fin dx → EVec DX) (V : Fin dy → EVec DY)
    (gradY : EVec dx → EVec dy → EVec dy)
    (X : EVec DX) (Y : EVec DY) : EVec DY :=
  orthogonalEmbed V (gradY (orthogonalProject U X) (orthogonalProject V Y))

def productProjectCLM {dx dy DX DY : Nat}
    (U : Fin dx → EVec DX) (V : Fin dy → EVec DY) :
    (EVec DX × EVec DY) →L[ℝ] (EVec dx × EVec dy) :=
  ((orthogonalProjectCLM U).comp
      (ContinuousLinearMap.fst ℝ (EVec DX) (EVec DY))).prod
    ((orthogonalProjectCLM V).comp
      (ContinuousLinearMap.snd ℝ (EVec DX) (EVec DY)))

@[simp] theorem productProjectCLM_apply {dx dy DX DY : Nat}
    (U : Fin dx → EVec DX) (V : Fin dy → EVec DY)
    (p : EVec DX × EVec DY) :
    productProjectCLM U V p =
      (orthogonalProject U p.1, orthogonalProject V p.2) := by
  simp [productProjectCLM]

/-- Coordinate fields represent the actual joint Frechet derivative. -/
def RepresentsRotatableGradient {dx dy : Nat}
    (F : EVec dx → EVec dy → ℝ)
    (gradX : EVec dx → EVec dy → EVec dx)
    (gradY : EVec dx → EVec dy → EVec dy) : Prop :=
  Differentiable ℝ (Function.uncurry F) ∧
    ∀ x y hx hy,
      fderiv ℝ (Function.uncurry F) (x, y) (hx, hy) =
        euclideanDot (gradX x y) hx + euclideanDot (gradY x y) hy

theorem rotatedObjective_representsGradient {dx dy DX DY : Nat}
    {F : EVec dx → EVec dy → ℝ}
    {gradX : EVec dx → EVec dy → EVec dx}
    {gradY : EVec dx → EVec dy → EVec dy}
    (hrep : RepresentsRotatableGradient F gradX gradY)
    (U : Fin dx → EVec DX) (V : Fin dy → EVec DY) :
    RepresentsRotatableGradient (rotatedObjective U V F)
      (rotatedGradientX U V gradX) (rotatedGradientY U V gradY) := by
  constructor
  · intro p
    have hP : HasFDerivAt
        (fun q : EVec DX × EVec DY ↦
          (orthogonalProject U q.1, orthogonalProject V q.2))
        (productProjectCLM U V) p :=
      by
        refine (productProjectCLM U V).hasFDerivAt.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun q ↦ ?_)
        exact (productProjectCLM_apply U V q).symm
    have hB := (hrep.1.differentiableAt).hasFDerivAt.comp p hP
    change DifferentiableAt ℝ
      (Function.uncurry F ∘ fun q : EVec DX × EVec DY ↦
        (orthogonalProject U q.1, orthogonalProject V q.2)) p
    exact hB.differentiableAt
  · intro X Y hX hY
    let P : (EVec DX × EVec DY) →L[ℝ] (EVec dx × EVec dy) :=
      productProjectCLM U V
    have hP : HasFDerivAt
        (fun q : EVec DX × EVec DY ↦
          (orthogonalProject U q.1, orthogonalProject V q.2)) P (X, Y) :=
      by
        refine P.hasFDerivAt.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun q ↦ ?_)
        exact (productProjectCLM_apply U V q).symm
    have hB : HasFDerivAt (Function.uncurry F)
        (fderiv ℝ (Function.uncurry F)
          (orthogonalProject U X, orthogonalProject V Y))
        (orthogonalProject U X, orthogonalProject V Y) :=
      (hrep.1 (orthogonalProject U X, orthogonalProject V Y)).hasFDerivAt
    have hc := hB.comp (X, Y) hP
    have hrot : HasFDerivAt
        (Function.uncurry (rotatedObjective U V F))
        ((fderiv ℝ (Function.uncurry F)
          (orthogonalProject U X, orthogonalProject V Y)).comp P) (X, Y) := by
      change HasFDerivAt
        (Function.uncurry F ∘ fun q : EVec DX × EVec DY ↦
          (orthogonalProject U q.1, orthogonalProject V q.2))
        ((fderiv ℝ (Function.uncurry F)
          (orthogonalProject U X, orthogonalProject V Y)).comp P) (X, Y)
      exact hc
    rw [hrot.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    rw [productProjectCLM_apply]
    change (fderiv ℝ (Function.uncurry F)
      (orthogonalProject U X, orthogonalProject V Y))
        (orthogonalProject U hX, orthogonalProject V hY) = _
    rw [hrep.2 (orthogonalProject U X) (orthogonalProject V Y)
      (orthogonalProject U hX) (orthogonalProject V hY)]
    unfold rotatedGradientX rotatedGradientY
    rw [euclideanDot_embed_left, euclideanDot_embed_left]
    rfl

def IsEuclideanJointlySmooth {dx dy : Nat} (L : ℝ)
    (gradX : EVec dx → EVec dy → EVec dx)
    (gradY : EVec dx → EVec dy → EVec dy) : Prop :=
  ∀ x y x' y',
    jointEuclideanSq (gradX x y - gradX x' y')
        (gradY x y - gradY x' y') ≤
      L ^ 2 * jointEuclideanSq (x - x') (y - y')

theorem rotatedGradient_isJointlySmooth {dx dy DX DY : Nat} {L : ℝ}
    {gradX : EVec dx → EVec dy → EVec dx}
    {gradY : EVec dx → EVec dy → EVec dy}
    {U : Fin dx → EVec DX} {V : Fin dy → EVec DY}
    (hU : IsEuclideanOrthonormalFrame U)
    (hV : IsEuclideanOrthonormalFrame V)
    (hsmooth : IsEuclideanJointlySmooth L gradX gradY) :
    IsEuclideanJointlySmooth L (rotatedGradientX U V gradX)
      (rotatedGradientY U V gradY) := by
  intro X Y X' Y'
  have hbase := hsmooth (orthogonalProject U X) (orthogonalProject V Y)
    (orthogonalProject U X') (orthogonalProject V Y')
  have hin : jointEuclideanSq
      (orthogonalProject U X - orthogonalProject U X')
      (orthogonalProject V Y - orthogonalProject V Y') ≤
      jointEuclideanSq (X - X') (Y - Y') := by
    rw [orthogonalProject_sub U X X', orthogonalProject_sub V Y Y']
    unfold jointEuclideanSq
    exact add_le_add (euclideanSq_orthogonalProject_le hU (X - X'))
      (euclideanSq_orthogonalProject_le hV (Y - Y'))
  have hmul := mul_le_mul_of_nonneg_left hin (sq_nonneg L)
  unfold rotatedGradientX rotatedGradientY jointEuclideanSq
  rw [orthogonalEmbed_sub, orthogonalEmbed_sub,
    euclideanSq_orthogonalEmbed hU, euclideanSq_orthogonalEmbed hV]
  exact hbase.trans hmul

def IsRotatedMaximizer {dx dy : Nat} (F : EVec dx → EVec dy → ℝ)
    (x : EVec dx) (y : EVec dy) : Prop :=
  ∀ v, F x v ≤ F x y

def RotationEnvelope {dx dy : Nat} (F : EVec dx → EVec dy → ℝ)
    (x : EVec dx) : ℝ :=
  sSup (Set.range (F x))

theorem rotatedObjective_isMaximizer {dx dy DX DY : Nat}
    {F : EVec dx → EVec dy → ℝ}
    {U : Fin dx → EVec DX} {V : Fin dy → EVec DY}
    (hV : IsEuclideanOrthonormalFrame V) {X : EVec DX} {y : EVec dy}
    (hy : IsRotatedMaximizer F (orthogonalProject U X) y) :
    IsRotatedMaximizer (rotatedObjective U V F) X (orthogonalEmbed V y) := by
  intro Y
  unfold rotatedObjective
  rw [orthogonalProject_embed hV]
  exact hy (orthogonalProject V Y)

/-- Surjectivity of `Vᵀ` gives exact equality of the lifted value function. -/
theorem rotationEnvelope_eq {dx dy DX DY : Nat}
    {F : EVec dx → EVec dy → ℝ}
    {U : Fin dx → EVec DX} {V : Fin dy → EVec DY}
    (hV : IsEuclideanOrthonormalFrame V) (X : EVec DX) :
    RotationEnvelope (rotatedObjective U V F) X =
      RotationEnvelope F (orthogonalProject U X) := by
  unfold RotationEnvelope
  congr 1
  ext z
  constructor
  · rintro ⟨Y, rfl⟩
    exact ⟨orthogonalProject V Y, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨orthogonalEmbed V y, ?_⟩
    simp [rotatedObjective, orthogonalProject_embed hV]

theorem range_rotationEnvelope_eq {dx dy DX DY : Nat}
    {F : EVec dx → EVec dy → ℝ}
    {U : Fin dx → EVec DX} {V : Fin dy → EVec DY}
    (hU : IsEuclideanOrthonormalFrame U)
    (hV : IsEuclideanOrthonormalFrame V) :
    Set.range (RotationEnvelope (rotatedObjective U V F)) =
      Set.range (RotationEnvelope F) := by
  ext z
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨orthogonalProject U X, (rotationEnvelope_eq hV X).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨orthogonalEmbed U x, ?_⟩
    rw [rotationEnvelope_eq hV, orthogonalProject_embed hU]

/-- A self-contained semantic version of the problem class used in Lemma 2.1. -/
structure EuclideanNCPLClass {dx dy : Nat} (L mu Delta : ℝ)
    (F : EVec dx → EVec dy → ℝ)
    (gradX : EVec dx → EVec dy → EVec dx)
    (gradY : EVec dx → EVec dy → EVec dy) : Prop where
  L_nonneg : 0 ≤ L
  mu_nonneg : 0 ≤ mu
  Delta_nonneg : 0 ≤ Delta
  gradient_representation : RepresentsRotatableGradient F gradX gradY
  jointly_smooth : IsEuclideanJointlySmooth L gradX gradY
  maximum_attained : ∀ x, ∃ y, IsRotatedMaximizer F x y
  maximization_PL : ∀ x y,
    (1 : ℝ) / 2 * euclideanSq (gradY x y) ≥
      mu * (RotationEnvelope F x - F x y)
  envelope_bddBelow : BddBelow (Set.range (RotationEnvelope F))
  initial_gap : RotationEnvelope F 0 -
    sInf (Set.range (RotationEnvelope F)) ≤ Delta

/-- Full class-preservation part of the manuscript's Lemma 2.1. -/
theorem EuclideanNCPLClass.rotate {dx dy DX DY : Nat} {L mu Delta : ℝ}
    {F : EVec dx → EVec dy → ℝ}
    {gradX : EVec dx → EVec dy → EVec dx}
    {gradY : EVec dx → EVec dy → EVec dy}
    {U : Fin dx → EVec DX} {V : Fin dy → EVec DY}
    (hclass : EuclideanNCPLClass L mu Delta F gradX gradY)
    (hU : IsEuclideanOrthonormalFrame U)
    (hV : IsEuclideanOrthonormalFrame V) :
    EuclideanNCPLClass L mu Delta (rotatedObjective U V F)
      (rotatedGradientX U V gradX) (rotatedGradientY U V gradY) := by
  refine
    { L_nonneg := hclass.L_nonneg
      mu_nonneg := hclass.mu_nonneg
      Delta_nonneg := hclass.Delta_nonneg
      gradient_representation := rotatedObjective_representsGradient
        hclass.gradient_representation U V
      jointly_smooth := rotatedGradient_isJointlySmooth hU hV hclass.jointly_smooth
      maximum_attained := ?_
      maximization_PL := ?_
      envelope_bddBelow := ?_
      initial_gap := ?_ }
  · intro X
    obtain ⟨y, hy⟩ := hclass.maximum_attained (orthogonalProject U X)
    exact ⟨orthogonalEmbed V y, rotatedObjective_isMaximizer hV hy⟩
  · intro X Y
    rw [rotationEnvelope_eq hV]
    unfold rotatedGradientY rotatedObjective
    rw [euclideanSq_orthogonalEmbed hV]
    exact hclass.maximization_PL (orthogonalProject U X) (orthogonalProject V Y)
  · rw [range_rotationEnvelope_eq hU hV]
    exact hclass.envelope_bddBelow
  · rw [rotationEnvelope_eq hV, orthogonalProject_zero,
      range_rotationEnvelope_eq hU hV]
    exact hclass.initial_gap

/-- The derivative represented by a finite dot product is transported by an
orthogonal projection to the embedded gradient. -/
theorem hasFDerivAt_comp_orthogonalProject {m D : Nat}
    {phi : EVec m → ℝ} {g : EVec m} {x : EVec m}
    (hphi : HasFDerivAt phi (finiteDotProductCLM g) x)
    (U : Fin m → EVec D) (X : EVec D)
    (hx : orthogonalProject U X = x) :
    HasFDerivAt (fun Z ↦ phi (orthogonalProject U Z))
      (finiteDotProductCLM (orthogonalEmbed U g)) X := by
  subst x
  have hproject : HasFDerivAt (orthogonalProject U) (orthogonalProjectCLM U) X :=
    by simpa using (orthogonalProjectCLM U).hasFDerivAt
  have hcomp := hphi.comp X hproject
  have hmap : (finiteDotProductCLM g).comp (orthogonalProjectCLM U) =
      finiteDotProductCLM (orthogonalEmbed U g) := by
    ext H
    simp only [ContinuousLinearMap.comp_apply, finiteDotProductCLM_apply,
      orthogonalProjectCLM_apply]
    change euclideanDot g (orthogonalProject U H) =
      euclideanDot (orthogonalEmbed U g) H
    rw [euclideanDot_embed_left]
    rfl
  rw [hmap] at hcomp
  exact hcomp

/-- Applied to the max-envelope identity, the lifted value function has the
embedded base gradient as its actual Frechet gradient.  The base derivative
is explicit because the manuscript obtains differentiability of NC--PL value
functions from its cited envelope theorem. -/
theorem rotatedEnvelope_hasFDerivAt {dx dy DX DY : Nat}
    {F : EVec dx → EVec dy → ℝ}
    {U : Fin dx → EVec DX} {V : Fin dy → EVec DY}
    (hV : IsEuclideanOrthonormalFrame V)
    {X : EVec DX} {g : EVec dx}
    (hbase : HasFDerivAt (RotationEnvelope F)
      (finiteDotProductCLM g) (orthogonalProject U X)) :
    HasFDerivAt (RotationEnvelope (rotatedObjective U V F))
      (finiteDotProductCLM (orthogonalEmbed U g)) X := by
  have heq : RotationEnvelope (rotatedObjective U V F) =
      fun Z : EVec DX ↦ RotationEnvelope F (orthogonalProject U Z) := by
    funext Z
    exact rotationEnvelope_eq hV Z
  rw [heq]
  exact hasFDerivAt_comp_orthogonalProject hbase U X rfl

/-- Exact gradient-norm identity in the final sentence of Lemma 2.1. -/
theorem rotated_value_gradient_sq_eq {m D : Nat}
    {U : Fin m → EVec D} (hU : IsEuclideanOrthonormalFrame U)
    (g : EVec m) :
    euclideanSq (orthogonalEmbed U g) = euclideanSq g :=
  euclideanSq_orthogonalEmbed hU g

/-- Hence epsilon-stationarity is equivalent before and after lifting. -/
theorem rotated_stationarity_iff {m D : Nat}
    {U : Fin m → EVec D} (hU : IsEuclideanOrthonormalFrame U)
    (g : EVec m) (epsilon : ℝ) :
    euclideanSq (orthogonalEmbed U g) ≤ epsilon ^ 2 ↔
      euclideanSq g ≤ epsilon ^ 2 := by
  rw [euclideanSq_orthogonalEmbed hU]

end

end NCPLRevised
