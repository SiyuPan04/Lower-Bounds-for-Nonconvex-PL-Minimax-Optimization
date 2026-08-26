/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.Gates
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Quadratic perspectives at zero scale

The apparent singularities in Lemma 5.1 all have the form
`eta^2 * Q (u / eta)`.  This file proves, for an arbitrary differentiable
bounded scalar gate, both the exact Fréchet derivative at nonzero scale and
the zero derivative on the entire degenerate hyperplane `eta = 0`.

Unlike a purely pointwise rewriting, `hasFDerivAt_quadraticPerspective_zero`
is a genuine two-variable Fréchet statement.  Its proof uses the quadratic
bound to control approaches in which the spatial coordinate and the scale
go to the interface at unrelated rates.
-/

namespace NCPLRevised

noncomputable section

/-- Fréchet differentiability on the product with the norm-topology
instances selected explicitly.  This avoids the harmless typeclass diamond
between the product and norm-induced additive-group instances. -/
def HasPairFDerivAt (f : (ℝ × ℝ) → ℝ)
    (f' : (ℝ × ℝ) →L[ℝ] ℝ) (z : ℝ × ℝ) : Prop :=
  @HasFDerivAt ℝ _ (ℝ × ℝ)
    Prod.normedAddCommGroup.toAddCommGroup Prod.normedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace ℝ
    Real.normedCommRing.toAddCommGroup
    (NormedAlgebra.toNormedSpace ℝ).toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace f f' z

/-- Totalized quadratic perspective of a scalar gate. -/
def quadraticPerspective (f : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  if z.1 = 0 then 0 else z.1 ^ 2 * f (z.2 / z.1)

/-- The explicit gradient of a quadratic perspective.  The value on the
zero-scale hyperplane is the genuine derivative proved below. -/
def quadraticPerspectiveGradient (f f' : ℝ → ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  if z.1 = 0 then (0, 0) else
    (z.1 * (2 * f (z.2 / z.1) - (z.2 / z.1) * f' (z.2 / z.1)),
      z.1 * f' (z.2 / z.1))

/-- Dot product with a two-coordinate gradient. -/
def pairGradientCLM (g : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  g.1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
    g.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem pairGradientCLM_apply (g h : ℝ × ℝ) :
    pairGradientCLM g h = g.1 * h.1 + g.2 * h.2 := by
  simp [pairGradientCLM]

@[simp] theorem quadraticPerspective_zero (f : ℝ → ℝ) (u : ℝ) :
    quadraticPerspective f (0, u) = 0 := by
  simp [quadraticPerspective]

@[simp] theorem quadraticPerspectiveGradient_zero (f f' : ℝ → ℝ) (u : ℝ) :
    quadraticPerspectiveGradient f f' (0, u) = (0, 0) := by
  simp [quadraticPerspectiveGradient]

/-- A gate in `[0,1]` gives the uniform quadratic value estimate required
at the degenerate perspective scale. -/
theorem abs_quadraticPerspective_le_sq (f : ℝ → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (z : ℝ × ℝ) :
    |quadraticPerspective f z| ≤ z.1 ^ 2 := by
  by_cases heta : z.1 = 0
  · simp [quadraticPerspective, heta]
  · rw [quadraticPerspective, if_neg heta]
    have hsq : 0 ≤ z.1 ^ 2 := sq_nonneg _
    have hnonneg : 0 ≤ z.1 ^ 2 * f (z.2 / z.1) :=
      mul_nonneg hsq (hf0 _)
    rw [abs_of_nonneg hnonneg]
    exact mul_le_of_le_one_right hsq (hf1 _)

/-- Exact nonzero-scale Fréchet derivative of the scalar quadratic
perspective. -/
theorem hasFDerivAt_quadraticPerspective_of_ne (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) {z : ℝ × ℝ} (hz : z.1 ≠ 0) :
    HasPairFDerivAt (quadraticPerspective f)
      (pairGradientCLM (quadraticPerspectiveGradient f f' z)) z := by
  letI : AddCommGroup (ℝ × ℝ) := Prod.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (ℝ × ℝ) := Prod.normedSpace.toModule
  letI : TopologicalSpace (ℝ × ℝ) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedCommRing.toAddCommGroup
  letI : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasPairFDerivAt
  have hfst : HasFDerivAt (fun w : ℝ × ℝ ↦ w.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) z :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hsnd : HasFDerivAt (fun w : ℝ × ℝ ↦ w.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) z :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have hinv := (hasDerivAt_inv hz).hasFDerivAt.comp z hfst
  have hratio := hsnd.mul hinv
  have hgate := (hf (z.2 / z.1)).hasFDerivAt.comp z hratio
  have hsq := hfst.pow 2
  have hraw := hsq.mul hgate
  have hevent : Filter.EventuallyEq (nhds z) (quadraticPerspective f)
      (fun w : ℝ × ℝ ↦ w.1 ^ 2 * f (w.2 / w.1)) := by
    filter_upwards [hfst.continuousAt.eventually_ne hz] with w hw
    simp [quadraticPerspective, hw]
  have hfinal := hraw.congr_of_eventuallyEq hevent
  apply hfinal.congr_fderiv
  ext
  all_goals simp [pairGradientCLM, quadraticPerspectiveGradient, hz]
  all_goals field_simp [hz]
  all_goals ring

/-- The totalized perspective has derivative zero at every point of the
zero-scale hyperplane.  Only the gate's range bound is used. -/
theorem hasFDerivAt_quadraticPerspective_zero (f : ℝ → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (u : ℝ) :
    HasPairFDerivAt (quadraticPerspective f)
      (0 : (ℝ × ℝ) →L[ℝ] ℝ) (0, u) := by
  letI : AddCommGroup (ℝ × ℝ) := Prod.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (ℝ × ℝ) := Prod.normedSpace.toModule
  letI : TopologicalSpace (ℝ × ℝ) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedCommRing.toAddCommGroup
  letI : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasPairFDerivAt
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,
    Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [eventually_norm_sub_lt (0 : ℝ × ℝ) hc] with h hh
  have hcoord : |h.1| ≤ ‖h‖ := by
    simpa [Real.norm_eq_abs] using norm_fst_le h
  have hvalue := abs_quadraticPerspective_le_sq f hf0 hf1
    ((0, u) + h)
  have hfirst : ((0, u) + h).1 = h.1 := by simp
  rw [hfirst] at hvalue
  have hsq : h.1 ^ 2 ≤ ‖h‖ ^ 2 := by
    nlinarith [abs_nonneg h.1, norm_nonneg h, sq_abs h.1]
  have hh' : ‖h‖ < c := by simpa using hh
  have hsmall : ‖h‖ ^ 2 ≤ c * ‖h‖ := by
    nlinarith [norm_nonneg h]
  simpa [Real.norm_eq_abs] using hvalue.trans (hsq.trans hsmall)

/-- The explicit gradient is the actual derivative at every scale. -/
theorem hasFDerivAt_quadraticPerspective (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (z : ℝ × ℝ) :
    HasPairFDerivAt (quadraticPerspective f)
      (pairGradientCLM (quadraticPerspectiveGradient f f' z)) z := by
  rcases z with ⟨eta, u⟩
  by_cases hz : eta = 0
  · subst eta
    have hzero := hasFDerivAt_quadraticPerspective_zero f hf0 hf1 u
    simpa [quadraticPerspectiveGradient, pairGradientCLM] using hzero
  · exact hasFDerivAt_quadraticPerspective_of_ne f f' hf hz

/-- The paper's terminal `q` perspective. -/
def qPerspective : ℝ × ℝ → ℝ := quadraticPerspective q

/-- The paper's shifted `p` perspective. -/
def pPerspective : ℝ × ℝ → ℝ := quadraticPerspective p

/-- Genuine global Fréchet derivative for the totalized `q` perspective. -/
theorem hasFDerivAt_qPerspective (z : ℝ × ℝ) :
    HasPairFDerivAt qPerspective
      (pairGradientCLM (quadraticPerspectiveGradient q qDeriv z)) z := by
  exact hasFDerivAt_quadraticPerspective q qDeriv hasDerivAt_q
    q_nonneg q_le_one z

/-- Genuine global Fréchet derivative for the totalized `p` perspective. -/
theorem hasFDerivAt_pPerspective (z : ℝ × ℝ) :
    HasPairFDerivAt pPerspective
      (pairGradientCLM (quadraticPerspectiveGradient p pDeriv z)) z := by
  exact hasFDerivAt_quadraticPerspective p pDeriv hasDerivAt_p
    p_nonneg p_le_one z

end

end NCPLRevised
