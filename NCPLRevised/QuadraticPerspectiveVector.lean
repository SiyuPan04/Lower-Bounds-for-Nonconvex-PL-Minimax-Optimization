/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.QuadraticPerspectiveSmoothness

/-!
# Vector quadratic perspectives

This is the finite-dimensional/vector version of
`QuadraticPerspectiveSmoothness`.  It covers the two-coordinate residual
kernel `1 - q(u) p(v)` in the proof of Lemma 5.1.
-/

namespace NCPLRevised

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Totalized map `(eta,u) ↦ eta² Q(u/eta)`. -/
def quadraticPerspectiveVec (Q : E → ℝ) (z : ℝ × E) : ℝ :=
  if z.1 = 0 then 0 else z.1 ^ 2 * Q (z.1⁻¹ • z.2)

/-- Explicit derivative of the vector quadratic perspective. -/
def quadraticPerspectiveVecFDeriv (Q : E → ℝ)
    (Q' : E → (E →L[ℝ] ℝ)) (z : ℝ × E) :
    (ℝ × E) →L[ℝ] ℝ :=
  if _h : z.1 = 0 then 0 else
    (2 * z.1 * Q (z.1⁻¹ • z.2) -
        Q' (z.1⁻¹ • z.2) z.2) •
        ContinuousLinearMap.fst ℝ ℝ E +
      z.1 • (Q' (z.1⁻¹ • z.2)).comp
        (ContinuousLinearMap.snd ℝ ℝ E)

/-- Explicit selection of the norm-topology instances on the product. -/
def HasVecPerspectiveFDerivAt (f : (ℝ × E) → ℝ)
    (f' : (ℝ × E) →L[ℝ] ℝ) (z : ℝ × E) : Prop :=
  @HasFDerivAt ℝ _ (ℝ × E)
    Prod.normedAddCommGroup.toAddCommGroup Prod.normedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace ℝ
    Real.normedCommRing.toAddCommGroup
    (NormedAlgebra.toNormedSpace ℝ).toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace f f' z

@[simp] theorem quadraticPerspectiveVec_zero (Q : E → ℝ) (u : E) :
    quadraticPerspectiveVec Q (0, u) = 0 := by
  simp [quadraticPerspectiveVec]

theorem abs_quadraticPerspectiveVec_le_sq (Q : E → ℝ)
    (hQ0 : ∀ u, 0 ≤ Q u) (hQ1 : ∀ u, Q u ≤ 1) (z : ℝ × E) :
    |quadraticPerspectiveVec Q z| ≤ z.1 ^ 2 := by
  by_cases heta : z.1 = 0
  · simp [quadraticPerspectiveVec, heta]
  · rw [quadraticPerspectiveVec, if_neg heta]
    have hsq : 0 ≤ z.1 ^ 2 := sq_nonneg _
    have hnonneg : 0 ≤ z.1 ^ 2 * Q (z.1⁻¹ • z.2) :=
      mul_nonneg hsq (hQ0 _)
    rw [abs_of_nonneg hnonneg]
    exact mul_le_of_le_one_right hsq (hQ1 _)

theorem hasVecPerspectiveFDerivAt_of_ne (Q : E → ℝ)
    (Q' : E → (E →L[ℝ] ℝ))
    (hQ : ∀ u, HasFDerivAt Q (Q' u) u)
    {z : ℝ × E} (hz : z.1 ≠ 0) :
    HasVecPerspectiveFDerivAt (quadraticPerspectiveVec Q)
      (quadraticPerspectiveVecFDeriv Q Q' z) z := by
  letI : AddCommGroup (ℝ × E) := Prod.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (ℝ × E) := Prod.normedSpace.toModule
  letI : TopologicalSpace (ℝ × E) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedCommRing.toAddCommGroup
  letI : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasVecPerspectiveFDerivAt
  have hfst : HasFDerivAt (fun w : ℝ × E ↦ w.1)
      (ContinuousLinearMap.fst ℝ ℝ E) z :=
    (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt
  have hsnd : HasFDerivAt (fun w : ℝ × E ↦ w.2)
      (ContinuousLinearMap.snd ℝ ℝ E) z :=
    (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt
  have hinv := (hasDerivAt_inv hz).hasFDerivAt.comp z hfst
  have hnorm := hinv.smul hsnd
  have hgate := (hQ (z.1⁻¹ • z.2)).comp z hnorm
  have hsq := hfst.pow 2
  have hraw := hsq.mul hgate
  have hevent : Filter.EventuallyEq (nhds z) (quadraticPerspectiveVec Q)
      (fun w : ℝ × E ↦ w.1 ^ 2 * Q (w.1⁻¹ • w.2)) := by
    filter_upwards [hfst.continuousAt.eventually_ne hz] with w hw
    simp [quadraticPerspectiveVec, hw]
  have hfinal := hraw.congr_of_eventuallyEq hevent
  apply hfinal.congr_fderiv
  ext
  all_goals simp [quadraticPerspectiveVecFDeriv, hz]
  all_goals field_simp [hz]
  all_goals ring

theorem hasVecPerspectiveFDerivAt_zero (Q : E → ℝ)
    (hQ0 : ∀ u, 0 ≤ Q u) (hQ1 : ∀ u, Q u ≤ 1) (u : E) :
    HasVecPerspectiveFDerivAt (quadraticPerspectiveVec Q)
      (0 : (ℝ × E) →L[ℝ] ℝ) (0, u) := by
  letI : AddCommGroup (ℝ × E) := Prod.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (ℝ × E) := Prod.normedSpace.toModule
  letI : TopologicalSpace (ℝ × E) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedCommRing.toAddCommGroup
  letI : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasVecPerspectiveFDerivAt
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,
    Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [eventually_norm_sub_lt (0 : ℝ × E) hc] with h hh
  have hcoord : |h.1| ≤ ‖h‖ := by
    simpa [Real.norm_eq_abs] using norm_fst_le h
  have hvalue := abs_quadraticPerspectiveVec_le_sq Q hQ0 hQ1
    ((0, u) + h)
  have hfirst : ((0, u) + h).1 = h.1 := by simp
  rw [hfirst] at hvalue
  have hsq : h.1 ^ 2 ≤ ‖h‖ ^ 2 := by
    nlinarith [abs_nonneg h.1, norm_nonneg h, sq_abs h.1]
  have hh' : ‖h‖ < c := by simpa using hh
  have hsmall : ‖h‖ ^ 2 ≤ c * ‖h‖ := by
    nlinarith [norm_nonneg h]
  simpa [Real.norm_eq_abs] using hvalue.trans (hsq.trans hsmall)

theorem hasVecPerspectiveFDerivAt (Q : E → ℝ)
    (Q' : E → (E →L[ℝ] ℝ))
    (hQ : ∀ u, HasFDerivAt Q (Q' u) u)
    (hQ0 : ∀ u, 0 ≤ Q u) (hQ1 : ∀ u, Q u ≤ 1)
    (z : ℝ × E) :
    HasVecPerspectiveFDerivAt (quadraticPerspectiveVec Q)
      (quadraticPerspectiveVecFDeriv Q Q' z) z := by
  rcases z with ⟨eta, u⟩
  by_cases heta : eta = 0
  · subst eta
    have hzero := hasVecPerspectiveFDerivAt_zero Q hQ0 hQ1 u
    simpa [quadraticPerspectiveVecFDeriv] using hzero
  · exact hasVecPerspectiveFDerivAt_of_ne Q Q' hQ heta

end

end NCPLRevised
