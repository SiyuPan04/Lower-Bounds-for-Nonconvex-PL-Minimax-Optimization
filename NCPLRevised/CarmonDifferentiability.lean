/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.CarmonChain
import NCPLRevised.OuterLinearAlgebra

/-!
# Actual Fréchet gradient of the Carmon chain
-/

namespace NCPLRevised

noncomputable section

/-- Fréchet differentiability on `EVec` with the norm topology and the
standard normed-ring structure on the real codomain.  This is mathematically
the same finite-dimensional topology used by `HasEVecFDerivAt`; the separate
wrapper keeps the scalar structure chosen by the integral FTC theorem. -/
def HasCarmonFDerivAt {N : Nat} (f : EVec N → ℝ)
    (f' : EVec N →L[ℝ] ℝ) (z : EVec N) : Prop :=
  @HasFDerivAt ℝ _ (EVec N)
    Pi.normedAddCommGroup.toAddCommGroup Pi.normedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace ℝ
    Real.normedCommRing.toAddCommGroup
    (NormedAlgebra.toNormedSpace ℝ).toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace f f' z

def carmonTermPrevCoeff {T : Nat} (x : EVec T) (i : Fin T) : ℝ :=
  if hi : i.1 = 0 then 0 else
    -(carmonPsiDeriv (-x ⟨i.1 - 1, by omega⟩) * carmonPhi (-x i) +
      carmonPsiDeriv (x ⟨i.1 - 1, by omega⟩) * carmonPhi (x i))

def carmonTermFDeriv {T : Nat} (x : EVec T) (i : Fin T) :
    EVec T →L[ℝ] ℝ :=
  if hi : i.1 = 0 then
    (-carmonPhiDeriv (x i)) • evecProj i
  else
    carmonTermPrevCoeff x i • evecProj ⟨i.1 - 1, by omega⟩ +
      (-carmonIncoming x i) • evecProj i

private theorem hasDerivAt_carmonPsi_local (t : ℝ) :
    HasDerivAt carmonPsi (carmonPsiDeriv t) t := by
  have h := (differentiable_carmonPsi t).hasDerivAt
  rw [deriv_carmonPsi] at h
  exact h

theorem hasEVecFDerivAt_carmonTerm {T : Nat} (x : EVec T) (i : Fin T) :
    HasCarmonFDerivAt (fun w : EVec T ↦ carmonTerm w i)
      (carmonTermFDeriv x i) x := by
  letI : AddCommGroup (EVec T) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec T) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec T) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedCommRing.toAddCommGroup
  letI : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasCarmonFDerivAt
  by_cases hi : i.1 = 0
  · have hhere : HasFDerivAt (fun w : EVec T ↦ w i) (evecProj i) x :=
      (evecProj (T := T) i).hasFDerivAt
    have hphi := (hasDerivAt_carmonPhi (x i)).hasFDerivAt.comp x hhere
    have hraw := hphi.const_mul (-carmonPsi 1)
    convert hraw using 1
    · funext w
      rw [carmonTerm, dif_pos hi, carmonPsi_one]
      simp
    · ext h
      simp [carmonTermFDeriv, hi, carmonPsi_one]
      ring
  · let p : Fin T := ⟨i.1 - 1, by omega⟩
    have hprev : HasFDerivAt (fun w : EVec T ↦ w p) (evecProj p) x :=
      (evecProj (T := T) p).hasFDerivAt
    have hhere : HasFDerivAt (fun w : EVec T ↦ w i) (evecProj i) x :=
      (evecProj (T := T) i).hasFDerivAt
    have hpsiNeg := (hasDerivAt_carmonPsi_local (-x p)).hasFDerivAt.comp x hprev.neg
    have hphiNeg := (hasDerivAt_carmonPhi (-x i)).hasFDerivAt.comp x hhere.neg
    have hpsiPos := (hasDerivAt_carmonPsi_local (x p)).hasFDerivAt.comp x hprev
    have hphiPos := (hasDerivAt_carmonPhi (x i)).hasFDerivAt.comp x hhere
    have hraw := (hpsiNeg.mul hphiNeg).sub (hpsiPos.mul hphiPos)
    convert hraw using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    · funext w
      simp [carmonTerm, hi, p, Function.comp_def]
    · ext h
      simp [carmonTermFDeriv, carmonTermPrevCoeff, carmonIncoming, hi, p]
      ring

def carmonFFDeriv (T : Nat) (x : EVec T) : EVec T →L[ℝ] ℝ :=
  ∑ i : Fin T, carmonTermFDeriv x i

theorem hasEVecFDerivAt_carmonF (T : Nat) (x : EVec T) :
    HasCarmonFDerivAt (carmonF T) (carmonFFDeriv T x) x := by
  letI : AddCommGroup (EVec T) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec T) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec T) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedCommRing.toAddCommGroup
  letI : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasCarmonFDerivAt carmonF carmonFFDeriv
  apply HasFDerivAt.fun_sum
  intro i _
  simpa only [HasCarmonFDerivAt] using hasEVecFDerivAt_carmonTerm x i

@[simp] theorem carmonTermFDeriv_apply {T : Nat} (x h : EVec T) (i : Fin T) :
    carmonTermFDeriv x i h =
      (if hi : i.1 = 0 then 0 else
        carmonTermPrevCoeff x i * h ⟨i.1 - 1, by omega⟩) -
        carmonIncoming x i * h i := by
  by_cases hi : i.1 = 0
  · simp [carmonTermFDeriv, carmonIncoming, hi]
  · simp [carmonTermFDeriv, hi]
    ring

theorem carmonTermPrevCoeff_successor {T : Nat} (x : EVec T) (i : Fin T)
    (hi : i.1 + 1 < T) :
    carmonTermPrevCoeff x ⟨i.1 + 1, hi⟩ = -carmonForward x i := by
  simp [carmonTermPrevCoeff, carmonForward, hi]

theorem sum_carmonPrevCoeff_eq_forward {T : Nat} (x h : EVec T) :
    (∑ i : Fin T, if hi : i.1 = 0 then 0 else
      carmonTermPrevCoeff x i * h ⟨i.1 - 1, by omega⟩) =
      ∑ j : Fin T, -carmonForward x j * h j := by
  rw [sum_predecessor_eq_sum_successor (fun i ↦ carmonTermPrevCoeff x i) h]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.1 + 1 < T
  · rw [dif_pos hj, carmonTermPrevCoeff_successor x j hj]
  · simp [carmonForward, hj]

theorem carmonFFDeriv_apply_eq_gradient_dot (T : Nat) (x h : EVec T) :
    carmonFFDeriv T x h = ∑ i : Fin T, carmonGradient T x i * h i := by
  unfold carmonFFDeriv
  rw [continuousLinearMap_sum_apply]
  simp_rw [carmonTermFDeriv_apply]
  rw [Finset.sum_sub_distrib, sum_carmonPrevCoeff_eq_forward]
  unfold carmonGradient
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem carmonFFDeriv_eq_gradientDot (T : Nat) (x : EVec T) :
    carmonFFDeriv T x = evecDot (carmonGradient T x) := by
  ext h
  rw [carmonFFDeriv_apply_eq_gradient_dot]
  rfl

theorem hasEVecFDerivAt_carmonF_gradient (T : Nat) (x : EVec T) :
    HasCarmonFDerivAt (carmonF T) (evecDot (carmonGradient T x)) x := by
  rw [← carmonFFDeriv_eq_gradientDot]
  exact hasEVecFDerivAt_carmonF T x

end

end NCPLRevised
