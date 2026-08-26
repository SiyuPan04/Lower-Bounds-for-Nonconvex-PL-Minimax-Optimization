/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.ZeroChain

/-!
# Finite-dimensional support for the outer Carmon chain

This file contains only generic facts about `EVec T = Fin T → ℝ`.  In
particular it has no dependency on the inner hard instance.
-/

namespace NCPLRevised

noncomputable section

/-- Squared Euclidean norm, written as a finite coordinate sum. -/
def vecSq {T : ℕ} (v : EVec T) : ℝ :=
  ∑ i : Fin T, v i ^ 2

/-- Coordinate projection as a continuous linear map for the norm topology. -/
def evecProj {T : ℕ} (i : Fin T) : EVec T →L[ℝ] ℝ := by
  letI : AddCommGroup (EVec T) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec T) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec T) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact LinearMap.toContinuousLinearMap
    ({ toFun := fun z : EVec T ↦ z i
       map_add' := by intro x y; rfl
       map_smul' := by intro c x; rfl } : EVec T →ₗ[ℝ] ℝ)

@[simp] theorem evecProj_apply {T : ℕ} (i : Fin T) (z : EVec T) :
    evecProj i z = z i := by
  rfl

/-- Continuous linear functional represented by Euclidean dot product. -/
def evecDot {T : ℕ} (g : EVec T) : EVec T →L[ℝ] ℝ := by
  letI : AddCommGroup (EVec T) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec T) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec T) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact LinearMap.toContinuousLinearMap
    ({ toFun := fun h : EVec T ↦ ∑ i : Fin T, g i * h i
       map_add' := by
         intro x y
         rw [← Finset.sum_add_distrib]
         apply Finset.sum_congr rfl
         intro i _
         simp only [Pi.add_apply]
         ring
       map_smul' := by
         intro c x
         simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
         rw [Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro i _
         ring } : EVec T →ₗ[ℝ] ℝ)

@[simp] theorem evecDot_apply {T : ℕ} (g h : EVec T) :
    evecDot g h = ∑ i : Fin T, g i * h i := by
  rfl

/-- Reindex a sum over nonzero coordinates by their predecessors. -/
theorem sum_predecessor_eq_sum_successor {T : ℕ} (a h : EVec T) :
    (∑ i : Fin T,
      if hi : i.1 = 0 then 0 else a i * h ⟨i.1 - 1, by omega⟩) =
    ∑ j : Fin T,
      if hj : j.1 + 1 < T then a ⟨j.1 + 1, hj⟩ * h j else 0 := by
  cases T with
  | zero => simp
  | succ n =>
      rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, ↓reduceDIte, Fin.val_succ,
        Nat.add_eq_zero_iff, one_ne_zero, and_false, add_tsub_cancel_right,
        zero_add, Fin.val_castSucc, Order.lt_add_one_iff, Order.add_one_le_iff,
        Fin.is_lt, Fin.val_last, lt_self_iff_false, add_zero]
      apply Finset.sum_congr rfl
      intro x _
      rfl

theorem continuousLinearMap_sum_apply {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E]
    [NormedSpace ℝ F] (f : ι → E →L[ℝ] F) (x : E) :
    (∑ i, f i) x = ∑ i, f i x := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

end

end NCPLRevised
