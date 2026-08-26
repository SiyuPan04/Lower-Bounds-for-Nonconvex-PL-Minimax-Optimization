/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.DualChain

/-!
# Coordinate derivatives of the dual chain

This file identifies the explicit fields `dualGradient` and `coupledGradient`
with the actual one-variable derivatives obtained by updating one coordinate.
-/

namespace NCPLRevised

noncomputable section

private theorem chainPrev_update_self' {N : ℕ} (y : ChainPoint N)
    (k : Fin N) (t : ℝ) :
    chainPrev (Function.update y k t) k.1 = chainPrev y k.1 := by
  by_cases hk0 : k.1 = 0
  · simp [chainPrev, hk0]
  · have hpredN : k.1 - 1 < N := by omega
    let pred : Fin N := ⟨k.1 - 1, hpredN⟩
    have hne : pred ≠ k := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [pred] at hv
      omega
    simp [chainPrev, hk0, chainCoord, hpredN, pred, hne]

private theorem chainPrev_update_succ' {N : ℕ} (y : ChainPoint N)
    (k i : Fin N) (t : ℝ) (hi : i.1 = k.1 + 1) :
    chainPrev (Function.update y k t) i.1 = t := by
  have hkN : k.1 < N := k.isLt
  simp [chainPrev, chainCoord, hi, hkN]

private theorem chainPrev_update_other' {N : ℕ} (y : ChainPoint N)
    (k i : Fin N) (t : ℝ) (hi : i.1 ≠ k.1 + 1) :
    chainPrev (Function.update y k t) i.1 = chainPrev y i.1 := by
  by_cases hi0 : i.1 = 0
  · simp [chainPrev, hi0]
  · have hpredN : i.1 - 1 < N := by omega
    let pred : Fin N := ⟨i.1 - 1, hpredN⟩
    have hne : pred ≠ k := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [pred] at hv
      omega
    simp [chainPrev, hi0, chainCoord, hpredN, pred, hne]

private def updateTermDerivative (N : ℕ) (y : ChainPoint N) (k i : Fin N) : ℝ :=
  (if i = k then -(incoming N y k + penalty N y k) else 0) +
    if i.1 = k.1 + 1 then
      -(omega N (k.1 + 1) * qDeriv (y k) * p (y i))
    else 0

private theorem hasDerivAt_localInteraction_update (N : ℕ) (y : ChainPoint N)
    (k i : Fin N) :
    HasDerivAt (fun t : ℝ ↦ localInteraction N (Function.update y k t) i)
      (updateTermDerivative N y k i) (y k) := by
  by_cases hik : i = k
  · subst i
    have hgate : HasDerivAt
        (fun t : ℝ ↦ 1 - q (chainPrev y k.1) * p t)
        (-(q (chainPrev y k.1) * pDeriv (y k))) (y k) := by
      convert (hasDerivAt_const (x := y k) (c := (1 : ℝ))).sub
        ((hasDerivAt_const (x := y k) (c := q (chainPrev y k.1))).mul
          (hasDerivAt_p (y k))) using 1
      all_goals try { apply AddCommGroup.ext <;> rfl }
      all_goals try { apply Module.ext <;> rfl }
      · funext t
        change 1 - q (chainPrev y k.1) * p t =
          1 - q (chainPrev y k.1) * p t
        rfl
      · ring
    have h := (hgate.const_mul (omega N k.1)).add
      ((hasDerivAt_negPartSq (y k)).const_mul (omega N (k.1 + 1) / 2))
    convert h using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      simp [localInteraction, gateTerm, chainPrev_update_self']
    · simp [updateTermDerivative, incoming, penalty]
      ring
  · by_cases hisucc : i.1 = k.1 + 1
    · have hgate : HasDerivAt
          (fun t : ℝ ↦ 1 - q t * p (y i))
          (-(qDeriv (y k) * p (y i))) (y k) := by
        convert (hasDerivAt_const (x := y k) (c := (1 : ℝ))).sub
          ((hasDerivAt_q (y k)).mul_const (p (y i))) using 1
        all_goals try { apply AddCommGroup.ext <;> rfl }
        all_goals try { apply Module.ext <;> rfl }
        · funext t
          simp only [Pi.sub_apply]
        · ring
      have hpen : HasDerivAt
          (fun _t : ℝ ↦ omega N (i.1 + 1) / 2 * (negPart (y i)) ^ 2)
          0 (y k) := hasDerivAt_const (x := y k) (c := _)
      have h := (hgate.const_mul (omega N i.1)).add hpen
      convert h using 1
      all_goals try { apply AddCommGroup.ext <;> rfl }
      all_goals try { apply Module.ext <;> rfl }
      · funext t
        simp only [localInteraction, gateTerm, chainPrev_update_succ' y k i t hisucc]
        simp [hik]
      · simp [updateTermDerivative, hik, hisucc]
        ring
    · have hconst : HasDerivAt
          (fun _t : ℝ ↦ localInteraction N y i) 0 (y k) :=
        hasDerivAt_const (x := y k) (c := _)
      convert hconst using 1
      · funext t
        simp [localInteraction, gateTerm, hik, chainPrev_update_other' y k i t hisucc]
      · simp [updateTermDerivative, hik, hisucc]

private theorem sum_updateTermDerivative (N : ℕ) (y : ChainPoint N) (k : Fin N) :
    ∑ i : Fin N, updateTermDerivative N y k i = dualGradient N y k := by
  classical
  rw [show (∑ i : Fin N, updateTermDerivative N y k i) =
      (∑ i : Fin N, if i = k then -(incoming N y k + penalty N y k) else 0) +
        ∑ i : Fin N, if i.1 = k.1 + 1 then
          -(omega N (k.1 + 1) * qDeriv (y k) * p (y i)) else 0 by
    simp only [updateTermDerivative, Finset.sum_add_distrib]]
  have hfirst :
      (∑ i : Fin N, if i = k then -(incoming N y k + penalty N y k) else 0) =
        -(incoming N y k + penalty N y k) := by simp
  rw [hfirst]
  by_cases hk : k.1 + 1 < N
  · let s : Fin N := ⟨k.1 + 1, hk⟩
    have hsucc :
        (∑ i : Fin N, if i.1 = k.1 + 1 then
            -(omega N (k.1 + 1) * qDeriv (y k) * p (y i)) else 0) =
          -(omega N (k.1 + 1) * qDeriv (y k) * p (y s)) := by
      rw [Finset.sum_eq_single_of_mem s (Finset.mem_univ s)]
      · simp [s]
      · intro i _ his
        have hi : i.1 ≠ k.1 + 1 := by
          intro hval
          apply his
          apply Fin.ext
          simpa [s] using hval
        simp [hi]
    rw [hsucc]
    simp [dualGradient, outgoing, hk, s]
    ring
  · have hsucc :
        (∑ i : Fin N, if i.1 = k.1 + 1 then
            -(omega N (k.1 + 1) * qDeriv (y k) * p (y i)) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hi : i.1 ≠ k.1 + 1 := by
        intro hval
        apply hk
        simpa [hval] using i.isLt
      simp [hi]
    rw [hsucc]
    simp [dualGradient, outgoing, hk]

/-- The field in equation (7) is the genuine derivative along each coordinate. -/
theorem hasDerivAt_dualChain_update (N : ℕ) (y : ChainPoint N) (k : Fin N) :
    HasDerivAt (fun t : ℝ ↦ dualChain N (Function.update y k t))
      (dualGradient N y k) (y k) := by
  have hsum : HasDerivAt
      (fun t : ℝ ↦ ∑ i : Fin N, localInteraction N (Function.update y k t) i)
      (∑ i : Fin N, updateTermDerivative N y k i) (y k) :=
    HasDerivAt.fun_sum fun i _ ↦ hasDerivAt_localInteraction_update N y k i
  simpa [dualChain, sum_updateTermDerivative] using hsum

private theorem terminalCoord_update_self {N : ℕ} (y : ChainPoint N)
    (k : Fin N) (t : ℝ) (hk : k.1 + 1 = N) :
    chainCoord (Function.update y k t) (N - 1) = t := by
  have hlast : N - 1 < N := by omega
  have hkval : k.1 = N - 1 := by omega
  let last : Fin N := ⟨N - 1, hlast⟩
  have hlastk : last = k := by
    apply Fin.ext
    simpa [last] using hkval.symm
  simp [chainCoord, hlast, last, hlastk]

private theorem terminalCoord_update_other {N : ℕ} (y : ChainPoint N)
    (k : Fin N) (t : ℝ) (hk : k.1 + 1 ≠ N) :
    chainCoord (Function.update y k t) (N - 1) = chainCoord y (N - 1) := by
  have hlast : N - 1 < N := by omega
  let last : Fin N := ⟨N - 1, hlast⟩
  have hlastk : last ≠ k := by
    intro h
    apply hk
    have hval := congrArg Fin.val h
    dsimp [last] at hval
    omega
  simp [chainCoord, hlast, last, hlastk]

/-- The field used in Lemma 4.3 is the genuine derivative of `coupledDual`
along each coordinate. -/
theorem hasDerivAt_coupledDual_update (N : ℕ) (α : ℝ)
    (y : ChainPoint N) (k : Fin N) :
    HasDerivAt (fun t : ℝ ↦ coupledDual N α (Function.update y k t))
      (coupledGradient N α y k) (y k) := by
  have hdual := hasDerivAt_dualChain_update N y k
  by_cases hk : k.1 + 1 = N
  · have hq := (hasDerivAt_q (y k)).const_mul α
    have h := hq.sub hdual
    convert h using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      simp only [coupledDual, terminalCoord_update_self y k t hk]
      change α * q t - dualChain N (Function.update y k t) =
        α * q t - dualChain N (Function.update y k t)
      rfl
    · simp [coupledGradient, hk]
      ring
  · have hq : HasDerivAt
        (fun _t : ℝ ↦ α * q (chainCoord y (N - 1))) 0 (y k) :=
      hasDerivAt_const (x := y k) (c := _)
    have h := hq.sub hdual
    convert h using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      simp only [coupledDual, terminalCoord_update_other y k t hk]
      change α * q (chainCoord y (N - 1)) - dualChain N (Function.update y k t) =
        α * q (chainCoord y (N - 1)) - dualChain N (Function.update y k t)
      rfl
    · simp [coupledGradient, hk]

/-- The continuous linear functional represented by a finite dot product. -/
def finiteDotProductCLM {N : ℕ} (g : ChainPoint N) : ChainPoint N →L[ℝ] ℝ :=
  ∑ k : Fin N, (g k) • ContinuousLinearMap.proj k

@[simp] theorem finiteDotProductCLM_apply {N : ℕ} (g v : ChainPoint N) :
    finiteDotProductCLM g v = ∑ k : Fin N, g k * v k := by
  simp [finiteDotProductCLM, smul_eq_mul]

private theorem differentiableAt_chainPrev (N : ℕ) (y : ChainPoint N) (i : Fin N) :
    DifferentiableAt ℝ (fun z : ChainPoint N ↦ chainPrev z i.1) y := by
  by_cases hi0 : i.1 = 0
  · simp [chainPrev, hi0]
  · have hpredN : i.1 - 1 < N := by omega
    simp only [chainPrev, hi0, ↓reduceIte, chainCoord, hpredN, dite_true]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N ↦ ℝ)
      (⟨i.1 - 1, hpredN⟩ : Fin N)).differentiableAt

private theorem differentiableAt_localInteraction (N : ℕ) (y : ChainPoint N)
    (i : Fin N) :
    DifferentiableAt ℝ (fun z : ChainPoint N ↦ localInteraction N z i) y := by
  have hprev := differentiableAt_chainPrev N y i
  have hq : DifferentiableAt ℝ (fun z : ChainPoint N ↦ q (chainPrev z i.1)) y :=
    by simpa only [Function.comp_def] using
      (differentiable_q (chainPrev y i.1)).comp y hprev
  have hcoord : DifferentiableAt ℝ (fun z : ChainPoint N ↦ z i) y := by fun_prop
  have hp : DifferentiableAt ℝ (fun z : ChainPoint N ↦ p (z i)) y :=
    by simpa only [Function.comp_def] using (differentiable_p (y i)).comp y hcoord
  have hneg : DifferentiableAt ℝ (fun z : ChainPoint N ↦ negPart (z i) ^ 2) y :=
    by simpa only [Function.comp_def] using
      (hasDerivAt_negPartSq (y i)).differentiableAt.comp y hcoord
  unfold localInteraction gateTerm
  fun_prop

private theorem differentiableAt_dualChain (N : ℕ) (y : ChainPoint N) :
    DifferentiableAt ℝ (dualChain N) y := by
  unfold dualChain
  exact DifferentiableAt.fun_sum fun i _ ↦ differentiableAt_localInteraction N y i

private theorem fderiv_dualChain_single (N : ℕ) (y : ChainPoint N) (k : Fin N) :
    fderiv ℝ (dualChain N) y (Pi.single k (1 : ℝ)) = dualGradient N y k := by
  have hF := (differentiableAt_dualChain N y).hasFDerivAt
  have hy : y = Function.update y k (y k) := by
    funext i
    by_cases hi : i = k
    · subst i
      simp
    · simp [hi]
  have hline := hF.comp_hasDerivAt_of_eq (y k) (hasDerivAt_update y k (y k)) hy
  have hline' : HasDerivAt
      (fun t : ℝ ↦ dualChain N (Function.update y k t))
      (fderiv ℝ (dualChain N) y (Pi.single k (1 : ℝ))) (y k) := by
    simpa only [Function.comp_def] using hline
  exact hline'.unique (hasDerivAt_dualChain_update N y k)

private theorem pi_eq_sum_single {N : ℕ} (v : ChainPoint N) :
    v = ∑ k : Fin N, v k • Pi.single k (1 : ℝ) := by
  funext i
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji.symm]

private theorem fderiv_dualChain_eq_finiteDotProductCLM (N : ℕ) (y : ChainPoint N) :
    fderiv ℝ (dualChain N) y = finiteDotProductCLM (dualGradient N y) := by
  apply ContinuousLinearMap.ext
  intro v
  calc
    fderiv ℝ (dualChain N) y v =
        fderiv ℝ (dualChain N) y
          (∑ k : Fin N, v k • Pi.single k (1 : ℝ)) := by
            rw [← pi_eq_sum_single v]
    _ = ∑ k : Fin N, v k * dualGradient N y k := by
          simp [fderiv_dualChain_single, smul_eq_mul]
    _ = finiteDotProductCLM (dualGradient N y) v := by
          rw [finiteDotProductCLM_apply]
          apply Finset.sum_congr rfl
          intro k _
          ring

/-- The full Fréchet derivative of `dualChain` is the finite dot product
with the explicit field from equation (7). -/
theorem hasFDerivAt_dualChain (N : ℕ) (y : ChainPoint N) :
    HasFDerivAt (dualChain N) (finiteDotProductCLM (dualGradient N y)) y :=
  (differentiableAt_dualChain N y).hasFDerivAt.congr_fderiv
    (fderiv_dualChain_eq_finiteDotProductCLM N y)

private theorem differentiableAt_chainCoord (N j : ℕ) (y : ChainPoint N) :
    DifferentiableAt ℝ (fun z : ChainPoint N ↦ chainCoord z j) y := by
  unfold chainCoord
  split_ifs with hj
  · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N ↦ ℝ)
      (⟨j, hj⟩ : Fin N)).differentiableAt
  · fun_prop

private theorem differentiableAt_coupledDual (N : ℕ) (α : ℝ) (y : ChainPoint N) :
    DifferentiableAt ℝ (coupledDual N α) y := by
  have hcoord := differentiableAt_chainCoord N (N - 1) y
  have hq : DifferentiableAt ℝ
      (fun z : ChainPoint N ↦ q (chainCoord z (N - 1))) y := by
    simpa only [Function.comp_def] using
      (differentiable_q (chainCoord y (N - 1))).comp y hcoord
  have hdual := differentiableAt_dualChain N y
  unfold coupledDual
  fun_prop

private theorem fderiv_coupledDual_single (N : ℕ) (α : ℝ)
    (y : ChainPoint N) (k : Fin N) :
    fderiv ℝ (coupledDual N α) y (Pi.single k (1 : ℝ)) =
      coupledGradient N α y k := by
  have hF := (differentiableAt_coupledDual N α y).hasFDerivAt
  have hy : y = Function.update y k (y k) := by
    funext i
    by_cases hi : i = k
    · subst i
      simp
    · simp [hi]
  have hline := hF.comp_hasDerivAt_of_eq (y k) (hasDerivAt_update y k (y k)) hy
  have hline' : HasDerivAt
      (fun t : ℝ ↦ coupledDual N α (Function.update y k t))
      (fderiv ℝ (coupledDual N α) y (Pi.single k (1 : ℝ))) (y k) := by
    simpa only [Function.comp_def] using hline
  exact hline'.unique (hasDerivAt_coupledDual_update N α y k)

private theorem fderiv_coupledDual_eq_finiteDotProductCLM (N : ℕ) (α : ℝ)
    (y : ChainPoint N) :
    fderiv ℝ (coupledDual N α) y = finiteDotProductCLM (coupledGradient N α y) := by
  apply ContinuousLinearMap.ext
  intro v
  calc
    fderiv ℝ (coupledDual N α) y v =
        fderiv ℝ (coupledDual N α) y
          (∑ k : Fin N, v k • Pi.single k (1 : ℝ)) := by
            rw [← pi_eq_sum_single v]
    _ = ∑ k : Fin N, v k * coupledGradient N α y k := by
          simp [fderiv_coupledDual_single, smul_eq_mul]
    _ = finiteDotProductCLM (coupledGradient N α y) v := by
          rw [finiteDotProductCLM_apply]
          apply Finset.sum_congr rfl
          intro k _
          ring

/-- The full Fréchet derivative of `coupledDual` is the finite dot product
with the explicit field used in Lemma 4.3. -/
theorem hasFDerivAt_coupledDual (N : ℕ) (α : ℝ) (y : ChainPoint N) :
    HasFDerivAt (coupledDual N α)
      (finiteDotProductCLM (coupledGradient N α y)) y :=
  (differentiableAt_coupledDual N α y).hasFDerivAt.congr_fderiv
    (fderiv_coupledDual_eq_finiteDotProductCLM N α y)

end

end NCPLRevised
