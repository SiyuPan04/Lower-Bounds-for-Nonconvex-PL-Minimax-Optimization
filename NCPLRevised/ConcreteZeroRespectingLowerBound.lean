/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.ConcreteHardInstance
import NCPLRevised.ConcreteSaddleZeroChain
import NCPLRevised.ScaledZeroChain
import NCPLRevised.ConditionalLowerBound
import NCPLRevised.RevisedConstants

/-!
# The concrete zero-respecting lower bound

This file performs the function-level rescaling in the proof of Theorem 3.1
and discharges the zero-chain and terminal-gradient hypotheses of
`conditional_zero_respecting_lower_bound` with the concrete hard instance.

The normalized constants are the ones proved for the construction:
`mu0 = 1 / 640`, `g0 = 1`, and `Delta0 = 12`.  The normalized smoothness
constant `ell0` remains a parameter here, so the assembly-level smoothness
bound can be supplied independently without entering the information-theoretic
argument.
-/

namespace NCPLRevised

noncomputable section

/-! ## Concrete paper parameters and scaled functions -/

/-- The inner-chain length selected in the proof of Theorem 3.1. -/
abbrev concretePaperN (ell0 kappa : ℝ) : ℕ :=
  paperN ell0 revisedMu0 kappa

/-- The outer-chain length selected in the proof of Theorem 3.1. -/
abbrev concretePaperM (ell ell0 Delta eps : ℝ) : ℕ :=
  paperM ell ell0 Delta revisedDelta0 revisedG0 eps

/-- The spatial scale from the paper, specialized to `g0 = 1`. -/
abbrev concretePaperLambda (ell ell0 eps : ℝ) : ℝ :=
  paperLambda ell ell0 revisedG0 eps

/-- The amplitude scale `ell * lambda^2 / ell0`. -/
def concretePaperAmplitude (ell ell0 eps : ℝ) : ℝ :=
  ell * concretePaperLambda ell ell0 eps ^ 2 / ell0

/-- The paper-scaled concrete saddle objective. -/
def concreteScaledBarF (ell ell0 Delta eps kappa : ℝ)
    (x : EVec (concretePaperM ell ell0 Delta eps))
    (y : EVec (concretePaperM ell ell0 Delta eps *
      concretePaperN ell0 kappa)) : ℝ :=
  scaledObjectiveGeneral (concretePaperAmplitude ell ell0 eps)
    (concretePaperLambda ell ell0 eps)
    (barF (concretePaperM ell ell0 Delta eps)
      (concretePaperN ell0 kappa)) x y

/-- The attained value of the scaled concrete saddle objective. -/
def concreteScaledBarPhi (ell ell0 Delta eps : ℝ)
    (x : EVec (concretePaperM ell ell0 Delta eps)) : ℝ :=
  concretePaperAmplitude ell ell0 eps *
    barPhi (concretePaperM ell ell0 Delta eps)
      (scaleEVec (concretePaperLambda ell ell0 eps) x)

/-- The displayed value gradient from the paper's scaling identity. -/
def concreteScaledBarPhiGradient (ell ell0 Delta eps : ℝ)
    (x : EVec (concretePaperM ell ell0 Delta eps)) :
    EVec (concretePaperM ell ell0 Delta eps) :=
  fun i ↦ ell * concretePaperLambda ell ell0 eps / ell0 *
    carmonGradient (concretePaperM ell ell0 Delta eps)
      (scaleEVec (concretePaperLambda ell ell0 eps) x) i

/-- Squared Euclidean norm of the actual scaled value gradient. -/
def concreteScaledBarPhiGradientSq (ell ell0 Delta eps : ℝ)
    (x : EVec (concretePaperM ell ell0 Delta eps)) : ℝ :=
  euclideanSq (concreteScaledBarPhiGradient ell ell0 Delta eps x)

/-- The displayed dual gradient after paper scaling. -/
def concreteScaledBarDualGradient (ell ell0 Delta eps kappa : ℝ)
    (x : EVec (concretePaperM ell ell0 Delta eps))
    (y : EVec (concretePaperM ell ell0 Delta eps *
      concretePaperN ell0 kappa)) :
    EVec (concretePaperM ell ell0 Delta eps *
      concretePaperN ell0 kappa) :=
  scaledGradientYGeneral (concretePaperAmplitude ell ell0 eps)
    (concretePaperLambda ell ell0 eps)
    (barDualGradient (concretePaperM ell ell0 Delta eps)
      (concretePaperN ell0 kappa)) x y

/-- Squared Euclidean norm of the scaled concrete dual gradient. -/
def concreteScaledBarDualGradientSq (ell ell0 Delta eps kappa : ℝ)
    (x : EVec (concretePaperM ell ell0 Delta eps))
    (y : EVec (concretePaperM ell ell0 Delta eps *
      concretePaperN ell0 kappa)) : ℝ :=
  euclideanSq
    (concreteScaledBarDualGradient ell ell0 Delta eps kappa x y)

/-- The scaled saddle-gradient field in the paper's interleaved order. -/
def concreteScaledOrderedSaddleField
    (ell ell0 Delta eps kappa : ℝ) :
    EVec (concretePaperM ell ell0 Delta eps *
      (concretePaperN ell0 kappa + 1)) →
    EVec (concretePaperM ell ell0 Delta eps *
      (concretePaperN ell0 kappa + 1)) :=
  scaledJointField (concretePaperAmplitude ell ell0 eps)
    (concretePaperLambda ell ell0 eps)
    (concreteOrderedSaddleGradient
      (concretePaperM ell ell0 Delta eps)
      (concretePaperN ell0 kappa))

/-! ## Exact envelope and value-gradient calculus -/

theorem concretePaperAmplitude_nonneg {ell ell0 eps : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) :
    0 ≤ concretePaperAmplitude ell ell0 eps := by
  unfold concretePaperAmplitude
  positivity

theorem concretePaperAmplitude_div_lambda
    {ell ell0 eps : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (heps : 0 < eps) :
    concretePaperAmplitude ell ell0 eps /
        concretePaperLambda ell ell0 eps =
      ell * concretePaperLambda ell ell0 eps / ell0 := by
  have hlambda : concretePaperLambda ell ell0 eps ≠ 0 :=
    (paperLambda_pos hell hell0 (by norm_num [revisedG0]) heps).ne'
  unfold concretePaperAmplitude
  field_simp [hlambda, hell0.ne']

/-- The scaled value is a finite attained maximum, with an explicit witness. -/
theorem concreteScaledBarF_envelope
    {ell ell0 Delta eps kappa : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (heps : 0 < eps)
    (hN : 2 ≤ concretePaperN ell0 kappa)
    (x : EVec (concretePaperM ell ell0 Delta eps)) :
    (∀ y, concreteScaledBarF ell ell0 Delta eps kappa x y ≤
      concreteScaledBarPhi ell ell0 Delta eps x) ∧
    ∃ y, concreteScaledBarF ell ell0 Delta eps kappa x y =
      concreteScaledBarPhi ell ell0 Delta eps x := by
  let M := concretePaperM ell ell0 Delta eps
  let N := concretePaperN ell0 kappa
  let lambda := concretePaperLambda ell ell0 eps
  let a := concretePaperAmplitude ell ell0 eps
  have hlambda : concretePaperLambda ell ell0 eps ≠ 0 :=
    (paperLambda_pos hell hell0 (by norm_num [revisedG0]) heps).ne'
  have hbaseUpper : ∀ u : EVec M, ∀ v : EVec (M * N),
      barF M N u v ≤ barPhi M u := fun u v ↦ (barF_envelope hN u).1 v
  have hbaseWitness : ∀ u : EVec M, ∃ v : EVec (M * N),
      barF M N u v = barPhi M u := fun u ↦
    ⟨barDualMaximizer M N u, (barF_envelope hN u).2⟩
  have h := scaledObjectiveGeneral_max hbaseUpper hbaseWitness
    (a := a) (lambda := lambda)
    (concretePaperAmplitude_nonneg (eps := eps) hell hell0) hlambda x
  constructor
  · intro y
    change scaledObjectiveGeneral a lambda (barF M N) x y ≤
      a * barPhi M (scaleEVec lambda x)
    exact h.1 y
  · obtain ⟨y, hy⟩ := h.2
    refine ⟨y, ?_⟩
    change scaledObjectiveGeneral a lambda (barF M N) x y =
      a * barPhi M (scaleEVec lambda x)
    exact hy

/-- Set-theoretic form of the scaled envelope identity. -/
theorem concreteScaledBarF_isGreatest
    {ell ell0 Delta eps kappa : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (heps : 0 < eps)
    (hN : 2 ≤ concretePaperN ell0 kappa)
    (x : EVec (concretePaperM ell ell0 Delta eps)) :
    IsGreatest (Set.range
      (concreteScaledBarF ell ell0 Delta eps kappa x))
      (concreteScaledBarPhi ell ell0 Delta eps x) := by
  obtain ⟨hupper, y, hy⟩ :=
    concreteScaledBarF_envelope hell hell0 heps hN x
  exact ⟨⟨y, hy⟩, by rintro _ ⟨v, rfl⟩; exact hupper v⟩

/-- The displayed vector is the actual Fréchet gradient of the scaled value. -/
theorem concreteScaledBarPhi_hasFDerivAt
    {ell ell0 Delta eps : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (heps : 0 < eps)
    (x : EVec (concretePaperM ell ell0 Delta eps)) :
    HasCarmonFDerivAt
      (concreteScaledBarPhi ell ell0 Delta eps)
      (evecDot (concreteScaledBarPhiGradient ell ell0 Delta eps x)) x := by
  let M := concretePaperM ell ell0 Delta eps
  let lambda := concretePaperLambda ell ell0 eps
  let a := concretePaperAmplitude ell ell0 eps
  have hlambda : lambda ≠ 0 :=
    (paperLambda_pos hell hell0 (by norm_num [revisedG0]) heps).ne'
  have hbase : HasFDerivAt (barPhi M)
      (finiteDotProductCLM
        (carmonGradient M (scaleEVec lambda x)))
      (scaleEVec lambda x) := by
    have hc := hasEVecFDerivAt_carmonF_gradient M (scaleEVec lambda x)
    change HasFDerivAt (barPhi M)
      (evecDot (carmonGradient M (scaleEVec lambda x)))
      (scaleEVec lambda x) at hc
    convert hc using 1
    ext h
    simp only [finiteDotProductCLM_apply, evecDot_apply]
  have hs := scaledValue_comp_hasFDerivAt
    (a := a) hlambda hbase
  change HasFDerivAt (concreteScaledBarPhi ell ell0 Delta eps)
    (evecDot (concreteScaledBarPhiGradient ell ell0 Delta eps x)) x
  convert hs using 1
  · rfl
  · ext h
    simp only [finiteDotProductCLM_apply, evecDot_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [concretePaperAmplitude_div_lambda hell hell0 heps]
    rfl

/-- Exact squared-norm form of the scaled value-gradient identity. -/
theorem concreteScaledBarPhiGradientSq_eq
    (ell ell0 Delta eps : ℝ)
    (x : EVec (concretePaperM ell ell0 Delta eps)) :
    concreteScaledBarPhiGradientSq ell ell0 Delta eps x =
      (ell * concretePaperLambda ell ell0 eps / ell0) ^ 2 *
        vecSq
          (carmonGradient (concretePaperM ell ell0 Delta eps)
            (scaleEVec (concretePaperLambda ell ell0 eps) x)) := by
  unfold concreteScaledBarPhiGradientSq concreteScaledBarPhiGradient
  rw [euclideanSq_const_mul]
  rfl

/-- The exact paper-scaled dual PL inequality for the concrete objective. -/
theorem concreteScaledBarF_dual_PL
    {ell ell0 Delta eps kappa : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (heps : 0 < eps)
    (hN : 2 ≤ concretePaperN ell0 kappa)
    (x : EVec (concretePaperM ell ell0 Delta eps))
    (y : EVec (concretePaperM ell ell0 Delta eps *
      concretePaperN ell0 kappa)) :
    (1 / 2 : ℝ) *
        concreteScaledBarDualGradientSq ell ell0 Delta eps kappa x y ≥
      (ell * revisedMu0 /
        (ell0 * (concretePaperN ell0 kappa : ℝ))) *
        (concreteScaledBarPhi ell ell0 Delta eps x -
          concreteScaledBarF ell ell0 Delta eps kappa x y) := by
  let M := concretePaperM ell ell0 Delta eps
  let N := concretePaperN ell0 kappa
  let lambda := concretePaperLambda ell ell0 eps
  let a := concretePaperAmplitude ell ell0 eps
  have hlambda : lambda ≠ 0 :=
    (paperLambda_pos hell hell0 (by norm_num [revisedG0]) heps).ne'
  have hNpos : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hbase : ∀ u : EVec M, ∀ v : EVec (M * N),
      (1 / 2 : ℝ) * euclideanSq (barDualGradient M N u v) ≥
        (revisedMu0 / (N : ℝ)) *
          (barPhi M u - barF M N u v) := by
    intro u v
    have h := barF_dual_PL hN u v
    change (1 / 2 : ℝ) * euclideanSq (barDualGradient M N u v) ≥
      (1 / (640 * (N : ℝ))) * (barPhi M u - barF M N u v) at h
    have hmu : revisedMu0 / (N : ℝ) = 1 / (640 * (N : ℝ)) := by
      norm_num [revisedMu0]
      field_simp [hNpos]
    rw [hmu]
    exact h
  have hs := scaledGradientYGeneral_PL hbase
    (a := a) (lambda := lambda) hlambda x y
  have hcoeff :
      a * (revisedMu0 / (N : ℝ)) / lambda ^ 2 =
        ell * revisedMu0 / (ell0 * (N : ℝ)) := by
    dsimp [a]
    unfold concretePaperAmplitude
    field_simp [hlambda, hell0.ne', hNpos]
    ring
  change (1 / 2 : ℝ) *
      euclideanSq (scaledGradientYGeneral a lambda
        (barDualGradient M N) x y) ≥
    (ell * revisedMu0 / (ell0 * (N : ℝ))) *
      (a * barPhi M (scaleEVec lambda x) -
        scaledObjectiveGeneral a lambda (barF M N) x y)
  rw [← hcoeff]
  exact hs

/-! ## The scaled zero-chain and its concrete terminal obstruction -/

/-- Scaling the concrete Proposition 5.2 field preserves its zero-chain
property; no field hypothesis remains. -/
theorem concreteScaledOrderedSaddleField_isZeroChain
    {ell ell0 Delta eps kappa : ℝ}
    (hN : 2 ≤ concretePaperN ell0 kappa) :
    IsFirstOrderSaddleZeroChain
      (concreteScaledOrderedSaddleField ell ell0 Delta eps kappa) := by
  exact scaledJointField_isZeroChain
    (proposition5_2_concrete
      (concretePaperM ell ell0 Delta eps)
      (concretePaperN ell0 kappa) hN)
    (concretePaperAmplitude ell ell0 eps)
    (concretePaperLambda ell ell0 eps)

/-- The last ordered joint coordinate controls the actual squared norm of
the scaled envelope gradient.  This is the scaled, concrete form of (C3). -/
theorem concreteScaled_terminal_gradient_lower
    {ell ell0 Delta eps kappa : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (hregime : eps ^ 2 ≤
      paperC1 ell0 revisedDelta0 revisedG0 * ell * Delta)
    (z : EVec (concretePaperM ell ell0 Delta eps *
      (concretePaperN ell0 kappa + 1)))
    (hz : z
      ⟨concretePaperM ell ell0 Delta eps *
          (concretePaperN ell0 kappa + 1) - 1,
        by
          have hMtwo : 2 ≤ concretePaperM ell ell0 Delta eps :=
            paperM_two_le hell hell0 hDelta
            revisedDelta0_pos (by norm_num [revisedG0]) heps hregime
          have hMpos : 0 < concretePaperM ell ell0 Delta eps := by omega
          have hprod : 0 < concretePaperM ell ell0 Delta eps *
              (concretePaperN ell0 kappa + 1) :=
            Nat.mul_pos hMpos (Nat.succ_pos _)
          exact Nat.sub_lt hprod (by omega)⟩ = 0) :
    (ell * concretePaperLambda ell ell0 eps / ell0 * revisedG0) ^ 2 ≤
      concreteScaledBarPhiGradientSq ell ell0 Delta eps
        (orderedPrimal z) := by
  let M := concretePaperM ell ell0 Delta eps
  let N := concretePaperN ell0 kappa
  let lambda := concretePaperLambda ell ell0 eps
  let c := ell * lambda / ell0
  have hMtwo : 2 ≤ M := paperM_two_le hell hell0 hDelta
    revisedDelta0_pos (by norm_num [revisedG0]) heps hregime
  have hM : 0 < M := by omega
  have hlast :
      orderedPrimal z (carmonLastIndex M hM) = 0 := by
    have hordered := orderedPrimal_last_eq_joint_last (N := N) hM z
    exact hordered.trans hz
  have hscaledLast :
      scaleEVec lambda (orderedPrimal z) (carmonLastIndex M hM) = 0 := by
    change orderedPrimal z (carmonLastIndex M hM) / lambda = 0
    rw [hlast]
    exact zero_div lambda
  have hbase : 1 ≤
      vecSq (carmonGradient M (scaleEVec lambda (orderedPrimal z))) :=
    (proposition5_3_concrete M N hM).2.1 _ hscaledLast
  have hmul := mul_le_mul_of_nonneg_left hbase (sq_nonneg c)
  rw [concreteScaledBarPhiGradientSq_eq]
  change (c * revisedG0) ^ 2 ≤
    c ^ 2 * vecSq (carmonGradient M
      (scaleEVec lambda (orderedPrimal z)))
  simpa [revisedG0] using hmul

/-! ## The information-theoretic conclusion -/

/-- Concrete zero-respecting part of Theorem 3.1.

For every transcript that is zero-respecting for the actual scaled ordered
saddle field, every query before the paper's real lower-bound threshold has
value-gradient norm strictly larger than `eps`.  The zero-chain and terminal
certificates are fully instantiated here. -/
theorem concrete_zero_respecting_lower_bound
    {ell ell0 Delta eps kappa : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (hkappa : paperC0 ell0 revisedMu0 ≤ kappa)
    (hregime : eps ^ 2 ≤
      paperC1 ell0 revisedDelta0 revisedG0 * ell * Delta)
    (query : ℕ → EVec
      (concretePaperM ell ell0 Delta eps *
        (concretePaperN ell0 kappa + 1)))
    (hquery : QueriesAreZeroRespecting
      (concreteScaledOrderedSaddleField ell ell0 Delta eps kappa) query)
    {t : ℕ}
    (ht : (t : ℝ) <
      paperC2 ell0 revisedMu0 revisedDelta0 revisedG0 *
        kappa * ell * Delta / eps ^ 2) :
    ¬concreteScaledBarPhiGradientSq ell ell0 Delta eps
        (orderedPrimal (query t)) ≤ eps ^ 2 := by
  have hN : 2 ≤ concretePaperN ell0 kappa :=
    paperN_two_le hell0 revisedMu0_pos hkappa
  apply conditional_zero_respecting_lower_bound
    (ell := ell) (ell0 := ell0) (mu0 := revisedMu0)
    (Delta := Delta) (Delta0 := revisedDelta0)
    (g0 := revisedG0) (eps := eps) (kappa := kappa)
    hell hell0 revisedMu0_pos hDelta revisedDelta0_pos
    (by norm_num [revisedG0]) heps hkappa hregime
    (concreteScaledOrderedSaddleField ell ell0 Delta eps kappa)
    query (concreteScaledBarPhiGradientSq ell ell0 Delta eps)
    (concreteScaledOrderedSaddleField_isZeroChain hN) hquery
  · intro z hz
    exact concreteScaled_terminal_gradient_lower hell hell0 hDelta heps
      hregime z hz
  · exact ht

end

end NCPLRevised
