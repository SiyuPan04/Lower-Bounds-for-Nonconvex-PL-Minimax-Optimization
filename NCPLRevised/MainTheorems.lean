/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.AssembledSmoothness
import NCPLRevised.ConcreteZeroRespectingLowerBound
import NCPLRevised.DeterministicTransfer
import NCPLRevised.OrderedOracleBridge

/-!
# Theorems 3.1 and 3.2

This module closes the analytic hard-instance certificates, the scaling
argument, the ordered zero-chain argument, and the finite-horizon transfer
into the two main lower bounds.  The deterministic theorem keeps the exact
statement of the manuscript's unproved Lemma 2.2 visible as its sole
non-derived hypothesis.
-/

namespace NCPLRevised

noncomputable section

/-! ## The real threshold and its natural finite horizon -/

/-- The real-valued lower-bound threshold occurring in Theorems 3.1--3.2. -/
def concreteLowerBoundThreshold
    (ell ell0 Delta eps kappa : ℝ) : ℝ :=
  paperC2 ell0 revisedMu0 revisedDelta0 revisedG0 *
    kappa * ell * Delta / eps ^ 2

/-- The first natural number not smaller than the real lower-bound threshold. -/
def concreteLowerBoundHorizon
    (ell ell0 Delta eps kappa : ℝ) : ℕ :=
  ⌈concreteLowerBoundThreshold ell ell0 Delta eps kappa⌉₊

theorem concreteLowerBoundThreshold_le_horizon
    (ell ell0 Delta eps kappa : ℝ) :
    concreteLowerBoundThreshold ell ell0 Delta eps kappa ≤
      (concreteLowerBoundHorizon ell ell0 Delta eps kappa : ℕ) := by
  exact Nat.le_ceil _

theorem lt_concreteLowerBoundHorizon_iff_cast_lt_threshold
    {ell ell0 Delta eps kappa : ℝ} {t : ℕ} :
    t < concreteLowerBoundHorizon ell ell0 Delta eps kappa ↔
      (t : ℝ) < concreteLowerBoundThreshold ell ell0 Delta eps kappa := by
  exact Nat.lt_ceil

theorem cast_lt_concreteLowerBoundThreshold_of_lt_horizon
    {ell ell0 Delta eps kappa : ℝ} {t : ℕ}
    (ht : t < concreteLowerBoundHorizon ell ell0 Delta eps kappa) :
    (t : ℝ) < concreteLowerBoundThreshold ell ell0 Delta eps kappa := by
  exact lt_concreteLowerBoundHorizon_iff_cast_lt_threshold.mp ht

/-! ## Coordinate-order identities used by the oracle bridge -/

theorem assembleOrdered_orderedProjections {M N : ℕ}
    (z : EVec (M * (N + 1))) :
    assembleOrdered (orderedPrimal z) (orderedDual z) = z := by
  funext r
  let ij := finProdFinEquiv.symm r
  have hr : finProdFinEquiv ij = r := finProdFinEquiv.apply_symm_apply r
  rcases ij with ⟨i, j⟩
  by_cases hj : j.1 < N
  · let jd : Fin N := ⟨j.1, hj⟩
    have hjcast : jd.castSucc = j := Fin.ext rfl
    rw [← hr, ← hjcast, assembleOrdered_dual_apply]
    simp [orderedDual, jd]
  · have hjlast : j = Fin.last N := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    rw [← hr, hjlast, assembleOrdered_primal_apply]
    rfl

theorem orderedPrimal_scaleEVec {M N : ℕ} (lambda : ℝ)
    (z : EVec (M * (N + 1))) :
    orderedPrimal (scaleEVec lambda z) =
      scaleEVec lambda (orderedPrimal z) := by
  rfl

theorem orderedDual_scaleEVec {M N : ℕ} (lambda : ℝ)
    (z : EVec (M * (N + 1))) :
    orderedDual (scaleEVec lambda z) =
      scaleEVec lambda (orderedDual z) := by
  funext k
  simp [orderedDual, scaleEVec]

theorem assembleOrdered_const_mul {M N : ℕ} (c : ℝ)
    (x : EVec M) (y : EVec (M * N)) :
    assembleOrdered (fun i ↦ c * x i) (fun j ↦ c * y j) =
      fun r ↦ c * assembleOrdered x y r := by
  funext r
  let ij := finProdFinEquiv.symm r
  have hr : finProdFinEquiv ij = r := finProdFinEquiv.apply_symm_apply r
  rcases ij with ⟨i, j⟩
  by_cases hj : j.1 < N
  · let jd : Fin N := ⟨j.1, hj⟩
    have hjcast : jd.castSucc = j := Fin.ext rfl
    rw [← hr, ← hjcast, assembleOrdered_dual_apply,
      assembleOrdered_dual_apply]
  · have hjlast : j = Fin.last N := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    rw [← hr, hjlast, assembleOrdered_primal_apply,
      assembleOrdered_primal_apply]

/-! ## The exact scaled envelope and initial gap -/

theorem rotationEnvelope_concreteScaledBarF_eq
    {ell ell0 Delta eps kappa : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (heps : 0 < eps)
    (hN : 2 ≤ concretePaperN ell0 kappa)
    (x : EVec (concretePaperM ell ell0 Delta eps)) :
    RotationEnvelope (concreteScaledBarF ell ell0 Delta eps kappa) x =
      concreteScaledBarPhi ell ell0 Delta eps x := by
  unfold RotationEnvelope
  exact (concreteScaledBarF_isGreatest hell hell0 heps hN x).csSup_eq

theorem range_concreteScaledBarPhi
    {ell ell0 Delta eps : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (heps : 0 < eps) :
    Set.range (concreteScaledBarPhi ell ell0 Delta eps) =
      Set.range (fun u : EVec (concretePaperM ell ell0 Delta eps) ↦
        concretePaperAmplitude ell ell0 eps *
          barPhi (concretePaperM ell ell0 Delta eps) u) := by
  let M := concretePaperM ell ell0 Delta eps
  let lambda := concretePaperLambda ell ell0 eps
  let a := concretePaperAmplitude ell ell0 eps
  have hlambda : lambda ≠ 0 :=
    (paperLambda_pos hell hell0 (by norm_num [revisedG0]) heps).ne'
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨scaleEVec lambda x, rfl⟩
  · rintro ⟨u, rfl⟩
    refine ⟨unscaleEVec lambda u, ?_⟩
    change a * barPhi M (scaleEVec lambda (unscaleEVec lambda u)) =
      a * barPhi M u
    rw [scaleEVec_unscaleEVec hlambda]

theorem sInf_range_concreteScaledBarPhi
    {ell ell0 Delta eps : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (heps : 0 < eps) :
    sInf (Set.range (concreteScaledBarPhi ell ell0 Delta eps)) =
      concretePaperAmplitude ell ell0 eps *
        sInf (Set.range
          (barPhi (concretePaperM ell ell0 Delta eps))) := by
  rw [range_concreteScaledBarPhi hell hell0 heps]
  have ha : 0 ≤ concretePaperAmplitude ell ell0 eps :=
    concretePaperAmplitude_nonneg (eps := eps) hell hell0
  simpa only [iInf, smul_eq_mul] using
    (Real.smul_iInf_of_nonneg ha
      (barPhi (concretePaperM ell ell0 Delta eps))).symm

theorem concreteScaledBarPhi_range_bddBelow
    {ell ell0 Delta eps : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) :
    BddBelow (Set.range (concreteScaledBarPhi ell ell0 Delta eps)) := by
  let M := concretePaperM ell ell0 Delta eps
  let a := concretePaperAmplitude ell ell0 eps
  obtain ⟨b, hb⟩ := carmonF_range_bddBelow M
  refine ⟨a * b, ?_⟩
  rintro _ ⟨x, rfl⟩
  apply mul_le_mul_of_nonneg_left _
    (concretePaperAmplitude_nonneg (eps := eps) hell hell0)
  exact hb ⟨scaleEVec (concretePaperLambda ell ell0 eps) x, rfl⟩

theorem concreteScaledBarPhi_initial_gap_le
    {ell ell0 Delta eps : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0)
    (hDelta : 0 < Delta) (heps : 0 < eps) :
    concreteScaledBarPhi ell ell0 Delta eps 0 -
        sInf (Set.range (concreteScaledBarPhi ell ell0 Delta eps)) ≤
      Delta := by
  let M := concretePaperM ell ell0 Delta eps
  let lambda := concretePaperLambda ell ell0 eps
  let a := concretePaperAmplitude ell ell0 eps
  have hbase :
      barPhi M 0 - sInf (Set.range (barPhi M)) ≤
        revisedDelta0 * (M : ℝ) := by
    change carmonF M 0 - sInf (Set.range (carmonF M)) ≤ 12 * (M : ℝ)
    exact carmon_initial_gap_twelve M
  have ha : 0 ≤ a := concretePaperAmplitude_nonneg (eps := eps) hell hell0
  have hmul := mul_le_mul_of_nonneg_left hbase ha
  have hscaled := scaled_gap_le_target
    (Delta0 := revisedDelta0) (g0 := revisedG0) (eps := eps)
    hell hell0 hDelta.le revisedDelta0_pos
      (by norm_num [revisedG0]) heps
  rw [sInf_range_concreteScaledBarPhi hell hell0 heps]
  change a * barPhi M (scaleEVec lambda 0) -
      a * sInf (Set.range (barPhi M)) ≤ Delta
  rw [scaleEVec_zero]
  calc
    a * barPhi M 0 - a * sInf (Set.range (barPhi M)) =
        a * (barPhi M 0 - sInf (Set.range (barPhi M))) := by ring
    _ ≤ a * (revisedDelta0 * (M : ℝ)) := hmul
    _ ≤ Delta := by
      simpa [a, M, concretePaperAmplitude, mul_assoc] using hscaled

/-! ## A certified scaled saddle oracle -/

/-- The primal component of the actual gradient after the paper's scaling. -/
def concreteScaledBarPrimalGradient
    (ell ell0 Delta eps kappa : ℝ)
    (x : EVec (concretePaperM ell ell0 Delta eps))
    (y : EVec (concretePaperM ell ell0 Delta eps *
      concretePaperN ell0 kappa)) :
    EVec (concretePaperM ell ell0 Delta eps) :=
  scaledGradientXGeneral (concretePaperAmplitude ell ell0 eps)
    (concretePaperLambda ell ell0 eps)
    (barPrimalGradient (concretePaperM ell ell0 Delta eps)
      (concretePaperN ell0 kappa)) x y

/-- The exact scaled objective, its genuine joint gradient, its attained
envelope, and the genuine envelope gradient packaged as one oracle. -/
def concreteScaledSmoothSaddle
    (ell ell0 Delta eps kappa : ℝ)
    (hell : 0 < ell) (hell0 : 0 < ell0) (heps : 0 < eps)
    (hN : 2 ≤ concretePaperN ell0 kappa) :
    SmoothSaddle (concretePaperM ell ell0 Delta eps)
      (concretePaperM ell ell0 Delta eps * concretePaperN ell0 kappa) where
  F := concreteScaledBarF ell ell0 Delta eps kappa
  gradX := concreteScaledBarPrimalGradient ell ell0 Delta eps kappa
  gradY := concreteScaledBarDualGradient ell ell0 Delta eps kappa
  gradient_representation := by
    have hlambda : concretePaperLambda ell ell0 eps ≠ 0 :=
      (paperLambda_pos hell hell0 (by norm_num [revisedG0]) heps).ne'
    change RepresentsRotatableGradient
      (scaledObjectiveGeneral (concretePaperAmplitude ell ell0 eps)
        (concretePaperLambda ell ell0 eps)
        (barF (concretePaperM ell ell0 Delta eps)
          (concretePaperN ell0 kappa)))
      (scaledGradientXGeneral (concretePaperAmplitude ell ell0 eps)
        (concretePaperLambda ell ell0 eps)
        (barPrimalGradient (concretePaperM ell ell0 Delta eps)
          (concretePaperN ell0 kappa)))
      (scaledGradientYGeneral (concretePaperAmplitude ell ell0 eps)
        (concretePaperLambda ell ell0 eps)
        (barDualGradient (concretePaperM ell ell0 Delta eps)
          (concretePaperN ell0 kappa)))
    exact scaledObjectiveGeneral_representsGradient
      (barF_representsGradient hN)
      (concretePaperAmplitude ell ell0 eps)
      (concretePaperLambda ell ell0 eps) hlambda
  maximum_attained := by
    intro x
    obtain ⟨hupper, y, hy⟩ :=
      concreteScaledBarF_envelope hell hell0 heps hN x
    refine ⟨y, ?_⟩
    intro v
    rw [hy]
    exact hupper v
  envelopeGradient := concreteScaledBarPhiGradient ell ell0 Delta eps
  envelope_hasFDerivAt := by
    intro x
    have hfun : RotationEnvelope
        (concreteScaledBarF ell ell0 Delta eps kappa) =
        concreteScaledBarPhi ell ell0 Delta eps := by
      funext u
      exact rotationEnvelope_concreteScaledBarF_eq hell hell0 heps hN u
    rw [hfun]
    have h := concreteScaledBarPhi_hasFDerivAt hell hell0 heps x
    unfold HasCarmonFDerivAt at h
    convert h using 1 <;> try rfl
    ext v
    simp only [finiteDotProductCLM_apply, evecDot_apply]

/-- Scaling a normalized jointly smooth concrete gradient by the manuscript's
amplitude and spatial scale gives exactly the requested target constant
`ell`.  This arithmetic helper is specialized to the proved normalized
smoothness certificate below. -/
theorem concreteScaledSmoothSaddle_isJointlySmooth_of_base
    {ell ell0 Delta eps kappa : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (heps : 0 < eps)
    (hbase : IsEuclideanJointlySmooth ell0
      (barPrimalGradient (concretePaperM ell ell0 Delta eps)
        (concretePaperN ell0 kappa))
      (barDualGradient (concretePaperM ell ell0 Delta eps)
        (concretePaperN ell0 kappa))) :
    IsEuclideanJointlySmooth ell
      (concreteScaledBarPrimalGradient ell ell0 Delta eps kappa)
      (concreteScaledBarDualGradient ell ell0 Delta eps kappa) := by
  have hlambda : concretePaperLambda ell ell0 eps ≠ 0 :=
    (paperLambda_pos hell hell0 (by norm_num [revisedG0]) heps).ne'
  have hsmooth := scaledGradientGeneral_isJointlySmooth hbase
    (concretePaperAmplitude ell ell0 eps)
    (concretePaperLambda ell ell0 eps) hlambda
  have hcoefficient :
      concretePaperAmplitude ell ell0 eps /
          concretePaperLambda ell ell0 eps ^ 2 * ell0 = ell := by
    unfold concretePaperAmplitude
    field_simp [hlambda, hell0.ne']
  unfold concreteScaledBarPrimalGradient concreteScaledBarDualGradient
  simpa only [hcoefficient] using hsmooth

/-- The ordered gradient of the certified oracle is definitionally the
scaled zero-chain field used in the concrete lower-bound theorem. -/
theorem orderedSaddleField_concreteScaledSmoothSaddle
    {ell ell0 Delta eps kappa : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (heps : 0 < eps)
    (hN : 2 ≤ concretePaperN ell0 kappa) :
    orderedSaddleField
        (concretePaperM ell ell0 Delta eps)
        (concretePaperN ell0 kappa)
        (concreteScaledSmoothSaddle ell ell0 Delta eps kappa
          hell hell0 heps hN) =
      concreteScaledOrderedSaddleField ell ell0 Delta eps kappa := by
  let M := concretePaperM ell ell0 Delta eps
  let N := concretePaperN ell0 kappa
  let a := concretePaperAmplitude ell ell0 eps
  let lambda := concretePaperLambda ell ell0 eps
  funext z
  have hscaledProjections :
      assembleOrdered
          (scaleEVec lambda (orderedPrimal z))
          (scaleEVec lambda (orderedDual z)) =
        scaleEVec lambda z := by
    rw [← orderedPrimal_scaleEVec, ← orderedDual_scaleEVec,
      assembleOrdered_orderedProjections]
  have hbase := assembleOrdered_barGradient_eq_concreteOrderedSaddleGradient
    M N (scaleEVec lambda (orderedPrimal z))
      (scaleEVec lambda (orderedDual z))
  rw [hscaledProjections] at hbase
  change
    assembleOrdered
      (scaledGradientXGeneral a lambda (barPrimalGradient M N)
        (orderedPrimal z) (orderedDual z))
      (scaledGradientYGeneral a lambda (barDualGradient M N)
        (orderedPrimal z) (orderedDual z)) =
    scaledJointField a lambda (concreteOrderedSaddleGradient M N) z
  rw [show
    assembleOrdered
        (scaledGradientXGeneral a lambda (barPrimalGradient M N)
          (orderedPrimal z) (orderedDual z))
        (scaledGradientYGeneral a lambda (barDualGradient M N)
          (orderedPrimal z) (orderedDual z)) =
      fun r ↦ a / lambda *
        assembleOrdered
          (barPrimalGradient M N
            (scaleEVec lambda (orderedPrimal z))
            (scaleEVec lambda (orderedDual z)))
          (barDualGradient M N
            (scaleEVec lambda (orderedPrimal z))
            (scaleEVec lambda (orderedDual z))) r by
      exact assembleOrdered_const_mul (a / lambda) _ _]
  unfold scaledJointField
  funext r
  rw [hbase]

/-- Every componentwise zero-respecting deterministic algorithm induces the
ordered transcript required by the concrete zero-chain theorem. -/
theorem concreteScaledSmoothSaddle_zeroRespecting_failure
    {ell ell0 Delta eps kappa : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (hkappa : paperC0 ell0 revisedMu0 ≤ kappa)
    (hregime : eps ^ 2 ≤
      paperC1 ell0 revisedDelta0 revisedG0 * ell * Delta)
    (Z : DeterministicSaddleAlgorithm) (hZ : Z.IsZeroRespecting)
    {t : ℕ}
    (ht : (t : ℝ) < concreteLowerBoundThreshold
      ell ell0 Delta eps kappa) :
    let hN : 2 ≤ concretePaperN ell0 kappa :=
      paperN_two_le hell0 revisedMu0_pos hkappa
    let f := concreteScaledSmoothSaddle ell ell0 Delta eps kappa
      hell hell0 heps hN
    ¬f.IsEpsilonStationary eps (Z.query f t).1 := by
  dsimp only
  let M := concretePaperM ell ell0 Delta eps
  let N := concretePaperN ell0 kappa
  let hN : 2 ≤ N := paperN_two_le hell0 revisedMu0_pos hkappa
  let f := concreteScaledSmoothSaddle ell ell0 Delta eps kappa
    hell hell0 heps hN
  have hordered : QueriesAreZeroRespecting
      (orderedSaddleField M N f)
      (orderedAlgorithmQuery M N Z f) :=
    zeroRespecting_orderedAlgorithmQuery Z hZ M N f
  have hfield : orderedSaddleField M N f =
      concreteScaledOrderedSaddleField ell ell0 Delta eps kappa := by
    exact orderedSaddleField_concreteScaledSmoothSaddle hell hell0 heps hN
  rw [hfield] at hordered
  have hbad := concrete_zero_respecting_lower_bound
    hell hell0 hDelta heps hkappa hregime
    (orderedAlgorithmQuery M N Z f) hordered ht
  simpa [f, M, N, SmoothSaddle.IsEpsilonStationary,
    concreteScaledSmoothSaddle, concreteScaledBarPhiGradientSq,
    orderedAlgorithmQuery] using hbad

/-! ## Class membership, apart from the now-concrete smoothness theorem -/

theorem concreteScaledSmoothSaddle_dualPL_at_mu
    {ell ell0 mu Delta eps : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (hmu : 0 < mu)
    (heps : 0 < eps)
    (hkappa : paperC0 ell0 revisedMu0 ≤ ell / mu)
    (x : EVec (concretePaperM ell ell0 Delta eps))
    (y : EVec (concretePaperM ell ell0 Delta eps *
      concretePaperN ell0 (ell / mu))) :
    let hN : 2 ≤ concretePaperN ell0 (ell / mu) :=
      paperN_two_le hell0 revisedMu0_pos hkappa
    let f := concreteScaledSmoothSaddle ell ell0 Delta eps (ell / mu)
      hell hell0 heps hN
    (1 / 2 : ℝ) * euclideanSq (f.gradY x y) ≥
      mu * (RotationEnvelope f.F x - f.F x y) := by
  dsimp only
  let N := concretePaperN ell0 (ell / mu)
  let hN : 2 ≤ N := paperN_two_le hell0 revisedMu0_pos hkappa
  let f := concreteScaledSmoothSaddle ell ell0 Delta eps (ell / mu)
    hell hell0 heps hN
  have hkappaPos : 0 < ell / mu := div_pos hell hmu
  have hcoefficient := scaled_dualPL_at_least_target
    hell hell0 revisedMu0_pos hkappaPos hkappa
  have hellDiv : ell / (ell / mu) = mu := by
    field_simp [hell.ne', hmu.ne']
  rw [hellDiv] at hcoefficient
  have henvelope := concreteScaledBarF_envelope
    hell hell0 heps hN x
  have hgap : 0 ≤
      concreteScaledBarPhi ell ell0 Delta eps x -
        concreteScaledBarF ell ell0 Delta eps (ell / mu) x y :=
    sub_nonneg.mpr (henvelope.1 y)
  have hmul := mul_le_mul_of_nonneg_right hcoefficient hgap
  have hraw := concreteScaledBarF_dual_PL
    hell hell0 heps hN x y
  change (1 / 2 : ℝ) * euclideanSq
      (concreteScaledBarDualGradient ell ell0 Delta eps (ell / mu) x y) ≥
    mu *
      (RotationEnvelope
          (concreteScaledBarF ell ell0 Delta eps (ell / mu)) x -
        concreteScaledBarF ell ell0 Delta eps (ell / mu) x y)
  rw [rotationEnvelope_concreteScaledBarF_eq hell hell0 heps hN]
  exact hmul.trans hraw

/-- Class membership obtained from the normalized smoothness certificate.
All other class fields are discharged by the concrete construction itself. -/
theorem concreteScaledSmoothSaddle_inClass_of_base
    {ell ell0 mu Delta eps : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (hmu : 0 < mu)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (hkappa : paperC0 ell0 revisedMu0 ≤ ell / mu)
    (hbase : IsEuclideanJointlySmooth ell0
      (barPrimalGradient (concretePaperM ell ell0 Delta eps)
        (concretePaperN ell0 (ell / mu)))
      (barDualGradient (concretePaperM ell ell0 Delta eps)
        (concretePaperN ell0 (ell / mu)))) :
    let hN : 2 ≤ concretePaperN ell0 (ell / mu) :=
      paperN_two_le hell0 revisedMu0_pos hkappa
    let f := concreteScaledSmoothSaddle ell ell0 Delta eps (ell / mu)
      hell hell0 heps hN
    f.InClass ell mu Delta := by
  dsimp only
  let hN : 2 ≤ concretePaperN ell0 (ell / mu) :=
    paperN_two_le hell0 revisedMu0_pos hkappa
  let f := concreteScaledSmoothSaddle ell ell0 Delta eps (ell / mu)
    hell hell0 heps hN
  have henvelope : RotationEnvelope f.F =
      concreteScaledBarPhi ell ell0 Delta eps := by
    funext x
    exact rotationEnvelope_concreteScaledBarF_eq hell hell0 heps hN x
  refine
    { L_nonneg := hell.le
      mu_nonneg := hmu.le
      Delta_nonneg := hDelta.le
      gradient_representation := f.gradient_representation
      jointly_smooth := ?_
      maximum_attained := f.maximum_attained
      maximization_PL := ?_
      envelope_bddBelow := ?_
      initial_gap := ?_ }
  · exact concreteScaledSmoothSaddle_isJointlySmooth_of_base
      hell hell0 heps hbase
  · intro x y
    exact concreteScaledSmoothSaddle_dualPL_at_mu
      hell hell0 hmu heps hkappa x y
  · rw [henvelope]
    exact concreteScaledBarPhi_range_bddBelow hell hell0
  · rw [henvelope]
    exact concreteScaledBarPhi_initial_gap_le hell hell0 hDelta heps

theorem concreteScaledSmoothSaddle_zeroRespecting_failure_before_horizon
    {ell ell0 Delta eps kappa : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (hkappa : paperC0 ell0 revisedMu0 ≤ kappa)
    (hregime : eps ^ 2 ≤
      paperC1 ell0 revisedDelta0 revisedG0 * ell * Delta)
    (Z : DeterministicSaddleAlgorithm) (hZ : Z.IsZeroRespecting)
    {t : ℕ}
    (ht : t < concreteLowerBoundHorizon ell ell0 Delta eps kappa) :
    let hN : 2 ≤ concretePaperN ell0 kappa :=
      paperN_two_le hell0 revisedMu0_pos hkappa
    let f := concreteScaledSmoothSaddle ell ell0 Delta eps kappa
      hell hell0 heps hN
    ¬f.IsEpsilonStationary eps (Z.query f t).1 := by
  exact concreteScaledSmoothSaddle_zeroRespecting_failure
    hell hell0 hDelta heps hkappa hregime Z hZ
      (cast_lt_concreteLowerBoundThreshold_of_lt_horizon ht)

/-! ## Main-theorem assembly before specializing the proved base smoothness -/

/-- The zero-respecting lower bound, parametrized only by a normalized
smoothness certificate so that the final theorem below can specialize it to
the concrete Lemma 5.1 constant. -/
theorem zeroRespecting_main_lower_bound_of_base
    {ell ell0 mu Delta eps : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (hmu : 0 < mu)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (hkappa : paperC0 ell0 revisedMu0 ≤ ell / mu)
    (hregime : eps ^ 2 ≤
      paperC1 ell0 revisedDelta0 revisedG0 * ell * Delta)
    (hbase : IsEuclideanJointlySmooth ell0
      (barPrimalGradient (concretePaperM ell ell0 Delta eps)
        (concretePaperN ell0 (ell / mu)))
      (barDualGradient (concretePaperM ell ell0 Delta eps)
        (concretePaperN ell0 (ell / mu)))) :
    ∃ f : SmoothSaddle (concretePaperM ell ell0 Delta eps)
        (concretePaperM ell ell0 Delta eps *
          concretePaperN ell0 (ell / mu)),
      f.InClass ell mu Delta ∧
      ∀ (Z : DeterministicSaddleAlgorithm), Z.IsZeroRespecting →
        ∀ t : ℕ,
          (t : ℝ) < concreteLowerBoundThreshold
            ell ell0 Delta eps (ell / mu) →
          ¬f.IsEpsilonStationary eps (Z.query f t).1 := by
  let hN : 2 ≤ concretePaperN ell0 (ell / mu) :=
    paperN_two_le hell0 revisedMu0_pos hkappa
  let f := concreteScaledSmoothSaddle ell ell0 Delta eps (ell / mu)
    hell hell0 heps hN
  refine ⟨f, ?_, ?_⟩
  · exact concreteScaledSmoothSaddle_inClass_of_base
      hell hell0 hmu hDelta heps hkappa hbase
  · intro Z hZ t ht
    exact concreteScaledSmoothSaddle_zeroRespecting_failure
      hell hell0 hDelta heps hkappa hregime Z hZ ht

/-- Deterministic finite-horizon lower bound after applying the exact
resisting-oracle proposition of Lemma 2.2.  This theorem has `hRO` as its
only manuscript-level assumption; the hard instance and every analytic
class certificate are concrete. -/
theorem deterministic_main_lower_bound_of_base
    (hRO : FiniteHorizonSaddleResistingOracle)
    {ell ell0 mu Delta eps : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (hmu : 0 < mu)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (hkappa : paperC0 ell0 revisedMu0 ≤ ell / mu)
    (hregime : eps ^ 2 ≤
      paperC1 ell0 revisedDelta0 revisedG0 * ell * Delta)
    (hbase : IsEuclideanJointlySmooth ell0
      (barPrimalGradient (concretePaperM ell ell0 Delta eps)
        (concretePaperN ell0 (ell / mu)))
      (barDualGradient (concretePaperM ell ell0 Delta eps)
        (concretePaperN ell0 (ell / mu))))
    (A : DeterministicSaddleAlgorithm) :
    let M := concretePaperM ell ell0 Delta eps
    let N := concretePaperN ell0 (ell / mu)
    let T := concreteLowerBoundHorizon ell ell0 Delta eps (ell / mu)
    ∃ (f : SmoothSaddle M (M * N))
      (U : Fin M → EVec (M + T))
      (hU : IsEuclideanOrthonormalFrame U)
      (V : Fin (M * N) → EVec (M * N + T))
      (hV : IsEuclideanOrthonormalFrame V),
      (f.rotate U V hU hV).InClass ell mu Delta ∧
      ∀ t : ℕ,
        (t : ℝ) < concreteLowerBoundThreshold
          ell ell0 Delta eps (ell / mu) →
        ¬(f.rotate U V hU hV).IsEpsilonStationary eps
          (A.query (f.rotate U V hU hV) t).1 := by
  dsimp only
  let M := concretePaperM ell ell0 Delta eps
  let N := concretePaperN ell0 (ell / mu)
  let T := concreteLowerBoundHorizon ell ell0 Delta eps (ell / mu)
  let hN : 2 ≤ N := paperN_two_le hell0 revisedMu0_pos hkappa
  let f : SmoothSaddle M (M * N) :=
    concreteScaledSmoothSaddle ell ell0 Delta eps (ell / mu)
      hell hell0 heps hN
  have hf : f.InClass ell mu Delta :=
    concreteScaledSmoothSaddle_inClass_of_base
      hell hell0 hmu hDelta heps hkappa hbase
  have hhard : ∀ (Z : DeterministicSaddleAlgorithm),
      Z.IsZeroRespecting → ∀ t : ℕ, t < T →
        ¬f.IsEpsilonStationary eps (Z.query f t).1 := by
    intro Z hZ t ht
    exact concreteScaledSmoothSaddle_zeroRespecting_failure_before_horizon
      hell hell0 hDelta heps hkappa hregime Z hZ ht
  obtain ⟨U, hU, V, hV, hclass, hfailure⟩ :=
    deterministic_failure_of_finiteHorizonResistingOracle
      hRO f hf hhard A
  refine ⟨f, U, hU, V, hV, hclass, ?_⟩
  intro t ht
  exact hfailure t
    (lt_concreteLowerBoundHorizon_iff_cast_lt_threshold.mpr ht)

/-- Fully quantified form of Theorem 3.1 for any already-proved normalized
smoothness constant.  The same concrete instance `f` defeats every
zero-respecting deterministic algorithm. -/
theorem theorem3_1_zeroRespecting_of_normalizedSmoothness
    (ell0 : ℝ) (hell0 : 0 < ell0)
    (hc0 : 1 < paperC0 ell0 revisedMu0)
    (hbase : ∀ {M N : ℕ}, 2 ≤ N →
      IsEuclideanJointlySmooth ell0
        (barPrimalGradient M N) (barDualGradient M N)) :
    1 < paperC0 ell0 revisedMu0 ∧
    0 < paperC1 ell0 revisedDelta0 revisedG0 ∧
    0 < paperC2 ell0 revisedMu0 revisedDelta0 revisedG0 ∧
    ∀ (ell mu Delta eps : ℝ),
      0 < ell → 0 < mu → 0 < Delta → 0 < eps →
      paperC0 ell0 revisedMu0 ≤ ell / mu →
      eps ^ 2 ≤ paperC1 ell0 revisedDelta0 revisedG0 * ell * Delta →
      ∃ f : SmoothSaddle (concretePaperM ell ell0 Delta eps)
          (concretePaperM ell ell0 Delta eps *
            concretePaperN ell0 (ell / mu)),
        f.InClass ell mu Delta ∧
        ∀ (Z : DeterministicSaddleAlgorithm), Z.IsZeroRespecting →
          ∀ t : ℕ,
            (t : ℝ) < paperC2 ell0 revisedMu0 revisedDelta0 revisedG0 *
              (ell / mu) * ell * Delta / eps ^ 2 →
            ¬f.IsEpsilonStationary eps (Z.query f t).1 := by
  have hc1 : 0 < paperC1 ell0 revisedDelta0 revisedG0 := by
    unfold paperC1 revisedDelta0 revisedG0
    positivity
  have hc2 : 0 < paperC2 ell0 revisedMu0 revisedDelta0 revisedG0 := by
    unfold paperC2 revisedMu0 revisedDelta0 revisedG0
    positivity
  refine ⟨hc0, hc1, hc2, ?_⟩
  intro ell mu Delta eps hell hmu hDelta heps hkappa hregime
  have hN : 2 ≤ concretePaperN ell0 (ell / mu) :=
    paperN_two_le hell0 revisedMu0_pos hkappa
  have hresult := zeroRespecting_main_lower_bound_of_base
    hell hell0 hmu hDelta heps hkappa hregime (hbase hN)
  simpa only [concreteLowerBoundThreshold] using hresult

/-- Fully quantified conditional form of Theorem 3.2.  The base instance is
fixed by the problem parameters, while the orthogonal rotation is allowed to
depend on the deterministic algorithm `A`, exactly as in Lemma 2.2. -/
theorem theorem3_2_deterministic_of_normalizedSmoothness
    (hRO : FiniteHorizonSaddleResistingOracle)
    (ell0 : ℝ) (hell0 : 0 < ell0)
    (hbase : ∀ {M N : ℕ}, 2 ≤ N →
      IsEuclideanJointlySmooth ell0
        (barPrimalGradient M N) (barDualGradient M N)) :
    ∀ (ell mu Delta eps : ℝ),
      0 < ell → 0 < mu → 0 < Delta → 0 < eps →
      paperC0 ell0 revisedMu0 ≤ ell / mu →
      eps ^ 2 ≤ paperC1 ell0 revisedDelta0 revisedG0 * ell * Delta →
      ∀ A : DeterministicSaddleAlgorithm,
        let M := concretePaperM ell ell0 Delta eps
        let N := concretePaperN ell0 (ell / mu)
        let T := concreteLowerBoundHorizon ell ell0 Delta eps (ell / mu)
        ∃ (f : SmoothSaddle M (M * N))
          (U : Fin M → EVec (M + T))
          (hU : IsEuclideanOrthonormalFrame U)
          (V : Fin (M * N) → EVec (M * N + T))
          (hV : IsEuclideanOrthonormalFrame V),
          (f.rotate U V hU hV).InClass ell mu Delta ∧
          ∀ t : ℕ,
            (t : ℝ) < paperC2 ell0 revisedMu0 revisedDelta0 revisedG0 *
              (ell / mu) * ell * Delta / eps ^ 2 →
            ¬(f.rotate U V hU hV).IsEpsilonStationary eps
              (A.query (f.rotate U V hU hV) t).1 := by
  intro ell mu Delta eps hell hmu hDelta heps hkappa hregime A
  have hN : 2 ≤ concretePaperN ell0 (ell / mu) :=
    paperN_two_le hell0 revisedMu0_pos hkappa
  have hresult := deterministic_main_lower_bound_of_base
    hRO hell hell0 hmu hDelta heps hkappa hregime (hbase hN) A
  simpa only [concreteLowerBoundThreshold] using hresult

/-! ## Concrete, premise-free analytic specialization -/

/-- The numerical constant `c₀` obtained from the completely explicit
normalized hard instance. -/
def concreteC0 : ℝ := paperC0 concreteEll0 revisedMu0

/-- The numerical constant `c₁` obtained from the completely explicit
normalized hard instance. -/
def concreteC1 : ℝ :=
  paperC1 concreteEll0 revisedDelta0 revisedG0

/-- The numerical constant `c₂` obtained from the completely explicit
normalized hard instance. -/
def concreteC2 : ℝ :=
  paperC2 concreteEll0 revisedMu0 revisedDelta0 revisedG0

theorem concreteC0_gt_one : 1 < concreteC0 := by
  exact revised_c0_gt_one one_le_concreteLC

theorem concreteC1_pos : 0 < concreteC1 := by
  exact revised_c1_pos (lt_of_lt_of_le zero_lt_one one_le_concreteLC)

theorem concreteC2_pos : 0 < concreteC2 := by
  exact revised_c2_pos (lt_of_lt_of_le zero_lt_one one_le_concreteLC)

/-- Theorem 3.1 with every analytic certificate discharged for the concrete
hard instance.  There is no project-defined axiom in this theorem. -/
theorem theorem3_1_concrete :
    1 < concreteC0 ∧
    0 < concreteC1 ∧
    0 < concreteC2 ∧
    ∀ (ell mu Delta eps : ℝ),
      0 < ell → 0 < mu → 0 < Delta → 0 < eps →
      concreteC0 ≤ ell / mu →
      eps ^ 2 ≤ concreteC1 * ell * Delta →
      ∃ f : SmoothSaddle (concretePaperM ell concreteEll0 Delta eps)
          (concretePaperM ell concreteEll0 Delta eps *
            concretePaperN concreteEll0 (ell / mu)),
        f.InClass ell mu Delta ∧
        ∀ (Z : DeterministicSaddleAlgorithm), Z.IsZeroRespecting →
          ∀ t : ℕ,
            (t : ℝ) < concreteC2 * (ell / mu) * ell * Delta / eps ^ 2 →
            ¬f.IsEpsilonStationary eps (Z.query f t).1 := by
  simpa only [concreteC0, concreteC1, concreteC2] using
    (theorem3_1_zeroRespecting_of_normalizedSmoothness
      concreteEll0 concreteEll0_pos concreteC0_gt_one
      (fun hN ↦ barF_isJointlySmooth hN))

/-- Paper-facing form of the deterministic transfer: the witness is the
actual rotated instance queried by `A`, rather than a base instance together
with its two embedding frames. -/
theorem theorem3_2_rotated_of_normalizedSmoothness
    (hRO : FiniteHorizonSaddleResistingOracle)
    (ell0 : ℝ) (hell0 : 0 < ell0)
    (hbase : ∀ {M N : ℕ}, 2 ≤ N →
      IsEuclideanJointlySmooth ell0
        (barPrimalGradient M N) (barDualGradient M N)) :
    ∀ (ell mu Delta eps : ℝ),
      0 < ell → 0 < mu → 0 < Delta → 0 < eps →
      paperC0 ell0 revisedMu0 ≤ ell / mu →
      eps ^ 2 ≤ paperC1 ell0 revisedDelta0 revisedG0 * ell * Delta →
      ∀ A : DeterministicSaddleAlgorithm,
        let M := concretePaperM ell ell0 Delta eps
        let N := concretePaperN ell0 (ell / mu)
        let T := concreteLowerBoundHorizon ell ell0 Delta eps (ell / mu)
        ∃ g : SmoothSaddle (M + T) (M * N + T),
          g.InClass ell mu Delta ∧
          ∀ t : ℕ,
            (t : ℝ) < paperC2 ell0 revisedMu0 revisedDelta0 revisedG0 *
              (ell / mu) * ell * Delta / eps ^ 2 →
            ¬g.IsEpsilonStationary eps (A.query g t).1 := by
  intro ell mu Delta eps hell hmu hDelta heps hkappa hregime A
  obtain ⟨f, U, hU, V, hV, hclass, hfailure⟩ :=
    theorem3_2_deterministic_of_normalizedSmoothness
      hRO ell0 hell0 hbase ell mu Delta eps
      hell hmu hDelta heps hkappa hregime A
  exact ⟨f.rotate U V hU hV, hclass, hfailure⟩

/-- Theorem 3.2 with every analytic certificate discharged.  Its sole
remaining premise is exactly the separately isolated statement of the
manuscript's Lemma 2.2. -/
theorem theorem3_2_concrete
    (hRO : FiniteHorizonSaddleResistingOracle) :
    1 < concreteC0 ∧
    0 < concreteC1 ∧
    0 < concreteC2 ∧
    ∀ (ell mu Delta eps : ℝ),
      0 < ell → 0 < mu → 0 < Delta → 0 < eps →
      concreteC0 ≤ ell / mu →
      eps ^ 2 ≤ concreteC1 * ell * Delta →
      ∀ A : DeterministicSaddleAlgorithm,
        let M := concretePaperM ell concreteEll0 Delta eps
        let N := concretePaperN concreteEll0 (ell / mu)
        let T := concreteLowerBoundHorizon
          ell concreteEll0 Delta eps (ell / mu)
        ∃ g : SmoothSaddle (M + T) (M * N + T),
          g.InClass ell mu Delta ∧
          ∀ t : ℕ,
            (t : ℝ) < concreteC2 * (ell / mu) * ell * Delta / eps ^ 2 →
            ¬g.IsEpsilonStationary eps (A.query g t).1 := by
  refine ⟨concreteC0_gt_one, concreteC1_pos, concreteC2_pos, ?_⟩
  simpa only [concreteC0, concreteC1, concreteC2] using
    (theorem3_2_rotated_of_normalizedSmoothness
      hRO concreteEll0 concreteEll0_pos
      (fun hN ↦ barF_isJointlySmooth hN))

/-- Literal existential-constants presentation of Theorem 3.1. -/
theorem theorem3_1 :
    ∃ c0 c1 c2 : ℝ,
      1 < c0 ∧ 0 < c1 ∧ 0 < c2 ∧
      ∀ (ell mu Delta eps : ℝ),
        0 < ell → 0 < mu → 0 < Delta → 0 < eps →
        c0 ≤ ell / mu → eps ^ 2 ≤ c1 * ell * Delta →
        ∃ f : SmoothSaddle (concretePaperM ell concreteEll0 Delta eps)
            (concretePaperM ell concreteEll0 Delta eps *
              concretePaperN concreteEll0 (ell / mu)),
          f.InClass ell mu Delta ∧
          ∀ (Z : DeterministicSaddleAlgorithm), Z.IsZeroRespecting →
            ∀ t : ℕ,
              (t : ℝ) < c2 * (ell / mu) * ell * Delta / eps ^ 2 →
              ¬f.IsEpsilonStationary eps (Z.query f t).1 := by
  exact ⟨concreteC0, concreteC1, concreteC2, theorem3_1_concrete⟩

end

end NCPLRevised
