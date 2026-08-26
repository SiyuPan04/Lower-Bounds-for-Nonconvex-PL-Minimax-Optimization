/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.ScalingCalculus

/-!
# Scaling preserves first-order saddle zero-chains

This file proves the support part of Lemma 5.2 for the actual rescaled
gradient field.  It is stated on the interleaved joint coordinates, so it
can be applied directly to the concrete field from Proposition 5.2.
-/

namespace NCPLRevised

noncomputable section

/-- The joint gradient field after the objective/value scaling
`f(z) = a * barf(z / lambda)`. -/
def scaledJointField {d : ℕ} (a lambda : ℝ)
    (field : EVec d → EVec d) (z : EVec d) : EVec d :=
  fun i ↦ a / lambda * field (scaleEVec lambda z) i

theorem supportedBelow_scaleEVec {d k : ℕ} {lambda : ℝ}
    {z : EVec d} (hz : SupportedBelow k z) :
    SupportedBelow k (scaleEVec lambda z) := by
  intro i hi
  simp [scaleEVec, hz i hi]

theorem supportedBelow_const_mul {d k : ℕ} (c : ℝ) {z : EVec d}
    (hz : SupportedBelow k z) :
    SupportedBelow k (fun i ↦ c * z i) := by
  intro i hi
  change c * z i = 0
  rw [hz i hi, mul_zero]

/-- Positive spatial/amplitude scaling preserves the one-coordinate
discovery rule.  In fact, this direction does not require either scalar to
be nonzero: multiplication and coordinatewise division cannot create a
nonzero coordinate from a zero one. -/
theorem scaledJointField_isZeroChain {d : ℕ} {field : EVec d → EVec d}
    (hfield : IsFirstOrderSaddleZeroChain field) (a lambda : ℝ) :
    IsFirstOrderSaddleZeroChain (scaledJointField a lambda field) := by
  intro k z hz
  have hscaled : SupportedBelow k (scaleEVec lambda z) :=
    supportedBelow_scaleEVec hz
  have hnext := hfield k (scaleEVec lambda z) hscaled
  exact supportedBelow_const_mul (a / lambda) hnext

/-- With nonzero scaling, zero-respecting transcripts are equivalent before
and after pulling both their points and gradient field back to normalized
coordinates. -/
theorem queriesAreZeroRespecting_scaledJointField_iff
    {d : ℕ} {field : EVec d → EVec d}
    {query : ℕ → EVec d} {a lambda : ℝ}
    (ha : a ≠ 0) (hlambda : lambda ≠ 0) :
    QueriesAreZeroRespecting (scaledJointField a lambda field) query ↔
      QueriesAreZeroRespecting field
        (fun t ↦ scaleEVec lambda (query t)) := by
  constructor
  · intro hscaled t i hquery
    have hquery' : query t i ≠ 0 := by
      simpa [scaleEVec, hlambda] using hquery
    obtain ⟨s, hst, hs⟩ := hscaled t i hquery'
    refine ⟨s, hst, ?_⟩
    simpa [scaledJointField, ha, hlambda] using hs
  · intro hbase t i hquery
    have hquery' : scaleEVec lambda (query t) i ≠ 0 := by
      simpa [scaleEVec, hlambda] using hquery
    obtain ⟨s, hst, hs⟩ := hbase t i hquery'
    refine ⟨s, hst, ?_⟩
    simpa [scaledJointField, ha, hlambda] using hs

end

end NCPLRevised
