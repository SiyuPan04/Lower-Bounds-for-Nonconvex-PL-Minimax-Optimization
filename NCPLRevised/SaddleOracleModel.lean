/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.RotationInvarianceCore

/-!
# Deterministic first-order saddle-oracle model

This module gives a dimension-polymorphic, transcript-based meaning to the
algorithm classes in Section 2.  The finite-horizon resisting-oracle lemma
is *not* postulated here; its exact proposition is defined at the end so
that the manuscript's unproved Lemma 2.2 can be isolated and audited.
-/

namespace NCPLRevised

noncomputable section

/-- A query point for an `m`-by-`n` saddle problem. -/
abbrev SaddlePoint (m n : ℕ) := EVec m × EVec n

/-- An admissible smooth saddle oracle together with the actual gradient of
its value function.  The value function is the exact supremum
`RotationEnvelope F`; `envelope_hasFDerivAt` certifies that the displayed
vector is its actual Fréchet gradient. -/
structure SmoothSaddle (m n : ℕ) where
  F : EVec m → EVec n → ℝ
  gradX : EVec m → EVec n → EVec m
  gradY : EVec m → EVec n → EVec n
  gradient_representation : RepresentsRotatableGradient F gradX gradY
  maximum_attained : ∀ x, ∃ y, IsRotatedMaximizer F x y
  envelopeGradient : EVec m → EVec m
  envelope_hasFDerivAt : ∀ x,
    HasFDerivAt (RotationEnvelope F)
      (finiteDotProductCLM (envelopeGradient x)) x

/-- Membership of a certified oracle in the paper's NC--PL class. -/
def SmoothSaddle.InClass {m n : ℕ} (f : SmoothSaddle m n)
    (ell mu Delta : ℝ) : Prop :=
  EuclideanNCPLClass ell mu Delta f.F f.gradX f.gradY

/-- Squared-gradient formulation of value-function stationarity. -/
def SmoothSaddle.IsEpsilonStationary {m n : ℕ}
    (f : SmoothSaddle m n) (epsilon : ℝ) (x : EVec m) : Prop :=
  euclideanSq (f.envelopeGradient x) ≤ epsilon ^ 2

/-- Orthogonal lifting of a certified saddle oracle. -/
def SmoothSaddle.rotate {m n M N : ℕ} (f : SmoothSaddle m n)
    (U : Fin m → EVec M) (V : Fin n → EVec N)
    (_hU : IsEuclideanOrthonormalFrame U)
    (hV : IsEuclideanOrthonormalFrame V) : SmoothSaddle M N where
  F := rotatedObjective U V f.F
  gradX := rotatedGradientX U V f.gradX
  gradY := rotatedGradientY U V f.gradY
  gradient_representation :=
    rotatedObjective_representsGradient f.gradient_representation U V
  maximum_attained := by
    intro X
    obtain ⟨y, hy⟩ := f.maximum_attained (orthogonalProject U X)
    exact ⟨orthogonalEmbed V y, rotatedObjective_isMaximizer hV hy⟩
  envelopeGradient := fun X ↦
    orthogonalEmbed U (f.envelopeGradient (orthogonalProject U X))
  envelope_hasFDerivAt := by
    intro X
    exact rotatedEnvelope_hasFDerivAt hV
      (f.envelope_hasFDerivAt (orthogonalProject U X))

theorem SmoothSaddle.rotate_inClass {m n M N : ℕ}
    {ell mu Delta : ℝ} (f : SmoothSaddle m n)
    (hf : f.InClass ell mu Delta)
    (U : Fin m → EVec M) (V : Fin n → EVec N)
    (hU : IsEuclideanOrthonormalFrame U)
    (hV : IsEuclideanOrthonormalFrame V) :
    (f.rotate U V hU hV).InClass ell mu Delta := by
  exact hf.rotate hU hV

theorem SmoothSaddle.rotate_stationary_iff {m n M N : ℕ}
    (f : SmoothSaddle m n) (epsilon : ℝ)
    (U : Fin m → EVec M) (V : Fin n → EVec N)
    (hU : IsEuclideanOrthonormalFrame U)
    (hV : IsEuclideanOrthonormalFrame V) (X : EVec M) :
    (f.rotate U V hU hV).IsEpsilonStationary epsilon X ↔
      f.IsEpsilonStationary epsilon (orthogonalProject U X) := by
  unfold SmoothSaddle.IsEpsilonStationary SmoothSaddle.rotate
  exact rotated_stationarity_iff hU
    (f.envelopeGradient (orthogonalProject U X)) epsilon

/-- The exact response returned by the first-order saddle oracle. -/
structure SaddleOracleAnswer (m n : ℕ) where
  value : ℝ
  gradX : EVec m
  gradY : EVec n

def saddleOracle {m n : ℕ} (f : SmoothSaddle m n)
    (z : SaddlePoint m n) : SaddleOracleAnswer m n where
  value := f.F z.1 z.2
  gradX := f.gradX z.1 z.2
  gradY := f.gradY z.1 z.2

/-- A deterministic first-order algorithm is dimension-polymorphic.  Its
`update` map depends only on the finite transcript; `query_eq_update`
rules out direct access to the hidden function beyond those oracle answers.
-/
structure DeterministicSaddleAlgorithm where
  query : ∀ {m n : ℕ}, SmoothSaddle m n → ℕ → SaddlePoint m n
  update : ∀ (m n t : ℕ),
    (Fin t → SaddleOracleAnswer m n) → SaddlePoint m n
  initial_zero : ∀ {m n : ℕ} (f : SmoothSaddle m n),
    query f 0 = (0, 0)
  query_eq_update : ∀ {m n : ℕ} (f : SmoothSaddle m n) (t : ℕ),
    query f t = update m n t
      (fun s ↦ saddleOracle f (query f s.1))

/-- Componentwise form of Definition 2.4.  It is independent of a chosen
coordinate permutation and therefore transports directly to the paper's
interleaved ordering. -/
def DeterministicSaddleAlgorithm.IsZeroRespecting
    (A : DeterministicSaddleAlgorithm) : Prop :=
  ∀ {m n : ℕ} (f : SmoothSaddle m n) (t : ℕ),
    (∀ i, (A.query f t).1 i ≠ 0 →
      ∃ s < t, f.gradX (A.query f s).1 (A.query f s).2 i ≠ 0) ∧
    (∀ j, (A.query f t).2 j ≠ 0 →
      ∃ s < t, f.gradY (A.query f s).1 (A.query f s).2 j ≠ 0)

/-- Exact proposition stated as Lemma 2.2 in the manuscript.  It is a
definition, not an axiom: the one user-authorized assumption can later be
made by supplying a term of this proposition (or by an explicitly audited
single declaration). -/
def FiniteHorizonSaddleResistingOracle : Prop :=
  ∀ (T : ℕ) (A : DeterministicSaddleAlgorithm),
    ∃ Z : DeterministicSaddleAlgorithm,
      Z.IsZeroRespecting ∧
      ∀ {m n : ℕ} (f : SmoothSaddle m n),
        ∃ (U : Fin m → EVec (m + T))
          (hU : IsEuclideanOrthonormalFrame U)
          (V : Fin n → EVec (n + T))
          (hV : IsEuclideanOrthonormalFrame V),
          ∀ t : ℕ, t < T →
            orthogonalProject U
                (A.query (f.rotate U V hU hV) t).1 =
              (Z.query f t).1 ∧
            orthogonalProject V
                (A.query (f.rotate U V hU hV) t).2 =
              (Z.query f t).2

end

end NCPLRevised
