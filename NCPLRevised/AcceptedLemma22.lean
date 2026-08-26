/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.MainTheorems

/-!
# Explicit acceptance of manuscript Lemma 2.2

The user requested that Lemma 2.2 be treated as given because the manuscript
states it without proof.  This file is the sole trust boundary for that
request.  All analytic hard-instance results and Theorem 3.1 are proved
without importing this declaration.
-/

namespace NCPLRevised

noncomputable section

/-- The manuscript's Lemma 2.2, explicitly accepted as the sole custom
axiom of the formalization. -/
axiom acceptedFiniteHorizonSaddleResistingOracle :
  FiniteHorizonSaddleResistingOracle

/-- Syntactically assumption-free deterministic lower bound once the one
authorized Lemma 2.2 declaration above is accepted.  The final concrete
specialization fixes `ell0` to the proved Lemma 5.1 constant. -/
theorem theorem3_2_deterministic_accepted_of_normalizedSmoothness
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
              (A.query (f.rotate U V hU hV) t).1 :=
  theorem3_2_deterministic_of_normalizedSmoothness
    acceptedFiniteHorizonSaddleResistingOracle ell0 hell0 hbase

/-- The completely specialized deterministic lower bound.  It has no
arguments: the only non-derived fact in its transitive dependency graph is
the explicitly accepted manuscript Lemma 2.2 above. -/
theorem theorem3_2_concrete_accepted :
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
            ¬g.IsEpsilonStationary eps (A.query g t).1 :=
  theorem3_2_concrete acceptedFiniteHorizonSaddleResistingOracle

/-- Literal existential-constants presentation of Theorem 3.2.  This is the
paper-facing final theorem of the accepted-Lemma-2.2 module. -/
theorem theorem3_2 :
    ∃ c0 c1 c2 : ℝ,
      1 < c0 ∧ 0 < c1 ∧ 0 < c2 ∧
      ∀ (ell mu Delta eps : ℝ),
        0 < ell → 0 < mu → 0 < Delta → 0 < eps →
        c0 ≤ ell / mu → eps ^ 2 ≤ c1 * ell * Delta →
        ∀ A : DeterministicSaddleAlgorithm,
          let M := concretePaperM ell concreteEll0 Delta eps
          let N := concretePaperN concreteEll0 (ell / mu)
          let T := concreteLowerBoundHorizon
            ell concreteEll0 Delta eps (ell / mu)
          ∃ g : SmoothSaddle (M + T) (M * N + T),
            g.InClass ell mu Delta ∧
            ∀ t : ℕ,
              (t : ℝ) < c2 * (ell / mu) * ell * Delta / eps ^ 2 →
              ¬g.IsEpsilonStationary eps (A.query g t).1 := by
  exact ⟨concreteC0, concreteC1, concreteC2,
    theorem3_2_concrete_accepted⟩

end

end NCPLRevised
