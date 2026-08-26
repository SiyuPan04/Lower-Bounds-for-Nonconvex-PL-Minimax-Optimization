/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.SaddleOracleModel

/-!
# Deterministic finite-horizon transfer

This is the proved implication used in Theorem 3.2.  Its only non-derived
input is the exact proposition stated as Lemma 2.2; rotation invariance and
stationarity preservation are supplied by kernel-checked theorems.
-/

namespace NCPLRevised

noncomputable section

theorem deterministic_failure_of_finiteHorizonResistingOracle
    (hRO : FiniteHorizonSaddleResistingOracle)
    {m n T : ℕ} {ell mu Delta epsilon : ℝ}
    (f : SmoothSaddle m n) (hf : f.InClass ell mu Delta)
    (hhard : ∀ (Z : DeterministicSaddleAlgorithm),
      Z.IsZeroRespecting → ∀ t : ℕ, t < T →
        ¬f.IsEpsilonStationary epsilon (Z.query f t).1)
    (A : DeterministicSaddleAlgorithm) :
    ∃ (U : Fin m → EVec (m + T))
      (hU : IsEuclideanOrthonormalFrame U)
      (V : Fin n → EVec (n + T))
      (hV : IsEuclideanOrthonormalFrame V),
      (f.rotate U V hU hV).InClass ell mu Delta ∧
      ∀ t : ℕ, t < T →
        ¬(f.rotate U V hU hV).IsEpsilonStationary epsilon
          (A.query (f.rotate U V hU hV) t).1 := by
  obtain ⟨Z, hZ, hsimulation⟩ := hRO T A
  obtain ⟨U, hU, V, hV, hagree⟩ := hsimulation f
  refine ⟨U, hU, V, hV, f.rotate_inClass hf U V hU hV, ?_⟩
  intro t ht hstationary
  have hbase : f.IsEpsilonStationary epsilon
      (orthogonalProject U (A.query (f.rotate U V hU hV) t).1) :=
    (f.rotate_stationary_iff epsilon U V hU hV _).mp hstationary
  rw [(hagree t ht).1] at hbase
  exact hhard Z hZ t ht hbase

end

end NCPLRevised
