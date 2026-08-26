/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.HardInstanceAssembly
import NCPLRevised.SaddleOracleModel

/-!
# Bridge from componentwise algorithms to the interleaved hard-instance order

Zero-respecting behavior is invariant under a coordinate permutation.  This
file proves that fact for the exact order used in the manuscript, without
assuming it as part of the resisting-oracle lemma.
-/

namespace NCPLRevised

noncomputable section

/-- Reorder a primal/flat-dual query into consecutive
`y₁⁽ⁱ⁾,…,y_N⁽ⁱ⁾,xᵢ` blocks. -/
def orderedAlgorithmQuery (M N : ℕ) (A : DeterministicSaddleAlgorithm)
    (f : SmoothSaddle M (M * N)) (t : ℕ) :
    EVec (M * (N + 1)) :=
  assembleOrdered (A.query f t).1 (A.query f t).2

/-- Reorder the actual saddle gradient of a certified oracle in the same
way. -/
def orderedSaddleField (M N : ℕ) (f : SmoothSaddle M (M * N))
    (z : EVec (M * (N + 1))) : EVec (M * (N + 1)) :=
  assembleOrdered
    (f.gradX (orderedPrimal z) (orderedDual z))
    (f.gradY (orderedPrimal z) (orderedDual z))

@[simp] theorem orderedSaddleField_at_algorithmQuery
    (M N : ℕ) (A : DeterministicSaddleAlgorithm)
    (f : SmoothSaddle M (M * N)) (t : ℕ) :
    orderedSaddleField M N f (orderedAlgorithmQuery M N A f t) =
      assembleOrdered
        (f.gradX (A.query f t).1 (A.query f t).2)
        (f.gradY (A.query f t).1 (A.query f t).2) := by
  simp [orderedSaddleField, orderedAlgorithmQuery]

/-- Definition 2.4 in component coordinates implies the same definition
after applying the paper's interleaving permutation. -/
theorem zeroRespecting_orderedAlgorithmQuery
    (A : DeterministicSaddleAlgorithm)
    (hA : A.IsZeroRespecting) (M N : ℕ)
    (f : SmoothSaddle M (M * N)) :
    QueriesAreZeroRespecting (orderedSaddleField M N f)
      (orderedAlgorithmQuery M N A f) := by
  intro t r hr
  let ij := finProdFinEquiv.symm r
  have hrindex : finProdFinEquiv ij = r :=
    finProdFinEquiv.apply_symm_apply r
  rcases ij with ⟨i, j⟩
  by_cases hj : j.1 < N
  · let jd : Fin N := ⟨j.1, hj⟩
    have hjcast : jd.castSucc = j := Fin.ext rfl
    have hquery : (A.query f t).2 (finProdFinEquiv (i, jd)) ≠ 0 := by
      change assembleOrdered (A.query f t).1 (A.query f t).2 r ≠ 0 at hr
      rw [← hrindex, ← hjcast, assembleOrdered_dual_apply] at hr
      exact hr
    obtain ⟨s, hst, hs⟩ := (hA f t).2 (finProdFinEquiv (i, jd)) hquery
    refine ⟨s, hst, ?_⟩
    rw [orderedSaddleField_at_algorithmQuery]
    rw [← hrindex, ← hjcast, assembleOrdered_dual_apply]
    exact hs
  · have hjlast : j = Fin.last N := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    have hquery : (A.query f t).1 i ≠ 0 := by
      change assembleOrdered (A.query f t).1 (A.query f t).2 r ≠ 0 at hr
      rw [← hrindex, hjlast, assembleOrdered_primal_apply] at hr
      exact hr
    obtain ⟨s, hst, hs⟩ := (hA f t).1 i hquery
    refine ⟨s, hst, ?_⟩
    rw [orderedSaddleField_at_algorithmQuery]
    rw [← hrindex, hjlast, assembleOrdered_primal_apply]
    exact hs

end

end NCPLRevised
