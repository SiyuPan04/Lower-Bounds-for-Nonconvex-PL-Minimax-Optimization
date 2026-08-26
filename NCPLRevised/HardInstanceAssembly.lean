/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.BlockLayout
import NCPLRevised.CarmonCertificate
import NCPLRevised.DualChain

/-!
# Assembly of the finite hard instance

This file implements the indexing and finite-separation layer used in
Section 5 of the revised manuscript.  A flat vector in `R^(M*N)` is split
into `M` consecutive dual blocks, and each link uses the predecessor
convention `x₀ = 1`.

The first part is deliberately generic in the cell and its value.  Thus the
finite-envelope theorem does not hide an existence or compactness argument:
it takes a pointwise upper bound and an explicit maximizer for each finite
block and constructs the global maximizing dual vector coordinate by
coordinate.
-/

namespace NCPLRevised

noncomputable section

/-- The `i`-th consecutive `N`-dimensional block of a flat dual vector. -/
def dualBlock {M N : ℕ} (y : EVec (M * N)) (i : Fin M) : ChainPoint N :=
  fun j ↦ y (finProdFinEquiv (i, j))

/-- Flatten a block-indexed family in the paper's canonical dual order. -/
def flattenDualBlocks {M N : ℕ} (Y : Fin M → ChainPoint N) : EVec (M * N) :=
  fun k ↦
    let ij := finProdFinEquiv.symm k
    Y ij.1 ij.2

@[simp] theorem dualBlock_flattenDualBlocks {M N : ℕ}
    (Y : Fin M → ChainPoint N) (i : Fin M) :
    dualBlock (flattenDualBlocks Y) i = Y i := by
  funext j
  simp [dualBlock, flattenDualBlocks]

@[simp] theorem flattenDualBlocks_dualBlock {M N : ℕ} (y : EVec (M * N)) :
    flattenDualBlocks (fun i ↦ dualBlock y i) = y := by
  funext k
  simp only [flattenDualBlocks, dualBlock]
  congr 1
  exact finProdFinEquiv.apply_symm_apply k

/-- The predecessor coordinate used on link `i`, including `x₀ = 1`. -/
def primalPrev {M : ℕ} (x : EVec M) (i : Fin M) : ℝ :=
  if hi : i.1 = 0 then 1 else x ⟨i.1 - 1, by omega⟩

@[simp] theorem primalPrev_zero {M : ℕ} (x : EVec M) (hM : 0 < M) :
    primalPrev x ⟨0, hM⟩ = 1 := by
  simp [primalPrev]

theorem primalPrev_ne_zero {M : ℕ} (x : EVec M) (i : Fin M)
    (hi : i.1 ≠ 0) :
    primalPrev x i = x ⟨i.1 - 1, by omega⟩ := by
  simp [primalPrev, hi]

/-- Sum one scalar/dual cell over every outer link. -/
def assembledCells {M N : ℕ}
    (cell : ℝ → ℝ → ChainPoint N → ℝ)
    (x : EVec M) (y : EVec (M * N)) : ℝ :=
  ∑ i : Fin M, cell (primalPrev x i) (x i) (dualBlock y i)

/-- The corresponding sum of local envelope values. -/
def assembledValues {M : ℕ} (value : ℝ → ℝ → ℝ) (x : EVec M) : ℝ :=
  ∑ i : Fin M, value (primalPrev x i) (x i)

/-- Pointwise local upper bounds sum to the global envelope upper bound. -/
theorem assembledCells_le_assembledValues {M N : ℕ}
    (cell : ℝ → ℝ → ChainPoint N → ℝ) (value : ℝ → ℝ → ℝ)
    (hupper : ∀ s t y, cell s t y ≤ value s t)
    (x : EVec M) (y : EVec (M * N)) :
    assembledCells cell x y ≤ assembledValues value x := by
  unfold assembledCells assembledValues
  exact Finset.sum_le_sum fun i _ ↦ hupper _ _ _

/-- Explicitly assemble independent local maximizing witnesses. -/
def assembledDualMaximizer {M N : ℕ}
    (witness : ℝ → ℝ → ChainPoint N) (x : EVec M) : EVec (M * N) :=
  flattenDualBlocks fun i ↦ witness (primalPrev x i) (x i)

@[simp] theorem dualBlock_assembledDualMaximizer {M N : ℕ}
    (witness : ℝ → ℝ → ChainPoint N) (x : EVec M) (i : Fin M) :
    dualBlock (assembledDualMaximizer witness x) i =
      witness (primalPrev x i) (x i) := by
  simp [assembledDualMaximizer]

/-- The global witness attains the sum of local envelope values. -/
theorem assembledCells_at_maximizer {M N : ℕ}
    (cell : ℝ → ℝ → ChainPoint N → ℝ) (value : ℝ → ℝ → ℝ)
    (witness : ℝ → ℝ → ChainPoint N)
    (hattain : ∀ s t, cell s t (witness s t) = value s t)
    (x : EVec M) :
    assembledCells cell x (assembledDualMaximizer witness x) =
      assembledValues value x := by
  unfold assembledCells assembledValues
  apply Finset.sum_congr rfl
  intro i _
  rw [dualBlock_assembledDualMaximizer, hattain]

/-- A finite-dimensional maximum certificate, stated without a choice or
supremum: every point is bounded above and the displayed point attains it. -/
theorem finite_separable_envelope {M N : ℕ}
    (cell : ℝ → ℝ → ChainPoint N → ℝ) (value : ℝ → ℝ → ℝ)
    (witness : ℝ → ℝ → ChainPoint N)
    (hupper : ∀ s t y, cell s t y ≤ value s t)
    (hattain : ∀ s t, cell s t (witness s t) = value s t)
    (x : EVec M) :
    (∀ y : EVec (M * N),
      assembledCells cell x y ≤ assembledValues value x) ∧
    assembledCells cell x (assembledDualMaximizer witness x) =
      assembledValues value x := by
  exact ⟨assembledCells_le_assembledValues cell value hupper x,
    assembledCells_at_maximizer cell value witness hattain x⟩

/-! ## Exact identification with the outer Carmon chain -/

/-- The manuscript's two-variable Carmon interaction `h(s,t)`, named here
to avoid pre-empting the analytic activation module's public name. -/
def assemblyCarmonInteraction (s t : ℝ) : ℝ :=
  carmonPsi (-s) * carmonPhi (-t) - carmonPsi s * carmonPhi t

theorem assemblyCarmonInteraction_primalPrev {M : ℕ}
    (x : EVec M) (i : Fin M) :
    assemblyCarmonInteraction (primalPrev x i) (x i) = carmonTerm x i := by
  by_cases hi : i.1 = 0
  · rw [assemblyCarmonInteraction, primalPrev, dif_pos hi, carmonTerm, dif_pos hi]
    rw [carmonPsi_of_le_half (by norm_num : (-1 : ℝ) ≤ 1 / 2)]
    simp
  · simp [assemblyCarmonInteraction, primalPrev, carmonTerm, hi]

/-- The finite local-value sum is definitionally the paper's Carmon chain. -/
theorem assembledValues_assemblyCarmonInteraction (M : ℕ) (x : EVec M) :
    assembledValues assemblyCarmonInteraction x = carmonF M x := by
  unfold assembledValues carmonF
  apply Finset.sum_congr rfl
  intro i _
  exact assemblyCarmonInteraction_primalPrev x i

/-! ## Ordered joint coordinates -/

/-- Assemble the interleaved vector
`(y⁽¹⁾₁,...,y⁽¹⁾_N,x₁,...,y⁽ᴹ⁾₁,...,y⁽ᴹ⁾_N,x_M)` from the
canonical primal and flat-dual vectors. -/
def assembleOrdered {M N : ℕ} (x : EVec M) (y : EVec (M * N)) :
    EVec (M * (N + 1)) := fun k ↦
  let ij := finProdFinEquiv.symm k
  if hj : ij.2.1 < N then
    y (finProdFinEquiv (ij.1, ⟨ij.2.1, hj⟩))
  else
    x ij.1

@[simp] theorem orderedPrimal_assembleOrdered {M N : ℕ}
    (x : EVec M) (y : EVec (M * N)) :
    orderedPrimal (assembleOrdered x y) = x := by
  funext i
  simp [orderedPrimal, assembleOrdered]

@[simp] theorem orderedDual_assembleOrdered {M N : ℕ}
    (x : EVec M) (y : EVec (M * N)) :
    orderedDual (assembleOrdered x y) = y := by
  funext k
  simp only [orderedDual, assembleOrdered, Equiv.symm_apply_apply]
  have hj : ((finProdFinEquiv.symm k).2.castSucc).1 < N :=
    (finProdFinEquiv.symm k).2.isLt
  rw [dif_pos hj]
  have hsecond :
      (⟨((finProdFinEquiv.symm k).2.castSucc).1, hj⟩ : Fin N) =
        (finProdFinEquiv.symm k).2 := Fin.ext rfl
  rw [hsecond, finProdFinEquiv.apply_symm_apply]

/-- In the interleaved order, the coordinate at within-block position `j<N`
is the corresponding dual coordinate. -/
theorem assembleOrdered_dual_apply {M N : ℕ} (x : EVec M)
    (y : EVec (M * N)) (i : Fin M) (j : Fin N) :
    assembleOrdered x y (finProdFinEquiv (i, j.castSucc)) =
      y (finProdFinEquiv (i, j)) := by
  simp [assembleOrdered]

/-- In the interleaved order, the last coordinate of block `i` is `xᵢ`. -/
theorem assembleOrdered_primal_apply {M N : ℕ} (x : EVec M)
    (y : EVec (M * N)) (i : Fin M) :
    assembleOrdered x y (finProdFinEquiv (i, Fin.last N)) = x i := by
  unfold assembleOrdered
  simp

/-- Terminal-coordinate clause of Proposition 5.3, transported to the joint
interleaved vector. -/
theorem assembleOrdered_last_eq_primal_last {M N : ℕ} (hM : 0 < M)
    (x : EVec M) (y : EVec (M * N)) :
    assembleOrdered x y
        ⟨M * (N + 1) - 1,
          Nat.sub_lt (Nat.mul_pos hM (Nat.succ_pos N)) (by omega)⟩ =
      x (carmonLastIndex M hM) := by
  have h := orderedPrimal_last_eq_joint_last hM (assembleOrdered x y)
  rw [orderedPrimal_assembleOrdered] at h
  simpa [carmonLastIndex] using h.symm

end

end NCPLRevised
