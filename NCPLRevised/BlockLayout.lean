/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.ZeroChain

/-!
# Interleaved primal-dual block layout

The manuscript orders each stage as
`y₁⁽ⁱ⁾, ..., y_N⁽ⁱ⁾, xᵢ`.  These projections separate the primal and dual
parts of a joint reordered vector.  In particular, the last joint coordinate
is the last primal coordinate.
-/

namespace NCPLRevised

noncomputable section

def orderedPrimal {M N : ℕ} (z : EVec (M * (N + 1))) : EVec M :=
  fun i ↦ z (finProdFinEquiv (i, Fin.last N))

def orderedDual {M N : ℕ} (z : EVec (M * (N + 1))) : EVec (M * N) :=
  fun k ↦
    let p := finProdFinEquiv.symm k
    z (finProdFinEquiv (p.1, p.2.castSucc))

theorem finProdFinEquiv_val {a b : ℕ} (i : Fin a) (j : Fin b) :
    (finProdFinEquiv (i, j)).1 = i.1 * b + j.1 := by
  change j.1 + b * i.1 = i.1 * b + j.1
  ac_rfl

@[simp] theorem orderedPrimal_apply {M N : ℕ}
    (z : EVec (M * (N + 1))) (i : Fin M) :
    orderedPrimal z i = z (finProdFinEquiv (i, Fin.last N)) := rfl

theorem orderedPrimal_last_eq_joint_last {M N : ℕ} (hM : 0 < M)
    (z : EVec (M * (N + 1))) :
    orderedPrimal z ⟨M - 1, Nat.sub_lt hM (by omega)⟩ =
      z ⟨M * (N + 1) - 1,
        Nat.sub_lt (Nat.mul_pos hM (Nat.succ_pos N)) (by omega)⟩ := by
  unfold orderedPrimal
  congr 1
  apply Fin.ext
  rw [finProdFinEquiv_val]
  simp only [Fin.val_last]
  have hMdecomp : M - 1 + 1 = M := Nat.sub_add_cancel (by omega)
  calc
    (M - 1) * (N + 1) + N =
        (M - 1) * (N + 1) + (N + 1) - 1 := by omega
    _ = ((M - 1) + 1) * (N + 1) - 1 := by
      simp [Nat.add_mul]
    _ = M * (N + 1) - 1 := by rw [hMdecomp]

end

end NCPLRevised
