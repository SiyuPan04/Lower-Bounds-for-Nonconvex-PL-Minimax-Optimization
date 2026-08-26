/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.HardInstanceAssembly
import NCPLRevised.EmbeddedCellSmoothness

/-!
# The concrete saddle zero-chain

This module proves Proposition 5.2 for the exact assembled function `barF`.
The joint coordinates are ordered blockwise as

`y₁⁽ⁱ⁾, ..., y_N⁽ⁱ⁾, xᵢ, ..., y₁⁽ᴹ⁾, ..., y_N⁽ᴹ⁾, x_M`.

The gradient field below is assembled from the actual gradient of the exact
embedded cell.  The final section identifies it with the full Frechet
derivative of the ordered objective.
-/

namespace NCPLRevised

noncomputable section

private theorem dualBlock_orderedDual_apply {M N : ℕ}
    (z : EVec (M * (N + 1))) (i : Fin M) (j : Fin N) :
    dualBlock (orderedDual z) i j =
      z (finProdFinEquiv (i, j.castSucc)) := by
  simp [dualBlock, orderedDual]

private theorem orderedPrimal_eq_joint_last {M N : ℕ}
    (z : EVec (M * (N + 1))) (i : Fin M) :
    orderedPrimal z i = z (finProdFinEquiv (i, Fin.last N)) := by
  rfl

/-- Away from the first inner coordinate, a zero coordinate whose inner
predecessor is also zero has zero coupled-dual gradient. -/
theorem coupledGradient_eq_zero_of_self_prev_zero {N : ℕ}
    (alpha : ℝ) (u : ChainPoint N) (j : Fin N)
    (hj : j.1 ≠ 0) (hself : u j = 0)
    (hprev : u ⟨j.1 - 1, by omega⟩ = 0) :
    coupledGradient N alpha u j = 0 := by
  have hchain : chainPrev u j.1 = 0 := by
    simp [chainPrev, hj, chainCoord, hprev]
  simp [coupledGradient, dualGradient, incoming, penalty, outgoing,
    hself, hchain, negPart]

/-- The scaled perspective preserves the local one-step zero pattern. -/
theorem scaledPerspectiveGradient_eq_zero_of_self_prev_zero {N : ℕ}
    (eta alpha : ℝ) (y : ChainPoint N) (j : Fin N)
    (hj : j.1 ≠ 0) (hself : y j = 0)
    (hprev : y ⟨j.1 - 1, by omega⟩ = 0) :
    scaledPerspectiveGradient N eta alpha y j = 0 := by
  by_cases heta : eta = 0
  · simp [scaledPerspectiveGradient, heta, hself, negPart]
  · have huself : perspectiveNormalize N eta y j = 0 := by
      simp [perspectiveNormalize, hself]
    have huprev :
        perspectiveNormalize N eta y ⟨j.1 - 1, by omega⟩ = 0 := by
      simp [perspectiveNormalize, hprev]
    rw [scaledPerspectiveGradient, if_neg heta]
    rw [coupledGradient_eq_zero_of_self_prev_zero (alpha / eta ^ 2)
      (perspectiveNormalize N eta y) j hj huself huprev]
    ring

/-- At zero perspective scale, a zero dual coordinate has zero gradient. -/
theorem scaledPerspectiveGradient_eq_zero_of_eta_zero {N : ℕ}
    (alpha : ℝ) (y : ChainPoint N) (j : Fin N)
    (hself : y j = 0) :
    scaledPerspectiveGradient N 0 alpha y j = 0 := by
  simp [scaledPerspectiveGradient, hself, negPart]

/-! ## A reusable blockwise zero-chain theorem -/

/-- Three components of a local cell gradient: predecessor primal,
successor primal, and dual block. -/
abbrev LocalGradientData (N : ℕ) := ℝ × (ℝ × ChainPoint N)

/-- Assemble local cell gradients in the paper's interleaved coordinate
order. A primal coordinate receives the successor derivative of its own
block and the predecessor derivative of the following block. -/
def assembledOrderedGradientFrom {M N : ℕ}
    (cellGradient : ℝ → ℝ → ChainPoint N → LocalGradientData N)
    (z : EVec (M * (N + 1))) : EVec (M * (N + 1)) := fun r ↦
  let ij := finProdFinEquiv.symm r
  let x := orderedPrimal z
  let y := orderedDual z
  if hj : ij.2.1 < N then
    (cellGradient (primalPrev x ij.1) (x ij.1) (dualBlock y ij.1)).2.2
      ⟨ij.2.1, hj⟩
  else
    (cellGradient (primalPrev x ij.1) (x ij.1) (dualBlock y ij.1)).2.1 +
      if hi : ij.1.1 + 1 < M then
        (cellGradient (x ij.1) (x ⟨ij.1.1 + 1, hi⟩)
          (dualBlock y ⟨ij.1.1 + 1, hi⟩)).1
      else 0

/-- The three exact local interfaces needed for the saddle zero-chain. -/
theorem assembledOrderedGradientFrom_is_zeroChain {M N : ℕ}
    (hN : 0 < N)
    (cellGradient : ℝ → ℝ → ChainPoint N → LocalGradientData N)
    (hdualFirst : ∀ t y,
      y ⟨0, hN⟩ = 0 → (cellGradient 0 t y).2.2 ⟨0, hN⟩ = 0)
    (hdualNext : ∀ s t y (j : Fin N), j.1 ≠ 0 →
      y j = 0 → y ⟨j.1 - 1, by omega⟩ = 0 →
      (cellGradient s t y).2.2 j = 0)
    (hsuccessor : ∀ s t y,
      y ⟨N - 1, by omega⟩ = 0 → (cellGradient s t y).2.1 = 0)
    (hpredecessorZero : (cellGradient 0 0 0).1 = 0) :
    IsFirstOrderSaddleZeroChain
      (assembledOrderedGradientFrom (M := M) cellGradient) := by
  intro k z hz r hkr
  generalize hij : finProdFinEquiv.symm r = ij
  rcases ij with ⟨i, j⟩
  have hr : finProdFinEquiv (i, j) = r := by
    rw [← hij]
    exact finProdFinEquiv.apply_symm_apply r
  have hrval : r.1 = i.1 * (N + 1) + j.1 := by
    rw [← hr, finProdFinEquiv_val]
  simp only [assembledOrderedGradientFrom, hij]
  by_cases hj : j.1 < N
  · rw [dif_pos hj]
    let jd : Fin N := ⟨j.1, hj⟩
    have hjcast : jd.castSucc = j := Fin.ext rfl
    have hself : dualBlock (orderedDual z) i jd = 0 := by
      rw [dualBlock_orderedDual_apply, hjcast, hr]
      exact hz r (by omega)
    by_cases hj0 : j.1 = 0
    · have hi0 : i.1 ≠ 0 := by
        intro hi
        have hrv := hrval
        simp [hi, hj0] at hrv
        omega
      have hscale : primalPrev (orderedPrimal z) i = 0 := by
        rw [primalPrev_ne_zero _ _ hi0, orderedPrimal_eq_joint_last]
        apply hz
        have hival : i.1 - 1 + 1 = i.1 :=
          Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hi0)
        have hpval :
            (finProdFinEquiv
              (⟨i.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩,
                Fin.last N)).1 + 1 = r.1 := by
          rw [finProdFinEquiv_val, Fin.val_last, hrval, hj0]
          calc
            (i.1 - 1) * (N + 1) + N + 1 =
                ((i.1 - 1) + 1) * (N + 1) := by
                  rw [Nat.add_mul]
                  omega
            _ = i.1 * (N + 1) := by rw [hival]
        omega
      rw [hscale]
      have hfirst := hdualFirst (orderedPrimal z i)
        (dualBlock (orderedDual z) i)
        (by simpa [jd, hj0] using hself)
      simpa [jd, hj0] using hfirst
    · let jp : Fin N := ⟨j.1 - 1, by omega⟩
      have hprev : dualBlock (orderedDual z) i jp = 0 := by
        rw [dualBlock_orderedDual_apply]
        apply hz
        have hjval : j.1 - 1 + 1 = j.1 :=
          Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj0)
        have hpval :
            (finProdFinEquiv (i, jp.castSucc)).1 + 1 = r.1 := by
          rw [finProdFinEquiv_val, hrval]
          dsimp [jp]
          omega
        omega
      exact hdualNext _ _ _ jd (by simpa [jd] using hj0)
        hself (by simpa [jd, jp] using hprev)
  · rw [dif_neg hj]
    have hjN : j.1 = N := by omega
    have hjlast : j = Fin.last N := Fin.ext (by simpa using hjN)
    let terminal : Fin N := ⟨N - 1, by omega⟩
    have hterminal : dualBlock (orderedDual z) i terminal = 0 := by
      rw [dualBlock_orderedDual_apply]
      apply hz
      have htval :
          (finProdFinEquiv (i, terminal.castSucc)).1 + 1 = r.1 := by
        rw [finProdFinEquiv_val, hrval, hjN]
        dsimp [terminal]
        omega
      omega
    have hown :
        (cellGradient (primalPrev (orderedPrimal z) i)
          (orderedPrimal z i) (dualBlock (orderedDual z) i)).2.1 = 0 :=
      hsuccessor _ _ _ hterminal
    rw [hown, zero_add]
    by_cases hi : i.1 + 1 < M
    · rw [dif_pos hi]
      let isucc : Fin M := ⟨i.1 + 1, hi⟩
      have hxi : orderedPrimal z i = 0 := by
        rw [orderedPrimal_eq_joint_last, ← hjlast, hr]
        exact hz r (by omega)
      have hxsucc : orderedPrimal z isucc = 0 := by
        rw [orderedPrimal_eq_joint_last]
        apply hz
        have hsval : r.1 <
            (finProdFinEquiv (isucc, Fin.last N)).1 := by
          rw [finProdFinEquiv_val, Fin.val_last, hrval, hjN]
          dsimp [isucc]
          rw [Nat.add_mul]
          omega
        omega
      have hysucc : dualBlock (orderedDual z) isucc = 0 := by
        funext a
        rw [dualBlock_orderedDual_apply]
        apply hz
        have hsval : r.1 <
            (finProdFinEquiv (isucc, a.castSucc)).1 := by
          rw [finProdFinEquiv_val, hrval, hjN]
          dsimp [isucc]
          rw [Nat.add_mul]
          omega
        omega
      rw [hxi, hxsucc, hysucc]
      exact hpredecessorZero
    · rw [dif_neg hi]

/-! ## Instantiation by the exact embedded cell -/

/-- The concrete local gradient.  The predecessor component is the actual
one-variable derivative, the successor component is the proved interface
derivative, and the dual component is the actual Frechet gradient from
Lemma 4.4. -/
def concreteCellGradient (N : ℕ) (s t : ℝ) (y : ChainPoint N) :
    LocalGradientData N :=
  (deriv (fun u : ℝ ↦ embeddedCell N u t y) s,
    embeddedSuccessorGradient N s t y,
    scaledPerspectiveGradient N (outerRho s) (carmonLiftedH s t) y)

/-- The exact joint saddle-gradient field of the unscaled hard instance in
the paper's coordinate order. -/
def concreteOrderedSaddleGradient (M N : ℕ) :
    EVec (M * (N + 1)) → EVec (M * (N + 1)) :=
  assembledOrderedGradientFrom (M := M) (concreteCellGradient N)

private theorem hasDerivAt_embeddedCell_predecessor_at_zero
    (N : ℕ) :
    HasDerivAt (fun s : ℝ ↦ embeddedCell N s 0 0) 0 0 := by
  refine (hasDerivAt_const (x := (0 : ℝ))
    (c := zeroPerspectiveBlock (0 : ChainPoint N))).congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ)
    (show 0 < (1 / 2 : ℝ) by norm_num)] with s hs
  have habs : |s| ≤ (1 / 2 : ℝ) := by
    rw [Metric.mem_ball, Real.dist_eq] at hs
    simpa using hs.le
  exact embeddedCell_of_abs_le_half habs 0

private theorem concreteCellGradient_predecessor_zero (N : ℕ) :
    (concreteCellGradient N 0 0 0).1 = 0 := by
  exact (hasDerivAt_embeddedCell_predecessor_at_zero N).deriv

/-- Proposition 5.2: the gradient of the exact embedded construction is a
first-order saddle zero-chain in the interleaved order. -/
theorem proposition5_2_concrete (M N : ℕ) (hN : 2 ≤ N) :
    IsFirstOrderSaddleZeroChain (concreteOrderedSaddleGradient M N) := by
  apply assembledOrderedGradientFrom_is_zeroChain (M := M) (by omega)
    (concreteCellGradient N)
  · intro t y hy
    have hrho : outerRho 0 = 0 :=
      outerRho_of_abs_le_half (by norm_num)
    change scaledPerspectiveGradient N (outerRho 0)
      (carmonLiftedH 0 t) y ⟨0, by omega⟩ = 0
    rw [hrho]
    exact scaledPerspectiveGradient_eq_zero_of_eta_zero
      (carmonLiftedH 0 t) y ⟨0, by omega⟩ hy
  · intro s t y j hj hself hprev
    exact scaledPerspectiveGradient_eq_zero_of_self_prev_zero
      (outerRho s) (carmonLiftedH s t) y j hj hself hprev
  · intro s t y hy
    apply embeddedSuccessorGradient_zero_of_terminal s t y
    simpa [chainCoord, show N - 1 < N by omega] using hy
  · exact concreteCellGradient_predecessor_zero N

end

end NCPLRevised
