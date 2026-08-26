/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.Gates
import NCPLRevised.Weights

/-!
# The weighted dual chain (Proposition 4.1 and Lemma 4.3)

This file formalizes the finite-dimensional chain from Section 4.1 of
*Lower Bounds for Nonconvex-PL Minimax Optimization*.  Coordinates of a
`ChainPoint N` are zero-based Lean coordinates; coordinate `k` represents
the paper's `y_{k+1}`.  Consequently `omega N k` is the coefficient
`omega_{j-1}` and `omega N (k+1)` is `omega_j` in equations (2) and (7).

`dualGradient` is the explicit field displayed in equation (7).  The main
algebraic theorem `proposition4_1` proves that this field is coordinatewise
nonpositive and satisfies the strengthened weighted PL estimate.  The
separate module `DualChainDerivative` proves that every coordinate of this
field is the actual derivative of `dualChain` under a one-coordinate update,
and bundles those identities into the full Fréchet derivative represented by
the finite dot product with `dualGradient`.
-/

namespace NCPLRevised

noncomputable section

/-- A point of the paper's `R^N`, represented as a finite function. -/
abbrev ChainPoint (N : ℕ) := Fin N → ℝ

/-- Totalized access to a chain coordinate.  Only in-range uses matter. -/
def chainCoord {N : ℕ} (y : ChainPoint N) (j : ℕ) : ℝ :=
  if hj : j < N then y ⟨j, hj⟩ else 0

@[simp] theorem chainCoord_fin {N : ℕ} (y : ChainPoint N) (j : Fin N) :
    chainCoord y j.1 = y j := by
  simp [chainCoord, j.isLt]

/-- The convention `y₀ = 1` from the paper. -/
def chainPrev {N : ℕ} (y : ChainPoint N) (j : ℕ) : ℝ :=
  if j = 0 then 1 else chainCoord y (j - 1)

@[simp] theorem chainPrev_zero {N : ℕ} (y : ChainPoint N) : chainPrev y 0 = 1 := by
  simp [chainPrev]

@[simp] theorem chainPrev_succ {N : ℕ} (y : ChainPoint N) (j : ℕ) :
    chainPrev y (j + 1) = chainCoord y j := by
  simp [chainPrev]

/-- The gate part of the local interaction `d_j`. -/
def gateTerm {N : ℕ} (y : ChainPoint N) (k : Fin N) : ℝ :=
  1 - q (chainPrev y k.1) * p (y k)

/-- The local interaction `d_j` in equation (2). -/
def localInteraction (N : ℕ) (y : ChainPoint N) (k : Fin N) : ℝ :=
  omega N k.1 * gateTerm y k +
    omega N (k.1 + 1) / 2 * (negPart (y k)) ^ 2

/-- The finite-dimensional dual chain `H` from equation (2). -/
def dualChain (N : ℕ) (y : ChainPoint N) : ℝ :=
  ∑ k : Fin N, localInteraction N y k

/-- First nonnegative magnitude in the negative gradient formula (7). -/
def incoming (N : ℕ) (y : ChainPoint N) (k : Fin N) : ℝ :=
  omega N k.1 * q (chainPrev y k.1) * pDeriv (y k)

/-- Second nonnegative magnitude in the negative gradient formula (7). -/
def penalty (N : ℕ) (y : ChainPoint N) (k : Fin N) : ℝ :=
  omega N (k.1 + 1) * negPart (y k)

/-- Third nonnegative magnitude in (7), absent at the terminal coordinate. -/
def outgoing (N : ℕ) (y : ChainPoint N) (k : Fin N) : ℝ :=
  if hk : k.1 + 1 < N then
    omega N (k.1 + 1) * qDeriv (y k) * p (y ⟨k.1 + 1, hk⟩)
  else 0

/-- The explicit coordinate field in equation (7). -/
def dualGradient (N : ℕ) (y : ChainPoint N) : ChainPoint N := fun k ↦
  -(incoming N y k + penalty N y k + outgoing N y k)

/-- The square of the weighted dual norm `||g||_{*,omega}`. -/
def weightedDualNormSq (N : ℕ) (g : ChainPoint N) : ℝ :=
  ∑ k : Fin N, (g k) ^ 2 / omega N (k.1 + 1)

/-- The weighted dual norm itself. -/
def weightedDualNorm (N : ℕ) (g : ChainPoint N) : ℝ :=
  Real.sqrt (weightedDualNormSq N g)

open Filter Set in
private theorem hasDerivAt_negPartSq_zero :
    HasDerivAt (fun t : ℝ ↦ negPart t ^ 2) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hc : Continuous (fun t : ℝ ↦ min t 0) :=
    (continuous_id : Continuous fun t : ℝ ↦ t).min continuous_const
  have hmin : Tendsto (fun t : ℝ ↦ min t 0)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    simpa using hc.tendsto 0
  apply hmin.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by simpa using ht
  symm
  by_cases hle : t ≤ 0
  · rw [min_eq_left hle]
    unfold slope
    simp only [sub_zero, vsub_eq_sub, smul_eq_mul]
    rw [negPart_of_nonpos hle, negPart_of_nonneg (le_refl 0)]
    field_simp [ht0]
    ring
  · have hpos : 0 < t := lt_of_not_ge hle
    rw [min_eq_right (le_of_lt hpos)]
    unfold slope
    simp only [sub_zero, vsub_eq_sub, smul_eq_mul]
    rw [negPart_of_nonneg hpos.le, negPart_of_nonneg (le_refl 0)]
    norm_num

/-- The squared negative part is differentiable even at its splice point. -/
theorem hasDerivAt_negPartSq (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ negPart s ^ 2) (-2 * negPart t) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have heq : (fun s : ℝ ↦ negPart s ^ 2) =ᶠ[nhds t] (fun s : ℝ ↦ s ^ 2) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      rw [negPart_of_nonpos (le_of_lt hs)]
      ring
    have h := heq.hasDerivAt_iff.mpr (hasDerivAt_pow 2 t)
    rw [negPart_of_nonpos (le_of_lt ht)]
    simpa using h
  · simpa [negPart] using hasDerivAt_negPartSq_zero
  · have heq : (fun s : ℝ ↦ negPart s ^ 2) =ᶠ[nhds t] (fun _s : ℝ ↦ 0) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      rw [negPart_of_nonneg (le_of_lt hs)]
      norm_num
    have h := heq.hasDerivAt_iff.mpr (hasDerivAt_const (x := t) (c := (0 : ℝ)))
    rw [negPart_of_nonneg (le_of_lt ht)]
    simpa using h

private theorem chainPrev_update_self {N : ℕ} (y : ChainPoint N)
    (k : Fin N) (t : ℝ) :
    chainPrev (Function.update y k t) k.1 = chainPrev y k.1 := by
  by_cases hk0 : k.1 = 0
  · simp [chainPrev, hk0]
  · have hpredN : k.1 - 1 < N := by omega
    let pred : Fin N := ⟨k.1 - 1, hpredN⟩
    have hne : pred ≠ k := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [pred] at hv
      omega
    simp [chainPrev, hk0, chainCoord, hpredN, pred, hne]

private theorem chainPrev_update_succ {N : ℕ} (y : ChainPoint N)
    (k i : Fin N) (t : ℝ) (hi : i.1 = k.1 + 1) :
    chainPrev (Function.update y k t) i.1 = t := by
  have hkN : k.1 < N := k.isLt
  simp [chainPrev, chainCoord, hi, hkN]

private theorem chainPrev_update_other {N : ℕ} (y : ChainPoint N)
    (k i : Fin N) (t : ℝ) (hi : i.1 ≠ k.1 + 1) :
    chainPrev (Function.update y k t) i.1 = chainPrev y i.1 := by
  by_cases hi0 : i.1 = 0
  · simp [chainPrev, hi0]
  · have hpredN : i.1 - 1 < N := by omega
    let pred : Fin N := ⟨i.1 - 1, hpredN⟩
    have hne : pred ≠ k := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [pred] at hv
      omega
    simp [chainPrev, hi0, chainCoord, hpredN, pred, hne]

private theorem negPart_nonneg' (t : ℝ) : 0 ≤ negPart t := by
  simp [negPart]

theorem incoming_nonneg {N : ℕ} (hN : 0 < N) (y : ChainPoint N) (k : Fin N) :
    0 ≤ incoming N y k := by
  unfold incoming
  exact mul_nonneg
    (mul_nonneg (omega_pos hN).le (q_nonneg _)) (pDeriv_nonneg _)

theorem penalty_nonneg {N : ℕ} (hN : 0 < N) (y : ChainPoint N) (k : Fin N) :
    0 ≤ penalty N y k := by
  unfold penalty
  exact mul_nonneg (omega_pos hN).le (negPart_nonneg' _)

theorem outgoing_nonneg {N : ℕ} (hN : 0 < N) (y : ChainPoint N) (k : Fin N) :
    0 ≤ outgoing N y k := by
  unfold outgoing
  split_ifs with hk
  · exact mul_nonneg
      (mul_nonneg (omega_pos hN).le (qDeriv_nonneg _)) (p_nonneg _)
  · exact le_rfl

/-- The sign assertion following equation (7). -/
theorem dualGradient_nonpos {N : ℕ} (hN : 0 < N) (y : ChainPoint N) (k : Fin N) :
    dualGradient N y k ≤ 0 := by
  rw [dualGradient]
  exact neg_nonpos.mpr <|
    add_nonneg (add_nonneg (incoming_nonneg hN y k) (penalty_nonneg hN y k))
      (outgoing_nonneg hN y k)

theorem weightedDualNormSq_nonneg {N : ℕ} (hN : 0 < N) (g : ChainPoint N) :
    0 ≤ weightedDualNormSq N g := by
  unfold weightedDualNormSq
  exact Finset.sum_nonneg fun k _ ↦
    div_nonneg (sq_nonneg _) (omega_pos hN).le

theorem weightedDualNorm_sq {N : ℕ} (hN : 0 < N) (g : ChainPoint N) :
    weightedDualNorm N g ^ 2 = weightedDualNormSq N g := by
  rw [weightedDualNorm, Real.sq_sqrt (weightedDualNormSq_nonneg hN g)]

/-- The coefficient `omega_k^2 / omega_{k+1}` is at least `1/N`.
It equals `1/N` off the terminal coordinate and equals one at the terminal
coordinate. -/
theorem omega_ratio_lower {N j : ℕ} (hN : 2 ≤ N) (hj : j < N) :
    (N : ℝ)⁻¹ ≤ omega N j ^ 2 / omega N (j + 1) := by
  have hNpos : 0 < N := by omega
  by_cases hnext : j + 1 < N
  · have hrec := omega_pred_sq_div (N := N) (j := j + 1) hNpos (by omega) hnext
    simpa using hrec.ge
  · have hjlast : j = N - 1 := by omega
    subst j
    have hNone : 1 ≤ N := by omega
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hNone
    simpa [omega_penultimate hNpos, Nat.sub_add_cancel hNone] using
      ((inv_le_one₀ (by positivity : (0 : ℝ) < N)).2 hNreal)

/-- The local energy used in equation (9). -/
def basicEnergy (N : ℕ) (y : ChainPoint N) : ℝ :=
  ∑ k : Fin N,
    ((q (chainPrev y k.1) * pDeriv (y k)) ^ 2 + (negPart (y k)) ^ 2)

/-- The weighted negative-part energy appearing in `H`. -/
def penaltyEnergy (N : ℕ) (y : ChainPoint N) : ℝ :=
  ∑ k : Fin N, omega N (k.1 + 1) * (negPart (y k)) ^ 2

theorem basicEnergy_nonneg (N : ℕ) (y : ChainPoint N) :
    0 ≤ basicEnergy N y := by
  unfold basicEnergy
  exact Finset.sum_nonneg fun k _ ↦ add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem penaltyEnergy_nonneg {N : ℕ} (hN : 0 < N) (y : ChainPoint N) :
    0 ≤ penaltyEnergy N y := by
  unfold penaltyEnergy
  exact Finset.sum_nonneg fun k _ ↦
    mul_nonneg (omega_pos hN).le (sq_nonneg _)

private theorem gradient_sq_ge_components {N : ℕ} (hN : 0 < N)
    (y : ChainPoint N) (k : Fin N) :
    incoming N y k ^ 2 + penalty N y k ^ 2 ≤ dualGradient N y k ^ 2 := by
  have hi := incoming_nonneg hN y k
  have hp := penalty_nonneg hN y k
  have ho := outgoing_nonneg hN y k
  rw [dualGradient]
  nlinarith [sq_nonneg (incoming N y k + penalty N y k + outgoing N y k)]

/-- Pointwise form of equation (9). -/
theorem basicEnergy_term_le_gradient_term {N : ℕ} (hN : 2 ≤ N)
    (y : ChainPoint N) (k : Fin N) :
    (N : ℝ)⁻¹ *
        ((q (chainPrev y k.1) * pDeriv (y k)) ^ 2 + (negPart (y k)) ^ 2) ≤
      dualGradient N y k ^ 2 / omega N (k.1 + 1) := by
  have hNpos : 0 < N := by omega
  let wp := omega N k.1
  let ws := omega N (k.1 + 1)
  let a := q (chainPrev y k.1) * pDeriv (y k)
  let b := negPart (y k)
  have hratio : (N : ℝ)⁻¹ ≤ wp ^ 2 / ws := by
    simpa [wp, ws] using omega_ratio_lower hN k.isLt
  have hwsLower : (N : ℝ)⁻¹ ≤ ws := by
    simpa [ws] using omega_lower (N := N) (j := k.1 + 1) hNpos
  have hwsPos : 0 < ws := by
    simpa [ws] using omega_pos (N := N) (j := k.1 + 1) hNpos
  have hcomp := gradient_sq_ge_components hNpos y k
  calc
    (N : ℝ)⁻¹ * (a ^ 2 + b ^ 2)
        = (N : ℝ)⁻¹ * a ^ 2 + (N : ℝ)⁻¹ * b ^ 2 := by ring
    _ ≤ (wp ^ 2 / ws) * a ^ 2 + ws * b ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hratio (sq_nonneg a))
        (mul_le_mul_of_nonneg_right hwsLower (sq_nonneg b))
    _ = (incoming N y k ^ 2 + penalty N y k ^ 2) / ws := by
      dsimp [wp, ws, a, b]
      unfold incoming penalty
      field_simp [ne_of_gt hwsPos]
    _ ≤ dualGradient N y k ^ 2 / ws := by
      exact div_le_div_of_nonneg_right hcomp hwsPos.le

/-- Equation (9), summed over all coordinates. -/
theorem basicEnergy_le_weightedGradient {N : ℕ} (hN : 2 ≤ N)
    (y : ChainPoint N) :
    (N : ℝ)⁻¹ * basicEnergy N y ≤
      weightedDualNormSq N (dualGradient N y) := by
  rw [basicEnergy, weightedDualNormSq, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ ↦ basicEnergy_term_le_gradient_term hN y k

/-- The negative-part energy is controlled with coefficient one, as in (8). -/
theorem penaltyEnergy_le_weightedGradient {N : ℕ} (hN : 2 ≤ N)
    (y : ChainPoint N) :
    penaltyEnergy N y ≤ weightedDualNormSq N (dualGradient N y) := by
  have hNpos : 0 < N := by omega
  rw [penaltyEnergy, weightedDualNormSq]
  apply Finset.sum_le_sum
  intro k _
  let ws := omega N (k.1 + 1)
  have hwsPos : 0 < ws := by
    simpa [ws] using omega_pos (N := N) (j := k.1 + 1) hNpos
  have hcomp := gradient_sq_ge_components hNpos y k
  have hpen : penalty N y k ^ 2 ≤ dualGradient N y k ^ 2 := by
    nlinarith [sq_nonneg (incoming N y k)]
  calc
    omega N (k.1 + 1) * negPart (y k) ^ 2
        = penalty N y k ^ 2 / ws := by
          dsimp [ws]
          unfold penalty
          field_simp [ne_of_gt hwsPos]
    _ ≤ dualGradient N y k ^ 2 / ws :=
      div_le_div_of_nonneg_right hpen hwsPos.le

/-- The finite-chain selection argument in the proof of Proposition 4.1.
For each coordinate, its activation deficit is controlled by sixteen times
the unweighted local energy. -/
theorem activation_deficit_le_basicEnergy {N : ℕ} (_hN : 0 < N)
    (y : ChainPoint N) (k : Fin N) :
    1 - q (y k) ≤ 16 * basicEnergy N y := by
  let δ : ℝ := 1 - q (y k)
  have hδ0 : 0 ≤ δ := by dsimp [δ]; linarith [q_le_one (y k)]
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith [q_nonneg (y k)]
  let P : ℕ → Prop := fun j ↦ δ / 2 ≤ 1 - q (chainCoord y j)
  have hPk : P k.1 := by
    dsimp [P, δ]
    rw [chainCoord_fin]
    linarith
  have hex : ∃ j, P j := ⟨k.1, hPk⟩
  let j := Nat.find hex
  have hjle : j ≤ k.1 := Nat.find_le hPk
  have hjN : j < N := lt_of_le_of_lt hjle k.isLt
  have hPj : P j := Nat.find_spec hex
  have hprev : (1 / 2 : ℝ) ≤ q (chainPrev y j) := by
    by_cases hj0 : j = 0
    · norm_num [chainPrev, hj0]
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      have hnot : ¬ P (j - 1) := Nat.find_min hex (Nat.pred_lt hj0)
      have hlt : 1 - q (chainCoord y (j - 1)) < δ / 2 := by
        exact lt_of_not_ge hnot
      rw [chainPrev]
      simp only [hj0, if_false]
      linarith
  let jf : Fin N := ⟨j, hjN⟩
  have hscalar := one_sub_q_le (chainCoord y j)
  have hqSq : (1 / 4 : ℝ) ≤ q (chainPrev y j) ^ 2 := by
    nlinarith [sq_nonneg (q (chainPrev y j) - 1 / 2)]
  have hpSq :
      pDeriv (chainCoord y j) ^ 2 ≤
        4 * (q (chainPrev y j) * pDeriv (chainCoord y j)) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hqSq
      (sq_nonneg (pDeriv (chainCoord y j)))
    nlinarith
  have hlocal :
      δ ≤ 16 *
        ((q (chainPrev y j) * pDeriv (chainCoord y j)) ^ 2 +
          negPart (chainCoord y j) ^ 2) := by
    dsimp [P] at hPj
    nlinarith
  have hterm :
      (q (chainPrev y jf.1) * pDeriv (y jf)) ^ 2 + (negPart (y jf)) ^ 2 ≤
        basicEnergy N y := by
    unfold basicEnergy
    have hsingle := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun i : Fin N ↦
        (q (chainPrev y i.1) * pDeriv (y i)) ^ 2 + (negPart (y i)) ^ 2)
      (fun i _ ↦ add_nonneg (sq_nonneg _) (sq_nonneg _))
      (Finset.mem_univ jf)
    simpa using hsingle
  dsimp [δ] at hlocal ⊢
  have hcoord : chainCoord y j = y jf := by simp [jf, chainCoord, hjN]
  rw [hcoord] at hlocal
  dsimp [jf] at hterm
  exact hlocal.trans (mul_le_mul_of_nonneg_left hterm (by norm_num))

/-- The activation deficit estimate in the paper: `1-q(y_k) <= 16 N D`. -/
theorem activation_deficit_le_weightedGradient {N : ℕ} (hN : 2 ≤ N)
    (y : ChainPoint N) (k : Fin N) :
    1 - q (y k) ≤
      16 * (N : ℝ) * weightedDualNormSq N (dualGradient N y) := by
  have hNreal : 0 < (N : ℝ) := by positivity
  have hbase := basicEnergy_le_weightedGradient hN y
  have hbase' : basicEnergy N y ≤
      weightedDualNormSq N (dualGradient N y) * (N : ℝ) := by
    apply (div_le_iff₀ hNreal).mp
    simpa [div_eq_mul_inv, mul_comm] using hbase
  have hact := activation_deficit_le_basicEnergy (by omega) y k
  nlinarith [weightedDualNormSq_nonneg (by omega : 0 < N) (dualGradient N y)]

private theorem predecessor_deficit_le_basicEnergy {N : ℕ} (hN : 0 < N)
    (y : ChainPoint N) (k : Fin N) :
    1 - q (chainPrev y k.1) ≤ 16 * basicEnergy N y := by
  cases hk : k.1 with
  | zero =>
      simp [chainPrev, basicEnergy_nonneg]
  | succ j =>
      have hjN : j < N := by omega
      let i : Fin N := ⟨j, hjN⟩
      have h := activation_deficit_le_basicEnergy hN y i
      simpa [chainPrev, hk, i, chainCoord, hjN] using h

/-- Each local gate is controlled by the two adjacent activation deficits. -/
theorem gateTerm_le_basicEnergy {N : ℕ} (hN : 0 < N)
    (y : ChainPoint N) (k : Fin N) :
    gateTerm y k ≤ 32 * basicEnergy N y := by
  let u := chainPrev y k.1
  let v := y k
  have hfactor : q u * (1 - p v) ≤ 1 - q v := by
    have h₁ : q u * (1 - p v) ≤ 1 * (1 - p v) :=
      mul_le_mul_of_nonneg_right (q_le_one u) (sub_nonneg.mpr (p_le_one v))
    have h₂ : 1 - p v ≤ 1 - q v := sub_le_sub_left (p_ge_q v) 1
    linarith
  have hprev := predecessor_deficit_le_basicEnergy hN y k
  have hcurr := activation_deficit_le_basicEnergy hN y k
  unfold gateTerm
  dsimp [u, v] at hfactor
  have hid :
      1 - q (chainPrev y k.1) * p (y k) =
        (1 - q (chainPrev y k.1)) +
          q (chainPrev y k.1) * (1 - p (y k)) := by ring
  rw [hid]
  linarith

theorem gateTerm_nonneg {N : ℕ} (y : ChainPoint N) (k : Fin N) :
    0 ≤ gateTerm y k := by
  unfold gateTerm
  have hprod : q (chainPrev y k.1) * p (y k) ≤ 1 * 1 :=
    mul_le_mul (q_le_one _) (p_le_one _) (p_nonneg _) (by norm_num)
  linarith

theorem localInteraction_nonneg {N : ℕ} (hN : 0 < N)
    (y : ChainPoint N) (k : Fin N) :
    0 ≤ localInteraction N y k := by
  unfold localInteraction
  exact add_nonneg
    (mul_nonneg (omega_pos hN).le (gateTerm_nonneg y k))
    (mul_nonneg (div_nonneg (omega_pos hN).le (by norm_num)) (sq_nonneg _))

theorem dualChain_nonneg {N : ℕ} (hN : 0 < N) (y : ChainPoint N) :
    0 ≤ dualChain N y := by
  unfold dualChain
  exact Finset.sum_nonneg fun k _ ↦ localInteraction_nonneg hN y k

private theorem dualChain_eq_gate_add_penalty {N : ℕ} (y : ChainPoint N) :
    dualChain N y =
      (∑ k : Fin N, omega N k.1 * gateTerm y k) + (1 / 2 : ℝ) * penaltyEnergy N y := by
  unfold dualChain localInteraction penaltyEnergy
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Proposition 4.1, inequality (6), for the explicit field (7). -/
theorem strengthened_weighted_PL {N : ℕ} (hN : 2 ≤ N) (y : ChainPoint N) :
    dualChain N y + 10 * (1 - q (chainCoord y (N - 1))) ≤
      320 * (N : ℝ) * weightedDualNormSq N (dualGradient N y) := by
  have hNpos : 0 < N := by omega
  let D := weightedDualNormSq N (dualGradient N y)
  let E := basicEnergy N y
  have hD0 : 0 ≤ D := weightedDualNormSq_nonneg hNpos _
  have hE0 : 0 ≤ E := basicEnergy_nonneg N y
  have hNreal : 0 < (N : ℝ) := by positivity
  have hED0 := basicEnergy_le_weightedGradient hN y
  have hED : E ≤ D * (N : ℝ) := by
    apply (div_le_iff₀ hNreal).mp
    simpa [E, D, div_eq_mul_inv, mul_comm] using hED0
  have hgatePoint (k : Fin N) : gateTerm y k ≤ 32 * E := by
    simpa [E] using gateTerm_le_basicEnergy hNpos y k
  have hgateSum :
      (∑ k : Fin N, omega N k.1 * gateTerm y k) ≤ 96 * E := by
    calc
      (∑ k : Fin N, omega N k.1 * gateTerm y k)
          ≤ ∑ k : Fin N, omega N k.1 * (32 * E) := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_left (hgatePoint k) (omega_pos hNpos).le
      _ = 32 * E * (∑ k : Fin N, omega N k.1) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ ≤ 32 * E * 3 := by
            apply mul_le_mul_of_nonneg_left
            · simpa using (show (∑ k : Fin N, omega N k.1) ≤ 3 by
                have hs := sum_omega_lt_three hN
                rw [← Fin.sum_univ_eq_sum_range (fun j ↦ omega N j) N] at hs
                exact hs.le)
            · positivity
      _ = 96 * E := by ring
  have hpen := penaltyEnergy_le_weightedGradient hN y
  have hlast : chainCoord y (N - 1) = y ⟨N - 1, by omega⟩ := by
    unfold chainCoord
    rw [dif_pos (by omega)]
  have hterminal := activation_deficit_le_basicEnergy hNpos y ⟨N - 1, by omega⟩
  rw [dualChain_eq_gate_add_penalty]
  rw [hlast]
  change
    (∑ k : Fin N, omega N k.1 * gateTerm y k) +
        (1 / 2 : ℝ) * penaltyEnergy N y +
        10 * (1 - q (y ⟨N - 1, by omega⟩)) ≤
      320 * (N : ℝ) * D
  have hpen' : (1 / 2 : ℝ) * penaltyEnergy N y ≤ (1 / 2) * D := by
    exact mul_le_mul_of_nonneg_left (by simpa [D] using hpen) (by norm_num)
  have hterminal' : 10 * (1 - q (y ⟨N - 1, by omega⟩)) ≤ 160 * E := by
    have ht : 1 - q (y ⟨N - 1, by omega⟩) ≤ 16 * E := by
      simpa [E] using hterminal
    nlinarith
  have hED' : 256 * E ≤ 256 * (D * (N : ℝ)) :=
    mul_le_mul_of_nonneg_left hED (by norm_num)
  have hhalf : (1 / 2 : ℝ) * D ≤ 64 * (N : ℝ) * D := by
    have hcoef : (1 / 2 : ℝ) ≤ 64 * (N : ℝ) := by
      have hNtwo : (2 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    exact mul_le_mul_of_nonneg_right hcoef hD0
  calc
    (∑ k : Fin N, omega N k.1 * gateTerm y k) +
          (1 / 2 : ℝ) * penaltyEnergy N y +
          10 * (1 - q (y ⟨N - 1, by omega⟩))
        ≤ 96 * E + (1 / 2) * D + 160 * E := by
          gcongr
    _ = 256 * E + (1 / 2) * D := by ring
    _ ≤ 256 * (D * (N : ℝ)) + (1 / 2) * D := by gcongr
    _ ≤ 256 * (D * (N : ℝ)) + 64 * (N : ℝ) * D := by gcongr
    _ = 320 * (N : ℝ) * D := by ring

/-- Proposition 4.1 bundled with its coordinatewise sign conclusion. -/
theorem proposition4_1 {N : ℕ} (hN : 2 ≤ N) (y : ChainPoint N) :
    (dualChain N y + 10 * (1 - q (chainCoord y (N - 1))) ≤
      320 * (N : ℝ) * weightedDualNormSq N (dualGradient N y)) ∧
    (∀ k : Fin N, dualGradient N y k ≤ 0) := by
  exact ⟨strengthened_weighted_PL hN y, fun k ↦ dualGradient_nonpos (by omega) y k⟩

/-- The terminal-gated function `G(alpha; y)` from Section 4.2. -/
def coupledDual (N : ℕ) (α : ℝ) (y : ChainPoint N) : ℝ :=
  α * q (chainCoord y (N - 1)) - dualChain N y

/-- The explicit `y`-gradient field of `G`, derived algebraically from (7). -/
def coupledGradient (N : ℕ) (α : ℝ) (y : ChainPoint N) : ChainPoint N := fun k ↦
  -dualGradient N y k +
    if k.1 + 1 = N then α * qDeriv (y k) else 0

private theorem chainPrev_one {N : ℕ} (k : Fin N) :
    chainPrev (fun _ : Fin N ↦ (1 : ℝ)) k.1 = 1 := by
  cases hk : k.1 with
  | zero => simp [chainPrev]
  | succ j =>
      have hjN : j < N := by omega
      simp [chainPrev, chainCoord, hjN]

@[simp] theorem dualChain_one {N : ℕ} (_hN : 0 < N) :
    dualChain N (fun _ ↦ (1 : ℝ)) = 0 := by
  unfold dualChain localInteraction gateTerm
  apply Finset.sum_eq_zero
  intro k _
  rw [chainPrev_one k]
  simp [p, negPart]

/-- Lemma 4.3, equation (10), stated as an upper bound plus an attaining
point (which is exactly the assertion that the maximum equals `alpha`). -/
theorem coupledDual_max {N : ℕ} (hN : 2 ≤ N) {α : ℝ} (hα0 : 0 ≤ α) :
    (∀ y : ChainPoint N, coupledDual N α y ≤ α) ∧
      coupledDual N α (fun _ ↦ (1 : ℝ)) = α := by
  constructor
  · intro y
    have hq := q_le_one (chainCoord y (N - 1))
    have hH := dualChain_nonneg (by omega) y
    unfold coupledDual
    nlinarith
  · unfold coupledDual
    have hcoord : chainCoord (fun _ : Fin N ↦ (1 : ℝ)) (N - 1) = 1 := by
      simp [chainCoord, show N - 1 < N by omega]
    rw [hcoord, q_one, dualChain_one (by omega)]
    ring

theorem weightedGradient_le_coupledGradient {N : ℕ} (hN : 2 ≤ N)
    {α : ℝ} (hα0 : 0 ≤ α) (y : ChainPoint N) :
    weightedDualNormSq N (dualGradient N y) ≤
      weightedDualNormSq N (coupledGradient N α y) := by
  have hNpos : 0 < N := by omega
  unfold weightedDualNormSq
  apply Finset.sum_le_sum
  intro k _
  have hg : dualGradient N y k ≤ 0 := dualGradient_nonpos hNpos y k
  have hadd : 0 ≤ (if k.1 + 1 = N then α * qDeriv (y k) else 0) := by
    split_ifs
    · exact mul_nonneg hα0 (qDeriv_nonneg _)
    · exact le_rfl
  have hsquare : dualGradient N y k ^ 2 ≤ coupledGradient N α y k ^ 2 := by
    unfold coupledGradient
    nlinarith
  exact div_le_div_of_nonneg_right hsquare (omega_pos hNpos).le

/-- Lemma 4.3, equation (11), with the maximum replaced by its proved value
`alpha`.  Together with `coupledDual_max`, this is the paper's statement. -/
theorem coupledDual_weighted_PL {N : ℕ} (hN : 2 ≤ N)
    {α : ℝ} (hα0 : 0 ≤ α) (hα10 : α ≤ 10) (y : ChainPoint N) :
    (1 / 2 : ℝ) * weightedDualNormSq N (coupledGradient N α y) ≥
      (1 / (640 * (N : ℝ))) * (α - coupledDual N α y) := by
  have hNpos : 0 < N := by omega
  have hprop := strengthened_weighted_PL hN y
  have hq0 : 0 ≤ 1 - q (chainCoord y (N - 1)) := by
    linarith [q_le_one (chainCoord y (N - 1))]
  have hgap : α - coupledDual N α y ≤
      320 * (N : ℝ) * weightedDualNormSq N (dualGradient N y) := by
    unfold coupledDual
    have halpha : α * (1 - q (chainCoord y (N - 1))) ≤
        10 * (1 - q (chainCoord y (N - 1))) :=
      mul_le_mul_of_nonneg_right hα10 hq0
    nlinarith
  have hnorm := weightedGradient_le_coupledGradient hN hα0 y
  have hNreal : 0 < (N : ℝ) := by positivity
  have hden : 0 < 640 * (N : ℝ) := by positivity
  have hgapG : α - coupledDual N α y ≤
      320 * (N : ℝ) * weightedDualNormSq N (coupledGradient N α y) := by
    exact hgap.trans <| mul_le_mul_of_nonneg_left hnorm (by positivity)
  have hquot :
      (α - coupledDual N α y) / (640 * (N : ℝ)) ≤
        (1 / 2 : ℝ) * weightedDualNormSq N (coupledGradient N α y) := by
    apply (div_le_iff₀ hden).2
    nlinarith
  simpa [div_eq_mul_inv, mul_comm] using hquot

/-- Lemma 4.3 bundled in a single theorem. -/
theorem lemma4_3 {N : ℕ} (hN : 2 ≤ N) {α : ℝ}
    (hα0 : 0 ≤ α) (hα10 : α ≤ 10) :
    ((∀ y : ChainPoint N, coupledDual N α y ≤ α) ∧
      coupledDual N α (fun _ ↦ (1 : ℝ)) = α) ∧
    (∀ y : ChainPoint N,
      (1 / 2 : ℝ) * weightedDualNormSq N (coupledGradient N α y) ≥
        (1 / (640 * (N : ℝ))) * (α - coupledDual N α y)) := by
  exact ⟨coupledDual_max hN hα0, fun y ↦ coupledDual_weighted_PL hN hα0 hα10 y⟩

end

end NCPLRevised
