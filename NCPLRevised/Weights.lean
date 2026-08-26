/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import Mathlib

/-!
# The weights in Lemma 4.2

This file formalizes the weight sequence from equation (3) and Lemma 4.2 of
*Lower Bounds for Nonconvex-PL Minimax Optimization* (`main_revised.tex`,
revised 2026-08-25).

The auxiliary sequence `innerWeight N k` is indexed by distance from the
terminal coordinate.  Thus `innerWeight N 0 = 1` and moving one place away
from the terminal coordinate applies the square-root recurrence.  The
paper's zero-based `omega N j`, for `0 <= j <= N`, reverses that indexing;
truncated natural subtraction also makes both terminal weights exactly one.
-/

namespace NCPLRevised

noncomputable section

/-- Weight at distance `k` from the terminal end of the chain. -/
def innerWeight (N : ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => Real.sqrt (innerWeight N k / (N : ℝ))

@[simp] theorem innerWeight_zero (N : ℕ) : innerWeight N 0 = 1 := rfl

@[simp] theorem innerWeight_succ (N k : ℕ) :
    innerWeight N (k + 1) = Real.sqrt (innerWeight N k / (N : ℝ)) := rfl

theorem innerWeight_pos {N : ℕ} (hN : 0 < N) (k : ℕ) :
    0 < innerWeight N k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [innerWeight_succ]
      exact Real.sqrt_pos.2 (div_pos ih (by positivity))

theorem innerWeight_nonneg {N : ℕ} (hN : 0 < N) (k : ℕ) :
    0 ≤ innerWeight N k := (innerWeight_pos hN k).le

/-- Squared form of the defining recurrence. -/
theorem innerWeight_succ_sq {N : ℕ} (hN : 0 < N) (k : ℕ) :
    innerWeight N (k + 1) ^ 2 = innerWeight N k / (N : ℝ) := by
  rw [innerWeight_succ, Real.sq_sqrt]
  exact div_nonneg (innerWeight_nonneg hN k) (by positivity)

/-- Every reverse-indexed weight belongs to `[1/N, 1]`. -/
theorem innerWeight_mem {N : ℕ} (hN : 0 < N) (k : ℕ) :
    innerWeight N k ∈ Set.Icc ((N : ℝ)⁻¹) 1 := by
  induction k with
  | zero =>
      constructor
      · simpa using (inv_le_one₀ (by exact_mod_cast hN)).2 (by exact_mod_cast hN)
      · simp
  | succ k ih =>
      constructor
      · have hsquare := innerWeight_succ_sq hN k
        have hnonneg := innerWeight_nonneg hN (k + 1)
        have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
        have hinvnonneg : 0 ≤ (N : ℝ)⁻¹ := (inv_pos.mpr hNreal).le
        have hprev : (N : ℝ)⁻¹ ≤ innerWeight N k := ih.1
        have hsq : (N : ℝ)⁻¹ ^ 2 ≤ innerWeight N (k + 1) ^ 2 := by
          rw [hsquare]
          simpa [pow_two, div_eq_mul_inv] using
            mul_le_mul_of_nonneg_right hprev hinvnonneg
        nlinarith
      · have hsquare := innerWeight_succ_sq hN k
        have hnonneg := innerWeight_nonneg hN (k + 1)
        have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
        have hquot : innerWeight N k / (N : ℝ) ≤ 1 := by
          apply (div_le_one (by positivity)).2
          linarith [ih.2]
        nlinarith

/-- Increasing the distance from the terminal end cannot increase a weight. -/
theorem innerWeight_antitone_step {N : ℕ} (hN : 0 < N) (k : ℕ) :
    innerWeight N (k + 1) ≤ innerWeight N k := by
  have hsquare := innerWeight_succ_sq hN k
  have hnext := innerWeight_nonneg hN (k + 1)
  have hprev := innerWeight_nonneg hN k
  have hlower := (innerWeight_mem hN k).1
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hmul : 1 ≤ (N : ℝ) * innerWeight N k := by
    have hdiv : 1 / (N : ℝ) ≤ innerWeight N k := by
      simpa [one_div] using hlower
    have := (div_le_iff₀ hNreal).mp hdiv
    simpa [mul_comm] using this
  have hsq : innerWeight N (k + 1) ^ 2 ≤ innerWeight N k ^ 2 := by
    rw [hsquare]
    apply (div_le_iff₀ hNreal).2
    nlinarith
  nlinarith

theorem innerWeight_antitone {N : ℕ} (hN : 0 < N) :
    Antitone (innerWeight N) := by
  exact antitone_nat_of_succ_le (innerWeight_antitone_step hN)

/-- An affine-geometric upper bound used to control the first sum. -/
theorem innerWeight_le_geometric {N : ℕ} (hN : 0 < N) (k : ℕ) :
    innerWeight N k ≤ ((1 : ℝ) / 2) ^ k + (N : ℝ)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hsquare := innerWeight_succ_sq hN k
      have hnext := innerWeight_nonneg hN (k + 1)
      have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
      have hamgm :
          innerWeight N (k + 1) ≤
            (innerWeight N k + (N : ℝ)⁻¹) / 2 := by
        have hsqnonneg :
            0 ≤ (innerWeight N k - (N : ℝ)⁻¹) ^ 2 := sq_nonneg _
        have htarget :
            innerWeight N (k + 1) ^ 2 ≤
              ((innerWeight N k + (N : ℝ)⁻¹) / 2) ^ 2 := by
          rw [hsquare, div_eq_mul_inv]
          nlinarith
        have hrhs : 0 ≤ (innerWeight N k + (N : ℝ)⁻¹) / 2 :=
          div_nonneg
            (add_nonneg (innerWeight_nonneg hN k) (inv_nonneg.mpr hNreal.le))
            (by norm_num)
        nlinarith
      rw [pow_succ]
      nlinarith [inv_pos.mpr hNreal]

theorem sum_half_pow_eq (n : ℕ) :
    ∑ k ∈ Finset.range n, ((1 : ℝ) / 2) ^ k =
      2 - 2 * ((1 : ℝ) / 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

/-- Strict version of the numerical estimate needed for Lemma 4.2. -/
theorem sum_innerWeight_range_lt_three {N : ℕ} (hN : 0 < N) :
    ∑ k ∈ Finset.range N, innerWeight N k < 3 := by
  have hmajor :
      (∑ k ∈ Finset.range N, innerWeight N k) ≤
        ∑ k ∈ Finset.range N, (((1 : ℝ) / 2) ^ k + (N : ℝ)⁻¹) := by
    exact Finset.sum_le_sum fun k _ ↦ innerWeight_le_geometric hN k
  have hgeom : (∑ k ∈ Finset.range N, ((1 : ℝ) / 2) ^ k) < 2 := by
    rw [sum_half_pow_eq]
    have : 0 < ((1 : ℝ) / 2) ^ N := pow_pos (by norm_num) _
    linarith
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  calc
    (∑ k ∈ Finset.range N, innerWeight N k)
        ≤ ∑ k ∈ Finset.range N, (((1 : ℝ) / 2) ^ k + (N : ℝ)⁻¹) := hmajor
    _ = (∑ k ∈ Finset.range N, ((1 : ℝ) / 2) ^ k) +
          (N : ℝ) * (N : ℝ)⁻¹ := by
            rw [Finset.sum_add_distrib]
            simp
    _ = (∑ k ∈ Finset.range N, ((1 : ℝ) / 2) ^ k) + 1 := by
      rw [mul_inv_cancel₀ hNreal.ne']
    _ < 2 + 1 := by linarith
    _ = 3 := by norm_num

/-- The paper's weight `ω_j`.  The relevant domain is `0 <= j <= N`. -/
def omega (N j : ℕ) : ℝ := innerWeight N (N - 1 - j)

@[simp] theorem omega_terminal (N : ℕ) : omega N N = 1 := by
  simp [omega]

@[simp] theorem omega_penultimate {N : ℕ} (_hN : 0 < N) :
    omega N (N - 1) = 1 := by
  simp [omega]

theorem omega_pos {N j : ℕ} (hN : 0 < N) : 0 < omega N j :=
  innerWeight_pos hN _

theorem omega_lower {N j : ℕ} (hN : 0 < N) :
    (N : ℝ)⁻¹ ≤ omega N j := (innerWeight_mem hN _).1

theorem omega_upper {N j : ℕ} (hN : 0 < N) : omega N j ≤ 1 :=
  (innerWeight_mem hN _).2

/-- The paper's recurrence, with precisely its nonterminal index range. -/
theorem omega_pred_eq_sqrt {N j : ℕ} (hjpos : 0 < j) (hjN : j < N) :
    omega N (j - 1) = Real.sqrt (omega N j / (N : ℝ)) := by
  have hk : N - 1 - (j - 1) = (N - 1 - j) + 1 := by omega
  simp only [omega, hk, innerWeight_succ]

/-- Squared recurrence identity `ω_{j-1}^2 / ω_j = 1/N`. -/
theorem omega_pred_sq_div {N j : ℕ} (hN : 0 < N)
    (hjpos : 0 < j) (hjN : j < N) :
    omega N (j - 1) ^ 2 / omega N j = (N : ℝ)⁻¹ := by
  have hk : N - 1 - (j - 1) = (N - 1 - j) + 1 := by omega
  rw [omega, omega, hk, innerWeight_succ_sq hN]
  have hw : innerWeight N (N - 1 - j) ≠ 0 :=
    ne_of_gt (innerWeight_pos hN _)
  field_simp [hw]

/-- Monotonicity of the paper-indexed sequence on its relevant domain. -/
theorem omega_mono {N i j : ℕ} (hN : 0 < N) (hij : i ≤ j) (_hjN : j ≤ N) :
    omega N i ≤ omega N j := by
  unfold omega
  apply innerWeight_antitone hN
  omega

/-- Equation (4), bundled in a form convenient for later files. -/
theorem lemma4_2_order {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ)⁻¹ ≤ omega N 0 ∧
      (∀ i j, i ≤ j → j ≤ N → omega N i ≤ omega N j) ∧
      omega N (N - 1) = 1 ∧ omega N N = 1 := by
  have hNpos : 0 < N := by omega
  exact ⟨omega_lower hNpos, fun _ _ ↦ omega_mono hNpos,
    omega_penultimate hNpos, omega_terminal N⟩

/-- Reversal turns the paper-indexed sum into the reverse-indexed sum. -/
theorem sum_omega_eq_sum_innerWeight (N : ℕ) :
    ∑ j ∈ Finset.range N, omega N j =
      ∑ k ∈ Finset.range N, innerWeight N k := by
  have homega (j : Fin N) :
      omega N j.1 = innerWeight N (Fin.rev j).1 := by
    unfold omega
    congr 1
    rw [Fin.val_rev]
    omega
  calc
    (∑ j ∈ Finset.range N, omega N j) = ∑ j : Fin N, omega N j.1 := by
      symm
      simpa using Fin.sum_univ_eq_sum_range (fun j ↦ omega N j) N
    _ = ∑ j : Fin N, innerWeight N (Fin.rev j).1 := by
      apply Fintype.sum_congr
      exact homega
    _ = ∑ j : Fin N, innerWeight N j.1 := by
      simpa using Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin N))
        (fun j : Fin N ↦ innerWeight N j.1)
    _ = ∑ k ∈ Finset.range N, innerWeight N k := by
      simpa using Fin.sum_univ_eq_sum_range (fun k ↦ innerWeight N k) N

/-- First strict sum inequality in (5). -/
theorem sum_omega_lt_three {N : ℕ} (hN : 2 ≤ N) :
    ∑ j ∈ Finset.range N, omega N j < 3 := by
  rw [sum_omega_eq_sum_innerWeight]
  exact sum_innerWeight_range_lt_three (by omega)

/-- Every nonterminal summand in the second sum is exactly `1/N`. -/
theorem omega_sq_div_succ {N j : ℕ} (hN : 0 < N) (hj : j + 1 < N) :
    omega N j ^ 2 / omega N (j + 1) = (N : ℝ)⁻¹ := by
  simpa using omega_pred_sq_div hN (j := j + 1) (by omega) hj

/-- Exact value of the second sum in (5). -/
theorem sum_omega_sq_div_succ_eq {N : ℕ} (hN : 0 < N) :
    ∑ j ∈ Finset.range N, omega N j ^ 2 / omega N (j + 1) =
      ((N - 1 : ℕ) : ℝ) * (N : ℝ)⁻¹ + 1 := by
  have hsplit :
      (∑ j ∈ Finset.range N, omega N j ^ 2 / omega N (j + 1)) =
        (∑ j ∈ Finset.range (N - 1), omega N j ^ 2 / omega N (j + 1)) +
          omega N (N - 1) ^ 2 / omega N (N - 1 + 1) := by
    have h := Finset.sum_range_succ
      (fun j ↦ omega N j ^ 2 / omega N (j + 1)) (N - 1)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hN.ne')] at h
    simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hN.ne')] using h
  rw [hsplit]
  have hconst :
      ∑ j ∈ Finset.range (N - 1),
          omega N j ^ 2 / omega N (j + 1) =
        ∑ _j ∈ Finset.range (N - 1), (N : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro j hj
    apply omega_sq_div_succ hN
    have hjlt : j < N - 1 := Finset.mem_range.mp hj
    omega
  rw [hconst]
  have hlast : omega N (N - 1) ^ 2 / omega N (N - 1 + 1) = 1 := by
    simp [omega_penultimate hN, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hN.ne')]
  rw [hlast]
  simp

/-- Second strict sum inequality in (5). -/
theorem sum_omega_sq_div_succ_lt_two {N : ℕ} (hN : 2 ≤ N) :
    ∑ j ∈ Finset.range N, omega N j ^ 2 / omega N (j + 1) < 2 := by
  have hNpos : 0 < (N : ℝ) := by positivity
  rw [sum_omega_sq_div_succ_eq (by omega)]
  have hsub : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  rw [hsub]
  have hinvpos : 0 < (N : ℝ)⁻¹ := inv_pos.mpr hNpos
  have hcancel : (N : ℝ) * (N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hNpos.ne'
  nlinarith

/-- Lemma 4.2: both strict sum inequalities, in the paper's indexing. -/
theorem lemma4_2_sums {N : ℕ} (hN : 2 ≤ N) :
    (∑ j ∈ Finset.range N, omega N j) < 3 ∧
      (∑ j ∈ Finset.range N, omega N j ^ 2 / omega N (j + 1)) < 2 :=
  ⟨sum_omega_lt_three hN, sum_omega_sq_div_succ_lt_two hN⟩

end

end NCPLRevised
