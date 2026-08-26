/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.QuadraticPerspectiveVector
import NCPLRevised.ScaleClipKernel
import NCPLRevised.ScaleClipPair

/-!
# Dimension-free Lipschitz estimates for the perspective kernels

The gradients of all quadratic perspectives used by the embedded cell are
positively homogeneous.  This file controls their angular part by clipping
each normalized coordinate to its fixed transition interval.  This removes
the apparent singularity at zero scale and gives numerical Lipschitz bounds.
-/

namespace NCPLRevised

noncomputable section

@[simp] theorem unitClip_eq_self {x : ℝ} (hlo : -1 ≤ x) (hhi : x ≤ 1) :
    unitClip x = x := unitClip_of_mem hlo hhi

@[simp] theorem unitClip_eq_neg_one {x : ℝ} (hx : x ≤ -1) :
    unitClip x = -1 := unitClip_of_le_neg_one hx

@[simp] theorem unitClip_eq_one {x : ℝ} (hx : 1 ≤ x) :
    unitClip x = 1 := unitClip_of_one_le hx

theorem unitClip_lipschitz_bound (x y : ℝ) :
    |unitClip x - unitClip y| ≤ |x - y| :=
  abs_unitClip_sub_unitClip_le x y

theorem q_unitClip (x : ℝ) : q (unitClip x) = q x := by
  by_cases hlo : x ≤ -1
  · rw [unitClip_eq_neg_one hlo, q_of_nonpos (by norm_num),
      q_of_nonpos (hlo.trans (by norm_num))]
  by_cases hhi : 1 ≤ x
  · rw [unitClip_eq_one hhi, q_one, q_of_one_le hhi]
  · rw [unitClip_eq_self (le_of_not_ge hlo) (le_of_not_ge hhi)]

theorem qDeriv_unitClip (x : ℝ) : qDeriv (unitClip x) = qDeriv x := by
  by_cases hlo : x ≤ -1
  · rw [unitClip_eq_neg_one hlo, qDeriv_of_nonpos (by norm_num),
      qDeriv_of_nonpos (hlo.trans (by norm_num))]
  by_cases hhi : 1 ≤ x
  · rw [unitClip_eq_one hhi, qDeriv_of_one_le (by norm_num),
      qDeriv_of_one_le hhi]
  · rw [unitClip_eq_self (le_of_not_ge hlo) (le_of_not_ge hhi)]

theorem p_unitClip (x : ℝ) : p (unitClip x) = p x := by
  by_cases hlo : x ≤ -1
  · rw [unitClip_eq_neg_one hlo]
    simp [p, q_of_nonpos (show (x + 1) / 2 ≤ 0 by linarith)]
  by_cases hhi : 1 ≤ x
  · rw [unitClip_eq_one hhi]
    simp [p, q_of_one_le (show (1 : ℝ) ≤ (x + 1) / 2 by linarith)]
  · rw [unitClip_eq_self (le_of_not_ge hlo) (le_of_not_ge hhi)]

theorem pDeriv_unitClip (x : ℝ) : pDeriv (unitClip x) = pDeriv x := by
  by_cases hlo : x ≤ -1
  · rw [unitClip_eq_neg_one hlo, pDeriv_of_le_neg_one (by norm_num),
      pDeriv_of_le_neg_one hlo]
  by_cases hhi : 1 ≤ x
  · rw [unitClip_eq_one hhi, pDeriv_of_one_le (by norm_num),
      pDeriv_of_one_le hhi]
  · rw [unitClip_eq_self (le_of_not_ge hlo) (le_of_not_ge hhi)]

theorem unitClip_mul_qDeriv (x : ℝ) :
    unitClip x * qDeriv (unitClip x) = x * qDeriv x := by
  by_cases hlo : x ≤ -1
  · simp [unitClip_eq_neg_one hlo, qDeriv_of_nonpos,
      hlo.trans (by norm_num : (-1 : ℝ) ≤ 0)]
  by_cases hhi : 1 ≤ x
  · simp [qDeriv_of_one_le, hhi]
  · rw [unitClip_eq_self (le_of_not_ge hlo) (le_of_not_ge hhi)]

theorem unitClip_mul_pDeriv (x : ℝ) :
    unitClip x * pDeriv (unitClip x) = x * pDeriv x := by
  by_cases hlo : x ≤ -1
  · simp [pDeriv_of_le_neg_one, hlo]
  by_cases hhi : 1 ≤ x
  · simp [pDeriv_of_one_le, hhi]
  · rw [unitClip_eq_self (le_of_not_ge hlo) (le_of_not_ge hhi)]

/-- The gates themselves inherit the maximum slope of their derivatives. -/
theorem q_lipschitz_three_halves : LipschitzWith (3 / 2 : NNReal) q := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_q
  intro x
  rw [deriv_q, ← NNReal.coe_le_coe]
  simpa [Real.norm_eq_abs, abs_of_nonneg (qDeriv_nonneg x)] using
    qDeriv_le_three_halves x

theorem p_lipschitz_three_quarters : LipschitzWith (3 / 4 : NNReal) p := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_p
  intro x
  rw [deriv_p, ← NNReal.coe_le_coe]
  simpa [Real.norm_eq_abs, abs_of_nonneg (pDeriv_nonneg x)] using
    pDeriv_le_three_quarters x

theorem q_lipschitz_bound (x y : ℝ) :
    |q x - q y| ≤ (3 / 2 : ℝ) * |x - y| := by
  simpa [Real.dist_eq] using q_lipschitz_three_halves.dist_le_mul x y

theorem p_lipschitz_bound (x y : ℝ) :
    |p x - p y| ≤ (3 / 4 : ℝ) * |x - y| := by
  simpa [Real.dist_eq] using p_lipschitz_three_quarters.dist_le_mul x y

def qPerspectiveEtaBase (x : ℝ) : ℝ := 2 * q x - x * qDeriv x
def qPerspectiveUBase (x : ℝ) : ℝ := qDeriv x

def pPerspectiveEtaBase (x : ℝ) : ℝ := 2 * p x - x * pDeriv x
def pPerspectiveUBase (x : ℝ) : ℝ := pDeriv x

def qpPerspectiveEtaBase (x y : ℝ) : ℝ :=
  2 * q x * p y - x * qDeriv x * p y - y * q x * pDeriv y

def qpPerspectiveUBase (x y : ℝ) : ℝ := qDeriv x * p y
def qpPerspectiveVBase (x y : ℝ) : ℝ := q x * pDeriv y

theorem qPerspectiveEtaBase_unitClip (x : ℝ) :
    qPerspectiveEtaBase (unitClip x) = qPerspectiveEtaBase x := by
  simp only [qPerspectiveEtaBase, q_unitClip, unitClip_mul_qDeriv]

theorem qPerspectiveUBase_unitClip (x : ℝ) :
    qPerspectiveUBase (unitClip x) = qPerspectiveUBase x := by
  simp only [qPerspectiveUBase, qDeriv_unitClip]

theorem pPerspectiveEtaBase_unitClip (x : ℝ) :
    pPerspectiveEtaBase (unitClip x) = pPerspectiveEtaBase x := by
  simp only [pPerspectiveEtaBase, p_unitClip, unitClip_mul_pDeriv]

theorem pPerspectiveUBase_unitClip (x : ℝ) :
    pPerspectiveUBase (unitClip x) = pPerspectiveUBase x := by
  simp only [pPerspectiveUBase, pDeriv_unitClip]

theorem qpPerspectiveEtaBase_unitClip (x y : ℝ) :
    qpPerspectiveEtaBase (unitClip x) (unitClip y) =
      qpPerspectiveEtaBase x y := by
  unfold qpPerspectiveEtaBase
  rw [q_unitClip, p_unitClip]
  have hx := unitClip_mul_qDeriv x
  have hy := unitClip_mul_pDeriv y
  calc
    2 * q x * p y - unitClip x * qDeriv (unitClip x) * p y -
        unitClip y * q x * pDeriv (unitClip y) =
      2 * q x * p y -
        (unitClip x * qDeriv (unitClip x)) * p y -
        q x * (unitClip y * pDeriv (unitClip y)) := by ring
    _ = 2 * q x * p y - x * qDeriv x * p y -
        y * q x * pDeriv y := by rw [hx, hy]; ring

theorem qpPerspectiveUBase_unitClip (x y : ℝ) :
    qpPerspectiveUBase (unitClip x) (unitClip y) =
      qpPerspectiveUBase x y := by
  simp only [qpPerspectiveUBase, qDeriv_unitClip, p_unitClip]

theorem qpPerspectiveVBase_unitClip (x y : ℝ) :
    qpPerspectiveVBase (unitClip x) (unitClip y) =
      qpPerspectiveVBase x y := by
  simp only [qpPerspectiveVBase, q_unitClip, pDeriv_unitClip]

theorem abs_qDeriv_le_three_halves (x : ℝ) :
    |qDeriv x| ≤ (3 / 2 : ℝ) := by
  rw [abs_of_nonneg (qDeriv_nonneg x)]
  exact qDeriv_le_three_halves x

theorem abs_pDeriv_le_three_quarters (x : ℝ) :
    |pDeriv x| ≤ (3 / 4 : ℝ) := by
  rw [abs_of_nonneg (pDeriv_nonneg x)]
  exact pDeriv_le_three_quarters x

theorem abs_mul_sub_mul_le (a b c d : ℝ) :
    |a * b - c * d| ≤ |a - c| * |b| + |c| * |b - d| := by
  calc
    |a * b - c * d| = |(a - c) * b + c * (b - d)| := by ring_nf
    _ ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ = |a - c| * |b| + |c| * |b - d| := by rw [abs_mul, abs_mul]

theorem abs_qPerspectiveEtaBase_clip_le_four (x : ℝ) :
    |qPerspectiveEtaBase (unitClip x)| ≤ 4 := by
  unfold qPerspectiveEtaBase
  have hq := q_mem_Icc (unitClip x)
  have hd := qDeriv_mem_Icc (unitClip x)
  have hx := abs_unitClip_le_one x
  calc
    |2 * q (unitClip x) - unitClip x * qDeriv (unitClip x)| ≤
        |2 * q (unitClip x)| +
          |unitClip x * qDeriv (unitClip x)| := abs_sub _ _
    _ = 2 * q (unitClip x) +
          |unitClip x| * qDeriv (unitClip x) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg hq.1, abs_of_nonneg hd.1]
    _ ≤ 4 := by
      have hm : |unitClip x| * qDeriv (unitClip x) ≤ (3 / 2 : ℝ) := by
        calc
          |unitClip x| * qDeriv (unitClip x) ≤
              1 * qDeriv (unitClip x) :=
            mul_le_mul_of_nonneg_right hx hd.1
          _ ≤ 1 * (3 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left hd.2 (by norm_num)
          _ = (3 / 2 : ℝ) := by ring
      nlinarith [hq.2]

theorem abs_qPerspectiveUBase_le_two (x : ℝ) :
    |qPerspectiveUBase x| ≤ 2 := by
  unfold qPerspectiveUBase
  exact (abs_qDeriv_le_three_halves x).trans (by norm_num)

theorem abs_pPerspectiveEtaBase_clip_le_three (x : ℝ) :
    |pPerspectiveEtaBase (unitClip x)| ≤ 3 := by
  unfold pPerspectiveEtaBase
  have hp := p_mem_Icc (unitClip x)
  have hd := pDeriv_mem_Icc (unitClip x)
  have hx := abs_unitClip_le_one x
  calc
    |2 * p (unitClip x) - unitClip x * pDeriv (unitClip x)| ≤
        |2 * p (unitClip x)| +
          |unitClip x * pDeriv (unitClip x)| := abs_sub _ _
    _ = 2 * p (unitClip x) +
          |unitClip x| * pDeriv (unitClip x) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg hp.1, abs_of_nonneg hd.1]
    _ ≤ 3 := by
      have hm : |unitClip x| * pDeriv (unitClip x) ≤ (3 / 4 : ℝ) := by
        calc
          |unitClip x| * pDeriv (unitClip x) ≤
              1 * pDeriv (unitClip x) :=
            mul_le_mul_of_nonneg_right hx hd.1
          _ ≤ 1 * (3 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_left hd.2 (by norm_num)
          _ = (3 / 4 : ℝ) := by ring
      nlinarith [hp.2]

theorem abs_pPerspectiveUBase_le_one (x : ℝ) :
    |pPerspectiveUBase x| ≤ 1 := by
  unfold pPerspectiveUBase
  exact (abs_pDeriv_le_three_quarters x).trans (by norm_num)

theorem qPerspectiveEtaBase_clip_lipschitz (x y : ℝ) :
    |qPerspectiveEtaBase (unitClip x) -
        qPerspectiveEtaBase (unitClip y)| ≤
      11 * |unitClip x - unitClip y| := by
  let X := unitClip x
  let Y := unitClip y
  have hX : |X| ≤ 1 := abs_unitClip_le_one x
  have hY : |Y| ≤ 1 := abs_unitClip_le_one y
  have hq := q_lipschitz_bound X Y
  have hd := qDeriv_lipschitz_bound X Y
  have hdX := abs_qDeriv_le_three_halves X
  have hprod0 := abs_mul_sub_mul_le X (qDeriv X) Y (qDeriv Y)
  have hprod : |X * qDeriv X - Y * qDeriv Y| ≤
      (15 / 2 : ℝ) * |X - Y| := by
    have hmul1 : |X - Y| * |qDeriv X| ≤
        |X - Y| * (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hdX (abs_nonneg _)
    have hmul2 : |Y| * |qDeriv X - qDeriv Y| ≤
        6 * |X - Y| := by
      calc
        |Y| * |qDeriv X - qDeriv Y| ≤
            1 * |qDeriv X - qDeriv Y| :=
          mul_le_mul_of_nonneg_right hY (abs_nonneg _)
        _ ≤ 1 * (6 * |X - Y|) :=
          mul_le_mul_of_nonneg_left hd (by norm_num)
        _ = 6 * |X - Y| := by ring
    exact hprod0.trans (by nlinarith)
  unfold qPerspectiveEtaBase
  have htri :
      |(2 * q X - X * qDeriv X) -
          (2 * q Y - Y * qDeriv Y)| ≤
        2 * |q X - q Y| +
          |X * qDeriv X - Y * qDeriv Y| := by
    calc
      |(2 * q X - X * qDeriv X) -
          (2 * q Y - Y * qDeriv Y)| =
          |2 * (q X - q Y) -
            (X * qDeriv X - Y * qDeriv Y)| := by ring_nf
      _ ≤ |2 * (q X - q Y)| +
          |X * qDeriv X - Y * qDeriv Y| := abs_sub _ _
      _ = 2 * |q X - q Y| +
          |X * qDeriv X - Y * qDeriv Y| := by rw [abs_mul]; norm_num
  dsimp [X, Y] at htri hq hprod ⊢
  nlinarith [abs_nonneg (unitClip x - unitClip y)]

theorem qPerspectiveUBase_clip_lipschitz (x y : ℝ) :
    |qPerspectiveUBase (unitClip x) -
        qPerspectiveUBase (unitClip y)| ≤
      6 * |unitClip x - unitClip y| := by
  exact qDeriv_lipschitz_bound _ _

theorem pPerspectiveEtaBase_clip_lipschitz (x y : ℝ) :
    |pPerspectiveEtaBase (unitClip x) -
        pPerspectiveEtaBase (unitClip y)| ≤
      4 * |unitClip x - unitClip y| := by
  let X := unitClip x
  let Y := unitClip y
  have hY : |Y| ≤ 1 := abs_unitClip_le_one y
  have hp := p_lipschitz_bound X Y
  have hd := pDeriv_lipschitz_bound X Y
  have hdX := abs_pDeriv_le_three_quarters X
  have hprod0 := abs_mul_sub_mul_le X (pDeriv X) Y (pDeriv Y)
  have hprod : |X * pDeriv X - Y * pDeriv Y| ≤
      (9 / 4 : ℝ) * |X - Y| := by
    have hmul1 : |X - Y| * |pDeriv X| ≤
        |X - Y| * (3 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hdX (abs_nonneg _)
    have hmul2 : |Y| * |pDeriv X - pDeriv Y| ≤
        (3 / 2 : ℝ) * |X - Y| := by
      calc
        |Y| * |pDeriv X - pDeriv Y| ≤
            1 * |pDeriv X - pDeriv Y| :=
          mul_le_mul_of_nonneg_right hY (abs_nonneg _)
        _ ≤ 1 * ((3 / 2 : ℝ) * |X - Y|) :=
          mul_le_mul_of_nonneg_left hd (by norm_num)
        _ = (3 / 2 : ℝ) * |X - Y| := by ring
    exact hprod0.trans (by nlinarith)
  unfold pPerspectiveEtaBase
  have htri :
      |(2 * p X - X * pDeriv X) -
          (2 * p Y - Y * pDeriv Y)| ≤
        2 * |p X - p Y| +
          |X * pDeriv X - Y * pDeriv Y| := by
    calc
      |(2 * p X - X * pDeriv X) -
          (2 * p Y - Y * pDeriv Y)| =
          |2 * (p X - p Y) -
            (X * pDeriv X - Y * pDeriv Y)| := by ring_nf
      _ ≤ |2 * (p X - p Y)| +
          |X * pDeriv X - Y * pDeriv Y| := abs_sub _ _
      _ = 2 * |p X - p Y| +
          |X * pDeriv X - Y * pDeriv Y| := by rw [abs_mul]; norm_num
  dsimp [X, Y] at htri hp hprod ⊢
  nlinarith [abs_nonneg (unitClip x - unitClip y)]

theorem pPerspectiveUBase_clip_lipschitz (x y : ℝ) :
    |pPerspectiveUBase (unitClip x) -
        pPerspectiveUBase (unitClip y)| ≤
      (3 / 2 : ℝ) * |unitClip x - unitClip y| := by
  exact pDeriv_lipschitz_bound _ _

theorem clip_mul_qDeriv_lipschitz (x y : ℝ) :
    |unitClip x * qDeriv (unitClip x) -
        unitClip y * qDeriv (unitClip y)| ≤
      (15 / 2 : ℝ) * |unitClip x - unitClip y| := by
  let X := unitClip x
  let Y := unitClip y
  have hY : |Y| ≤ 1 := abs_unitClip_le_one y
  have hd := qDeriv_lipschitz_bound X Y
  have hdX := abs_qDeriv_le_three_halves X
  have hprod0 := abs_mul_sub_mul_le X (qDeriv X) Y (qDeriv Y)
  have hmul1 : |X - Y| * |qDeriv X| ≤
      |X - Y| * (3 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_left hdX (abs_nonneg _)
  have hmul2 : |Y| * |qDeriv X - qDeriv Y| ≤
      6 * |X - Y| := by
    calc
      |Y| * |qDeriv X - qDeriv Y| ≤
          1 * |qDeriv X - qDeriv Y| :=
        mul_le_mul_of_nonneg_right hY (abs_nonneg _)
      _ ≤ 1 * (6 * |X - Y|) :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
      _ = 6 * |X - Y| := by ring
  dsimp [X, Y] at hprod0 hmul1 hmul2 ⊢
  exact hprod0.trans (by nlinarith)

theorem clip_mul_pDeriv_lipschitz (x y : ℝ) :
    |unitClip x * pDeriv (unitClip x) -
        unitClip y * pDeriv (unitClip y)| ≤
      (9 / 4 : ℝ) * |unitClip x - unitClip y| := by
  let X := unitClip x
  let Y := unitClip y
  have hY : |Y| ≤ 1 := abs_unitClip_le_one y
  have hd := pDeriv_lipschitz_bound X Y
  have hdX := abs_pDeriv_le_three_quarters X
  have hprod0 := abs_mul_sub_mul_le X (pDeriv X) Y (pDeriv Y)
  have hmul1 : |X - Y| * |pDeriv X| ≤
      |X - Y| * (3 / 4 : ℝ) :=
    mul_le_mul_of_nonneg_left hdX (abs_nonneg _)
  have hmul2 : |Y| * |pDeriv X - pDeriv Y| ≤
      (3 / 2 : ℝ) * |X - Y| := by
    calc
      |Y| * |pDeriv X - pDeriv Y| ≤
          1 * |pDeriv X - pDeriv Y| :=
        mul_le_mul_of_nonneg_right hY (abs_nonneg _)
      _ ≤ 1 * ((3 / 2 : ℝ) * |X - Y|) :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
      _ = (3 / 2 : ℝ) * |X - Y| := by ring
  dsimp [X, Y] at hprod0 hmul1 hmul2 ⊢
  exact hprod0.trans (by nlinarith)

theorem abs_qpPerspectiveEtaBase_clip_le_five (x y : ℝ) :
    |qpPerspectiveEtaBase (unitClip x) (unitClip y)| ≤ 5 := by
  let X := unitClip x
  let Y := unitClip y
  have hX := abs_unitClip_le_one x
  have hY := abs_unitClip_le_one y
  have hq := q_mem_Icc X
  have hp := p_mem_Icc Y
  have hqd := qDeriv_mem_Icc X
  have hpd := pDeriv_mem_Icc Y
  have hqp : q X * p Y ≤ 1 := by
    calc
      q X * p Y ≤ 1 * p Y := mul_le_mul_of_nonneg_right hq.2 hp.1
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hp.2 (by norm_num)
      _ = 1 := by ring
  have hxqd : |X| * qDeriv X ≤ (3 / 2 : ℝ) := by
    calc
      |X| * qDeriv X ≤ 1 * qDeriv X :=
        mul_le_mul_of_nonneg_right hX hqd.1
      _ ≤ 1 * (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hqd.2 (by norm_num)
      _ = (3 / 2 : ℝ) := by ring
  have hyqd : |Y| * pDeriv Y ≤ (3 / 4 : ℝ) := by
    calc
      |Y| * pDeriv Y ≤ 1 * pDeriv Y :=
        mul_le_mul_of_nonneg_right hY hpd.1
      _ ≤ 1 * (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hpd.2 (by norm_num)
      _ = (3 / 4 : ℝ) := by ring
  have hxterm : |X * qDeriv X * p Y| ≤ (3 / 2 : ℝ) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hqd.1, abs_of_nonneg hp.1]
    calc
      |X| * qDeriv X * p Y ≤ (3 / 2 : ℝ) * p Y :=
        mul_le_mul_of_nonneg_right hxqd hp.1
      _ ≤ (3 / 2 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hp.2 (by norm_num)
      _ = (3 / 2 : ℝ) := by ring
  have hyterm : |Y * q X * pDeriv Y| ≤ (3 / 4 : ℝ) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hq.1, abs_of_nonneg hpd.1]
    calc
      |Y| * q X * pDeriv Y ≤ |Y| * 1 * pDeriv Y :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hq.2 (abs_nonneg Y)) hpd.1
      _ = |Y| * pDeriv Y := by ring
      _ ≤ (3 / 4 : ℝ) := hyqd
  unfold qpPerspectiveEtaBase
  have htri : |2 * q X * p Y - X * qDeriv X * p Y -
      Y * q X * pDeriv Y| ≤
      2 * q X * p Y + |X * qDeriv X * p Y| +
        |Y * q X * pDeriv Y| := by
    calc
      |2 * q X * p Y - X * qDeriv X * p Y -
          Y * q X * pDeriv Y| ≤
          |2 * q X * p Y - X * qDeriv X * p Y| +
            |Y * q X * pDeriv Y| := abs_sub _ _
      _ ≤ |2 * q X * p Y| + |X * qDeriv X * p Y| +
            |Y * q X * pDeriv Y| := by
          gcongr
          exact abs_sub _ _
      _ = 2 * q X * p Y + |X * qDeriv X * p Y| +
            |Y * q X * pDeriv Y| := by
          rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hq.1) hp.1)]
  dsimp [X, Y] at htri hqp hxterm hyterm ⊢
  nlinarith

theorem abs_qpPerspectiveUBase_clip_le_two (x y : ℝ) :
    |qpPerspectiveUBase (unitClip x) (unitClip y)| ≤ 2 := by
  unfold qpPerspectiveUBase
  rw [abs_mul, abs_of_nonneg (qDeriv_nonneg _), abs_of_nonneg (p_nonneg _)]
  have hd := qDeriv_le_three_halves (unitClip x)
  have hp := p_le_one (unitClip y)
  have h0 := p_nonneg (unitClip y)
  have hm := mul_le_mul_of_nonneg_right hd h0
  nlinarith

theorem abs_qpPerspectiveVBase_clip_le_one (x y : ℝ) :
    |qpPerspectiveVBase (unitClip x) (unitClip y)| ≤ 1 := by
  unfold qpPerspectiveVBase
  rw [abs_mul, abs_of_nonneg (q_nonneg _), abs_of_nonneg (pDeriv_nonneg _)]
  have hq := q_le_one (unitClip x)
  have hd := pDeriv_le_three_quarters (unitClip y)
  have h0 := pDeriv_nonneg (unitClip y)
  have hm := mul_le_mul_of_nonneg_right hq h0
  nlinarith

theorem qpPerspectiveUBase_clip_lipschitz (x y x' y' : ℝ) :
    |qpPerspectiveUBase (unitClip x) (unitClip y) -
        qpPerspectiveUBase (unitClip x') (unitClip y')| ≤
      8 * (|unitClip x - unitClip x'| +
        |unitClip y - unitClip y'|) := by
  let X := unitClip x
  let Y := unitClip y
  let X' := unitClip x'
  let Y' := unitClip y'
  have hprod := abs_mul_sub_mul_le (qDeriv X) (p Y)
    (qDeriv X') (p Y')
  have hpdiff := p_lipschitz_bound Y Y'
  have hqddiff := qDeriv_lipschitz_bound X X'
  have hpabs : |p Y| ≤ 1 := by
    rw [abs_of_nonneg (p_nonneg Y)]
    exact p_le_one Y
  have hqdabs : |qDeriv X'| ≤ (3 / 2 : ℝ) :=
    abs_qDeriv_le_three_halves X'
  have hfirst : |qDeriv X - qDeriv X'| * |p Y| ≤
      6 * |X - X'| := by
    calc
      |qDeriv X - qDeriv X'| * |p Y| ≤
          |qDeriv X - qDeriv X'| * 1 :=
        mul_le_mul_of_nonneg_left hpabs (abs_nonneg _)
      _ ≤ (6 * |X - X'|) * 1 :=
        mul_le_mul_of_nonneg_right hqddiff (by norm_num)
      _ = 6 * |X - X'| := by ring
  have hsecond : |qDeriv X'| * |p Y - p Y'| ≤
      (9 / 8 : ℝ) * |Y - Y'| := by
    calc
      |qDeriv X'| * |p Y - p Y'| ≤
          (3 / 2 : ℝ) * |p Y - p Y'| :=
        mul_le_mul_of_nonneg_right hqdabs (abs_nonneg _)
      _ ≤ (3 / 2 : ℝ) * ((3 / 4 : ℝ) * |Y - Y'|) :=
        mul_le_mul_of_nonneg_left hpdiff (by norm_num)
      _ = (9 / 8 : ℝ) * |Y - Y'| := by ring
  unfold qpPerspectiveUBase
  dsimp [X, Y, X', Y'] at hprod hfirst hsecond ⊢
  have hx0 : 0 ≤ |unitClip x - unitClip x'| := abs_nonneg _
  have hy0 : 0 ≤ |unitClip y - unitClip y'| := abs_nonneg _
  exact hprod.trans (by nlinarith)

theorem qpPerspectiveVBase_clip_lipschitz (x y x' y' : ℝ) :
    |qpPerspectiveVBase (unitClip x) (unitClip y) -
        qpPerspectiveVBase (unitClip x') (unitClip y')| ≤
      3 * (|unitClip x - unitClip x'| +
        |unitClip y - unitClip y'|) := by
  let X := unitClip x
  let Y := unitClip y
  let X' := unitClip x'
  let Y' := unitClip y'
  have hprod := abs_mul_sub_mul_le (q X) (pDeriv Y)
    (q X') (pDeriv Y')
  have hqdiff := q_lipschitz_bound X X'
  have hpddiff := pDeriv_lipschitz_bound Y Y'
  have hpdabs : |pDeriv Y| ≤ (3 / 4 : ℝ) :=
    abs_pDeriv_le_three_quarters Y
  have hqabs : |q X'| ≤ 1 := by
    rw [abs_of_nonneg (q_nonneg X')]
    exact q_le_one X'
  have hfirst : |q X - q X'| * |pDeriv Y| ≤
      (9 / 8 : ℝ) * |X - X'| := by
    calc
      |q X - q X'| * |pDeriv Y| ≤
          ((3 / 2 : ℝ) * |X - X'|) * |pDeriv Y| :=
        mul_le_mul_of_nonneg_right hqdiff (abs_nonneg _)
      _ ≤ ((3 / 2 : ℝ) * |X - X'|) * (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hpdabs (by positivity)
      _ = (9 / 8 : ℝ) * |X - X'| := by ring
  have hsecond : |q X'| * |pDeriv Y - pDeriv Y'| ≤
      (3 / 2 : ℝ) * |Y - Y'| := by
    calc
      |q X'| * |pDeriv Y - pDeriv Y'| ≤
          1 * |pDeriv Y - pDeriv Y'| :=
        mul_le_mul_of_nonneg_right hqabs (abs_nonneg _)
      _ ≤ 1 * ((3 / 2 : ℝ) * |Y - Y'|) :=
        mul_le_mul_of_nonneg_left hpddiff (by norm_num)
      _ = (3 / 2 : ℝ) * |Y - Y'| := by ring
  unfold qpPerspectiveVBase
  dsimp [X, Y, X', Y'] at hprod hfirst hsecond ⊢
  have hx0 : 0 ≤ |unitClip x - unitClip x'| := abs_nonneg _
  have hy0 : 0 ≤ |unitClip y - unitClip y'| := abs_nonneg _
  exact hprod.trans (by nlinarith)

theorem qpPerspectiveEtaBase_clip_lipschitz (x y x' y' : ℝ) :
    |qpPerspectiveEtaBase (unitClip x) (unitClip y) -
        qpPerspectiveEtaBase (unitClip x') (unitClip y')| ≤
      12 * (|unitClip x - unitClip x'| +
        |unitClip y - unitClip y'|) := by
  let X := unitClip x
  let Y := unitClip y
  let X' := unitClip x'
  let Y' := unitClip y'
  have hqdiff := q_lipschitz_bound X X'
  have hpdiff := p_lipschitz_bound Y Y'
  have hqabs : |q X'| ≤ 1 := by
    rw [abs_of_nonneg (q_nonneg X')]
    exact q_le_one X'
  have hpabs : |p Y| ≤ 1 := by
    rw [abs_of_nonneg (p_nonneg Y)]
    exact p_le_one Y
  have hA0 := abs_mul_sub_mul_le (q X) (p Y) (q X') (p Y')
  have hA : |2 * q X * p Y - 2 * q X' * p Y'| ≤
      3 * |X - X'| + (3 / 2 : ℝ) * |Y - Y'| := by
    have hfirst : |q X - q X'| * |p Y| ≤
        (3 / 2 : ℝ) * |X - X'| := by
      calc
        |q X - q X'| * |p Y| ≤
            ((3 / 2 : ℝ) * |X - X'|) * |p Y| :=
          mul_le_mul_of_nonneg_right hqdiff (abs_nonneg _)
        _ ≤ ((3 / 2 : ℝ) * |X - X'|) * 1 :=
          mul_le_mul_of_nonneg_left hpabs (by positivity)
        _ = (3 / 2 : ℝ) * |X - X'| := by ring
    have hsecond : |q X'| * |p Y - p Y'| ≤
        (3 / 4 : ℝ) * |Y - Y'| := by
      calc
        |q X'| * |p Y - p Y'| ≤ 1 * |p Y - p Y'| :=
          mul_le_mul_of_nonneg_right hqabs (abs_nonneg _)
        _ ≤ 1 * ((3 / 4 : ℝ) * |Y - Y'|) :=
          mul_le_mul_of_nonneg_left hpdiff (by norm_num)
        _ = (3 / 4 : ℝ) * |Y - Y'| := by ring
    have hbase := hA0.trans (add_le_add hfirst hsecond)
    rw [show 2 * q X * p Y - 2 * q X' * p Y' =
      2 * (q X * p Y - q X' * p Y') by ring, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith
  have hrDiff := clip_mul_qDeriv_lipschitz x x'
  have hrDiff' : |X * qDeriv X - X' * qDeriv X'| ≤
      (15 / 2 : ℝ) * |X - X'| := by
    simpa [X, X'] using hrDiff
  have hrAbs : |X' * qDeriv X'| ≤ (3 / 2 : ℝ) := by
    rw [abs_mul]
    have hX' := abs_unitClip_le_one x'
    have hd := abs_qDeriv_le_three_halves X'
    calc
      |X'| * |qDeriv X'| ≤ 1 * |qDeriv X'| :=
        mul_le_mul_of_nonneg_right hX' (abs_nonneg _)
      _ ≤ 1 * (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
      _ = (3 / 2 : ℝ) := by ring
  have hB0 := abs_mul_sub_mul_le (X * qDeriv X) (p Y)
    (X' * qDeriv X') (p Y')
  have hB : |X * qDeriv X * p Y - X' * qDeriv X' * p Y'| ≤
      (15 / 2 : ℝ) * |X - X'| +
        (9 / 8 : ℝ) * |Y - Y'| := by
    have hfirst : |X * qDeriv X - X' * qDeriv X'| * |p Y| ≤
        (15 / 2 : ℝ) * |X - X'| := by
      calc
        |X * qDeriv X - X' * qDeriv X'| * |p Y| ≤
            ((15 / 2 : ℝ) * |X - X'|) * |p Y| := by
          exact mul_le_mul_of_nonneg_right hrDiff' (abs_nonneg _)
        _ ≤ ((15 / 2 : ℝ) * |X - X'|) * 1 :=
          mul_le_mul_of_nonneg_left hpabs (by positivity)
        _ = (15 / 2 : ℝ) * |X - X'| := by ring
    have hsecond : |X' * qDeriv X'| * |p Y - p Y'| ≤
        (9 / 8 : ℝ) * |Y - Y'| := by
      calc
        |X' * qDeriv X'| * |p Y - p Y'| ≤
            (3 / 2 : ℝ) * |p Y - p Y'| :=
          mul_le_mul_of_nonneg_right hrAbs (abs_nonneg _)
        _ ≤ (3 / 2 : ℝ) * ((3 / 4 : ℝ) * |Y - Y'|) :=
          mul_le_mul_of_nonneg_left hpdiff (by norm_num)
        _ = (9 / 8 : ℝ) * |Y - Y'| := by ring
    exact hB0.trans (add_le_add hfirst hsecond)
  have hsDiff := clip_mul_pDeriv_lipschitz y y'
  have hsDiff' : |Y * pDeriv Y - Y' * pDeriv Y'| ≤
      (9 / 4 : ℝ) * |Y - Y'| := by
    simpa [Y, Y'] using hsDiff
  have hsAbs : |Y * pDeriv Y| ≤ (3 / 4 : ℝ) := by
    rw [abs_mul]
    have hY := abs_unitClip_le_one y
    have hd := abs_pDeriv_le_three_quarters Y
    calc
      |Y| * |pDeriv Y| ≤ 1 * |pDeriv Y| :=
        mul_le_mul_of_nonneg_right hY (abs_nonneg _)
      _ ≤ 1 * (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
      _ = (3 / 4 : ℝ) := by ring
  have hC0 := abs_mul_sub_mul_le (q X) (Y * pDeriv Y)
    (q X') (Y' * pDeriv Y')
  have hC : |Y * q X * pDeriv Y - Y' * q X' * pDeriv Y'| ≤
      (9 / 8 : ℝ) * |X - X'| +
        (9 / 4 : ℝ) * |Y - Y'| := by
    have hfirst : |q X - q X'| * |Y * pDeriv Y| ≤
        (9 / 8 : ℝ) * |X - X'| := by
      calc
        |q X - q X'| * |Y * pDeriv Y| ≤
            ((3 / 2 : ℝ) * |X - X'|) * |Y * pDeriv Y| :=
          mul_le_mul_of_nonneg_right hqdiff (abs_nonneg _)
        _ ≤ ((3 / 2 : ℝ) * |X - X'|) * (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hsAbs (by positivity)
        _ = (9 / 8 : ℝ) * |X - X'| := by ring
    have hsecond : |q X'| * |Y * pDeriv Y - Y' * pDeriv Y'| ≤
        (9 / 4 : ℝ) * |Y - Y'| := by
      calc
        |q X'| * |Y * pDeriv Y - Y' * pDeriv Y'| ≤
            1 * |Y * pDeriv Y - Y' * pDeriv Y'| :=
          mul_le_mul_of_nonneg_right hqabs (abs_nonneg _)
        _ ≤ 1 * ((9 / 4 : ℝ) * |Y - Y'|) := by
          exact mul_le_mul_of_nonneg_left hsDiff' (by norm_num)
        _ = (9 / 4 : ℝ) * |Y - Y'| := by ring
    have := hC0.trans (add_le_add hfirst hsecond)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using this
  unfold qpPerspectiveEtaBase
  have htri :
      |(2 * q X * p Y - X * qDeriv X * p Y - Y * q X * pDeriv Y) -
        (2 * q X' * p Y' - X' * qDeriv X' * p Y' -
          Y' * q X' * pDeriv Y')| ≤
      |2 * q X * p Y - 2 * q X' * p Y'| +
        |X * qDeriv X * p Y - X' * qDeriv X' * p Y'| +
        |Y * q X * pDeriv Y - Y' * q X' * pDeriv Y'| := by
    calc
      |(2 * q X * p Y - X * qDeriv X * p Y - Y * q X * pDeriv Y) -
        (2 * q X' * p Y' - X' * qDeriv X' * p Y' -
          Y' * q X' * pDeriv Y')| =
        |(2 * q X * p Y - 2 * q X' * p Y') -
          (X * qDeriv X * p Y - X' * qDeriv X' * p Y') -
          (Y * q X * pDeriv Y - Y' * q X' * pDeriv Y')| := by ring_nf
      _ ≤ |(2 * q X * p Y - 2 * q X' * p Y') -
          (X * qDeriv X * p Y - X' * qDeriv X' * p Y')| +
          |Y * q X * pDeriv Y - Y' * q X' * pDeriv Y'| := abs_sub _ _
      _ ≤ (|2 * q X * p Y - 2 * q X' * p Y'| +
          |X * qDeriv X * p Y - X' * qDeriv X' * p Y'|) +
          |Y * q X * pDeriv Y - Y' * q X' * pDeriv Y'| := by
        gcongr
        exact abs_sub _ _
  dsimp [X, Y, X', Y'] at htri hA hB hC ⊢
  nlinarith [abs_nonneg (unitClip x - unitClip x'),
    abs_nonneg (unitClip y - unitClip y')]

/-! ## Totalized first-homogeneous perspective gradients -/

def qPerspectiveEtaLift : ℝ → ℝ → ℝ :=
  scaleClipLift qPerspectiveEtaBase

def qPerspectiveULift : ℝ → ℝ → ℝ :=
  scaleClipLift qPerspectiveUBase

def pPerspectiveEtaLift : ℝ → ℝ → ℝ :=
  scaleClipLift pPerspectiveEtaBase

def pPerspectiveULift : ℝ → ℝ → ℝ :=
  scaleClipLift pPerspectiveUBase

def qpPerspectiveEtaLift : ℝ → ℝ → ℝ → ℝ :=
  scaleClipPairLift qpPerspectiveEtaBase

def qpPerspectiveULift : ℝ → ℝ → ℝ → ℝ :=
  scaleClipPairLift qpPerspectiveUBase

def qpPerspectiveVLift : ℝ → ℝ → ℝ → ℝ :=
  scaleClipPairLift qpPerspectiveVBase

theorem qPerspectiveEtaLift_eq_gradient {eta u : ℝ} (heta : 0 ≤ eta) :
    qPerspectiveEtaLift eta u =
      (quadraticPerspectiveGradient q qDeriv (eta, u)).1 := by
  rcases heta.eq_or_lt with rfl | heta
  · simp [qPerspectiveEtaLift, scaleClipLift, quadraticPerspectiveGradient]
  · rw [qPerspectiveEtaLift, scaleClipLift_eq_mul,
      qPerspectiveEtaBase_unitClip]
    simp [quadraticPerspectiveGradient, qPerspectiveEtaBase, heta.ne']

theorem qPerspectiveULift_eq_gradient {eta u : ℝ} (heta : 0 ≤ eta) :
    qPerspectiveULift eta u =
      (quadraticPerspectiveGradient q qDeriv (eta, u)).2 := by
  rcases heta.eq_or_lt with rfl | heta
  · simp [qPerspectiveULift, scaleClipLift, quadraticPerspectiveGradient]
  · rw [qPerspectiveULift, scaleClipLift_eq_mul,
      qPerspectiveUBase_unitClip]
    simp [quadraticPerspectiveGradient, qPerspectiveUBase, heta.ne']

theorem pPerspectiveEtaLift_eq_gradient {eta u : ℝ} (heta : 0 ≤ eta) :
    pPerspectiveEtaLift eta u =
      (quadraticPerspectiveGradient p pDeriv (eta, u)).1 := by
  rcases heta.eq_or_lt with rfl | heta
  · simp [pPerspectiveEtaLift, scaleClipLift, quadraticPerspectiveGradient]
  · rw [pPerspectiveEtaLift, scaleClipLift_eq_mul,
      pPerspectiveEtaBase_unitClip]
    simp [quadraticPerspectiveGradient, pPerspectiveEtaBase, heta.ne']

theorem pPerspectiveULift_eq_gradient {eta u : ℝ} (heta : 0 ≤ eta) :
    pPerspectiveULift eta u =
      (quadraticPerspectiveGradient p pDeriv (eta, u)).2 := by
  rcases heta.eq_or_lt with rfl | heta
  · simp [pPerspectiveULift, scaleClipLift, quadraticPerspectiveGradient]
  · rw [pPerspectiveULift, scaleClipLift_eq_mul,
      pPerspectiveUBase_unitClip]
    simp [quadraticPerspectiveGradient, pPerspectiveUBase, heta.ne']

theorem qPerspectiveEtaLift_lipschitz {eta theta u v : ℝ}
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta) :
    |qPerspectiveEtaLift eta u - qPerspectiveEtaLift theta v| ≤
      15 * (|eta - theta| + |u - v|) := by
  have h := abs_scaleClipLift_sub_scaleClipLift_le
    qPerspectiveEtaBase
    (M := (4 : ℝ)) (L := (11 : ℝ))
    (eta := eta) (theta := theta) (u := u) (v := v)
    abs_qPerspectiveEtaBase_clip_le_four
    qPerspectiveEtaBase_clip_lipschitz (by norm_num) heta htheta
  unfold qPerspectiveEtaLift
  exact h.trans (by nlinarith [abs_nonneg (eta - theta), abs_nonneg (u - v)])

theorem qPerspectiveULift_lipschitz {eta theta u v : ℝ}
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta) :
    |qPerspectiveULift eta u - qPerspectiveULift theta v| ≤
      8 * (|eta - theta| + |u - v|) := by
  have h := abs_scaleClipLift_sub_scaleClipLift_le
    qPerspectiveUBase
    (M := (2 : ℝ)) (L := (6 : ℝ))
    (eta := eta) (theta := theta) (u := u) (v := v)
    (fun x ↦ by simpa [qPerspectiveUBase_unitClip] using
      abs_qPerspectiveUBase_le_two (unitClip x))
    qPerspectiveUBase_clip_lipschitz (by norm_num) heta htheta
  unfold qPerspectiveULift
  exact h.trans (by nlinarith [abs_nonneg (eta - theta), abs_nonneg (u - v)])

theorem pPerspectiveEtaLift_lipschitz {eta theta u v : ℝ}
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta) :
    |pPerspectiveEtaLift eta u - pPerspectiveEtaLift theta v| ≤
      7 * (|eta - theta| + |u - v|) := by
  have h := abs_scaleClipLift_sub_scaleClipLift_le
    pPerspectiveEtaBase
    (M := (3 : ℝ)) (L := (4 : ℝ))
    (eta := eta) (theta := theta) (u := u) (v := v)
    abs_pPerspectiveEtaBase_clip_le_three
    pPerspectiveEtaBase_clip_lipschitz (by norm_num) heta htheta
  unfold pPerspectiveEtaLift
  exact h.trans (by nlinarith [abs_nonneg (eta - theta), abs_nonneg (u - v)])

theorem pPerspectiveULift_lipschitz {eta theta u v : ℝ}
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta) :
    |pPerspectiveULift eta u - pPerspectiveULift theta v| ≤
      3 * (|eta - theta| + |u - v|) := by
  have h := abs_scaleClipLift_sub_scaleClipLift_le
    pPerspectiveUBase
    (M := (1 : ℝ)) (L := (3 / 2 : ℝ))
    (eta := eta) (theta := theta) (u := u) (v := v)
    (fun x ↦ by simpa [pPerspectiveUBase_unitClip] using
      abs_pPerspectiveUBase_le_one (unitClip x))
    pPerspectiveUBase_clip_lipschitz (by norm_num) heta htheta
  unfold pPerspectiveULift
  exact h.trans (by nlinarith [abs_nonneg (eta - theta), abs_nonneg (u - v)])

theorem qpPerspectiveEtaLift_lipschitz
    {eta theta u v u' v' : ℝ} (heta : 0 ≤ eta) (htheta : 0 ≤ theta) :
    |qpPerspectiveEtaLift eta u v -
        qpPerspectiveEtaLift theta u' v'| ≤
      29 * (|eta - theta| + |u - u'| + |v - v'|) := by
  have hLip : ∀ x y x' y',
      |qpPerspectiveEtaBase (unitClip x) (unitClip y) -
          qpPerspectiveEtaBase (unitClip x') (unitClip y')| ≤
        12 * |unitClip x - unitClip x'| +
          12 * |unitClip y - unitClip y'| := by
    intro x y x' y'
    simpa [mul_add] using qpPerspectiveEtaBase_clip_lipschitz x y x' y'
  have h := abs_scaleClipPairLift_sub_scaleClipPairLift_le
    qpPerspectiveEtaBase
    (M := (5 : ℝ)) (Lx := (12 : ℝ)) (Ly := (12 : ℝ))
    (eta := eta) (theta := theta) (u := u) (v := v)
    (u' := u') (v' := v')
    abs_qpPerspectiveEtaBase_clip_le_five hLip
    (by norm_num) (by norm_num) heta htheta
  unfold qpPerspectiveEtaLift
  have he0 : 0 ≤ |eta - theta| := abs_nonneg _
  have hu0 : 0 ≤ |u - u'| := abs_nonneg _
  have hv0 : 0 ≤ |v - v'| := abs_nonneg _
  exact h.trans (by nlinarith)

theorem qpPerspectiveULift_lipschitz
    {eta theta u v u' v' : ℝ} (heta : 0 ≤ eta) (htheta : 0 ≤ theta) :
    |qpPerspectiveULift eta u v -
        qpPerspectiveULift theta u' v'| ≤
      18 * (|eta - theta| + |u - u'| + |v - v'|) := by
  have hLip : ∀ x y x' y',
      |qpPerspectiveUBase (unitClip x) (unitClip y) -
          qpPerspectiveUBase (unitClip x') (unitClip y')| ≤
        8 * |unitClip x - unitClip x'| +
          8 * |unitClip y - unitClip y'| := by
    intro x y x' y'
    simpa [mul_add] using qpPerspectiveUBase_clip_lipschitz x y x' y'
  have h := abs_scaleClipPairLift_sub_scaleClipPairLift_le
    qpPerspectiveUBase
    (M := (2 : ℝ)) (Lx := (8 : ℝ)) (Ly := (8 : ℝ))
    (eta := eta) (theta := theta) (u := u) (v := v)
    (u' := u') (v' := v')
    abs_qpPerspectiveUBase_clip_le_two hLip
    (by norm_num) (by norm_num) heta htheta
  unfold qpPerspectiveULift
  have he0 : 0 ≤ |eta - theta| := abs_nonneg _
  have hu0 : 0 ≤ |u - u'| := abs_nonneg _
  have hv0 : 0 ≤ |v - v'| := abs_nonneg _
  exact h.trans (by nlinarith)

theorem qpPerspectiveVLift_lipschitz
    {eta theta u v u' v' : ℝ} (heta : 0 ≤ eta) (htheta : 0 ≤ theta) :
    |qpPerspectiveVLift eta u v -
        qpPerspectiveVLift theta u' v'| ≤
      7 * (|eta - theta| + |u - u'| + |v - v'|) := by
  have hLip : ∀ x y x' y',
      |qpPerspectiveVBase (unitClip x) (unitClip y) -
          qpPerspectiveVBase (unitClip x') (unitClip y')| ≤
        3 * |unitClip x - unitClip x'| +
          3 * |unitClip y - unitClip y'| := by
    intro x y x' y'
    simpa [mul_add] using qpPerspectiveVBase_clip_lipschitz x y x' y'
  have h := abs_scaleClipPairLift_sub_scaleClipPairLift_le
    qpPerspectiveVBase
    (M := (1 : ℝ)) (Lx := (3 : ℝ)) (Ly := (3 : ℝ))
    (eta := eta) (theta := theta) (u := u) (v := v)
    (u' := u') (v' := v')
    abs_qpPerspectiveVBase_clip_le_one hLip
    (by norm_num) (by norm_num) heta htheta
  unfold qpPerspectiveVLift
  have he0 : 0 ≤ |eta - theta| := abs_nonneg _
  have hu0 : 0 ≤ |u - u'| := abs_nonneg _
  have hv0 : 0 ≤ |v - v'| := abs_nonneg _
  exact h.trans (by nlinarith)

end

end NCPLRevised
