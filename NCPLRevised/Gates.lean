/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import Mathlib

/-!
# The scalar gates from Lemma 4.1

This file formalizes the functions `q` and `p` used in Section 4.1 of
*Lower Bounds for Nonconvex-PL Minimax Optimization*, together with the
explicit derivatives displayed in the paper and all inequalities in Lemma
4.1.
-/

namespace NCPLRevised

noncomputable section

/-- The cubic transition gate from `0` to `1`. -/
def q (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if t ≤ 1 then 3 * t ^ 2 - 2 * t ^ 3 else 1

/-- The shifted and dilated transition gate. -/
def p (t : ℝ) : ℝ := q ((t + 1) / 2)

/-- The negative part, written `t⁻` in the paper. -/
def negPart (t : ℝ) : ℝ := max (-t) 0

/-- The explicit derivative of `q`. -/
def qDeriv (t : ℝ) : ℝ :=
  if 0 < t ∧ t < 1 then 6 * t * (1 - t) else 0

/-- The explicit derivative of `p`. -/
def pDeriv (t : ℝ) : ℝ :=
  if -1 < t ∧ t < 1 then (3 / 4 : ℝ) * (1 - t ^ 2) else 0

@[simp] theorem q_of_nonpos {t : ℝ} (ht : t ≤ 0) : q t = 0 := by
  simp [q, ht]

theorem q_of_pos_of_le_one {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) :
    q t = 3 * t ^ 2 - 2 * t ^ 3 := by
  simp [q, not_le_of_gt h0, h1]

theorem q_of_one_lt {t : ℝ} (ht : 1 < t) : q t = 1 := by
  simp [q, not_le_of_gt ht, not_le_of_gt (lt_trans zero_lt_one ht)]

theorem q_of_one_le {t : ℝ} (ht : 1 ≤ t) : q t = 1 := by
  rcases ht.eq_or_lt with rfl | ht
  · norm_num [q]
  · exact q_of_one_lt ht

@[simp] theorem q_zero : q 0 = 0 := by simp [q]

@[simp] theorem q_one : q 1 = 1 := by norm_num [q]

@[simp] theorem qDeriv_of_nonpos {t : ℝ} (ht : t ≤ 0) : qDeriv t = 0 := by
  simp [qDeriv, not_lt_of_ge ht]

theorem qDeriv_of_pos_of_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    qDeriv t = 6 * t * (1 - t) := by
  simp [qDeriv, h0, h1]

@[simp] theorem qDeriv_of_one_le {t : ℝ} (ht : 1 ≤ t) : qDeriv t = 0 := by
  simp [qDeriv, not_lt_of_ge ht]

theorem pDeriv_of_mem {t : ℝ} (hneg : -1 < t) (hone : t < 1) :
    pDeriv t = (3 / 4 : ℝ) * (1 - t ^ 2) := by
  simp [pDeriv, hneg, hone]

@[simp] theorem pDeriv_of_le_neg_one {t : ℝ} (ht : t ≤ -1) : pDeriv t = 0 := by
  simp [pDeriv, not_lt_of_ge ht]

@[simp] theorem pDeriv_of_one_le {t : ℝ} (ht : 1 ≤ t) : pDeriv t = 0 := by
  simp [pDeriv, not_lt_of_ge ht]

@[simp] theorem negPart_of_nonneg {t : ℝ} (ht : 0 ≤ t) : negPart t = 0 := by
  simp [negPart, ht]

@[simp] theorem negPart_of_nonpos {t : ℝ} (ht : t ≤ 0) : negPart t = -t := by
  simp [negPart, ht]

theorem q_nonneg (t : ℝ) : 0 ≤ q t := by
  by_cases h0 : t ≤ 0
  · simp [q, h0]
  by_cases h1 : t ≤ 1
  · rw [q_of_pos_of_le_one (lt_of_not_ge h0) h1]
    have hs : 0 ≤ t ^ 2 := sq_nonneg t
    have hf : 0 ≤ 3 - 2 * t := by linarith
    nlinarith [mul_nonneg hs hf]
  · simp [q, h0, h1]

theorem q_le_one (t : ℝ) : q t ≤ 1 := by
  by_cases h0 : t ≤ 0
  · simp [q, h0]
  by_cases h1 : t ≤ 1
  · rw [q_of_pos_of_le_one (lt_of_not_ge h0) h1]
    have hs : 0 ≤ (1 - t) ^ 2 := sq_nonneg (1 - t)
    have hf : 0 ≤ 1 + 2 * t := by linarith
    have hp := mul_nonneg hs hf
    nlinarith
  · simp [q, h0, h1]

theorem q_mem_Icc (t : ℝ) : q t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨q_nonneg t, q_le_one t⟩

theorem p_nonneg (t : ℝ) : 0 ≤ p t := q_nonneg _

theorem p_le_one (t : ℝ) : p t ≤ 1 := q_le_one _

theorem p_mem_Icc (t : ℝ) : p t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨p_nonneg t, p_le_one t⟩

theorem qDeriv_nonneg (t : ℝ) : 0 ≤ qDeriv t := by
  by_cases h : 0 < t ∧ t < 1
  · rw [qDeriv_of_pos_of_lt_one h.1 h.2]
    exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt h.1))
      (sub_nonneg.mpr (le_of_lt h.2))
  · norm_num [qDeriv, h]

theorem qDeriv_le_three_halves (t : ℝ) : qDeriv t ≤ (3 / 2 : ℝ) := by
  by_cases h : 0 < t ∧ t < 1
  · rw [qDeriv_of_pos_of_lt_one h.1 h.2]
    nlinarith [sq_nonneg (2 * t - 1)]
  · norm_num [qDeriv, h]

theorem qDeriv_mem_Icc (t : ℝ) : qDeriv t ∈ Set.Icc (0 : ℝ) (3 / 2) :=
  ⟨qDeriv_nonneg t, qDeriv_le_three_halves t⟩

theorem pDeriv_nonneg (t : ℝ) : 0 ≤ pDeriv t := by
  by_cases h : -1 < t ∧ t < 1
  · rw [pDeriv_of_mem h.1 h.2]
    have : t ^ 2 ≤ 1 := by nlinarith
    nlinarith
  · norm_num [pDeriv, h]

theorem pDeriv_le_three_quarters (t : ℝ) : pDeriv t ≤ (3 / 4 : ℝ) := by
  by_cases h : -1 < t ∧ t < 1
  · rw [pDeriv_of_mem h.1 h.2]
    nlinarith [sq_nonneg t]
  · norm_num [pDeriv, h]

theorem pDeriv_mem_Icc (t : ℝ) : pDeriv t ∈ Set.Icc (0 : ℝ) (3 / 4) :=
  ⟨pDeriv_nonneg t, pDeriv_le_three_quarters t⟩

/-- Monotonicity of the cubic on its transition interval. -/
private theorem cubic_mono_on {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    3 * x ^ 2 - 2 * x ^ 3 ≤ 3 * y ^ 2 - 2 * y ^ 3 := by
  have hx1 : x ≤ 1 := hxy.trans hy1
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hxx : x ^ 2 ≤ x := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  have hyy : y ^ 2 ≤ y := by
    nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]
  have hsq : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  have hfac : 0 ≤ 3 * (x + y) - 2 * (x ^ 2 + x * y + y ^ 2) := by
    nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr hxy) hfac
  nlinarith

theorem q_monotone : Monotone q := by
  intro x y hxy
  by_cases hy0 : y ≤ 0
  · rw [q_of_nonpos (hxy.trans hy0), q_of_nonpos hy0]
  by_cases hx0 : x ≤ 0
  · rw [q_of_nonpos hx0]
    exact q_nonneg y
  by_cases hx1 : x ≤ 1
  · by_cases hy1 : y ≤ 1
    · rw [q_of_pos_of_le_one (lt_of_not_ge hx0) hx1,
          q_of_pos_of_le_one (lt_of_not_ge hy0) hy1]
      exact cubic_mono_on (le_of_lt (lt_of_not_ge hx0)) hxy hy1
    · rw [q_of_pos_of_le_one (lt_of_not_ge hx0) hx1,
          q_of_one_lt (lt_of_not_ge hy1)]
      have h := q_le_one x
      rw [q_of_pos_of_le_one (lt_of_not_ge hx0) hx1] at h
      exact h
  · have hxlt : 1 < x := lt_of_not_ge hx1
    rw [q_of_one_lt hxlt, q_of_one_lt (hxlt.trans_le hxy)]

theorem p_ge_q (t : ℝ) : q t ≤ p t := by
  by_cases ht : t ≤ 1
  · change q t ≤ q ((t + 1) / 2)
    apply q_monotone
    linarith
  · have ht' : 1 < t := lt_of_not_ge ht
    simp [p, q_of_one_lt ht', q_of_one_lt (show 1 < (t + 1) / 2 by linarith)]

private def qPoly (x : ℝ) : ℝ := 3 * x ^ 2 - 2 * x ^ 3

private theorem hasDerivAt_qPoly (x : ℝ) :
    HasDerivAt qPoly (6 * x - 6 * x ^ 2) x := by
  unfold qPoly
  have h2 := ((hasDerivAt_id x).pow 2).const_mul 3
  have h3 := ((hasDerivAt_id x).pow 3).const_mul 2
  have h := h2.sub h3
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one] at h
  change HasDerivAt (fun y : ℝ ↦ 3 * y ^ 2 - 2 * y ^ 3) _ x at h
  exact h.congr_deriv (by ring)

private theorem q_eq_poly {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    q x = qPoly x := by
  rcases hx.1.eq_or_lt with hzero | hpos
  · subst x
    norm_num [q, qPoly]
  · simp [q, qPoly, not_le.mpr hpos, hx.2]

private theorem hasDerivWithinAt_q_left_zero :
    HasDerivWithinAt q 0 (Set.Iic (0 : ℝ)) 0 := by
  refine (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ))).hasDerivWithinAt.congr ?_ ?_
  · intro x hx
    exact q_of_nonpos hx
  · exact q_zero

private theorem hasDerivWithinAt_q_middle (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt q (6 * x - 6 * x ^ 2) (Set.Icc (0 : ℝ) 1) x := by
  refine (hasDerivAt_qPoly x).hasDerivWithinAt.congr ?_ ?_
  · intro y hy
    exact q_eq_poly hy
  · exact q_eq_poly hx

private theorem hasDerivWithinAt_q_right_one :
    HasDerivWithinAt q 0 (Set.Ici (1 : ℝ)) 1 := by
  refine (hasDerivAt_const (x := (1 : ℝ)) (c := (1 : ℝ))).hasDerivWithinAt.congr ?_ ?_
  · intro x hx
    exact q_of_one_le hx
  · exact q_one

private theorem hasDerivAt_q_zero : HasDerivAt q 0 0 := by
  have hm : HasDerivWithinAt q 0 (Set.Icc (0 : ℝ) 1) 0 := by
    simpa using hasDerivWithinAt_q_middle 0 (by norm_num)
  have hu := hasDerivWithinAt_q_left_zero.union hm
  have hset : Set.Iic (0 : ℝ) ∪ Set.Icc 0 1 = Set.Iic 1 := by
    ext x
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc]
    constructor <;> intro h
    · rcases h with h | h <;> linarith
    · by_cases hx : x ≤ 0
      · exact Or.inl hx
      · exact Or.inr ⟨le_of_not_ge hx, h⟩
  rw [hset] at hu
  exact hu.hasDerivAt (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))

private theorem hasDerivAt_q_one : HasDerivAt q 0 1 := by
  have hm : HasDerivWithinAt q 0 (Set.Icc (0 : ℝ) 1) 1 := by
    simpa using hasDerivWithinAt_q_middle 1 (by norm_num)
  have hu := hm.union hasDerivWithinAt_q_right_one
  have hset : Set.Icc (0 : ℝ) 1 ∪ Set.Ici 1 = Set.Ici 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
    constructor <;> intro h
    · rcases h with h | h <;> linarith
    · by_cases hx : x ≤ 1
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (le_of_not_ge hx)
  rw [hset] at hu
  exact hu.hasDerivAt (Ici_mem_nhds (by norm_num : (0 : ℝ) < 1))

/-- `qDeriv` is the actual derivative of `q`, including at both splice points. -/
theorem hasDerivAt_q (t : ℝ) : HasDerivAt q (qDeriv t) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hc : HasDerivWithinAt q 0 (Set.Iic (0 : ℝ)) t := by
      refine (hasDerivAt_const (x := t) (c := (0 : ℝ))).hasDerivWithinAt.congr ?_ ?_
      · intro x hx
        exact q_of_nonpos hx
      · exact q_of_nonpos ht.le
    have hd := hc.hasDerivAt (Iic_mem_nhds ht)
    simpa [qDeriv, not_lt_of_ge ht.le] using hd
  · simpa [qDeriv] using hasDerivAt_q_zero
  · rcases lt_trichotomy t 1 with ht1 | rfl | ht1
    · have hm := hasDerivWithinAt_q_middle t ⟨ht.le, ht1.le⟩
      have hd := hm.hasDerivAt (Icc_mem_nhds ht ht1)
      have heq : qDeriv t = 6 * t - 6 * t ^ 2 := by
        rw [qDeriv_of_pos_of_lt_one ht ht1]
        ring
      rw [heq]
      exact hd
    · simpa [qDeriv] using hasDerivAt_q_one
    · have hc : HasDerivWithinAt q 0 (Set.Ici (1 : ℝ)) t := by
        refine (hasDerivAt_const (x := t) (c := (1 : ℝ))).hasDerivWithinAt.congr ?_ ?_
        · intro x hx
          exact q_of_one_le hx
        · exact q_of_one_le ht1.le
      have hd := hc.hasDerivAt (Ici_mem_nhds ht1)
      simpa [qDeriv, not_lt_of_ge ht1.le] using hd

theorem differentiable_q : Differentiable ℝ q :=
  fun t ↦ (hasDerivAt_q t).differentiableAt

theorem deriv_q (t : ℝ) : deriv q t = qDeriv t :=
  (hasDerivAt_q t).deriv

theorem pDeriv_eq_half_qDeriv (t : ℝ) :
    pDeriv t = (1 / 2 : ℝ) * qDeriv ((t + 1) / 2) := by
  by_cases hlo : t ≤ -1
  · have harg : (t + 1) / 2 ≤ 0 := by linarith
    simp [pDeriv_of_le_neg_one hlo, qDeriv_of_nonpos harg]
  by_cases hhi : 1 ≤ t
  · have harg : 1 ≤ (t + 1) / 2 := by linarith
    simp [pDeriv_of_one_le hhi, qDeriv_of_one_le harg]
  · have hlo' : -1 < t := lt_of_not_ge hlo
    have hhi' : t < 1 := lt_of_not_ge hhi
    have harg0 : 0 < (t + 1) / 2 := by linarith
    have harg1 : (t + 1) / 2 < 1 := by linarith
    rw [pDeriv_of_mem hlo' hhi', qDeriv_of_pos_of_lt_one harg0 harg1]
    ring

/-- `pDeriv` is the actual derivative of `p`, by the chain rule. -/
theorem hasDerivAt_p (t : ℝ) : HasDerivAt p (pDeriv t) t := by
  have hi : HasDerivAt (fun x : ℝ ↦ (x + 1) / 2) (1 / 2 : ℝ) t := by
    have h := ((hasDerivAt_id t).add_const 1).const_mul (1 / 2 : ℝ)
    convert h using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext x
      simp [id_eq]
      ring
    · ring
  have hc := (hasDerivAt_q ((t + 1) / 2)).comp t hi
  convert hc using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · rfl
  · rw [pDeriv_eq_half_qDeriv]
    ring

theorem differentiable_p : Differentiable ℝ p :=
  fun t ↦ (hasDerivAt_p t).differentiableAt

theorem deriv_p (t : ℝ) : deriv p t = pDeriv t :=
  (hasDerivAt_p t).deriv

/-- A pointwise form of the `6`-Lipschitz bound for `qDeriv`. -/
theorem qDeriv_lipschitz_bound (x y : ℝ) :
    |qDeriv x - qDeriv y| ≤ 6 * |x - y| := by
  wlog hxy : x ≤ y generalizing x y
  · have hyx : y ≤ x := le_of_not_ge hxy
    have h := this y x hyx
    simpa [abs_sub_comm] using h
  by_cases hy0 : y ≤ 0
  · have hx0 : x ≤ 0 := hxy.trans hy0
    simp [qDeriv_of_nonpos hx0, qDeriv_of_nonpos hy0]
  by_cases hx1 : 1 ≤ x
  · have hy1 : 1 ≤ y := hx1.trans hxy
    simp [qDeriv_of_one_le hx1, qDeriv_of_one_le hy1]
  by_cases hx0 : x ≤ 0
  · by_cases hy1 : 1 ≤ y
    · simp [qDeriv_of_nonpos hx0, qDeriv_of_one_le hy1]
    · have hypos : 0 < y := lt_of_not_ge hy0
      have hylt : y < 1 := lt_of_not_ge hy1
      rw [qDeriv_of_nonpos hx0, qDeriv_of_pos_of_lt_one hypos hylt]
      have hnonneg : 0 ≤ y * (1 - y) := mul_nonneg (le_of_lt hypos) (sub_nonneg.mpr (le_of_lt hylt))
      have hsign : 0 - 6 * y * (1 - y) ≤ 0 := by nlinarith
      rw [abs_of_nonpos hsign, abs_of_nonpos (sub_nonpos.mpr hxy)]
      have hle : y * (1 - y) ≤ y - x := by nlinarith [sq_nonneg y]
      nlinarith
  by_cases hy1 : 1 ≤ y
  · have hxpos : 0 < x := lt_of_not_ge hx0
    have hxlt : x < 1 := lt_of_not_ge hx1
    rw [qDeriv_of_pos_of_lt_one hxpos hxlt, qDeriv_of_one_le hy1]
    have hsign : 0 ≤ 6 * x * (1 - x) - 0 := by
      simpa using mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) (le_of_lt hxpos))
        (sub_nonneg.mpr (le_of_lt hxlt))
    rw [abs_of_nonneg hsign, abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hle : x * (1 - x) ≤ y - x := by
      have : x * (1 - x) ≤ 1 - x := by nlinarith [sq_nonneg (1 - x)]
      linarith
    nlinarith
  · have hxpos : 0 < x := lt_of_not_ge hx0
    have hxlt : x < 1 := lt_of_not_ge hx1
    have hypos : 0 < y := lt_of_not_ge hy0
    have hylt : y < 1 := lt_of_not_ge hy1
    rw [qDeriv_of_pos_of_lt_one hxpos hxlt,
      qDeriv_of_pos_of_lt_one hypos hylt]
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hsum : |1 - (x + y)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hid : 6 * x * (1 - x) - 6 * y * (1 - y) =
        6 * (x - y) * (1 - (x + y)) := by ring
    calc
      |6 * x * (1 - x) - 6 * y * (1 - y)|
          = 6 * (y - x) * |1 - (x + y)| := by
              rw [hid, abs_mul, abs_mul]
              rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
              rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
              ring
      _ ≤ 6 * (y - x) * 1 := by
            gcongr
      _ = 6 * (y - x) := by ring
      _ = 6 * -(x - y) := by ring

theorem qDeriv_lipschitz : LipschitzWith 6 qDeriv := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [Real.dist_eq] using qDeriv_lipschitz_bound x y

/-- A pointwise form of the `3/2`-Lipschitz bound for `pDeriv`. -/
theorem pDeriv_lipschitz_bound (x y : ℝ) :
    |pDeriv x - pDeriv y| ≤ (3 / 2 : ℝ) * |x - y| := by
  rw [pDeriv_eq_half_qDeriv, pDeriv_eq_half_qDeriv]
  have h := qDeriv_lipschitz_bound ((x + 1) / 2) ((y + 1) / 2)
  calc
    |(1 / 2 : ℝ) * qDeriv ((x + 1) / 2) -
        (1 / 2 : ℝ) * qDeriv ((y + 1) / 2)| =
        (1 / 2 : ℝ) * |qDeriv ((x + 1) / 2) - qDeriv ((y + 1) / 2)| := by
          rw [← mul_sub, abs_mul]
          norm_num
    _ ≤ (1 / 2 : ℝ) * (6 * |(x + 1) / 2 - (y + 1) / 2|) := by
          exact mul_le_mul_of_nonneg_left h (by norm_num)
    _ = (3 / 2 : ℝ) * |x - y| := by
          have heq : (x + 1) / 2 - (y + 1) / 2 = (x - y) / 2 := by ring
          rw [heq, abs_div]
          norm_num
          ring

theorem pDeriv_lipschitz : LipschitzWith (3 / 2) pDeriv := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [Real.dist_eq] using pDeriv_lipschitz_bound x y

/-- The final scalar inequality in Lemma 4.1. -/
theorem one_sub_q_le (t : ℝ) :
    1 - q t ≤ 2 * ((pDeriv t) ^ 2 + (negPart t) ^ 2) := by
  by_cases hneg1 : t ≤ -1
  · have ht0 : t ≤ 0 := hneg1.trans (by norm_num)
    rw [q_of_nonpos ht0, pDeriv_of_le_neg_one hneg1, negPart_of_nonpos ht0]
    nlinarith [sq_nonneg t]
  by_cases ht0 : t ≤ 0
  · have hneg1' : -1 < t := lt_of_not_ge hneg1
    rw [q_of_nonpos ht0, pDeriv_of_mem hneg1' (lt_of_le_of_lt ht0 zero_lt_one),
      negPart_of_nonpos ht0]
    nlinarith [sq_nonneg (3 * t ^ 2 - (1 / 3 : ℝ))]
  by_cases ht1 : t < 1
  · have ht0' : 0 < t := lt_of_not_ge ht0
    rw [q_of_pos_of_le_one ht0' (le_of_lt ht1),
      pDeriv_of_mem (by linarith) ht1, negPart_of_nonneg (le_of_lt ht0')]
    have hcoef : 1 + 2 * t ≤ (9 / 8 : ℝ) * (1 + t) ^ 2 := by
      nlinarith [sq_nonneg t]
    have hmul := mul_le_mul_of_nonneg_left hcoef (sq_nonneg (1 - t))
    calc
      1 - (3 * t ^ 2 - 2 * t ^ 3) = (1 - t) ^ 2 * (1 + 2 * t) := by ring
      _ ≤ (1 - t) ^ 2 * ((9 / 8 : ℝ) * (1 + t) ^ 2) := hmul
      _ = 2 * (((3 / 4 : ℝ) * (1 - t ^ 2)) ^ 2 + 0 ^ 2) := by ring
  · have ht1' : 1 ≤ t := le_of_not_gt ht1
    rw [q_of_one_le ht1']
    nlinarith [sq_nonneg (pDeriv t), sq_nonneg (negPart t)]

/-- Lemma 4.1, bundled in exactly the order used in the paper. -/
theorem lemma4_1 (t : ℝ) :
    (0 ≤ q t ∧ q t ≤ 1) ∧
    (0 ≤ qDeriv t ∧ qDeriv t ≤ (3 / 2 : ℝ)) ∧
    LipschitzWith 6 qDeriv ∧
    (0 ≤ p t ∧ p t ≤ 1) ∧
    (0 ≤ pDeriv t ∧ pDeriv t ≤ (3 / 4 : ℝ)) ∧
    LipschitzWith (3 / 2) pDeriv ∧
    q t ≤ p t ∧
    1 - q t ≤ 2 * ((pDeriv t) ^ 2 + (negPart t) ^ 2) := by
  exact ⟨⟨q_nonneg t, q_le_one t⟩,
    ⟨qDeriv_nonneg t, qDeriv_le_three_halves t⟩,
    qDeriv_lipschitz,
    ⟨p_nonneg t, p_le_one t⟩,
    ⟨pDeriv_nonneg t, pDeriv_le_three_quarters t⟩,
    pDeriv_lipschitz,
    p_ge_q t, one_sub_q_le t⟩

end

end NCPLRevised
