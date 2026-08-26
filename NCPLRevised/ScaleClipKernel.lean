/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.Gates
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Scale--clip estimates for quadratic perspectives

The gradient of a two-homogeneous perspective contains first-homogeneous
terms of the form `eta * A (u / eta)`.  The lemmas in this file control such
terms uniformly as the nonnegative scale tends to zero.  They are purely
scalar and are reused for every coordinate of the residual and terminal
perspectives in Lemma 5.1.
-/

namespace NCPLRevised

noncomputable section

/-- Projection of a real number onto `[-1,1]`. -/
def unitClip (x : ℝ) : ℝ := max (-1) (min 1 x)

theorem neg_one_le_unitClip (x : ℝ) : -1 ≤ unitClip x := by
  exact le_max_left _ _

theorem unitClip_le_one (x : ℝ) : unitClip x ≤ 1 := by
  unfold unitClip
  exact max_le (by norm_num) (min_le_left _ _)

theorem abs_unitClip_le_one (x : ℝ) : |unitClip x| ≤ 1 := by
  rw [abs_le]
  exact ⟨neg_one_le_unitClip x, unitClip_le_one x⟩

theorem unitClip_of_le_neg_one {x : ℝ} (hx : x ≤ -1) :
    unitClip x = -1 := by
  unfold unitClip
  rw [min_eq_right (hx.trans (by norm_num)), max_eq_left hx]

theorem unitClip_of_mem {x : ℝ} (hlo : -1 ≤ x) (hhi : x ≤ 1) :
    unitClip x = x := by
  simp [unitClip, min_eq_right hhi, max_eq_right hlo]

theorem unitClip_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    unitClip x = 1 := by
  unfold unitClip
  rw [min_eq_left hx, max_eq_right (by norm_num)]

theorem unitClip_neg (x : ℝ) : unitClip (-x) = -unitClip x := by
  rcases le_total x (-1) with hx | hx
  · have hnx : 1 ≤ -x := by linarith
    rw [unitClip_of_le_neg_one hx, unitClip_of_one_le hnx]
    norm_num
  · rcases le_total 1 x with hx1 | hx1
    · have hnx : -x ≤ -1 := by linarith
      rw [unitClip_of_one_le hx1, unitClip_of_le_neg_one hnx]
    · have hnxlo : -1 ≤ -x := by linarith
      have hnxhi : -x ≤ 1 := by linarith
      rw [unitClip_of_mem hx hx1, unitClip_of_mem hnxlo hnxhi]

/-- Clipping is a Euclidean contraction. -/
theorem unitClip_lipschitz : LipschitzWith (1 : NNReal) unitClip := by
  unfold unitClip
  simpa [min_comm] using (LipschitzWith.id.min_const 1).const_max (-1)

theorem abs_unitClip_sub_unitClip_le (x y : ℝ) :
    |unitClip x - unitClip y| ≤ |x - y| := by
  have h := unitClip_lipschitz.dist_le_mul x y
  simpa [Real.dist_eq] using h

/-- At a fixed nonnegative numerator, changing a positive scale costs at
most the scale change after multiplication by the smaller scale. -/
theorem scale_mul_abs_unitClip_div_sub_unitClip_div_of_nonneg
    {eta theta v : ℝ} (heta : 0 < eta) (hetatheta : eta ≤ theta)
    (hv : 0 ≤ v) :
    eta * |unitClip (v / eta) - unitClip (v / theta)| ≤ theta - eta := by
  have htheta : 0 < theta := lt_of_lt_of_le heta hetatheta
  rcases le_total v eta with hve | hev
  · have hve0 : 0 ≤ v / eta := div_nonneg hv heta.le
    have hve1 : v / eta ≤ 1 := (div_le_one heta).2 hve
    have hvt0 : 0 ≤ v / theta := div_nonneg hv htheta.le
    have hvt1 : v / theta ≤ 1 := (div_le_one htheta).2 (hve.trans hetatheta)
    rw [unitClip_of_mem (by linarith) hve1,
      unitClip_of_mem (by linarith) hvt1]
    have hdiv : 0 ≤ v / eta - v / theta := by
      field_simp [heta.ne', htheta.ne']
      nlinarith
    have habs : |v / eta - v / theta| = v / eta - v / theta := by
      rw [abs_of_nonneg]
      exact hdiv
    rw [habs]
    field_simp [heta.ne', htheta.ne']
    nlinarith
  · rcases le_total v theta with hvt | htv
    · have he1 : 1 ≤ v / eta := (one_le_div heta).2 hev
      have hvt0 : 0 ≤ v / theta := div_nonneg hv htheta.le
      have hvt1 : v / theta ≤ 1 := (div_le_one htheta).2 hvt
      rw [unitClip_of_one_le he1, unitClip_of_mem (by linarith) hvt1]
      have habs : |1 - v / theta| = 1 - v / theta := by
        rw [abs_of_nonneg]
        linarith
      rw [habs]
      field_simp [htheta.ne']
      nlinarith
    · have he1 : 1 ≤ v / eta := (one_le_div heta).2 (hetatheta.trans htv)
      have ht1 : 1 ≤ v / theta := (one_le_div htheta).2 htv
      rw [unitClip_of_one_le he1, unitClip_of_one_le ht1]
      simp [sub_nonneg.2 hetatheta]

/-- Signed version of the fixed-numerator scale estimate. -/
theorem scale_mul_abs_unitClip_div_sub_unitClip_div
    {eta theta v : ℝ} (heta : 0 < eta) (hetatheta : eta ≤ theta) :
    eta * |unitClip (v / eta) - unitClip (v / theta)| ≤ theta - eta := by
  rcases le_total 0 v with hv | hv
  · exact scale_mul_abs_unitClip_div_sub_unitClip_div_of_nonneg
      heta hetatheta hv
  · have hneg : 0 ≤ -v := by linarith
    have h := scale_mul_abs_unitClip_div_sub_unitClip_div_of_nonneg
      (v := -v) heta hetatheta hneg
    have he : (-v) / eta = -(v / eta) := by ring
    have ht : (-v) / theta = -(v / theta) := by ring
    rw [he, ht, unitClip_neg, unitClip_neg] at h
    calc
      eta * |unitClip (v / eta) - unitClip (v / theta)| =
          eta * |-unitClip (v / eta) - -unitClip (v / theta)| := by
        congr 1
        rw [show -unitClip (v / eta) - -unitClip (v / theta) =
          -(unitClip (v / eta) - unitClip (v / theta)) by ring, abs_neg]
      _ ≤ theta - eta := h

/-- The scale--clip inequality used at every first-homogeneous perspective
gradient component.  It is total at scale zero. -/
theorem min_scale_mul_abs_unitClip_div_sub_unitClip_div
    {eta theta u v : ℝ} (heta : 0 ≤ eta) (htheta : 0 ≤ theta) :
    min eta theta * |unitClip (u / eta) - unitClip (v / theta)| ≤
      |u - v| + |eta - theta| := by
  rcases eq_or_lt_of_le heta with rfl | heta_pos
  · rw [min_eq_left htheta, zero_mul]
    positivity
  rcases eq_or_lt_of_le htheta with rfl | htheta_pos
  · rw [min_eq_right heta, zero_mul]
    positivity
  rcases le_total eta theta with het | hte
  · rw [min_eq_left het, abs_of_nonpos (sub_nonpos.2 het)]
    have hclip := abs_unitClip_sub_unitClip_le (u / eta) (v / eta)
    have hsame : eta * |unitClip (u / eta) - unitClip (v / eta)| ≤
        |u - v| := by
      have hmul := mul_le_mul_of_nonneg_left hclip heta
      calc
        eta * |unitClip (u / eta) - unitClip (v / eta)| ≤
            eta * |u / eta - v / eta| := hmul
        _ = |u - v| := by
          rw [← sub_div]
          rw [abs_div, abs_of_pos heta_pos]
          field_simp [heta_pos.ne']
    have hscale := scale_mul_abs_unitClip_div_sub_unitClip_div
      (v := v) heta_pos het
    have htri := abs_sub_le
      (unitClip (u / eta)) (unitClip (v / eta)) (unitClip (v / theta))
    have hmultri := mul_le_mul_of_nonneg_left htri heta
    nlinarith
  · rw [min_eq_right hte, abs_of_nonneg (sub_nonneg.2 hte)]
    have hclip := abs_unitClip_sub_unitClip_le (v / theta) (u / theta)
    have hsame : theta * |unitClip (v / theta) - unitClip (u / theta)| ≤
        |u - v| := by
      have hmul := mul_le_mul_of_nonneg_left hclip htheta
      calc
        theta * |unitClip (v / theta) - unitClip (u / theta)| ≤
            theta * |v / theta - u / theta| := hmul
        _ = |u - v| := by
          rw [← sub_div, abs_div, abs_of_pos htheta_pos]
          field_simp [htheta_pos.ne']
          rw [abs_sub_comm]
    have hscale := scale_mul_abs_unitClip_div_sub_unitClip_div
      (v := u) htheta_pos hte
    have htri := abs_sub_le
      (unitClip (v / theta)) (unitClip (u / theta)) (unitClip (u / eta))
    have hmultri := mul_le_mul_of_nonneg_left htri htheta
    rw [abs_sub_comm (unitClip (u / eta)) (unitClip (v / theta))]
    nlinarith

/-- Totalized first-homogeneous scale lift. -/
def scaleClipLift (A : ℝ → ℝ) (eta u : ℝ) : ℝ :=
  if eta = 0 then 0 else eta * A (unitClip (u / eta))

theorem scaleClipLift_eq_mul (A : ℝ → ℝ) (eta u : ℝ) :
    scaleClipLift A eta u = eta * A (unitClip (u / eta)) := by
  by_cases heta : eta = 0
  · simp [scaleClipLift, heta]
  · simp [scaleClipLift, heta]

/-- Generic scale-lift estimate.  The hypotheses are deliberately stated in
the exact pointwise form produced by the gate derivative bounds. -/
theorem abs_scaleClipLift_sub_scaleClipLift_le
    (A : ℝ → ℝ) {M L eta theta u v : ℝ}
    (hM : ∀ x, |A (unitClip x)| ≤ M)
    (hL : ∀ x y,
      |A (unitClip x) - A (unitClip y)| ≤
        L * |unitClip x - unitClip y|)
    (hL0 : 0 ≤ L) (heta : 0 ≤ eta) (htheta : 0 ≤ theta) :
    |scaleClipLift A eta u - scaleClipLift A theta v| ≤
      (M + L) * |eta - theta| + L * |u - v| := by
  rw [scaleClipLift_eq_mul, scaleClipLift_eq_mul]
  rcases le_total eta theta with het | hte
  · have hcore := min_scale_mul_abs_unitClip_div_sub_unitClip_div
      (u := u) (v := v) heta htheta
    rw [min_eq_left het, abs_of_nonpos (sub_nonpos.2 het)] at hcore
    rw [neg_sub] at hcore
    rw [abs_of_nonpos (sub_nonpos.2 het)]
    have hA := hL (u / eta) (v / theta)
    have hscaledA :
        eta * |A (unitClip (u / eta)) - A (unitClip (v / theta))| ≤
          L * (|u - v| + (theta - eta)) := by
      calc
        eta * |A (unitClip (u / eta)) - A (unitClip (v / theta))| ≤
            eta * (L * |unitClip (u / eta) - unitClip (v / theta)|) :=
          mul_le_mul_of_nonneg_left hA heta
        _ = L * (eta *
            |unitClip (u / eta) - unitClip (v / theta)|) := by ring
        _ ≤ L * (|u - v| + (theta - eta)) :=
          mul_le_mul_of_nonneg_left hcore hL0
    have hbound := hM (v / theta)
    have htri := abs_sub_le
      (eta * A (unitClip (u / eta)))
      (eta * A (unitClip (v / theta)))
      (theta * A (unitClip (v / theta)))
    have hscale :
        |eta * A (unitClip (v / theta)) -
            theta * A (unitClip (v / theta))| ≤
          M * (theta - eta) := by
      rw [← sub_mul, abs_mul, abs_of_nonpos (sub_nonpos.2 het),
        neg_sub]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left hbound (sub_nonneg.2 het)
    have hfirst :
        |eta * A (unitClip (u / eta)) -
            eta * A (unitClip (v / theta))| ≤
          L * (|u - v| + (theta - eta)) := by
      rw [← mul_sub, abs_mul, abs_of_nonneg heta]
      exact hscaledA
    exact htri.trans (add_le_add hfirst hscale) |>.trans (by ring_nf; rfl)
  · have hcore := min_scale_mul_abs_unitClip_div_sub_unitClip_div
      (u := v) (v := u) htheta heta
    rw [min_eq_left hte, abs_of_nonpos (sub_nonpos.2 hte)] at hcore
    rw [neg_sub] at hcore
    rw [abs_of_nonneg (sub_nonneg.2 hte)]
    have hA := hL (v / theta) (u / eta)
    have hscaledA :
        theta * |A (unitClip (v / theta)) - A (unitClip (u / eta))| ≤
          L * (|u - v| + (eta - theta)) := by
      calc
        theta * |A (unitClip (v / theta)) - A (unitClip (u / eta))| ≤
            theta * (L * |unitClip (v / theta) - unitClip (u / eta)|) :=
          mul_le_mul_of_nonneg_left hA htheta
        _ = L * (theta *
            |unitClip (v / theta) - unitClip (u / eta)|) := by ring
        _ ≤ L * (|v - u| + (eta - theta)) :=
          mul_le_mul_of_nonneg_left hcore hL0
        _ = L * (|u - v| + (eta - theta)) := by rw [abs_sub_comm]
    have hbound := hM (u / eta)
    have htri := abs_sub_le
      (theta * A (unitClip (v / theta)))
      (theta * A (unitClip (u / eta)))
      (eta * A (unitClip (u / eta)))
    have hscale :
        |theta * A (unitClip (u / eta)) -
            eta * A (unitClip (u / eta))| ≤
          M * (eta - theta) := by
      rw [← sub_mul, abs_mul, abs_of_nonpos (sub_nonpos.2 hte),
        neg_sub]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left hbound (sub_nonneg.2 hte)
    have hfirst :
        |theta * A (unitClip (v / theta)) -
            theta * A (unitClip (u / eta))| ≤
          L * (|u - v| + (eta - theta)) := by
      rw [← mul_sub, abs_mul, abs_of_nonneg htheta]
      exact hscaledA
    rw [abs_sub_comm]
    exact htri.trans (add_le_add hfirst hscale) |>.trans (by ring_nf; rfl)

end

end NCPLRevised
