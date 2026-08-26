/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.ScaleClipKernel

/-!
# Two-coordinate scale--clip lift

This is the gate-independent two-coordinate analogue of
`abs_scaleClipLift_sub_scaleClipLift_le`.  It is used for the residual
kernel `1-q(u)p(v)` without introducing any gate-specific names here.
-/

namespace NCPLRevised

noncomputable section

/-- Totalized first-homogeneous lift of a function of two clipped ratios. -/
def scaleClipPairLift (A : ℝ → ℝ → ℝ) (eta u v : ℝ) : ℝ :=
  if eta = 0 then 0 else
    eta * A (unitClip (u / eta)) (unitClip (v / eta))

theorem scaleClipPairLift_eq_mul (A : ℝ → ℝ → ℝ) (eta u v : ℝ) :
    scaleClipPairLift A eta u v =
      eta * A (unitClip (u / eta)) (unitClip (v / eta)) := by
  by_cases heta : eta = 0
  · simp [scaleClipPairLift, heta]
  · simp [scaleClipPairLift, heta]

/-- Uniform estimate for a first-homogeneous two-coordinate perspective
gradient component. -/
theorem abs_scaleClipPairLift_sub_scaleClipPairLift_le
    (A : ℝ → ℝ → ℝ) {M Lx Ly eta theta u v u' v' : ℝ}
    (hM : ∀ x y, |A (unitClip x) (unitClip y)| ≤ M)
    (hLip : ∀ x y x' y',
      |A (unitClip x) (unitClip y) -
          A (unitClip x') (unitClip y')| ≤
        Lx * |unitClip x - unitClip x'| +
          Ly * |unitClip y - unitClip y'|)
    (hLx : 0 ≤ Lx) (hLy : 0 ≤ Ly)
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta) :
    |scaleClipPairLift A eta u v -
        scaleClipPairLift A theta u' v'| ≤
      (M + Lx + Ly) * |eta - theta| +
        Lx * |u - u'| + Ly * |v - v'| := by
  rw [scaleClipPairLift_eq_mul, scaleClipPairLift_eq_mul]
  rcases le_total eta theta with het | hte
  · have hcoreU := min_scale_mul_abs_unitClip_div_sub_unitClip_div
      (u := u) (v := u') heta htheta
    have hcoreV := min_scale_mul_abs_unitClip_div_sub_unitClip_div
      (u := v) (v := v') heta htheta
    rw [min_eq_left het, abs_of_nonpos (sub_nonpos.2 het)] at hcoreU hcoreV
    rw [neg_sub] at hcoreU hcoreV
    rw [abs_of_nonpos (sub_nonpos.2 het)]
    have hA := hLip (u / eta) (v / eta) (u' / theta) (v' / theta)
    have hscaledA :
        eta * |A (unitClip (u / eta)) (unitClip (v / eta)) -
            A (unitClip (u' / theta)) (unitClip (v' / theta))| ≤
          Lx * (|u - u'| + (theta - eta)) +
            Ly * (|v - v'| + (theta - eta)) := by
      calc
        eta * |A (unitClip (u / eta)) (unitClip (v / eta)) -
            A (unitClip (u' / theta)) (unitClip (v' / theta))| ≤
          eta * (Lx * |unitClip (u / eta) - unitClip (u' / theta)| +
            Ly * |unitClip (v / eta) - unitClip (v' / theta)|) :=
              mul_le_mul_of_nonneg_left hA heta
        _ = Lx * (eta *
              |unitClip (u / eta) - unitClip (u' / theta)|) +
            Ly * (eta *
              |unitClip (v / eta) - unitClip (v' / theta)|) := by ring
        _ ≤ Lx * (|u - u'| + (theta - eta)) +
            Ly * (|v - v'| + (theta - eta)) :=
          add_le_add (mul_le_mul_of_nonneg_left hcoreU hLx)
            (mul_le_mul_of_nonneg_left hcoreV hLy)
    have hbound := hM (u' / theta) (v' / theta)
    have htri := abs_sub_le
      (eta * A (unitClip (u / eta)) (unitClip (v / eta)))
      (eta * A (unitClip (u' / theta)) (unitClip (v' / theta)))
      (theta * A (unitClip (u' / theta)) (unitClip (v' / theta)))
    have hfirst :
        |eta * A (unitClip (u / eta)) (unitClip (v / eta)) -
            eta * A (unitClip (u' / theta)) (unitClip (v' / theta))| ≤
          Lx * (|u - u'| + (theta - eta)) +
            Ly * (|v - v'| + (theta - eta)) := by
      rw [← mul_sub, abs_mul, abs_of_nonneg heta]
      exact hscaledA
    have hscale :
        |eta * A (unitClip (u' / theta)) (unitClip (v' / theta)) -
            theta * A (unitClip (u' / theta)) (unitClip (v' / theta))| ≤
          M * (theta - eta) := by
      rw [← sub_mul, abs_mul, abs_of_nonpos (sub_nonpos.2 het), neg_sub]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left hbound (sub_nonneg.2 het)
    exact htri.trans (add_le_add hfirst hscale) |>.trans (by ring_nf; rfl)
  · have hcoreU := min_scale_mul_abs_unitClip_div_sub_unitClip_div
      (u := u') (v := u) htheta heta
    have hcoreV := min_scale_mul_abs_unitClip_div_sub_unitClip_div
      (u := v') (v := v) htheta heta
    rw [min_eq_left hte, abs_of_nonpos (sub_nonpos.2 hte)] at hcoreU hcoreV
    rw [neg_sub] at hcoreU hcoreV
    rw [abs_of_nonneg (sub_nonneg.2 hte)]
    have hA := hLip (u' / theta) (v' / theta) (u / eta) (v / eta)
    have hscaledA :
        theta * |A (unitClip (u' / theta)) (unitClip (v' / theta)) -
            A (unitClip (u / eta)) (unitClip (v / eta))| ≤
          Lx * (|u - u'| + (eta - theta)) +
            Ly * (|v - v'| + (eta - theta)) := by
      calc
        theta * |A (unitClip (u' / theta)) (unitClip (v' / theta)) -
            A (unitClip (u / eta)) (unitClip (v / eta))| ≤
          theta * (Lx * |unitClip (u' / theta) - unitClip (u / eta)| +
            Ly * |unitClip (v' / theta) - unitClip (v / eta)|) :=
              mul_le_mul_of_nonneg_left hA htheta
        _ = Lx * (theta *
              |unitClip (u' / theta) - unitClip (u / eta)|) +
            Ly * (theta *
              |unitClip (v' / theta) - unitClip (v / eta)|) := by ring
        _ ≤ Lx * (|u' - u| + (eta - theta)) +
            Ly * (|v' - v| + (eta - theta)) :=
          add_le_add (mul_le_mul_of_nonneg_left hcoreU hLx)
            (mul_le_mul_of_nonneg_left hcoreV hLy)
        _ = Lx * (|u - u'| + (eta - theta)) +
            Ly * (|v - v'| + (eta - theta)) := by
          rw [abs_sub_comm u' u, abs_sub_comm v' v]
    have hbound := hM (u / eta) (v / eta)
    have htri := abs_sub_le
      (theta * A (unitClip (u' / theta)) (unitClip (v' / theta)))
      (theta * A (unitClip (u / eta)) (unitClip (v / eta)))
      (eta * A (unitClip (u / eta)) (unitClip (v / eta)))
    have hfirst :
        |theta * A (unitClip (u' / theta)) (unitClip (v' / theta)) -
            theta * A (unitClip (u / eta)) (unitClip (v / eta))| ≤
          Lx * (|u - u'| + (eta - theta)) +
            Ly * (|v - v'| + (eta - theta)) := by
      rw [← mul_sub, abs_mul, abs_of_nonneg htheta]
      exact hscaledA
    have hscale :
        |theta * A (unitClip (u / eta)) (unitClip (v / eta)) -
            eta * A (unitClip (u / eta)) (unitClip (v / eta))| ≤
          M * (eta - theta) := by
      rw [← sub_mul, abs_mul, abs_of_nonpos (sub_nonpos.2 hte), neg_sub]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left hbound (sub_nonneg.2 hte)
    rw [abs_sub_comm]
    exact htri.trans (add_le_add hfirst hscale) |>.trans (by ring_nf; rfl)

end

end NCPLRevised
