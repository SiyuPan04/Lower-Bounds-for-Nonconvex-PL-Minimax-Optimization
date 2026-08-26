/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.CarmonActivation
import NCPLRevised.PerspectiveGradientLipschitz

/-!
# Dimension-free smoothness of the terminal perspective

The active terminal contribution to an embedded cell is

`rho(s)^2 * alpha(t) * q(u / rho(s))`.

This file totalizes its value and three coordinate-gradient components at
zero scale and proves a single, deliberately coarse, numerical Euclidean
Lipschitz estimate.  The estimate is independent of the inner-chain length.
-/

namespace NCPLRevised

noncomputable section

/-! ## Totalized value perspective -/

/-- The continuous two-homogeneous value perspective `eta^2 q(u/eta)`,
written using the total first-homogeneous scale--clip lift. -/
def qPerspectiveValueLift (eta u : ℝ) : ℝ :=
  eta * scaleClipLift q eta u

theorem abs_scaleClipLift_q_le {eta u : ℝ} (heta : 0 ≤ eta) :
    |scaleClipLift q eta u| ≤ eta := by
  rw [scaleClipLift_eq_mul, abs_mul, abs_of_nonneg heta]
  have hq := q_mem_Icc (unitClip (u / eta))
  rw [abs_of_nonneg hq.1]
  calc
    eta * q (unitClip (u / eta)) ≤ eta * 1 :=
      mul_le_mul_of_nonneg_left hq.2 heta
    _ = eta := by ring

theorem abs_qPerspectiveValueLift_le_four {eta u : ℝ}
    (heta : 0 ≤ eta) (hetaTwo : eta ≤ 2) :
    |qPerspectiveValueLift eta u| ≤ 4 := by
  unfold qPerspectiveValueLift
  rw [abs_mul, abs_of_nonneg heta]
  have hscale := abs_scaleClipLift_q_le (u := u) heta
  nlinarith

/-- On the scale interval used by the Carmon activation, the terminal value
perspective has a uniform two-variable Lipschitz bound. -/
theorem qPerspectiveValueLift_lipschitz
    {eta theta u v : ℝ}
    (heta : 0 ≤ eta) (hetaTwo : eta ≤ 2)
    (htheta : 0 ≤ theta) (hthetaTwo : theta ≤ 2) :
    |qPerspectiveValueLift eta u - qPerspectiveValueLift theta v| ≤
      7 * |eta - theta| + 3 * |u - v| := by
  have hlift := abs_scaleClipLift_sub_scaleClipLift_le q
    (M := (1 : ℝ)) (L := (3 / 2 : ℝ))
    (eta := eta) (theta := theta) (u := u) (v := v)
    (fun x ↦ by
      have hq := q_mem_Icc (unitClip x)
      rw [abs_of_nonneg hq.1]
      exact hq.2)
    (fun x y ↦ by
      simpa using q_lipschitz_bound (unitClip x) (unitClip y))
    (by norm_num) heta htheta
  have hthetaLift := abs_scaleClipLift_q_le (u := v) htheta
  have htri := abs_sub_le
    (eta * scaleClipLift q eta u)
    (eta * scaleClipLift q theta v)
    (theta * scaleClipLift q theta v)
  have hfirst :
      |eta * scaleClipLift q eta u - eta * scaleClipLift q theta v| ≤
        5 * |eta - theta| + 3 * |u - v| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg heta]
    have hmul := mul_le_mul_of_nonneg_left hlift heta
    nlinarith [abs_nonneg (eta - theta), abs_nonneg (u - v)]
  have hsecond :
      |eta * scaleClipLift q theta v - theta * scaleClipLift q theta v| ≤
        2 * |eta - theta| := by
    rw [← sub_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left hthetaLift (abs_nonneg (eta - theta)) |>.trans
      (by
        have hd := abs_nonneg (eta - theta)
        nlinarith)
  unfold qPerspectiveValueLift
  exact htri.trans (add_le_add hfirst hsecond) |>.trans (by ring_nf; rfl)

/-! ## Uniform bounds for the two first-homogeneous derivative lifts -/

theorem abs_qPerspectiveEtaLift_le_eight {eta u : ℝ}
    (heta : 0 ≤ eta) (hetaTwo : eta ≤ 2) :
    |qPerspectiveEtaLift eta u| ≤ 8 := by
  unfold qPerspectiveEtaLift
  rw [scaleClipLift_eq_mul, abs_mul, abs_of_nonneg heta]
  have hbase := abs_qPerspectiveEtaBase_clip_le_four (u / eta)
  nlinarith

theorem abs_qPerspectiveULift_le_four {eta u : ℝ}
    (heta : 0 ≤ eta) (hetaTwo : eta ≤ 2) :
    |qPerspectiveULift eta u| ≤ 4 := by
  unfold qPerspectiveULift
  rw [scaleClipLift_eq_mul, abs_mul, abs_of_nonneg heta]
  have hbase := abs_qPerspectiveUBase_le_two (unitClip (u / eta))
  nlinarith

/-! ## The two Carmon terminal branches -/

inductive TerminalBranch where
  | plus
  | minus
  deriving DecidableEq

def terminalAlpha : TerminalBranch → ℝ → ℝ
  | .plus => carmonAlphaPlus
  | .minus => carmonAlphaMinus

/-- Actual derivative of `terminalAlpha branch`. -/
def terminalAlphaDeriv : TerminalBranch → ℝ → ℝ
  | .plus => fun t ↦ -carmonPhiDeriv t
  | .minus => fun t ↦ -carmonPhiDeriv (-t)

theorem hasDerivAt_terminalAlpha (branch : TerminalBranch) (t : ℝ) :
    HasDerivAt (terminalAlpha branch) (terminalAlphaDeriv branch t) t := by
  cases branch with
  | plus =>
      have h := (hasDerivAt_const (x := t) (c := (5 : ℝ))).sub
        (hasDerivAt_carmonPhi t)
      convert h using 1
      all_goals try { apply AddCommGroup.ext <;> rfl }
      all_goals try { apply Module.ext <;> rfl }
      · funext x
        rfl
      · simp only [terminalAlphaDeriv]
        ring
  | minus =>
      have hneg := (hasDerivAt_carmonPhi (-t)).comp t (hasDerivAt_id t).neg
      have h := (hasDerivAt_const (x := t) (c := (5 : ℝ))).add hneg
      convert h using 1
      all_goals try { apply AddCommGroup.ext <;> rfl }
      all_goals try { apply Module.ext <;> rfl }
      · funext x
        rfl
      · simp only [terminalAlphaDeriv]
        ring

theorem terminalAlpha_pos (branch : TerminalBranch) (t : ℝ) :
    0 < terminalAlpha branch t := by
  cases branch with
  | plus => exact carmonAlphaPlus_pos t
  | minus => exact carmonAlphaMinus_pos t

theorem terminalAlpha_le_ten (branch : TerminalBranch) (t : ℝ) :
    terminalAlpha branch t ≤ 10 := by
  cases branch with
  | plus => exact (carmonAlphaPlus_lt_ten t).le
  | minus => exact (carmonAlphaMinus_lt_ten t).le

theorem abs_terminalAlpha_le_ten (branch : TerminalBranch) (t : ℝ) :
    |terminalAlpha branch t| ≤ 10 := by
  rw [abs_of_pos (terminalAlpha_pos branch t)]
  exact terminalAlpha_le_ten branch t

theorem abs_terminalAlphaDeriv_le_two (branch : TerminalBranch) (t : ℝ) :
    |terminalAlphaDeriv branch t| ≤ 2 := by
  cases branch with
  | plus =>
      simpa [terminalAlphaDeriv] using (abs_carmonPhiDeriv_lt_two t).le
  | minus =>
      simpa [terminalAlphaDeriv] using (abs_carmonPhiDeriv_lt_two (-t)).le

theorem terminalAlpha_lipschitz
    (branch : TerminalBranch) (t t' : ℝ) :
    |terminalAlpha branch t - terminalAlpha branch t'| ≤
      2 * |t - t'| := by
  have hLip : LipschitzWith (2 : NNReal) (terminalAlpha branch) := by
    apply lipschitzWith_of_nnnorm_deriv_le
    · exact fun x ↦ (hasDerivAt_terminalAlpha branch x).differentiableAt
    · intro x
      rw [(hasDerivAt_terminalAlpha branch x).deriv, ← NNReal.coe_le_coe]
      simpa [Real.norm_eq_abs] using abs_terminalAlphaDeriv_le_two branch x
  simpa [Real.dist_eq] using hLip.dist_le_mul t t'

theorem terminalAlphaDeriv_lipschitz
    (branch : TerminalBranch) (t t' : ℝ) :
    |terminalAlphaDeriv branch t - terminalAlphaDeriv branch t'| ≤
      |t - t'| := by
  have h := carmonPhiDeriv_lipschitz_one.dist_le_mul
  cases branch with
  | plus =>
      change |-carmonPhiDeriv t - -carmonPhiDeriv t'| ≤ |t - t'|
      rw [show -carmonPhiDeriv t - -carmonPhiDeriv t' =
        -(carmonPhiDeriv t - carmonPhiDeriv t') by ring, abs_neg]
      simpa [Real.dist_eq] using h t t'
  | minus =>
      have hn := h (-t) (-t')
      change |-carmonPhiDeriv (-t) - -carmonPhiDeriv (-t')| ≤ |t - t'|
      rw [show -carmonPhiDeriv (-t) - -carmonPhiDeriv (-t') =
        -(carmonPhiDeriv (-t) - carmonPhiDeriv (-t')) by ring, abs_neg]
      simpa [Real.dist_eq, abs_sub_comm] using hn

/-! ## Branch-specific Carmon scales -/

/-- The positive branch uses `theta(s)` and the negative branch uses
`theta(-s)`.  At every `s`, at most one of these two scales is nonzero. -/
def terminalScale : TerminalBranch → ℝ → ℝ
  | .plus => carmonTheta
  | .minus => fun s ↦ carmonTheta (-s)

/-- Actual derivative of `terminalScale branch`. -/
def terminalScaleDeriv : TerminalBranch → ℝ → ℝ
  | .plus => carmonThetaDeriv
  | .minus => fun s ↦ -carmonThetaDeriv (-s)

theorem hasDerivAt_terminalScale (branch : TerminalBranch) (s : ℝ) :
    HasDerivAt (terminalScale branch) (terminalScaleDeriv branch s) s := by
  cases branch with
  | plus => exact hasDerivAt_carmonTheta s
  | minus =>
      have h := (hasDerivAt_carmonTheta (-s)).comp s (hasDerivAt_id s).neg
      convert h using 1
      all_goals try { apply AddCommGroup.ext <;> rfl }
      all_goals try { apply Module.ext <;> rfl }
      · funext x
        rfl
      · simp only [terminalScaleDeriv]
        ring

theorem terminalScale_nonneg (branch : TerminalBranch) (s : ℝ) :
    0 ≤ terminalScale branch s := by
  cases branch with
  | plus => exact carmonTheta_nonneg s
  | minus => exact carmonTheta_nonneg (-s)

theorem terminalScale_le_two (branch : TerminalBranch) (s : ℝ) :
    terminalScale branch s ≤ 2 := by
  cases branch with
  | plus =>
      have hrho := outerRho_le_two s
      have hn := carmonTheta_nonneg (-s)
      change carmonTheta s ≤ 2
      unfold outerRho at hrho
      linarith
  | minus =>
      have hrho := outerRho_le_two s
      have hp := carmonTheta_nonneg s
      change carmonTheta (-s) ≤ 2
      unfold outerRho at hrho
      linarith

theorem abs_terminalScaleDeriv_le_thirtyTwo
    (branch : TerminalBranch) (s : ℝ) :
    |terminalScaleDeriv branch s| ≤ 32 := by
  cases branch with
  | plus => exact abs_carmonThetaDeriv_le_thirtyTwo s
  | minus =>
      simpa [terminalScaleDeriv] using abs_carmonThetaDeriv_le_thirtyTwo (-s)

theorem terminalScale_lipschitz_bound
    (branch : TerminalBranch) (s s' : ℝ) :
    |terminalScale branch s - terminalScale branch s'| ≤
      32 * |s - s'| := by
  have hLip : LipschitzWith (32 : NNReal) (terminalScale branch) := by
    apply lipschitzWith_of_nnnorm_deriv_le
    · exact fun x ↦ (hasDerivAt_terminalScale branch x).differentiableAt
    · intro x
      rw [(hasDerivAt_terminalScale branch x).deriv, ← NNReal.coe_le_coe]
      simpa [Real.norm_eq_abs] using
        abs_terminalScaleDeriv_le_thirtyTwo branch x
  simpa [Real.dist_eq] using hLip.dist_le_mul s s'

theorem terminalScaleDeriv_lipschitz_bound
    (branch : TerminalBranch) (s s' : ℝ) :
    |terminalScaleDeriv branch s - terminalScaleDeriv branch s'| ≤
      576 * |s - s'| := by
  have hLip : LipschitzWith (576 : NNReal) carmonThetaDeriv := by
    apply lipschitzWith_of_nnnorm_deriv_le differentiable_carmonThetaDeriv
    intro x
    rw [(hasDerivAt_carmonThetaDeriv x).deriv, ← NNReal.coe_le_coe]
    simpa [Real.norm_eq_abs] using abs_carmonThetaSecond_le_fiveSeventySix x
  cases branch with
  | plus =>
      simpa [terminalScaleDeriv, Real.dist_eq] using hLip.dist_le_mul s s'
  | minus =>
      have h := hLip.dist_le_mul (-s) (-s')
      change |-carmonThetaDeriv (-s) - -carmonThetaDeriv (-s')| ≤
        576 * |s - s'|
      rw [show -carmonThetaDeriv (-s) - -carmonThetaDeriv (-s') =
        -(carmonThetaDeriv (-s) - carmonThetaDeriv (-s')) by ring, abs_neg]
      simpa [Real.dist_eq, abs_sub_comm] using h

/-! ## Explicit terminal gradient and componentwise bounds -/

/-- Gradient of the branch value
`theta_branch(s)^2 * alpha_branch(t) * q(u/theta_branch(s))`
in `(s,t,u)`. -/
def terminalPerspectiveGradient (branch : TerminalBranch)
    (s t u : ℝ) : ℝ × (ℝ × ℝ) :=
  (terminalScaleDeriv branch s * terminalAlpha branch t *
      qPerspectiveEtaLift (terminalScale branch s) u,
    terminalAlphaDeriv branch t *
      qPerspectiveValueLift (terminalScale branch s) u,
    terminalAlpha branch t * qPerspectiveULift (terminalScale branch s) u)

theorem terminalPerspectiveGradient_first_lipschitz
    (branch : TerminalBranch) (s t u s' t' u' : ℝ) :
    |(terminalPerspectiveGradient branch s t u).1 -
        (terminalPerspectiveGradient branch s' t' u').1| ≤
      706560 * |s - s'| + 1024 * |t - t'| + 9600 * |u - u'| := by
  let E := qPerspectiveEtaLift (terminalScale branch s) u
  let E' := qPerspectiveEtaLift (terminalScale branch s') u'
  let a := terminalAlpha branch t
  let a' := terminalAlpha branch t'
  let d := terminalScaleDeriv branch s
  let d' := terminalScaleDeriv branch s'
  have htheta0 := terminalScale_lipschitz_bound branch s s'
  have htheta : |terminalScale branch s - terminalScale branch s'| ≤
      64 * |s - s'| := by
    nlinarith [abs_nonneg (s - s')]
  have hd0 := terminalScaleDeriv_lipschitz_bound branch s s'
  have hd : |d - d'| ≤ 1152 * |s - s'| := by
    dsimp [d, d']
    nlinarith [abs_nonneg (s - s')]
  have ha := terminalAlpha_lipschitz branch t t'
  have hEbase := qPerspectiveEtaLift_lipschitz
    (eta := terminalScale branch s) (theta := terminalScale branch s')
    (u := u) (v := u') (terminalScale_nonneg branch s)
      (terminalScale_nonneg branch s')
  have hE : |E - E'| ≤ 960 * |s - s'| + 15 * |u - u'| := by
    dsimp [E, E']
    nlinarith [abs_nonneg (terminalScale branch s - terminalScale branch s'),
      abs_nonneg (u - u')]
  have hEabs : |E| ≤ 8 :=
    abs_qPerspectiveEtaLift_le_eight (terminalScale_nonneg branch s)
      (terminalScale_le_two branch s)
  have ha'abs : |a'| ≤ 10 := abs_terminalAlpha_le_ten branch t'
  have hd'abs : |d'| ≤ 64 := by
    have h := abs_terminalScaleDeriv_le_thirtyTwo branch s'
    dsimp [d']
    linarith
  have htri :
      |d * a * E - d' * a' * E'| ≤
        |d - d'| * |a| * |E| +
          |d'| * |a - a'| * |E| +
          |d'| * |a'| * |E - E'| := by
    calc
      |d * a * E - d' * a' * E'| =
          |(d - d') * a * E + d' * (a - a') * E +
            d' * a' * (E - E')| := by ring_nf
      _ ≤ |(d - d') * a * E + d' * (a - a') * E| +
          |d' * a' * (E - E')| := abs_add_le _ _
      _ ≤ (|(d - d') * a * E| + |d' * (a - a') * E|) +
          |d' * a' * (E - E')| := by gcongr; exact abs_add_le _ _
      _ = _ := by simp only [abs_mul]
  have haabs : |a| ≤ 10 := abs_terminalAlpha_le_ten branch t
  have hterm1 : |d - d'| * |a| * |E| ≤ 92160 * |s - s'| := by
    calc
      |d - d'| * |a| * |E| ≤
          (1152 * |s - s'|) * 10 * 8 := by gcongr
      _ = 92160 * |s - s'| := by ring
  have hterm2 : |d'| * |a - a'| * |E| ≤ 1024 * |t - t'| := by
    calc
      |d'| * |a - a'| * |E| ≤ 64 * (2 * |t - t'|) * 8 := by gcongr
      _ = 1024 * |t - t'| := by ring
  have hterm3 : |d'| * |a'| * |E - E'| ≤
      614400 * |s - s'| + 9600 * |u - u'| := by
    calc
      |d'| * |a'| * |E - E'| ≤
          64 * 10 * (960 * |s - s'| + 15 * |u - u'|) := by gcongr
      _ = 614400 * |s - s'| + 9600 * |u - u'| := by ring
  dsimp [terminalPerspectiveGradient, E, E', a, a', d, d']
  dsimp [E, E', a, a', d, d'] at htri hterm1 hterm2 hterm3
  linarith

theorem terminalPerspectiveGradient_second_lipschitz
    (branch : TerminalBranch) (s t u s' t' u' : ℝ) :
    |(terminalPerspectiveGradient branch s t u).2.1 -
        (terminalPerspectiveGradient branch s' t' u').2.1| ≤
      896 * |s - s'| + 4 * |t - t'| + 6 * |u - u'| := by
  let V := qPerspectiveValueLift (terminalScale branch s) u
  let V' := qPerspectiveValueLift (terminalScale branch s') u'
  let aD := terminalAlphaDeriv branch t
  let aD' := terminalAlphaDeriv branch t'
  have htheta0 := terminalScale_lipschitz_bound branch s s'
  have htheta : |terminalScale branch s - terminalScale branch s'| ≤
      64 * |s - s'| := by
    nlinarith [abs_nonneg (s - s')]
  have hVbase := qPerspectiveValueLift_lipschitz
    (eta := terminalScale branch s) (theta := terminalScale branch s')
    (u := u) (v := u') (terminalScale_nonneg branch s)
      (terminalScale_le_two branch s) (terminalScale_nonneg branch s')
      (terminalScale_le_two branch s')
  have hV : |V - V'| ≤ 448 * |s - s'| + 3 * |u - u'| := by
    dsimp [V, V']
    nlinarith [abs_nonneg (terminalScale branch s - terminalScale branch s'),
      abs_nonneg (u - u')]
  have hVabs : |V| ≤ 4 :=
    abs_qPerspectiveValueLift_le_four (terminalScale_nonneg branch s)
      (terminalScale_le_two branch s)
  have haD := terminalAlphaDeriv_lipschitz branch t t'
  have haD'abs := abs_terminalAlphaDeriv_le_two branch t'
  have htri : |aD * V - aD' * V'| ≤
      |aD - aD'| * |V| + |aD'| * |V - V'| :=
    abs_mul_sub_mul_le aD V aD' V'
  have hterm1 : |aD - aD'| * |V| ≤ 4 * |t - t'| := by
    calc
      |aD - aD'| * |V| ≤ |t - t'| * 4 := by gcongr
      _ = 4 * |t - t'| := by ring
  have hterm2 : |aD'| * |V - V'| ≤
      896 * |s - s'| + 6 * |u - u'| := by
    calc
      |aD'| * |V - V'| ≤
          2 * (448 * |s - s'| + 3 * |u - u'|) := by gcongr
      _ = 896 * |s - s'| + 6 * |u - u'| := by ring
  dsimp [terminalPerspectiveGradient, V, V', aD, aD']
  dsimp [V, V', aD, aD'] at htri hterm1 hterm2
  linarith

theorem terminalPerspectiveGradient_third_lipschitz
    (branch : TerminalBranch) (s t u s' t' u' : ℝ) :
    |(terminalPerspectiveGradient branch s t u).2.2 -
        (terminalPerspectiveGradient branch s' t' u').2.2| ≤
      5120 * |s - s'| + 8 * |t - t'| + 80 * |u - u'| := by
  let U := qPerspectiveULift (terminalScale branch s) u
  let U' := qPerspectiveULift (terminalScale branch s') u'
  let a := terminalAlpha branch t
  let a' := terminalAlpha branch t'
  have htheta0 := terminalScale_lipschitz_bound branch s s'
  have htheta : |terminalScale branch s - terminalScale branch s'| ≤
      64 * |s - s'| := by
    nlinarith [abs_nonneg (s - s')]
  have hUbase := qPerspectiveULift_lipschitz
    (eta := terminalScale branch s) (theta := terminalScale branch s')
    (u := u) (v := u') (terminalScale_nonneg branch s)
      (terminalScale_nonneg branch s')
  have hU : |U - U'| ≤ 512 * |s - s'| + 8 * |u - u'| := by
    dsimp [U, U']
    nlinarith [abs_nonneg (terminalScale branch s - terminalScale branch s'),
      abs_nonneg (u - u')]
  have hUabs : |U| ≤ 4 :=
    abs_qPerspectiveULift_le_four (terminalScale_nonneg branch s)
      (terminalScale_le_two branch s)
  have ha := terminalAlpha_lipschitz branch t t'
  have ha'abs := abs_terminalAlpha_le_ten branch t'
  have htri : |a * U - a' * U'| ≤
      |a - a'| * |U| + |a'| * |U - U'| :=
    abs_mul_sub_mul_le a U a' U'
  have hterm1 : |a - a'| * |U| ≤ 8 * |t - t'| := by
    calc
      |a - a'| * |U| ≤ (2 * |t - t'|) * 4 := by gcongr
      _ = 8 * |t - t'| := by ring
  have hterm2 : |a'| * |U - U'| ≤
      5120 * |s - s'| + 80 * |u - u'| := by
    calc
      |a'| * |U - U'| ≤
          10 * (512 * |s - s'| + 8 * |u - u'|) := by gcongr
      _ = 5120 * |s - s'| + 80 * |u - u'| := by ring
  dsimp [terminalPerspectiveGradient, U, U', a, a']
  dsimp [U, U', a, a'] at htri hterm1 hterm2
  linarith

/-! ## One Euclidean certificate for both signs -/

def terminalGradientSq (g : ℝ × (ℝ × ℝ)) : ℝ :=
  g.1 ^ 2 + g.2.1 ^ 2 + g.2.2 ^ 2

def terminalInputSq (s t u : ℝ) : ℝ := s ^ 2 + t ^ 2 + u ^ 2

def terminalPerspectiveSmoothnessConstant : ℝ := 3000000

theorem terminalPerspectiveSmoothnessConstant_pos :
    0 < terminalPerspectiveSmoothnessConstant := by
  norm_num [terminalPerspectiveSmoothnessConstant]

theorem terminalPerspectiveGradient_lipschitz_sq
    (branch : TerminalBranch) (s t u s' t' u' : ℝ) :
    terminalGradientSq
        (terminalPerspectiveGradient branch s t u -
          terminalPerspectiveGradient branch s' t' u') ≤
      terminalPerspectiveSmoothnessConstant ^ 2 *
        terminalInputSq (s - s') (t - t') (u - u') := by
  have h1 := terminalPerspectiveGradient_first_lipschitz
    branch s t u s' t' u'
  have h2 := terminalPerspectiveGradient_second_lipschitz
    branch s t u s' t' u'
  have h3 := terminalPerspectiveGradient_third_lipschitz
    branch s t u s' t' u'
  let a := (terminalPerspectiveGradient branch s t u).1 -
    (terminalPerspectiveGradient branch s' t' u').1
  let b := (terminalPerspectiveGradient branch s t u).2.1 -
    (terminalPerspectiveGradient branch s' t' u').2.1
  let c := (terminalPerspectiveGradient branch s t u).2.2 -
    (terminalPerspectiveGradient branch s' t' u').2.2
  let S := |s - s'| + |t - t'| + |u - u'|
  have h1' : |a| ≤ 1000000 * S := by
    dsimp [a, S]
    nlinarith [abs_nonneg (s - s'), abs_nonneg (t - t'),
      abs_nonneg (u - u')]
  have h2' : |b| ≤ 1000000 * S := by
    dsimp [b, S]
    nlinarith [abs_nonneg (s - s'), abs_nonneg (t - t'),
      abs_nonneg (u - u')]
  have h3' : |c| ≤ 1000000 * S := by
    dsimp [c, S]
    nlinarith [abs_nonneg (s - s'), abs_nonneg (t - t'),
      abs_nonneg (u - u')]
  have hS : S ^ 2 ≤ 3 * terminalInputSq (s - s') (t - t') (u - u') := by
    have haux : (|s - s'| + |t - t'| + |u - u'|) ^ 2 ≤
        3 * (|s - s'| ^ 2 + |t - t'| ^ 2 + |u - u'| ^ 2) := by
      nlinarith [sq_nonneg (|s - s'| - |t - t'|),
      sq_nonneg (|s - s'| - |u - u'|),
      sq_nonneg (|t - t'| - |u - u'|)]
    simpa only [S, terminalInputSq, sq_abs] using haux
  have hSnonneg : 0 ≤ S := by dsimp [S]; positivity
  have hKSnonneg : 0 ≤ (1000000 : ℝ) * S := mul_nonneg (by norm_num) hSnonneg
  have ha2 : a ^ 2 ≤ 1000000 ^ 2 * S ^ 2 := by
    have hpow := (sq_le_sq₀ (abs_nonneg a) hKSnonneg).2 h1'
    simpa only [sq_abs, mul_pow] using hpow
  have hb2 : b ^ 2 ≤ 1000000 ^ 2 * S ^ 2 := by
    have hpow := (sq_le_sq₀ (abs_nonneg b) hKSnonneg).2 h2'
    simpa only [sq_abs, mul_pow] using hpow
  have hc2 : c ^ 2 ≤ 1000000 ^ 2 * S ^ 2 := by
    have hpow := (sq_le_sq₀ (abs_nonneg c) hKSnonneg).2 h3'
    simpa only [sq_abs, mul_pow] using hpow
  have hsum : a ^ 2 + b ^ 2 + c ^ 2 ≤
      3 * (1000000 ^ 2 * S ^ 2) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hS
    (show 0 ≤ 3 * 1000000 ^ 2 by positivity)
  dsimp [terminalGradientSq, terminalInputSq,
    terminalPerspectiveSmoothnessConstant]
  change a ^ 2 + b ^ 2 + c ^ 2 ≤
    3000000 ^ 2 * ((s - s') ^ 2 + (t - t') ^ 2 + (u - u') ^ 2)
  calc
    a ^ 2 + b ^ 2 + c ^ 2 ≤ 3 * (1000000 ^ 2 * S ^ 2) := hsum
    _ ≤ 3000000 ^ 2 * terminalInputSq
        (s - s') (t - t') (u - u') := by
      nlinarith

end

end NCPLRevised
