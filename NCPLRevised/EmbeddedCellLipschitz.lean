/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.EmbeddedCellJointDerivative
import NCPLRevised.PerspectiveGradientLipschitz
import NCPLRevised.TerminalPerspectiveSmoothness
import NCPLRevised.ResidualGradientSmoothness
import NCPLRevised.ResidualGradientDerivative

/-!
# Dimension-free joint smoothness of the embedded cell

This module supplies the quantitative half of Lemma 5.1.  The derivative
half (including the two flat splice interfaces) is proved in
`EmbeddedCellJointDerivative`.
-/

namespace NCPLRevised

noncomputable section

/-- Squared Euclidean size of an increment in the three local blocks. -/
def cellInputSq {N : ℕ} (s t : ℝ) (y : ChainPoint N) : ℝ :=
  s ^ 2 + t ^ 2 + euclideanNormSq y

/-- Squared Euclidean size of a local gradient vector. -/
def cellGradientSq {N : ℕ} (g : CellPoint N) : ℝ :=
  g.1 ^ 2 + g.2.1 ^ 2 + euclideanNormSq g.2.2

theorem cellInputSq_nonneg {N : ℕ} (s t : ℝ) (y : ChainPoint N) :
    0 ≤ cellInputSq s t y := by
  unfold cellInputSq euclideanNormSq
  positivity

theorem cellGradientSq_nonneg {N : ℕ} (g : CellPoint N) :
    0 ≤ cellGradientSq g := by
  unfold cellGradientSq euclideanNormSq
  positivity

/-! ## The dimension-free negative-part penalty -/

theorem abs_negPart_sub_negPart_le (a b : ℝ) :
    |negPart a - negPart b| ≤ |a - b| := by
  unfold negPart
  have h := abs_max_sub_max_le_abs (-a) (-b) 0
  calc
    |max (-a) 0 - max (-b) 0| ≤ |(-a) - (-b)| := h
    _ = |a - b| := by
      rw [show (-a) - (-b) = -(a - b) by ring, abs_neg]

theorem euclideanNormSq_negPart_sub_le {N : ℕ}
    (y y' : ChainPoint N) :
    euclideanNormSq (fun k ↦ negPart (y k) - negPart (y' k)) ≤
      euclideanNormSq (y - y') := by
  unfold euclideanNormSq
  apply Finset.sum_le_sum
  intro k _
  have h := abs_negPart_sub_negPart_le (y k) (y' k)
  change (negPart (y k) - negPart (y' k)) ^ 2 ≤
    (y k - y' k) ^ 2
  have hsq := (sq_le_sq₀
    (abs_nonneg (negPart (y k) - negPart (y' k)))
    (abs_nonneg (y k - y' k))).2 h
  simpa only [sq_abs] using hsq

/-! ## The elementary outer quadratic term -/

/-- Gradient of the offset `-5 * rho(s)^2`. -/
def embeddedOffsetGradient (s : ℝ) : ℝ :=
  -10 * outerRho s * outerRhoDeriv s

theorem embeddedOffsetGradient_lipschitz (s s' : ℝ) :
    |embeddedOffsetGradient s - embeddedOffsetGradient s'| ≤
      80000 * |s - s'| := by
  have hrho : |outerRho s - outerRho s'| ≤ 64 * |s - s'| := by
    simpa [Real.dist_eq] using outerRho_lipschitz_sixtyFour.dist_le_mul s s'
  have hdrho : |outerRhoDeriv s - outerRhoDeriv s'| ≤
      1152 * |s - s'| := by
    simpa [Real.dist_eq] using outerRhoDeriv_lipschitz.dist_le_mul s s'
  have hmul := abs_mul_sub_mul_le
    (outerRho s) (outerRhoDeriv s)
    (outerRho s') (outerRhoDeriv s')
  unfold embeddedOffsetGradient
  rw [show -10 * outerRho s * outerRhoDeriv s -
      -10 * outerRho s' * outerRhoDeriv s' =
        -10 * (outerRho s * outerRhoDeriv s -
          outerRho s' * outerRhoDeriv s') by ring, abs_mul]
  have hten : |(-10 : ℝ)| = 10 := by norm_num
  rw [hten]
  calc
    10 * |outerRho s * outerRhoDeriv s -
        outerRho s' * outerRhoDeriv s'| ≤
      10 * (|outerRho s - outerRho s'| * |outerRhoDeriv s| +
        |outerRho s'| * |outerRhoDeriv s - outerRhoDeriv s'|) := by
          exact mul_le_mul_of_nonneg_left hmul (by norm_num)
    _ ≤ 80000 * |s - s'| := by
      have hdrhoAbsS : |outerRhoDeriv s| ≤ 64 :=
        abs_outerRhoDeriv_le_sixtyFour s
      have hrhoAbs' : |outerRho s'| ≤ 2 := by
        rw [abs_of_nonneg (outerRho_nonneg s')]
        exact outerRho_le_two s'
      have hterm1 :
          |outerRho s - outerRho s'| * |outerRhoDeriv s| ≤
            4096 * |s - s'| := by
        calc
          |outerRho s - outerRho s'| * |outerRhoDeriv s| ≤
              (64 * |s - s'|) * 64 := by gcongr
          _ = 4096 * |s - s'| := by ring
      have hterm2 :
          |outerRho s'| * |outerRhoDeriv s - outerRhoDeriv s'| ≤
            2304 * |s - s'| := by
        calc
          |outerRho s'| * |outerRhoDeriv s - outerRhoDeriv s'| ≤
              2 * (1152 * |s - s'|) := by gcongr
          _ = 2304 * |s - s'| := by ring
      nlinarith [abs_nonneg (s - s')]

/-! ## The two terminal branches and the flat splice -/

theorem qPerspectiveValueLift_eq_qPerspective {eta u : ℝ}
    (heta : 0 ≤ eta) :
    qPerspectiveValueLift eta u = qPerspective (eta, u) := by
  by_cases hz : eta = 0
  · subst eta
    simp [qPerspectiveValueLift, qPerspective]
  · have hetaPos : 0 < eta := lt_of_le_of_ne heta (Ne.symm hz)
    unfold qPerspectiveValueLift qPerspective quadraticPerspective
    rw [if_neg hz, scaleClipLift_eq_mul, q_unitClip]
    ring

/-- The globally totalized value of one Carmon terminal branch. -/
def terminalPerspectiveValue (branch : TerminalBranch)
    (s t u : ℝ) : ℝ :=
  terminalAlpha branch t *
    qPerspective (terminalScale branch s, u)

theorem carmonTheta_pos_of_half_lt {s : ℝ} (hs : 1 / 2 < s) :
    0 < carmonTheta s := by
  unfold carmonTheta expNegHalfInvSqGlue
  have hlinear : 0 < 2 * s - 1 := by linarith
  have harg : 0 < Real.sqrt 2 * (2 * s - 1) :=
    mul_pos sqrt_two_pos hlinear
  exact mul_pos (Real.sqrt_pos.2 (Real.exp_pos 1))
    (expNegInvSqGlue_pos_of_pos harg)

/-- The two totalized branches are exactly the active terminal term from
the embedded cell.  The right-hand side is totalized at `rho = 0`; the
identity therefore includes both splice interfaces. -/
theorem terminalPerspectiveValue_sum_eq (s t u : ℝ) :
    terminalPerspectiveValue .plus s t u +
        terminalPerspectiveValue .minus s t u =
      if outerRho s = 0 then 0 else
        carmonLiftedH s t * q (u / outerRho s) := by
  by_cases hp : 1 / 2 < s
  · have hn0 : carmonTheta (-s) = 0 :=
      carmonTheta_of_le_half (by linarith)
    have htheta : carmonTheta s ≠ 0 :=
      (carmonTheta_pos_of_half_lt hp).ne'
    have hrho : outerRho s = carmonTheta s := by
      simp [outerRho, hn0]
    have hrho0 : outerRho s ≠ 0 := by simpa [hrho] using htheta
    rw [if_neg hrho0, carmonLiftedH_of_gt_half hp, hrho]
    simp [terminalPerspectiveValue, terminalScale, qPerspective,
      quadraticPerspective, htheta, hn0, terminalAlpha, carmonAlphaPlus]
    ring
  · by_cases hn : s < -(1 / 2)
    · have hp0 : carmonTheta s = 0 :=
        carmonTheta_of_le_half (by linarith)
      have htheta : carmonTheta (-s) ≠ 0 :=
        (carmonTheta_pos_of_half_lt (by linarith : 1 / 2 < -s)).ne'
      have hrho : outerRho s = carmonTheta (-s) := by
        simp [outerRho, hp0]
      have hrho0 : outerRho s ≠ 0 := by simpa [hrho] using htheta
      rw [if_neg hrho0, carmonLiftedH_of_lt_neg_half hn, hrho]
      simp [terminalPerspectiveValue, terminalScale, qPerspective,
        quadraticPerspective, htheta, hp0, terminalAlpha, carmonAlphaMinus]
      ring
    · have hp0 : carmonTheta s = 0 :=
        carmonTheta_of_le_half (by linarith)
      have hn0 : carmonTheta (-s) = 0 :=
        carmonTheta_of_le_half (by linarith)
      have hrho : outerRho s = 0 := by simp [outerRho, hp0, hn0]
      rw [if_pos hrho]
      simp [terminalPerspectiveValue, terminalScale, qPerspective,
        quadraticPerspective, hp0, hn0]

/-- The first displayed branch component is the actual predecessor
derivative of the totalized terminal value, including zero branch scale. -/
theorem hasDerivAt_terminalPerspectiveValue_s
    (branch : TerminalBranch) (s t u : ℝ) :
    HasDerivAt (fun x : ℝ ↦ terminalPerspectiveValue branch x t u)
      (terminalPerspectiveGradient branch s t u).1 s := by
  have hpath : HasDerivAt
      (fun x : ℝ ↦ ((terminalScale branch x, u) : ℝ × ℝ))
      (terminalScaleDeriv branch s, 0) s :=
    (hasDerivAt_terminalScale branch s).prodMk
      (hasDerivAt_const (x := s) (c := u))
  have hq := hasFDerivAt_qPerspective (terminalScale branch s, u)
  unfold HasPairFDerivAt at hq
  have hcomp := hq.comp_hasDerivAt s hpath
  have hscaled := hcomp.const_mul (terminalAlpha branch t)
  have hgrad := qPerspectiveEtaLift_eq_gradient
    (eta := terminalScale branch s) (u := u)
    (terminalScale_nonneg branch s)
  simpa [terminalPerspectiveValue, terminalPerspectiveGradient,
    pairGradientCLM_apply, hgrad, mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- The second displayed branch component is the actual successor
derivative of the totalized terminal value. -/
theorem hasDerivAt_terminalPerspectiveValue_t
    (branch : TerminalBranch) (s t u : ℝ) :
    HasDerivAt (fun x : ℝ ↦ terminalPerspectiveValue branch s x u)
      (terminalPerspectiveGradient branch s t u).2.1 t := by
  have h := (hasDerivAt_terminalAlpha branch t).mul_const
    (qPerspective (terminalScale branch s, u))
  have hvalue := qPerspectiveValueLift_eq_qPerspective
    (eta := terminalScale branch s) (u := u)
    (terminalScale_nonneg branch s)
  simpa [terminalPerspectiveValue, terminalPerspectiveGradient, hvalue] using h

/-- The third displayed branch component is the actual terminal-dual
derivative of the totalized terminal value. -/
theorem hasDerivAt_terminalPerspectiveValue_u
    (branch : TerminalBranch) (s t u : ℝ) :
    HasDerivAt (fun x : ℝ ↦ terminalPerspectiveValue branch s t x)
      (terminalPerspectiveGradient branch s t u).2.2 u := by
  have hpath : HasDerivAt
      (fun x : ℝ ↦ ((terminalScale branch s, x) : ℝ × ℝ))
      (0, 1) u :=
    (hasDerivAt_const (x := u) (c := terminalScale branch s)).prodMk
      (hasDerivAt_id u)
  have hq := hasFDerivAt_qPerspective (terminalScale branch s, u)
  unfold HasPairFDerivAt at hq
  have hcomp := hq.comp_hasDerivAt u hpath
  have hscaled := hcomp.const_mul (terminalAlpha branch t)
  have hgrad := qPerspectiveULift_eq_gradient
    (eta := terminalScale branch s) (u := u)
    (terminalScale_nonneg branch s)
  simpa [terminalPerspectiveValue, terminalPerspectiveGradient,
    pairGradientCLM_apply, hgrad, mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- Sum of the positive and negative terminal gradients.  Flatness of
`theta` makes this a single globally defined field at both interfaces. -/
def terminalPerspectiveGradientSum (s t u : ℝ) : ℝ × (ℝ × ℝ) :=
  terminalPerspectiveGradient .plus s t u +
    terminalPerspectiveGradient .minus s t u

theorem terminalPerspectiveGradientSum_first_lipschitz
    (s t u s' t' u' : ℝ) :
    |(terminalPerspectiveGradientSum s t u).1 -
        (terminalPerspectiveGradientSum s' t' u').1| ≤
      1413120 * |s - s'| + 2048 * |t - t'| + 19200 * |u - u'| := by
  have hp := terminalPerspectiveGradient_first_lipschitz
    .plus s t u s' t' u'
  have hm := terminalPerspectiveGradient_first_lipschitz
    .minus s t u s' t' u'
  have htri := abs_add_le
    ((terminalPerspectiveGradient .plus s t u).1 -
      (terminalPerspectiveGradient .plus s' t' u').1)
    ((terminalPerspectiveGradient .minus s t u).1 -
      (terminalPerspectiveGradient .minus s' t' u').1)
  unfold terminalPerspectiveGradientSum
  dsimp
  rw [show
      (terminalPerspectiveGradient .plus s t u).1 +
          (terminalPerspectiveGradient .minus s t u).1 -
        ((terminalPerspectiveGradient .plus s' t' u').1 +
          (terminalPerspectiveGradient .minus s' t' u').1) =
      ((terminalPerspectiveGradient .plus s t u).1 -
          (terminalPerspectiveGradient .plus s' t' u').1) +
        ((terminalPerspectiveGradient .minus s t u).1 -
          (terminalPerspectiveGradient .minus s' t' u').1) by ring]
  linarith

theorem terminalPerspectiveGradientSum_second_lipschitz
    (s t u s' t' u' : ℝ) :
    |(terminalPerspectiveGradientSum s t u).2.1 -
        (terminalPerspectiveGradientSum s' t' u').2.1| ≤
      1792 * |s - s'| + 8 * |t - t'| + 12 * |u - u'| := by
  have hp := terminalPerspectiveGradient_second_lipschitz
    .plus s t u s' t' u'
  have hm := terminalPerspectiveGradient_second_lipschitz
    .minus s t u s' t' u'
  have htri := abs_add_le
    ((terminalPerspectiveGradient .plus s t u).2.1 -
      (terminalPerspectiveGradient .plus s' t' u').2.1)
    ((terminalPerspectiveGradient .minus s t u).2.1 -
      (terminalPerspectiveGradient .minus s' t' u').2.1)
  unfold terminalPerspectiveGradientSum
  dsimp
  rw [show
      (terminalPerspectiveGradient .plus s t u).2.1 +
          (terminalPerspectiveGradient .minus s t u).2.1 -
        ((terminalPerspectiveGradient .plus s' t' u').2.1 +
          (terminalPerspectiveGradient .minus s' t' u').2.1) =
      ((terminalPerspectiveGradient .plus s t u).2.1 -
          (terminalPerspectiveGradient .plus s' t' u').2.1) +
        ((terminalPerspectiveGradient .minus s t u).2.1 -
          (terminalPerspectiveGradient .minus s' t' u').2.1) by ring]
  linarith

theorem terminalPerspectiveGradientSum_third_lipschitz
    (s t u s' t' u' : ℝ) :
    |(terminalPerspectiveGradientSum s t u).2.2 -
        (terminalPerspectiveGradientSum s' t' u').2.2| ≤
      10240 * |s - s'| + 16 * |t - t'| + 160 * |u - u'| := by
  have hp := terminalPerspectiveGradient_third_lipschitz
    .plus s t u s' t' u'
  have hm := terminalPerspectiveGradient_third_lipschitz
    .minus s t u s' t' u'
  have htri := abs_add_le
    ((terminalPerspectiveGradient .plus s t u).2.2 -
      (terminalPerspectiveGradient .plus s' t' u').2.2)
    ((terminalPerspectiveGradient .minus s t u).2.2 -
      (terminalPerspectiveGradient .minus s' t' u').2.2)
  unfold terminalPerspectiveGradientSum
  dsimp
  rw [show
      (terminalPerspectiveGradient .plus s t u).2.2 +
          (terminalPerspectiveGradient .minus s t u).2.2 -
        ((terminalPerspectiveGradient .plus s' t' u').2.2 +
          (terminalPerspectiveGradient .minus s' t' u').2.2) =
      ((terminalPerspectiveGradient .plus s t u).2.2 -
          (terminalPerspectiveGradient .plus s' t' u').2.2) +
        ((terminalPerspectiveGradient .minus s t u).2.2 -
          (terminalPerspectiveGradient .minus s' t' u').2.2) by ring]
  linarith

/-- A deliberately coarse Euclidean constant for the sum of both terminal
branches. -/
def terminalGradientSumConstant : ℝ := 6000000

theorem terminalPerspectiveGradientSum_lipschitz_sq
    (s t u s' t' u' : ℝ) :
    terminalGradientSq
        (terminalPerspectiveGradientSum s t u -
          terminalPerspectiveGradientSum s' t' u') ≤
      terminalGradientSumConstant ^ 2 *
        terminalInputSq (s - s') (t - t') (u - u') := by
  have h1 := terminalPerspectiveGradientSum_first_lipschitz
    s t u s' t' u'
  have h2 := terminalPerspectiveGradientSum_second_lipschitz
    s t u s' t' u'
  have h3 := terminalPerspectiveGradientSum_third_lipschitz
    s t u s' t' u'
  let a := (terminalPerspectiveGradientSum s t u).1 -
    (terminalPerspectiveGradientSum s' t' u').1
  let b := (terminalPerspectiveGradientSum s t u).2.1 -
    (terminalPerspectiveGradientSum s' t' u').2.1
  let c := (terminalPerspectiveGradientSum s t u).2.2 -
    (terminalPerspectiveGradientSum s' t' u').2.2
  let S := |s - s'| + |t - t'| + |u - u'|
  have h1' : |a| ≤ 2000000 * S := by
    dsimp [a, S]
    nlinarith [abs_nonneg (s - s'), abs_nonneg (t - t'),
      abs_nonneg (u - u')]
  have h2' : |b| ≤ 2000000 * S := by
    dsimp [b, S]
    nlinarith [abs_nonneg (s - s'), abs_nonneg (t - t'),
      abs_nonneg (u - u')]
  have h3' : |c| ≤ 2000000 * S := by
    dsimp [c, S]
    nlinarith [abs_nonneg (s - s'), abs_nonneg (t - t'),
      abs_nonneg (u - u')]
  have hS : S ^ 2 ≤
      3 * terminalInputSq (s - s') (t - t') (u - u') := by
    have haux : (|s - s'| + |t - t'| + |u - u'|) ^ 2 ≤
        3 * (|s - s'| ^ 2 + |t - t'| ^ 2 + |u - u'| ^ 2) := by
      nlinarith [sq_nonneg (|s - s'| - |t - t'|),
        sq_nonneg (|s - s'| - |u - u'|),
        sq_nonneg (|t - t'| - |u - u'|)]
    simpa only [S, terminalInputSq, sq_abs] using haux
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hKS0 : 0 ≤ (2000000 : ℝ) * S := mul_nonneg (by norm_num) hS0
  have ha2 : a ^ 2 ≤ 2000000 ^ 2 * S ^ 2 := by
    have hpow := (sq_le_sq₀ (abs_nonneg a) hKS0).2 h1'
    simpa only [sq_abs, mul_pow] using hpow
  have hb2 : b ^ 2 ≤ 2000000 ^ 2 * S ^ 2 := by
    have hpow := (sq_le_sq₀ (abs_nonneg b) hKS0).2 h2'
    simpa only [sq_abs, mul_pow] using hpow
  have hc2 : c ^ 2 ≤ 2000000 ^ 2 * S ^ 2 := by
    have hpow := (sq_le_sq₀ (abs_nonneg c) hKS0).2 h3'
    simpa only [sq_abs, mul_pow] using hpow
  have hsum : a ^ 2 + b ^ 2 + c ^ 2 ≤
      3 * (2000000 ^ 2 * S ^ 2) := by linarith
  dsimp [terminalGradientSq, terminalInputSq, terminalGradientSumConstant]
  change a ^ 2 + b ^ 2 + c ^ 2 ≤
    6000000 ^ 2 * ((s - s') ^ 2 + (t - t') ^ 2 + (u - u') ^ 2)
  calc
    a ^ 2 + b ^ 2 + c ^ 2 ≤ 3 * (2000000 ^ 2 * S ^ 2) := hsum
    _ ≤ 6000000 ^ 2 * terminalInputSq
        (s - s') (t - t') (u - u') := by
      nlinarith

/-! ## Residual composition with the Carmon scale -/

theorem abs_pPerspectiveEtaLift_le_three_mul {eta u : ℝ}
    (heta : 0 ≤ eta) :
    |pPerspectiveEtaLift eta u| ≤ 3 * eta := by
  unfold pPerspectiveEtaLift
  rw [scaleClipLift_eq_mul, abs_mul, abs_of_nonneg heta]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left
    (abs_pPerspectiveEtaBase_clip_le_three (u / eta)) heta

theorem abs_qpPerspectiveEtaLift_le_five_mul {eta u v : ℝ}
    (heta : 0 ≤ eta) :
    |qpPerspectiveEtaLift eta u v| ≤ 5 * eta := by
  unfold qpPerspectiveEtaLift
  rw [scaleClipPairLift_eq_mul, abs_mul, abs_of_nonneg heta]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left
    (abs_qpPerspectiveEtaBase_clip_le_five (u / eta) (v / eta)) heta

theorem abs_residualGateEtaLift_le_seven {N : ℕ} (hN : 2 ≤ N)
    {eta : ℝ} (heta : 0 ≤ eta) (y : ChainPoint N) (k : Fin N) :
    |residualGateEtaLift N eta y k| ≤
      7 * omega N k.1 * eta := by
  have hw : 0 ≤ omega N k.1 := (omega_pos (by omega : 0 < N)).le
  unfold residualGateEtaLift
  split_ifs with hk
  · have hp := abs_pPerspectiveEtaLift_le_three_mul
      (u := y k / weightSqrt N k) heta
    rw [abs_mul, abs_of_nonneg hw]
    have hsub := abs_sub (2 * eta)
      (pPerspectiveEtaLift eta (y k / weightSqrt N k))
    have htwo : |2 * eta| = 2 * eta := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) heta)]
    rw [htwo] at hsub
    have hinner :
        |2 * eta - pPerspectiveEtaLift eta
          (y k / weightSqrt N k)| ≤ 7 * eta := by
      linarith
    calc
      omega N k.1 *
          |2 * eta - pPerspectiveEtaLift eta
            (y k / weightSqrt N k)| ≤
        omega N k.1 * (7 * eta) := by gcongr
      _ = 7 * omega N k.1 * eta := by ring
  · have hqp := abs_qpPerspectiveEtaLift_le_five_mul
      (u := y ⟨k.1 - 1, by omega⟩ /
        weightSqrt N ⟨k.1 - 1, by omega⟩)
      (v := y k / weightSqrt N k) heta
    rw [abs_mul, abs_of_nonneg hw]
    have hsub := abs_sub (2 * eta)
      (qpPerspectiveEtaLift eta
        (y ⟨k.1 - 1, by omega⟩ /
          weightSqrt N ⟨k.1 - 1, by omega⟩)
        (y k / weightSqrt N k))
    have htwo : |2 * eta| = 2 * eta := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) heta)]
    rw [htwo] at hsub
    have hinner :
        |2 * eta - qpPerspectiveEtaLift eta
          (y ⟨k.1 - 1, by omega⟩ /
            weightSqrt N ⟨k.1 - 1, by omega⟩)
          (y k / weightSqrt N k)| ≤ 7 * eta := by
      linarith
    calc
      omega N k.1 *
          |2 * eta - qpPerspectiveEtaLift eta
            (y ⟨k.1 - 1, by omega⟩ /
              weightSqrt N ⟨k.1 - 1, by omega⟩)
            (y k / weightSqrt N k)| ≤
        omega N k.1 * (7 * eta) := by gcongr
      _ = 7 * omega N k.1 * eta := by ring

/-- Uniform absolute bound needed when differentiating the composed scale.
It is independent of both the dual point and the chain length. -/
theorem abs_embeddedResidualEtaLift_le_fifty {N : ℕ} (hN : 2 ≤ N)
    {eta : ℝ} (heta : 0 ≤ eta) (hetaTwo : eta ≤ 2)
    (y : ChainPoint N) :
    |embeddedResidualEtaLift N eta y| ≤ 50 := by
  have habs := Finset.abs_sum_le_sum_abs
    (s := Finset.univ) (f := fun k : Fin N ↦ residualGateEtaLift N eta y k)
  have hterm :
      (∑ k : Fin N, |residualGateEtaLift N eta y k|) ≤
        ∑ k : Fin N, 7 * omega N k.1 * eta := by
    apply Finset.sum_le_sum
    intro k _
    exact abs_residualGateEtaLift_le_seven hN heta y k
  have hsumOmega : (∑ k : Fin N, omega N k.1) < 3 := by
    have h := sum_omega_lt_three hN
    rw [← Fin.sum_univ_eq_sum_range (fun j ↦ omega N j) N] at h
    exact h
  have hsumNonneg : 0 ≤ (∑ k : Fin N, omega N k.1) := by
    apply Finset.sum_nonneg
    intro k _
    exact (omega_pos (by omega : 0 < N)).le
  unfold embeddedResidualEtaLift
  calc
    |∑ k : Fin N, residualGateEtaLift N eta y k| ≤
        ∑ k : Fin N, |residualGateEtaLift N eta y k| := habs
    _ ≤ ∑ k : Fin N, 7 * omega N k.1 * eta := hterm
    _ = 7 * eta * ∑ k : Fin N, omega N k.1 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ 50 := by
      have hprod : eta * (∑ k : Fin N, omega N k.1) ≤ 6 := by
        nlinarith
      nlinarith

/-- Residual gradient after composing its nonnegative scale with `rho(s)`. -/
def embeddedComposedResidualGradient (N : ℕ)
    (s : ℝ) (y : ChainPoint N) : ℝ × ChainPoint N :=
  (outerRhoDeriv s * embeddedResidualEtaLift N (outerRho s) y,
    embeddedResidualYLift N (outerRho s) y)

/-- Coarse dimension-free Euclidean Lipschitz constant for the residual
gradient after scale composition. -/
def embeddedComposedResidualConstant : ℝ := 100000000

theorem embeddedComposedResidualGradient_lipschitz_sq {N : ℕ}
    (hN : 2 ≤ N) (s s' : ℝ) (y y' : ChainPoint N) :
    ((embeddedComposedResidualGradient N s y).1 -
        (embeddedComposedResidualGradient N s' y').1) ^ 2 +
      euclideanNormSq
        ((embeddedComposedResidualGradient N s y).2 -
          (embeddedComposedResidualGradient N s' y').2) ≤
      embeddedComposedResidualConstant ^ 2 *
        ((s - s') ^ 2 + euclideanNormSq (y - y')) := by
  let eta := outerRho s
  let theta := outerRho s'
  let E := embeddedResidualEtaLift N eta y
  let E' := embeddedResidualEtaLift N theta y'
  let Y := embeddedResidualYLift N eta y
  let Y' := embeddedResidualYLift N theta y'
  let d := outerRhoDeriv s
  let d' := outerRhoDeriv s'
  have hrhoAbs : |eta - theta| ≤ 64 * |s - s'| := by
    dsimp [eta, theta]
    simpa [Real.dist_eq] using outerRho_lipschitz_sixtyFour.dist_le_mul s s'
  have hrhoSq : (eta - theta) ^ 2 ≤ 64 ^ 2 * (s - s') ^ 2 := by
    have hsq := (sq_le_sq₀ (abs_nonneg (eta - theta))
      (mul_nonneg (by norm_num) (abs_nonneg (s - s')))).2 hrhoAbs
    simpa only [sq_abs, mul_pow] using hsq
  have hres0 := embeddedResidualGradient_lipschitz_sq hN
    (outerRho_nonneg s) (outerRho_nonneg s') y y'
  have hres : (E - E') ^ 2 + euclideanNormSq (Y - Y') ≤
      (225 : ℝ) ^ 2 *
        (64 ^ 2 * (s - s') ^ 2 + euclideanNormSq (y - y')) := by
    dsimp [E, E', Y, Y', eta, theta]
    calc
      (embeddedResidualEtaLift N (outerRho s) y -
          embeddedResidualEtaLift N (outerRho s') y') ^ 2 +
          euclideanNormSq
            (embeddedResidualYLift N (outerRho s) y -
              embeddedResidualYLift N (outerRho s') y') ≤
        (225 : ℝ) ^ 2 *
          ((outerRho s - outerRho s') ^ 2 +
            euclideanNormSq (y - y')) := hres0
      _ ≤ (225 : ℝ) ^ 2 *
          (64 ^ 2 * (s - s') ^ 2 + euclideanNormSq (y - y')) := by
        gcongr
  have hdAbs : |d| ≤ 64 := by
    dsimp [d]
    exact abs_outerRhoDeriv_le_sixtyFour s
  have hdSq : d ^ 2 ≤ 64 ^ 2 := by
    have hsq := (sq_le_sq₀ (abs_nonneg d) (by norm_num : 0 ≤ (64 : ℝ))).2 hdAbs
    simpa only [sq_abs] using hsq
  have hddAbs : |d - d'| ≤ 1152 * |s - s'| := by
    dsimp [d, d']
    simpa [Real.dist_eq] using outerRhoDeriv_lipschitz.dist_le_mul s s'
  have hddSq : (d - d') ^ 2 ≤ 1152 ^ 2 * (s - s') ^ 2 := by
    have hsq := (sq_le_sq₀ (abs_nonneg (d - d'))
      (mul_nonneg (by norm_num) (abs_nonneg (s - s')))).2 hddAbs
    simpa only [sq_abs, mul_pow] using hsq
  have hE'Abs : |E'| ≤ 50 := by
    dsimp [E', theta]
    exact abs_embeddedResidualEtaLift_le_fifty hN
      (outerRho_nonneg s') (outerRho_le_two s') y'
  have hE'Sq : E' ^ 2 ≤ 50 ^ 2 := by
    have hsq := (sq_le_sq₀ (abs_nonneg E') (by norm_num : 0 ≤ (50 : ℝ))).2 hE'Abs
    simpa only [sq_abs] using hsq
  have hfirst : d ^ 2 * (E - E') ^ 2 ≤
      64 ^ 2 * (E - E') ^ 2 :=
    mul_le_mul_of_nonneg_right hdSq (sq_nonneg _)
  have hsecond : (d - d') ^ 2 * E' ^ 2 ≤
      (1152 ^ 2 * (s - s') ^ 2) * 50 ^ 2 := by
    calc
      (d - d') ^ 2 * E' ^ 2 ≤
          (1152 ^ 2 * (s - s') ^ 2) * E' ^ 2 :=
        mul_le_mul_of_nonneg_right hddSq (sq_nonneg _)
      _ ≤ (1152 ^ 2 * (s - s') ^ 2) * 50 ^ 2 := by
        exact mul_le_mul_of_nonneg_left hE'Sq
          (mul_nonneg (by positivity) (sq_nonneg _))
  have hprod : (d * E - d' * E') ^ 2 ≤
      2 * 64 ^ 2 * (E - E') ^ 2 +
        2 * (1152 ^ 2 * (s - s') ^ 2) * 50 ^ 2 := by
    calc
      (d * E - d' * E') ^ 2 =
          (d * (E - E') + (d - d') * E') ^ 2 := by ring
      _ ≤ 2 * (d * (E - E')) ^ 2 +
          2 * ((d - d') * E') ^ 2 := residual_sq_add_le_two _ _
      _ ≤ 2 * 64 ^ 2 * (E - E') ^ 2 +
          2 * (1152 ^ 2 * (s - s') ^ 2) * 50 ^ 2 := by
        rw [mul_pow, mul_pow]
        nlinarith
  have hY0 : 0 ≤ euclideanNormSq (Y - Y') := euclideanNormSq_nonneg _
  have hcombine :
      (d * E - d' * E') ^ 2 + euclideanNormSq (Y - Y') ≤
        (2 * 64 ^ 2) *
          ((E - E') ^ 2 + euclideanNormSq (Y - Y')) +
        2 * (1152 ^ 2 * (s - s') ^ 2) * 50 ^ 2 := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hres
    (by norm_num : 0 ≤ (2 * (64 : ℝ) ^ 2))
  have hinput0 :
      0 ≤ (s - s') ^ 2 + euclideanNormSq (y - y') :=
    add_nonneg (sq_nonneg _) (euclideanNormSq_nonneg _)
  unfold embeddedComposedResidualGradient embeddedComposedResidualConstant
  dsimp [eta, theta, E, E', Y, Y', d, d'] at *
  calc
    (outerRhoDeriv s * embeddedResidualEtaLift N (outerRho s) y -
          outerRhoDeriv s' * embeddedResidualEtaLift N (outerRho s') y') ^ 2 +
        euclideanNormSq
          (embeddedResidualYLift N (outerRho s) y -
            embeddedResidualYLift N (outerRho s') y') ≤
      (2 * 64 ^ 2) *
          ((embeddedResidualEtaLift N (outerRho s) y -
            embeddedResidualEtaLift N (outerRho s') y') ^ 2 +
            euclideanNormSq
              (embeddedResidualYLift N (outerRho s) y -
                embeddedResidualYLift N (outerRho s') y')) +
        2 * (1152 ^ 2 * (s - s') ^ 2) * 50 ^ 2 := hcombine
    _ ≤ (2 * 64 ^ 2) *
          ((225 : ℝ) ^ 2 *
            (64 ^ 2 * (s - s') ^ 2 + euclideanNormSq (y - y'))) +
        2 * (1152 ^ 2 * (s - s') ^ 2) * 50 ^ 2 := by
      gcongr
    _ ≤ (100000000 : ℝ) ^ 2 *
        ((s - s') ^ 2 + euclideanNormSq (y - y')) := by
      have hy0 := euclideanNormSq_nonneg (y - y')
      nlinarith

/-! ## Lifting the terminal scalar coordinate into the dual block -/

def embeddedTerminalCoord {N : ℕ} (y : ChainPoint N) : ℝ :=
  chainCoord y (N - 1)

def terminalDualLift (N : ℕ) (a : ℝ) : ChainPoint N := fun k ↦
  if k.1 = N - 1 then a else 0

theorem euclideanNormSq_terminalDualLift {N : ℕ} (hN : 0 < N)
    (a : ℝ) :
    euclideanNormSq (terminalDualLift N a) = a ^ 2 := by
  classical
  let last : Fin N := ⟨N - 1, by omega⟩
  unfold euclideanNormSq terminalDualLift
  calc
    (∑ k : Fin N, (if k.1 = N - 1 then a else 0) ^ 2) =
        ∑ k : Fin N, if k = last then a ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = last
      · subst k
        simp [last]
      · have hkval : k.1 ≠ N - 1 := by
          intro hval
          apply hk
          apply Fin.ext
          simpa [last] using hval
        simp [hk, hkval]
    _ = a ^ 2 := by simp [last]

theorem terminalDualLift_sub (N : ℕ) (a b : ℝ) :
    terminalDualLift N a - terminalDualLift N b =
      terminalDualLift N (a - b) := by
  funext k
  simp only [Pi.sub_apply, terminalDualLift]
  split_ifs <;> ring

theorem embeddedTerminalCoord_sub_sq_le {N : ℕ} (hN : 0 < N)
    (y y' : ChainPoint N) :
    (embeddedTerminalCoord y - embeddedTerminalCoord y') ^ 2 ≤
      euclideanNormSq (y - y') := by
  let last : Fin N := ⟨N - 1, by omega⟩
  have hlast : N - 1 < N := by omega
  have hcoord : embeddedTerminalCoord y - embeddedTerminalCoord y' =
      (y - y') last := by
    simp [embeddedTerminalCoord, chainCoord, hlast, last]
  rw [hcoord]
  unfold euclideanNormSq
  exact Finset.single_le_sum (fun k _ ↦ sq_nonneg ((y - y') k))
    (Finset.mem_univ last)

/-- The two-branch terminal gradient placed in the full local cell space. -/
def embeddedTerminalCellGradient (N : ℕ)
    (s t : ℝ) (y : ChainPoint N) : CellPoint N :=
  let g := terminalPerspectiveGradientSum s t (embeddedTerminalCoord y)
  (g.1, (g.2.1, terminalDualLift N g.2.2))

theorem embeddedTerminalCellGradient_lipschitz_sq {N : ℕ}
    (hN : 2 ≤ N) (s t : ℝ) (y : ChainPoint N)
    (s' t' : ℝ) (y' : ChainPoint N) :
    cellGradientSq
        (embeddedTerminalCellGradient N s t y -
          embeddedTerminalCellGradient N s' t' y') ≤
      terminalGradientSumConstant ^ 2 *
        cellInputSq (s - s') (t - t') (y - y') := by
  have hterm := terminalPerspectiveGradientSum_lipschitz_sq
    s t (embeddedTerminalCoord y) s' t' (embeddedTerminalCoord y')
  have hu := embeddedTerminalCoord_sub_sq_le (by omega : 0 < N) y y'
  have hconst0 : 0 ≤ terminalGradientSumConstant ^ 2 := sq_nonneg _
  have hinput := add_le_add_left hu ((s - s') ^ 2 + (t - t') ^ 2)
  have hscaled := mul_le_mul_of_nonneg_left hinput hconst0
  let g := terminalPerspectiveGradientSum s t (embeddedTerminalCoord y)
  let g' := terminalPerspectiveGradientSum s' t' (embeddedTerminalCoord y')
  change (g.1 - g'.1) ^ 2 + (g.2.1 - g'.2.1) ^ 2 +
      euclideanNormSq (terminalDualLift N g.2.2 - terminalDualLift N g'.2.2) ≤
    terminalGradientSumConstant ^ 2 *
      ((s - s') ^ 2 + (t - t') ^ 2 + euclideanNormSq (y - y'))
  rw [terminalDualLift_sub,
    euclideanNormSq_terminalDualLift (by omega : 0 < N)]
  dsimp [terminalGradientSq, terminalInputSq] at hterm
  dsimp [g, g']
  exact hterm.trans (by
    simpa [add_assoc, add_comm, add_left_comm] using hscaled)

/-! ## The stable full gradient field -/

theorem sq_add_four_le_four (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤
      4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

theorem cellGradientSq_add_four_le
    {N : ℕ} (a b c d : CellPoint N) :
    cellGradientSq (a + b + c + d) ≤
      4 * (cellGradientSq a + cellGradientSq b +
        cellGradientSq c + cellGradientSq d) := by
  have hs := sq_add_four_le_four a.1 b.1 c.1 d.1
  have ht := sq_add_four_le_four a.2.1 b.2.1 c.2.1 d.2.1
  have hy :
      (∑ k : Fin N, (a.2.2 k + b.2.2 k + c.2.2 k + d.2.2 k) ^ 2) ≤
        ∑ k : Fin N,
          4 * (a.2.2 k ^ 2 + b.2.2 k ^ 2 + c.2.2 k ^ 2 + d.2.2 k ^ 2) := by
    apply Finset.sum_le_sum
    intro k _
    exact sq_add_four_le_four _ _ _ _
  unfold cellGradientSq euclideanNormSq at *
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply] at hs ht hy ⊢
  have hy' :
      (∑ k : Fin N, (a.2.2 k + b.2.2 k + c.2.2 k + d.2.2 k) ^ 2) ≤
        4 * ((∑ k : Fin N, a.2.2 k ^ 2) +
          (∑ k : Fin N, b.2.2 k ^ 2) +
          (∑ k : Fin N, c.2.2 k ^ 2) +
          (∑ k : Fin N, d.2.2 k ^ 2)) := by
    calc
      (∑ k : Fin N,
          (a.2.2 k + b.2.2 k + c.2.2 k + d.2.2 k) ^ 2) ≤
          ∑ k : Fin N,
            4 * (a.2.2 k ^ 2 + b.2.2 k ^ 2 +
              c.2.2 k ^ 2 + d.2.2 k ^ 2) := hy
      _ = 4 * ∑ k : Fin N,
          (a.2.2 k ^ 2 + b.2.2 k ^ 2 + c.2.2 k ^ 2 + d.2.2 k ^ 2) := by
        rw [Finset.mul_sum]
      _ = 4 * ((∑ k : Fin N, a.2.2 k ^ 2) +
          (∑ k : Fin N, b.2.2 k ^ 2) +
          (∑ k : Fin N, c.2.2 k ^ 2) +
          (∑ k : Fin N, d.2.2 k ^ 2)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib]
  linarith

def embeddedOffsetCellGradient (N : ℕ) (s : ℝ) : CellPoint N :=
  (embeddedOffsetGradient s, (0, 0))

def embeddedResidualCellGradient (N : ℕ)
    (s : ℝ) (y : ChainPoint N) : CellPoint N :=
  ((embeddedComposedResidualGradient N s y).1,
    (0, (embeddedComposedResidualGradient N s y).2))

def embeddedPenaltyCellGradient (N : ℕ) (y : ChainPoint N) : CellPoint N :=
  (0, (0, fun k ↦ negPart (y k)))

/-- The explicit, nonsingular gradient formula obtained from the two
terminal perspectives, the residual perspective, the outer offset, and the
negative-part penalty. -/
def embeddedStableCellGradient (N : ℕ)
    (s t : ℝ) (y : ChainPoint N) : CellPoint N :=
  embeddedOffsetCellGradient N s +
    embeddedTerminalCellGradient N s t y -
    embeddedResidualCellGradient N s y +
    embeddedPenaltyCellGradient N y

/-- Nonsingular value formula whose four gradient summands are displayed in
`embeddedStableCellGradient`. -/
def embeddedStableCell (N : ℕ)
    (s t : ℝ) (y : ChainPoint N) : ℝ :=
  -5 * outerRho s ^ 2 +
    (terminalPerspectiveValue .plus s t (embeddedTerminalCoord y) +
      terminalPerspectiveValue .minus s t (embeddedTerminalCoord y)) -
    embeddedResidualAtScale N (outerRho s) y -
    (1 / 2 : ℝ) * negPartNormSq y

/-- The stable perspective value is exactly the manuscript's embedded cell,
including the whole zero-scale strip. -/
theorem embeddedStableCell_eq_embeddedCell {N : ℕ} (hN : 2 ≤ N)
    (s t : ℝ) (y : ChainPoint N) :
    embeddedStableCell N s t y = embeddedCell N s t y := by
  have hNpos : 0 < N := by omega
  by_cases hrho : outerRho s = 0
  · unfold embeddedStableCell
    rw [terminalPerspectiveValue_sum_eq, if_pos hrho]
    simp [embeddedResidualAtScale, hrho, embeddedCell,
      scaledPerspectiveBlock, zeroPerspectiveBlock, negPartNormSq,
      pPerspective, quadraticPerspective, quadraticPerspectiveVec]
  · have hrhopos : 0 < outerRho s :=
      lt_of_le_of_ne (outerRho_nonneg s) (Ne.symm hrho)
    rw [embeddedCell_expanded_of_rho_pos hNpos hrhopos]
    unfold embeddedStableCell
    rw [terminalPerspectiveValue_sum_eq, if_neg hrho,
      embeddedResidualAtScale_eq_raw_of_ne hrho]
    unfold embeddedTerminal embeddedTerminalCoord embeddedResidual
      embeddedResidualRawAtScale embeddedNormalized
    rw [perspectiveNormalize_terminal hNpos]

/-- The predecessor component of the stable field is an actual derivative
of the stable value. -/
theorem hasDerivAt_embeddedStableCell_s {N : ℕ}
    (s t : ℝ) (y : ChainPoint N) :
    HasResidualDerivAt (fun x : ℝ ↦ embeddedStableCell N x t y)
      (embeddedStableCellGradient N s t y).1 s := by
  have hoff0 := ((hasDerivAt_outerRho s).pow 2).const_mul (-5)
  have hoff : HasDerivAt (fun x : ℝ ↦ -5 * outerRho x ^ 2)
      (embeddedOffsetGradient s) s := by
    have hderiv : -5 * ((2 : ℝ) * outerRho s ^ (2 - 1) *
        outerRhoDeriv s) = embeddedOffsetGradient s := by
      simp [embeddedOffsetGradient]
      ring
    simpa only [Pi.pow_apply] using hoff0.congr_deriv hderiv
  have hplus := hasDerivAt_terminalPerspectiveValue_s .plus s t
    (embeddedTerminalCoord y)
  have hminus := hasDerivAt_terminalPerspectiveValue_s .minus s t
    (embeddedTerminalCoord y)
  have hterm := hplus.add hminus
  have hres0 := hasDerivAt_embeddedResidualAtScale N (outerRho s) y
  unfold HasResidualDerivAt at hres0
  have hres := hres0.comp s (hasDerivAt_outerRho s)
  have hpen := hasDerivAt_const (x := s)
    (c := (1 / 2 : ℝ) * negPartNormSq y)
  have h := (hoff.add hterm).sub hres |>.sub hpen
  have hstable : HasResidualDerivAt
      (fun x : ℝ ↦ embeddedStableCell N x t y)
      (embeddedOffsetGradient s +
        (terminalPerspectiveGradientSum s t (embeddedTerminalCoord y)).1 -
        outerRhoDeriv s * embeddedResidualEtaLift N (outerRho s) y) s := by
    unfold HasResidualDerivAt
    have hderiv :
        embeddedOffsetGradient s +
            ((terminalPerspectiveGradient .plus s t (embeddedTerminalCoord y)).1 +
              (terminalPerspectiveGradient .minus s t (embeddedTerminalCoord y)).1) -
          embeddedResidualEtaLift N (outerRho s) y * outerRhoDeriv s - 0 =
        embeddedOffsetGradient s +
            (terminalPerspectiveGradientSum s t (embeddedTerminalCoord y)).1 -
          outerRhoDeriv s * embeddedResidualEtaLift N (outerRho s) y := by
      simp only [terminalPerspectiveGradientSum, Prod.fst_add]
      ring
    have hh := h.congr_deriv hderiv
    convert hh using 1
    funext x
    rfl
  convert hstable using 1
  simp [embeddedStableCellGradient, embeddedOffsetCellGradient,
    embeddedTerminalCellGradient, embeddedResidualCellGradient,
    embeddedPenaltyCellGradient, embeddedComposedResidualGradient]

/-- The successor component of the stable field is an actual derivative of
the stable value. -/
theorem hasDerivAt_embeddedStableCell_t {N : ℕ}
    (s t : ℝ) (y : ChainPoint N) :
    HasResidualDerivAt (fun x : ℝ ↦ embeddedStableCell N s x y)
      (embeddedStableCellGradient N s t y).2.1 t := by
  have hplus := hasDerivAt_terminalPerspectiveValue_t .plus s t
    (embeddedTerminalCoord y)
  have hminus := hasDerivAt_terminalPerspectiveValue_t .minus s t
    (embeddedTerminalCoord y)
  have hterm := hplus.add hminus
  have h := hterm.const_add (-5 * outerRho s ^ 2) |>.sub_const
    (embeddedResidualAtScale N (outerRho s) y) |>.sub_const
    ((1 / 2 : ℝ) * negPartNormSq y)
  have hstable : HasResidualDerivAt
      (fun x : ℝ ↦ embeddedStableCell N s x y)
      (terminalPerspectiveGradientSum s t (embeddedTerminalCoord y)).2.1 t := by
    unfold HasResidualDerivAt
    convert h using 1
    · funext x
      rfl
    · simp only [terminalPerspectiveGradientSum,
        Prod.snd_add, Prod.fst_add]
  convert hstable using 1
  simp [embeddedStableCellGradient, embeddedOffsetCellGradient,
    embeddedTerminalCellGradient, embeddedResidualCellGradient,
    embeddedPenaltyCellGradient]

theorem embeddedStableCellGradient_first_eq_actual {N : ℕ}
    (hN : 2 ≤ N) (s t : ℝ) (y : ChainPoint N) :
    (embeddedStableCellGradient N s t y).1 =
      (embeddedCellGradient N (s, (t, y))).1 := by
  have hs := hasDerivAt_embeddedStableCell_s (N := N) s t y
  have hfun : (fun x : ℝ ↦ embeddedStableCell N x t y) =
      (fun x : ℝ ↦ embeddedCell N x t y) := by
    funext x
    exact embeddedStableCell_eq_embeddedCell hN x t y
  rw [hfun] at hs
  exact hs.unique (hasDerivAt_embeddedCell_predecessor hN s t y)

theorem embeddedStableCellGradient_second_eq_actual {N : ℕ}
    (hN : 2 ≤ N) (s t : ℝ) (y : ChainPoint N) :
    (embeddedStableCellGradient N s t y).2.1 =
      (embeddedCellGradient N (s, (t, y))).2.1 := by
  have ht := hasDerivAt_embeddedStableCell_t (N := N) s t y
  have hfun : (fun x : ℝ ↦ embeddedStableCell N s x y) =
      (fun x : ℝ ↦ embeddedCell N s x y) := by
    funext x
    exact embeddedStableCell_eq_embeddedCell hN s x y
  rw [hfun] at ht
  have hactual := hasDerivAt_embeddedCell_successor (by omega : 0 < N) s t y
  exact ht.unique hactual

/-! ## Full dual derivative of the terminal and penalty pieces -/

def embeddedTerminalCoordCLM (N : ℕ) (hN : 0 < N) :
    ChainPoint N →L[ℝ] ℝ :=
  ContinuousLinearMap.proj ⟨N - 1, by omega⟩

@[simp] theorem embeddedTerminalCoordCLM_apply {N : ℕ} (hN : 0 < N)
    (y : ChainPoint N) :
    embeddedTerminalCoordCLM N hN y = embeddedTerminalCoord y := by
  simp [embeddedTerminalCoordCLM, embeddedTerminalCoord, chainCoord, hN]

theorem finiteDotProductCLM_terminalDualLift_apply {N : ℕ}
    (hN : 0 < N) (a : ℝ) (v : ChainPoint N) :
    finiteDotProductCLM (terminalDualLift N a) v =
      a * embeddedTerminalCoord v := by
  classical
  let last : Fin N := ⟨N - 1, by omega⟩
  rw [finiteDotProductCLM_apply]
  calc
    (∑ k : Fin N, terminalDualLift N a k * v k) =
        ∑ k : Fin N, if k = last then a * v last else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = last
      · subst k
        simp [terminalDualLift, last]
      · have hkval : k.1 ≠ N - 1 := by
          intro hval
          apply hk
          apply Fin.ext
          simpa [last] using hval
        simp [terminalDualLift, hk, hkval]
    _ = a * v last := by simp [last]
    _ = a * embeddedTerminalCoord v := by
      simp [embeddedTerminalCoord, chainCoord, hN, last]

theorem hasFDerivAt_terminalPerspectiveValue_y {N : ℕ}
    (hN : 0 < N) (branch : TerminalBranch)
    (s t : ℝ) (y : ChainPoint N) :
    HasChainFDerivAt N
      (fun z : ChainPoint N ↦
        terminalPerspectiveValue branch s t (embeddedTerminalCoord z))
      (finiteDotProductCLM
        (terminalDualLift N
          (terminalPerspectiveGradient branch s t
            (embeddedTerminalCoord y)).2.2)) y := by
  have hu := hasDerivAt_terminalPerspectiveValue_u branch s t
    (embeddedTerminalCoord y)
  have hcoord0 : HasFDerivAt (embeddedTerminalCoordCLM N hN)
      (embeddedTerminalCoordCLM N hN) y :=
    (embeddedTerminalCoordCLM N hN).hasFDerivAt
  have hcoord : HasFDerivAt embeddedTerminalCoord
      (embeddedTerminalCoordCLM N hN) y := by
    convert hcoord0 using 1
    funext z
    exact (embeddedTerminalCoordCLM_apply hN z).symm
  have hcomp := hu.hasFDerivAt.comp y hcoord
  unfold HasChainFDerivAt
  apply hcomp.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  rw [finiteDotProductCLM_terminalDualLift_apply hN]
  simp [embeddedTerminalCoordCLM_apply]
  ring

theorem hasFDerivAt_terminalPerspectiveValue_sum_y {N : ℕ}
    (hN : 0 < N) (s t : ℝ) (y : ChainPoint N) :
    HasChainFDerivAt N
      (fun z : ChainPoint N ↦
        terminalPerspectiveValue .plus s t (embeddedTerminalCoord z) +
          terminalPerspectiveValue .minus s t (embeddedTerminalCoord z))
      (finiteDotProductCLM
        (terminalDualLift N
          (terminalPerspectiveGradientSum s t
            (embeddedTerminalCoord y)).2.2)) y := by
  have hp := hasFDerivAt_terminalPerspectiveValue_y hN .plus s t y
  have hm := hasFDerivAt_terminalPerspectiveValue_y hN .minus s t y
  unfold HasChainFDerivAt at hp hm ⊢
  have h := hp.add hm
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply, finiteDotProductCLM_terminalDualLift_apply hN,
    terminalPerspectiveGradientSum, Prod.snd_add]
  ring

theorem hasFDerivAt_embeddedPenaltyValue {N : ℕ} (hN : 2 ≤ N)
    (y : ChainPoint N) :
    HasChainFDerivAt N
      (fun z : ChainPoint N ↦ -(1 / 2 : ℝ) * negPartNormSq z)
      (finiteDotProductCLM (fun k ↦ negPart (y k))) y := by
  have h := hasFDerivAt_scaledPerspectiveBlock hN 0 0 y
  unfold HasChainFDerivAt
  have hfun : scaledPerspectiveBlock N 0 0 =
      (fun z : ChainPoint N ↦ -(1 / 2 : ℝ) * negPartNormSq z) := by
    funext z
    simp [scaledPerspectiveBlock, zeroPerspectiveBlock, negPartNormSq]
  rw [hfun] at h
  simpa [scaledPerspectiveGradient] using h

/-- The stable dual field is the genuine full dual Fréchet gradient. -/
theorem hasFDerivAt_embeddedStableCell_y {N : ℕ} (hN : 2 ≤ N)
    (s t : ℝ) (y : ChainPoint N) :
    HasChainFDerivAt N (embeddedStableCell N s t)
      (finiteDotProductCLM
        (embeddedStableCellGradient N s t y).2.2) y := by
  have hterm := hasFDerivAt_terminalPerspectiveValue_sum_y
    (by omega : 0 < N) s t y
  have hres := hasFDerivAt_embeddedResidualAtScale_y
    N (outerRho s) y
  have hpen := hasFDerivAt_embeddedPenaltyValue hN y
  unfold HasChainFDerivAt at hterm hres hpen ⊢
  have h := (hterm.const_add (-5 * outerRho s ^ 2)).sub hres |>.add hpen
  convert h using 1
  · funext z
    simp only [embeddedStableCell, Pi.sub_apply, Pi.add_apply]
    ring
  · apply ContinuousLinearMap.ext
    intro v
    simp only [sub_apply, add_apply, finiteDotProductCLM_apply]
    unfold embeddedStableCellGradient embeddedOffsetCellGradient
      embeddedTerminalCellGradient embeddedResidualCellGradient
      embeddedPenaltyCellGradient
    simp only [Prod.snd_add, Prod.snd_sub, Pi.add_apply, Pi.sub_apply]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp [embeddedComposedResidualGradient]
    ring

theorem finiteDotProductCLM_injective {N : ℕ} :
    Function.Injective (finiteDotProductCLM :
      ChainPoint N → (ChainPoint N →L[ℝ] ℝ)) := by
  intro a b hab
  funext k
  classical
  have h := congrArg
    (fun L : ChainPoint N →L[ℝ] ℝ ↦
      L (Pi.single k (1 : ℝ) : ChainPoint N)) hab
  simpa only [finiteDotProductCLM_apply, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

/-- All three blocks of the stable formula agree with the already-certified
actual joint gradient of `embeddedCell`. -/
theorem embeddedStableCellGradient_eq_actual {N : ℕ}
    (hN : 2 ≤ N) (s t : ℝ) (y : ChainPoint N) :
    embeddedStableCellGradient N s t y =
      embeddedCellGradient N (s, (t, y)) := by
  apply Prod.ext
  · exact embeddedStableCellGradient_first_eq_actual hN s t y
  · apply Prod.ext
    · exact embeddedStableCellGradient_second_eq_actual hN s t y
    · have hstable := hasFDerivAt_embeddedStableCell_y hN s t y
      have hfun : embeddedStableCell N s t = embeddedCell N s t := by
        funext z
        exact embeddedStableCell_eq_embeddedCell hN s t z
      unfold HasChainFDerivAt at hstable
      rw [hfun] at hstable
      have hactual := hasFDerivAt_embeddedCell_dual_jointModule hN s t y
      unfold HasChainFDerivAt at hactual
      exact finiteDotProductCLM_injective (hstable.unique hactual)

theorem embeddedOffsetCellGradient_lipschitz_sq {N : ℕ}
    (s t : ℝ) (y : ChainPoint N) (s' t' : ℝ) (y' : ChainPoint N) :
    cellGradientSq
        (embeddedOffsetCellGradient N s - embeddedOffsetCellGradient N s') ≤
      (80000 : ℝ) ^ 2 * cellInputSq (s - s') (t - t') (y - y') := by
  have habs := embeddedOffsetGradient_lipschitz s s'
  have hsq : (embeddedOffsetGradient s - embeddedOffsetGradient s') ^ 2 ≤
      (80000 : ℝ) ^ 2 * (s - s') ^ 2 := by
    have hp := (sq_le_sq₀ (abs_nonneg (embeddedOffsetGradient s -
      embeddedOffsetGradient s'))
      (mul_nonneg (by norm_num) (abs_nonneg (s - s')))).2 habs
    simpa only [sq_abs, mul_pow] using hp
  have hrest : 0 ≤ (t - t') ^ 2 + euclideanNormSq (y - y') :=
    add_nonneg (sq_nonneg _) (euclideanNormSq_nonneg _)
  calc
    cellGradientSq
        (embeddedOffsetCellGradient N s - embeddedOffsetCellGradient N s') =
      (embeddedOffsetGradient s - embeddedOffsetGradient s') ^ 2 := by
        simp [embeddedOffsetCellGradient, cellGradientSq, euclideanNormSq]
    _ ≤ (80000 : ℝ) ^ 2 * (s - s') ^ 2 := hsq
    _ ≤ (80000 : ℝ) ^ 2 *
        cellInputSq (s - s') (t - t') (y - y') := by
      unfold cellInputSq
      nlinarith

theorem embeddedResidualCellGradient_lipschitz_sq {N : ℕ}
    (hN : 2 ≤ N) (s t : ℝ) (y : ChainPoint N)
    (s' t' : ℝ) (y' : ChainPoint N) :
    cellGradientSq
        (embeddedResidualCellGradient N s y -
          embeddedResidualCellGradient N s' y') ≤
      embeddedComposedResidualConstant ^ 2 *
        cellInputSq (s - s') (t - t') (y - y') := by
  have h := embeddedComposedResidualGradient_lipschitz_sq hN s s' y y'
  have ht0 : 0 ≤ (t - t') ^ 2 := sq_nonneg _
  have hc0 : 0 ≤ embeddedComposedResidualConstant ^ 2 := sq_nonneg _
  calc
    cellGradientSq
        (embeddedResidualCellGradient N s y -
          embeddedResidualCellGradient N s' y') =
      ((embeddedComposedResidualGradient N s y).1 -
          (embeddedComposedResidualGradient N s' y').1) ^ 2 +
        euclideanNormSq
          ((embeddedComposedResidualGradient N s y).2 -
            (embeddedComposedResidualGradient N s' y').2) := by
      simp [embeddedResidualCellGradient, cellGradientSq]
    _ ≤ embeddedComposedResidualConstant ^ 2 *
        ((s - s') ^ 2 + euclideanNormSq (y - y')) := h
    _ ≤ embeddedComposedResidualConstant ^ 2 *
        cellInputSq (s - s') (t - t') (y - y') := by
      have hm := mul_le_mul_of_nonneg_left
        (show (s - s') ^ 2 + euclideanNormSq (y - y') ≤
            (s - s') ^ 2 + (t - t') ^ 2 + euclideanNormSq (y - y') by
          linarith) hc0
      simpa [cellInputSq, add_assoc] using hm

theorem embeddedPenaltyCellGradient_lipschitz_sq {N : ℕ}
    (s t : ℝ) (y : ChainPoint N) (s' t' : ℝ) (y' : ChainPoint N) :
    cellGradientSq
        (embeddedPenaltyCellGradient N y - embeddedPenaltyCellGradient N y') ≤
      cellInputSq (s - s') (t - t') (y - y') := by
  have hneg := euclideanNormSq_negPart_sub_le y y'
  have hst : 0 ≤ (s - s') ^ 2 + (t - t') ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  calc
    cellGradientSq
        (embeddedPenaltyCellGradient N y - embeddedPenaltyCellGradient N y') =
      euclideanNormSq (fun k ↦ negPart (y k) - negPart (y' k)) := by
        simp only [embeddedPenaltyCellGradient, cellGradientSq,
          Prod.fst_sub, Prod.snd_sub, sub_zero]
        norm_num
        congr 1
    _ ≤ euclideanNormSq (y - y') := hneg
    _ ≤ cellInputSq (s - s') (t - t') (y - y') := by
      unfold cellInputSq
      linarith

/-- The fixed numerical constant used for Lemma 5.1. -/
def embeddedCellSmoothnessConstant : ℝ := 1000000000

theorem embeddedCellSmoothnessConstant_ge_one :
    1 ≤ embeddedCellSmoothnessConstant := by
  norm_num [embeddedCellSmoothnessConstant]

/-- Dimension-free Lipschitz estimate for the stable explicit field. -/
theorem embeddedStableCellGradient_lipschitz_sq {N : ℕ}
    (hN : 2 ≤ N) (s t : ℝ) (y : ChainPoint N)
    (s' t' : ℝ) (y' : ChainPoint N) :
    cellGradientSq
        (embeddedStableCellGradient N s t y -
          embeddedStableCellGradient N s' t' y') ≤
      embeddedCellSmoothnessConstant ^ 2 *
        cellInputSq (s - s') (t - t') (y - y') := by
  let A := embeddedOffsetCellGradient N s - embeddedOffsetCellGradient N s'
  let B := embeddedTerminalCellGradient N s t y -
    embeddedTerminalCellGradient N s' t' y'
  let C := -(embeddedResidualCellGradient N s y -
    embeddedResidualCellGradient N s' y')
  let D := embeddedPenaltyCellGradient N y - embeddedPenaltyCellGradient N y'
  have hdecomp : embeddedStableCellGradient N s t y -
      embeddedStableCellGradient N s' t' y' = A + B + C + D := by
    dsimp [embeddedStableCellGradient, A, B, C, D]
    abel
  rw [hdecomp]
  have hfour := cellGradientSq_add_four_le A B C D
  have hA := embeddedOffsetCellGradient_lipschitz_sq
    (N := N) s t y s' t' y'
  have hB := embeddedTerminalCellGradient_lipschitz_sq hN s t y s' t' y'
  have hR := embeddedResidualCellGradient_lipschitz_sq hN s t y s' t' y'
  have hC : cellGradientSq C ≤
      embeddedComposedResidualConstant ^ 2 *
        cellInputSq (s - s') (t - t') (y - y') := by
    dsimp [C]
    have hneg : cellGradientSq
        (-(embeddedResidualCellGradient N s y -
          embeddedResidualCellGradient N s' y')) =
        cellGradientSq
          (embeddedResidualCellGradient N s y -
            embeddedResidualCellGradient N s' y') := by
      unfold cellGradientSq euclideanNormSq
      simp only [Prod.fst_neg, Prod.snd_neg, neg_sq, Pi.neg_apply]
    rw [hneg]
    exact hR
  have hD := embeddedPenaltyCellGradient_lipschitz_sq
    (N := N) s t y s' t' y'
  have hinput0 := cellInputSq_nonneg (s - s') (t - t') (y - y')
  have hsum : cellGradientSq A + cellGradientSq B +
      cellGradientSq C + cellGradientSq D ≤
    ((80000 : ℝ) ^ 2 + terminalGradientSumConstant ^ 2 +
      embeddedComposedResidualConstant ^ 2 + 1) *
        cellInputSq (s - s') (t - t') (y - y') := by
    linarith
  calc
    cellGradientSq (A + B + C + D) ≤
        4 * (cellGradientSq A + cellGradientSq B +
          cellGradientSq C + cellGradientSq D) := hfour
    _ ≤ 4 * (((80000 : ℝ) ^ 2 + terminalGradientSumConstant ^ 2 +
        embeddedComposedResidualConstant ^ 2 + 1) *
          cellInputSq (s - s') (t - t') (y - y')) := by gcongr
    _ ≤ embeddedCellSmoothnessConstant ^ 2 *
        cellInputSq (s - s') (t - t') (y - y') := by
      dsimp [terminalGradientSumConstant, embeddedComposedResidualConstant,
        embeddedCellSmoothnessConstant]
      nlinarith

/-- Lemma 5.1: the genuine joint Fréchet gradient of the embedded cell is
globally Lipschitz, with one numerical constant that is independent of `N`.
The squared formulation is exactly the Euclidean Lipschitz inequality. -/
theorem embeddedCellGradient_lipschitz_sq {N : ℕ}
    (hN : 2 ≤ N) (s t : ℝ) (y : ChainPoint N)
    (s' t' : ℝ) (y' : ChainPoint N) :
    cellGradientSq
        (embeddedCellGradient N (s, (t, y)) -
          embeddedCellGradient N (s', (t', y'))) ≤
      embeddedCellSmoothnessConstant ^ 2 *
        cellInputSq (s - s') (t - t') (y - y') := by
  rw [← embeddedStableCellGradient_eq_actual hN s t y,
    ← embeddedStableCellGradient_eq_actual hN s' t' y']
  exact embeddedStableCellGradient_lipschitz_sq hN s t y s' t' y'

/-- Alias emphasizing that the preceding estimate is the local-cell
smoothness assertion used by the assembled hard instance. -/
theorem embeddedCellGradient_local_lipschitz {N : ℕ}
    (hN : 2 ≤ N) (s t : ℝ) (y : ChainPoint N)
    (s' t' : ℝ) (y' : ChainPoint N) :
    cellGradientSq
        (embeddedCellGradient N (s, (t, y)) -
          embeddedCellGradient N (s', (t', y'))) ≤
      embeddedCellSmoothnessConstant ^ 2 *
        cellInputSq (s - s') (t - t') (y - y') :=
  embeddedCellGradient_lipschitz_sq hN s t y s' t' y'

end

end NCPLRevised
