/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import Mathlib

/-!
# Arithmetic certificate behind Theorem 3.1

This file checks the floor choices and scaling identities in the revised
manuscript (`main_revised.tex`, 2026-08-25).  It deliberately takes the analytic hard-instance
certificates (C1)--(C4) as theorem parameters; no missing analytic statement
is introduced as an axiom.
-/

namespace NCPLRevised

noncomputable section

/-- Paper's choice `N = floor ((mu0 / ell0) * kappa)`. -/
def paperN (ell0 mu0 kappa : ℝ) : ℕ :=
  ⌊mu0 / ell0 * kappa⌋₊

/-- Paper's coordinate scale `lambda`. -/
def paperLambda (ell ell0 g0 eps : ℝ) : ℝ :=
  2 * ell0 * eps / (ell * g0)

/-- Paper's choice `M = floor (ell0 Delta / (ell Delta0 lambda^2))`. -/
def paperM (ell ell0 Delta Delta0 g0 eps : ℝ) : ℕ :=
  ⌊ell0 * Delta /
    (ell * Delta0 * paperLambda ell ell0 g0 eps ^ 2)⌋₊

def paperC0 (ell0 mu0 : ℝ) : ℝ := 2 * ell0 / mu0
def paperC1 (ell0 Delta0 g0 : ℝ) : ℝ := g0 ^ 2 / (8 * ell0 * Delta0)
def paperC2 (ell0 mu0 Delta0 g0 : ℝ) : ℝ :=
  g0 ^ 2 * mu0 / (8 * ell0 ^ 2 * Delta0)

theorem paperLambda_pos {ell ell0 g0 eps : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (hg0 : 0 < g0)
    (heps : 0 < eps) :
    0 < paperLambda ell ell0 g0 eps := by
  unfold paperLambda
  positivity

theorem paperN_two_le {ell0 mu0 kappa : ℝ}
    (hell0 : 0 < ell0) (hmu0 : 0 < mu0)
    (hkappa : paperC0 ell0 mu0 ≤ kappa) :
    2 ≤ paperN ell0 mu0 kappa := by
  unfold paperN
  unfold paperC0 at hkappa
  apply Nat.le_floor
  calc
    (2 : ℝ) = mu0 / ell0 * (2 * ell0 / mu0) := by
      field_simp [ne_of_gt hell0, ne_of_gt hmu0]
    _ ≤ mu0 / ell0 * kappa := by
      exact mul_le_mul_of_nonneg_left hkappa (div_nonneg hmu0.le hell0.le)

theorem paperN_cast_le {ell0 mu0 kappa : ℝ}
    (hell0 : 0 < ell0) (hmu0 : 0 < mu0) (hkappa : 0 ≤ kappa) :
    (paperN ell0 mu0 kappa : ℝ) ≤ mu0 / ell0 * kappa := by
  unfold paperN
  apply Nat.floor_le
  positivity

theorem paperN_plus_one_lower {ell0 mu0 kappa : ℝ} :
    mu0 / ell0 * kappa ≤ (paperN ell0 mu0 kappa + 1 : ℕ) := by
  have h := Nat.lt_floor_add_one (mu0 / ell0 * kappa)
  exact le_of_lt (by simpa [paperN] using h)

theorem paperLambda_gradient_scale {ell ell0 g0 eps : ℝ}
    (hell : ell ≠ 0) (hell0 : ell0 ≠ 0) (hg0 : g0 ≠ 0) :
    ell * paperLambda ell ell0 g0 eps / ell0 * g0 = 2 * eps := by
  unfold paperLambda
  field_simp

theorem paperM_two_le {ell ell0 Delta Delta0 g0 eps : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (_hDelta : 0 < Delta)
    (hDelta0 : 0 < Delta0) (hg0 : 0 < g0) (heps : 0 < eps)
    (hregime : eps ^ 2 ≤ paperC1 ell0 Delta0 g0 * ell * Delta) :
    2 ≤ paperM ell ell0 Delta Delta0 g0 eps := by
  unfold paperM
  apply Nat.le_floor
  have hlambda := paperLambda_pos hell hell0 hg0 heps
  unfold paperC1 at hregime
  unfold paperLambda
  field_simp [ne_of_gt hell, ne_of_gt hell0, ne_of_gt hDelta0,
    ne_of_gt hg0, ne_of_gt heps] at hregime ⊢
  ring_nf at hregime ⊢
  nlinarith [sq_pos_of_pos heps]

theorem paperM_cast_le {ell ell0 Delta Delta0 g0 eps : ℝ}
    (hell : 0 ≤ ell) (hell0 : 0 ≤ ell0) (hDelta : 0 ≤ Delta)
    (hDelta0 : 0 ≤ Delta0) :
    (paperM ell ell0 Delta Delta0 g0 eps : ℝ) ≤
      ell0 * Delta /
        (ell * Delta0 * paperLambda ell ell0 g0 eps ^ 2) := by
  unfold paperM
  apply Nat.floor_le
  positivity

/-- Lower floor estimate used verbatim in the paper: if `2 ≤ a`, then
`a / 2 ≤ floor a`. -/
theorem half_le_natFloor {a : ℝ} (ha : 2 ≤ a) :
    a / 2 ≤ (⌊a⌋₊ : ℝ) := by
  have hfloor : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
  have hfloorNonneg : 0 ≤ (⌊a⌋₊ : ℝ) := by positivity
  linarith

theorem paperM_lower {ell ell0 Delta Delta0 g0 eps : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (hDelta : 0 < Delta)
    (hDelta0 : 0 < Delta0) (hg0 : 0 < g0) (heps : 0 < eps)
    (hregime : eps ^ 2 ≤ paperC1 ell0 Delta0 g0 * ell * Delta) :
    g0 ^ 2 * ell * Delta / (8 * ell0 * Delta0 * eps ^ 2) ≤
      (paperM ell ell0 Delta Delta0 g0 eps : ℝ) := by
  let a := ell0 * Delta /
    (ell * Delta0 * paperLambda ell ell0 g0 eps ^ 2)
  have ha2 : 2 ≤ a := by
    have hm := paperM_two_le hell hell0 hDelta hDelta0 hg0 heps hregime
    have hfloor : (2 : ℝ) ≤ (paperM ell ell0 Delta Delta0 g0 eps : ℝ) := by
      exact_mod_cast hm
    have hupper := paperM_cast_le (g0 := g0) (eps := eps)
      hell.le hell0.le hDelta.le hDelta0.le
    exact hfloor.trans hupper
  have hhalf := half_le_natFloor ha2
  have hfloorEq : ⌊a⌋₊ = paperM ell ell0 Delta Delta0 g0 eps := by
    rfl
  rw [hfloorEq] at hhalf
  calc
    g0 ^ 2 * ell * Delta / (8 * ell0 * Delta0 * eps ^ 2) = a / 2 := by
      unfold a paperLambda
      field_simp [ne_of_gt hell, ne_of_gt hell0, ne_of_gt hDelta0,
        ne_of_gt hg0, ne_of_gt heps]
      ring
    _ ≤ _ := hhalf

theorem scaled_dualPL_at_least_target {ell ell0 mu0 kappa : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (hmu0 : 0 < mu0)
    (hkappa : 0 < kappa) (hkappaLarge : paperC0 ell0 mu0 ≤ kappa) :
    ell / kappa ≤
      ell * mu0 / (ell0 * (paperN ell0 mu0 kappa : ℝ)) := by
  have hNtwo := paperN_two_le hell0 hmu0 hkappaLarge
  have hNpos : 0 < paperN ell0 mu0 kappa := by omega
  have hNupper := paperN_cast_le hell0 hmu0 hkappa.le
  rw [div_le_div_iff₀ hkappa
    (mul_pos hell0 (by exact_mod_cast hNpos))]
  have hmul := mul_le_mul_of_nonneg_left hNupper hell0.le
  field_simp [ne_of_gt hell0] at hmul ⊢
  nlinarith

theorem scaled_gap_le_target {ell ell0 Delta Delta0 g0 eps : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (hDelta : 0 ≤ Delta)
    (hDelta0 : 0 < Delta0) (hg0 : 0 < g0) (heps : 0 < eps) :
    ell * paperLambda ell ell0 g0 eps ^ 2 / ell0 * Delta0 *
        (paperM ell ell0 Delta Delta0 g0 eps : ℝ) ≤ Delta := by
  have hM := paperM_cast_le (g0 := g0) (eps := eps)
    hell.le hell0.le hDelta hDelta0.le
  have hlambda := paperLambda_pos hell hell0 hg0 heps
  have hcoeff : 0 ≤ ell * paperLambda ell ell0 g0 eps ^ 2 / ell0 * Delta0 := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hM hcoeff
  calc
    ell * paperLambda ell ell0 g0 eps ^ 2 / ell0 * Delta0 *
        (paperM ell ell0 Delta Delta0 g0 eps : ℝ)
        ≤ (ell * paperLambda ell ell0 g0 eps ^ 2 / ell0 * Delta0) *
          (ell0 * Delta /
            (ell * Delta0 * paperLambda ell ell0 g0 eps ^ 2)) := hmul
    _ = Delta := by
      field_simp [ne_of_gt hell, ne_of_gt hell0, ne_of_gt hDelta0,
        ne_of_gt hlambda]

theorem paper_chain_length_lower {ell ell0 mu0 Delta Delta0 g0 eps kappa : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (hmu0 : 0 < mu0)
    (hDelta : 0 < Delta) (hDelta0 : 0 < Delta0) (hg0 : 0 < g0)
    (heps : 0 < eps) (hkappa : paperC0 ell0 mu0 ≤ kappa)
    (hregime : eps ^ 2 ≤ paperC1 ell0 Delta0 g0 * ell * Delta) :
    paperC2 ell0 mu0 Delta0 g0 * kappa * ell * Delta / eps ^ 2 ≤
      (paperM ell ell0 Delta Delta0 g0 eps *
        (paperN ell0 mu0 kappa + 1) : ℕ) := by
  have hkappa0 : 0 ≤ kappa :=
    le_trans (by
      unfold paperC0
      positivity : 0 ≤ paperC0 ell0 mu0) hkappa
  have hM := paperM_lower hell hell0 hDelta hDelta0 hg0 heps hregime
  have hN := paperN_plus_one_lower (ell0 := ell0) (mu0 := mu0)
    (kappa := kappa)
  have hM0 : 0 ≤ g0 ^ 2 * ell * Delta /
      (8 * ell0 * Delta0 * eps ^ 2) := by positivity
  have hN0 : 0 ≤ mu0 / ell0 * kappa := by positivity
  have hprod := mul_le_mul hM hN hN0
    (by exact_mod_cast (Nat.zero_le (paperM ell ell0 Delta Delta0 g0 eps)))
  calc
    paperC2 ell0 mu0 Delta0 g0 * kappa * ell * Delta / eps ^ 2 =
        (g0 ^ 2 * ell * Delta / (8 * ell0 * Delta0 * eps ^ 2)) *
          (mu0 / ell0 * kappa) := by
      unfold paperC2
      field_simp [ne_of_gt hell0, ne_of_gt hDelta0, ne_of_gt heps]
    _ ≤ (paperM ell ell0 Delta Delta0 g0 eps : ℝ) *
          (paperN ell0 mu0 kappa + 1 : ℕ) := hprod
    _ = (paperM ell ell0 Delta Delta0 g0 eps *
          (paperN ell0 mu0 kappa + 1) : ℕ) := by norm_num

/-- A single machine-checkable certificate for every numerical step in the
manuscript's parameter choice. -/
theorem paper_parameter_certificate
    {ell ell0 mu0 Delta Delta0 g0 eps kappa : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (hmu0 : 0 < mu0)
    (hDelta : 0 < Delta) (hDelta0 : 0 < Delta0) (hg0 : 0 < g0)
    (heps : 0 < eps) (hkappa : paperC0 ell0 mu0 ≤ kappa)
    (hregime : eps ^ 2 ≤ paperC1 ell0 Delta0 g0 * ell * Delta) :
    2 ≤ paperN ell0 mu0 kappa ∧
    2 ≤ paperM ell ell0 Delta Delta0 g0 eps ∧
    ell / kappa ≤
      ell * mu0 / (ell0 * (paperN ell0 mu0 kappa : ℝ)) ∧
    ell * paperLambda ell ell0 g0 eps ^ 2 / ell0 * Delta0 *
      (paperM ell ell0 Delta Delta0 g0 eps : ℝ) ≤ Delta ∧
    ell * paperLambda ell ell0 g0 eps / ell0 * g0 = 2 * eps ∧
    paperC2 ell0 mu0 Delta0 g0 * kappa * ell * Delta / eps ^ 2 ≤
      (paperM ell ell0 Delta Delta0 g0 eps *
        (paperN ell0 mu0 kappa + 1) : ℕ) := by
  have hkappaPos : 0 < kappa := by
    have hc0 : 0 < paperC0 ell0 mu0 := by
      unfold paperC0
      positivity
    exact hc0.trans_le hkappa
  exact ⟨paperN_two_le hell0 hmu0 hkappa,
    paperM_two_le hell hell0 hDelta hDelta0 hg0 heps hregime,
    scaled_dualPL_at_least_target hell hell0 hmu0 hkappaPos hkappa,
    scaled_gap_le_target hell hell0 hDelta.le hDelta0 hg0 heps,
    paperLambda_gradient_scale hell.ne' hell0.ne' hg0.ne',
    paper_chain_length_lower hell hell0 hmu0 hDelta hDelta0 hg0 heps
      hkappa hregime⟩

end

end NCPLRevised
