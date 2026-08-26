/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.CertificateScaling

/-!
# Constants made explicit in the revised manuscript

The revised proof sets `mu0 = 1 / 640`, `ell0 = 2 * L_C`, `g0 = 1`, and
`Delta0 = 12`.  Its appendix chooses `L_C` as the larger of `1` and a
uniform Hessian bound.  This file records the resulting elementary facts.
-/

namespace NCPLRevised

noncomputable section

def revisedMu0 : ℝ := 1 / 640
def revisedEll0 (LC : ℝ) : ℝ := 2 * LC
def revisedG0 : ℝ := 1
def revisedDelta0 : ℝ := 12

theorem revisedMu0_pos : 0 < revisedMu0 := by
  norm_num [revisedMu0]

theorem revisedEll0_pos {LC : ℝ} (hLC : 0 < LC) :
    0 < revisedEll0 LC := by
  unfold revisedEll0
  positivity

theorem revisedDelta0_pos : 0 < revisedDelta0 := by
  norm_num [revisedDelta0]

/-- With the constants stated in the revised manuscript,
`c0 = 2 ell0 / mu0 = 2560 L_C`. -/
theorem revised_c0_eq (LC : ℝ) :
    paperC0 (revisedEll0 LC) revisedMu0 = 2560 * LC := by
  norm_num [paperC0, revisedEll0, revisedMu0]
  ring

/-- The manuscript's choice `L_C >= 1` directly implies `c0 > 1`.
This is independent of the later hypothesis `kappa >= c0`. -/
theorem revised_c0_gt_one {LC : ℝ} (hLC : 1 ≤ LC) :
    1 < paperC0 (revisedEll0 LC) revisedMu0 := by
  rw [revised_c0_eq]
  nlinarith

theorem revised_c1_pos {LC : ℝ} (hLC : 0 < LC) :
    0 < paperC1 (revisedEll0 LC) revisedDelta0 revisedG0 := by
  unfold paperC1 revisedEll0 revisedDelta0 revisedG0
  positivity

theorem revised_c2_pos {LC : ℝ} (hLC : 0 < LC) :
    0 < paperC2 (revisedEll0 LC) revisedMu0 revisedDelta0 revisedG0 := by
  unfold paperC2 revisedEll0 revisedMu0 revisedDelta0 revisedG0
  positivity

end

end NCPLRevised
