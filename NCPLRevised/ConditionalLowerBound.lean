/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.CertificateScaling
import NCPLRevised.BlockLayout

/-!
# Conditional zero-respecting lower bound

This theorem is the formally checked implication from the paper's
zero-chain/terminal certificates and its parameter choices to the explicit
Omega lower bound.  The analytic construction of the certificates remains a
separate obligation.
-/

namespace NCPLRevised

noncomputable section

theorem conditional_zero_respecting_lower_bound
    {ell ell0 mu0 Delta Delta0 g0 eps kappa : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (hmu0 : 0 < mu0)
    (hDelta : 0 < Delta) (hDelta0 : 0 < Delta0) (hg0 : 0 < g0)
    (heps : 0 < eps) (hkappa : paperC0 ell0 mu0 ≤ kappa)
    (hregime : eps ^ 2 ≤ paperC1 ell0 Delta0 g0 * ell * Delta)
    (field : EVec (paperM ell ell0 Delta Delta0 g0 eps *
      (paperN ell0 mu0 kappa + 1)) →
      EVec (paperM ell ell0 Delta Delta0 g0 eps *
        (paperN ell0 mu0 kappa + 1)))
    (query : ℕ → EVec (paperM ell ell0 Delta Delta0 g0 eps *
      (paperN ell0 mu0 kappa + 1)))
    (envelopeGradSq : EVec (paperM ell ell0 Delta Delta0 g0 eps) → ℝ)
    (hfield : IsFirstOrderSaddleZeroChain field)
    (hquery : QueriesAreZeroRespecting field query)
    (hterminal : ∀ z,
      z ⟨paperM ell ell0 Delta Delta0 g0 eps *
          (paperN ell0 mu0 kappa + 1) - 1,
        by
          have hM := paperM_two_le hell hell0 hDelta hDelta0 hg0 heps hregime
          have hprod : 0 < paperM ell ell0 Delta Delta0 g0 eps *
              (paperN ell0 mu0 kappa + 1) :=
            Nat.mul_pos (by omega) (Nat.succ_pos _)
          exact Nat.sub_lt hprod (by omega)⟩ = 0 →
      (ell * paperLambda ell ell0 g0 eps / ell0 * g0) ^ 2 ≤
        envelopeGradSq (orderedPrimal z))
    {t : ℕ}
    (ht : (t : ℝ) <
      paperC2 ell0 mu0 Delta0 g0 * kappa * ell * Delta / eps ^ 2) :
    ¬envelopeGradSq (orderedPrimal (query t)) ≤ eps ^ 2 := by
  let M := paperM ell ell0 Delta Delta0 g0 eps
  let N := paperN ell0 mu0 kappa
  let d := M * (N + 1)
  have hMtwo : 2 ≤ M :=
    paperM_two_le hell hell0 hDelta hDelta0 hg0 heps hregime
  have hNtwo : 2 ≤ N := paperN_two_le hell0 hmu0 hkappa
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hlength := paper_chain_length_lower hell hell0 hmu0 hDelta
    hDelta0 hg0 heps hkappa hregime
  have htdReal : (t : ℝ) < (d : ℕ) := by
    exact ht.trans_le (by simpa [d, M, N] using hlength)
  have htd : t < d := by exact_mod_cast htdReal
  have hscale := paperLambda_gradient_scale hell.ne' hell0.ne' hg0.ne'
    (eps := eps)
  have hthreshold : eps ^ 2 <
      (ell * paperLambda ell ell0 g0 eps / ell0 * g0) ^ 2 := by
    rw [hscale]
    nlinarith [sq_pos_of_pos heps]
  apply zero_chain_obstruction hd hfield hquery
    (g0 := ell * paperLambda ell ell0 g0 eps / ell0 * g0)
    (eps := eps)
    (envelopeGradSq := fun z ↦ envelopeGradSq (orderedPrimal z))
  · intro z hz
    apply hterminal z
    simpa [d, M, N] using hz
  · exact hthreshold
  · exact htd

end

end NCPLRevised
