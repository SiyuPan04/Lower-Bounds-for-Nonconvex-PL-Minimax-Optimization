/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import Mathlib

/-!
# Saddle zero-chain discovery

This is the coordinate-reordered form of Definitions 2.4 and 2.7.  It proves
the support induction used in the proof of Theorem 3.1 without assuming a
linear-span method.
-/

namespace NCPLRevised

abbrev EVec (d : ℕ) := Fin d → ℝ

/-- Zero-based form of `supp(z) subseteq [k]`: coordinates numbered `k` and
above vanish. -/
def SupportedBelow {d : ℕ} (k : ℕ) (z : EVec d) : Prop :=
  ∀ i, k ≤ i.1 → z i = 0

theorem supportedBelow_zero (d k : ℕ) :
    SupportedBelow k (0 : EVec d) := by
  intro i hi
  rfl

theorem SupportedBelow.mono {d a b : ℕ} {z : EVec d}
    (h : SupportedBelow a z) (hab : a ≤ b) : SupportedBelow b z := by
  intro i hbi
  exact h i (hab.trans hbi)

/-- A reordered joint saddle-gradient field is a first-order zero-chain. -/
def IsFirstOrderSaddleZeroChain {d : ℕ} (field : EVec d → EVec d) : Prop :=
  ∀ k z, SupportedBelow k z → SupportedBelow (k + 1) (field z)

/-- Definition 2.4, expressed on the reordered joint vector. -/
def QueriesAreZeroRespecting {d : ℕ} (field : EVec d → EVec d)
    (query : ℕ → EVec d) : Prop :=
  ∀ t i, query t i ≠ 0 → ∃ s < t, field (query s) i ≠ 0

/-- Optional explicit output model used for Remark 3.1. -/
def OutputsAreZeroRespecting {d : ℕ} (field : EVec d → EVec d)
    (query output : ℕ → EVec d) : Prop :=
  ∀ t i, output t i ≠ 0 → ∃ s < t, field (query s) i ≠ 0

theorem sequential_query_discovery {d : ℕ} {field : EVec d → EVec d}
    {query : ℕ → EVec d} (hfield : IsFirstOrderSaddleZeroChain field)
    (hquery : QueriesAreZeroRespecting field query) (t : ℕ) :
    SupportedBelow t (query t) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro i hti
      by_contra hne
      obtain ⟨s, hst, hresponse⟩ := hquery t i hne
      have hsupp : SupportedBelow s (query s) := ih s hst
      have hnext : SupportedBelow (s + 1) (field (query s)) :=
        hfield s (query s) hsupp
      have hsit : s + 1 ≤ i.1 := (Nat.succ_le_of_lt hst).trans hti
      exact hresponse (hnext i hsit)

theorem sequential_output_discovery {d : ℕ} {field : EVec d → EVec d}
    {query output : ℕ → EVec d}
    (hfield : IsFirstOrderSaddleZeroChain field)
    (hquery : QueriesAreZeroRespecting field query)
    (houtput : OutputsAreZeroRespecting field query output) (t : ℕ) :
    SupportedBelow t (output t) := by
  intro i hti
  by_contra hne
  obtain ⟨s, hst, hresponse⟩ := houtput t i hne
  have hsupp : SupportedBelow s (query s) :=
    sequential_query_discovery hfield hquery s
  have hnext : SupportedBelow (s + 1) (field (query s)) :=
    hfield s (query s) hsupp
  have hsit : s + 1 ≤ i.1 := (Nat.succ_le_of_lt hst).trans hti
  exact hresponse (hnext i hsit)

/-- Condition (C2) forces the last coordinate to remain zero before the full
chain has been discovered. -/
theorem terminal_coordinate_zero_before_chain {d : ℕ} (hd : 0 < d)
    {field : EVec d → EVec d} {query : ℕ → EVec d}
    (hfield : IsFirstOrderSaddleZeroChain field)
    (hquery : QueriesAreZeroRespecting field query)
    {t : ℕ} (ht : t < d) :
    query t ⟨d - 1, Nat.sub_lt hd (by omega)⟩ = 0 := by
  have hsupp := sequential_query_discovery hfield hquery t
  apply hsupp
  change t ≤ d - 1
  omega

/-- Conditional C2+C3 obstruction: a terminal-coordinate gradient lower
bound rules out epsilon-stationarity at every early zero-respecting query. -/
theorem zero_chain_obstruction {d : ℕ} (hd : 0 < d)
    {field : EVec d → EVec d} {query : ℕ → EVec d}
    {envelopeGradSq : EVec d → ℝ} {g0 eps : ℝ}
    (hfield : IsFirstOrderSaddleZeroChain field)
    (hquery : QueriesAreZeroRespecting field query)
    (hterminal : ∀ z, z ⟨d - 1, Nat.sub_lt hd (by omega)⟩ = 0 →
      g0 ^ 2 ≤ envelopeGradSq z)
    (hthreshold : eps ^ 2 < g0 ^ 2)
    {t : ℕ} (ht : t < d) :
    ¬envelopeGradSq (query t) ≤ eps ^ 2 := by
  intro hstationary
  have hzero := terminal_coordinate_zero_before_chain hd hfield hquery ht
  have hlower := hterminal (query t) hzero
  linarith

end NCPLRevised
