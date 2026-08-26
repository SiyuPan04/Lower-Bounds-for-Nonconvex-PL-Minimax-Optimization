/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.HardInstanceAssembly
import NCPLRevised.EmbeddedCellSmoothness

/-!
# The concrete unscaled NC--PL hard instance

This file instantiates the finite assembly framework with the exact cell
`C(s,t;y)` from the revised manuscript.  It proves constructively that dual
maximization is attained and gives exactly the Carmon chain, sums the local
dual PL inequalities, and transports the terminal-gradient and initial-gap
certificates to the resulting value function.
-/

namespace NCPLRevised

noncomputable section

/-- The manuscript's unscaled saddle function `bar f`. -/
def barF (M N : ℕ) (x : EVec M) (y : EVec (M * N)) : ℝ :=
  assembledCells (embeddedCell N) x y

/-- The explicit value function.  The envelope theorem below proves that
this is the attained maximum of `barF M N x`. -/
def barPhi (M : ℕ) (x : EVec M) : ℝ := carmonF M x

/-- The blockwise maximizing dual vector used in the envelope proof. -/
def barDualMaximizer (M N : ℕ) (x : EVec M) : EVec (M * N) :=
  assembledDualMaximizer (fun s _t ↦ embeddedCellMaximizer N s) x

theorem assembledValues_carmonInteraction (M : ℕ) (x : EVec M) :
    assembledValues carmonInteraction x = carmonF M x := by
  rw [show carmonInteraction = assemblyCarmonInteraction by rfl]
  exact assembledValues_assemblyCarmonInteraction M x

/-- Constructive form of
`max_y barF(x,y) = barPhi(x) = carmonF(x)`: the first component is the
global upper bound and the second displays a point attaining it. -/
theorem barF_envelope {M N : ℕ} (hN : 2 ≤ N) (x : EVec M) :
    (∀ y : EVec (M * N), barF M N x y ≤ barPhi M x) ∧
      barF M N x (barDualMaximizer M N x) = barPhi M x := by
  have hsep := finite_separable_envelope
    (cell := embeddedCell N) (value := carmonInteraction)
    (witness := fun s _t ↦ embeddedCellMaximizer N s)
    (fun s t y ↦ (embeddedCell_max hN s t).1 y)
    (fun s t ↦ (embeddedCell_max hN s t).2) x
  simpa [barF, barPhi, barDualMaximizer,
    assembledValues_carmonInteraction M x] using hsep

/-- Set-theoretic maximum statement for the concrete value function. -/
theorem barF_isGreatest {M N : ℕ} (hN : 2 ≤ N) (x : EVec M) :
    IsGreatest (Set.range (barF M N x)) (barPhi M x) := by
  have h := barF_envelope (M := M) hN x
  constructor
  · exact ⟨barDualMaximizer M N x, h.2⟩
  · rintro _ ⟨y, rfl⟩
    exact h.1 y

@[simp] theorem barPhi_eq_carmonF (M : ℕ) (x : EVec M) :
    barPhi M x = carmonF M x := rfl

/-! ## The actual blockwise dual gradient and its PL certificate -/

/-- The explicit `y`-gradient, flattened in canonical block order. -/
def barDualGradient (M N : ℕ) (x : EVec M) (y : EVec (M * N)) :
    EVec (M * N) :=
  flattenDualBlocks fun i ↦
    scaledPerspectiveGradient N
      (outerRho (primalPrev x i))
      (carmonLiftedH (primalPrev x i) (x i))
      (dualBlock y i)

@[simp] theorem dualBlock_barDualGradient (M N : ℕ)
    (x : EVec M) (y : EVec (M * N)) (i : Fin M) :
    dualBlock (barDualGradient M N x y) i =
      scaledPerspectiveGradient N
        (outerRho (primalPrev x i))
        (carmonLiftedH (primalPrev x i) (x i))
        (dualBlock y i) := by
  simp [barDualGradient]

/-- The squared Euclidean norm of the concrete flattened dual gradient. -/
def barDualGradientSq (M N : ℕ) (x : EVec M) (y : EVec (M * N)) : ℝ :=
  euclideanNormSq (barDualGradient M N x y)

theorem euclideanNormSq_flattenDualBlocks {M N : ℕ}
    (Y : Fin M → ChainPoint N) :
    euclideanNormSq (flattenDualBlocks Y) =
      ∑ i : Fin M, euclideanNormSq (Y i) := by
  unfold euclideanNormSq
  calc
    (∑ k : Fin (M * N), flattenDualBlocks Y k ^ 2) =
        ∑ ij : Fin M × Fin N,
          flattenDualBlocks Y (finProdFinEquiv ij) ^ 2 := by
            exact (Equiv.sum_comp finProdFinEquiv
              (fun k : Fin (M * N) ↦ flattenDualBlocks Y k ^ 2)).symm
    _ = ∑ ij : Fin M × Fin N, (Y ij.1 ij.2) ^ 2 := by
          apply Finset.sum_congr rfl
          intro ij _
          simp [flattenDualBlocks]
    _ = ∑ i : Fin M, ∑ j : Fin N, (Y i j) ^ 2 :=
          Fintype.sum_prod_type _

theorem barDualGradientSq_eq_sum (M N : ℕ)
    (x : EVec M) (y : EVec (M * N)) :
    barDualGradientSq M N x y =
      ∑ i : Fin M,
        euclideanNormSq
          (scaledPerspectiveGradient N
            (outerRho (primalPrev x i))
            (carmonLiftedH (primalPrev x i) (x i))
            (dualBlock y i)) := by
  unfold barDualGradientSq barDualGradient
  exact euclideanNormSq_flattenDualBlocks _

/-- Local dual PL inequality after subtracting the `-5 rho²` offset. -/
theorem embeddedCell_dual_PL {N : ℕ} (hN : 2 ≤ N)
    (s t : ℝ) (y : ChainPoint N) :
    (1 / 2 : ℝ) *
        euclideanNormSq
          (scaledPerspectiveGradient N (outerRho s) (carmonLiftedH s t) y) ≥
      (1 / (640 * (N : ℝ))) *
        (carmonInteraction s t - embeddedCell N s t y) := by
  have hadm := embeddedCell_parameters_admissible s t
  have h := scaledPerspectiveBlock_PL hN hadm.1 hadm.2.1 hadm.2.2 y
  convert h using 1
  simp only [embeddedCell, carmonLiftedH]
  ring

/-- Proposition 5.1's dual PL inequality with `mu0 = 1/640`, summed over
the disjoint dual blocks. -/
theorem barF_dual_PL {M N : ℕ} (hN : 2 ≤ N)
    (x : EVec M) (y : EVec (M * N)) :
    (1 / 2 : ℝ) * barDualGradientSq M N x y ≥
      (1 / (640 * (N : ℝ))) * (barPhi M x - barF M N x y) := by
  have hsum :
      ∑ i : Fin M,
          (1 / 2 : ℝ) *
            euclideanNormSq
              (scaledPerspectiveGradient N
                (outerRho (primalPrev x i))
                (carmonLiftedH (primalPrev x i) (x i))
                (dualBlock y i)) ≥
        ∑ i : Fin M,
          (1 / (640 * (N : ℝ))) *
            (carmonInteraction (primalPrev x i) (x i) -
              embeddedCell N (primalPrev x i) (x i) (dualBlock y i)) := by
    exact Finset.sum_le_sum fun i _ ↦ embeddedCell_dual_PL hN _ _ _
  rw [← Finset.mul_sum] at hsum
  rw [← Finset.mul_sum] at hsum
  rw [barDualGradientSq_eq_sum]
  unfold barPhi barF assembledCells
  rw [← assembledValues_carmonInteraction]
  unfold assembledValues
  rw [← Finset.sum_sub_distrib]
  exact hsum

/-! ## Proposition 5.3 for the concrete envelope -/

/-- The concrete value function has the actual displayed gradient, terminal
obstruction, final-coordinate ordering, and exact `12 M` initial-gap bound. -/
theorem proposition5_3_concrete (M N : ℕ) (hM : 0 < M) :
    (∀ x : EVec M,
      HasCarmonFDerivAt (barPhi M) (evecDot (carmonGradient M x)) x) ∧
    (∀ x : EVec M,
      x (carmonLastIndex M hM) = 0 →
        1 ≤ vecSq (carmonGradient M x)) ∧
    (∀ x : EVec M, ∀ y : EVec (M * N),
      assembleOrdered x y
          ⟨M * (N + 1) - 1,
            Nat.sub_lt (Nat.mul_pos hM (Nat.succ_pos N)) (by omega)⟩ =
        x (carmonLastIndex M hM)) ∧
    barPhi M 0 - sInf (Set.range (barPhi M)) ≤ 12 * (M : ℝ) := by
  have hc := carmon_terminal_gap_certificate M hM
  exact ⟨by
      intro x
      change HasCarmonFDerivAt (carmonF M) (evecDot (carmonGradient M x)) x
      exact hc.1 x,
    hc.2.1,
    fun x y ↦ assembleOrdered_last_eq_primal_last hM x y,
    by
      change carmonF M 0 - sInf (Set.range (carmonF M)) ≤ 12 * (M : ℝ)
      exact hc.2.2⟩

/-- Combined exact value/dual-PL/terminal-gap certificate for Propositions
5.1 and 5.3.  Every conclusion concerns the concrete definitions above. -/
theorem concrete_value_and_dual_certificate (M N : ℕ)
    (hM : 0 < M) (hN : 2 ≤ N) :
    (∀ x : EVec M, IsGreatest (Set.range (barF M N x)) (barPhi M x)) ∧
    (∀ x : EVec M, ∀ y : EVec (M * N),
      (1 / 2 : ℝ) * barDualGradientSq M N x y ≥
        (1 / (640 * (N : ℝ))) * (barPhi M x - barF M N x y)) ∧
    (∀ x : EVec M,
      HasCarmonFDerivAt (barPhi M) (evecDot (carmonGradient M x)) x) ∧
    (∀ x : EVec M,
      x (carmonLastIndex M hM) = 0 →
        1 ≤ vecSq (carmonGradient M x)) ∧
    barPhi M 0 - sInf (Set.range (barPhi M)) ≤ 12 * (M : ℝ) := by
  have hp53 := proposition5_3_concrete M N hM
  exact ⟨barF_isGreatest hN,
    fun x y ↦ barF_dual_PL hN x y,
    hp53.1, hp53.2.1, hp53.2.2.2⟩

end

end NCPLRevised
