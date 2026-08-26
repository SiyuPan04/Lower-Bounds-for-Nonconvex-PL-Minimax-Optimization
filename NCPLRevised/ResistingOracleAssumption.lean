/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import Mathlib

/-!
# Explicit interface for the manuscript's unproved Lemma 2.2

The user requested that the finite-horizon resisting-oracle statement be
accepted.  It is therefore represented below as an explicit hypothesis of
the deterministic-transfer theorem, not as a global Lean `axiom`.

The model deliberately abstracts from coordinates.  `rotate` represents the
two orthogonal embeddings `(U,V)`, while `project` represents projection by
their transposes.  Every inhabitant of `Algorithm` is understood to be a
deterministic first-order method; `zeroRespecting` selects the subclass used
in Theorem 3.1.
-/

namespace NCPLRevised

universe uAlg uInst uPoint uFrame

/-- The data needed for the finite-horizon reduction in Theorem 3.2. -/
structure FiniteHorizonModel
    (Algorithm : Type uAlg) (Instance : Type uInst)
    (Point : Type uPoint) (Frame : Type uFrame) where
  query : Algorithm → Instance → ℕ → Point
  rotate : Frame → Instance → Instance
  project : Frame → Point → Point
  zeroRespecting : Algorithm → Prop
  admissible : Instance → Prop
  stationary : Instance → Point → Prop

/-- Exact abstract content of Lemma 2.2: for each horizon and deterministic
method there is one zero-respecting deterministic simulator; for every base
instance, suitable frames make all projected queries agree up to the horizon.
-/
def FiniteHorizonResistingOracle
    {Algorithm : Type uAlg} {Instance : Type uInst}
    {Point : Type uPoint} {Frame : Type uFrame}
    (M : FiniteHorizonModel Algorithm Instance Point Frame) : Prop :=
  ∀ (T : ℕ) (A : Algorithm),
    ∃ Z : Algorithm, M.zeroRespecting Z ∧
      ∀ f : Instance, ∃ frame : Frame, ∀ t : ℕ, t < T →
        M.project frame (M.query A (M.rotate frame f) t) = M.query Z f t

/-- The two conclusions of the manuscript's proved rotation-invariance
Lemma 2.1 that are used by Theorem 3.2. -/
def RotationPreservesProblem
    {Algorithm : Type uAlg} {Instance : Type uInst}
    {Point : Type uPoint} {Frame : Type uFrame}
    (M : FiniteHorizonModel Algorithm Instance Point Frame) : Prop :=
  (∀ frame f, M.admissible f → M.admissible (M.rotate frame f)) ∧
  (∀ frame f x,
    M.stationary (M.rotate frame f) x ↔
      M.stationary f (M.project frame x))

/-- A fixed instance defeats every zero-respecting method before time `T`. -/
def ZeroRespectingHardInstance
    {Algorithm : Type uAlg} {Instance : Type uInst}
    {Point : Type uPoint} {Frame : Type uFrame}
    (M : FiniteHorizonModel Algorithm Instance Point Frame)
    (T : ℕ) (f : Instance) : Prop :=
  M.admissible f ∧
    ∀ Z : Algorithm, M.zeroRespecting Z → ∀ t : ℕ, t < T →
      ¬M.stationary f (M.query Z f t)

/-- Conditional form of Theorem 3.2.  Lemma 2.2 is visible as `hRO` in the
theorem signature.  The proof itself is ordinary kernel-checked Lean logic. -/
theorem deterministic_failure_before_of_resistingOracle
    {Algorithm : Type uAlg} {Instance : Type uInst}
    {Point : Type uPoint} {Frame : Type uFrame}
    (M : FiniteHorizonModel Algorithm Instance Point Frame)
    {T : ℕ}
    (hRO : FiniteHorizonResistingOracle M)
    (hrotation : RotationPreservesProblem M)
    {f : Instance} (hhard : ZeroRespectingHardInstance M T f)
    (A : Algorithm) :
    ∃ rotatedInstance : Instance,
      M.admissible rotatedInstance ∧
      ∀ t : ℕ, t < T → ¬M.stationary rotatedInstance
        (M.query A rotatedInstance t) := by
  obtain ⟨Z, hZ, hsimulation⟩ := hRO T A
  obtain ⟨frame, hagree⟩ := hsimulation f
  refine ⟨M.rotate frame f, hrotation.1 frame f hhard.1, ?_⟩
  intro t ht hstationary
  have hprojected :
      M.stationary f
        (M.project frame (M.query A (M.rotate frame f) t)) :=
    (hrotation.2 frame f (M.query A (M.rotate frame f) t)).mp hstationary
  rw [hagree t ht] at hprojected
  exact hhard.2 Z hZ t ht hprojected

end NCPLRevised
