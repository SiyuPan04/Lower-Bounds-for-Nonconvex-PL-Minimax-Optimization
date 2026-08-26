/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.CarmonGates
import NCPLRevised.OuterLinearAlgebra

/-!
# The outer Carmon zero-chain

The definitions use zero-based `Fin T` indices.  Coordinate zero is the
paper's special first term, while every later term couples a coordinate to
its predecessor.
-/

namespace NCPLRevised

noncomputable section

open MeasureTheory

/-- The exact summand `h_i` in the article. -/
def carmonTerm {T : Nat} (x : EVec T) (i : Fin T) : ℝ :=
  if hi : i.1 = 0 then
    -carmonPsi 1 * carmonPhi (x i)
  else
    carmonPsi (-x ⟨i.1 - 1, by omega⟩) * carmonPhi (-x i) -
      carmonPsi (x ⟨i.1 - 1, by omega⟩) * carmonPhi (x i)

def carmonF (T : Nat) (x : EVec T) : ℝ :=
  ∑ i : Fin T, carmonTerm x i

def carmonLastIndex (T : Nat) (hT : 0 < T) : Fin T :=
  ⟨T - 1, Nat.sub_lt hT (by omega)⟩

/-- The squared activation gate `rho_i²`, with `rho_1² = 1`. -/
def carmonRhoSq {T : Nat} (x : EVec T) (i : Fin T) : ℝ :=
  if hi : i.1 = 0 then 1 else
    carmonPsi (x ⟨i.1 - 1, by omega⟩) +
      carmonPsi (-x ⟨i.1 - 1, by omega⟩)

/-- Positive magnitude of the derivative of term `i` in its current
coordinate. -/
def carmonIncoming {T : Nat} (x : EVec T) (i : Fin T) : ℝ :=
  if hi : i.1 = 0 then carmonPhiDeriv (x i) else
    carmonPsi (-x ⟨i.1 - 1, by omega⟩) * carmonPhiDeriv (-x i) +
      carmonPsi (x ⟨i.1 - 1, by omega⟩) * carmonPhiDeriv (x i)

/-- Positive magnitude of the derivative contributed by the successor term. -/
def carmonForward {T : Nat} (x : EVec T) (i : Fin T) : ℝ :=
  if hi : i.1 + 1 < T then
    carmonPsiDeriv (-x i) * carmonPhi (-x ⟨i.1 + 1, hi⟩) +
      carmonPsiDeriv (x i) * carmonPhi (x ⟨i.1 + 1, hi⟩)
  else 0

/-- Coordinate formula for the actual gradient of `carmonF`. -/
def carmonGradient (T : Nat) (x : EVec T) : EVec T :=
  fun i ↦ -(carmonIncoming x i + carmonForward x i)

def carmonPhiCap : ℝ :=
  Real.sqrt (Real.exp 1) * ∫ s : ℝ, carmonGaussian s

def carmonTermCap : ℝ := Real.exp 1 * carmonPhiCap

def carmonRho {T : Nat} (x : EVec T) (i : Fin T) : ℝ :=
  Real.sqrt (carmonRhoSq x i)

def carmonOuterA {T : Nat} (x : EVec T) (i : Fin T) : ℝ :=
  carmonPhiCap * carmonRhoSq x i + carmonTerm x i

def carmonAmax : ℝ := 2 * carmonPhiCap

theorem carmonPhiCap_nonneg : 0 ≤ carmonPhiCap := by
  unfold carmonPhiCap
  apply mul_nonneg (Real.sqrt_nonneg _)
  exact MeasureTheory.integral_nonneg_of_ae
    (ae_of_all _ fun s ↦ (carmonGaussian_pos s).le)

theorem carmonTermCap_nonneg : 0 ≤ carmonTermCap := by
  exact mul_nonneg (Real.exp_pos _).le carmonPhiCap_nonneg

theorem carmonPhi_le_cap (t : ℝ) : carmonPhi t ≤ carmonPhiCap := by
  exact carmonPhi_le_full_integral t

theorem carmonRhoSq_nonneg {T : Nat} (x : EVec T) (i : Fin T) :
    0 ≤ carmonRhoSq x i := by
  by_cases hi : i.1 = 0
  · simp [carmonRhoSq, hi]
  · simp only [carmonRhoSq, dif_neg hi]
    exact add_nonneg (carmonPsi_nonneg _) (carmonPsi_nonneg _)

theorem carmonRho_nonneg {T : Nat} (x : EVec T) (i : Fin T) :
    0 ≤ carmonRho x i := Real.sqrt_nonneg _

theorem carmonRho_sq {T : Nat} (x : EVec T) (i : Fin T) :
    carmonRho x i ^ 2 = carmonRhoSq x i := by
  unfold carmonRho
  exact Real.sq_sqrt (carmonRhoSq_nonneg x i)

theorem abs_carmonTerm_le_phiCap_mul_rhoSq {T : Nat}
    (x : EVec T) (i : Fin T) :
    |carmonTerm x i| ≤ carmonPhiCap * carmonRhoSq x i := by
  by_cases hi : i.1 = 0
  · rw [carmonTerm, dif_pos hi, carmonPsi_one]
    simp only [neg_mul, one_mul, abs_neg]
    rw [abs_of_nonneg (carmonPhi_nonneg _)]
    simpa [carmonRhoSq, hi] using carmonPhi_le_cap (x i)
  · rw [carmonTerm, dif_neg hi]
    have htri := abs_sub
      (carmonPsi (-x ⟨i.1 - 1, by omega⟩) * carmonPhi (-x i))
      (carmonPsi (x ⟨i.1 - 1, by omega⟩) * carmonPhi (x i))
    have hleft0 : 0 ≤ carmonPsi (-x ⟨i.1 - 1, by omega⟩) *
        carmonPhi (-x i) :=
      mul_nonneg (carmonPsi_nonneg _) (carmonPhi_nonneg _)
    have hright0 : 0 ≤ carmonPsi (x ⟨i.1 - 1, by omega⟩) *
        carmonPhi (x i) :=
      mul_nonneg (carmonPsi_nonneg _) (carmonPhi_nonneg _)
    rw [abs_of_nonneg hleft0, abs_of_nonneg hright0] at htri
    calc
      |carmonPsi (-x ⟨i.1 - 1, by omega⟩) * carmonPhi (-x i) -
          carmonPsi (x ⟨i.1 - 1, by omega⟩) * carmonPhi (x i)| ≤
          carmonPsi (-x ⟨i.1 - 1, by omega⟩) * carmonPhi (-x i) +
            carmonPsi (x ⟨i.1 - 1, by omega⟩) * carmonPhi (x i) := htri
      _ ≤ carmonPsi (-x ⟨i.1 - 1, by omega⟩) * carmonPhiCap +
            carmonPsi (x ⟨i.1 - 1, by omega⟩) * carmonPhiCap := by
        gcongr
        · exact carmonPsi_nonneg _
        · exact carmonPhi_le_cap _
        · exact carmonPsi_nonneg _
        · exact carmonPhi_le_cap _
      _ = carmonPhiCap * carmonRhoSq x i := by
        rw [carmonRhoSq, dif_neg hi]
        ring

theorem carmonOuterA_nonneg {T : Nat} (x : EVec T) (i : Fin T) :
    0 ≤ carmonOuterA x i := by
  unfold carmonOuterA
  have habs := abs_carmonTerm_le_phiCap_mul_rhoSq x i
  linarith [neg_le_of_abs_le habs]

theorem carmonAmax_nonneg : 0 ≤ carmonAmax := by
  unfold carmonAmax
  exact mul_nonneg (by norm_num) carmonPhiCap_nonneg

theorem carmonOuterA_le {T : Nat} (x : EVec T) (i : Fin T) :
    carmonOuterA x i ≤ carmonAmax * carmonRho x i ^ 2 := by
  unfold carmonOuterA carmonAmax
  rw [carmonRho_sq]
  have habs := abs_carmonTerm_le_phiCap_mul_rhoSq x i
  have hterm := le_of_abs_le habs
  linarith

theorem carmonTerm_lower {T : Nat} (x : EVec T) (i : Fin T) :
    -carmonTermCap ≤ carmonTerm x i := by
  have heone : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hphi0 := carmonPhi_nonneg (x i)
  have hphicap := carmonPhi_le_cap (x i)
  have hphineg0 := carmonPhi_nonneg (-x i)
  have hphinegcap := carmonPhi_le_cap (-x i)
  by_cases hi : i.1 = 0
  · rw [carmonTerm, dif_pos hi, carmonPsi_one]
    rw [show -1 * carmonPhi (x i) = -carmonPhi (x i) by ring]
    unfold carmonTermCap
    have hcap : carmonPhiCap ≤ Real.exp 1 * carmonPhiCap := by
      nlinarith [carmonPhiCap_nonneg]
    linarith
  · rw [carmonTerm, dif_neg hi]
    have hpsi := carmonPsi_le_exp_one (x ⟨i.1 - 1, by omega⟩)
    have hprod : carmonPsi (x ⟨i.1 - 1, by omega⟩) * carmonPhi (x i) ≤
        Real.exp 1 * carmonPhiCap := by
      calc
        _ ≤ Real.exp 1 * carmonPhi (x i) :=
          mul_le_mul_of_nonneg_right hpsi hphi0
        _ ≤ Real.exp 1 * carmonPhiCap :=
          mul_le_mul_of_nonneg_left hphicap (Real.exp_pos _).le
    have hfirst : 0 ≤ carmonPsi (-x ⟨i.1 - 1, by omega⟩) *
        carmonPhi (-x i) :=
      mul_nonneg (carmonPsi_nonneg _) hphineg0
    unfold carmonTermCap
    linarith

theorem carmonF_lower (T : Nat) (x : EVec T) :
    -(T : ℝ) * carmonTermCap ≤ carmonF T x := by
  unfold carmonF
  calc
    -(T : ℝ) * carmonTermCap = ∑ _i : Fin T, -carmonTermCap := by
      simp
    _ ≤ ∑ i : Fin T, carmonTerm x i := by
      apply Finset.sum_le_sum
      intro i _
      exact carmonTerm_lower x i

theorem carmonF_zero_nonpos (T : Nat) : carmonF T (0 : EVec T) ≤ 0 := by
  unfold carmonF
  apply Finset.sum_nonpos
  intro i _
  by_cases hi : i.1 = 0
  · simp [carmonTerm, hi, carmonPhi_nonneg]
  · simp [carmonTerm, hi]

theorem carmonF_range_bddBelow (T : Nat) :
    BddBelow (Set.range (carmonF T)) := by
  refine ⟨-(T : ℝ) * carmonTermCap, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact carmonF_lower T x

/-- The initial envelope gap bound (C4), with an explicit numerical constant
represented by the fixed scalar `carmonTermCap`. -/
theorem carmon_initial_gap (T : Nat) :
    carmonF T 0 - sInf (Set.range (carmonF T)) ≤
      (T : ℝ) * carmonTermCap := by
  have hinf : -(T : ℝ) * carmonTermCap ≤
      sInf (Set.range (carmonF T)) := by
    rw [le_csInf_iff (carmonF_range_bddBelow T) (Set.range_nonempty _)]
    rintro _ ⟨x, rfl⟩
    exact carmonF_lower T x
  have hzero := carmonF_zero_nonpos T
  linarith

theorem carmonIncoming_eq_rho_mul {T : Nat} (x : EVec T) (i : Fin T) :
    carmonIncoming x i = carmonRhoSq x i * carmonPhiDeriv (x i) := by
  by_cases hi : i.1 = 0
  · simp [carmonIncoming, carmonRhoSq, hi]
  · simp only [carmonIncoming, carmonRhoSq, dif_neg hi]
    rw [carmonPhiDeriv_neg]
    ring

theorem carmonIncoming_nonneg {T : Nat} (x : EVec T) (i : Fin T) :
    0 ≤ carmonIncoming x i := by
  rw [carmonIncoming_eq_rho_mul]
  exact mul_nonneg (carmonRhoSq_nonneg x i) (carmonPhiDeriv_pos _).le

theorem carmonForward_nonneg {T : Nat} (x : EVec T) (i : Fin T) :
    0 ≤ carmonForward x i := by
  by_cases hi : i.1 + 1 < T
  · simp only [carmonForward, dif_pos hi]
    exact add_nonneg
      (mul_nonneg (carmonPsiDeriv_nonneg _) (carmonPhi_nonneg _))
      (mul_nonneg (carmonPsiDeriv_nonneg _) (carmonPhi_nonneg _))
  · simp [carmonForward, hi]

theorem carmonRhoSq_successor {T : Nat} (x : EVec T) (i : Fin T)
    (hi : i.1 + 1 < T) :
    carmonRhoSq x ⟨i.1 + 1, hi⟩ = carmonPsi (x i) + carmonPsi (-x i) := by
  simp [carmonRhoSq]

/-- The explicit gradient is a one-step zero-chain. -/
theorem carmonGradient_is_zeroChain (T : Nat) :
    IsFirstOrderSaddleZeroChain (carmonGradient T) := by
  intro r x hx i hir
  have hi0 : i.1 ≠ 0 := by omega
  have hxi : x i = 0 := hx i (by omega)
  have hprev : x ⟨i.1 - 1, by omega⟩ = 0 := by
    apply hx
    change r ≤ i.1 - 1
    omega
  unfold carmonGradient
  rw [carmonIncoming, dif_neg hi0]
  simp only [hprev, hxi, neg_zero, carmonPsi_zero, zero_mul, add_zero]
  rw [carmonForward]
  split
  · simp [hxi, carmonPsiDeriv_zero]
  · simp

/-- Some coordinate has an incoming derivative of magnitude at least one
whenever the terminal coordinate is zero. -/
theorem exists_one_le_carmonIncoming {T : Nat} (hT : 0 < T)
    (x : EVec T) (hlast : x (carmonLastIndex T hT) = 0) :
    ∃ i : Fin T, 1 ≤ carmonIncoming x i := by
  let S : Finset (Fin T) := Finset.univ.filter fun i ↦ 1 ≤ carmonRhoSq x i
  let i0 : Fin T := ⟨0, hT⟩
  have hzero : i0 ∈ S := by
    simp [S, carmonRhoSq, i0]
  have hSne : S.Nonempty := ⟨i0, hzero⟩
  let j : Fin T := S.max' hSne
  have hjmem : j ∈ S := Finset.max'_mem S hSne
  have hjrho : 1 ≤ carmonRhoSq x j := by
    exact (Finset.mem_filter.mp hjmem).2
  by_cases hjlast : j = carmonLastIndex T hT
  · refine ⟨j, ?_⟩
    rw [hjlast] at hjrho
    rw [carmonIncoming_eq_rho_mul, hjlast, hlast]
    have hphi := one_le_carmonPhiDeriv_of_abs_le_one
      (show |(0 : ℝ)| ≤ 1 by norm_num)
    exact one_le_mul_of_one_le_of_one_le hjrho hphi
  · have hjlt : j.1 + 1 < T := by
      by_contra hbad
      have hjval : j.1 = T - 1 := by omega
      apply hjlast
      apply Fin.ext
      exact hjval
    let k : Fin T := ⟨j.1 + 1, hjlt⟩
    have hknot : ¬ 1 ≤ carmonRhoSq x k := by
      intro hk
      have hkmem : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
      have hkle : k ≤ j := Finset.le_max' S k hkmem
      have : k.1 ≤ j.1 := hkle
      simp only [k] at this
      omega
    have hknext : carmonRhoSq x k ≤ 1 := le_of_lt (lt_of_not_ge hknot)
    have habs : |x j| ≤ 1 := by
      apply abs_le_one_of_carmonPsi_add_neg_le_one
      rw [← carmonRhoSq_successor x j hjlt]
      simpa only [k] using hknext
    have hphi := one_le_carmonPhiDeriv_of_abs_le_one habs
    refine ⟨j, ?_⟩
    rw [carmonIncoming_eq_rho_mul]
    exact one_le_mul_of_one_le_of_one_le hjrho hphi

/-- Carmon's terminal-gradient property with explicit constant `1` in
squared norm. -/
theorem one_le_vecSq_carmonGradient_of_terminal_zero {T : Nat} (hT : 0 < T)
    (x : EVec T) (hlast : x (carmonLastIndex T hT) = 0) :
    1 ≤ vecSq (carmonGradient T x) := by
  obtain ⟨i, hi⟩ := exists_one_le_carmonIncoming hT x hlast
  have hf := carmonForward_nonneg x i
  have hcoord : 1 ≤ carmonGradient T x i ^ 2 := by
    unfold carmonGradient
    nlinarith [sq_nonneg (carmonIncoming x i + carmonForward x i - 1)]
  have hsingle : carmonGradient T x i ^ 2 ≤
      ∑ j : Fin T, carmonGradient T x j ^ 2 :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (carmonGradient T x j))
      (Finset.mem_univ i)
  unfold vecSq
  exact hcoord.trans hsingle

end

end NCPLRevised
