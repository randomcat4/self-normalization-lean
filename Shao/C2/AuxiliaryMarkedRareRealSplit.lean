import Shao.C2.AuxiliaryMarkedDeletion
import Shao.OQ4.KilledPathLaw
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryMarkedRareRealSplit
open MeasureTheory ProbabilityTheory

theorem auxiliary_actual_marked_rare_real_split
    {n : ℕ} (w : Shao.Path n) (z x s a : ℝ) (ha : 0 ≤ a) (hx : 1 ≤ x) :
    let B : Set (Shao.Path (n + 1)) := {v |
      ((3 / 2) * x) * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v (n + 1)|}
    let A : Set (Shao.Path n) := {u | 0 < Shao.energy u ∧
      Real.sqrt ((9 / 4) * x ^ 2 - 1) * Real.sqrt (Shao.energy u) ≤
        |Shao.prefixSum u n|}
    let F : Shao.Path (n + 1) → ℝ := fun v =>
      |v 0| ^ 3 * Real.rpow |Shao.prefixSum v (n + 1)| a * Real.exp (-s * Shao.energy v)
    B.indicator F (Fin.cons z w) ≤
      Real.rpow 2 a * (Real.rpow |z| (3 + a) + |z| ^ 3 * Real.rpow |Shao.prefixSum w n| a) *
        Real.exp (-s * z ^ 2) *
        A.indicator (fun u => Real.exp (-s * Shao.energy u)) w := by
  classical
  intro B A F
  let d : ℝ := Shao.prefixSum w n
  let M : ℝ := max |z| |d|
  have hM0 : 0 ≤ M := (abs_nonneg z).trans (le_max_left |z| |d|)
  have hMaxPow : Real.rpow M a ≤ Real.rpow |z| a + Real.rpow |d| a := by
    rcases le_total |z| |d| with h | h
    · dsimp [M]
      rw [max_eq_right h]
      linarith [Real.rpow_nonneg (abs_nonneg z) a]
    · dsimp [M]
      rw [max_eq_left h]
      linarith [Real.rpow_nonneg (abs_nonneg d) a]
  have hTriangle : |z + d| ≤ 2 * M := (abs_add_le z d).trans (by
    dsimp [M]
    linarith [le_max_left |z| |d|, le_max_right |z| |d|])
  have hPolynomial : Real.rpow |z + d| a ≤
      Real.rpow 2 a * (Real.rpow |z| a + Real.rpow |d| a) := by
    have hPower := Real.rpow_le_rpow (abs_nonneg (z + d)) hTriangle ha
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hM0] at hPower
    exact hPower.trans (mul_le_mul_of_nonneg_left hMaxPow
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) a))
  have hMarkAdd : Real.rpow |z| (3 + a) = |z| ^ 3 * Real.rpow |z| a := by
    change (|z| : ℝ) ^ ((3 : ℝ) + a) = |z| ^ 3 * (|z| : ℝ) ^ a
    rw [Real.rpow_add_of_nonneg (abs_nonneg z) (by norm_num : (0 : ℝ) ≤ 3) ha]
    exact congrArg (fun t : ℝ => t * Real.rpow |z| a) (Real.rpow_natCast |z| 3)
  have hMarkedPolynomial : |z| ^ 3 * Real.rpow |z + d| a ≤
      Real.rpow 2 a * (Real.rpow |z| (3 + a) + |z| ^ 3 * Real.rpow |d| a) := by
    calc
      _ ≤ |z| ^ 3 * (Real.rpow 2 a * (Real.rpow |z| a + Real.rpow |d| a)) :=
        mul_le_mul_of_nonneg_left hPolynomial (pow_nonneg (abs_nonneg z) 3)
      _ = _ := by rw [hMarkAdd]; ring
  have hConsEnergy : Shao.energy (Fin.cons z w) = z ^ 2 + Shao.energy w := by
    simp only [Shao.energy, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  have hRemainingWeight : 0 ≤ A.indicator (fun u => Real.exp (-s * Shao.energy u)) w := by
    by_cases ha : w ∈ A
    · rw [Set.indicator_of_mem ha]
      exact (Real.exp_pos _).le
    · simp only [Set.indicator_of_notMem ha, le_refl]
  by_cases hb : Fin.cons z w ∈ B
  · by_cases hE0 : Shao.energy (Fin.cons z w) = 0
    · have hz : z = 0 := by
        simpa only [Fin.cons_zero] using
          (Shao.energy_eq_zero_iff (Fin.cons z w)).mp hE0 0
      rw [Set.indicator_of_mem hb]
      simp [F, hz, Real.zero_rpow (by linarith : (3 : ℝ) + a ≠ 0)]
    · have hPositive : 0 < Shao.energy (Fin.cons z w) :=
        lt_of_le_of_ne (Shao.energy_nonneg _) (Ne.symm hE0)
      have hCross := hb
      change (3 / 2 : ℝ) * x * Real.sqrt (Shao.energy (Fin.cons z w)) ≤
        |Shao.prefixSum (Fin.cons z w) (n + 1)| at hCross
      rw [hConsEnergy, Shao.OQ4.prefixSum_cons] at hCross
      have ha : w ∈ A :=
        Shao.C2.AuxiliaryMarkedDeletion.auxiliary_marked_terminal_deletion w z x hx
          (by simpa only [hConsEnergy] using hPositive) hCross
      rw [Set.indicator_of_mem hb]
      change |z| ^ 3 * Real.rpow |Shao.prefixSum (Fin.cons z w) (n + 1)| a *
        Real.exp (-s * Shao.energy (Fin.cons z w)) ≤ _
      rw [Shao.OQ4.prefixSum_cons, hConsEnergy, mul_add, Real.exp_add,
        Set.indicator_of_mem ha]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hMarkedPolynomial
        (mul_nonneg (Real.exp_pos (-s * z ^ 2)).le
          (Real.exp_pos (-s * Shao.energy w)).le)
  · rw [Set.indicator_of_notMem hb]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) a)
          (add_nonneg (Real.rpow_nonneg (abs_nonneg z) (3 + a))
            (mul_nonneg (pow_nonneg (abs_nonneg z) 3)
              (Real.rpow_nonneg (abs_nonneg (Shao.prefixSum w n)) a))))
        (Real.exp_pos _).le) hRemainingWeight

end Shao.C2.AuxiliaryMarkedRareRealSplit
