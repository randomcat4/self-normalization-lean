import Shao.C2.AuxiliaryMarkedDeletion
import Shao.OQ4.KilledPathLaw

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryMarkedRareSplit
open MeasureTheory ProbabilityTheory

theorem auxiliary_actual_marked_rare_polynomial_split
    {n : ℕ} (w : Shao.Path n) (z x s : ℝ) (p : ℕ) (hx : 1 ≤ x) :
    let B : Set (Shao.Path (n + 1)) := {v |
      ((3 / 2) * x) * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v (n + 1)|}
    let A : Set (Shao.Path n) := {u | 0 < Shao.energy u ∧
      Real.sqrt ((9 / 4) * x ^ 2 - 1) * Real.sqrt (Shao.energy u) ≤
        |Shao.prefixSum u n|}
    let F : Shao.Path (n + 1) → ℝ := fun v =>
      |v 0| ^ 3 * |Shao.prefixSum v (n + 1)| ^ p * Real.exp (-s * Shao.energy v)
    B.indicator F (Fin.cons z w) ≤
      (2 : ℝ) ^ p * (|z| ^ (3 + p) + |z| ^ 3 * |Shao.prefixSum w n| ^ p) *
        Real.exp (-s * z ^ 2) *
        A.indicator (fun u => Real.exp (-s * Shao.energy u)) w := by
  classical
  intro B A F
  let d : ℝ := Shao.prefixSum w n
  let M : ℝ := max |z| |d|
  have hMaxPow : M ^ p ≤ |z| ^ p + |d| ^ p := by
    rcases le_total |z| |d| with h | h
    · dsimp [M]
      rw [max_eq_right h]
      linarith [pow_nonneg (abs_nonneg z) p]
    · dsimp [M]
      rw [max_eq_left h]
      linarith [pow_nonneg (abs_nonneg d) p]
  have hTriangle : |z + d| ≤ 2 * M := (abs_add_le z d).trans (by
    dsimp [M]
    linarith [le_max_left |z| |d|, le_max_right |z| |d|])
  have hPolynomial : |z + d| ^ p ≤ (2 : ℝ) ^ p * (|z| ^ p + |d| ^ p) := by
    have hPower := pow_le_pow_left₀ (abs_nonneg (z + d)) hTriangle p
    rw [mul_pow] at hPower
    exact hPower.trans (mul_le_mul_of_nonneg_left hMaxPow (pow_nonneg (by norm_num) p))
  have hMarkedPolynomial : |z| ^ 3 * |z + d| ^ p ≤
      (2 : ℝ) ^ p * (|z| ^ (3 + p) + |z| ^ 3 * |d| ^ p) := by
    calc
      _ ≤ |z| ^ 3 * ((2 : ℝ) ^ p * (|z| ^ p + |d| ^ p)) :=
        mul_le_mul_of_nonneg_left hPolynomial (pow_nonneg (abs_nonneg z) 3)
      _ = _ := by rw [pow_add]; ring
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
      simp [F, hz]
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
      change |z| ^ 3 * |Shao.prefixSum (Fin.cons z w) (n + 1)| ^ p *
        Real.exp (-s * Shao.energy (Fin.cons z w)) ≤ _
      rw [Shao.OQ4.prefixSum_cons, hConsEnergy, mul_add, Real.exp_add,
        Set.indicator_of_mem ha]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hMarkedPolynomial
        (mul_nonneg (Real.exp_pos (-s * z ^ 2)).le
          (Real.exp_pos (-s * Shao.energy w)).le)
  · rw [Set.indicator_of_notMem hb]
    exact mul_nonneg (by positivity) hRemainingWeight

end Shao.C2.AuxiliaryMarkedRareSplit
