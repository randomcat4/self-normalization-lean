import Shao.C2.AuxiliaryMarkedDeletion
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.C2.AuxiliarySourceCutoffPayment

theorem auxiliary_original_cutoff_rank_payment
    (beta L rhoStar K s x : ℝ) (hBeta : 1 ≤ beta) (hL : 0 ≤ L)
    (hRho : 0 < rhoStar) (hs : 0 ≤ s) (hx : 1 ≤ x)
    (hKDrift : 8000000 * (1 + L) ^ 2 ≤ K)
    (hKBudget : 2 * (768 / rhoStar) ^ 2 ≤ K)
    (t n : ℕ)
    (hCutoff : Nat.ceil (K * beta ^ 2 * (1 + x) ^ 6) ≤ t)
    (hLength : n = t ∨ n = t - 1)
    (hTime : s * (t : ℝ) ≤ L * x ^ 2) :
    4 ≤ Nat.ceil (K * beta ^ 2 * (1 + x) ^ 6) ∧
      0 < n ∧ (t : ℝ) / 2 ≤ (n : ℝ) ∧
      s * (n : ℝ) ≤ L * x ^ 2 ∧
      4000000 * (1 + L) ^ 2 * beta ^ 2 * (1 + x) ^ 6 ≤ (n : ℝ) ∧
      (768 / rhoStar) ^ 2 * beta ^ 2 * (1 + x) ^ 6 ≤ (n : ℝ) := by
  let H : ℝ := K * beta ^ 2 * (1 + x) ^ 6
  let M : ℝ := beta ^ 2 * (1 + x) ^ 6
  have hBeta2 : 1 ≤ beta ^ 2 := by nlinarith
  have hPow : 1 ≤ (1 + x) ^ 6 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (show 1 ≤ 1 + x by linarith) 6
    simpa only [one_pow] using hh
  have hM : 1 ≤ M := by
    have hh := mul_nonneg (sq_nonneg beta) (sub_nonneg.mpr hPow)
    dsimp [M]
    nlinarith
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hK : 8000000 ≤ K := by nlinarith [sq_nonneg L]
  have hKM : K ≤ H := by
    have hh := mul_nonneg (show 0 ≤ K by linarith) (sub_nonneg.mpr hM)
    dsimp [H, M] at hh ⊢
    nlinarith
  have hH4 : 4 ≤ H := by linarith
  have hCeil : H ≤ (Nat.ceil H : ℝ) := Nat.le_ceil H
  have hm4 : 4 ≤ Nat.ceil H := by exact_mod_cast hH4.trans hCeil
  have hT4 : 4 ≤ t := hm4.trans hCutoff
  have hT1 : 1 ≤ t := (by norm_num : 1 ≤ 4).trans hT4
  have hTReal4 : (4 : ℝ) ≤ t := by exact_mod_cast hT4
  have hHt : H ≤ (t : ℝ) := Nat.ceil_le.mp hCutoff
  have hNLower : (t : ℝ) / 2 ≤ (n : ℝ) := by
    rcases hLength with rfl | rfl
    · nlinarith
    · rw [Nat.cast_sub hT1, Nat.cast_one]
      linarith
  have hNLe : n ≤ t := by
    rcases hLength with rfl | rfl
    · exact le_rfl
    · exact Nat.sub_le t 1
  have hNLeReal : (n : ℝ) ≤ t := by exact_mod_cast hNLe
  have hn : 0 < n := by
    have hh : (0 : ℝ) < n := by linarith
    exact_mod_cast hh
  have hTimeN : s * (n : ℝ) ≤ L * x ^ 2 :=
    (mul_le_mul_of_nonneg_left hNLeReal hs).trans hTime
  have hDriftPay : 4000000 * (1 + L) ^ 2 * beta ^ 2 * (1 + x) ^ 6 ≤ (n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hKDrift hM0
    dsimp [M] at hh
    dsimp [H] at hHt
    nlinarith
  have hBudgetPay : (768 / rhoStar) ^ 2 * beta ^ 2 * (1 + x) ^ 6 ≤ (n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hKBudget hM0
    dsimp [M] at hh
    dsimp [H] at hHt
    nlinarith
  exact ⟨hm4, hn, hNLower, hTimeN, hDriftPay, hBudgetPay⟩

end Shao.C2.AuxiliarySourceCutoffPayment
