import Shao.C2.AuxiliarySourceGaussian

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.C2.AuxiliaryMarkedDeletion

theorem auxiliary_marked_terminal_deletion
    {n : ℕ} (w : Shao.Path n) (v x : ℝ) (hx : 1 ≤ x)
    (hFull : 0 < v ^ 2 + Shao.energy w)
    (hCross : (3 / 2 : ℝ) * x * Real.sqrt (v ^ 2 + Shao.energy w) ≤
      |v + Shao.prefixSum w n|) :
    0 < Shao.energy w ∧
      Real.sqrt ((9 / 4) * x ^ 2 - 1) * Real.sqrt (Shao.energy w) ≤
        |Shao.prefixSum w n| := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hT0 : 0 ≤ Shao.energy w := Shao.energy_nonneg w
  have hT : 0 < Shao.energy w := by
    by_contra hNot
    have hZero : Shao.energy w = 0 := le_antisymm (le_of_not_gt hNot) hT0
    have hSumZero : Shao.prefixSum w n = 0 :=
      Shao.prefixSum_eq_zero_of_energy_eq_zero w hZero n
    have hVne : v ≠ 0 := by
      intro hv
      simp only [hv, hZero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, lt_self_iff_false] at hFull
    have hAbs : 0 < |v| := abs_pos.mpr hVne
    rw [hZero, hSumZero, add_zero, add_zero, Real.sqrt_sq_eq_abs] at hCross
    have hScale := mul_le_mul_of_nonneg_right hx (abs_nonneg v)
    nlinarith
  have hRad : 0 ≤ (9 / 4 : ℝ) * x ^ 2 - 1 := by
    nlinarith [sq_nonneg (x - 1)]
  have hSquared := pow_le_pow_left₀
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) hx0)
      (Real.sqrt_nonneg _)) hCross 2
  rw [mul_pow, Real.sq_sqrt hFull.le, sq_abs] at hSquared
  have hCauchy : Shao.energy w * (v + Shao.prefixSum w n) ^ 2 ≤
      (v ^ 2 + Shao.energy w) * (Shao.energy w + (Shao.prefixSum w n) ^ 2) := by
    nlinarith [sq_nonneg (v * Shao.prefixSum w n - Shao.energy w)]
  have hWeighted := mul_le_mul_of_nonneg_left hSquared hT0
  have hCancel : (9 / 4 : ℝ) * x ^ 2 * Shao.energy w ≤
      Shao.energy w + (Shao.prefixSum w n) ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right hFull).1
    nlinarith
  refine ⟨hT, ?_⟩
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (abs_nonneg _)).1
  rw [mul_pow, Real.sq_sqrt hRad, Real.sq_sqrt hT0, sq_abs]
  nlinarith

end Shao.C2.AuxiliaryMarkedDeletion
