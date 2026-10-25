import Shao.Probability.GaussianTail

set_option autoImplicit false

namespace Shao.C2.UniformGaussianTailPolynomial

theorem standardNormalTail_cubic_uniform_bound (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ 3 * Shao.standardNormalTail x ≤
      (16 / 3 : ℝ) * (Real.sqrt (2 * Real.pi))⁻¹ := by
  have hpos : 0 < 1 + x := by linarith
  have hc : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  have hdensity : Shao.standardNormalDensity x =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
    simp [Shao.standardNormalDensity, ProbabilityTheory.gaussianPDFReal]
  have hexp : Real.exp (x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) = 1 := by
    rw [← Real.exp_add, show x ^ 2 / 2 + -x ^ 2 / 2 = 0 by ring, Real.exp_zero]
  have hlinear : (1 + x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (x ^ 2 / 2))
      (Real.exp_nonneg (-x ^ 2 / 2))
    rw [hexp] at h
    nlinarith only [h]
  have hquadratic : (1 + x) ^ 2 ≤ 2 * (1 + x ^ 2) := by
    nlinarith only [sq_nonneg (x - 1)]
  have hpoly : (1 + x) ^ 2 * Real.exp (-x ^ 2 / 2) ≤ 4 := by
    have h := mul_le_mul_of_nonneg_right hquadratic (Real.exp_nonneg (-x ^ 2 / 2))
    nlinarith only [h, hlinear, Real.exp_nonneg (-x ^ 2 / 2)]
  have hm := (le_div_iff₀ hpos).mp (Shao.standardNormal_mills_bounds x hx).2.1
  rw [hdensity] at hm
  calc
    (1 + x) ^ 3 * Shao.standardNormalTail x =
        (1 + x) ^ 2 * (Shao.standardNormalTail x * (1 + x)) := by ring
    _ ≤ (1 + x) ^ 2 * ((4 / 3 : ℝ) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2))) :=
      mul_le_mul_of_nonneg_left hm (sq_nonneg (1 + x))
    _ = ((4 / 3 : ℝ) * (Real.sqrt (2 * Real.pi))⁻¹) *
        ((1 + x) ^ 2 * Real.exp (-x ^ 2 / 2)) := by ring
    _ ≤ ((4 / 3 : ℝ) * (Real.sqrt (2 * Real.pi))⁻¹) * 4 :=
      mul_le_mul_of_nonneg_left hpoly (mul_nonneg (by norm_num) hc)
    _ = (16 / 3 : ℝ) * (Real.sqrt (2 * Real.pi))⁻¹ := by ring

end Shao.C2.UniformGaussianTailPolynomial
