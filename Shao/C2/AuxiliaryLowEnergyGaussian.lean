import Shao.C2.AuxiliaryTiltedProductEnergy
import Shao.Probability.GaussianTail

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.C2.AuxiliaryLowEnergyGaussian
open MeasureTheory ProbabilityTheory

theorem auxiliary_exponential_le_gaussian_tail
    (y A : ℝ) (hy : 0 ≤ y) (hA : y + y ^ 2 / 2 ≤ A) :
    Real.exp (-A) ≤ (8 / 3 : ℝ) * Shao.standardNormalTail y := by
  have hTail : 0 < Shao.standardNormalTail y := (Shao.standardNormalTail_basic.2.2.1 y).1
  have hRatio : (1 / 2 : ℝ) ≤
      (4 / 3 : ℝ) * (1 + y) * Real.exp (y ^ 2 / 2) * Shao.standardNormalTail y := by
    have hh := Shao.standardNormalTail_ratio_bound y 0 hy (by norm_num)
    simpa only [Shao.standardNormalTail_basic.2.1, add_zero, div_one, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
      using hh
  have hExp : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hRatioExp : (1 / 2 : ℝ) ≤
      (4 / 3 : ℝ) * Real.exp (y + y ^ 2 / 2) * Shao.standardNormalTail y := by
    rw [Real.exp_add]
    have hCoeff0 : 0 ≤ (4 / 3 : ℝ) * Real.exp (y ^ 2 / 2) * Shao.standardNormalTail y := by
      positivity
    have hh := mul_le_mul_of_nonneg_left hExp hCoeff0
    nlinarith
  have hMul := mul_le_mul_of_nonneg_right hRatioExp (Real.exp_pos (-A)).le
  have hExpProd : Real.exp (y + y ^ 2 / 2) * Real.exp (-A) =
      Real.exp (y + y ^ 2 / 2 - A) := by
    rw [← Real.exp_add]
    congr 1
  have hExpBound : Real.exp (y + y ^ 2 / 2 - A) ≤ 1 :=
    Real.exp_le_one_iff.mpr (sub_nonpos.mpr hA)
  have hRHS : ((4 / 3 : ℝ) * Real.exp (y + y ^ 2 / 2) * Shao.standardNormalTail y) *
      Real.exp (-A) ≤ (4 / 3 : ℝ) * Shao.standardNormalTail y := by
    calc
      _ = (4 / 3 : ℝ) * (Real.exp (y + y ^ 2 / 2) * Real.exp (-A)) *
          Shao.standardNormalTail y := by ring
      _ = (4 / 3 : ℝ) * Real.exp (y + y ^ 2 / 2 - A) * Shao.standardNormalTail y := by
        rw [hExpProd]
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hExpBound
          (show 0 ≤ (4 / 3 : ℝ) * Shao.standardNormalTail y by positivity)
        nlinarith
  nlinarith

theorem auxiliary_tilted_low_energy_gaussian
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (s : ℝ) (hs : 0 ≤ s)
    (hsBound : s ≤ 1 / (128 * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2))
    (n : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hRank : 1024 * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 * (1 + x) ^ 6 ≤ (n : ℝ)) :
    let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
    P.real {v : Shao.Path n | Shao.energy v ≤ (n : ℝ) / 8} ≤
      (8 / 3 : ℝ) * Shao.standardNormalTail ((3 / 2) * x) := by
  intro rho P
  let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
  have hBeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one nu h2 h3 hnorm
  have hBetaPos : 0 < beta := lt_of_lt_of_le zero_lt_one hBeta
  have hDen : 0 < 1024 * beta ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hBetaPos)
  change 1024 * beta ^ 2 * (1 + x) ^ 6 ≤ (n : ℝ) at hRank
  have hPower : 5 * (1 + x) ^ 6 ≤ 5 * (n : ℝ) / (1024 * beta ^ 2) := by
    apply (le_div_iff₀ hDen).2
    have hh := mul_le_mul_of_nonneg_left hRank (show 0 ≤ (5 : ℝ) by norm_num)
    nlinarith
  have hPolynomial : (3 / 2 : ℝ) * x + ((3 / 2 : ℝ) * x) ^ 2 / 2 ≤
      5 * (1 + x) ^ 6 := by
    nlinarith [sq_nonneg x, pow_nonneg hx 3, pow_nonneg hx 4,
      pow_nonneg hx 5, pow_nonneg hx 6]
  have hTail := Shao.C2.AuxiliaryTiltedProductEnergy.auxiliary_tilted_source_low_energy
    nu h2 h3 hmean hnorm s hs hsBound n
  exact hTail.2.2.trans (auxiliary_exponential_le_gaussian_tail
    ((3 / 2) * x) (5 * (n : ℝ) / (1024 * beta ^ 2))
    (mul_nonneg (by norm_num) hx) (hPolynomial.trans hPower))

end Shao.C2.AuxiliaryLowEnergyGaussian
