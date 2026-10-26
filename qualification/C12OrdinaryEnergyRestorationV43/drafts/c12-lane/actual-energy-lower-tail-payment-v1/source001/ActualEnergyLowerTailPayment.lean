import Shao.C2.AuxiliaryLowEnergyGaussian
import Shao.Probability.QuadraticEnergyLowerTail

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
noncomputable section
namespace Shao.C2.ActualEnergyLowerTailPayment
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

theorem own_cubic_small_energy_exponential_payment
    (delta x : ℝ) (hdelta : 0 < delta) (hx : 0 ≤ x)
    (hsmall : delta * (1 + x) ^ 3 ≤ 1 / 16) :
    Real.exp (-(1 / (64 * delta ^ 2))) ≤
      32 * delta * (1 + x) ^ 3 * Shao.standardNormalTail x := by
  let A : ℝ := 1 / (128 * delta ^ 2)
  have hApos : 0 < A := by dsimp only [A]; positivity
  have hCubeOne : (1 : ℝ) ≤ (1 + x) ^ 3 := by
    nlinarith only [hx, sq_nonneg x, pow_nonneg hx 3]
  have hLinearCube : 1 + x ≤ (1 + x) ^ 3 := by
    nlinarith only [hx, sq_nonneg x, pow_nonneg hx 3]
  have hDeltaWeight : delta ≤ delta * (1 + x) ^ 3 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hCubeOne hdelta.le
  have hDeltaSmall : delta ≤ 1 / 16 := hDeltaWeight.trans hsmall
  have hLinearSmall : delta * (1 + x) ≤ 1 / 16 :=
    (mul_le_mul_of_nonneg_left hLinearCube hdelta.le).trans hsmall
  have hLinearSquare : (delta * (1 + x)) ^ 2 ≤ (1 / 16 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hdelta.le (by linarith only [hx])) hLinearSmall 2
  have hShape : x + x ^ 2 / 2 ≤ (1 + x) ^ 2 := by
    nlinarith only [hx, sq_nonneg x]
  have hProduct : (x + x ^ 2 / 2) * (128 * delta ^ 2) ≤ 1 := by
    calc
      (x + x ^ 2 / 2) * (128 * delta ^ 2) ≤
          (1 + x) ^ 2 * (128 * delta ^ 2) :=
        mul_le_mul_of_nonneg_right hShape (by positivity)
      _ ≤ 1 := by nlinarith only [hLinearSquare]
  have hTailExponent : x + x ^ 2 / 2 ≤ A := by
    dsimp only [A]
    exact (le_div_iff₀ (show 0 < 128 * delta ^ 2 by positivity)).mpr hProduct
  have hTail : Real.exp (-A) ≤ (8 / 3 : ℝ) * Shao.standardNormalTail x :=
    Shao.C2.AuxiliaryLowEnergyGaussian.auxiliary_exponential_le_gaussian_tail
      x A hx hTailExponent
  have hExpLower : A ≤ Real.exp A := by linarith only [Real.add_one_le_exp A]
  have hFirst : Real.exp (-A) ≤ 8 * delta := by
    calc
      Real.exp (-A) = 1 / Real.exp A := by rw [Real.exp_neg, one_div]
      _ ≤ 1 / A := one_div_le_one_div_of_le hApos hExpLower
      _ = 128 * delta ^ 2 := by
        dsimp only [A]
        field_simp [hdelta.ne'] <;> ring
      _ ≤ 8 * delta := by
        have hMul := mul_le_mul_of_nonneg_left hDeltaSmall hdelta.le
        nlinarith only [hMul]
  have hSplit : Real.exp (-(1 / (64 * delta ^ 2))) =
      Real.exp (-A) * Real.exp (-A) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [A]
    field_simp [hdelta.ne'] <;> ring
  have hPsi : 0 ≤ Shao.standardNormalTail x :=
    ((Shao.standardNormalTail_basic.2.2.1 x).1).le
  calc
    Real.exp (-(1 / (64 * delta ^ 2))) = Real.exp (-A) * Real.exp (-A) := hSplit
    _ ≤ (8 * delta) * ((8 / 3 : ℝ) * Shao.standardNormalTail x) :=
      mul_le_mul hFirst hTail (Real.exp_pos (-A)).le (by positivity)
    _ = (64 / 3 : ℝ) * (delta * Shao.standardNormalTail x) := by ring
    _ ≤ 32 * (delta * Shao.standardNormalTail x) :=
      mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hdelta.le hPsi)
    _ = 32 * delta * Shao.standardNormalTail x := by ring
    _ ≤ 32 * delta * (1 + x) ^ 3 * Shao.standardNormalTail x := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hDeltaWeight (by norm_num : (0 : ℝ) ≤ 32)) hPsi

theorem iid_actual_energy_lower_tail_gaussian_payment
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (x : ℝ) (hx : 0 ≤ x) :
    let delta : ℝ := (n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂nu)
    delta * (1 + x) ^ 3 ≤ 1 / 16 →
      0 < delta ∧
        (Measure.pi (fun _ : Fin n => nu)).real
            {v : Shao.Path n | Shao.energy v ≤ 1 / 2} ≤
          32 * delta * (1 + x) ^ 3 * Shao.standardNormalTail x := by
  intro delta hsmall
  rcases Shao.Probability.finite_iid_energy_lower_tail nu n hn h2 h3 hnorm
      (1 / 2) (by norm_num) (by norm_num) with ⟨hdelta, hTail⟩
  change 0 < delta at hdelta
  change (Measure.pi (fun _ : Fin n => nu)).real
      {v : Shao.Path n | Shao.energy v ≤ 1 - (1 / 2 : ℝ)} ≤
    Real.exp (-((1 / 2 : ℝ) ^ 3 / (8 * delta ^ 2))) at hTail
  have hFraction : (1 / 2 : ℝ) ^ 3 / (8 * delta ^ 2) = 1 / (64 * delta ^ 2) := by
    field_simp [hdelta.ne'] <;> ring
  have hTail' : (Measure.pi (fun _ : Fin n => nu)).real
      {v : Shao.Path n | Shao.energy v ≤ 1 / 2} ≤
    Real.exp (-(1 / (64 * delta ^ 2))) := by
    simpa only [hFraction, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using hTail
  exact ⟨hdelta, hTail'.trans
    (own_cubic_small_energy_exponential_payment delta x hdelta hx hsmall)⟩

end Shao.C2.ActualEnergyLowerTailPayment
