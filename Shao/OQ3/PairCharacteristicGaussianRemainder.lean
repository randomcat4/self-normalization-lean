import Shao.OQ3.PairCharacteristicQuadraticRemainder

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
noncomputable section

theorem real_gaussian_quadratic_remainder_bound (u v : ℝ)
    (hr : Real.sqrt (u ^ 2 + v ^ 2) ≤ 1) :
    ‖((Real.exp (-(u ^ 2 + v ^ 2) / 2) : ℝ) : ℂ) -
      (1 - ((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2)‖ ≤
        Real.exp 1 * (Real.sqrt (u ^ 2 + v ^ 2)) ^ 3 := by
  let r : ℝ := Real.sqrt (u ^ 2 + v ^ 2)
  let q : ℝ := u ^ 2 + v ^ 2
  let z : ℂ := -((q : ℝ) : ℂ) / 2
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = q := Real.sq_sqrt (by positivity)
  have hr2 : r ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr)]
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hz : ‖z‖ = r ^ 2 / 2 := by
    dsimp [z]
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hq0]
    norm_num
    rw [hrsq]
  have hz1 : ‖z‖ ≤ 1 := by rw [hz]; linarith
  have hpow : ‖z‖ ^ 2 ≤ r ^ 3 := by
    rw [hz]
    calc
      (r ^ 2 / 2) ^ 2 = r ^ 3 * (r / 4) := by ring
      _ ≤ r ^ 3 * 1 := mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hr0 3)
      _ = r ^ 3 := mul_one _
  have hsum : (∑ m ∈ Finset.range 2, z ^ m / (m.factorial : ℂ)) = 1 + z := by
    norm_num [Finset.sum_range_succ]
  have hrem := Complex.norm_exp_sub_sum_le_norm_mul_exp z 2
  rw [hsum] at hrem
  have hexpz : Complex.exp z = ((Real.exp (-q / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    dsimp [z]
    push_cast
    ring
  have hpoly : 1 + z = 1 - ((q : ℝ) : ℂ) / 2 := by dsimp [z]; ring
  calc
    ‖((Real.exp (-(u ^ 2 + v ^ 2) / 2) : ℝ) : ℂ) -
        (1 - ((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2)‖ =
        ‖Complex.exp z - (1 + z)‖ := by rw [hexpz, hpoly]
    _ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ := hrem
    _ ≤ r ^ 3 * Real.exp 1 :=
      mul_le_mul hpow (Real.exp_le_exp.mpr hz1) (Real.exp_nonneg _)
        (pow_nonneg hr0 3)
    _ = Real.exp 1 * r ^ 3 := mul_comm _ _

theorem pair_probability_characteristic_gaussian_remainder_bound
    (law : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure law]
    (hL2 : ∀ i : Fin 2, MemLp (fun y : Fin 2 → ℝ => y i) 2 law)
    (hmean : ∀ i : Fin 2, (∫ y : Fin 2 → ℝ, y i ∂law) = 0)
    (hcov : ∀ i j : Fin 2, ProbabilityTheory.covariance
      (fun y : Fin 2 → ℝ => y i) (fun y : Fin 2 → ℝ => y j) law =
        if i = j then 1 else 0)
    (hthird : Integrable (fun y : Fin 2 → ℝ =>
      (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 3) law)
    (u v : ℝ) (hr : Real.sqrt (u ^ 2 + v ^ 2) ≤ 1) :
    ‖(∫ y : Fin 2 → ℝ,
      Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂law) -
        ((Real.exp (-(u ^ 2 + v ^ 2) / 2) : ℝ) : ℂ)‖ ≤
      ((Real.exp 1 + 4) *
        (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 3 ∂law) +
          Real.exp 1) * (Real.sqrt (u ^ 2 + v ^ 2)) ^ 3 := by
  let z : ℂ := ∫ y : Fin 2 → ℝ,
    Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂law
  let P : ℂ := 1 - ((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2
  let G : ℂ := ((Real.exp (-(u ^ 2 + v ^ 2) / 2) : ℝ) : ℂ)
  have hactual := pair_probability_characteristic_quadratic_remainder_bound
    law hL2 hmean hcov hthird u v
  have hgauss := real_gaussian_quadratic_remainder_bound u v hr
  calc
    ‖z - G‖ = ‖(z - P) + (P - G)‖ := by congr 1; ring
    _ ≤ ‖z - P‖ + ‖P - G‖ := norm_add_le _ _
    _ = ‖z - P‖ + ‖G - P‖ := by rw [norm_sub_rev P G]
    _ ≤ (Real.exp 1 + 4) * (Real.sqrt (u ^ 2 + v ^ 2)) ^ 3 *
        (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 3 ∂law) +
          Real.exp 1 * (Real.sqrt (u ^ 2 + v ^ 2)) ^ 3 :=
      add_le_add hactual hgauss
    _ = _ := by ring

end
end Shao.OQ3
