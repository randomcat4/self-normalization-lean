import Shao.OQ3.ScalarCharacteristicQuadraticRemainder
import Mathlib.Probability.Moments.Covariance

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
noncomputable section

theorem pair_linear_projection_abs_le_euclidean (u v a b : ℝ) :
    |u * a + v * b| ≤
      Real.sqrt (u ^ 2 + v ^ 2) * Real.sqrt (a ^ 2 + b ^ 2) := by
  have hsq : (u * a + v * b) ^ 2 ≤
      (Real.sqrt (u ^ 2 + v ^ 2) * Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg (u * b - v * a)]
  exact abs_le_of_sq_le_sq hsq
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem pair_probability_characteristic_quadratic_remainder_bound
    (law : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure law]
    (hL2 : ∀ i : Fin 2, MemLp (fun y : Fin 2 → ℝ => y i) 2 law)
    (hmean : ∀ i : Fin 2, (∫ y : Fin 2 → ℝ, y i ∂law) = 0)
    (hcov : ∀ i j : Fin 2, ProbabilityTheory.covariance
      (fun y : Fin 2 → ℝ => y i) (fun y : Fin 2 → ℝ => y j) law =
        if i = j then 1 else 0)
    (hthird : Integrable (fun y : Fin 2 → ℝ =>
      (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 3) law) (u v : ℝ) :
    ‖(∫ y : Fin 2 → ℝ,
      Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂law) -
        (1 - ((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2)‖ ≤
      (Real.exp 1 + 4) * (Real.sqrt (u ^ 2 + v ^ 2)) ^ 3 *
        (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 3 ∂law) := by
  let X : (Fin 2 → ℝ) → ℝ := fun y => u * y 0 + v * y 1
  let nu : Measure ℝ := law.map X
  let r : ℝ := Real.sqrt (u ^ 2 + v ^ 2)
  have hX : Continuous X := by dsimp [X]; fun_prop
  have hnu : IsProbabilityMeasure nu :=
    (Measure.isProbabilityMeasure_map_iff hX.measurable.aemeasurable).mpr inferInstance
  letI : IsProbabilityMeasure nu := hnu
  have hI : ∀ i : Fin 2, Integrable (fun y : Fin 2 → ℝ => y i) law := by
    intro i
    exact MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) (hL2 i)
  have hprod : ∀ i j : Fin 2,
      Integrable (fun y : Fin 2 → ℝ => y i * y j) law := by
    intro i j
    exact ((hL2 i).integrable_mul (hL2 j)).congr
      (Filter.Eventually.of_forall (fun y => by rfl))
  have hraw : ∀ i j : Fin 2,
      (∫ y : Fin 2 → ℝ, y i * y j ∂law) = if i = j then 1 else 0 := by
    intro i j
    simpa only [ProbabilityTheory.covariance, hmean, sub_zero] using hcov i j
  have hXI : Integrable X law := (hI 0).const_mul u |>.add ((hI 1).const_mul v)
  have hsquare : (fun y : Fin 2 → ℝ => (X y) ^ 2) =
      (fun y => u ^ 2 * (y 0 * y 0) + (2 * u * v) * (y 0 * y 1) +
        v ^ 2 * (y 1 * y 1)) := by
    funext y
    dsimp [X]
    ring
  have hX2 : Integrable (fun y : Fin 2 → ℝ => (X y) ^ 2) law := by
    rw [hsquare]
    exact (((hprod 0 0).const_mul (u ^ 2)).add
      ((hprod 0 1).const_mul (2 * u * v))).add ((hprod 1 1).const_mul (v ^ 2))
  have hXmean : (∫ y : Fin 2 → ℝ, X y ∂law) = 0 := by
    change (∫ y : Fin 2 → ℝ, u * y 0 + v * y 1 ∂law) = 0
    rw [integral_add ((hI 0).const_mul u) ((hI 1).const_mul v),
      integral_const_mul, integral_const_mul, hmean 0, hmean 1]
    ring
  have hXsecond : (∫ y : Fin 2 → ℝ, (X y) ^ 2 ∂law) = u ^ 2 + v ^ 2 := by
    have hab : Integrable (fun y : Fin 2 → ℝ =>
        u ^ 2 * (y 0 * y 0) + (2 * u * v) * (y 0 * y 1)) law :=
      ((hprod 0 0).const_mul (u ^ 2)).add ((hprod 0 1).const_mul (2 * u * v))
    have hc : Integrable (fun y : Fin 2 → ℝ =>
        v ^ 2 * (y 1 * y 1)) law := (hprod 1 1).const_mul (v ^ 2)
    rw [hsquare, integral_add hab hc,
      integral_add (f := fun y : Fin 2 → ℝ => u ^ 2 * (y 0 * y 0))
        (g := fun y : Fin 2 → ℝ => (2 * u * v) * (y 0 * y 1))
        ((hprod 0 0).const_mul (u ^ 2)) ((hprod 0 1).const_mul (2 * u * v)),
      integral_const_mul, integral_const_mul, integral_const_mul,
      hraw 0 0, hraw 0 1, hraw 1 1]
    norm_num
  have hthirdpoint : ∀ y : Fin 2 → ℝ, |X y| ^ 3 ≤
      r ^ 3 * (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 3 := by
    intro y
    have h := pow_le_pow_left₀ (abs_nonneg (X y))
      (pair_linear_projection_abs_le_euclidean u v (y 0) (y 1)) 3
    simpa only [mul_pow, X, r] using h
  have hX3 : Integrable (fun y : Fin 2 → ℝ => |X y| ^ 3) law :=
    (hthird.const_mul (r ^ 3)).mono' (by dsimp [X]; fun_prop)
      (Filter.Eventually.of_forall (fun y => by
        simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using hthirdpoint y))
  have hn1 : Integrable (fun x : ℝ => x) nu := by
    exact (integrable_map_measure (μ := law)
      (show AEStronglyMeasurable (fun x : ℝ => x) (law.map X) from
        continuous_id.aestronglyMeasurable) hX.measurable.aemeasurable).2 hXI
  have hn2 : Integrable (fun x : ℝ => x ^ 2) nu := by
    exact (integrable_map_measure (μ := law)
      (show AEStronglyMeasurable (fun x : ℝ => x ^ 2) (law.map X) from
        (show Continuous (fun x : ℝ => x ^ 2) by fun_prop).aestronglyMeasurable)
          hX.measurable.aemeasurable).2 hX2
  have hn3 : Integrable (fun x : ℝ => |x| ^ 3) nu := by
    exact (integrable_map_measure (μ := law)
      (show AEStronglyMeasurable (fun x : ℝ => |x| ^ 3) (law.map X) from
        (show Continuous (fun x : ℝ => |x| ^ 3) by fun_prop).aestronglyMeasurable)
          hX.measurable.aemeasurable).2 hX3
  have hnmean : (∫ x : ℝ, x ∂nu) = 0 := by
    change (∫ x : ℝ, x ∂law.map X) = 0
    exact (MeasureTheory.integral_map (μ := law) hX.measurable.aemeasurable
      (show AEStronglyMeasurable (fun x : ℝ => x) (law.map X) from
        continuous_id.aestronglyMeasurable)).trans hXmean
  have hnsecond : (∫ x : ℝ, x ^ 2 ∂nu) = u ^ 2 + v ^ 2 := by
    change (∫ x : ℝ, x ^ 2 ∂law.map X) = u ^ 2 + v ^ 2
    rw [MeasureTheory.integral_map (μ := law) hX.measurable.aemeasurable
      (show Continuous (fun x : ℝ => x ^ 2) by fun_prop).aestronglyMeasurable]
    exact hXsecond
  have hnthird : (∫ x : ℝ, |x| ^ 3 ∂nu) ≤
      r ^ 3 * (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 3 ∂law) := by
    change (∫ x : ℝ, |x| ^ 3 ∂law.map X) ≤ _
    rw [MeasureTheory.integral_map (μ := law) hX.measurable.aemeasurable
      (show Continuous (fun x : ℝ => |x| ^ 3) by fun_prop).aestronglyMeasurable]
    exact (integral_mono hX3 (hthird.const_mul (r ^ 3)) hthirdpoint).trans_eq
      (integral_const_mul _ _)
  have hcf : (∫ x : ℝ, Complex.exp ((x : ℂ) * Complex.I) ∂nu) =
      ∫ y : Fin 2 → ℝ,
        Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂law := by
    change (∫ x : ℝ, Complex.exp ((x : ℂ) * Complex.I) ∂law.map X) = _
    exact MeasureTheory.integral_map (μ := law) hX.measurable.aemeasurable
      (show Continuous (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) by
        fun_prop).aestronglyMeasurable
  have hq := probability_characteristic_quadratic_remainder_bound
    nu hn1 hn2 hn3 hnmean 1
  simp only [one_mul, Complex.ofReal_one, one_pow, abs_one, mul_one, hnsecond] at hq
  rw [hcf] at hq
  refine hq.trans ?_
  have hK : 0 ≤ Real.exp 1 + 4 := by positivity
  simpa only [mul_assoc, r] using mul_le_mul_of_nonneg_left hnthird hK

end
end Shao.OQ3
