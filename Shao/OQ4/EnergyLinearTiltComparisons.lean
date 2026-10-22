import Shao.OQ4.EnergyLinearTiltLaw

/-! Finite raw and normalized comparisons for the same actual linear energy tilt. -/

namespace Shao.OQ4

open MeasureTheory

/-- A global scalar estimate, used below only on the actual energy-law full support set. -/
theorem energyLinearComparison_abs_exp_sub_one (y : ℝ) :
    |Real.exp y - 1| ≤ Real.exp |y| * |y| := by
  by_cases hy : 0 ≤ y
  · have he : 1 ≤ Real.exp y := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hy
    have hm : (-y + 1) * Real.exp y ≤ 1 := by
      calc
        _ ≤ Real.exp (-y) * Real.exp y :=
          mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-y)) (Real.exp_nonneg _)
        _ = 1 := by rw [← Real.exp_add]; simp
    rw [abs_of_nonneg (sub_nonneg.mpr he), abs_of_nonneg hy]
    nlinarith
  · have hy' : y ≤ 0 := le_of_not_ge hy
    have he : Real.exp y ≤ 1 := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hy'
    have hE : 1 ≤ Real.exp (-y) := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonneg.mpr hy')
    rw [abs_of_nonpos (sub_nonpos.mpr he), abs_of_nonpos hy']
    calc
      _ ≤ -y := by linarith [Real.add_one_le_exp y]
      _ ≤ Real.exp (-y) * -y := by nlinarith

/-- The actual closed-support pointwise bound; no bound on original ν is assumed. -/
theorem energyLinearComparison_exp_sub_one_bound (h t x : ℝ) (hx : |x| ≤ 2 * h) :
    |Real.exp (t * x) - 1| ≤ Real.exp (2 * h * |t|) * |t| * |x| := by
  have ha : |t * x| ≤ 2 * h * |t| := by
    rw [abs_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hx (abs_nonneg t)
  calc
    _ ≤ Real.exp |t * x| * |t * x| := energyLinearComparison_abs_exp_sub_one _
    _ ≤ Real.exp (2 * h * |t|) * |t * x| :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ha) (abs_nonneg _)
    _ = _ := by rw [abs_mul]; ring

section Admissible

variable (ν : Measure ℝ) [IsProbabilityMeasure ν] (T h s : ℝ)
  (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
  (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
  (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)

include hT hh hs hSq hsecond

theorem energyLinearComparison_power_integrable (k : ℕ) (t : ℝ) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (t * x)) (energyTiltedLaw ν h s) := by
  apply (energyLinear_power_exp_integrable ν T h s hT hh hs hSq hsecond k t).mono'
    (show Measurable (fun x : ℝ => x ^ k * Real.exp (t * x)) by fun_prop).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _), le_refl]

/-- Every subtraction below is justified by actual integrability, uniformly in the finite power. -/
theorem energyLinearComparison_power_deviation (k : ℕ) (t : ℝ) :
    |(∫ x : ℝ, x ^ k * Real.exp (t * x) ∂energyTiltedLaw ν h s) -
        (∫ x : ℝ, x ^ k ∂energyTiltedLaw ν h s)| ≤
      Real.exp (2 * h * |t|) * |t| * (∫ x : ℝ, |x| ^ (k + 1) ∂energyTiltedLaw ν h s) := by
  have hi := energyLinearComparison_power_integrable ν T h s hT hh hs hSq hsecond k t
  have hb : Integrable (fun x : ℝ => x ^ k) (energyTiltedLaw ν h s) := by
    simpa only [zero_mul, Real.exp_zero, mul_one] using
      energyLinearComparison_power_integrable ν T h s hT hh hs hSq hsecond k 0
  have hc : Integrable (fun x : ℝ => |x| ^ (k + 1)) (energyTiltedLaw ν h s) := by
    simpa only [zero_mul, Real.exp_zero, mul_one] using
      energyLinear_power_exp_integrable ν T h s hT hh hs hSq hsecond (k + 1) 0
  have hd : Integrable (fun x : ℝ => x ^ k * (Real.exp (t * x) - 1)) (energyTiltedLaw ν h s) := by
    convert hi.sub hb using 1
    ext x
    simp only [Pi.sub_apply]
    ring
  have hlin : (∫ x : ℝ, x ^ k * (Real.exp (t * x) - 1) ∂energyTiltedLaw ν h s) =
      (∫ x : ℝ, x ^ k * Real.exp (t * x) ∂energyTiltedLaw ν h s) -
        (∫ x : ℝ, x ^ k ∂energyTiltedLaw ν h s) := by
    calc
      _ = ∫ x : ℝ, x ^ k * Real.exp (t * x) - x ^ k ∂energyTiltedLaw ν h s := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = _ := integral_sub hi hb
  calc
    _ = |∫ x : ℝ, x ^ k * (Real.exp (t * x) - 1) ∂energyTiltedLaw ν h s| := congrArg abs hlin.symm
    _ ≤ ∫ x : ℝ, |x ^ k * (Real.exp (t * x) - 1)| ∂energyTiltedLaw ν h s := abs_integral_le_integral_abs
    _ ≤ ∫ x : ℝ, (Real.exp (2 * h * |t|) * |t|) * |x| ^ (k + 1) ∂energyTiltedLaw ν h s := by
      apply integral_mono_ae hd.abs (hc.const_mul _)
      filter_upwards [energyTiltedLaw_ae_support ν h s] with x hx
      rw [abs_mul, abs_pow]
      calc
        _ ≤ |x| ^ k * (Real.exp (2 * h * |t|) * |t| * |x|) :=
          mul_le_mul_of_nonneg_left (energyLinearComparison_exp_sub_one_bound h t x hx)
            (pow_nonneg (abs_nonneg x) k)
        _ = _ := by rw [pow_succ]; ring
    _ = _ := integral_const_mul _ _

/-- The four requested raw comparisons of the actual first-leaf numerators. -/
theorem energyLinear_raw_comparisons (t : ℝ) :
    |energyLinearNormalizer ν h s t - 1| ≤
        Real.exp (2 * h * |t|) * |t| * (∫ x : ℝ, |x| ∂energyTiltedLaw ν h s) ∧
    |energyLinearFirstNumerator ν h s t - (∫ x : ℝ, x ∂energyTiltedLaw ν h s)| ≤
        Real.exp (2 * h * |t|) * |t| * (∫ x : ℝ, x ^ 2 ∂energyTiltedLaw ν h s) ∧
    |energyLinearSecondNumerator ν h s t - (∫ x : ℝ, x ^ 2 ∂energyTiltedLaw ν h s)| ≤
        Real.exp (2 * h * |t|) * |t| * (∫ x : ℝ, |x| ^ 3 ∂energyTiltedLaw ν h s) ∧
    (0 ≤ energyLinearThirdNumerator ν h s t ∧ energyLinearThirdNumerator ν h s t ≤
        Real.exp (2 * h * |t|) * (∫ x : ℝ, |x| ^ 3 ∂energyTiltedLaw ν h s)) := by
  have : IsProbabilityMeasure (energyTiltedLaw ν h s) :=
    energyTiltedLaw_isProbabilityMeasure ν T h s hT hh hs hSq hsecond
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [energyLinearNormalizer] using
      energyLinearComparison_power_deviation ν T h s hT hh hs hSq hsecond 0 t
  · simpa [energyLinearFirstNumerator, sq_abs] using
      energyLinearComparison_power_deviation ν T h s hT hh hs hSq hsecond 1 t
  · simpa [energyLinearSecondNumerator] using
      energyLinearComparison_power_deviation ν T h s hT hh hs hSq hsecond 2 t
  · exact integral_nonneg fun x => mul_nonneg (pow_nonneg (abs_nonneg x) 3) (Real.exp_nonneg _)
  · have hc : Integrable (fun x : ℝ => |x| ^ 3) (energyTiltedLaw ν h s) := by
      simpa only [zero_mul, Real.exp_zero, mul_one] using
        energyLinear_power_exp_integrable ν T h s hT hh hs hSq hsecond 3 0
    calc
      _ ≤ ∫ x : ℝ, Real.exp (2 * h * |t|) * |x| ^ 3 ∂energyTiltedLaw ν h s := by
        apply integral_mono_ae (energyLinear_integrability ν T h s hT hh hs hSq hsecond t).2.2.2 (hc.const_mul _)
        filter_upwards [energyTiltedLaw_ae_support ν h s] with x hx
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (energyLinear_exponent_bounds h t x hx).2) (pow_nonneg (abs_nonneg x) 3)
      _ = _ := integral_const_mul _ _

theorem energyLinearComparison_reciprocal_bound (t : ℝ) :
    1 / energyLinearNormalizer ν h s t ≤ Real.exp (2 * h * |t|) := by
  have hL := energyLinearNormalizer_pos ν T h s hT hh hs hSq hsecond t
  apply (div_le_iff₀ hL).2
  calc
    1 = Real.exp (-2 * h * |t|) * Real.exp (2 * h * |t|) := by rw [← Real.exp_add]; simp
    _ ≤ energyLinearNormalizer ν h s t * Real.exp (2 * h * |t|) :=
      mul_le_mul_of_nonneg_right (energyLinearNormalizer_bounds ν T h s hT hh hs hSq hsecond t).1 (Real.exp_nonneg _)
    _ = _ := mul_comm _ _

end Admissible

/-- Both numerator and normalizer errors are retained in this scalar algebra step. -/
theorem energyLinearComparison_div_deviation (A b L D τ u v : ℝ) (hL : 0 < L)
    (hD : 0 ≤ D) (hτ : 0 ≤ τ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hInv : 1 / L ≤ D) (hA : |A - b| ≤ D * τ * v) (hN : |L - 1| ≤ D * τ * u) :
    |A / L - b| ≤ D ^ 2 * τ * (v + |b| * u) := by
  have heq : A / L - b = ((A - b) + b * (1 - L)) / L := by field_simp; ring
  have hNum : |(A - b) + b * (1 - L)| ≤ D * τ * v + |b| * (D * τ * u) := by
    calc
      _ ≤ |A - b| + |b * (1 - L)| := abs_add_le _ _
      _ = |A - b| + |b| * |L - 1| := by rw [abs_mul, abs_sub_comm 1 L]
      _ ≤ _ := add_le_add hA (mul_le_mul_of_nonneg_left hN (abs_nonneg b))
  calc
    _ = |(A - b) + b * (1 - L)| * (1 / L) := by rw [heq, abs_div, abs_of_pos hL]; ring
    _ ≤ (D * τ * v + |b| * (D * τ * u)) * (1 / L) :=
      mul_le_mul_of_nonneg_right hNum (by positivity)
    _ = (D * (1 / L)) * (τ * (v + |b| * u)) := by ring
    _ ≤ (D * D) * (τ * (v + |b| * u)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hInv hD) (by positivity)
    _ = _ := by ring

section Admissible

variable (ν : Measure ℝ) [IsProbabilityMeasure ν] (T h s : ℝ)
  (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
  (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
  (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)

include hT hh hs hSq hsecond

/-- The three normalized comparisons under the actual linear tilted probability law. -/
theorem energyLinear_normalized_comparisons (t : ℝ) :
    |energyLinearMean ν h s t - (∫ x : ℝ, x ∂energyTiltedLaw ν h s)| ≤
      Real.exp (2 * h * |t|) ^ 2 * |t| *
        ((∫ x : ℝ, x ^ 2 ∂energyTiltedLaw ν h s) +
          |∫ x : ℝ, x ∂energyTiltedLaw ν h s| * (∫ x : ℝ, |x| ∂energyTiltedLaw ν h s)) ∧
    |(∫ x : ℝ, x ^ 2 ∂energyLinearTiltLaw ν h s t) - (∫ x : ℝ, x ^ 2 ∂energyTiltedLaw ν h s)| ≤
      Real.exp (2 * h * |t|) ^ 2 * |t| *
        ((∫ x : ℝ, |x| ^ 3 ∂energyTiltedLaw ν h s) +
          (∫ x : ℝ, x ^ 2 ∂energyTiltedLaw ν h s) * (∫ x : ℝ, |x| ∂energyTiltedLaw ν h s)) ∧
    (∫ x : ℝ, |x| ^ 3 ∂energyLinearTiltLaw ν h s t) ≤
      Real.exp (2 * h * |t|) ^ 2 * (∫ x : ℝ, |x| ^ 3 ∂energyTiltedLaw ν h s) := by
  have hr := energyLinear_raw_comparisons ν T h s hT hh hs hSq hsecond t
  have hInv := energyLinearComparison_reciprocal_bound ν T h s hT hh hs hSq hsecond t
  have hL := energyLinearNormalizer_pos ν T h s hT hh hs hSq hsecond t
  have hu : 0 ≤ ∫ x : ℝ, |x| ∂energyTiltedLaw ν h s := integral_nonneg fun _ => abs_nonneg _
  have hq : 0 ≤ ∫ x : ℝ, x ^ 2 ∂energyTiltedLaw ν h s := integral_nonneg fun _ => sq_nonneg _
  have hc : 0 ≤ ∫ x : ℝ, |x| ^ 3 ∂energyTiltedLaw ν h s := integral_nonneg fun _ => pow_nonneg (abs_nonneg _) 3
  have hm := energyLinearTiltLaw_moments ν T h s hT hh hs hSq hsecond t
  refine ⟨?_, ?_, ?_⟩
  · exact energyLinearComparison_div_deviation _ _ _ _ _ _ _ hL (Real.exp_nonneg _) (abs_nonneg _) hu hq hInv hr.2.1 hr.1
  · rw [hm.2.2.2.2.2.1]
    simpa only [abs_of_nonneg hq] using energyLinearComparison_div_deviation _ _ _ _ _ _ _
      hL (Real.exp_nonneg _) (abs_nonneg _) hu hc hInv hr.2.2.1 hr.1
  · rw [hm.2.2.2.2.2.2]
    calc
      _ = energyLinearThirdNumerator ν h s t * (1 / energyLinearNormalizer ν h s t) := by ring
      _ ≤ (Real.exp (2 * h * |t|) * (∫ x : ℝ, |x| ^ 3 ∂energyTiltedLaw ν h s)) *
          (1 / energyLinearNormalizer ν h s t) := mul_le_mul_of_nonneg_right hr.2.2.2.2 (by positivity)
      _ ≤ (Real.exp (2 * h * |t|) * (∫ x : ℝ, |x| ^ 3 ∂energyTiltedLaw ν h s)) *
          Real.exp (2 * h * |t|) := mul_le_mul_of_nonneg_left hInv (mul_nonneg (Real.exp_nonneg _) hc)
      _ = _ := by ring

end Admissible

end Shao.OQ4
