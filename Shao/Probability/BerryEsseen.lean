import Shao.Probability.MeasurablePath
import Shao.OQ4.IntervalConcentration
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod

/-!
Quantitative finite iid normal approximation and atomic Fourier smoothing.
The classical Fourier smoothing method is implemented for the actual finite
product laws, retaining closed CDF events and arbitrary atoms. The affine
specializations center by the actual mean and retain the raw-law drift error.
-/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped Topology Convolution FourierTransform

noncomputable def cdfFourierError
    (mu nu : Measure ℝ) (t : ℝ) : ℝ :=
  ‖MeasureTheory.charFun mu t - MeasureTheory.charFun nu t‖ / |t|

private theorem be_phase_integrable (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (t : ℝ) :
    Integrable (fun z : ℝ => Complex.exp ((t * z : ℝ) * Complex.I)) mu := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  exact Filter.Eventually.of_forall fun z => by
    simp [Complex.norm_exp, Complex.mul_re]

private theorem be_charFun_sub_one (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hmu : Integrable (fun z : ℝ => z) mu) (t : ℝ) :
    ‖charFun mu t - 1‖ ≤ |t| * (∫ z : ℝ, |z| ∂mu) := by
  have heq : charFun mu t - 1 =
      ∫ z : ℝ, Complex.exp ((t * z : ℝ) * Complex.I) - 1 ∂mu := by
    rw [integral_sub (be_phase_integrable mu t) (integrable_const (1 : ℂ))]
    simp only [integral_const, probReal_univ, one_smul]
    rw [charFun_apply_real]
    simp only [Complex.ofReal_mul]
  rw [heq]
  calc
    _ ≤ ∫ z : ℝ, |t| * |z| ∂mu := by
      apply norm_integral_le_of_norm_le (hmu.abs.const_mul |t|)
      filter_upwards [] with z
      simpa only [mul_comm Complex.I, Real.norm_eq_abs, abs_mul] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * z))
    _ = _ := integral_const_mul _ _

private theorem be_cdfFourierError_nonneg (mu nu : Measure ℝ) (t : ℝ) :
    0 ≤ cdfFourierError mu nu t := by
  exact div_nonneg (norm_nonneg _) (abs_nonneg t)

private theorem be_cdfFourierError_bound
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : Integrable (fun z : ℝ => z) mu)
    (hnu : Integrable (fun z : ℝ => z) nu) (t : ℝ) :
    cdfFourierError mu nu t ≤
      (∫ z : ℝ, |z| ∂mu) + (∫ z : ℝ, |z| ∂nu) := by
  by_cases ht : t = 0
  · simp only [cdfFourierError, ht, abs_zero, div_zero]
    positivity
  have htpos : 0 < |t| := abs_pos.mpr ht
  apply (div_le_iff₀ htpos).2
  have htri : ‖charFun mu t - charFun nu t‖ ≤
      ‖charFun mu t - 1‖ + ‖charFun nu t - 1‖ := by
    calc
      _ = ‖(charFun mu t - 1) - (charFun nu t - 1)‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  calc
    _ ≤ ‖charFun mu t - 1‖ + ‖charFun nu t - 1‖ := htri
    _ ≤ |t| * (∫ z : ℝ, |z| ∂mu) + |t| * (∫ z : ℝ, |z| ∂nu) :=
      add_le_add (be_charFun_sub_one mu hmu t) (be_charFun_sub_one nu hnu t)
    _ = _ := by ring

private theorem be_integrableOn_cdfFourierError
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : Integrable (fun z : ℝ => z) mu)
    (hnu : Integrable (fun z : ℝ => z) nu) (T : ℝ) :
    IntegrableOn (cdfFourierError mu nu) (Set.Icc (-T) T) := by
  have hc : IntegrableOn (fun _ : ℝ =>
      (∫ z : ℝ, |z| ∂mu) + (∫ z : ℝ, |z| ∂nu)) (Set.Icc (-T) T) :=
    integrableOn_const (by simp)
  refine hc.mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · unfold cdfFourierError
    exact (show Measurable (fun t : ℝ =>
      ‖charFun mu t - charFun nu t‖ / |t|) by fun_prop).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (be_cdfFourierError_nonneg mu nu t)]
    exact be_cdfFourierError_bound mu nu hmu hnu t

private theorem be_cdf_step_section (z : ℝ) :
    Integrable (fun x : ℝ =>
      (if z ≤ x then (1 : ℝ) else 0) - (if 0 ≤ x then (1 : ℝ) else 0)) ∧
      (∫ x : ℝ, ‖(if z ≤ x then (1 : ℝ) else 0) -
        (if 0 ≤ x then (1 : ℝ) else 0)‖) = |z| := by
  by_cases hz : 0 ≤ z
  · have heq : (fun x : ℝ =>
        (if z ≤ x then (1 : ℝ) else 0) - (if 0 ≤ x then (1 : ℝ) else 0)) =
        (Set.Ico 0 z).indicator (fun _ : ℝ => (-1 : ℝ)) := by
      funext x
      by_cases hx : 0 ≤ x <;> by_cases hzx : z ≤ x <;>
        simp [Set.indicator, Set.mem_Ico, hx, hzx] <;> linarith
    rw [heq]
    constructor
    · exact (integrableOn_const (by simp) :
        IntegrableOn (fun _ : ℝ => (-1 : ℝ)) (Set.Ico 0 z)).integrable_indicator
          measurableSet_Ico
    · change (∫ x : ℝ, ‖(fun x : ℝ =>
        (if z ≤ x then (1 : ℝ) else 0) - (if 0 ≤ x then (1 : ℝ) else 0)) x‖) = |z|
      rw [heq]
      simp only [norm_indicator_eq_indicator_norm, Real.norm_eq_abs, abs_neg, abs_one]
      rw [integral_indicator measurableSet_Ico]
      simp [Real.volume_real_Ico_of_le hz, abs_of_nonneg hz]
  · have hz0 : z ≤ 0 := le_of_not_ge hz
    have heq : (fun x : ℝ =>
        (if z ≤ x then (1 : ℝ) else 0) - (if 0 ≤ x then (1 : ℝ) else 0)) =
        (Set.Ico z 0).indicator (fun _ : ℝ => (1 : ℝ)) := by
      funext x
      by_cases hx : 0 ≤ x <;> by_cases hzx : z ≤ x <;>
        simp [Set.indicator, Set.mem_Ico, hx, hzx] <;> linarith
    rw [heq]
    constructor
    · exact (integrableOn_const (by simp) :
        IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ico z 0)).integrable_indicator
          measurableSet_Ico
    · change (∫ x : ℝ, ‖(fun x : ℝ =>
        (if z ≤ x then (1 : ℝ) else 0) - (if 0 ≤ x then (1 : ℝ) else 0)) x‖) = |z|
      rw [heq]
      simp only [norm_indicator_eq_indicator_norm, Real.norm_eq_abs, abs_one]
      rw [integral_indicator measurableSet_Ico]
      simp [Real.volume_real_Ico_of_le hz0, abs_of_nonpos hz0]

private theorem be_cdf_step_integrable_prod
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hmu : Integrable (fun z : ℝ => z) mu) :
    Integrable (fun p : ℝ × ℝ =>
      (if p.1 ≤ p.2 then (1 : ℝ) else 0) -
        (if 0 ≤ p.2 then (1 : ℝ) else 0)) (mu.prod volume) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      (if p.1 ≤ p.2 then (1 : ℝ) else 0) -
        (if 0 ≤ p.2 then (1 : ℝ) else 0)) := by
    exact (Measurable.ite (measurableSet_le measurable_fst measurable_snd)
      measurable_const measurable_const).sub
        (Measurable.ite (measurableSet_le measurable_const measurable_snd)
          measurable_const measurable_const)
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun z => (be_cdf_step_section z).1
  · simpa only [(be_cdf_step_section _).2] using hmu.abs

private theorem be_cdf_step_integral
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (x : ℝ) :
    (∫ z : ℝ, (if z ≤ x then (1 : ℝ) else 0) -
        (if 0 ≤ x then (1 : ℝ) else 0) ∂mu) =
      mu.real (Set.Iic x) - (if 0 ≤ x then (1 : ℝ) else 0) := by
  have heq : (fun z : ℝ => if z ≤ x then (1 : ℝ) else 0) =
      (Set.Iic x).indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext z
    simp only [Set.indicator, Set.mem_Iic]
  have hi : Integrable (fun z : ℝ => if z ≤ x then (1 : ℝ) else 0) mu := by
    rw [heq]
    exact (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  rw [integral_sub hi (integrable_const _), heq, integral_indicator measurableSet_Iic]
  simp

private theorem be_integrable_cdf_difference
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : Integrable (fun z : ℝ => z) mu)
    (hnu : Integrable (fun z : ℝ => z) nu) :
    Integrable (fun x : ℝ => mu.real (Set.Iic x) - nu.real (Set.Iic x)) := by
  have hmi := (be_cdf_step_integrable_prod mu hmu).integral_prod_right
  have hni := (be_cdf_step_integrable_prod nu hnu).integral_prod_right
  simp_rw [be_cdf_step_integral] at hmi hni
  convert hmi.sub hni using 1
  funext x
  change mu.real (Set.Iic x) - nu.real (Set.Iic x) =
    (mu.real (Set.Iic x) - (if 0 ≤ x then (1 : ℝ) else 0)) -
      (nu.real (Set.Iic x) - (if 0 ≤ x then (1 : ℝ) else 0))
  ring

private theorem be_cdf_step_fourier (z t : ℝ) (ht : t ≠ 0) :
    (∫ x : ℝ, Complex.exp ((t * x : ℝ) * Complex.I) *
      (((if z ≤ x then (1 : ℝ) else 0) -
        (if 0 ≤ x then (1 : ℝ) else 0) : ℝ) : ℂ)) =
      -(Complex.exp ((t * z : ℝ) * Complex.I) - 1) /
        ((t : ℂ) * Complex.I) := by
  have hc : (t : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) Complex.I_ne_zero
  have hphase : (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I)) =
      (fun x : ℝ => Complex.exp (((t : ℂ) * Complex.I) * x)) := by
    funext x
    congr 1
    push_cast
    ring
  by_cases hz : 0 ≤ z
  · have heq : (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I) *
        (((if z ≤ x then (1 : ℝ) else 0) -
          (if 0 ≤ x then (1 : ℝ) else 0) : ℝ) : ℂ)) =
        (Set.Ico 0 z).indicator
          (fun x : ℝ => -Complex.exp ((t * x : ℝ) * Complex.I)) := by
      funext x
      by_cases hx : 0 ≤ x <;> by_cases hzx : z ≤ x <;>
        simp [Set.indicator, Set.mem_Ico, hx, hzx] <;> linarith
    rw [heq, integral_indicator measurableSet_Ico, integral_neg,
      integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hz,
      hphase, integral_exp_mul_complex hc]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    push_cast
    ring
  · have hz0 : z ≤ 0 := le_of_not_ge hz
    have heq : (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I) *
        (((if z ≤ x then (1 : ℝ) else 0) -
          (if 0 ≤ x then (1 : ℝ) else 0) : ℝ) : ℂ)) =
        (Set.Ico z 0).indicator
          (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I)) := by
      funext x
      by_cases hx : 0 ≤ x <;> by_cases hzx : z ≤ x <;>
        simp [Set.indicator, Set.mem_Ico, hx, hzx] <;> linarith
    rw [heq, integral_indicator measurableSet_Ico,
      integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hz0,
      hphase, integral_exp_mul_complex hc]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    push_cast
    ring

private theorem be_cdf_step_fourier_integrable_prod
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hmu : Integrable (fun z : ℝ => z) mu) (t : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      Complex.exp ((t * p.2 : ℝ) * Complex.I) *
        (((if p.1 ≤ p.2 then (1 : ℝ) else 0) -
          (if 0 ≤ p.2 then (1 : ℝ) else 0) : ℝ) : ℂ)) (mu.prod volume) := by
  refine (be_cdf_step_integrable_prod mu hmu).norm.mono' ?_ ?_
  · apply AEStronglyMeasurable.mul
    · exact (show Measurable (fun p : ℝ × ℝ =>
        Complex.exp ((t * p.2 : ℝ) * Complex.I)) by fun_prop).aestronglyMeasurable
    · exact ((be_cdf_step_integrable_prod mu hmu).ofReal (𝕜 := ℂ)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p => by
      by_cases h1 : p.1 ≤ p.2 <;> by_cases h0 : 0 ≤ p.2 <;>
        simp [h1, h0, Complex.norm_exp, Complex.mul_re]

private theorem be_cdf_step_transform
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hmu : Integrable (fun z : ℝ => z) mu) (t : ℝ) (ht : t ≠ 0) :
    (∫ x : ℝ, Complex.exp ((t * x : ℝ) * Complex.I) *
      ((mu.real (Set.Iic x) - (if 0 ≤ x then (1 : ℝ) else 0) : ℝ) : ℂ)) =
      -(charFun mu t - 1) / ((t : ℂ) * Complex.I) := by
  have hinner (x : ℝ) :
      (∫ z : ℝ, Complex.exp ((t * x : ℝ) * Complex.I) *
        (((if z ≤ x then (1 : ℝ) else 0) -
          (if 0 ≤ x then (1 : ℝ) else 0) : ℝ) : ℂ) ∂mu) =
        Complex.exp ((t * x : ℝ) * Complex.I) *
          ((mu.real (Set.Iic x) - (if 0 ≤ x then (1 : ℝ) else 0) : ℝ) : ℂ) := by
    rw [integral_const_mul, integral_complex_ofReal, be_cdf_step_integral]
  calc
    _ = ∫ x : ℝ, ∫ z : ℝ, Complex.exp ((t * x : ℝ) * Complex.I) *
        (((if z ≤ x then (1 : ℝ) else 0) -
          (if 0 ≤ x then (1 : ℝ) else 0) : ℝ) : ℂ) ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => (hinner x).symm
    _ = ∫ z : ℝ, (∫ x : ℝ, Complex.exp ((t * x : ℝ) * Complex.I) *
        (((if z ≤ x then (1 : ℝ) else 0) -
          (if 0 ≤ x then (1 : ℝ) else 0) : ℝ) : ℂ)) ∂mu :=
      (integral_integral_swap (μ := mu) (ν := volume)
        (be_cdf_step_fourier_integrable_prod mu hmu t)).symm
    _ = ∫ z : ℝ, -(Complex.exp ((t * z : ℝ) * Complex.I) - 1) /
        ((t : ℂ) * Complex.I) ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => be_cdf_step_fourier z t ht
    _ = _ := by
      rw [integral_div, integral_neg,
        integral_sub (be_phase_integrable mu t) (integrable_const (1 : ℂ))]
      simp only [integral_const, probReal_univ, one_smul,
        charFun_apply_real, Complex.ofReal_mul]

private theorem be_cdf_difference_fourier
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : Integrable (fun z : ℝ => z) mu)
    (hnu : Integrable (fun z : ℝ => z) nu) (t : ℝ) (ht : t ≠ 0) :
    (∫ x : ℝ, Complex.exp ((t * x : ℝ) * Complex.I) *
      ((mu.real (Set.Iic x) - nu.real (Set.Iic x) : ℝ) : ℂ)) =
        -(charFun mu t - charFun nu t) / ((t : ℂ) * Complex.I) := by
  have hi (rho : Measure ℝ) [IsProbabilityMeasure rho]
      (hrho : Integrable (fun z : ℝ => z) rho) :
      Integrable (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I) *
        ((rho.real (Set.Iic x) - (if 0 ≤ x then (1 : ℝ) else 0) : ℝ) : ℂ)) := by
    have h := (be_cdf_step_fourier_integrable_prod rho hrho t).integral_prod_right
    simp_rw [integral_const_mul, integral_complex_ofReal, be_cdf_step_integral] at h
    exact h
  have heq : (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I) *
      ((mu.real (Set.Iic x) - nu.real (Set.Iic x) : ℝ) : ℂ)) =
      (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I) *
        ((mu.real (Set.Iic x) - (if 0 ≤ x then (1 : ℝ) else 0) : ℝ) : ℂ)) -
      (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I) *
        ((nu.real (Set.Iic x) - (if 0 ≤ x then (1 : ℝ) else 0) : ℝ) : ℂ)) := by
    funext x
    simp only [Pi.sub_apply, Complex.ofReal_sub]
    ring
  rw [heq]
  change (∫ x : ℝ,
    Complex.exp ((t * x : ℝ) * Complex.I) *
      ((mu.real (Set.Iic x) - (if 0 ≤ x then (1 : ℝ) else 0) : ℝ) : ℂ) -
    Complex.exp ((t * x : ℝ) * Complex.I) *
      ((nu.real (Set.Iic x) - (if 0 ≤ x then (1 : ℝ) else 0) : ℝ) : ℂ)) = _
  rw [integral_sub (hi mu hmu) (hi nu hnu),
    be_cdf_step_transform mu hmu t ht, be_cdf_step_transform nu hnu t ht]
  ring

private theorem be_sinc_fourth_majorant (x : ℝ) :
    0 ≤ (Real.sinc x) ^ 4 ∧
      (Real.sinc x) ^ 4 ≤ 2 / (1 + x ^ 2) ∧
      |x| * (Real.sinc x) ^ 4 ≤ 2 / (1 + x ^ 2) := by
  let X : ℝ := |x|
  let a : ℝ := |Real.sinc x|
  have hX : 0 ≤ X := abs_nonneg x
  have ha : 0 ≤ a := abs_nonneg _
  have ha1 : a ≤ 1 := Real.abs_sinc_le_one x
  have ha4 : a ^ 4 ≤ 1 := by simpa using pow_le_pow_left₀ ha ha1 4
  have heq : a ^ 4 = (Real.sinc x) ^ 4 := by
    dsimp [a]
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  have hX2 : X ^ 2 = x ^ 2 := sq_abs x
  have hden : 0 < 1 + x ^ 2 := by positivity
  have hbounds : a ^ 4 * (1 + X ^ 2) ≤ 2 ∧
      X * a ^ 4 * (1 + X ^ 2) ≤ 2 := by
    by_cases hsmall : X ≤ 1
    · have hXs : X ^ 2 ≤ 1 := by nlinarith
      have hp : X * a ^ 4 ≤ 1 :=
        (mul_le_mul_of_nonneg_right hsmall (pow_nonneg ha 4)).trans (by simpa using ha4)
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr ha4) (sub_nonneg.mpr hXs)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hXs)]
    · have hbig : 1 ≤ X := (lt_of_not_ge hsmall).le
      have hx : x ≠ 0 := by intro hx; norm_num [X, hx] at hbig
      have hprod : a * X ≤ 1 := by
        dsimp [a, X]
        rw [Real.sinc_of_ne_zero hx, abs_div, div_mul_cancel₀ _ (abs_ne_zero.mpr hx)]
        exact Real.abs_sin_le_one x
      have hp4 : a ^ 4 * X ^ 4 ≤ 1 := by
        simpa only [mul_pow, one_pow] using
          pow_le_pow_left₀ (mul_nonneg ha hX) hprod 4
      have hXsq : 1 ≤ X ^ 2 := by nlinarith
      have hXcube : X ≤ X ^ 3 := by nlinarith [mul_nonneg hX (sub_nonneg.mpr hXsq)]
      have hXfour : X ^ 3 ≤ X ^ 4 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hbig) (pow_nonneg hX 3)]
      have hXs4 : X ^ 2 ≤ X ^ 4 := by nlinarith [sq_nonneg (X ^ 2 - 1)]
      constructor
      · have hh := mul_le_mul_of_nonneg_left (show 1 + X ^ 2 ≤ 2 * X ^ 4 by
          nlinarith) (pow_nonneg ha 4)
        nlinarith
      · have hh := mul_le_mul_of_nonneg_left (show X * (1 + X ^ 2) ≤ 2 * X ^ 4 by
          nlinarith) (pow_nonneg ha 4)
        nlinarith
  rw [← heq]
  refine ⟨pow_nonneg ha 4, (le_div_iff₀ hden).2 ?_, (le_div_iff₀ hden).2 ?_⟩
  · simpa only [← hX2] using hbounds.1
  · simpa only [← hX2] using hbounds.2

private theorem be_sinc_fourth_integrable :
    Integrable (fun x : ℝ => (Real.sinc x) ^ 4) ∧
      Integrable (fun x : ℝ => |x| * (Real.sinc x) ^ 4) := by
  have hg : Integrable (fun x : ℝ => 2 / (1 + x ^ 2)) := by
    simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul 2
  constructor
  · refine hg.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (be_sinc_fourth_majorant x).1]
    exact (be_sinc_fourth_majorant x).2.1
  · refine hg.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (abs_nonneg x) (be_sinc_fourth_majorant x).1)]
    exact (be_sinc_fourth_majorant x).2.2

private theorem be_sinc_fourth_tail (x : ℝ) (hx : 0 < x) :
    x * (Real.sinc x) ^ 4 ≤ x ^ (-3 : ℝ) := by
  have hs : (Real.sin x) ^ 4 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg (Real.sin x)) (Real.abs_sin_le_one x) 4
    simpa only [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, one_pow] using h
  have hp : x * (Real.sinc x) ^ 4 ≤ 1 / x ^ 3 := by
    apply (le_div_iff₀ (pow_pos hx 3)).2
    calc
      _ = (Real.sin x) ^ 4 := by
        rw [Real.sinc_of_ne_zero hx.ne']
        field_simp
        <;> ring
      _ ≤ 1 := hs
  simpa [Real.rpow_neg] using hp

private theorem be_sinc_fourth_firstMoment :
    (∫ x : ℝ, |x| * (Real.sinc x) ^ 4) ≤ 2 := by
  let f : ℝ → ℝ := fun x => |x| * (Real.sinc x) ^ 4
  have hf : Integrable f := be_sinc_fourth_integrable.2
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hcompact : (∫ x : ℝ in (0 : ℝ)..1, f x) ≤ 1 / 2 := by
    calc
      _ ≤ ∫ x : ℝ in (0 : ℝ)..1, x := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (hc.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)
        intro x hx
        have hs4 : (Real.sinc x) ^ 4 ≤ 1 := by
          have h := pow_le_pow_left₀ (abs_nonneg (Real.sinc x))
            (Real.abs_sinc_le_one x) 4
          simpa only [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, one_pow] using h
        dsimp [f]
        rw [abs_of_nonneg hx.1]
        exact (mul_le_mul_of_nonneg_left hs4 hx.1).trans_eq (mul_one x)
      _ = _ := by norm_num
  have hrp : IntegrableOn (fun x : ℝ => x ^ (-3 : ℝ)) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have htail : (∫ x : ℝ in Set.Ioi (1 : ℝ), f x) ≤ 1 / 2 := by
    have hle : (∫ x : ℝ in Set.Ioi (1 : ℝ), f x) ≤
        ∫ x : ℝ in Set.Ioi (1 : ℝ), x ^ (-3 : ℝ) := by
      apply integral_mono_ae hf.integrableOn hrp
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxp : 0 < x := lt_trans (by norm_num) hx
      simpa only [f, abs_of_pos hxp] using be_sinc_fourth_tail x hxp
    have heval := integral_Ioi_rpow_of_lt (a := (-3 : ℝ)) (c := (1 : ℝ))
      (by norm_num) (by norm_num)
    norm_num at heval
    have hle' : (∫ x : ℝ in Set.Ioi (1 : ℝ), f x) ≤
        ∫ x : ℝ in Set.Ioi (1 : ℝ), (x ^ 3)⁻¹ := by
      simpa [Real.rpow_neg] using hle
    rwa [heval] at hle'
  have hpos : (∫ x : ℝ in Set.Ioi (0 : ℝ), f x) ≤ 1 := by
    have hh := intervalIntegral.integral_interval_add_Ioi
      (a := (0 : ℝ)) (b := (1 : ℝ)) hf.integrableOn hf.integrableOn
    linarith
  have heven (x : ℝ) : f (-x) = f x := by simp [f, Real.sinc_neg]
  have hneg : (∫ x : ℝ in Set.Iic (0 : ℝ), f x) =
      ∫ x : ℝ in Set.Ioi (0 : ℝ), f x := by
    have hh := integral_comp_neg_Iic (0 : ℝ) f
    simpa only [heven, neg_zero] using hh
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (b := (0 : ℝ)) hf.integrableOn hf.integrableOn
  change (∫ x : ℝ, f x) ≤ 2
  linarith

private theorem be_box_convolution (x : ℝ) :
    let b : ℝ → ℂ := (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℂ))
    (b ⋆[.mul ℂ ℂ] b) x = (max (2 - |x|) 0 : ℝ) := by
  let b : ℝ → ℂ := (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℂ))
  change (∫ t : ℝ, b t * b (x - t)) = ((max (2 - |x|) 0 : ℝ) : ℂ)
  have heq : (fun t : ℝ => b t * b (x - t)) =
      (Set.Icc (max (-1) (x - 1)) (min 1 (x + 1))).indicator
        (fun _ : ℝ => (1 : ℂ)) := by
    funext t
    have hm : t ∈ Set.Icc (max (-1) (x - 1)) (min 1 (x + 1)) ↔
        t ∈ Set.Icc (-1 : ℝ) 1 ∧ x - t ∈ Set.Icc (-1 : ℝ) 1 := by
      simp only [Set.mem_Icc, max_le_iff, le_min_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨⟨h1, h3⟩, ⟨by linarith, by linarith⟩⟩
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨⟨h1, by linarith⟩, h2, by linarith⟩
    by_cases h1 : t ∈ Set.Icc (-1 : ℝ) 1 <;>
      by_cases h2 : x - t ∈ Set.Icc (-1 : ℝ) 1 <;>
        simp [b, Set.indicator, h1, h2, hm]
  rw [heq, integral_indicator measurableSet_Icc]
  simp only [setIntegral_const, RCLike.real_smul_eq_coe_mul, mul_one]
  congr 1
  rw [Real.volume_real_Icc]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_right (by linarith : (-1 : ℝ) ≤ x - 1),
      min_eq_left (by linarith : (1 : ℝ) ≤ x + 1)]
    congr 1
    ring
  · have hx0 : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx0, max_eq_left (by linarith : x - 1 ≤ (-1 : ℝ)),
      min_eq_right (by linarith : x + 1 ≤ (1 : ℝ))]
    congr 1
    ring

private theorem be_interval_phase_integral (t : ℝ) :
    (∫ x : ℝ in (-1 : ℝ)..1,
      Complex.exp ((t * x : ℝ) * Complex.I)) = (2 * Real.sinc t : ℝ) := by
  by_cases ht : t = 0
  · norm_num [ht]
  have hc : (t : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) Complex.I_ne_zero
  have heq : (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I)) =
      (fun x : ℝ => Complex.exp (((t : ℂ) * Complex.I) * x)) := by
    funext x
    congr 1
    push_cast
    ring
  rw [heq, integral_exp_mul_complex hc, Real.sinc_of_ne_zero ht]
  simp only [Complex.ofReal_neg, Complex.ofReal_one, mul_one, mul_neg_one,
    show -((t : ℂ) * Complex.I) = (-t : ℂ) * Complex.I by ring,
    Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  field_simp
  <;> ring

private theorem be_box_fourier (t : ℝ) :
    let b : ℝ → ℂ := (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℂ))
    𝓕 b t = (2 * Real.sinc (2 * Real.pi * t) : ℝ) := by
  let b : ℝ → ℂ := (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℂ))
  change 𝓕 b t = ((2 * Real.sinc (2 * Real.pi * t) : ℝ) : ℂ)
  rw [Real.fourier_real_eq_integral_exp_smul]
  have heq : (fun x : ℝ => Complex.exp ((-2 * Real.pi * x * t : ℝ) * Complex.I) • b x) =
      (Set.Icc (-1 : ℝ) 1).indicator
        (fun x : ℝ => Complex.exp (((-2 * Real.pi * t) * x : ℝ) * Complex.I)) := by
    funext x
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
    · simp only [b, Set.indicator_of_mem hx, smul_eq_mul, mul_one]
      congr 1
      push_cast
      ring
    · simp [b, Set.indicator_of_notMem hx]
  rw [heq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    be_interval_phase_integral]
  have he : -2 * Real.pi * t = -(2 * Real.pi * t) := by ring
  rw [he, Real.sinc_neg]

private theorem be_triangle_data :
    let g : ℝ → ℂ := fun x => ((max (2 - |x|) 0 : ℝ) : ℂ)
    Integrable g ∧ Continuous g ∧ HasCompactSupport g ∧
      ∀ t : ℝ, 𝓕 g t = (4 * (Real.sinc (2 * Real.pi * t)) ^ 2 : ℝ) := by
  let b : ℝ → ℂ := (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℂ))
  let g : ℝ → ℂ := fun x => ((max (2 - |x|) 0 : ℝ) : ℂ)
  have hb : Integrable b :=
    (integrableOn_const (by simp) :
      IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Set.Icc (-1 : ℝ) 1)).integrable_indicator
        measurableSet_Icc
  have heq : (b ⋆[.mul ℂ ℂ] b) = g := by
    funext x
    exact be_box_convolution x
  have hgi : Integrable g := by
    rw [← heq]
    exact hb.integrable_convolution (.mul ℂ ℂ) hb
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have hgs : HasCompactSupport g := by
    apply HasCompactSupport.intro isCompact_Icc
    intro x hx
    have hlarge : 2 ≤ |x| := by
      by_contra hn
      have hh := abs_lt.mp (lt_of_not_ge hn)
      exact hx ⟨hh.1.le, hh.2.le⟩
    simp [g, max_eq_right (by linarith : 2 - |x| ≤ 0)]
  refine ⟨hgi, hgc, hgs, ?_⟩
  intro t
  change 𝓕 g t = ((4 * (Real.sinc (2 * Real.pi * t)) ^ 2 : ℝ) : ℂ)
  rw [← heq, Real.fourier_mul_convolution_eq hb hb t,
    be_box_fourier t]
  push_cast
  ring

private theorem be_fourBox_data :
    let g : ℝ → ℂ := fun x => ((max (2 - |x|) 0 : ℝ) : ℂ)
    let p : ℝ → ℂ := g ⋆[.mul ℂ ℂ] g
    Integrable p ∧ Continuous p ∧
      (∀ t : ℝ, 4 < |t| → p t = 0) ∧
      ∀ t : ℝ, 𝓕 p t = (16 * (Real.sinc (2 * Real.pi * t)) ^ 4 : ℝ) := by
  let g : ℝ → ℂ := fun x => ((max (2 - |x|) 0 : ℝ) : ℂ)
  let p : ℝ → ℂ := g ⋆[.mul ℂ ℂ] g
  obtain ⟨hgi, hgc, hgs, hgF⟩ := be_triangle_data
  change Integrable g at hgi
  change Continuous g at hgc
  change HasCompactSupport g at hgs
  have hpi : Integrable p := hgi.integrable_convolution (.mul ℂ ℂ) hgi
  have hpc : Continuous p :=
    hgs.continuous_convolution_right (.mul ℂ ℂ) hgi.locallyIntegrable hgc
  refine ⟨hpi, hpc, ?_, ?_⟩
  · intro t ht
    change (∫ u : ℝ, g u * g (t - u)) = 0
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun u => by
      by_cases hu : 2 ≤ |u|
      · simp [g, max_eq_right (by linarith : 2 - |u| ≤ 0)]
      · have htu : 2 ≤ |t - u| := by
          have hh : |t| ≤ |u| + |t - u| := by
            simpa only [add_sub_cancel] using abs_add_le u (t - u)
          linarith
        simp [g, max_eq_right (by linarith : 2 - |t - u| ≤ 0)]
  · intro t
    change 𝓕 p t = ((16 * (Real.sinc (2 * Real.pi * t)) ^ 4 : ℝ) : ℂ)
    change 𝓕 (g ⋆[.mul ℂ ℂ] g) t = _
    rw [Real.fourier_mul_convolution_eq hgi hgi t, hgF t]
    push_cast
    ring

private theorem be_triangle_square_integral :
    (∫ x : ℝ, (max (2 - |x|) 0) ^ 2) = 16 / 3 := by
  let f : ℝ → ℝ := fun x => (max (2 - |x|) 0) ^ 2
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hs : ∀ x : ℝ, x ∉ Set.Icc (-2 : ℝ) 2 → f x = 0 := by
    intro x hx
    have hlarge : 2 ≤ |x| := by
      by_contra hn
      have hh := abs_lt.mp (lt_of_not_ge hn)
      exact hx ⟨hh.1.le, hh.2.le⟩
    simp [f, max_eq_right (by linarith : 2 - |x| ≤ 0)]
  have hright : (∫ x : ℝ in (0 : ℝ)..2, f x) = 8 / 3 := by
    have heq : (∫ x : ℝ in (0 : ℝ)..2, f x) =
        ∫ x : ℝ in (0 : ℝ)..2, (2 - x) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hx
      dsimp [f]
      rw [abs_of_nonneg hx.1, max_eq_left (by linarith [hx.2] : 0 ≤ 2 - x)]
    rw [heq]
    have hd (x : ℝ) : HasDerivAt (fun x : ℝ => (2 - x) ^ 3 / (-3))
        ((2 - x) ^ 2) x := by
      convert (((hasDerivAt_id x).const_sub 2).pow 3).div_const (-3) using 1
      all_goals try funext u
      all_goals dsimp
      all_goals ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hd x) ((show Continuous (fun x : ℝ => (2 - x) ^ 2) by
        fun_prop).intervalIntegrable 0 2)]
    norm_num
  have heven (x : ℝ) : f (-x) = f x := by simp [f]
  have hleft : (∫ x : ℝ in (-2 : ℝ)..0, f x) =
      ∫ x : ℝ in (0 : ℝ)..2, f x := by
    have hh := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := (2 : ℝ))
    simpa only [heven, neg_zero] using hh.symm
  have hsum : (∫ x : ℝ in (-2 : ℝ)..0, f x) +
      (∫ x : ℝ in (0 : ℝ)..2, f x) = ∫ x : ℝ in (-2 : ℝ)..2, f x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (-2) 0) (hc.intervalIntegrable 0 2)
  have hfull : (∫ x : ℝ in Set.Icc (-2 : ℝ) 2, f x) = ∫ x : ℝ, f x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hs
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)] at hfull
  change (∫ x : ℝ, f x) = 16 / 3
  linarith only [hright, hleft, hsum, hfull]

private theorem be_fourBox_zero :
    let g : ℝ → ℂ := fun x => ((max (2 - |x|) 0 : ℝ) : ℂ)
    (g ⋆[.mul ℂ ℂ] g) 0 = (16 / 3 : ℂ) := by
  let g : ℝ → ℂ := fun x => ((max (2 - |x|) 0 : ℝ) : ℂ)
  change (∫ u : ℝ, g u * g (0 - u)) = (16 / 3 : ℂ)
  have heq : (fun u : ℝ => g u * g (0 - u)) =
      (fun u : ℝ => (((max (2 - |u|) 0) ^ 2 : ℝ) : ℂ)) := by
    funext u
    simp [g, abs_neg, pow_two, Complex.ofReal_mul]
  rw [heq, integral_complex_ofReal, be_triangle_square_integral]
  norm_num

private theorem be_fourBox_inverse (x : ℝ) :
    let g : ℝ → ℂ := fun u => ((max (2 - |u|) 0 : ℝ) : ℂ)
    (g ⋆[.mul ℂ ℂ] g) x =
      (8 / Real.pi : ℝ) *
        (∫ u : ℝ, Complex.exp ((u * x : ℝ) * Complex.I) *
          (((Real.sinc u) ^ 4 : ℝ) : ℂ)) := by
  let g : ℝ → ℂ := fun u => ((max (2 - |u|) 0 : ℝ) : ℂ)
  let p : ℝ → ℂ := g ⋆[.mul ℂ ℂ] g
  obtain ⟨hpi, hpc, _, hpF⟩ := be_fourBox_data
  change Integrable p at hpi
  change Continuous p at hpc
  have hscaled : Integrable (fun u : ℝ => (Real.sinc ((2 * Real.pi) * u)) ^ 4) :=
    be_sinc_fourth_integrable.1.comp_mul_left' (by positivity : 2 * Real.pi ≠ 0)
  have hFi : Integrable (𝓕 p) := by
    have hi := (hscaled.const_mul 16).ofReal (𝕜 := ℂ)
    convert hi using 1
    funext u
    exact hpF u
  have hinv := hpi.fourierInv_fourier_eq hFi (hpc.continuousAt (x := x))
  change p x = _
  rw [← hinv, Real.fourierInv_eq']
  simp only [real_inner_comm, RCLike.inner_apply, conj_trivial, smul_eq_mul]
  have heq : (fun u : ℝ =>
      Complex.exp ((2 * Real.pi * (x * u) : ℝ) * Complex.I) * 𝓕 p u) =
      (fun u : ℝ => (16 : ℂ) *
        (Complex.exp ((((2 * Real.pi) * u) * x : ℝ) * Complex.I) *
          (((Real.sinc ((2 * Real.pi) * u)) ^ 4 : ℝ) : ℂ))) := by
    funext u
    rw [hpF u]
    rw [show 2 * Real.pi * (x * u) = ((2 * Real.pi) * u) * x by ring]
    push_cast
    ring
  rw [heq, integral_const_mul]
  rw [Measure.integral_comp_mul_left
    (fun u : ℝ => Complex.exp ((u * x : ℝ) * Complex.I) *
      (((Real.sinc u) ^ 4 : ℝ) : ℂ)) (2 * Real.pi)]
  rw [abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * Real.pi)),
    RCLike.real_smul_eq_coe_mul]
  push_cast
  field_simp
  have heI :
      (∫ y : ℝ, Complex.exp ((y : ℂ) * x * Complex.I) * (Real.sinc y : ℂ) ^ 4) =
      (∫ y : ℝ, Complex.exp ((x : ℂ) * Complex.I * y) * (Real.sinc y : ℂ) ^ 4) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      congr 1
      congr 1
      ring
  rw [heI]
  ring_nf
  all_goals rfl

private theorem be_sinc_kernel_transform (t : ℝ) :
    let q : ℝ → ℝ := fun u => (3 / (2 * Real.pi)) * (Real.sinc u) ^ 4
    let g : ℝ → ℂ := fun u => ((max (2 - |u|) 0 : ℝ) : ℂ)
    (∫ u : ℝ, Complex.exp ((t * u : ℝ) * Complex.I) * (q u : ℂ)) =
      (3 / 16 : ℂ) * (g ⋆[.mul ℂ ℂ] g) t := by
  let q : ℝ → ℝ := fun u => (3 / (2 * Real.pi)) * (Real.sinc u) ^ 4
  let g : ℝ → ℂ := fun u => ((max (2 - |u|) 0 : ℝ) : ℂ)
  let p : ℝ → ℂ := g ⋆[.mul ℂ ℂ] g
  let I : ℂ := ∫ u : ℝ, Complex.exp ((u * t : ℝ) * Complex.I) *
    (((Real.sinc u) ^ 4 : ℝ) : ℂ)
  have hinv : p t = (8 / Real.pi : ℝ) * I := be_fourBox_inverse t
  change (∫ u : ℝ, Complex.exp ((t * u : ℝ) * Complex.I) * (q u : ℂ)) =
    (3 / 16 : ℂ) * p t
  calc
    _ = ((3 / (2 * Real.pi) : ℝ) : ℂ) * I := by
      dsimp [I]
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by
        dsimp [q]
        rw [mul_comm t u]
        push_cast
        ring
    _ = _ := by
      rw [hinv]
      push_cast
      field_simp
      <;> ring

private theorem be_sinc_kernel_data :
    let q : ℝ → ℝ := fun u => (3 / (2 * Real.pi)) * (Real.sinc u) ^ 4
    (∀ u : ℝ, 0 ≤ q u) ∧ Integrable q ∧
      Integrable (fun u : ℝ => |u| * q u) ∧
      (∫ u : ℝ, q u) = 1 ∧
      (∫ u : ℝ, |u| * q u) ≤ 1 ∧
      ∀ t : ℝ, 4 < |t| →
        (∫ u : ℝ, Complex.exp ((t * u : ℝ) * Complex.I) * (q u : ℂ)) = 0 := by
  let q : ℝ → ℝ := fun u => (3 / (2 * Real.pi)) * (Real.sinc u) ^ 4
  have hqpos (u : ℝ) : 0 ≤ q u := by dsimp [q]; positivity
  have hqi : Integrable q := be_sinc_fourth_integrable.1.const_mul _
  have hqmi : Integrable (fun u : ℝ => |u| * q u) := by
    convert be_sinc_fourth_integrable.2.const_mul (3 / (2 * Real.pi)) using 1
    funext u
    dsimp [q]
    ring
  have hnorm : (∫ u : ℝ, q u) = 1 := by
    have hh := be_sinc_kernel_transform 0
    simp only [mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
      one_mul, integral_complex_ofReal, be_fourBox_zero] at hh
    norm_num at hh
    exact_mod_cast hh
  have hmom : (∫ u : ℝ, |u| * q u) ≤ 1 := by
    have heq : (fun u : ℝ => |u| * q u) =
        (fun u : ℝ => (3 / (2 * Real.pi)) * (|u| * (Real.sinc u) ^ 4)) := by
      funext u
      dsimp [q]
      ring
    rw [heq, integral_const_mul]
    calc
      _ ≤ (3 / (2 * Real.pi)) * 2 :=
        mul_le_mul_of_nonneg_left be_sinc_fourth_firstMoment (by positivity)
      _ = 3 / Real.pi := by field_simp
      _ ≤ 1 := (div_le_one Real.pi_pos).2 (le_of_lt Real.pi_gt_three)
  refine ⟨hqpos, hqi, hqmi, hnorm, hmom, ?_⟩
  intro t ht
  rw [be_sinc_kernel_transform t, be_fourBox_data.2.2.1 t ht, mul_zero]

private theorem be_sinc_smoothing_law_data :
    let q : ℝ → ℝ := fun u => (3 / (2 * Real.pi)) * (Real.sinc u) ^ 4
    let Q : Measure ℝ := volume.withDensity (fun u => ENNReal.ofReal (q u))
    IsProbabilityMeasure Q ∧ Integrable (fun u : ℝ => u) Q ∧
      (∫ u : ℝ, |u| ∂Q) ≤ 1 ∧
      ∀ t : ℝ, 4 < |t| → charFun Q t = 0 := by
  let q : ℝ → ℝ := fun u => (3 / (2 * Real.pi)) * (Real.sinc u) ^ 4
  let Q : Measure ℝ := volume.withDensity (fun u => ENNReal.ofReal (q u))
  obtain ⟨hqpos, hqi, hqmi, hnorm, hmom, hband⟩ := be_sinc_kernel_data
  change (∀ u : ℝ, 0 ≤ q u) at hqpos
  change Integrable q at hqi
  change Integrable (fun u : ℝ => |u| * q u) at hqmi
  change (∫ u : ℝ, q u) = 1 at hnorm
  change (∫ u : ℝ, |u| * q u) ≤ 1 at hmom
  have hqm : Measurable q := by dsimp [q]; fun_prop
  have hQ : IsProbabilityMeasure Q := by
    constructor
    change volume.withDensity (fun u => ENNReal.ofReal (q u)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hqi (Filter.Eventually.of_forall hqpos), hnorm]
    exact ENNReal.ofReal_one
  have habs : Integrable (fun u : ℝ => |u|) Q := by
    apply (integrable_withDensity_iff hqm.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2
    simpa only [ENNReal.toReal_ofReal (hqpos _)] using hqmi
  have hId : Integrable (fun u : ℝ => u) Q := by
    exact habs.mono' measurable_id.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by simp)
  refine ⟨hQ, hId, ?_, ?_⟩
  · change (∫ u : ℝ, |u| ∂volume.withDensity (fun u => ENNReal.ofReal (q u))) ≤ 1
    rw [integral_withDensity_eq_integral_toReal_smul hqm.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal (hqpos _), smul_eq_mul, mul_comm] using hmom
  · intro t ht
    change charFun Q t = 0
    rw [charFun_apply_real]
    change (∫ u : ℝ, Complex.exp ((t : ℂ) * u * Complex.I)
      ∂volume.withDensity (fun u => ENNReal.ofReal (q u))) = 0
    rw [integral_withDensity_eq_integral_toReal_smul hqm.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hqpos _), RCLike.real_smul_eq_coe_mul]
    convert hband t ht using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by
      dsimp [q]
      push_cast
      ring

private theorem be_density_scale_integral
    (q : ℝ → ℝ) (c : ℝ) (hc : 0 < c) (f : ℝ → ℂ) :
    (∫ x : ℝ, ((c⁻¹ * q (c⁻¹ * x) : ℝ) : ℂ) * f x) =
      ∫ u : ℝ, (q u : ℂ) * f (c * u) := by
  have heq : (fun x : ℝ => ((c⁻¹ * q (c⁻¹ * x) : ℝ) : ℂ) * f x) =
      (fun x : ℝ => ((c⁻¹ : ℝ) : ℂ) *
        ((q (c⁻¹ * x) : ℂ) * f (c * (c⁻¹ * x)))) := by
    funext x
    rw [← mul_assoc c c⁻¹ x, mul_inv_cancel₀ hc.ne', one_mul]
    push_cast
    ring
  rw [heq, integral_const_mul,
    Measure.integral_comp_inv_mul_left (fun u : ℝ => (q u : ℂ) * f (c * u)) c,
    abs_of_pos hc, RCLike.real_smul_eq_coe_mul]
  push_cast
  have he : ((c⁻¹ : ℝ) : ℂ) * (c : ℂ) = 1 := by
    norm_cast
    exact inv_mul_cancel₀ hc.ne'
  calc
    _ = (((c⁻¹ : ℝ) : ℂ) * (c : ℂ)) *
        (∫ y : ℝ, (q y : ℂ) * f (c * y)) := by
      simp only [Complex.ofReal_inv]
      exact (mul_assoc _ _ _).symm
    _ = _ := by rw [he, one_mul]

private theorem be_scaled_sinc_kernel_data (c : ℝ) (hc : 0 < c) :
    let q : ℝ → ℝ := fun u => (3 / (2 * Real.pi)) * (Real.sinc u) ^ 4
    let K : ℝ → ℝ := fun y => c⁻¹ * q (c⁻¹ * y)
    (∀ y : ℝ, 0 ≤ K y) ∧ Integrable K ∧ Continuous K ∧
      (∀ y : ℝ, K y ≤ c⁻¹ * (3 / (2 * Real.pi))) ∧
      (∫ y : ℝ, K y) = 1 ∧
      Integrable (fun y : ℝ => |y| * K y) ∧
      (∫ y : ℝ, |y| * K y) ≤ c ∧
      ∀ t : ℝ, 4 < |c * t| →
        (∫ y : ℝ, Complex.exp ((t * y : ℝ) * Complex.I) * (K y : ℂ)) = 0 := by
  let q : ℝ → ℝ := fun u => (3 / (2 * Real.pi)) * (Real.sinc u) ^ 4
  let K : ℝ → ℝ := fun y => c⁻¹ * q (c⁻¹ * y)
  obtain ⟨hqpos, hqi, hqmi, hnorm, hmom, hband⟩ := be_sinc_kernel_data
  change (∀ u : ℝ, 0 ≤ q u) at hqpos
  change Integrable q at hqi
  change Integrable (fun u : ℝ => |u| * q u) at hqmi
  change (∫ u : ℝ, q u) = 1 at hnorm
  change (∫ u : ℝ, |u| * q u) ≤ 1 at hmom
  have hKpos (y : ℝ) : 0 ≤ K y := mul_nonneg (inv_nonneg.mpr hc.le) (hqpos _)
  have hKi : Integrable K := (hqi.comp_mul_left' (inv_ne_zero hc.ne')).const_mul _
  have hKc : Continuous K := by dsimp [K, q]; fun_prop
  have hKb (y : ℝ) : K y ≤ c⁻¹ * (3 / (2 * Real.pi)) := by
    have hs : (Real.sinc (c⁻¹ * y)) ^ 4 ≤ 1 := by
      have hh := pow_le_pow_left₀ (abs_nonneg (Real.sinc (c⁻¹ * y)))
        (Real.abs_sinc_le_one (c⁻¹ * y)) 4
      simpa only [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, one_pow] using hh
    exact mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 3 / (2 * Real.pi))).trans_eq
        (mul_one _)) (inv_nonneg.mpr hc.le)
  have hKn : (∫ y : ℝ, K y) = 1 := by
    change (∫ y : ℝ, c⁻¹ * q (c⁻¹ * y)) = 1
    rw [integral_const_mul, Measure.integral_comp_inv_mul_left q c,
      abs_of_pos hc, hnorm, smul_eq_mul, mul_one, inv_mul_cancel₀ hc.ne']
  have hweight : (fun y : ℝ => |y| * K y) =
      (fun y : ℝ => |c⁻¹ * y| * q (c⁻¹ * y)) := by
    funext y
    dsimp [K]
    rw [abs_mul, abs_inv, abs_of_pos hc]
    ring
  have hKmi : Integrable (fun y : ℝ => |y| * K y) := by
    rw [hweight]
    exact hqmi.comp_mul_left' (inv_ne_zero hc.ne')
  have hKm : (∫ y : ℝ, |y| * K y) ≤ c := by
    rw [hweight, Measure.integral_comp_inv_mul_left (fun u : ℝ => |u| * q u) c,
      abs_of_pos hc, smul_eq_mul]
    exact (mul_le_mul_of_nonneg_left hmom hc.le).trans_eq (mul_one c)
  refine ⟨hKpos, hKi, hKc, hKb, hKn, hKmi, hKm, ?_⟩
  intro t ht
  change (∫ y : ℝ, Complex.exp ((t * y : ℝ) * Complex.I) * (K y : ℂ)) = 0
  have heq : (fun y : ℝ => Complex.exp ((t * y : ℝ) * Complex.I) * (K y : ℂ)) =
      (fun y : ℝ => ((c⁻¹ * q (c⁻¹ * y) : ℝ) : ℂ) *
        Complex.exp ((t * y : ℝ) * Complex.I)) := by
    funext y
    dsimp [K]
    exact mul_comm _ _
  rw [heq, be_density_scale_integral q c hc]
  convert hband (c * t) ht using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    dsimp only
    have he : t * (c * u) = (c * t) * u := by ring
    rw [he]
    dsimp [q]
    push_cast
    ring

private theorem be_scaled_sinc_fourier (c : ℝ) (hc : 0 < c) (xi : ℝ) :
    let q : ℝ → ℝ := fun u => (3 / (2 * Real.pi)) * (Real.sinc u) ^ 4
    let K : ℝ → ℝ := fun y => c⁻¹ * q (c⁻¹ * y)
    ‖𝓕 (fun y : ℝ => (K y : ℂ)) xi‖ ≤ 1 ∧
      (4 < |c * (-2 * Real.pi * xi)| →
        𝓕 (fun y : ℝ => (K y : ℂ)) xi = 0) := by
  let q : ℝ → ℝ := fun u => (3 / (2 * Real.pi)) * (Real.sinc u) ^ 4
  let K : ℝ → ℝ := fun y => c⁻¹ * q (c⁻¹ * y)
  obtain ⟨hKpos, hKi, _, _, hKn, _, _, hband⟩ := be_scaled_sinc_kernel_data c hc
  change (∀ y : ℝ, 0 ≤ K y) at hKpos
  change Integrable K at hKi
  change (∫ y : ℝ, K y) = 1 at hKn
  have heq : 𝓕 (fun y : ℝ => (K y : ℂ)) xi =
      ∫ y : ℝ, Complex.exp (((-2 * Real.pi * xi) * y : ℝ) * Complex.I) * (K y : ℂ) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      simp only [smul_eq_mul]
      congr 1
      congr 1
      push_cast
      ring
  change ‖𝓕 (fun y : ℝ => (K y : ℂ)) xi‖ ≤ 1 ∧
    (4 < |c * (-2 * Real.pi * xi)| → 𝓕 (fun y : ℝ => (K y : ℂ)) xi = 0)
  rw [heq]
  constructor
  · calc
      _ ≤ ∫ y : ℝ, K y := by
        apply norm_integral_le_of_norm_le hKi
        exact Filter.Eventually.of_forall fun y => by
          simp [norm_mul, Complex.norm_exp, Complex.mul_re,
            abs_of_nonneg (hKpos y)]
      _ = 1 := hKn
  · intro hxi
    exact hband (-2 * Real.pi * xi) hxi

private theorem be_cdf_difference_fourier_norm
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : Integrable (fun z : ℝ => z) mu)
    (hnu : Integrable (fun z : ℝ => z) nu) (xi : ℝ) (hxi : xi ≠ 0) :
    ‖𝓕 (fun x : ℝ => ((mu.real (Set.Iic x) - nu.real (Set.Iic x) : ℝ) : ℂ)) xi‖ =
      cdfFourierError mu nu (-2 * Real.pi * xi) := by
  have ht : -2 * Real.pi * xi ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hxi
  have heq :
      𝓕 (fun x : ℝ => ((mu.real (Set.Iic x) - nu.real (Set.Iic x) : ℝ) : ℂ)) xi =
      ∫ x : ℝ, Complex.exp (((-2 * Real.pi * xi) * x : ℝ) * Complex.I) *
        ((mu.real (Set.Iic x) - nu.real (Set.Iic x) : ℝ) : ℂ) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [smul_eq_mul]
      congr 1
      congr 1
      push_cast
      ring
  rw [heq, be_cdf_difference_fourier mu nu hmu hnu _ ht]
  simp only [cdfFourierError, norm_div, norm_neg, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one]
  congr 1
  rw [abs_mul, abs_mul, abs_neg]

private theorem be_convolution_inverse_bound
    (f g : ℝ → ℂ) (D : ℝ → ℝ)
    (hf : Integrable f) (hg : Integrable g) (hgc : Continuous g)
    (hgb : BddAbove (Set.range fun x => ‖g x‖))
    (hD : Integrable D)
    (hbound : ∀ᵐ xi : ℝ, ‖𝓕 f xi * 𝓕 g xi‖ ≤ D xi) (x : ℝ) :
    ‖(f ⋆[.mul ℂ ℂ] g) x‖ ≤ ∫ xi : ℝ, D xi := by
  let S : ℝ → ℂ := f ⋆[.mul ℂ ℂ] g
  have hSi : Integrable S := hf.integrable_convolution (.mul ℂ ℂ) hg
  have hSc : Continuous S :=
    hgb.continuous_convolution_right_of_integrable (.mul ℂ ℂ) hf hgc
  have hSF : ∀ᵐ xi : ℝ, ‖𝓕 S xi‖ ≤ D xi := by
    filter_upwards [hbound] with xi hxi
    simpa only [S, Real.fourier_mul_convolution_eq hf hg xi] using hxi
  have hFc : Continuous (𝓕 S) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hSi
  have hFi : Integrable (𝓕 S) := hD.mono' hFc.aestronglyMeasurable hSF
  change ‖S x‖ ≤ ∫ xi : ℝ, D xi
  rw [← hSi.fourierInv_fourier_eq hFi (hSc.continuousAt (x := x)),
    Real.fourierInv_eq']
  apply norm_integral_le_of_norm_le hD
  filter_upwards [hSF] with xi hxi
  simpa only [norm_smul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self,
    Real.exp_zero, one_mul] using hxi

private theorem be_smoothed_cdf_bound
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : Integrable (fun z : ℝ => z) mu)
    (hnu : Integrable (fun z : ℝ => z) nu) (T : ℝ) (hT : 0 < T) (x : ℝ) :
    let q : ℝ → ℝ := fun u => (3 / (2 * Real.pi)) * (Real.sinc u) ^ 4
    let K : ℝ → ℝ := fun y => (4 / T)⁻¹ * q ((4 / T)⁻¹ * y)
    |∫ y : ℝ, (mu.real (Set.Iic (x - y)) - nu.real (Set.Iic (x - y))) * K y| ≤
      (∫ t : ℝ in Set.Icc (-T) T, cdfFourierError mu nu t) / (2 * Real.pi) := by
  let c : ℝ := 4 / T
  have hc : 0 < c := by dsimp [c]; positivity
  let q : ℝ → ℝ := fun u => (3 / (2 * Real.pi)) * (Real.sinc u) ^ 4
  let K : ℝ → ℝ := fun y => c⁻¹ * q (c⁻¹ * y)
  let H : ℝ → ℂ := fun u => ((mu.real (Set.Iic u) - nu.real (Set.Iic u) : ℝ) : ℂ)
  let D : ℝ → ℝ := (Set.Icc (-T) T).indicator (cdfFourierError mu nu)
  let a : ℝ := -2 * Real.pi
  have ha : a ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hHi : Integrable H := (be_integrable_cdf_difference mu nu hmu hnu).ofReal
  obtain ⟨hKpos, hKi, hKc, hKb, hKn, hKmi, hKm, hband⟩ :=
    be_scaled_sinc_kernel_data c hc
  change (∀ y : ℝ, 0 ≤ K y) at hKpos
  change Integrable K at hKi
  change Continuous K at hKc
  change (∀ y : ℝ, K y ≤ c⁻¹ * (3 / (2 * Real.pi))) at hKb
  have hKCi : Integrable (fun y => (K y : ℂ)) := hKi.ofReal
  have hKCc : Continuous (fun y => (K y : ℂ)) := by fun_prop
  have hKCb : BddAbove (Set.range fun y => ‖(K y : ℂ)‖) := by
    refine ⟨c⁻¹ * (3 / (2 * Real.pi)), ?_⟩
    rintro _ ⟨y, rfl⟩
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hKpos y)] using hKb y
  have hDi : Integrable D := (integrable_indicator_iff measurableSet_Icc).2
    (be_integrableOn_cdfFourierError mu nu hmu hnu T)
  have hDas : Integrable (fun xi : ℝ => D (a * xi)) := hDi.comp_mul_left' ha
  have hbound : ∀ᵐ xi : ℝ,
      ‖𝓕 H xi * 𝓕 (fun y => (K y : ℂ)) xi‖ ≤ D (a * xi) := by
    filter_upwards [(volume : Measure ℝ).ae_ne 0] with xi hxi
    obtain ⟨hFn, hF0⟩ := be_scaled_sinc_fourier c hc xi
    change ‖𝓕 (fun y => (K y : ℂ)) xi‖ ≤ 1 at hFn
    change (4 < |c * (a * xi)| → 𝓕 (fun y => (K y : ℂ)) xi = 0) at hF0
    by_cases ht : a * xi ∈ Set.Icc (-T) T
    · simp only [D, Set.indicator_of_mem ht, norm_mul]
      calc
        _ ≤ ‖𝓕 H xi‖ * 1 := mul_le_mul_of_nonneg_left hFn (norm_nonneg _)
        _ = cdfFourierError mu nu (a * xi) := by
          rw [mul_one]
          exact be_cdf_difference_fourier_norm mu nu hmu hnu xi hxi
    · have ht' : T < |a * xi| := by
        have hh : ¬ |a * xi| ≤ T := by
          simpa only [abs_le, Set.mem_Icc] using ht
        exact lt_of_not_ge hh
      have hct : 4 < |c * (a * xi)| := by
        rw [abs_mul, abs_of_pos hc]
        calc
          4 = c * T := by dsimp [c]; field_simp
          _ < c * |a * xi| := mul_lt_mul_of_pos_left ht' hc
      rw [hF0 hct, mul_zero, norm_zero]
      simp only [D, Set.indicator_of_notMem ht, le_refl]
  have hS := be_convolution_inverse_bound H (fun y => (K y : ℂ))
    (fun xi : ℝ => D (a * xi)) hHi hKCi hKCc hKCb hDas hbound x
  have hSreal : (H ⋆[.mul ℂ ℂ] (fun y => (K y : ℂ))) x =
      ((∫ y : ℝ, (mu.real (Set.Iic (x - y)) - nu.real (Set.Iic (x - y))) * K y : ℝ) : ℂ) := by
    rw [convolution_mul_swap, ← integral_complex_ofReal]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp [H]
      push_cast
      rfl
  rw [hSreal, Complex.norm_real, Real.norm_eq_abs,
    Measure.integral_comp_mul_left D a, smul_eq_mul, abs_inv] at hS
  have haa : |a| = 2 * Real.pi := by
    dsimp [a]
    rw [abs_mul]
    simp only [abs_neg, abs_of_pos Real.pi_pos]
    norm_num
  rw [haa] at hS
  dsimp only [D] at hS
  rw [integral_indicator measurableSet_Icc] at hS
  change |∫ y : ℝ, (mu.real (Set.Iic (x - y)) - nu.real (Set.Iic (x - y))) * K y| ≤ _
  simpa only [div_eq_mul_inv, mul_comm] using hS

private theorem be_unsmoothing_pointwise
    (f g : ℝ → ℝ) (hf : Monotone f)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y : ℝ, |g x - g y| ≤ L * |x - y|)
    (D : ℝ) (hD : ∀ x : ℝ, |f x - g x| ≤ D)
    (h : ℝ) (hh : 0 ≤ h) (x y : ℝ) :
    (f x - g x ≤ (f (x + h - y) - g (x + h - y)) +
      L * (h + |y|) + 2 * D * (Set.Ioi h).indicator (fun _ : ℝ => 1) y) ∧
    (-(f x - g x) ≤ -(f (x - h - y) - g (x - h - y)) +
      L * (h + |y|) + 2 * D * (Set.Iio (-h)).indicator (fun _ : ℝ => 1) y) := by
  have hp : 0 ≤ L * (h + |y|) := mul_nonneg hL (add_nonneg hh (abs_nonneg y))
  constructor
  · by_cases hy : h < y
    · simp only [Set.indicator_of_mem (show y ∈ Set.Ioi h from hy), mul_one]
      have h1 := (abs_le.mp (hD x)).2
      have h2 := (abs_le.mp (hD (x + h - y))).1
      linarith
    · simp only [Set.indicator_of_notMem (show y ∉ Set.Ioi h from hy), mul_zero,
        add_zero]
      have hfx : f x ≤ f (x + h - y) := hf (by linarith)
      have he : (x + h - y) - x = h - y := by ring
      have ha : |(x + h - y) - x| ≤ h + |y| := by
        rw [he]
        simpa only [abs_of_nonneg hh] using abs_sub h y
      have hg := (le_abs_self (g (x + h - y) - g x)).trans
        ((hLip (x + h - y) x).trans (mul_le_mul_of_nonneg_left ha hL))
      linarith
  · by_cases hy : y < -h
    · simp only [Set.indicator_of_mem (show y ∈ Set.Iio (-h) from hy), mul_one]
      have h1 := (abs_le.mp (hD x)).1
      have h2 := (abs_le.mp (hD (x - h - y))).2
      linarith
    · simp only [Set.indicator_of_notMem (show y ∉ Set.Iio (-h) from hy), mul_zero,
        add_zero]
      have hfx : f (x - h - y) ≤ f x := hf (by linarith)
      have he : x - (x - h - y) = h + y := by ring
      have ha : |x - (x - h - y)| ≤ h + |y| := by
        rw [he]
        simpa only [abs_of_nonneg hh] using abs_add_le h y
      have hg := (le_abs_self (g x - g (x - h - y))).trans
        ((hLip x (x - h - y)).trans (mul_le_mul_of_nonneg_left ha hL))
      linarith

private theorem be_integrated_unsmoothing
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : Integrable (fun y : ℝ => y) Q)
    (F : ℝ → ℝ) (hF : Integrable F Q)
    (s : Set ℝ) (hs : MeasurableSet s)
    (A L h c D v : ℝ) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hM : (∫ y : ℝ, |y| ∂Q) ≤ c)
    (htail : Q.real s ≤ 1 / 4)
    (hA : (∫ y : ℝ, F y ∂Q) ≤ A)
    (hpoint : ∀ y : ℝ, v ≤ F y + L * (h + |y|) +
      2 * D * s.indicator (fun _ : ℝ => 1) y) :
    v ≤ A + L * (h + c) + D / 2 := by
  have hp : Integrable (fun y : ℝ => L * (h + |y|)) Q :=
    ((integrable_const h).add hQ.abs).const_mul L
  have hb : Integrable (fun y : ℝ => 2 * D * s.indicator (fun _ : ℝ => 1) y) Q :=
    ((integrable_const (1 : ℝ)).indicator hs).const_mul (2 * D)
  have hi := integral_mono (integrable_const v) ((hF.add hp).add hb) hpoint
  have hpi : (∫ y : ℝ, L * (h + |y|) ∂Q) = L * (h + ∫ y : ℝ, |y| ∂Q) := by
    rw [integral_const_mul, integral_add (integrable_const h) hQ.abs]
    simp only [integral_const, probReal_univ, one_smul]
  have hbi : (∫ y : ℝ, 2 * D * s.indicator (fun _ : ℝ => 1) y ∂Q) =
      2 * D * Q.real s := by
    rw [integral_const_mul, integral_indicator hs, integral_const]
    simp [smul_eq_mul, Measure.real_def]
  have hFp : Integrable (fun y : ℝ => F y + L * (h + |y|)) Q := hF.add hp
  simp only [Pi.add_apply] at hi
  rw [integral_add hFp hb, integral_add hF hp, hpi, hbi] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  have hpM := mul_le_mul_of_nonneg_left (add_le_add_left hM h) hL
  have hpT := mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ 2 * D)
  linarith

private theorem be_atomic_unsmoothing
    (f g : ℝ → ℝ) (hf : Monotone f) (hfm : Measurable f) (hgm : Measurable g)
    (hfg : ∀ x : ℝ, |f x - g x| ≤ 1)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y : ℝ, |g x - g y| ≤ L * |x - y|)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : Integrable (fun y : ℝ => y) Q)
    (h c : ℝ) (hh : 0 ≤ h)
    (hM : (∫ y : ℝ, |y| ∂Q) ≤ c)
    (htailP : Q.real (Set.Ioi h) ≤ 1 / 4)
    (htailN : Q.real (Set.Iio (-h)) ≤ 1 / 4)
    (A : ℝ)
    (hA : ∀ x : ℝ, |∫ y : ℝ, (f (x - y) - g (x - y)) ∂Q| ≤ A) :
    ∀ x : ℝ, |f x - g x| ≤ 2 * A + 2 * L * (h + c) := by
  let D : ℝ := sSup (Set.range fun x : ℝ => |f x - g x|)
  have hne : (Set.range fun x : ℝ => |f x - g x|).Nonempty := ⟨_, 0, rfl⟩
  have hbdd : BddAbove (Set.range fun x : ℝ => |f x - g x|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hfg x
  have hD (x : ℝ) : |f x - g x| ≤ D := le_csSup hbdd ⟨x, rfl⟩
  have hDpos : 0 ≤ D := (abs_nonneg (f 0 - g 0)).trans (hD 0)
  have hFi (z : ℝ) : Integrable (fun y : ℝ => f (z - y) - g (z - y)) Q := by
    apply (integrable_const (1 : ℝ)).mono'
    · exact ((hfm.comp (by fun_prop)).sub (hgm.comp (by fun_prop))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs] using hfg (z - y)
  have hp (x : ℝ) : f x - g x ≤ A + L * (h + c) + D / 2 := by
    apply be_integrated_unsmoothing Q hQ
      (fun y => f (x + h - y) - g (x + h - y)) (hFi (x + h))
      (Set.Ioi h) measurableSet_Ioi A L h c D (f x - g x) hL hDpos hM htailP
    · exact (le_abs_self _).trans (hA (x + h))
    · intro y
      exact (be_unsmoothing_pointwise f g hf L hL hLip D hD h hh x y).1
  have hn (x : ℝ) : -(f x - g x) ≤ A + L * (h + c) + D / 2 := by
    apply be_integrated_unsmoothing Q hQ
      (fun y => -(f (x - h - y) - g (x - h - y))) (hFi (x - h)).neg
      (Set.Iio (-h)) measurableSet_Iio A L h c D (-(f x - g x))
      hL hDpos hM htailN
    · rw [integral_neg]
      exact (neg_le_abs _).trans (hA (x - h))
    · intro y
      exact (be_unsmoothing_pointwise f g hf L hL hLip D hD h hh x y).2
  have hDs : D ≤ A + L * (h + c) + D / 2 := by
    apply csSup_le hne
    rintro _ ⟨x, rfl⟩
    exact abs_le.mpr ⟨by linarith [hn x], hp x⟩
  intro x
  linarith [hD x]

private theorem be_abs_tail_probability
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : Integrable (fun y : ℝ => y) Q)
    (s : Set ℝ) (hs : MeasurableSet s) (h : ℝ) (hh : 0 < h)
    (hsabs : ∀ y ∈ s, h ≤ |y|) :
    Q.real s ≤ (∫ y : ℝ, |y| ∂Q) / h := by
  have hi := integral_mono
    (((integrable_const (1 : ℝ)).indicator hs).const_mul h) hQ.abs
    (show ∀ y : ℝ, h * s.indicator (fun _ : ℝ => 1) y ≤ |y| from fun y => by
      by_cases hy : y ∈ s
      · simpa only [Set.indicator_of_mem hy, mul_one] using hsabs y hy
      · simp only [Set.indicator_of_notMem hy, mul_zero]
        exact abs_nonneg y)
  rw [integral_const_mul, integral_indicator hs, integral_const] at hi
  simp [smul_eq_mul, Measure.real_def] at hi
  exact (le_div_iff₀ hh).2 (by simpa only [mul_comm, Measure.real_def] using hi)

theorem cdf_error_le_fourier_smoothing
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu1 : Integrable (fun z : ℝ => z) mu)
    (hnu1 : Integrable (fun z : ℝ => z) nu)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y : ℝ,
      |nu.real (Set.Iic x) - nu.real (Set.Iic y)| ≤ L * |x - y|)
    (T : ℝ) (hT : 0 < T) :
    IntegrableOn (cdfFourierError mu nu) (Set.Icc (-T) T) ∧
      ∀ x : ℝ,
        |mu.real (Set.Iic x) - nu.real (Set.Iic x)| ≤
          2 * (∫ t : ℝ in Set.Icc (-T) T, cdfFourierError mu nu t) +
            64 * L / T := by
  refine ⟨be_integrableOn_cdfFourierError mu nu hmu1 hnu1 T, ?_⟩
  let c : ℝ := 4 / T
  have hc : 0 < c := by dsimp [c]; positivity
  let h : ℝ := 16 / T
  have hh : 0 < h := by dsimp [h]; positivity
  let q : ℝ → ℝ := fun u => (3 / (2 * Real.pi)) * (Real.sinc u) ^ 4
  let K : ℝ → ℝ := fun y => c⁻¹ * q (c⁻¹ * y)
  let Q : Measure ℝ := volume.withDensity (fun y => ENNReal.ofReal (K y))
  let I : ℝ := ∫ t : ℝ in Set.Icc (-T) T, cdfFourierError mu nu t
  obtain ⟨hKpos, hKi, hKc, hKb, hKn, hKmi, hKm, hband⟩ :=
    be_scaled_sinc_kernel_data c hc
  change (∀ y : ℝ, 0 ≤ K y) at hKpos
  change Integrable K at hKi
  change Continuous K at hKc
  change (∫ y : ℝ, K y) = 1 at hKn
  change Integrable (fun y : ℝ => |y| * K y) at hKmi
  change (∫ y : ℝ, |y| * K y) ≤ c at hKm
  have hKmbl : Measurable K := hKc.measurable
  have hQprob : IsProbabilityMeasure Q := by
    constructor
    change volume.withDensity (fun y => ENNReal.ofReal (K y)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hKi (Filter.Eventually.of_forall hKpos), hKn]
    exact ENNReal.ofReal_one
  letI : IsProbabilityMeasure Q := hQprob
  have hQabs : Integrable (fun y : ℝ => |y|) Q := by
    apply (integrable_withDensity_iff hKmbl.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2
    simpa only [ENNReal.toReal_ofReal (hKpos _)] using hKmi
  have hQid : Integrable (fun y : ℝ => y) Q :=
    hQabs.mono' measurable_id.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simp)
  have hQmoment : (∫ y : ℝ, |y| ∂Q) ≤ c := by
    change (∫ y : ℝ, |y| ∂volume.withDensity (fun y => ENNReal.ofReal (K y))) ≤ c
    rw [integral_withDensity_eq_integral_toReal_smul hKmbl.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal (hKpos _), smul_eq_mul, mul_comm] using hKm
  have hratio : c / h = 1 / 4 := by dsimp [c, h]; field_simp; ring
  have htailP : Q.real (Set.Ioi h) ≤ 1 / 4 := by
    calc
      _ ≤ (∫ y : ℝ, |y| ∂Q) / h :=
        be_abs_tail_probability Q hQid (Set.Ioi h) measurableSet_Ioi h hh
          (fun y hy => (show h ≤ y from hy.le).trans (le_abs_self y))
      _ ≤ c / h := div_le_div_of_nonneg_right hQmoment hh.le
      _ = _ := hratio
  have htailN : Q.real (Set.Iio (-h)) ≤ 1 / 4 := by
    calc
      _ ≤ (∫ y : ℝ, |y| ∂Q) / h :=
        be_abs_tail_probability Q hQid (Set.Iio (-h)) measurableSet_Iio h hh
          (fun y hy => (show h ≤ -y by linarith [show y < -h from hy]).trans (neg_le_abs y))
      _ ≤ c / h := div_le_div_of_nonneg_right hQmoment hh.le
      _ = _ := hratio
  have hS (x : ℝ) :
      |∫ y : ℝ, (mu.real (Set.Iic (x - y)) - nu.real (Set.Iic (x - y))) ∂Q| ≤
        I / (2 * Real.pi) := by
    change |∫ y : ℝ, (mu.real (Set.Iic (x - y)) - nu.real (Set.Iic (x - y)))
      ∂volume.withDensity (fun y => ENNReal.ofReal (K y))| ≤ _
    rw [integral_withDensity_eq_integral_toReal_smul hKmbl.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hKpos _), smul_eq_mul]
    simpa only [K, c, q, I, mul_comm] using be_smoothed_cdf_bound mu nu hmu1 hnu1 T hT x
  have hm (rho : Measure ℝ) [IsProbabilityMeasure rho] :
      Monotone (fun x : ℝ => rho.real (Set.Iic x)) := by
    intro x y hxy
    exact measureReal_mono (Set.Iic_subset_Iic.mpr hxy)
  have hb (x : ℝ) : |mu.real (Set.Iic x) - nu.real (Set.Iic x)| ≤ 1 := by
    have hmp : 0 ≤ mu.real (Set.Iic x) := ENNReal.toReal_nonneg
    have hnp : 0 ≤ nu.real (Set.Iic x) := ENNReal.toReal_nonneg
    have hm1 : mu.real (Set.Iic x) ≤ 1 := by
      simpa only [probReal_univ] using
        (measureReal_mono (μ := mu) (Set.subset_univ (Set.Iic x)))
    have hn1 : nu.real (Set.Iic x) ≤ 1 := by
      simpa only [probReal_univ] using
        (measureReal_mono (μ := nu) (Set.subset_univ (Set.Iic x)))
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hU := be_atomic_unsmoothing
    (fun x : ℝ => mu.real (Set.Iic x)) (fun x : ℝ => nu.real (Set.Iic x))
    (hm mu) (hm mu).measurable (hm nu).measurable hb L hL hLip
    Q hQid h c hh.le hQmoment htailP htailN (I / (2 * Real.pi)) hS
  have hI : 0 ≤ I := integral_nonneg fun t => be_cdfFourierError_nonneg mu nu t
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hratioI : I / (2 * Real.pi) ≤ I :=
    (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2 (by nlinarith)
  have hpen : 2 * L * (h + c) ≤ 64 * L / T := by
    dsimp [h, c]
    have hpenEq : 2 * L * (16 / T + 4 / T) = 40 * L / T := by ring
    rw [hpenEq]
    exact div_le_div_of_nonneg_right (by nlinarith) hT.le
  intro x
  change |mu.real (Set.Iic x) - nu.real (Set.Iic x)| ≤ 2 * I + 64 * L / T
  linarith [hU x]

private theorem be_third_moment_memLp
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu) : MemLp id 3 nu := by
  apply (integrable_norm_rpow_iff (p := (3 : ENNReal))
    measurable_id.aestronglyMeasurable (by norm_num) (by norm_num)).1
  simp_rw [← Real.rpow_natCast] at h3
  simpa only [ENNReal.toReal_ofNat, Real.norm_eq_abs, id_eq, Nat.cast_ofNat] using h3

private theorem be_third_moment_ge_one
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂nu) = 1) :
    1 ≤ ∫ z : ℝ, |z| ^ 3 ∂nu := by
  have h2 : Integrable (fun z : ℝ => z ^ 2) nu :=
    Integrable.of_integral_ne_zero (by rw [hsecond]; norm_num)
  have hpt (z : ℝ) : 3 * z ^ 2 ≤ 2 * |z| ^ 3 + 1 := by
    have hh := mul_nonneg (sq_nonneg (|z| - 1))
      (by positivity : 0 ≤ 2 * |z| + 1)
    nlinarith only [hh, sq_abs z]
  have hi := integral_mono (h2.const_mul 3)
    ((h3.const_mul 2).add (integrable_const (1 : ℝ))) hpt
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add (h3.const_mul 2) (integrable_const (1 : ℝ)),
    integral_const_mul, hsecond] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  linarith

private theorem be_charFun_third_deriv_bound
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu) (u : ℝ) :
    ‖iteratedDeriv 3 (charFun nu) u‖ ≤ ∫ z : ℝ, |z| ^ 3 ∂nu := by
  rw [iteratedDeriv_charFun (be_third_moment_memLp nu h3), norm_mul]
  simp only [norm_pow, Complex.norm_I, one_pow, one_mul]
  apply norm_integral_le_of_norm_le h3
  exact Filter.Eventually.of_forall fun z => by
    simp [norm_mul, norm_pow, Complex.norm_exp, Complex.mul_re]

private theorem be_unitVariance_charFun_taylor_nonneg
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (u : ℝ) (hu : 0 ≤ u) :
    ‖charFun nu u - (1 - (u : ℂ) ^ 2 / 2)‖ ≤
      (∫ z : ℝ, |z| ^ 3 ∂nu) * u ^ 3 / 2 := by
  rcases eq_or_lt_of_le hu with rfl | hu
  · simp
  have hLp := be_third_moment_memLp nu h3
  have hcf : ContDiff ℝ (3 : ℕ) (charFun nu) := contDiff_charFun hLp
  have hpoly : taylorWithinEval (charFun nu) 2 (Set.Icc 0 u) 0 u =
      taylorWithinEval (charFun nu) 2 Set.univ 0 u := by
    simp only [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    have hj3 : j ≤ 3 := by simp only [Finset.mem_range] at hj; omega
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hu)
      ((hcf.of_le (by exact_mod_cast hj3)).contDiffAt) ⟨le_rfl, hu.le⟩,
      iteratedDerivWithin_univ]
  have hpoly0 : taylorWithinEval (charFun nu) 2 Set.univ 0 u =
      1 - (u : ℂ) ^ 2 / 2 := by
    rw [taylorWithinEval_charFun_zero (hLp.mono_exponent (by norm_num))]
    simp [Finset.sum_range_succ, hmean, hsecond]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hr := taylor_mean_remainder_bound (n := 2) hu.le hcf.contDiffOn
    (show u ∈ Set.Icc 0 u from ⟨hu.le, le_rfl⟩)
    (C := ∫ z : ℝ, |z| ^ 3 ∂nu) (fun y hy => by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hu) hcf.contDiffAt hy]
      exact be_charFun_third_deriv_bound nu h3 y)
  rw [hpoly, hpoly0] at hr
  simpa only [sub_zero, Nat.factorial_two, Nat.cast_ofNat] using hr

private theorem be_unitVariance_charFun_taylor
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂nu) = 1) (u : ℝ) :
    ‖charFun nu u - (1 - (u : ℂ) ^ 2 / 2)‖ ≤
      (∫ z : ℝ, |z| ^ 3 ∂nu) * |u| ^ 3 / 2 := by
  by_cases hu : 0 ≤ u
  · simpa only [abs_of_nonneg hu] using
      be_unitVariance_charFun_taylor_nonneg nu h3 hmean hsecond u hu
  · have hr := be_unitVariance_charFun_taylor_nonneg nu h3 hmean hsecond (-u)
      (by linarith)
    have he : (starRingEnd ℂ) (1 - (u : ℂ) ^ 2 / 2) =
        1 - (u : ℂ) ^ 2 / 2 := by
      have hp : (1 : ℂ) - (u : ℂ) ^ 2 / 2 = ((1 - u ^ 2 / 2 : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [hp]
      exact Complex.conj_ofReal _
    rw [charFun_neg, Complex.ofReal_neg, neg_sq, ← he, ← map_sub] at hr
    simpa only [Complex.norm_conj, abs_of_neg (lt_of_not_ge hu)] using hr

private theorem be_unitVariance_charFun_band
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂nu) = 1) (u : ℝ)
    (hu : (∫ z : ℝ, |z| ^ 3 ∂nu) * |u| ≤ 1 / 2) :
    ‖charFun nu u‖ ≤ Real.exp (-u ^ 2 / 4) ∧
      ‖charFun nu u - (Real.exp (-u ^ 2 / 2) : ℂ)‖ ≤
        (5 / 8 : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂nu) * |u| ^ 3 := by
  let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
  have hb : 1 ≤ beta := be_third_moment_ge_one nu h3 hsecond
  have hba : beta * |u| ≤ 1 / 2 := hu
  have huabs : |u| ≤ 1 / 2 := by nlinarith [abs_nonneg u]
  have hu2 : u ^ 2 ≤ 1 / 4 := by
    have hh := mul_self_le_mul_self (abs_nonneg u) huabs
    nlinarith only [hh, sq_abs u]
  have hr := be_unitVariance_charFun_taylor nu h3 hmean hsecond u
  change ‖charFun nu u - (1 - (u : ℂ) ^ 2 / 2)‖ ≤ beta * |u| ^ 3 / 2 at hr
  have hpoly : ‖(1 : ℂ) - (u : ℂ) ^ 2 / 2‖ = 1 - u ^ 2 / 2 := by
    have he : (1 : ℂ) - (u : ℂ) ^ 2 / 2 = ((1 - u ^ 2 / 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [he, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - u ^ 2 / 2)]
  have hcubic : beta * |u| ^ 3 / 2 ≤ u ^ 2 / 4 := by
    have hh := mul_le_mul_of_nonneg_right hba (sq_nonneg |u|)
    nlinarith only [hh, sq_abs u]
  have hnorm : ‖charFun nu u‖ ≤ 1 - u ^ 2 / 4 := by
    have hh := norm_sub_le (charFun nu u - (1 - (u : ℂ) ^ 2 / 2))
      (-(1 - (u : ℂ) ^ 2 / 2))
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg, hpoly] at hh
    linarith
  constructor
  · exact hnorm.trans (by convert Real.add_one_le_exp (-u ^ 2 / 4) using 1 <;> ring)
  · have hgauss := Real.norm_exp_sub_one_sub_id_le
      (x := -u ^ 2 / 2) (by
        rw [Real.norm_eq_abs, abs_of_nonpos (by nlinarith : -u ^ 2 / 2 ≤ 0)]
        linarith)
    have hgauss' : ‖(1 : ℂ) - (u : ℂ) ^ 2 / 2 -
        (Real.exp (-u ^ 2 / 2) : ℂ)‖ ≤ u ^ 4 / 4 := by
      have heq : (1 : ℂ) - (u : ℂ) ^ 2 / 2 - (Real.exp (-u ^ 2 / 2) : ℂ) =
          -(((Real.exp (-u ^ 2 / 2) - 1 - (-u ^ 2 / 2) : ℝ) : ℂ)) := by
        push_cast
        ring
      rw [heq, norm_neg, Complex.norm_real]
      convert hgauss using 1 <;> simp only [Real.norm_eq_abs, sq_abs] <;> ring
    have hfour : u ^ 4 / 4 ≤ beta * |u| ^ 3 / 8 := by
      have hh := mul_le_mul_of_nonneg_right huabs (pow_nonneg (abs_nonneg u) 3)
      have hh' := mul_le_mul_of_nonneg_right hb (pow_nonneg (abs_nonneg u) 3)
      have he : |u| ^ 4 = u ^ 4 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
      nlinarith only [hh, hh', he]
    calc
      _ ≤ ‖charFun nu u - (1 - (u : ℂ) ^ 2 / 2)‖ +
          ‖(1 : ℂ) - (u : ℂ) ^ 2 / 2 - (Real.exp (-u ^ 2 / 2) : ℂ)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ beta * |u| ^ 3 / 2 + u ^ 4 / 4 := add_le_add hr hgauss'
      _ ≤ (5 / 8 : ℝ) * beta * |u| ^ 3 := by linarith

private theorem be_iid_normalized_charFun
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (k : ℕ) (t : ℝ) :
    charFun ((Measure.pi (fun _ : Fin k => nu)).map
      (fun a : Shao.Path k => Shao.prefixSum a k / Real.sqrt (k : ℝ))) t =
      (charFun nu (t / Real.sqrt (k : ℝ))) ^ k := by
  have hfun : (fun a : Shao.Path k => Shao.prefixSum a k / Real.sqrt (k : ℝ)) =
      (fun a : Shao.Path k => (Real.sqrt (k : ℝ))⁻¹ * Shao.prefixSum a k) := by
    funext a
    ring
  rw [hfun, charFun_map_mul_comp (Shao.measurable_prefixSum k).aemeasurable]
  have he := congrFun (charFun_map_sum_pi_eq_prod (fun _ : Fin k => nu))
    ((Real.sqrt (k : ℝ))⁻¹ * t)
  simpa [Shao.prefixSum, mul_comm, div_eq_mul_inv] using he

private theorem be_complex_power_error
    (a b : ℂ) (R d : ℝ) (hR : 0 ≤ R) (hd : 0 ≤ d)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (hab : ‖a - b‖ ≤ d) (n : ℕ) :
    ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ (n + 1 : ℝ) * R ^ n * d := by
  induction n with
  | zero => simpa using hab
  | succ n ih =>
    have he : a ^ (n + 1 + 1) - b ^ (n + 1 + 1) =
        a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1) := by ring
    rw [he]
    calc
      _ ≤ ‖a * (a ^ (n + 1) - b ^ (n + 1))‖ + ‖(a - b) * b ^ (n + 1)‖ :=
        norm_add_le _ _
      _ = ‖a‖ * ‖a ^ (n + 1) - b ^ (n + 1)‖ + ‖a - b‖ * ‖b‖ ^ (n + 1) := by
        rw [norm_mul, norm_mul, norm_pow]
      _ ≤ R * ((n + 1 : ℝ) * R ^ n * d) + d * R ^ (n + 1) := by
        exact add_le_add (mul_le_mul ha ih (norm_nonneg _) hR)
          (mul_le_mul hab (pow_le_pow_left₀ (norm_nonneg b) hb (n + 1))
            (pow_nonneg (norm_nonneg b) (n + 1)) hd)
      _ = (n + 1 + 1 : ℝ) * R ^ (n + 1) * d := by rw [pow_succ]; ring
      _ = _ := by push_cast; ring

theorem iid_unitVariance_charFun_error
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (k : ℕ) (hk : 1 ≤ k) (t : ℝ)
    (ht : |t| ≤ Real.sqrt (k : ℝ) /
      (2 * (∫ z : ℝ, |z| ^ 3 ∂nu))) :
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
    let P : Measure (Shao.Path k) :=
      Measure.pi (fun _ : Fin k => nu)
    let law : Measure ℝ :=
      P.map (fun a : Shao.Path k =>
        Shao.prefixSum a k / Real.sqrt (k : ℝ))
    ‖MeasureTheory.charFun law t -
        (Real.exp (-(t ^ 2) / 2) : ℂ)‖ ≤
      beta * |t| ^ 3 / Real.sqrt (k : ℝ) * Real.exp (-(t ^ 2) / 8) := by
  let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
  let v : ℝ := Real.sqrt (k : ℝ)
  let u : ℝ := t / v
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hv : 0 < v := Real.sqrt_pos.2 hkpos
  have hvsq : v ^ 2 = (k : ℝ) := Real.sq_sqrt hkpos.le
  have hb : 1 ≤ beta := be_third_moment_ge_one nu h3 hsecond
  have hbp : 0 < beta := by linarith
  have ht' : |t| * (2 * beta) ≤ v := (le_div_iff₀ (by positivity)).1 ht
  have huba : beta * |u| ≤ 1 / 2 := by
    dsimp [u]
    rw [abs_div, abs_of_pos hv, ← mul_div_assoc]
    apply (div_le_iff₀ hv).2
    nlinarith
  have hua : |u| ≤ 1 / 2 := by nlinarith [abs_nonneg u]
  have hu2 : u ^ 2 ≤ 1 / 4 := by
    have hh := mul_self_le_mul_self (abs_nonneg u) hua
    nlinarith only [hh, sq_abs u]
  have hku : (k : ℝ) * u ^ 2 = t ^ 2 := by
    rw [← hvsq]
    dsimp [u]
    field_simp
  have hcoef : (k : ℝ) * ((5 / 8 : ℝ) * beta * |u| ^ 3) =
      (5 / 8 : ℝ) * (beta * |t| ^ 3 / v) := by
    rw [← hvsq]
    dsimp [u]
    rw [abs_div, abs_of_pos hv]
    field_simp
    <;> ring
  obtain ⟨hphi, herr⟩ := be_unitVariance_charFun_band nu h3 hmean hsecond u huba
  change ‖charFun nu u - (Real.exp (-u ^ 2 / 2) : ℂ)‖ ≤
    (5 / 8 : ℝ) * beta * |u| ^ 3 at herr
  have hgauss : ‖(Real.exp (-u ^ 2 / 2) : ℂ)‖ ≤ Real.exp (-u ^ 2 / 4) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u])
  have hpow := be_complex_power_error (charFun nu u) (Real.exp (-u ^ 2 / 2))
    (Real.exp (-u ^ 2 / 4)) ((5 / 8 : ℝ) * beta * |u| ^ 3)
    (Real.exp_pos _).le (by positivity) hphi hgauss herr (k - 1)
  rw [Nat.sub_add_cancel hk] at hpow
  rw [Nat.cast_sub hk, Nat.cast_one, sub_add_cancel] at hpow
  have hgaussPow : (Real.exp (-u ^ 2 / 2) : ℂ) ^ k =
      (Real.exp (-(t ^ 2) / 2) : ℂ) := by
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 1
    congr 1
    nlinarith only [hku]
  rw [hgaussPow] at hpow
  have hfac : (5 / 8 : ℝ) ≤ Real.exp (-u ^ 2 / 8) := by
    have hh := Real.add_one_le_exp (-u ^ 2 / 8)
    linarith
  have hdecay : (5 / 8 : ℝ) * Real.exp (-u ^ 2 / 4) ^ (k - 1) ≤
      Real.exp (-(t ^ 2) / 8) := by
    calc
      _ ≤ Real.exp (-u ^ 2 / 8) * Real.exp (-u ^ 2 / 4) ^ (k - 1) :=
        mul_le_mul_of_nonneg_right hfac (pow_nonneg (Real.exp_pos _).le _)
      _ = Real.exp (-u ^ 2 / 8 + (k - 1 : ℕ) * (-u ^ 2 / 4)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [Nat.cast_sub hk, Nat.cast_one]
        have hh := mul_nonneg (show 0 ≤ (k : ℝ) - 1 by
            have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
            linarith)
          (sq_nonneg u)
        nlinarith only [hh, hku]
  change ‖charFun ((Measure.pi (fun _ : Fin k => nu)).map
    (fun a : Shao.Path k => Shao.prefixSum a k / v)) t -
    (Real.exp (-(t ^ 2) / 2) : ℂ)‖ ≤ beta * |t| ^ 3 / v * Real.exp (-(t ^ 2) / 8)
  rw [be_iid_normalized_charFun nu k t]
  change ‖(charFun nu u) ^ k - (Real.exp (-(t ^ 2) / 2) : ℂ)‖ ≤ _
  calc
    _ ≤ (k : ℝ) * Real.exp (-u ^ 2 / 4) ^ (k - 1) *
        ((5 / 8 : ℝ) * beta * |u| ^ 3) := hpow
    _ = (beta * |t| ^ 3 / v) *
        ((5 / 8 : ℝ) * Real.exp (-u ^ 2 / 4) ^ (k - 1)) := by
      calc
        _ = ((k : ℝ) * ((5 / 8 : ℝ) * beta * |u| ^ 3)) *
            Real.exp (-u ^ 2 / 4) ^ (k - 1) := by ring
        _ = _ := by rw [hcoef]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)

private theorem be_gaussian_fourier_majorant :
    Integrable (fun t : ℝ => t ^ 2 * Real.exp (-(t ^ 2) / 8)) ∧
      (∫ t : ℝ, t ^ 2 * Real.exp (-(t ^ 2) / 8)) ≤ 32 := by
  have hroot : 0 < Real.sqrt (8 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hG : (∫ t : ℝ, t ^ 2 ∂gaussianReal 0 4) = 4 := by
    have hv := variance_fun_id_gaussianReal (μ := 0) (v := 4)
    change variance (id : ℝ → ℝ) (gaussianReal 0 4) = (4 : NNReal) at hv
    rw [variance_eq_integral measurable_id.aemeasurable] at hv
    dsimp only [id_eq] at hv
    rw [integral_id_gaussianReal] at hv
    simpa only [sub_zero, NNReal.coe_ofNat] using hv
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (4 : NNReal) ≠ 0)] at hG
  have hd : (fun t : ℝ => gaussianPDFReal 0 4 t • t ^ 2) =
      (fun t : ℝ => (Real.sqrt (8 * Real.pi))⁻¹ *
        (t ^ 2 * Real.exp (-(t ^ 2) / 8))) := by
    funext t
    simp only [gaussianPDFReal, NNReal.coe_ofNat, sub_zero, smul_eq_mul]
    ring_nf
  rw [hd, integral_const_mul] at hG
  have hval : (∫ t : ℝ, t ^ 2 * Real.exp (-(t ^ 2) / 8)) =
      4 * Real.sqrt (8 * Real.pi) := by
    calc
      _ = Real.sqrt (8 * Real.pi) *
          ((Real.sqrt (8 * Real.pi))⁻¹ *
            (∫ t : ℝ, t ^ 2 * Real.exp (-(t ^ 2) / 8))) := by
        rw [← mul_assoc, mul_inv_cancel₀ hroot.ne', one_mul]
      _ = _ := by rw [hG]; ring
  constructor
  · apply Integrable.of_integral_ne_zero
    rw [hval]
    positivity
  · rw [hval]
    have hr : Real.sqrt (8 * Real.pi) ≤ 8 := by
      apply (Real.sqrt_le_iff).2
      constructor
      · norm_num
      · nlinarith [Real.pi_lt_four]
    linarith

theorem iid_unitVariance_berryEsseen
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    |(Measure.pi (fun _ : Fin k => nu)).real
        {a : Shao.Path k |
          Shao.prefixSum a k / Real.sqrt (k : ℝ) ≤ x} -
        Shao.OQ4.standardNormalCDF x| ≤
      (1024 : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂nu) / Real.sqrt (k : ℝ) := by
  let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
  let v : ℝ := Real.sqrt (k : ℝ)
  let T : ℝ := v / (2 * beta)
  let P : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => nu)
  let X : Shao.Path k → ℝ := fun a => Shao.prefixSum a k / v
  let law : Measure ℝ := P.map X
  have hv : 0 < v := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < k by omega))
  have hb : 1 ≤ beta := be_third_moment_ge_one nu h3 hsecond
  have hbp : 0 < beta := by linarith
  have hT : 0 < T := div_pos hv (by positivity)
  have hX : Measurable X := (Shao.measurable_prefixSum k).div_const v
  have hprob : IsProbabilityMeasure law := by
    constructor
    change P.map X Set.univ = 1
    rw [Measure.map_apply hX MeasurableSet.univ]
    simp
  letI : IsProbabilityMeasure law := hprob
  have hnu1 : Integrable (id : ℝ → ℝ) nu :=
    (be_third_moment_memLp nu h3).integrable (by norm_num)
  have hcoord (i : Fin k) : Integrable (fun a : Shao.Path k => a i) P :=
    (measurePreserving_eval (fun _ : Fin k => nu) i).integrable_comp_of_integrable hnu1
  have hsum : Integrable (fun a : Shao.Path k => Shao.prefixSum a k) P := by
    simpa [Shao.prefixSum] using
      (integrable_finsetSum Finset.univ (fun i _ => hcoord i))
  have hXi : Integrable X P := hsum.div_const v
  have hlaw1 : Integrable (fun z : ℝ => z) law :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hX.aemeasurable).2 hXi
  have hG1 : Integrable (fun z : ℝ => z) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable (by norm_num)
  have hLip (a b : ℝ) :
      |(gaussianReal 0 1).real (Set.Iic a) - (gaussianReal 0 1).real (Set.Iic b)| ≤
        1 * |a - b| := by
    simpa only [← Shao.OQ4.standardNormalCDF_eq_real, one_mul] using
      Shao.OQ4.standardNormalCDF_lipschitz a b
  have hSm := cdf_error_le_fourier_smoothing law (gaussianReal 0 1)
    hlaw1 hG1 1 (by norm_num) hLip T hT
  have hGcf (t : ℝ) : charFun (gaussianReal 0 1) t =
      (Real.exp (-(t ^ 2) / 2) : ℂ) := by
    rw [charFun_gaussianReal, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have herr (t : ℝ) (ht : t ∈ Set.Icc (-T) T) :
      cdfFourierError law (gaussianReal 0 1) t ≤
        (beta / v) * (t ^ 2 * Real.exp (-(t ^ 2) / 8)) := by
    have htband : |t| ≤ Real.sqrt (k : ℝ) /
        (2 * (∫ z : ℝ, |z| ^ 3 ∂nu)) := abs_le.mpr ht
    have hcf := iid_unitVariance_charFun_error nu h3 hmean hsecond k hk t htband
    change ‖charFun law t - (Real.exp (-(t ^ 2) / 2) : ℂ)‖ ≤
      beta * |t| ^ 3 / v * Real.exp (-(t ^ 2) / 8) at hcf
    by_cases ht0 : t = 0
    · subst t
      simp only [cdfFourierError, abs_zero, div_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, neg_zero, zero_div, Real.exp_zero, mul_zero, zero_mul,
        le_refl]
    · rw [cdfFourierError, hGcf]
      calc
        _ ≤ (beta * |t| ^ 3 / v * Real.exp (-(t ^ 2) / 8)) / |t| :=
          div_le_div_of_nonneg_right hcf (abs_nonneg t)
        _ = _ := by
          field_simp [(abs_pos.mpr ht0).ne', hv.ne']
          <;> rw [← sq_abs t]
          <;> ring
  obtain ⟨hGi, hGbound⟩ := be_gaussian_fourier_majorant
  have hmajor : Integrable (fun t : ℝ =>
      (beta / v) * (t ^ 2 * Real.exp (-(t ^ 2) / 8))) := hGi.const_mul (beta / v)
  have hInt : (∫ t : ℝ in Set.Icc (-T) T,
      cdfFourierError law (gaussianReal 0 1) t) ≤ 32 * beta / v := by
    calc
      _ ≤ ∫ t : ℝ in Set.Icc (-T) T,
          (beta / v) * (t ^ 2 * Real.exp (-(t ^ 2) / 8)) := by
        apply integral_mono_ae hSm.1 hmajor.restrict
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact herr t ht
      _ ≤ ∫ t : ℝ, (beta / v) * (t ^ 2 * Real.exp (-(t ^ 2) / 8)) :=
        setIntegral_le_integral hmajor (Filter.Eventually.of_forall fun t => by positivity)
      _ = (beta / v) * ∫ t : ℝ, t ^ 2 * Real.exp (-(t ^ 2) / 8) := integral_const_mul _ _
      _ ≤ (beta / v) * 32 := mul_le_mul_of_nonneg_left hGbound (by positivity)
      _ = _ := by ring
  have hTail : 64 * 1 / T = 128 * beta / v := by
    dsimp [T]
    field_simp
    norm_num
  have hMap : law.real (Set.Iic x) = P.real {a : Shao.Path k | X a ≤ x} := by
    simp only [law, Measure.real_def, Measure.map_apply hX measurableSet_Iic]
    rfl
  have hx := hSm.2 x
  rw [hMap, ← Shao.OQ4.standardNormalCDF_eq_real, hTail] at hx
  change |P.real {a : Shao.Path k | X a ≤ x} - Shao.OQ4.standardNormalCDF x| ≤
    1024 * beta / v
  have hp : 0 ≤ beta / v := by positivity
  calc
    _ ≤ 2 * (∫ t : ℝ in Set.Icc (-T) T,
        cdfFourierError law (gaussianReal 0 1) t) + 128 * beta / v := hx
    _ ≤ 2 * (32 * beta / v) + 128 * beta / v := by linarith only [hInt]
    _ = 192 * (beta / v) := by ring
    _ ≤ 1024 * (beta / v) := mul_le_mul_of_nonneg_right (by norm_num) hp
    _ = _ := by ring

private theorem be_centered_unitVariance_moments
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu) :
    let mu : ℝ := ∫ z : ℝ, z ∂nu
    let V : ℝ := variance (id : ℝ → ℝ) nu
    let tau : ℝ := Real.sqrt V
    let Z : ℝ → ℝ := fun z => (z - mu) / tau
    let zeta : Measure ℝ := nu.map Z
    IsProbabilityMeasure zeta ∧
      Integrable (fun z : ℝ => |z| ^ 3) zeta ∧
      (∫ z : ℝ, z ∂zeta) = 0 ∧
      (∫ z : ℝ, z ^ 2 ∂zeta) = 1 ∧
      (∫ z : ℝ, |z| ^ 3 ∂zeta) =
        (∫ z : ℝ, |z - mu| ^ 3 ∂nu) / tau ^ 3 := by
  let mu : ℝ := ∫ z : ℝ, z ∂nu
  let V : ℝ := variance (id : ℝ → ℝ) nu
  let tau : ℝ := Real.sqrt V
  let Z : ℝ → ℝ := fun z => (z - mu) / tau
  let zeta : Measure ℝ := nu.map Z
  have htau : 0 < tau := Real.sqrt_pos.2 hV
  have htau2 : tau ^ 2 = V := Real.sq_sqrt hV.le
  have hZ : Measurable Z := (measurable_id.sub measurable_const).div_const tau
  have h1 : Integrable (fun z : ℝ => z) nu :=
    (be_third_moment_memLp nu h3).integrable (by norm_num)
  have hc1 : Integrable (fun z : ℝ => z - mu) nu := h1.sub (integrable_const mu)
  have hLpc : MemLp (fun z : ℝ => z - mu) 3 nu :=
    (be_third_moment_memLp nu h3).sub (memLp_const mu)
  have hc3 : Integrable (fun z : ℝ => |z - mu| ^ 3) nu := by
    simpa only [Real.norm_eq_abs] using hLpc.integrable_norm_pow'
  have hc2 : Integrable (fun z : ℝ => (z - mu) ^ 2) nu := by
    have hh := (hLpc.mono_exponent (show (2 : ENNReal) ≤ 3 by norm_num)).integrable_norm_pow'
    simpa only [Real.norm_eq_abs, sq_abs] using hh
  have hcmean : (∫ z : ℝ, z - mu ∂nu) = 0 := by
    rw [integral_sub h1 (integrable_const mu), integral_const]
    simp only [probReal_univ, one_smul]
    exact sub_self mu
  have hVeq : (∫ z : ℝ, (z - mu) ^ 2 ∂nu) = V := by
    exact (variance_eq_integral measurable_id.aemeasurable).symm
  have hZ1 : Integrable Z nu := hc1.div_const tau
  have hZ2 : Integrable (fun z : ℝ => (Z z) ^ 2) nu := by
    apply (hc2.div_const (tau ^ 2)).congr
    exact Filter.Eventually.of_forall fun z => by dsimp [Z]; rw [div_pow]
  have hcube (z : ℝ) : |Z z| ^ 3 = |z - mu| ^ 3 / tau ^ 3 := by
    rw [show Z z = (z - mu) / tau from rfl, abs_div, abs_of_pos htau, div_pow]
  have hZ3 : Integrable (fun z : ℝ => |Z z| ^ 3) nu :=
    (hc3.div_const (tau ^ 3)).congr
      (Filter.Eventually.of_forall fun z => (hcube z).symm)
  have hprob : IsProbabilityMeasure zeta := by
    constructor
    change nu.map Z Set.univ = 1
    rw [Measure.map_apply hZ MeasurableSet.univ]
    simp
  refine ⟨hprob, ?_, ?_, ?_, ?_⟩
  · exact (integrable_map_measure (continuous_abs.pow 3).aestronglyMeasurable
      hZ.aemeasurable).2 hZ3
  · change (∫ z : ℝ, z ∂nu.map Z) = 0
    rw [integral_map (μ := nu) (φ := Z) (f := fun z : ℝ => z)
      hZ.aemeasurable measurable_id.aestronglyMeasurable]
    change (∫ z : ℝ, (z - mu) / tau ∂nu) = 0
    rw [integral_div, hcmean, zero_div]
  · change (∫ z : ℝ, z ^ 2 ∂nu.map Z) = 1
    rw [integral_map (μ := nu) (φ := Z) (f := fun z : ℝ => z ^ 2)
      hZ.aemeasurable (continuous_id.pow 2).aestronglyMeasurable]
    simp_rw [show ∀ z, Z z = (z - mu) / tau from fun _ => rfl, div_pow]
    rw [integral_div, hVeq, htau2, div_self hV.ne']
  · change (∫ z : ℝ, |z| ^ 3 ∂nu.map Z) = _
    rw [integral_map (μ := nu) (φ := Z) (f := fun z : ℝ => |z| ^ 3)
      hZ.aemeasurable (continuous_abs.pow 3).aestronglyMeasurable]
    simp_rw [hcube]
    rw [integral_div]

theorem iid_centered_berryEsseen
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    let mu : ℝ := ∫ z : ℝ, z ∂nu
    let V : ℝ := variance (id : ℝ → ℝ) nu
    let m3c : ℝ := ∫ z : ℝ, |z - mu| ^ 3 ∂nu
    |(Measure.pi (fun _ : Fin k => nu)).real
        {a : Shao.Path k |
          (Shao.prefixSum a k - (k : ℝ) * mu) /
            (Real.sqrt V * Real.sqrt (k : ℝ)) ≤ x} -
        Shao.OQ4.standardNormalCDF x| ≤
      (1024 : ℝ) * m3c /
        ((Real.sqrt V) ^ 3 * Real.sqrt (k : ℝ)) := by
  let mu : ℝ := ∫ z : ℝ, z ∂nu
  let V : ℝ := variance (id : ℝ → ℝ) nu
  let tau : ℝ := Real.sqrt V
  let v : ℝ := Real.sqrt (k : ℝ)
  let Z : ℝ → ℝ := fun z => (z - mu) / tau
  let zeta : Measure ℝ := nu.map Z
  let G : Shao.Path k → Shao.Path k := fun a i => Z (a i)
  have hZ : Measurable Z := (measurable_id.sub measurable_const).div_const tau
  have hG : Measurable G := Measurable.of_eval fun i => hZ.comp (measurable_pi_apply i)
  obtain ⟨hprob, hz3, hzmean, hzsecond, hzcube⟩ := be_centered_unitVariance_moments nu h3 hV
  change IsProbabilityMeasure zeta at hprob
  change Integrable (fun z : ℝ => |z| ^ 3) zeta at hz3
  change (∫ z : ℝ, z ∂zeta) = 0 at hzmean
  change (∫ z : ℝ, z ^ 2 ∂zeta) = 1 at hzsecond
  change (∫ z : ℝ, |z| ^ 3 ∂zeta) = (∫ z : ℝ, |z - mu| ^ 3 ∂nu) / tau ^ 3 at hzcube
  letI : IsProbabilityMeasure zeta := hprob
  have hmap : (Measure.pi (fun _ : Fin k => nu)).map G =
      Measure.pi (fun _ : Fin k => zeta) :=
    Measure.pi_map_pi (fun _ : Fin k => hZ.aemeasurable)
  have hprefix (a : Shao.Path k) : Shao.prefixSum (G a) k =
      (Shao.prefixSum a k - (k : ℝ) * mu) / tau := by
    simp [Shao.prefixSum, G, Z]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp
  have hB : MeasurableSet {a : Shao.Path k | Shao.prefixSum a k / v ≤ x} :=
    measurableSet_le ((Shao.measurable_prefixSum k).div_const v) measurable_const
  have hCDF := iid_unitVariance_berryEsseen zeta hz3 hzmean hzsecond k hk x
  have hCDFmap : (Measure.pi (fun _ : Fin k => zeta)).real
      {a : Shao.Path k | Shao.prefixSum a k / v ≤ x} =
      (Measure.pi (fun _ : Fin k => nu)).real
        {a : Shao.Path k | (Shao.prefixSum a k - (k : ℝ) * mu) / (tau * v) ≤ x} := by
    rw [← hmap, Measure.real_def, Measure.map_apply hG hB]
    congr 1
    congr 1
    ext a
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hprefix, div_div]
  change |(Measure.pi (fun _ : Fin k => zeta)).real
    {a : Shao.Path k | Shao.prefixSum a k / v ≤ x} - Shao.OQ4.standardNormalCDF x| ≤
    1024 * (∫ z : ℝ, |z| ^ 3 ∂zeta) / v at hCDF
  rw [hCDFmap, hzcube] at hCDF
  change |(Measure.pi (fun _ : Fin k => nu)).real
    {a : Shao.Path k | (Shao.prefixSum a k - (k : ℝ) * mu) / (tau * v) ≤ x} -
    Shao.OQ4.standardNormalCDF x| ≤
    1024 * (∫ z : ℝ, |z - mu| ^ 3 ∂nu) / (tau ^ 3 * v)
  convert hCDF using 1 <;> ring

theorem iid_uncentered_berryEsseen
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    let mu : ℝ := ∫ z : ℝ, z ∂nu
    let V : ℝ := variance (id : ℝ → ℝ) nu
    let m3c : ℝ := ∫ z : ℝ, |z - mu| ^ 3 ∂nu
    |(Measure.pi (fun _ : Fin k => nu)).real
        {a : Shao.Path k |
          Shao.prefixSum a k /
            (Real.sqrt V * Real.sqrt (k : ℝ)) ≤ x} -
        Shao.OQ4.standardNormalCDF x| ≤
      (1024 : ℝ) * m3c /
          ((Real.sqrt V) ^ 3 * Real.sqrt (k : ℝ)) +
        |mu| * Real.sqrt (k : ℝ) / Real.sqrt V := by
  let mu : ℝ := ∫ z : ℝ, z ∂nu
  let V : ℝ := variance (id : ℝ → ℝ) nu
  let tau : ℝ := Real.sqrt V
  let v : ℝ := Real.sqrt (k : ℝ)
  let d : ℝ := mu * v / tau
  let P : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => nu)
  let B : ℝ := 1024 * (∫ z : ℝ, |z - mu| ^ 3 ∂nu) / (tau ^ 3 * v)
  have htau : 0 < tau := Real.sqrt_pos.2 hV
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hv : 0 < v := Real.sqrt_pos.2 hkpos
  have hvsq : v ^ 2 = (k : ℝ) := Real.sq_sqrt hkpos.le
  have hcenter (a : Shao.Path k) :
      (Shao.prefixSum a k - (k : ℝ) * mu) / (tau * v) =
        Shao.prefixSum a k / (tau * v) - d := by
    rw [← hvsq]
    dsimp [d]
    field_simp
    <;> ring
  have hEvent : {a : Shao.Path k |
      (Shao.prefixSum a k - (k : ℝ) * mu) / (tau * v) ≤ x - d} =
      {a : Shao.Path k | Shao.prefixSum a k / (tau * v) ≤ x} := by
    ext a
    simp only [Set.mem_setOf_eq, hcenter, sub_le_sub_iff_right]
  have hc := iid_centered_berryEsseen nu h3 hV k hk (x - d)
  change |P.real {a : Shao.Path k |
    (Shao.prefixSum a k - (k : ℝ) * mu) / (tau * v) ≤ x - d} -
    Shao.OQ4.standardNormalCDF (x - d)| ≤ B at hc
  rw [hEvent] at hc
  have hPhi : |Shao.OQ4.standardNormalCDF (x - d) - Shao.OQ4.standardNormalCDF x| ≤
      |d| := by
    have hh := Shao.OQ4.standardNormalCDF_lipschitz (x - d) x
    have he : (x - d) - x = -d := by ring
    simpa only [he, abs_neg] using hh
  have hd : |d| = |mu| * v / tau := by
    dsimp [d]
    rw [abs_div, abs_mul, abs_of_pos hv, abs_of_pos htau]
  change |P.real {a : Shao.Path k | Shao.prefixSum a k / (tau * v) ≤ x} -
    Shao.OQ4.standardNormalCDF x| ≤ B + |mu| * v / tau
  calc
    _ ≤ |P.real {a : Shao.Path k | Shao.prefixSum a k / (tau * v) ≤ x} -
        Shao.OQ4.standardNormalCDF (x - d)| +
        |Shao.OQ4.standardNormalCDF (x - d) - Shao.OQ4.standardNormalCDF x| :=
      abs_sub_le _ _ _
    _ ≤ B + |d| := add_le_add hc hPhi
    _ = _ := by rw [hd]

end Shao.Probability
