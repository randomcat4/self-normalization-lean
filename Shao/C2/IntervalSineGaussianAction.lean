import Shao.C2.BrownianKilledInitialLimit
import Shao.C2.IntervalSineSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
namespace Shao.C2.IntervalSineGaussianAction
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
open Shao.C2.IntervalSineTerms Shao.C2.IntervalSineSeries Shao.C2.IntervalSpectralGaussian

private theorem gaussian_cos_sin (v : ℝ≥0) (ω : ℝ) :
    (∫ x : ℝ, Real.cos (ω * x) ∂gaussianReal 0 v) = Real.exp (-(v : ℝ) * ω ^ 2 / 2) ∧
      (∫ x : ℝ, Real.sin (ω * x) ∂gaussianReal 0 v) = 0 := by
  have hi : Integrable (fun x : ℝ => Complex.exp ((ω : ℂ) * x * Complex.I))
      (gaussianReal 0 v) := by
    apply Integrable.of_bound (by fun_prop : Measurable
      (fun x : ℝ => Complex.exp ((ω : ℂ) * x * Complex.I))).aestronglyMeasurable 1
    exact Eventually.of_forall fun x => by simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hg : charFun (gaussianReal 0 v) ω = (Real.exp (-(v : ℝ) * ω ^ 2 / 2) : ℂ) := by
    rw [charFun_gaussianReal, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hr := integral_re hi
  have hm := integral_im hi
  rw [← charFun_apply_real, hg] at hr hm
  change (∫ x : ℝ, (Complex.exp ((ω : ℂ) * x * Complex.I)).re ∂gaussianReal 0 v) =
    (Real.exp (-(v : ℝ) * ω ^ 2 / 2) : ℂ).re at hr
  change (∫ x : ℝ, (Complex.exp ((ω : ℂ) * x * Complex.I)).im ∂gaussianReal 0 v) =
    (Real.exp (-(v : ℝ) * ω ^ 2 / 2) : ℂ).im at hm
  constructor
  · simpa only [Complex.ofReal_re, Complex.ofReal_im, Complex.exp_re, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul,
      sub_zero, zero_sub, add_zero, zero_add, Real.exp_zero, one_mul] using hr
  · simpa only [Complex.ofReal_re, Complex.ofReal_im, Complex.exp_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul,
      sub_zero, zero_sub, add_zero, zero_add, Real.exp_zero, one_mul] using hm

theorem gaussian_sine_affine (v : ℝ≥0) (ω r : ℝ) :
    Integrable (fun x : ℝ => Real.sin (ω * (r + x))) (gaussianReal 0 v) ∧
      (∫ x : ℝ, Real.sin (ω * (r + x)) ∂gaussianReal 0 v) =
        Real.exp (-(v : ℝ) * ω ^ 2 / 2) * Real.sin (ω * r) := by
  have hsin : Integrable (fun x : ℝ => Real.sin (ω * x)) (gaussianReal 0 v) := by
    apply Integrable.of_bound (by fun_prop : Measurable (fun x : ℝ => Real.sin (ω * x))).aestronglyMeasurable 1
    exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (ω * x)
  have hcos : Integrable (fun x : ℝ => Real.cos (ω * x)) (gaussianReal 0 v) := by
    apply Integrable.of_bound (by fun_prop : Measurable (fun x : ℝ => Real.cos (ω * x))).aestronglyMeasurable 1
    exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (ω * x)
  have hi : Integrable (fun x : ℝ => Real.sin (ω * (r + x))) (gaussianReal 0 v) := by
    apply Integrable.of_bound (by fun_prop : Measurable (fun x : ℝ => Real.sin (ω * (r + x)))).aestronglyMeasurable 1
    exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (ω * (r + x))
  refine ⟨hi, ?_⟩
  calc
    _ = ∫ x : ℝ, Real.sin (ω * r) * Real.cos (ω * x) +
        Real.cos (ω * r) * Real.sin (ω * x) ∂gaussianReal 0 v := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change Real.sin (ω * (r + x)) = Real.sin (ω * r) * Real.cos (ω * x) +
          Real.cos (ω * r) * Real.sin (ω * x)
        rw [mul_add, Real.sin_add]
    _ = _ := by
      rw [integral_add (hcos.const_mul _) (hsin.const_mul _), integral_const_mul, integral_const_mul,
        (gaussian_cos_sin v ω).1, (gaussian_cos_sin v ω).2]
      ring

theorem sineTerm_gaussian_action (a z T y : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => sineTerm a z T (y + x) n) (gaussianReal 0 v) ∧
      (∫ x : ℝ, sineTerm a z T (y + x) n ∂gaussianReal 0 v) =
        sineTerm a z (T + (v : ℝ)) y n := by
  let c : ℝ := (1 / a) * Real.exp (-(frequency a n) ^ 2 * T / 2) *
    Real.sin (frequency a n * (z + a))
  have hp := gaussian_sine_affine v (frequency a n) (y + a)
  have heq : (fun x : ℝ => sineTerm a z T (y + x) n) =
      (fun x : ℝ => c * Real.sin (frequency a n * ((y + a) + x))) := by
    funext x
    have he : y + x + a = y + a + x := by ring
    simp only [sineTerm, he, c]
    ring
  have hi : Integrable (fun x : ℝ => sineTerm a z T (y + x) n) (gaussianReal 0 v) := by
    rw [heq]
    exact hp.1.const_mul c
  refine ⟨hi, ?_⟩
  rw [heq, integral_const_mul, hp.2]
  have he : Real.exp (-(frequency a n) ^ 2 * T / 2) *
      Real.exp (-(v : ℝ) * (frequency a n) ^ 2 / 2) =
      Real.exp (-(frequency a n) ^ 2 * (T + (v : ℝ)) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (1 / a) * (Real.exp (-(frequency a n) ^ 2 * T / 2) *
        Real.exp (-(v : ℝ) * (frequency a n) ^ 2 / 2)) *
        Real.sin (frequency a n * (y + a)) * Real.sin (frequency a n * (z + a)) := by dsimp only [c]; ring
    _ = _ := by rw [he]; rfl

theorem sineSeries_gaussian_action (a z T y : ℝ) (ha : 0 < a) (hT : 0 < T) (v : ℝ≥0) :
    Integrable (fun x : ℝ => mixedSineSeries 0 0 a z T (y + x)) (gaussianReal 0 v) ∧
      (∫ x : ℝ, mixedSineSeries 0 0 a z T (y + x) ∂gaussianReal 0 v) =
        mixedSineSeries 0 0 a z (T + (v : ℝ)) y := by
  let C : ℕ → ℝ := fun n => (1 / a) * weightedGaussian (Real.pi ^ 2 / 8) 0 (T / a ^ 2) n
  have hCs : Summable C :=
    (weightedGaussian_summable (Real.pi ^ 2 / 8) (T / a ^ 2) 0 (by positivity) (by positivity)).mul_left (1 / a)
  have hb (n : ℕ) (x : ℝ) : ‖sineTerm a z T (y + x) n‖ ≤ C n := by
    simpa only [mixedSineTerm, iteratedDeriv_zero, pow_zero, Nat.cast_zero, mul_zero,
      zero_add, one_mul, mul_one] using mixedSineTerm_weighted_bound 0 0 a z T (y + x) n ha
  have hc : Continuous (fun x : ℝ => mixedSineSeries 0 0 a z T (y + x)) := by
    have hh : Continuous (mixedSineSeries 0 0 a z T) :=
      continuous_iff_continuousAt.mpr fun w => (mixedSineSeries_spatial_hasDerivAt 0 0 a z T w ha hT).continuousAt
    exact hh.comp (continuous_const.add continuous_id)
  have hi : Integrable (fun x : ℝ => mixedSineSeries 0 0 a z T (y + x)) (gaussianReal 0 v) := by
    apply Integrable.of_bound hc.aestronglyMeasurable
      ((1 / a) * ∑' n : ℕ, weightedGaussian (Real.pi ^ 2 / 8) 0 (T / a ^ 2) n)
    exact Eventually.of_forall fun x => by
      simpa only [pow_zero, Nat.cast_zero, mul_zero, zero_add, one_mul, mul_one] using
        mixedSineSeries_weighted_bound 0 0 a z T (y + x) ha hT
  refine ⟨hi, ?_⟩
  have hpoint (x : ℝ) : HasSum (fun n : ℕ => sineTerm a z T (y + x) n)
      (mixedSineSeries 0 0 a z T (y + x)) := by
    simpa only [mixedSineSeries, mixedSineTerm, iteratedDeriv_zero] using
      (mixedSineTerm_summable 0 0 a z T (y + x) ha hT).hasSum
  have hd := hasSum_integral_of_dominated_convergence (μ := gaussianReal 0 v)
    (fun n _ => C n) (fun n => (sineTerm_gaussian_action a z T y v n).1.aestronglyMeasurable)
    (fun n => Eventually.of_forall (hb n)) (Eventually.of_forall fun _ => hCs)
    (integrable_const (∑' n, C n)) (Eventually.of_forall hpoint)
  have heq : (fun n : ℕ => ∫ x : ℝ, sineTerm a z T (y + x) n ∂gaussianReal 0 v) =
      (fun n : ℕ => sineTerm a z (T + (v : ℝ)) y n) :=
    funext fun n => (sineTerm_gaussian_action a z T y v n).2
  rw [heq] at hd
  have ht : HasSum (fun n : ℕ => sineTerm a z (T + (v : ℝ)) y n)
      (mixedSineSeries 0 0 a z (T + (v : ℝ)) y) := by
    simpa only [mixedSineSeries, mixedSineTerm, iteratedDeriv_zero] using
      (mixedSineTerm_summable 0 0 a z (T + (v : ℝ)) y ha (add_pos_of_pos_of_nonneg hT v.property)).hasSum
  exact hd.unique ht

end Shao.C2.IntervalSineGaussianAction
