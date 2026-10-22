import Shao.Probability.QuadraticChordNoise
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped ContDiff ComplexConjugate

private noncomputable def sourceScalarBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

noncomputable def sourceScalarDensity : ℝ → ℝ := sourceScalarBump.normed volume

noncomputable def sourceScalarLaw : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (sourceScalarDensity t))

noncomputable def sourceScalarChar (t : ℝ) : ℂ :=
  ∫ r : ℝ, Complex.exp (((t * r : ℝ) : ℂ) * Complex.I) ∂sourceScalarLaw

theorem sourceScalarDensity_data :
    ContDiff ℝ ∞ sourceScalarDensity ∧ HasCompactSupport sourceScalarDensity ∧
    (∀ t : ℝ, 0 ≤ sourceScalarDensity t) ∧
    (∀ t : ℝ, sourceScalarDensity (-t) = sourceScalarDensity t) ∧
    (∀ t : ℝ, 1 ≤ |t| → sourceScalarDensity t = 0) ∧
    (∫ t : ℝ, sourceScalarDensity t) = 1 := by
  refine ⟨sourceScalarBump.contDiff_normed, sourceScalarBump.hasCompactSupport_normed,
    sourceScalarBump.nonneg_normed, sourceScalarBump.normed_neg, ?_,
    sourceScalarBump.integral_normed⟩
  intro t ht
  unfold sourceScalarDensity ContDiffBump.normed
  rw [sourceScalarBump.zero_of_le_dist (by simpa [sourceScalarBump, Real.dist_eq] using ht)]
  exact zero_div _

private lemma scalar_probability : IsProbabilityMeasure sourceScalarLaw := by
  obtain ⟨hsmooth, _, hn, _, _, hm⟩ := sourceScalarDensity_data
  have hi : Integrable sourceScalarDensity := sourceScalarBump.integrable_normed
  constructor
  unfold sourceScalarLaw
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn), hm]
  exact ENNReal.ofReal_one

private lemma scalar_reflection :
    Measure.map (fun t : ℝ => -t) sourceScalarLaw = sourceScalarLaw := by
  obtain ⟨hd, _, _, heven, _, _⟩ := sourceScalarDensity_data
  ext s hs
  rw [Measure.map_apply measurable_neg hs]
  unfold sourceScalarLaw
  rw [withDensity_apply _ (measurable_neg hs), withDensity_apply _ hs,
    ← lintegral_indicator (measurable_neg hs), ← lintegral_indicator hs]
  have he : (fun t : ℝ => ((fun r : ℝ => -r) ⁻¹' s).indicator
      (fun r => ENNReal.ofReal (sourceScalarDensity r)) t) =
      (fun t => s.indicator (fun r => ENNReal.ofReal (sourceScalarDensity r)) (-t)) := by
    funext t
    by_cases ht : -t ∈ s
    · simp [ht, heven]
    · simp [ht]
  rw [he]
  exact (Measure.measurePreserving_neg (volume : Measure ℝ)).lintegral_comp
    ((hd.continuous.measurable.ennreal_ofReal).indicator hs)

private lemma scalar_support : ∀ᵐ t : ℝ ∂sourceScalarLaw, |t| ≤ 1 := by
  obtain ⟨_, _, _, _, hz, _⟩ := sourceScalarDensity_data
  rw [ae_iff]
  change volume.withDensity _ {t : ℝ | ¬ |t| ≤ 1} = 0
  have hs : MeasurableSet {t : ℝ | ¬ |t| ≤ 1} := by measurability
  rw [withDensity_apply _ hs]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem hs] with t ht
  rw [hz t (le_of_not_ge ht)]
  exact ENNReal.ofReal_zero

theorem sourceScalarLaw_data :
    IsProbabilityMeasure sourceScalarLaw ∧
    Measure.map (fun t : ℝ => -t) sourceScalarLaw = sourceScalarLaw ∧
    (∀ᵐ t : ℝ ∂sourceScalarLaw, |t| ≤ 1) ∧
    Integrable (fun t : ℝ => t) sourceScalarLaw ∧
    Integrable (fun t : ℝ => |t|) sourceScalarLaw ∧
    Integrable (fun t : ℝ => t ^ 2) sourceScalarLaw ∧
    (∫ t : ℝ, t ∂sourceScalarLaw) = 0 ∧
    (∫ t : ℝ, |t| ∂sourceScalarLaw) ≤ 1 ∧
    (∫ t : ℝ, t ^ 2 ∂sourceScalarLaw) ≤ 1 := by
  let := scalar_probability
  have hi : Integrable (fun t : ℝ => t) sourceScalarLaw := by
    refine (integrable_const (1 : ℝ)).mono' measurable_id.aestronglyMeasurable ?_
    simpa only [Real.norm_eq_abs] using scalar_support
  have hs : Integrable (fun t : ℝ => t ^ 2) sourceScalarLaw := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [scalar_support] with t ht
    simpa only [Real.norm_eq_abs, abs_pow, one_pow] using
      pow_le_pow_left₀ (abs_nonneg t) ht 2
  have hm : (∫ t : ℝ, t ∂sourceScalarLaw) = 0 := by
    have he : (∫ t : ℝ, t ∂sourceScalarLaw) = -(∫ t : ℝ, t ∂sourceScalarLaw) := by
      calc
        _ = ∫ t : ℝ, t ∂Measure.map (fun t : ℝ => -t) sourceScalarLaw := by rw [scalar_reflection]
        _ = ∫ t : ℝ, -t ∂sourceScalarLaw := integral_map (by fun_prop) (by fun_prop)
        _ = _ := integral_neg _
    linarith
  refine ⟨scalar_probability, scalar_reflection, scalar_support, hi, hi.abs, hs, hm, ?_, ?_⟩
  · simpa using integral_mono_ae hi.abs (integrable_const (1 : ℝ)) scalar_support
  · have hb : ∀ᵐ t : ℝ ∂sourceScalarLaw, t ^ 2 ≤ 1 := by
      filter_upwards [scalar_support] with t ht
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg t) ht 2
    simpa using integral_mono_ae hs (integrable_const (1 : ℝ)) hb

theorem sourceScalarChar_even_bound (t : ℝ) :
    sourceScalarChar (-t) = sourceScalarChar t ∧
    (sourceScalarChar t).im = 0 ∧ ‖sourceScalarChar t‖ ≤ 1 := by
  let := scalar_probability
  have he : sourceScalarChar (-t) = sourceScalarChar t := by
    unfold sourceScalarChar
    calc
      _ = ∫ r : ℝ, Complex.exp (((t * (-r) : ℝ) : ℂ) * Complex.I) ∂sourceScalarLaw := by
        apply integral_congr_ae
        filter_upwards [] with r
        congr 2
        push_cast
        ring
      _ = ∫ r : ℝ, Complex.exp (((t * r : ℝ) : ℂ) * Complex.I)
          ∂Measure.map (fun r : ℝ => -r) sourceScalarLaw :=
        (integral_map (φ := fun r : ℝ => -r)
          (f := fun r : ℝ => Complex.exp (((t * r : ℝ) : ℂ) * Complex.I))
          (by fun_prop) (by fun_prop)).symm
      _ = _ := by rw [scalar_reflection]
  have hconj : conj (sourceScalarChar t) = sourceScalarChar (-t) := by
    unfold sourceScalarChar
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with r
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_mul,
      Complex.ofReal_neg]
    ring
  have him := congrArg Complex.im hconj
  rw [he] at him
  have him0 : (sourceScalarChar t).im = 0 := by
    simp only [Complex.conj_im] at him
    linarith
  refine ⟨he, him0, ?_⟩
  unfold sourceScalarChar
  simpa using norm_integral_le_of_norm_le (integrable_const (μ := sourceScalarLaw) (1 : ℝ))
    (Filter.Eventually.of_forall fun r : ℝ => by simp [Complex.norm_exp, Complex.mul_re])

end Shao.Probability
