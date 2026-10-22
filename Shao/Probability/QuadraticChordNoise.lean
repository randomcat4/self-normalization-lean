import Shao.Probability.LowFrequencyDamping
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

attribute [local instance 2000] NormedSpace.complexToReal

noncomputable def quadraticTriangleLaw : Measure ℝ :=
  volume.withDensity (fun t : ℝ =>
    ENNReal.ofReal (if |t| ≤ 1 then 1 - |t| else 0))

noncomputable def quadraticBiasedPairLaw (ν : Measure ℝ) : Measure (ℝ × ℝ) :=
  (ν.prod ν).withDensity (fun p : ℝ × ℝ =>
    ENNReal.ofReal ((p.1 - p.2) ^ 2 /
      (2 * variance (id : ℝ → ℝ) ν)))

noncomputable def quadraticChordLaw (ν : Measure ℝ) : Measure (ℝ × ℝ) :=
  Measure.map
    (fun z : (ℝ × ℝ) × ℝ =>
      (z.2 * (z.1.1 - z.1.2), z.2 * (z.1.1 ^ 2 - z.1.2 ^ 2)))
    ((quadraticBiasedPairLaw ν).prod quadraticTriangleLaw)

noncomputable def quadraticChordChar (ν : Measure ℝ) (u v : ℝ) : ℂ :=
  ∫ z : ℝ × ℝ, Complex.exp
    (((u * z.1 + v * z.2 : ℝ) : ℂ) * Complex.I) ∂quadraticChordLaw ν

private lemma triangle_weight_nonneg (r : ℝ) :
    0 ≤ (if |r| ≤ 1 then 1 - |r| else 0 : ℝ) := by
  split_ifs with h
  · linarith
  · exact le_rfl

private lemma triangle_weight_measurable :
    Measurable (fun r : ℝ => if |r| ≤ 1 then 1 - |r| else (0 : ℝ)) := by
  exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    (measurable_const.sub continuous_abs.measurable) measurable_const

private lemma triangle_weight_indicator (r : ℝ) :
    (if |r| ≤ 1 then 1 - |r| else (0 : ℝ)) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun r => 1 - |r|) r := by
  by_cases h : |r| ≤ 1
  · have hr : r ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp h
    simp [h, hr]
  · have hr : r ∉ Set.Icc (-1 : ℝ) 1 := fun hr => h (abs_le.mpr hr)
    simp [h, hr]

private lemma triangle_weight_integrable :
    Integrable (fun r : ℝ => if |r| ≤ 1 then 1 - |r| else (0 : ℝ)) := by
  have hc : Continuous (fun r : ℝ => 1 - |r|) := by fun_prop
  have hi : Integrable ((Set.Icc (-1 : ℝ) 1).indicator (fun r => 1 - |r|)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr hc.integrableOn_Icc
  exact hi.congr (Filter.Eventually.of_forall fun r => (triangle_weight_indicator r).symm)

private lemma triangle_weighted_integral (g : ℝ → ℂ) (hg : Continuous g) :
    (∫ r : ℝ, ((if |r| ≤ 1 then 1 - |r| else 0 : ℝ) : ℂ) * g r) =
      (∫ r : ℝ in (-1)..0, ((1 + r : ℝ) : ℂ) * g r) +
      (∫ r : ℝ in 0..1, ((1 - r : ℝ) : ℂ) * g r) := by
  have he : (fun r : ℝ => ((if |r| ≤ 1 then 1 - |r| else 0 : ℝ) : ℂ) * g r) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun r => ((1 - |r| : ℝ) : ℂ) * g r) := by
    funext r
    by_cases h : r ∈ Set.Icc (-1 : ℝ) 1
    · simp [h, abs_le.mpr h]
    · have ha : ¬ |r| ≤ 1 := fun ha => h (abs_le.mp ha)
      simp [h, ha]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hc : Continuous (fun r : ℝ => ((1 - |r| : ℝ) : ℂ) * g r) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-1) 0)
    (hc.intervalIntegrable 0 1)]
  congr 1
  · apply intervalIntegral.integral_congr
    intro r hr
    have hr0 : r ≤ 0 := by simpa using hr.2
    dsimp only
    rw [abs_of_nonpos hr0]
    congr 2
    ring
  · apply intervalIntegral.integral_congr
    intro r hr
    have hr0 : 0 ≤ r := by simpa using hr.1
    dsimp only
    rw [abs_of_nonneg hr0]

private lemma affine_phase_integral (a b c k t : ℝ) (ht : t ≠ 0) :
    let z : ℂ := (t : ℂ) * Complex.I
    let E : ℝ → ℂ := fun r => Complex.exp (((t * r : ℝ) : ℂ) * Complex.I)
    (∫ r : ℝ in a..b, ((c + k * r : ℝ) : ℂ) * E r) =
      (((c + k * b : ℝ) : ℂ) * E b / z - (k : ℂ) * E b / z ^ 2) -
      (((c + k * a : ℝ) : ℂ) * E a / z - (k : ℂ) * E a / z ^ 2) := by
  dsimp only
  let z : ℂ := (t : ℂ) * Complex.I
  let E : ℝ → ℂ := fun r => Complex.exp (((t * r : ℝ) : ℂ) * Complex.I)
  have hz : z ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) Complex.I_ne_zero
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro r _
    have he : HasDerivAt E (z * E r) r := by
      convert ((((hasDerivAt_id r).const_mul t).ofReal_comp).mul_const Complex.I).cexp using 1
      all_goals dsimp [z, E]
      all_goals push_cast
      all_goals ring
    have ha : HasDerivAt (fun s : ℝ => ((c + k * s : ℝ) : ℂ)) (k : ℂ) r := by
      simpa only [mul_one, id_eq] using (((hasDerivAt_id r).const_mul k).const_add c).ofReal_comp
    convert ((ha.mul he).div_const z).sub ((he.const_mul (k : ℂ)).div_const (z ^ 2)) using 1
    dsimp [E]
    field_simp
    ring
  · have hc : Continuous (fun r : ℝ => ((c + k * r : ℝ) : ℂ) * E r) := by
      dsimp [E]
      fun_prop
    exact hc.intervalIntegrable a b

private lemma triangle_density_mass :
    (∫ r : ℝ, (if |r| ≤ 1 then 1 - |r| else 0 : ℝ)) = 1 := by
  have hh := triangle_weighted_integral (fun _ => (1 : ℂ)) continuous_const
  simp only [mul_one] at hh
  have hleft : (∫ r : ℝ in (-1)..0, ((1 + r : ℝ) : ℂ)) = 1 / 2 := by
    have hr : (∫ r : ℝ in (-1)..0, 1 + r) = 1 / 2 := by
      calc
        _ = (∫ r : ℝ in (-1)..0, 1) + (∫ r : ℝ in (-1)..0, r) :=
          intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
            (continuous_id.intervalIntegrable _ _)
        _ = _ := by norm_num [intervalIntegral.integral_const, integral_id]
    rw [intervalIntegral.integral_ofReal, hr]
    norm_num
  have hright : (∫ r : ℝ in 0..1, ((1 - r : ℝ) : ℂ)) = 1 / 2 := by
    have hr : (∫ r : ℝ in 0..1, 1 - r) = 1 / 2 := by
      calc
        _ = (∫ r : ℝ in 0..1, 1) - (∫ r : ℝ in 0..1, r) :=
          intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
            (continuous_id.intervalIntegrable _ _)
        _ = _ := by norm_num [intervalIntegral.integral_const, integral_id]
    rw [intervalIntegral.integral_ofReal, hr]
    norm_num
  have hcast : (∫ r : ℝ, ((if |r| ≤ 1 then 1 - |r| else 0 : ℝ) : ℂ)) =
      Complex.ofReal (∫ r : ℝ, (if |r| ≤ 1 then 1 - |r| else 0 : ℝ)) := integral_complex_ofReal
  rw [hleft, hright, hcast] at hh
  have hh' := congrArg Complex.re hh
  norm_num at hh'
  exact hh'

private lemma real_density_probability {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (w : α → ℝ) (hi : Integrable w μ) (hw : ∀ x, 0 ≤ w x) (hm : ∫ x, w x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (w x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hw), hm]
  exact ENNReal.ofReal_one

private lemma triangle_probability : IsProbabilityMeasure quadraticTriangleLaw :=
  real_density_probability volume _ triangle_weight_integrable triangle_weight_nonneg
    triangle_density_mass

private lemma real_density_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (w : α → ℝ) (hw : Measurable w) (hn : ∀ x, 0 ≤ w x) (g : α → ℂ) :
    (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (w x))) =
      ∫ x, (w x : ℂ) * g x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hn _), Complex.real_smul]

theorem quadraticTriangle_probability_char :
    IsProbabilityMeasure quadraticTriangleLaw ∧
      ∀ t : ℝ,
        (∫ r : ℝ, Complex.exp (((t * r : ℝ) : ℂ) * Complex.I)
          ∂quadraticTriangleLaw) =
        ((if t = 0 then 1 else 2 * (1 - Real.cos t) / t ^ 2 : ℝ) : ℂ) := by
  refine ⟨triangle_probability, ?_⟩
  intro t
  by_cases ht : t = 0
  · subst t
    let := triangle_probability
    simp
  · change (∫ r : ℝ, Complex.exp (((t * r : ℝ) : ℂ) * Complex.I)
      ∂volume.withDensity (fun r : ℝ => ENNReal.ofReal
        (if |r| ≤ 1 then 1 - |r| else 0))) = _
    rw [real_density_integral volume _ triangle_weight_measurable triangle_weight_nonneg]
    rw [triangle_weighted_integral _ (by fun_prop), ite_eq_right ht]
    have hleft := affine_phase_integral (-1) 0 1 1 t ht
    have hright := affine_phase_integral 0 1 1 (-1) t ht
    dsimp only at hleft hright
    simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at hleft hright
    rw [hleft, hright]
    have hz : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    have hexp : Complex.exp ((t : ℂ) * Complex.I) +
        Complex.exp (-(t : ℂ) * Complex.I) = 2 * (Real.cos t : ℂ) := by
      simp only [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
    rw [neg_mul] at hexp
    simp only [mul_zero, mul_one, mul_neg_one, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, add_zero, one_mul, Complex.ofReal_one,
      sub_self, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_ofNat]
    rw [show ((t : ℂ) * Complex.I) ^ 2 = -(t : ℂ) ^ 2 by rw [mul_pow, Complex.I_sq]; ring]
    field_simp
    linear_combination -Complex.I * hexp

private lemma biased_probability (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν) :
    IsProbabilityMeasure (quadraticBiasedPairLaw ν) := by
  obtain ⟨hi, hm⟩ := quadratic_pair_square_moment ν h3
  apply real_density_probability (ν.prod ν) _ (hi.div_const _)
  · intro p
    exact div_nonneg (sq_nonneg _) (by positivity)
  · rw [integral_div, hm, div_self (by positivity)]

private lemma chord_probability (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν) :
    IsProbabilityMeasure (quadraticChordLaw ν) := by
  let := biased_probability ν h3 hV
  let := triangle_probability
  unfold quadraticChordLaw
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

private lemma triangle_support : ∀ᵐ r : ℝ ∂quadraticTriangleLaw, |r| ≤ 1 := by
  rw [ae_iff]
  change volume.withDensity _ {r : ℝ | ¬ |r| ≤ 1} = 0
  have hs : MeasurableSet {r : ℝ | ¬ |r| ≤ 1} :=
    (measurableSet_le continuous_abs.measurable measurable_const).compl
  rw [withDensity_apply _ hs]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem hs] with r hr
  simp [hr]

private lemma pair_support (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    ∀ᵐ p : ℝ × ℝ ∂ν.prod ν, |p.1| ≤ h ∧ |p.2| ≤ h := by
  apply (Measure.ae_prod_iff_ae_ae (p := fun p : ℝ × ℝ => |p.1| ≤ h ∧ |p.2| ≤ h)
    ((measurableSet_le (f := fun p : ℝ × ℝ => |p.1|) (g := fun _ => h)
      (by fun_prop) measurable_const).inter
      (measurableSet_le (f := fun p : ℝ × ℝ => |p.2|) (g := fun _ => h)
        (by fun_prop) measurable_const))).mpr
  filter_upwards [hs] with a ha
  filter_upwards [hs] with b hb
  exact ⟨ha, hb⟩

private lemma probability_phase_integrable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Measurable f) :
    Integrable (fun x => Complex.exp ((f x : ℂ) * Complex.I)) μ := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Filter.Eventually.of_forall ?_)
  intro x
  simp [Complex.norm_exp, Complex.mul_re]

theorem quadraticChord_law_data (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    IsProbabilityMeasure (quadraticBiasedPairLaw ν) ∧
      IsProbabilityMeasure (quadraticChordLaw ν) ∧
      (∀ᵐ z : ℝ × ℝ ∂quadraticChordLaw ν,
        |z.1| ≤ 2 * h ∧ |z.2| ≤ 2 * h * |z.1|) ∧
      ∀ u v : ℝ,
        Integrable (fun z : ℝ × ℝ => Complex.exp
          (((u * z.1 + v * z.2 : ℝ) : ℂ) * Complex.I))
          (quadraticChordLaw ν) := by
  let := biased_probability ν h3 hV
  let := chord_probability ν h3 hV
  let := triangle_probability
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · have hp : ∀ᵐ p : ℝ × ℝ ∂quadraticBiasedPairLaw ν,
        |p.1| ≤ h ∧ |p.2| ≤ h :=
      (withDensity_absolutelyContinuous (ν.prod ν) _).ae_le (pair_support ν h hsupport)
    have ht : ∀ᵐ z : (ℝ × ℝ) × ℝ ∂(quadraticBiasedPairLaw ν).prod quadraticTriangleLaw,
        (|z.1.1| ≤ h ∧ |z.1.2| ≤ h) ∧ |z.2| ≤ 1 := by
      apply (Measure.ae_prod_iff_ae_ae
        (p := fun z : (ℝ × ℝ) × ℝ => (|z.1.1| ≤ h ∧ |z.1.2| ≤ h) ∧ |z.2| ≤ 1)
        (((measurableSet_le (f := fun z : (ℝ × ℝ) × ℝ => |z.1.1|)
          (g := fun _ => h) (by fun_prop) measurable_const).inter
          (measurableSet_le (f := fun z : (ℝ × ℝ) × ℝ => |z.1.2|)
            (g := fun _ => h) (by fun_prop) measurable_const)).inter
          (measurableSet_le (f := fun z : (ℝ × ℝ) × ℝ => |z.2|)
            (g := fun _ => 1) (by fun_prop) measurable_const))).mpr
      filter_upwards [hp] with p hp
      filter_upwards [triangle_support] with r hr
      exact ⟨hp, hr⟩
    unfold quadraticChordLaw
    apply (ae_map_iff (p := fun z : ℝ × ℝ => |z.1| ≤ 2 * h ∧ |z.2| ≤ 2 * h * |z.1|)
      (by fun_prop)
      ((measurableSet_le (f := fun z : ℝ × ℝ => |z.1|) (g := fun _ => 2 * h)
        (by fun_prop) measurable_const).inter
        (measurableSet_le (f := fun z : ℝ × ℝ => |z.2|)
          (g := fun z => 2 * h * |z.1|) (by fun_prop) (by fun_prop)))).mpr
    filter_upwards [ht] with z hz
    have hd : |z.1.1 - z.1.2| ≤ 2 * h := by
      calc
        _ ≤ |z.1.1| + |z.1.2| := abs_sub _ _
        _ ≤ _ := by linarith [hz.1.1, hz.1.2]
    have ha : |z.1.1 + z.1.2| ≤ 2 * h := by
      calc
        _ ≤ |z.1.1| + |z.1.2| := abs_add_le _ _
        _ ≤ _ := by linarith [hz.1.1, hz.1.2]
    constructor
    · 
      rw [abs_mul]
      calc
        _ = |z.1.1 - z.1.2| * |z.2| := mul_comm _ _
        _ ≤ (2 * h) * 1 := mul_le_mul hd hz.2 (abs_nonneg _) (by linarith only [hh])
        _ = _ := mul_one _
    · 
      rw [show z.1.1 ^ 2 - z.1.2 ^ 2 =
        (z.1.1 - z.1.2) * (z.1.1 + z.1.2) by ring, abs_mul, abs_mul, abs_mul]
      calc
        _ = (|z.2| * |z.1.1 - z.1.2|) * |z.1.1 + z.1.2| := by ring
        _ ≤ (|z.2| * |z.1.1 - z.1.2|) * (2 * h) :=
          mul_le_mul_of_nonneg_left ha (by positivity)
        _ = _ := by ring
  · intro u v
    exact probability_phase_integrable _ _ (by fun_prop)

private lemma triangle_kernel_bounds (t : ℝ) :
    0 ≤ (if t = 0 then 1 else 2 * (1 - Real.cos t) / t ^ 2 : ℝ) ∧
      (if t = 0 then 1 else 2 * (1 - Real.cos t) / t ^ 2 : ℝ) ≤ 1 := by
  let := triangle_probability
  constructor
  · split_ifs
    · norm_num
    · exact div_nonneg (by nlinarith [Real.cos_le_one t]) (sq_nonneg t)
  · have hn := norm_integral_le_of_norm_le_const (μ := quadraticTriangleLaw)
      (f := fun r : ℝ => Complex.exp (((t * r : ℝ) : ℂ) * Complex.I))
      (C := 1) (Filter.Eventually.of_forall fun r => by
        simp [Complex.norm_exp, Complex.mul_re])
    rw [quadraticTriangle_probability_char.2 t] at hn
    have hn' : |if t = 0 then 1 else 2 * (1 - Real.cos t) / t ^ 2| ≤ 1 := by
      simpa [Complex.norm_real, Real.norm_eq_abs, Measure.real] using hn
    exact le_trans (le_abs_self _) hn'

private lemma triangle_kernel_quotient (d θ : ℝ) :
    d ^ 2 / 2 * (if d * θ = 0 then 1 else
      2 * (1 - Real.cos (d * θ)) / (d * θ) ^ 2) =
      if θ = 0 then d ^ 2 / 2 else (1 - Real.cos (d * θ)) / θ ^ 2 := by
  by_cases hθ : θ = 0
  · simp [hθ]
  · by_cases hd : d = 0
    · simp [hd, hθ]
    · simp only [hθ, mul_ne_zero hd hθ, ite_false]
      field_simp

private lemma chord_quotient_bounds (d θ : ℝ) :
    0 ≤ (if θ = 0 then d ^ 2 / 2 else (1 - Real.cos (d * θ)) / θ ^ 2) ∧
      (if θ = 0 then d ^ 2 / 2 else (1 - Real.cos (d * θ)) / θ ^ 2) ≤ d ^ 2 / 2 := by
  rw [← triangle_kernel_quotient]
  obtain ⟨hl, hu⟩ := triangle_kernel_bounds (d * θ)
  constructor
  · positivity
  · exact mul_le_of_le_one_right (by positivity) hu

private lemma chord_quotient_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) (u v : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      if u + v * (p.1 + p.2) = 0 then (p.1 - p.2) ^ 2 / 2 else
        (1 - Real.cos ((p.1 - p.2) * (u + v * (p.1 + p.2)))) /
          (u + v * (p.1 + p.2)) ^ 2) (ν.prod ν) := by
  refine ((quadratic_pair_square_moment ν h3).1.div_const 2).mono' ?_
    (Filter.Eventually.of_forall ?_)
  · apply Measurable.aestronglyMeasurable
    exact Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
      (by fun_prop) (by fun_prop)
  · intro p
    obtain ⟨hl, hu⟩ := chord_quotient_bounds (p.1 - p.2) (u + v * (p.1 + p.2))
    simpa only [Real.norm_eq_abs, abs_of_nonneg hl] using hu

private lemma chord_kernel_integral (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν) (u v : ℝ) :
    quadraticChordChar ν u v =
      ∫ p : ℝ × ℝ, ((if (p.1 - p.2) * (u + v * (p.1 + p.2)) = 0 then 1 else
        2 * (1 - Real.cos ((p.1 - p.2) * (u + v * (p.1 + p.2)))) /
          ((p.1 - p.2) * (u + v * (p.1 + p.2))) ^ 2 : ℝ) : ℂ)
        ∂quadraticBiasedPairLaw ν := by
  let := biased_probability ν h3 hV
  let := triangle_probability
  unfold quadraticChordChar quadraticChordLaw
  rw [integral_map (by fun_prop) (by fun_prop)]
  have he : (fun z : (ℝ × ℝ) × ℝ => Complex.exp
      (((u * (z.2 * (z.1.1 - z.1.2)) + v * (z.2 * (z.1.1 ^ 2 - z.1.2 ^ 2)) : ℝ) : ℂ) *
        Complex.I)) = (fun z => Complex.exp
      ((((z.1.1 - z.1.2) * (u + v * (z.1.1 + z.1.2)) * z.2 : ℝ) : ℂ) * Complex.I)) := by
    funext z
    congr 2
    push_cast
    ring
  rw [he, integral_prod _ (probability_phase_integrable _ _ (by fun_prop))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p =>
    quadraticTriangle_probability_char.2 ((p.1 - p.2) * (u + v * (p.1 + p.2)))

theorem quadraticChordChar_exact (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν) (u v : ℝ) :
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let Q : ℝ × ℝ → ℝ := fun p =>
      if u + v * (p.1 + p.2) = 0 then (p.1 - p.2) ^ 2 / 2
      else
        (1 - Real.cos ((p.1 - p.2) * (u + v * (p.1 + p.2)))) /
          (u + v * (p.1 + p.2)) ^ 2
    Integrable Q (ν.prod ν) ∧
      quadraticChordChar ν u v =
        (((∫ p : ℝ × ℝ, Q p ∂ν.prod ν) / V : ℝ) : ℂ) ∧
      (quadraticChordChar ν u v).im = 0 ∧
      0 ≤ (quadraticChordChar ν u v).re ∧
      (quadraticChordChar ν u v).re ≤ 1 := by
  dsimp only
  have hi := chord_quotient_integrable ν h3 u v
  have hk : quadraticChordChar ν u v =
      Complex.ofReal ((∫ p : ℝ × ℝ, if u + v * (p.1 + p.2) = 0 then (p.1 - p.2) ^ 2 / 2
        else (1 - Real.cos ((p.1 - p.2) * (u + v * (p.1 + p.2)))) /
          (u + v * (p.1 + p.2)) ^ 2 ∂ν.prod ν) / variance (id : ℝ → ℝ) ν) := by
    rw [chord_kernel_integral ν h3 hV]
    unfold quadraticBiasedPairLaw
    rw [real_density_integral _ _ (by fun_prop) (fun p => div_nonneg (sq_nonneg _) (by positivity))]
    have he : (fun p : ℝ × ℝ =>
        (((p.1 - p.2) ^ 2 / (2 * variance (id : ℝ → ℝ) ν) : ℝ) : ℂ) *
          ((if (p.1 - p.2) * (u + v * (p.1 + p.2)) = 0 then 1 else
            2 * (1 - Real.cos ((p.1 - p.2) * (u + v * (p.1 + p.2)))) /
              ((p.1 - p.2) * (u + v * (p.1 + p.2))) ^ 2 : ℝ) : ℂ)) =
        (fun p => Complex.ofReal ((if u + v * (p.1 + p.2) = 0 then (p.1 - p.2) ^ 2 / 2
          else (1 - Real.cos ((p.1 - p.2) * (u + v * (p.1 + p.2)))) /
            (u + v * (p.1 + p.2)) ^ 2) / variance (id : ℝ → ℝ) ν)) := by
      funext p
      rw [← Complex.ofReal_mul, ← triangle_kernel_quotient]
      congr 1
      ring
    rw [he, integral_complex_ofReal, integral_div]
  refine ⟨hi, hk, ?_⟩
  rw [hk]
  simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
  constructor
  · apply div_nonneg (integral_nonneg fun p => (chord_quotient_bounds _ _).1) hV.le
  · apply (div_le_one hV).mpr
    calc
      _ ≤ ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 / 2 ∂ν.prod ν :=
        integral_mono hi ((quadratic_pair_square_moment ν h3).1.div_const 2)
          (fun p => (chord_quotient_bounds _ _).2)
      _ = _ := by rw [integral_div, (quadratic_pair_square_moment ν h3).2]; ring

private lemma cone_theta_bounds (a b h u v : ℝ) (hh : 0 < h)
    (ha : |a| ≤ h) (hb : |b| ≤ h) (hu : u ≠ 0) (hv : |v| ≤ |u| / (4 * h)) :
    u + v * (a + b) ≠ 0 ∧
      u ^ 2 / 4 ≤ (u + v * (a + b)) ^ 2 ∧
      (u + v * (a + b)) ^ 2 ≤ 9 * u ^ 2 / 4 := by
  have hab : |a + b| ≤ 2 * h := by linarith [abs_add_le a b]
  have hp : |v * (a + b)| ≤ |u| / 2 := by
    calc
      _ = |v| * |a + b| := abs_mul _ _
      _ ≤ (|u| / (4 * h)) * (2 * h) :=
        mul_le_mul hv hab (abs_nonneg _) (by positivity)
      _ = _ := by field_simp; ring
  have hupper : |u + v * (a + b)| ≤ 3 * |u| / 2 := by
    linarith [abs_add_le u (v * (a + b))]
  have hlower : |u| / 2 ≤ |u + v * (a + b)| := by
    have hs := abs_sub (u + v * (a + b)) (v * (a + b))
    rw [add_sub_cancel_right] at hs
    linarith
  have haU : 0 < |u| := abs_pos.mpr hu
  refine ⟨?_, ?_, ?_⟩
  · intro he
    rw [he, abs_zero] at hlower
    linarith
  · nlinarith [sq_abs u, sq_abs (u + v * (a + b)),
      mul_nonneg (by linarith : 0 ≤ |u + v * (a + b)| - |u| / 2)
        (by positivity : 0 ≤ |u + v * (a + b)| + |u| / 2)]
  · nlinarith [sq_abs u, sq_abs (u + v * (a + b)),
      mul_nonneg (sub_nonneg.mpr hupper)
        (by positivity : 0 ≤ 3 * |u| / 2 + |u + v * (a + b)|)]

private lemma cone_quotient_bounds (a b h u v : ℝ) (hh : 0 < h)
    (ha : |a| ≤ h) (hb : |b| ≤ h) (hu : u ≠ 0) (hv : |v| ≤ |u| / (4 * h)) :
    (4 / 9 : ℝ) * (1 - Real.cos ((a - b) * (u + v * (a + b)))) / u ^ 2 ≤
      (1 - Real.cos ((a - b) * (u + v * (a + b)))) / (u + v * (a + b)) ^ 2 ∧
      (1 - Real.cos ((a - b) * (u + v * (a + b)))) / (u + v * (a + b)) ^ 2 ≤
        4 * (1 - Real.cos ((a - b) * (u + v * (a + b)))) / u ^ 2 := by
  obtain ⟨hθ, hlo, hhi⟩ := cone_theta_bounds a b h u v hh ha hb hu hv
  have hn : 0 ≤ 1 - Real.cos ((a - b) * (u + v * (a + b))) :=
    sub_nonneg.mpr (Real.cos_le_one _)
  constructor
  · apply (div_le_div_iff₀ (sq_pos_of_ne_zero hu) (sq_pos_of_ne_zero hθ)).mpr
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hhi)]
  · apply (div_le_div_iff₀ (sq_pos_of_ne_zero hθ) (sq_pos_of_ne_zero hu)).mpr
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hlo)]

theorem quadraticChordChar_cone_gap (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (u v : ℝ) (hu : u ≠ 0) (hv : |v| ≤ |u| / (4 * h)) :
    (4 / 9 : ℝ) * (1 - ‖quadraticChar ν u v‖ ^ 2) /
        (variance (id : ℝ → ℝ) ν * u ^ 2) ≤
      (quadraticChordChar ν u v).re ∧
      (quadraticChordChar ν u v).re ≤
        4 * (1 - ‖quadraticChar ν u v‖ ^ 2) /
          (variance (id : ℝ → ℝ) ν * u ^ 2) := by
  let N : ℝ × ℝ → ℝ := fun p =>
    1 - Real.cos ((p.1 - p.2) * (u + v * (p.1 + p.2)))
  let Q : ℝ × ℝ → ℝ := fun p =>
    if u + v * (p.1 + p.2) = 0 then (p.1 - p.2) ^ 2 / 2 else
      N p / (u + v * (p.1 + p.2)) ^ 2
  have hN : Integrable N (ν.prod ν) := by
    refine (integrable_const (2 : ℝ)).mono' (by dsimp [N]; fun_prop)
      (Filter.Eventually.of_forall ?_)
    intro p
    dsimp [N]
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
    linarith [Real.neg_one_le_cos ((p.1 - p.2) * (u + v * (p.1 + p.2)))]
  obtain ⟨hQ, hK, _, _, _⟩ := quadraticChordChar_exact ν h3 hV u v
  change Integrable Q (ν.prod ν) at hQ
  change quadraticChordChar ν u v = Complex.ofReal ((∫ p, Q p ∂ν.prod ν) /
    variance (id : ℝ → ℝ) ν) at hK
  have hp : ∀ᵐ p : ℝ × ℝ ∂ν.prod ν,
      (4 / 9 : ℝ) * N p / u ^ 2 ≤ Q p ∧ Q p ≤ 4 * N p / u ^ 2 := by
    filter_upwards [pair_support ν h hsupport] with p hp
    obtain ⟨hθ, _, _⟩ := cone_theta_bounds p.1 p.2 h u v hh hp.1 hp.2 hu hv
    have ht := cone_quotient_bounds p.1 p.2 h u v hh hp.1 hp.2 hu hv
    simpa only [N, Q, hθ, ite_false] using ht
  have hl := integral_mono_ae ((hN.const_mul (4 / 9)).div_const (u ^ 2)) hQ
    (hp.mono fun _ hp => hp.1)
  have hu' := integral_mono_ae hQ ((hN.const_mul 4).div_const (u ^ 2))
    (hp.mono fun _ hp => hp.2)
  rw [integral_div, integral_const_mul] at hl hu'
  have hgap : (∫ p, N p ∂ν.prod ν) = 1 - ‖quadraticChar ν u v‖ ^ 2 :=
    (quadraticChar_gap_identity ν u v).symm
  rw [hgap] at hl hu'
  rw [hK, Complex.ofReal_re]
  constructor
  · calc
      _ = ((4 / 9 : ℝ) * (1 - ‖quadraticChar ν u v‖ ^ 2) / u ^ 2) /
          variance (id : ℝ → ℝ) ν := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hl hV.le
  · calc
      _ ≤ (4 * (1 - ‖quadraticChar ν u v‖ ^ 2) / u ^ 2) /
          variance (id : ℝ → ℝ) ν := div_le_div_of_nonneg_right hu' hV.le
      _ = _ := by ring

end Shao.Probability
