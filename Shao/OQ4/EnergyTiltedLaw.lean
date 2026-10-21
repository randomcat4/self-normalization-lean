import Shao.OQ4.TruncatedEnergy
import Shao.OQ4.IntervalConcentration
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The actual normalized energy law and its finite source-bound moments. -/

namespace Shao.OQ4

open MeasureTheory

noncomputable def energyTiltedLaw (ν : Measure ℝ) (h s : ℝ) : Measure ℝ :=
  ν.withDensity (fun x => ENNReal.ofReal (energyWeight h s x / energyNormalizer ν h s))

noncomputable def energyTiltFirstNumeratorConstant (T : ℝ) : ℝ :=
  1 / 4 + Real.exp (4 * T) * T

noncomputable def energyTiltSecondNumeratorConstant (T : ℝ) : ℝ :=
  1 / 2 + 2 * Real.exp (4 * T) * T

noncomputable def energyTiltInverseNormalizerBound (T : ℝ) : ℝ :=
  (4 / 3) * Real.exp (4 * T)

noncomputable def energyTiltMeanConstant (T : ℝ) : ℝ :=
  energyTiltInverseNormalizerBound T * energyTiltFirstNumeratorConstant T

noncomputable def energyTiltSecondMomentConstant (T : ℝ) : ℝ :=
  energyTiltInverseNormalizerBound T *
    (energyTiltSecondNumeratorConstant T + T + energyNormalizerErrorConstant T)

noncomputable def energyTiltThirdMomentConstant (T : ℝ) : ℝ :=
  energyTiltInverseNormalizerBound T * Real.exp (4 * T)

theorem energyTiltedLaw_density_measurable (ν : Measure ℝ) (h s : ℝ) :
    Measurable (fun x => ENNReal.ofReal (energyWeight h s x / energyNormalizer ν h s)) :=
  ((energyWeight_measurable h s).div measurable_const).ennreal_ofReal

theorem energyTiltedLaw_normalizer_pos (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    0 < energyNormalizer ν h s :=
  lt_of_lt_of_le (by positivity) (energyNormalizer_bounds ν T h s hT hh hs hSq hsecond).1

theorem energyTiltedLaw_isProbabilityMeasure (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    IsProbabilityMeasure (energyTiltedLaw ν h s) := by
  have hZ := energyTiltedLaw_normalizer_pos ν T h s hT hh hs hSq hsecond
  have hw := energyWeight_integrable ν T h s hT (by linarith) hs
  constructor
  rw [energyTiltedLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hw.div_const (energyNormalizer ν h s))
      (Filter.Eventually.of_forall fun x => div_nonneg (energyWeight_nonneg h s x) hZ.le),
    integral_div]
  change ENNReal.ofReal (energyNormalizer ν h s / energyNormalizer ν h s) = 1
  simp [ne_of_gt hZ]

theorem energyTiltedLaw_real_apply (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (energyTiltedLaw ν h s).real A = (∫ x in A, energyWeight h s x ∂ν) / energyNormalizer ν h s := by
  have hZ := energyTiltedLaw_normalizer_pos ν T h s hT hh hs hSq hsecond
  have hw := energyWeight_integrable ν T h s hT (by linarith) hs
  have hp (x : ℝ) : 0 ≤ energyWeight h s x / energyNormalizer ν h s :=
    div_nonneg (energyWeight_nonneg h s x) hZ.le
  rw [energyTiltedLaw, measureReal_def, withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal (hw.div_const (energyNormalizer ν h s)).restrict
      (Filter.Eventually.of_forall hp), ENNReal.toReal_ofReal (integral_nonneg hp), integral_div]

theorem energyTiltedLaw_ae_support (ν : Measure ℝ) (h s : ℝ) :
    ∀ᵐ x ∂energyTiltedLaw ν h s, |x| ≤ 2 * h := by
  apply (ae_withDensity_iff (energyTiltedLaw_density_measurable ν h s)).2
  exact Filter.Eventually.of_forall fun x hx => by
    by_contra hn
    apply hx
    simp [energyWeight, hn]

/-- Borel tests with genuinely integrable weighted functions have genuine tilted integrals. -/
theorem energyTiltedLaw_integral (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (f : ℝ → ℝ) (_hf : Measurable f) (hfw : Integrable (fun x => f x * energyWeight h s x) ν) :
    Integrable f (energyTiltedLaw ν h s) ∧
    (∫ x : ℝ, f x ∂energyTiltedLaw ν h s) =
      (∫ x : ℝ, f x * energyWeight h s x ∂ν) / energyNormalizer ν h s := by
  have hZ := energyTiltedLaw_normalizer_pos ν T h s hT hh hs hSq hsecond
  have hp (x : ℝ) : 0 ≤ energyWeight h s x / energyNormalizer ν h s :=
    div_nonneg (energyWeight_nonneg h s x) hZ.le
  have htop : ∀ᵐ x ∂ν, ENNReal.ofReal (energyWeight h s x / energyNormalizer ν h s) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  constructor
  · apply (integrable_withDensity_iff (energyTiltedLaw_density_measurable ν h s) htop).2
    convert hfw.div_const (energyNormalizer ν h s) using 1
    ext x
    rw [ENNReal.toReal_ofReal (hp x)]
    ring
  · rw [energyTiltedLaw,
      integral_withDensity_eq_integral_toReal_smul (energyTiltedLaw_density_measurable ν h s) htop]
    simp_rw [ENNReal.toReal_ofReal (hp _), smul_eq_mul]
    calc
      _ = ∫ x : ℝ, (f x * energyWeight h s x) / energyNormalizer ν h s ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = _ := integral_div _ _

theorem energyTilt_original_moment_inputs (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    Integrable (fun x : ℝ => x) ν ∧ 1 ≤ ∫ x : ℝ, |x| ^ 3 ∂ν := by
  constructor
  · apply (hSq.add (integrable_const 1)).mono' measurable_id.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      change |x| ≤ x ^ 2 + 1
      nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  · exact third_absolute_moment_ge_one ν hSq hCube hsecond

theorem energyTilt_weighted_integrable (ν : Measure ℝ) [IsFiniteMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 0 < h) (hs : |s| ≤ T)
    (f : ℝ → ℝ) (hf : Measurable f) (hfi : Integrable f ν) :
    Integrable (fun x => f x * energyWeight h s x) ν := by
  apply (hfi.abs.const_mul (Real.exp (4 * T))).mono'
    (hf.mul (energyWeight_measurable h s)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    change |f x * energyWeight h s x| ≤ Real.exp (4 * T) * |f x|
    rw [abs_mul, abs_of_nonneg (energyWeight_nonneg h s x)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (energyWeight_le T h s x hT hh hs) (abs_nonneg (f x))

theorem energyTilt_exp_difference_bound (T u : ℝ) (hT : 0 ≤ T) (hu : |u| ≤ 4 * T) :
    |Real.exp u - 1| ≤ Real.exp (4 * T) * |u| := by
  let F : ℝ → ℝ := fun v => Real.exp (4 * T) * v - Real.exp v
  have hd (v : ℝ) : deriv F v = Real.exp (4 * T) - Real.exp v := by
    simp (disch := fun_prop) [F]
  have hm : MonotoneOn F (Set.Icc (-4 * T) (4 * T)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by fun_prop) (by fun_prop)
    intro v hv
    have hv' : v ∈ Set.Icc (-4 * T) (4 * T) := interior_subset hv
    rw [hd]
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr hv'.2)
  have hz : (0 : ℝ) ∈ Set.Icc (-4 * T) (4 * T) := ⟨by linarith, by linarith⟩
  have hu' : u ∈ Set.Icc (-4 * T) (4 * T) := by
    have ha := abs_le.mp hu
    exact ⟨by linarith [ha.1], ha.2⟩
  rcases le_total 0 u with hu0 | hu0
  · have hi := hm hz hu' hu0
    have he : 0 ≤ Real.exp u - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hu0)
    rw [abs_of_nonneg he, abs_of_nonneg hu0]
    dsimp [F] at hi
    norm_num at hi
    linarith
  · have hi := hm hu' hz hu0
    have he : Real.exp u - 1 ≤ 0 := sub_nonpos.mpr (Real.exp_le_one_iff.mpr hu0)
    rw [abs_of_nonpos he, abs_of_nonpos hu0]
    dsimp [F] at hi
    norm_num at hi
    linarith

theorem energyTilt_weight_difference_inside (T h s x : ℝ) (hT : 0 ≤ T) (hh : 0 < h)
    (hs : |s| ≤ T) (hx : |x| ≤ 2 * h) :
    |energyWeight h s x - 1| ≤ (Real.exp (4 * T) * T / h ^ 2) * x ^ 2 := by
  have ha := energy_argument_bounds T h s x hT hh hs hx
  have hb := energyTilt_exp_difference_bound T (s * x ^ 2 / h ^ 2) hT
    (abs_le.mpr ⟨by linarith [ha.1], ha.2⟩)
  simp only [energyWeight, hx, ite_true]
  calc
    _ ≤ Real.exp (4 * T) * |s * x ^ 2 / h ^ 2| := hb
    _ = Real.exp (4 * T) * |s| * (x ^ 2 / h ^ 2) := by
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg x), abs_of_nonneg (sq_nonneg h)]
      ring
    _ ≤ Real.exp (4 * T) * T * (x ^ 2 / h ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (Real.exp_nonneg _))
        (div_nonneg (sq_nonneg x) (sq_nonneg h))
    _ = _ := by ring

/-- Global integrable envelopes retain the strict complement and closed cutoff atoms. -/
theorem energyTilt_moment_pointwise (T h s x : ℝ) (hT : 0 ≤ T) (hh : 0 < h)
    (hs : |s| ≤ T) :
    |x * energyWeight h s x - x| ≤ (if 2 * h < |x| then |x| else 0) +
      (Real.exp (4 * T) * T / h ^ 2) * |x| ^ 3 ∧
    |x ^ 2 * energyWeight h s x - x ^ 2| ≤ (if 2 * h < |x| then x ^ 2 else 0) +
      (Real.exp (4 * T) * T / h ^ 2) * (if |x| ≤ 2 * h then x ^ 4 else 0) := by
  have hK : 0 ≤ Real.exp (4 * T) * T / h ^ 2 := by positivity
  by_cases hx : |x| ≤ 2 * h
  · have hn : ¬ 2 * h < |x| := not_lt.mpr hx
    have he := energyTilt_weight_difference_inside T h s x hT hh hs hx
    simp only [hn, hx, ite_false, ite_true, zero_add]
    constructor
    · calc
        _ = |x| * |energyWeight h s x - 1| := by rw [← abs_mul]; congr 1; ring
        _ ≤ |x| * ((Real.exp (4 * T) * T / h ^ 2) * x ^ 2) :=
          mul_le_mul_of_nonneg_left he (abs_nonneg x)
        _ = _ := by rw [← sq_abs x]; ring
    · calc
        _ = x ^ 2 * |energyWeight h s x - 1| := by
          calc
            _ = |x ^ 2 * (energyWeight h s x - 1)| := congrArg abs (by ring)
            _ = _ := by rw [abs_mul, abs_of_nonneg (sq_nonneg x)]
        _ ≤ x ^ 2 * ((Real.exp (4 * T) * T / h ^ 2) * x ^ 2) :=
          mul_le_mul_of_nonneg_left he (sq_nonneg x)
        _ = _ := by ring
  · have hn : 2 * h < |x| := lt_of_not_ge hx
    simp only [energyWeight, hx, hn, ite_false, ite_true, mul_zero, zero_sub,
      abs_neg, abs_of_nonneg (sq_nonneg x), add_zero]
    exact ⟨le_add_of_nonneg_right (mul_nonneg hK (pow_nonneg (abs_nonneg x) 3)), le_rfl⟩

theorem energyTilt_weighted_moment_integrability (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    Integrable (fun x : ℝ => x * energyWeight h s x) ν ∧
    Integrable (fun x : ℝ => x ^ 2 * energyWeight h s x) ν ∧
    Integrable (fun x : ℝ => |x| ^ 3 * energyWeight h s x) ν := by
  have hh0 : 0 < h := by linarith
  have hid := (energyTilt_original_moment_inputs ν hSq hCube hsecond).1
  exact ⟨energyTilt_weighted_integrable ν T h s hT hh0 hs _ measurable_id hid,
    energyTilt_weighted_integrable ν T h s hT hh0 hs _ (by fun_prop) hSq,
    energyTilt_weighted_integrable ν T h s hT hh0 hs _ (by fun_prop) hCube⟩

theorem energyTiltedLaw_moment_integrability (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    Integrable (fun x : ℝ => x) (energyTiltedLaw ν h s) ∧
    Integrable (fun x : ℝ => x ^ 2) (energyTiltedLaw ν h s) ∧
    Integrable (fun x : ℝ => |x| ^ 3) (energyTiltedLaw ν h s) := by
  obtain ⟨hi, hq, hc⟩ := energyTilt_weighted_moment_integrability ν T h s hT hh hs hSq hCube hsecond
  exact ⟨(energyTiltedLaw_integral ν T h s hT hh hs hSq hsecond (fun x : ℝ => x) measurable_id hi).1,
    (energyTiltedLaw_integral ν T h s hT hh hs hSq hsecond _ (by fun_prop) hq).1,
    (energyTiltedLaw_integral ν T h s hT hh hs hSq hsecond _ (by fun_prop) hc).1⟩

theorem energyTilt_first_numerator_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (hmean : (∫ x : ℝ, x ∂ν) = 0) :
    |∫ x : ℝ, x * energyWeight h s x ∂ν| ≤
      energyTiltFirstNumeratorConstant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 2 := by
  have hh0 : 0 < h := by linarith
  have hid := (energyTilt_original_moment_inputs ν hSq hCube hsecond).1
  obtain ⟨hi, _hq, _hc⟩ := energyTilt_weighted_moment_integrability ν T h s hT hh hs hSq hCube hsecond
  obtain ⟨ha, _hq, _hf, _hm, hab, _hqb, _hfb⟩ := energy_third_moment_payments ν h hh0 hCube
  let K : ℝ := Real.exp (4 * T) * T / h ^ 2
  have hlin := integral_sub (μ := ν) hi hid
  rw [hmean, sub_zero] at hlin
  calc
    _ = |∫ x : ℝ, x * energyWeight h s x - x ∂ν| := congrArg abs hlin.symm
    _ ≤ ∫ x : ℝ, (if 2 * h < |x| then |x| else 0) + K * |x| ^ 3 ∂ν := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (ha.add (hCube.const_mul K))
      exact Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, Pi.add_apply, K] using (energyTilt_moment_pointwise T h s x hT hh0 hs).1
    _ = (∫ x : ℝ, if 2 * h < |x| then |x| else 0 ∂ν) + K * (∫ x : ℝ, |x| ^ 3 ∂ν) := by
      rw [integral_add ha (hCube.const_mul K), integral_const_mul]
    _ ≤ (∫ x : ℝ, |x| ^ 3 ∂ν) / (4 * h ^ 2) + K * (∫ x : ℝ, |x| ^ 3 ∂ν) :=
      add_le_add hab le_rfl
    _ = _ := by unfold energyTiltFirstNumeratorConstant; dsimp only [K]; field_simp

theorem energyTilt_second_numerator_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    |(∫ x : ℝ, x ^ 2 * energyWeight h s x ∂ν) - 1| ≤
      energyTiltSecondNumeratorConstant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h := by
  have hh0 : 0 < h := by linarith
  obtain ⟨_hi, hq, _hc⟩ := energyTilt_weighted_moment_integrability ν T h s hT hh hs hSq hCube hsecond
  obtain ⟨_ha, ha, hf, _hm, _hab, hab, hfb⟩ := energy_third_moment_payments ν h hh0 hCube
  let K : ℝ := Real.exp (4 * T) * T / h ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlin := integral_sub (μ := ν) hq hSq
  rw [hsecond] at hlin
  calc
    _ = |∫ x : ℝ, x ^ 2 * energyWeight h s x - x ^ 2 ∂ν| := congrArg abs hlin.symm
    _ ≤ ∫ x : ℝ, (if 2 * h < |x| then x ^ 2 else 0) + K *
        (if |x| ≤ 2 * h then x ^ 4 else 0) ∂ν := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (ha.add (hf.const_mul K))
      exact Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, Pi.add_apply, K] using (energyTilt_moment_pointwise T h s x hT hh0 hs).2
    _ = (∫ x : ℝ, if 2 * h < |x| then x ^ 2 else 0 ∂ν) + K *
        (∫ x : ℝ, if |x| ≤ 2 * h then x ^ 4 else 0 ∂ν) := by
      rw [integral_add ha (hf.const_mul K), integral_const_mul]
    _ ≤ (∫ x : ℝ, |x| ^ 3 ∂ν) / (2 * h) + K * (2 * h * (∫ x : ℝ, |x| ^ 3 ∂ν)) :=
      add_le_add hab (mul_le_mul_of_nonneg_left hfb hK)
    _ = _ := by unfold energyTiltSecondNumeratorConstant; dsimp only [K]; field_simp

theorem energyTilt_third_numerator_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    0 ≤ ∫ x : ℝ, |x| ^ 3 * energyWeight h s x ∂ν ∧
    (∫ x : ℝ, |x| ^ 3 * energyWeight h s x ∂ν) ≤ Real.exp (4 * T) * (∫ x : ℝ, |x| ^ 3 ∂ν) := by
  have hh0 : 0 < h := by linarith
  have hi := (energyTilt_weighted_moment_integrability ν T h s hT hh hs hSq hCube hsecond).2.2
  constructor
  · exact integral_nonneg fun x => mul_nonneg (pow_nonneg (abs_nonneg x) 3) (energyWeight_nonneg h s x)
  · calc
      _ ≤ ∫ x : ℝ, Real.exp (4 * T) * |x| ^ 3 ∂ν :=
        integral_mono hi (hCube.const_mul _) fun x => by
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left (energyWeight_le T h s x hT hh0 hs)
            (pow_nonneg (abs_nonneg x) 3)
      _ = _ := integral_const_mul _ _

theorem energyTilt_inverse_normalizer_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    (energyNormalizer ν h s)⁻¹ ≤ energyTiltInverseNormalizerBound T := by
  have hl := (energyNormalizer_bounds ν T h s hT hh hs hSq hsecond).1
  calc
    _ ≤ 1 / ((3 / 4 : ℝ) * Real.exp (-4 * T)) := by
      simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hl
    _ = _ := by
      unfold energyTiltInverseNormalizerBound
      rw [show -4 * T = -(4 * T) by ring, Real.exp_neg]
      field_simp

theorem energyTilt_normalizer_difference_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    |energyNormalizer ν h s - 1| ≤
      (T + energyNormalizerErrorConstant T) * (∫ x : ℝ, |x| ^ 3 ∂ν) / h := by
  have hh0 : 0 < h := by linarith
  have hβ := (energyTilt_original_moment_inputs ν hSq hCube hsecond).2
  have hβ0 : 0 ≤ ∫ x : ℝ, |x| ^ 3 ∂ν := by linarith
  have hC := energyNormalizerErrorConstant_nonneg T hT
  have hc : |s / h ^ 2| ≤ T / h ^ 2 := by
    rw [abs_div, abs_of_nonneg (sq_nonneg h)]
    exact div_le_div_of_nonneg_right hs (sq_nonneg h)
  have hr1 : 1 / h ^ 2 ≤ (∫ x : ℝ, |x| ^ 3 ∂ν) / h := by
    apply (div_le_div_iff₀ (pow_pos hh0 2) hh0).2
    have hp := mul_le_mul_of_nonneg_right hβ (sq_nonneg h)
    nlinarith
  have hhh : h ≤ h ^ 3 := by
    have hp := mul_nonneg hh0.le (show 0 ≤ h ^ 2 - 1 by nlinarith)
    nlinarith
  have hr3 : (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3 ≤ (∫ x : ℝ, |x| ^ 3 ∂ν) / h := by
    apply (div_le_div_iff₀ (pow_pos hh0 3) hh0).2
    exact mul_le_mul_of_nonneg_left hhh hβ0
  calc
    _ = |(energyNormalizer ν h s - 1 - s / h ^ 2) + s / h ^ 2| := congrArg abs (by ring)
    _ ≤ |energyNormalizer ν h s - 1 - s / h ^ 2| + |s / h ^ 2| := abs_add_le _ _
    _ ≤ energyNormalizerErrorConstant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3 + T / h ^ 2 :=
      add_le_add (energyNormalizer_expansion ν T h s hT hh hs hSq hCube hsecond) hc
    _ ≤ energyNormalizerErrorConstant T * ((∫ x : ℝ, |x| ^ 3 ∂ν) / h) +
        T * ((∫ x : ℝ, |x| ^ 3 ∂ν) / h) := by
      convert add_le_add (mul_le_mul_of_nonneg_left hr3 hC) (mul_le_mul_of_nonneg_left hr1 hT) using 1; ring
    _ = _ := by ring

theorem energyTilt_constants_nonneg (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ energyTiltFirstNumeratorConstant T ∧ 0 ≤ energyTiltSecondNumeratorConstant T ∧
    0 ≤ energyTiltInverseNormalizerBound T ∧ 0 ≤ energyTiltMeanConstant T ∧
    0 ≤ energyTiltSecondMomentConstant T ∧ 0 ≤ energyTiltThirdMomentConstant T := by
  unfold energyTiltMeanConstant energyTiltSecondMomentConstant energyTiltThirdMomentConstant
    energyTiltInverseNormalizerBound energyTiltFirstNumeratorConstant energyTiltSecondNumeratorConstant energyNormalizerErrorConstant
  exact ⟨by positivity, by positivity, by positivity, by positivity, by positivity, by positivity⟩

theorem energyTiltedLaw_mean_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (hmean : (∫ x : ℝ, x ∂ν) = 0) :
    |∫ x : ℝ, x ∂energyTiltedLaw ν h s| ≤
      energyTiltMeanConstant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 2 := by
  have hZ := energyTiltedLaw_normalizer_pos ν T h s hT hh hs hSq hsecond
  have hInv := energyTilt_inverse_normalizer_le ν T h s hT hh hs hSq hsecond
  have hβ := (energyTilt_original_moment_inputs ν hSq hCube hsecond).2
  have hβ0 : 0 ≤ ∫ x : ℝ, |x| ^ 3 ∂ν := by linarith
  have hC := (energyTilt_constants_nonneg T hT).1
  have hi := (energyTilt_weighted_moment_integrability ν T h s hT hh hs hSq hCube hsecond).1
  rw [(energyTiltedLaw_integral ν T h s hT hh hs hSq hsecond (fun x : ℝ => x) measurable_id hi).2,
    abs_div, abs_of_pos hZ, div_eq_mul_inv]
  calc
    _ ≤ (energyTiltFirstNumeratorConstant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 2) *
        energyTiltInverseNormalizerBound T :=
      mul_le_mul (energyTilt_first_numerator_bound ν T h s hT hh hs hSq hCube hsecond hmean) hInv
        (inv_nonneg.mpr hZ.le) (by positivity)
    _ = _ := by unfold energyTiltMeanConstant; ring

theorem energyTiltedLaw_second_moment_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    |(∫ x : ℝ, x ^ 2 ∂energyTiltedLaw ν h s) - 1| ≤
      energyTiltSecondMomentConstant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h := by
  have hh0 : 0 < h := by linarith
  have hZ := energyTiltedLaw_normalizer_pos ν T h s hT hh hs hSq hsecond
  have hInv := energyTilt_inverse_normalizer_le ν T h s hT hh hs hSq hsecond
  have hβ := (energyTilt_original_moment_inputs ν hSq hCube hsecond).2
  have hβ0 : 0 ≤ ∫ x : ℝ, |x| ^ 3 ∂ν := by linarith
  have hC2 := (energyTilt_constants_nonneg T hT).2.1
  have hCZ := energyNormalizerErrorConstant_nonneg T hT
  have hi := (energyTilt_weighted_moment_integrability ν T h s hT hh hs hSq hCube hsecond).2.1
  let M2 : ℝ := ∫ x : ℝ, x ^ 2 * energyWeight h s x ∂ν
  have hdiff : |M2 - energyNormalizer ν h s| ≤
      (energyTiltSecondNumeratorConstant T + T + energyNormalizerErrorConstant T) *
        (∫ x : ℝ, |x| ^ 3 ∂ν) / h := by
    calc
      _ = |(M2 - 1) - (energyNormalizer ν h s - 1)| := congrArg abs (by ring)
      _ ≤ |M2 - 1| + |energyNormalizer ν h s - 1| := abs_sub _ _
      _ ≤ energyTiltSecondNumeratorConstant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h +
          (T + energyNormalizerErrorConstant T) * (∫ x : ℝ, |x| ^ 3 ∂ν) / h :=
        add_le_add (energyTilt_second_numerator_bound ν T h s hT hh hs hSq hCube hsecond)
          (energyTilt_normalizer_difference_bound ν T h s hT hh hs hSq hCube hsecond)
      _ = _ := by ring
  rw [(energyTiltedLaw_integral ν T h s hT hh hs hSq hsecond _ (by fun_prop) hi).2]
  change |M2 / energyNormalizer ν h s - 1| ≤ _
  rw [show M2 / energyNormalizer ν h s - 1 = (M2 - energyNormalizer ν h s) / energyNormalizer ν h s by
      field_simp, abs_div, abs_of_pos hZ, div_eq_mul_inv]
  calc
    _ ≤ ((energyTiltSecondNumeratorConstant T + T + energyNormalizerErrorConstant T) *
        (∫ x : ℝ, |x| ^ 3 ∂ν) / h) * energyTiltInverseNormalizerBound T :=
      mul_le_mul hdiff hInv (inv_nonneg.mpr hZ.le) (by positivity)
    _ = _ := by unfold energyTiltSecondMomentConstant; ring

theorem energyTiltedLaw_third_moment_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    (∫ x : ℝ, |x| ^ 3 ∂energyTiltedLaw ν h s) ≤
      energyTiltThirdMomentConstant T * (∫ x : ℝ, |x| ^ 3 ∂ν) := by
  have hZ := energyTiltedLaw_normalizer_pos ν T h s hT hh hs hSq hsecond
  have hInv := energyTilt_inverse_normalizer_le ν T h s hT hh hs hSq hsecond
  have hβ := (energyTilt_original_moment_inputs ν hSq hCube hsecond).2
  have hβ0 : 0 ≤ ∫ x : ℝ, |x| ^ 3 ∂ν := by linarith
  have hi := (energyTilt_weighted_moment_integrability ν T h s hT hh hs hSq hCube hsecond).2.2
  rw [(energyTiltedLaw_integral ν T h s hT hh hs hSq hsecond _ (by fun_prop) hi).2, div_eq_mul_inv]
  calc
    _ ≤ (Real.exp (4 * T) * (∫ x : ℝ, |x| ^ 3 ∂ν)) * energyTiltInverseNormalizerBound T :=
      mul_le_mul (energyTilt_third_numerator_bound ν T h s hT hh hs hSq hCube hsecond).2 hInv
        (inv_nonneg.mpr hZ.le) (mul_nonneg (Real.exp_nonneg _) hβ0)
    _ = _ := by unfold energyTiltThirdMomentConstant; ring

end Shao.OQ4
