import Shao.OQ4.EnergyTiltedLaw

/-! The actual linear tilt family over the fixed supported energy law, for every real parameter. -/

namespace Shao.OQ4

open MeasureTheory

noncomputable def energyLinearNormalizer (ν : Measure ℝ) (h s t : ℝ) : ℝ :=
  ∫ x : ℝ, Real.exp (t * x) ∂energyTiltedLaw ν h s

noncomputable def energyLinearFirstNumerator (ν : Measure ℝ) (h s t : ℝ) : ℝ :=
  ∫ x : ℝ, x * Real.exp (t * x) ∂energyTiltedLaw ν h s

noncomputable def energyLinearSecondNumerator (ν : Measure ℝ) (h s t : ℝ) : ℝ :=
  ∫ x : ℝ, x ^ 2 * Real.exp (t * x) ∂energyTiltedLaw ν h s

noncomputable def energyLinearThirdNumerator (ν : Measure ℝ) (h s t : ℝ) : ℝ :=
  ∫ x : ℝ, |x| ^ 3 * Real.exp (t * x) ∂energyTiltedLaw ν h s

noncomputable def energyLinearTiltLaw (ν : Measure ℝ) (h s t : ℝ) : Measure ℝ :=
  (energyTiltedLaw ν h s).withDensity
    (fun x => ENNReal.ofReal (Real.exp (t * x) / energyLinearNormalizer ν h s t))

noncomputable def energyLinearMean (ν : Measure ℝ) (h s t : ℝ) : ℝ :=
  energyLinearFirstNumerator ν h s t / energyLinearNormalizer ν h s t

theorem energyLinear_density_measurable (ν : Measure ℝ) (h s t : ℝ) :
    Measurable (fun x => ENNReal.ofReal (Real.exp (t * x) / energyLinearNormalizer ν h s t)) := by
  exact (show Measurable (fun x : ℝ => Real.exp (t * x) / energyLinearNormalizer ν h s t) by
    fun_prop).ennreal_ofReal

/-- Only a closed-interval point is used here; global exponential boundedness is not asserted. -/
theorem energyLinear_exponent_bounds (h t x : ℝ) (hx : |x| ≤ 2 * h) :
    -2 * h * |t| ≤ t * x ∧ t * x ≤ 2 * h * |t| := by
  have ha : |t * x| ≤ 2 * h * |t| := by
    rw [abs_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hx (abs_nonneg t)
  have hb := abs_le.mp ha
  exact ⟨by linarith [hb.1], hb.2⟩

/-- Absolute continuity transfers the same actual energy-law almost-everywhere support. -/
theorem energyLinearTiltLaw_ae_support (ν : Measure ℝ) (h s t : ℝ) :
    ∀ᵐ x ∂energyLinearTiltLaw ν h s t, |x| ≤ 2 * h := by
  apply (ae_withDensity_iff (energyLinear_density_measurable ν h s t)).2
  filter_upwards [energyTiltedLaw_ae_support ν h s] with x hx
  exact fun _ => hx

section Admissible

variable (ν : Measure ℝ) [IsProbabilityMeasure ν] (T h s : ℝ)
  (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
  (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)

include hT hh hs hSq hsecond

/-- All natural absolute powers may be handled uniformly on this same almost-everywhere support. -/
theorem energyLinear_power_exp_integrable (k : ℕ) (t : ℝ) :
    Integrable (fun x : ℝ => |x| ^ k * Real.exp (t * x)) (energyTiltedLaw ν h s) := by
  have : IsProbabilityMeasure (energyTiltedLaw ν h s) :=
    energyTiltedLaw_isProbabilityMeasure ν T h s hT hh hs hSq hsecond
  apply Integrable.of_bound (by fun_prop) ((2 * h) ^ k * Real.exp (2 * h * |t|))
  filter_upwards [energyTiltedLaw_ae_support ν h s] with x hx
  have hp := pow_le_pow_left₀ (abs_nonneg x) hx k
  have he := Real.exp_le_exp.mpr (energyLinear_exponent_bounds h t x hx).2
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (abs_nonneg x) k),
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul hp he (Real.exp_nonneg _) (pow_nonneg (by linarith) k)

theorem energyLinear_integrability (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (energyTiltedLaw ν h s) ∧
    Integrable (fun x : ℝ => x * Real.exp (t * x)) (energyTiltedLaw ν h s) ∧
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (t * x)) (energyTiltedLaw ν h s) ∧
    Integrable (fun x : ℝ => |x| ^ 3 * Real.exp (t * x)) (energyTiltedLaw ν h s) := by
  refine ⟨?_, ?_, ?_, energyLinear_power_exp_integrable ν T h s hT hh hs hSq hsecond 3 t⟩
  · simpa only [pow_zero, one_mul] using
      energyLinear_power_exp_integrable ν T h s hT hh hs hSq hsecond 0 t
  · apply (energyLinear_power_exp_integrable ν T h s hT hh hs hSq hsecond 1 t).mono'
      (show Measurable (fun x : ℝ => x * Real.exp (t * x)) by fun_prop).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), pow_one, le_refl]
  · simpa only [sq_abs] using
      energyLinear_power_exp_integrable ν T h s hT hh hs hSq hsecond 2 t

theorem energyLinearNormalizer_bounds (t : ℝ) :
    Real.exp (-2 * h * |t|) ≤ energyLinearNormalizer ν h s t ∧
      energyLinearNormalizer ν h s t ≤ Real.exp (2 * h * |t|) := by
  have : IsProbabilityMeasure (energyTiltedLaw ν h s) :=
    energyTiltedLaw_isProbabilityMeasure ν T h s hT hh hs hSq hsecond
  have hi := (energyLinear_integrability ν T h s hT hh hs hSq hsecond t).1
  have he : ∀ᵐ x ∂energyTiltedLaw ν h s,
      Real.exp (-2 * h * |t|) ≤ Real.exp (t * x) ∧ Real.exp (t * x) ≤ Real.exp (2 * h * |t|) := by
    filter_upwards [energyTiltedLaw_ae_support ν h s] with x hx
    exact ⟨Real.exp_le_exp.mpr (energyLinear_exponent_bounds h t x hx).1,
      Real.exp_le_exp.mpr (energyLinear_exponent_bounds h t x hx).2⟩
  constructor
  · simpa only [energyLinearNormalizer, integral_const, probReal_univ, smul_eq_mul, one_mul] using
      integral_mono_ae (integrable_const _) hi (he.mono fun _ hx => hx.1)
  · simpa only [energyLinearNormalizer, integral_const, probReal_univ, smul_eq_mul, one_mul] using
      integral_mono_ae hi (integrable_const _) (he.mono fun _ hx => hx.2)

theorem energyLinearNormalizer_pos (t : ℝ) : 0 < energyLinearNormalizer ν h s t :=
  lt_of_lt_of_le (Real.exp_pos _) (energyLinearNormalizer_bounds ν T h s hT hh hs hSq hsecond t).1

theorem energyLinearTiltLaw_isProbabilityMeasure (t : ℝ) :
    IsProbabilityMeasure (energyLinearTiltLaw ν h s t) := by
  have hL := energyLinearNormalizer_pos ν T h s hT hh hs hSq hsecond t
  have hi := (energyLinear_integrability ν T h s hT hh hs hSq hsecond t).1
  constructor
  rw [energyLinearTiltLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const (energyLinearNormalizer ν h s t))
      (Filter.Eventually.of_forall fun x => div_nonneg (Real.exp_nonneg _) hL.le), integral_div]
  change ENNReal.ofReal (energyLinearNormalizer ν h s t / energyLinearNormalizer ν h s t) = 1
  simp [ne_of_gt hL]

theorem energyLinearTiltLaw_real_apply (t : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    (energyLinearTiltLaw ν h s t).real A =
      (∫ x in A, Real.exp (t * x) ∂energyTiltedLaw ν h s) / energyLinearNormalizer ν h s t := by
  have hL := energyLinearNormalizer_pos ν T h s hT hh hs hSq hsecond t
  have hi := (energyLinear_integrability ν T h s hT hh hs hSq hsecond t).1
  have hp (x : ℝ) : 0 ≤ Real.exp (t * x) / energyLinearNormalizer ν h s t :=
    div_nonneg (Real.exp_nonneg _) hL.le
  rw [energyLinearTiltLaw, measureReal_def, withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const (energyLinearNormalizer ν h s t)).restrict
      (Filter.Eventually.of_forall hp), ENNReal.toReal_ofReal (integral_nonneg hp), integral_div]

theorem energyLinearTiltLaw_integral (t : ℝ) (f : ℝ → ℝ) (_hf : Measurable f)
    (hfw : Integrable (fun x => f x * Real.exp (t * x)) (energyTiltedLaw ν h s)) :
    Integrable f (energyLinearTiltLaw ν h s t) ∧
    (∫ x : ℝ, f x ∂energyLinearTiltLaw ν h s t) =
      (∫ x : ℝ, f x * Real.exp (t * x) ∂energyTiltedLaw ν h s) / energyLinearNormalizer ν h s t := by
  have hL := energyLinearNormalizer_pos ν T h s hT hh hs hSq hsecond t
  have hp (x : ℝ) : 0 ≤ Real.exp (t * x) / energyLinearNormalizer ν h s t :=
    div_nonneg (Real.exp_nonneg _) hL.le
  have htop : ∀ᵐ x ∂energyTiltedLaw ν h s,
      ENNReal.ofReal (Real.exp (t * x) / energyLinearNormalizer ν h s t) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  constructor
  · apply (integrable_withDensity_iff (energyLinear_density_measurable ν h s t) htop).2
    convert hfw.div_const (energyLinearNormalizer ν h s t) using 1
    ext x
    rw [ENNReal.toReal_ofReal (hp x)]
    ring
  · rw [energyLinearTiltLaw,
      integral_withDensity_eq_integral_toReal_smul (energyLinear_density_measurable ν h s t) htop]
    simp_rw [ENNReal.toReal_ofReal (hp _), smul_eq_mul]
    calc
      _ = ∫ x : ℝ, (f x * Real.exp (t * x)) / energyLinearNormalizer ν h s t ∂energyTiltedLaw ν h s := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = _ := integral_div _ _

theorem energyLinearTiltLaw_moments (t : ℝ) :
    Integrable (fun x : ℝ => x) (energyLinearTiltLaw ν h s t) ∧
    Integrable (fun x : ℝ => x ^ 2) (energyLinearTiltLaw ν h s t) ∧
    Integrable (fun x : ℝ => |x| ^ 3) (energyLinearTiltLaw ν h s t) ∧
    (∫ x : ℝ, x ∂energyLinearTiltLaw ν h s t) =
      energyLinearFirstNumerator ν h s t / energyLinearNormalizer ν h s t ∧
    (∫ x : ℝ, x ∂energyLinearTiltLaw ν h s t) = energyLinearMean ν h s t ∧
    (∫ x : ℝ, x ^ 2 ∂energyLinearTiltLaw ν h s t) =
      energyLinearSecondNumerator ν h s t / energyLinearNormalizer ν h s t ∧
    (∫ x : ℝ, |x| ^ 3 ∂energyLinearTiltLaw ν h s t) =
      energyLinearThirdNumerator ν h s t / energyLinearNormalizer ν h s t := by
  obtain ⟨_he, hi, hq, hc⟩ := energyLinear_integrability ν T h s hT hh hs hSq hsecond t
  have h1 := energyLinearTiltLaw_integral ν T h s hT hh hs hSq hsecond t (fun x : ℝ => x) measurable_id hi
  have h2 := energyLinearTiltLaw_integral ν T h s hT hh hs hSq hsecond t (fun x : ℝ => x ^ 2) (by fun_prop) hq
  have h3 := energyLinearTiltLaw_integral ν T h s hT hh hs hSq hsecond t (fun x : ℝ => |x| ^ 3) (by fun_prop) hc
  exact ⟨h1.1, h2.1, h3.1, h1.2, h1.2, h2.2, h3.2⟩

theorem energyLinearNormalizer_zero : energyLinearNormalizer ν h s 0 = 1 := by
  have : IsProbabilityMeasure (energyTiltedLaw ν h s) :=
    energyTiltedLaw_isProbabilityMeasure ν T h s hT hh hs hSq hsecond
  simp [energyLinearNormalizer]

theorem energyLinearTiltLaw_zero : energyLinearTiltLaw ν h s 0 = energyTiltedLaw ν h s := by
  unfold energyLinearTiltLaw
  rw [energyLinearNormalizer_zero ν T h s hT hh hs hSq hsecond]
  simp

theorem energyLinearMean_zero : energyLinearMean ν h s 0 = ∫ x : ℝ, x ∂energyTiltedLaw ν h s := by
  unfold energyLinearMean
  rw [energyLinearNormalizer_zero ν T h s hT hh hs hSq hsecond]
  simp [energyLinearFirstNumerator]

end Admissible

end Shao.OQ4
