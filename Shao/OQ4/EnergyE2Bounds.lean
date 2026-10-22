import Shao.OQ4.EnergyLinearTiltCentering

/-! The actual small-parameter log error and one common finite E2 interface. -/

namespace Shao.OQ4

open MeasureTheory

noncomputable def energyE2Threshold (M T : ℝ) : ℝ := energyLinearCenteringThreshold M T

noncomputable def energyE2Constant (M T : ℝ) : ℝ :=
  1 + energyLinearCenteringK M T +
    energyLinearCenteringK M T * (energyLinearVarianceA M T + 2 * energyLinearCenteringK M T) +
    (energyLinearVarianceA M T + energyLinearVarianceB M T (energyLinearCenteringK M T)) +
    Real.exp 2 * energyLinearVarianceA M T

theorem energyE2Constant_dominates (M T : ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T) :
    1 ≤ energyE2Constant M T ∧ energyLinearCenteringK M T ≤ energyE2Constant M T ∧
    energyLinearCenteringK M T * (energyLinearVarianceA M T + 2 * energyLinearCenteringK M T) ≤ energyE2Constant M T ∧
    energyLinearVarianceA M T + energyLinearVarianceB M T (energyLinearCenteringK M T) ≤ energyE2Constant M T ∧
    Real.exp 2 * energyLinearVarianceA M T ≤ energyE2Constant M T := by
  have hK := energyLinearCentering_K_pos M T hM hT
  obtain ⟨hA, hB, _hC⟩ := energyLinearVariance_constants_nonneg M T (energyLinearCenteringK M T) hM hT hK.le
  have hp : 0 ≤ energyLinearCenteringK M T * (energyLinearVarianceA M T + 2 * energyLinearCenteringK M T) := by positivity
  have hq := add_nonneg hA hB
  have hr := mul_nonneg (Real.exp_nonneg 2) hA
  unfold energyE2Constant
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- A genuine MVT bound with separate positive, negative and zero parameter cases. -/
theorem energyE2_abs_sub_zero_bound (f f' : ℝ → ℝ) (C t : ℝ) (hc : Continuous f)
    (hd : ∀ u : ℝ, HasDerivAt f (f' u) u) (hb : ∀ u : ℝ, |u| ≤ |t| → |f' u| ≤ C) :
    |f t - f 0| ≤ C * |t| := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · obtain ⟨c, hcmem, heq⟩ := exists_hasDerivAt_eq_slope f f' ht hc.continuousOn (fun u _ => hd u)
    have hcu : |c| ≤ |t| := by
      rw [abs_of_neg ht]
      exact abs_le.mpr ⟨by linarith [hcmem.1], by linarith [hcmem.2]⟩
    have heq' : f 0 - f t = f' c * (0 - t) := ((eq_div_iff (by linarith : (0 : ℝ) - t ≠ 0)).1 heq).symm
    calc
      _ = |f 0 - f t| := abs_sub_comm _ _
      _ = |f' c| * |0 - t| := by rw [heq', abs_mul]
      _ ≤ C * |0 - t| := mul_le_mul_of_nonneg_right (hb c hcu) (abs_nonneg _)
      _ = _ := by simp
  · subst t
    simp
  · obtain ⟨c, hcmem, heq⟩ := exists_hasDerivAt_eq_slope f f' ht hc.continuousOn (fun u _ => hd u)
    have hcu : |c| ≤ |t| := by
      rw [abs_of_pos ht]
      exact abs_le.mpr ⟨by linarith [hcmem.1], by linarith [hcmem.2]⟩
    have heq' : f t - f 0 = f' c * (t - 0) := ((eq_div_iff (by linarith : t - (0 : ℝ) ≠ 0)).1 heq).symm
    calc
      _ = |f' c| * |t - 0| := by rw [heq', abs_mul]
      _ ≤ C * |t - 0| := mul_le_mul_of_nonneg_right (hb c hcu) (abs_nonneg _)
      _ = _ := by simp

section Admissible

variable (ν : Measure ℝ) [IsProbabilityMeasure ν] (M T h s : ℝ)
  (hM : 0 ≤ M) (hT : 0 ≤ T) (hh : energyE2Threshold M T ≤ h) (hs : |s| ≤ T)
  (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
  (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0)
  (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M)

include hM hT hh hs hSq hCube hsecond hmean hβM

/-- The actual mean is uniformly small by the actual derivative upper bound and E1 at zero. -/
theorem energyE2_mean_small (u : ℝ) (hu : |u| ≤ energyLinearCenteringK M T / h ^ 2) :
    |energyLinearMean ν h s u| ≤ (energyLinearVarianceA M T + 2 * energyLinearCenteringK M T) / h ^ 2 := by
  have hheight := energyLinearCentering_height_bounds M T h hM hT hh
  have hh1 : 1 ≤ h := by linarith [hheight.2.2.1]
  have hcont := (energyLinear_family_continuous ν T h s hT hh1 hs hSq hsecond hCube).2.2.1
  let v : ℝ → ℝ := fun t => ∫ x : ℝ, (x - energyLinearMean ν h s t) ^ 2 ∂energyLinearTiltLaw ν h s t
  have hd (t : ℝ) : HasDerivAt (energyLinearMean ν h s) (v t) t :=
    energyLinearMean_hasDerivAt_centeredSquare ν T h s hT hh1 hs hSq hsecond hCube t
  have hb (t : ℝ) (ht : |t| ≤ |u|) : |v t| ≤ 2 := by
    have hw := energyLinearVariance_window ν M T (energyLinearCenteringK M T) h s
      hM hT hheight.1.le hh hs hSq hCube hsecond hmean hβM t (ht.trans hu)
    exact abs_le.mpr ⟨by linarith [hw.2.2.2.2.2.1.1], hw.2.2.2.2.2.1.2⟩
  have hdiff := energyE2_abs_sub_zero_bound (energyLinearMean ν h s) v 2 u hcont hd hb
  obtain ⟨hzero, hinit⟩ := energyLinearCentering_initial_mean ν M T h s hM hT hh hs hSq hCube hsecond hmean hβM
  rw [← hzero] at hinit
  calc
    _ = |(energyLinearMean ν h s u - energyLinearMean ν h s 0) + energyLinearMean ν h s 0| := congrArg abs (by ring)
    _ ≤ |energyLinearMean ν h s u - energyLinearMean ν h s 0| + |energyLinearMean ν h s 0| := abs_add_le _ _
    _ ≤ 2 * |u| + energyLinearVarianceA M T / h ^ 2 := add_le_add hdiff hinit
    _ ≤ 2 * (energyLinearCenteringK M T / h ^ 2) + energyLinearVarianceA M T / h ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
    _ = _ := by ring

/-- The genuine logarithmic derivative and a second MVT pay the frozen h⁻⁴ coefficient. -/
theorem energyE2_log_bound (t : ℝ) (ht : |t| ≤ energyLinearCenteringK M T / h ^ 2) :
    |Real.log (energyLinearNormalizer ν h s t)| ≤
      energyLinearCenteringK M T * (energyLinearVarianceA M T + 2 * energyLinearCenteringK M T) / h ^ 4 := by
  have hheight := energyLinearCentering_height_bounds M T h hM hT hh
  have hh1 : 1 ≤ h := by linarith [hheight.2.2.1]
  have hcont := (energyLinear_family_continuous ν T h s hT hh1 hs hSq hsecond hCube).2.2.2
  have hd (u : ℝ) : HasDerivAt (fun z => Real.log (energyLinearNormalizer ν h s z)) (energyLinearMean ν h s u) u :=
    energyLinear_logNormalizer_hasDerivAt ν T h s hT hh1 hs hSq hsecond hCube u
  have hb (u : ℝ) (hu : |u| ≤ |t|) :
      |energyLinearMean ν h s u| ≤ (energyLinearVarianceA M T + 2 * energyLinearCenteringK M T) / h ^ 2 :=
    energyE2_mean_small ν M T h s hM hT hh hs hSq hCube hsecond hmean hβM u (hu.trans ht)
  have hdiff := energyE2_abs_sub_zero_bound (fun z => Real.log (energyLinearNormalizer ν h s z))
    (energyLinearMean ν h s) ((energyLinearVarianceA M T + 2 * energyLinearCenteringK M T) / h ^ 2) t hcont hd hb
  have hzero : Real.log (energyLinearNormalizer ν h s 0) = 0 := by
    rw [energyLinearNormalizer_zero ν T h s hT hh1 hs hSq hsecond, Real.log_one]
  rw [hzero, sub_zero] at hdiff
  have hA := (energyLinearVariance_constants_nonneg M T (energyLinearCenteringK M T) hM hT hheight.1.le).1
  calc
    _ ≤ ((energyLinearVarianceA M T + 2 * energyLinearCenteringK M T) / h ^ 2) * |t| := hdiff
    _ ≤ ((energyLinearVarianceA M T + 2 * energyLinearCenteringK M T) / h ^ 2) * (energyLinearCenteringK M T / h ^ 2) :=
      mul_le_mul_of_nonneg_left ht (div_nonneg (add_nonneg hA (mul_nonneg (by norm_num) hheight.1.le)) (sq_nonneg h))
    _ = _ := by ring

end Admissible

/-- A transparent conclusion for one θ and the same actual probability law, never a premise. -/
def energyE2Conclusion (ν : Measure ℝ) (M T h s θ : ℝ) : Prop :=
  energyLinearMean ν h s θ = 0 ∧
  IsProbabilityMeasure (energyLinearTiltLaw ν h s θ) ∧
  (∀ᵐ x ∂energyLinearTiltLaw ν h s θ, |x| ≤ 2 * h) ∧
  Integrable (fun x : ℝ => x) (energyLinearTiltLaw ν h s θ) ∧
  Integrable (fun x : ℝ => x ^ 2) (energyLinearTiltLaw ν h s θ) ∧
  Integrable (fun x : ℝ => |x| ^ 3) (energyLinearTiltLaw ν h s θ) ∧
  (∫ x : ℝ, x ∂energyLinearTiltLaw ν h s θ) = 0 ∧
  |θ| ≤ energyE2Constant M T / h ^ 2 ∧
  |Real.log (energyLinearNormalizer ν h s θ)| ≤ energyE2Constant M T / h ^ 4 ∧
  |(∫ x : ℝ, x ^ 2 ∂energyLinearTiltLaw ν h s θ) - 1| ≤ energyE2Constant M T / h ∧
  (∫ x : ℝ, |x| ^ 3 ∂energyLinearTiltLaw ν h s θ) ≤ energyE2Constant M T

/-- A common explicit C2 and H2 for every law in the frozen third-moment class. -/
theorem energyE2_common_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν] (M T h s : ℝ)
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hh : energyE2Threshold M T ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M) : ∃ θ : ℝ, energyE2Conclusion ν M T h s θ := by
  obtain ⟨θ, hθ, hmeanθ, hprob, hsupport, hi, hq, hc, hmeanInt⟩ :=
    energyLinearCentering_law ν M T h s hM hT hh hs hSq hCube hsecond hmean hβM
  have hheight := energyLinearCentering_height_bounds M T h hM hT hh
  have hhpos : 0 < h := by linarith [hheight.2.2.1]
  have hh1 : 1 ≤ h := by linarith [hheight.2.2.1]
  obtain ⟨_hC1, hCK, hClog, hCq, hCr⟩ := energyE2Constant_dominates M T hM hT
  obtain ⟨_hChange, hQerr, _hQsmall, _hMean, _hMeanSmall⟩ := energyLinearVariance_moment_bounds
    ν M T (energyLinearCenteringK M T) h s hM hT hheight.1.le hh hs hSq hCube hsecond hmean hβM θ hθ
  have hlog := energyE2_log_bound ν M T h s hM hT hh hs hSq hCube hsecond hmean hβM θ hθ
  have hthird := (energyLinear_normalized_comparisons ν T h s hT hh1 hs hSq hsecond θ).2.2
  have hD := energyLinearVariance_exponential_bound M T (energyLinearCenteringK M T) h θ hM hT hheight.1.le hh hθ
  have hinit := energyLinearVariance_initial_bounds ν M T (energyLinearCenteringK M T) h s
    hM hT hheight.1.le hh hs hSq hCube hsecond hmean hβM
  obtain ⟨hA, hB, _hC⟩ := energyLinearVariance_constants_nonneg M T (energyLinearCenteringK M T) hM hT hheight.1.le
  have hBdiv : energyLinearVarianceB M T (energyLinearCenteringK M T) / h ^ 2 ≤
      energyLinearVarianceB M T (energyLinearCenteringK M T) / h := by
    apply (div_le_div_iff₀ (pow_pos hhpos 2) hhpos).2
    exact mul_le_mul_of_nonneg_left (by nlinarith : h ≤ h ^ 2) hB
  refine ⟨θ, hmeanθ, hprob, hsupport, hi, hq, hc, hmeanInt, ?_, ?_, ?_, ?_⟩
  · exact hθ.trans (div_le_div_of_nonneg_right hCK (sq_nonneg h))
  · exact hlog.trans (div_le_div_of_nonneg_right hClog (by positivity))
  · calc
      _ ≤ energyLinearVarianceA M T / h + energyLinearVarianceB M T (energyLinearCenteringK M T) / h ^ 2 := hQerr
      _ ≤ energyLinearVarianceA M T / h + energyLinearVarianceB M T (energyLinearCenteringK M T) / h := add_le_add le_rfl hBdiv
      _ = (energyLinearVarianceA M T + energyLinearVarianceB M T (energyLinearCenteringK M T)) / h := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hCq hhpos.le
  · have hr0 : 0 ≤ ∫ x : ℝ, |x| ^ 3 ∂energyTiltedLaw ν h s := integral_nonneg fun _ => pow_nonneg (abs_nonneg _) 3
    exact hthird.trans ((mul_le_mul hD hinit.2.2.2.2.2.2 hr0 (Real.exp_nonneg _)).trans hCr)

/-- Fixed-law specialization uses the same formulas with M equal to the actual third moment. -/
theorem energyE2_fixed_law_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν] (T h s : ℝ)
    (hT : 0 ≤ T) (hh : energyE2Threshold (∫ x : ℝ, |x| ^ 3 ∂ν) T ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0) :
    ∃ θ : ℝ, energyE2Conclusion ν (∫ x : ℝ, |x| ^ 3 ∂ν) T h s θ :=
  energyE2_common_bounds ν (∫ x : ℝ, |x| ^ 3 ∂ν) T h s
    (integral_nonneg fun _ => pow_nonneg (abs_nonneg _) 3) hT hh hs hSq hCube hsecond hmean le_rfl

end Shao.OQ4
