import Shao.Probability.QuadraticChordNoise

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

private lemma triangle_weight_nonneg (r : ℝ) :
    0 ≤ (if |r| ≤ 1 then 1 - |r| else 0 : ℝ) := by
  split_ifs with h
  · linarith
  · exact le_rfl

private lemma triangle_weight_measurable :
    Measurable (fun r : ℝ => if |r| ≤ 1 then 1 - |r| else (0 : ℝ)) := by
  exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    (measurable_const.sub continuous_abs.measurable) measurable_const

private lemma triangle_support : ∀ᵐ r : ℝ ∂quadraticTriangleLaw, |r| ≤ 1 := by
  rw [ae_iff]
  change volume.withDensity _ {r : ℝ | ¬ |r| ≤ 1} = 0
  have hs : MeasurableSet {r : ℝ | ¬ |r| ≤ 1} :=
    (measurableSet_le continuous_abs.measurable measurable_const).compl
  rw [withDensity_apply _ hs]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem hs] with r hr
  simp [hr]

private lemma bounded_integrable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ)
    (hf : Measurable f) (b : ℝ) (hb : ∀ᵐ x ∂μ, |f x| ≤ b) : Integrable f μ := by
  exact (integrable_const b).mono' hf.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hb)

private lemma real_density_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (w : α → ℝ) (hw : Measurable w) (hn : ∀ x, 0 ≤ w x) (g : α → ℝ) :
    (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (w x))) =
      ∫ x, w x * g x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hn _), smul_eq_mul]

private lemma triangle_integral (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ r : ℝ, g r ∂quadraticTriangleLaw) =
      (∫ r : ℝ in (-1)..0, (1 + r) * g r) +
      (∫ r : ℝ in 0..1, (1 - r) * g r) := by
  unfold quadraticTriangleLaw
  rw [real_density_integral volume _ triangle_weight_measurable triangle_weight_nonneg]
  have he : (fun r : ℝ => (if |r| ≤ 1 then 1 - |r| else 0 : ℝ) * g r) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun r => (1 - |r|) * g r) := by
    funext r
    by_cases h : r ∈ Set.Icc (-1 : ℝ) 1
    · simp [h, abs_le.mpr h]
    · have ha : ¬ |r| ≤ 1 := fun ha => h (abs_le.mp ha)
      simp [h, ha]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hc : Continuous (fun r : ℝ => (1 - |r|) * g r) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-1) 0)
    (hc.intervalIntegrable 0 1)]
  congr 1
  · apply intervalIntegral.integral_congr
    intro r hr
    have hr0 : r ≤ 0 := by simpa using hr.2
    dsimp only
    rw [abs_of_nonpos hr0]
    ring
  · apply intervalIntegral.integral_congr
    intro r hr
    have hr0 : 0 ≤ r := by simpa using hr.1
    dsimp only
    rw [abs_of_nonneg hr0]

private lemma integral_pow_add (a b : ℝ) (m n : ℕ) :
    (∫ r : ℝ in a..b, r ^ m + r ^ n) =
      (b ^ (m + 1) - a ^ (m + 1)) / (m + 1) +
        (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) := by
  have hm : IntervalIntegrable (fun r : ℝ => r ^ m) volume a b :=
    (by fun_prop : Continuous (fun r : ℝ => r ^ m)).intervalIntegrable _ _
  have hn : IntervalIntegrable (fun r : ℝ => r ^ n) volume a b :=
    (by fun_prop : Continuous (fun r : ℝ => r ^ n)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hm hn, integral_pow, integral_pow]

private lemma integral_pow_sub (a b : ℝ) (m n : ℕ) :
    (∫ r : ℝ in a..b, r ^ m - r ^ n) =
      (b ^ (m + 1) - a ^ (m + 1)) / (m + 1) -
        (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) := by
  have hm : IntervalIntegrable (fun r : ℝ => r ^ m) volume a b :=
    (by fun_prop : Continuous (fun r : ℝ => r ^ m)).intervalIntegrable _ _
  have hn : IntervalIntegrable (fun r : ℝ => r ^ n) volume a b :=
    (by fun_prop : Continuous (fun r : ℝ => r ^ n)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hm hn, integral_pow, integral_pow]

theorem quadraticTriangle_moments :
    Integrable (fun t : ℝ => t) quadraticTriangleLaw ∧
    Integrable (fun t : ℝ => |t|) quadraticTriangleLaw ∧
    Integrable (fun t : ℝ => t ^ 2) quadraticTriangleLaw ∧
    (∫ t : ℝ, t ∂quadraticTriangleLaw) = 0 ∧
    (∫ t : ℝ, |t| ∂quadraticTriangleLaw) = (1 / 3 : ℝ) ∧
    (∫ t : ℝ, t ^ 2 ∂quadraticTriangleLaw) = (1 / 6 : ℝ) := by
  let := quadraticTriangle_probability_char.1
  have hsq : ∀ᵐ t : ℝ ∂quadraticTriangleLaw, |t ^ 2| ≤ 1 := by
    filter_upwards [triangle_support] with t ht
    simpa only [abs_pow, one_pow] using pow_le_pow_left₀ (abs_nonneg t) ht 2
  refine ⟨bounded_integrable _ _ measurable_id 1 triangle_support,
    bounded_integrable _ _ continuous_abs.measurable 1 (by simpa using triangle_support),
    bounded_integrable _ _ (by fun_prop) 1 hsq, ?_, ?_, ?_⟩
  · rw [triangle_integral (fun r : ℝ => r) continuous_id]
    have hleft : (fun r : ℝ => (1 + r) * r) = (fun r => r ^ 1 + r ^ 2) := by
      funext r; ring
    have hright : (fun r : ℝ => (1 - r) * r) = (fun r => r ^ 1 - r ^ 2) := by
      funext r; ring
    rw [hleft, hright, integral_pow_add, integral_pow_sub]
    norm_num
  · rw [triangle_integral _ continuous_abs]
    have hleft : (∫ r : ℝ in (-1)..0, (1 + r) * |r|) =
        -(∫ r : ℝ in (-1)..0, r ^ 1 + r ^ 2) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro r hr
      have hr0 : r ≤ 0 := by simpa using hr.2
      dsimp only
      rw [abs_of_nonpos hr0]
      ring
    have hright : (∫ r : ℝ in 0..1, (1 - r) * |r|) =
        (∫ r : ℝ in 0..1, r ^ 1 - r ^ 2) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr0 : 0 ≤ r := by simpa using hr.1
      dsimp only
      rw [abs_of_nonneg hr0]
      ring
    rw [hleft, hright, integral_pow_add, integral_pow_sub]
    norm_num
  · rw [triangle_integral (fun r : ℝ => r ^ 2) (continuous_id.pow 2)]
    have hleft : (fun r : ℝ => (1 + r) * r ^ 2) = (fun r => r ^ 2 + r ^ 3) := by
      funext r; ring
    have hright : (fun r : ℝ => (1 - r) * r ^ 2) = (fun r => r ^ 2 - r ^ 3) := by
      funext r; ring
    rw [hleft, hright, integral_pow_add, integral_pow_sub]
    norm_num

private lemma pair_support (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    ∀ᵐ p : ℝ × ℝ ∂ν.prod ν, |p.1| ≤ h ∧ |p.2| ≤ h := by
  apply (Measure.ae_prod_iff_ae_ae
    (p := fun p : ℝ × ℝ => |p.1| ≤ h ∧ |p.2| ≤ h) (by measurability)).mpr
  filter_upwards [hs] with a ha
  filter_upwards [hs] with b hb
  exact ⟨ha, hb⟩

private lemma cube_difference_bound (a b : ℝ) :
    |a - b| ^ 3 ≤ 4 * (|a| ^ 3 + |b| ^ 3) := by
  have hab := abs_sub a b
  have hpow := pow_le_pow_left₀ (abs_nonneg (a - b)) hab 3
  have hfactor := mul_nonneg (show 0 ≤ |a| + |b| by positivity) (sq_nonneg (|a| - |b|))
  nlinarith only [hpow, hfactor]

private lemma pair_cube_data (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) :
    Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ 3) (ν.prod ν) ∧
      (∫ p : ℝ × ℝ, |p.1 - p.2| ^ 3 ∂ν.prod ν) ≤
        8 * (∫ a : ℝ, |a| ^ 3 ∂ν) := by
  have hi : Integrable (fun p : ℝ × ℝ => 4 * (|p.1| ^ 3 + |p.2| ^ 3)) (ν.prod ν) :=
    (((h3.comp_fst ν).add (h3.comp_snd ν)).const_mul 4)
  have hc : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ 3) (ν.prod ν) := by
    refine hi.mono' (by fun_prop) (Filter.Eventually.of_forall ?_)
    intro p
    simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using cube_difference_bound p.1 p.2
  refine ⟨hc, ?_⟩
  have hm := integral_mono hc hi (fun p => cube_difference_bound p.1 p.2)
  have hf : (∫ p : ℝ × ℝ, |p.1| ^ 3 ∂ν.prod ν) = ∫ a : ℝ, |a| ^ 3 ∂ν := by
    rw [integral_prod _ (h3.comp_fst ν)]
    simp
  have hs : (∫ p : ℝ × ℝ, |p.2| ^ 3 ∂ν.prod ν) = ∫ a : ℝ, |a| ^ 3 ∂ν := by
    rw [integral_prod _ (h3.comp_snd ν)]
    simp
  rw [integral_const_mul, integral_add (h3.comp_fst ν) (h3.comp_snd ν), hf, hs] at hm
  linarith

theorem quadraticChord_moments (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    let V := variance (id : ℝ → ℝ) ν
    let gamma := (∫ a : ℝ, |a| ^ 3 ∂ν) / V
    Integrable (fun z : ℝ × ℝ => z.1) (quadraticChordLaw ν) ∧
    Integrable (fun z : ℝ × ℝ => |z.1|) (quadraticChordLaw ν) ∧
    Integrable (fun z : ℝ × ℝ => z.1 ^ 2) (quadraticChordLaw ν) ∧
    Integrable (fun z : ℝ × ℝ => |z.2|) (quadraticChordLaw ν) ∧
    (∫ z : ℝ × ℝ, z.1 ∂quadraticChordLaw ν) = 0 ∧
    (∫ z : ℝ × ℝ, |z.1| ∂quadraticChordLaw ν) =
      (∫ p : ℝ × ℝ, |p.1 - p.2| ^ 3 ∂ν.prod ν) / (6 * V) ∧
    (∫ z : ℝ × ℝ, z.1 ^ 2 ∂quadraticChordLaw ν) =
      (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 4 ∂ν.prod ν) / (12 * V) ∧
    (∫ z : ℝ × ℝ, |z.1| ∂quadraticChordLaw ν) ≤ (4 / 3 : ℝ) * gamma ∧
    (∫ z : ℝ × ℝ, |z.2| ∂quadraticChordLaw ν) ≤ (8 / 3 : ℝ) * h * gamma ∧
    (∫ z : ℝ × ℝ, z.1 ^ 2 ∂quadraticChordLaw ν) ≤ (4 / 3 : ℝ) * h * gamma := by
  let V : ℝ := variance (id : ℝ → ℝ) ν
  let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂ν) / V
  obtain ⟨hp, hc, hz, _⟩ := quadraticChord_law_data ν h3 hV h hh hs
  let := hp
  let := hc
  let := quadraticTriangle_probability_char.1
  have hzi : Integrable (fun z : ℝ × ℝ => z.1) (quadraticChordLaw ν) :=
    bounded_integrable _ _ measurable_fst (2 * h) (hz.mono fun _ hq => hq.1)
  have hza : Integrable (fun z : ℝ × ℝ => |z.1|) (quadraticChordLaw ν) := hzi.abs
  have hzs : Integrable (fun z : ℝ × ℝ => z.1 ^ 2) (quadraticChordLaw ν) := by
    apply bounded_integrable _ _ (by fun_prop) ((2 * h) ^ 2)
    filter_upwards [hz] with z hz
    simpa only [abs_pow, sq_abs] using pow_le_pow_left₀ (abs_nonneg z.1) hz.1 2
  have hya : Integrable (fun z : ℝ × ℝ => |z.2|) (quadraticChordLaw ν) := by
    apply bounded_integrable _ _ (by fun_prop) (4 * h ^ 2)
    filter_upwards [hz] with z hz
    simp only [abs_abs]
    nlinarith only [hz.2, mul_le_mul_of_nonneg_left hz.1 (show 0 ≤ 2 * h by positivity)]
  obtain ⟨_, _, _, htm, hta, hts⟩ := quadraticTriangle_moments
  have hm : (∫ z : ℝ × ℝ, z.1 ∂quadraticChordLaw ν) = 0 := by
    unfold quadraticChordLaw
    rw [integral_map (by fun_prop) (by fun_prop)]
    have he : (fun z : (ℝ × ℝ) × ℝ => z.2 * (z.1.1 - z.1.2)) =
        (fun z => (z.1.1 - z.1.2) * z.2) := by funext z; ring
    rw [he, integral_prod_mul (fun p : ℝ × ℝ => p.1 - p.2) (fun t : ℝ => t), htm, mul_zero]
  have hweight : ∀ p : ℝ × ℝ, 0 ≤ (p.1 - p.2) ^ 2 / (2 * V) :=
    fun p => div_nonneg (sq_nonneg _) (by positivity)
  have ha : (∫ z : ℝ × ℝ, |z.1| ∂quadraticChordLaw ν) =
      (∫ p : ℝ × ℝ, |p.1 - p.2| ^ 3 ∂ν.prod ν) / (6 * V) := by
    unfold quadraticChordLaw
    rw [integral_map (by fun_prop) (by fun_prop)]
    have he : (fun z : (ℝ × ℝ) × ℝ => |z.2 * (z.1.1 - z.1.2)|) =
        (fun z => |z.1.1 - z.1.2| * |z.2|) := by
      funext z
      rw [abs_mul, mul_comm]
    rw [he, integral_prod_mul (fun p : ℝ × ℝ => |p.1 - p.2|) (fun t : ℝ => |t|), hta]
    unfold quadraticBiasedPairLaw
    rw [real_density_integral _ _ (by fun_prop) hweight]
    have he : (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2 / (2 * V) * |p.1 - p.2|) =
        (fun p => |p.1 - p.2| ^ 3 / (2 * V)) := by
      funext p
      rw [← sq_abs (p.1 - p.2)]
      ring
    rw [he, integral_div]
    ring
  have hsq : (∫ z : ℝ × ℝ, z.1 ^ 2 ∂quadraticChordLaw ν) =
      (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 4 ∂ν.prod ν) / (12 * V) := by
    unfold quadraticChordLaw
    rw [integral_map (by fun_prop) (by fun_prop)]
    have he : (fun z : (ℝ × ℝ) × ℝ => (z.2 * (z.1.1 - z.1.2)) ^ 2) =
        (fun z => (z.1.1 - z.1.2) ^ 2 * z.2 ^ 2) := by funext z; ring
    rw [he, integral_prod_mul (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) (fun t : ℝ => t ^ 2), hts]
    unfold quadraticBiasedPairLaw
    rw [real_density_integral _ _ (by fun_prop) hweight]
    have he : (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2 / (2 * V) * (p.1 - p.2) ^ 2) =
        (fun p => (p.1 - p.2) ^ 4 / (2 * V)) := by funext p; ring
    rw [he, integral_div]
    ring
  obtain ⟨hi3, hb3⟩ := pair_cube_data ν h3
  have hd : ∀ᵐ p : ℝ × ℝ ∂ν.prod ν, |p.1 - p.2| ≤ 2 * h := by
    filter_upwards [pair_support ν h hs] with p hp
    exact (abs_sub p.1 p.2).trans (by linarith only [hp.1, hp.2])
  have h4point : ∀ᵐ p : ℝ × ℝ ∂ν.prod ν,
      (p.1 - p.2) ^ 4 ≤ (2 * h) * |p.1 - p.2| ^ 3 := by
    filter_upwards [hd] with p hp
    have he : (p.1 - p.2) ^ 4 = |p.1 - p.2| ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    calc
      _ = |p.1 - p.2| * |p.1 - p.2| ^ 3 := by rw [he]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (by positivity)
  have hi4 : Integrable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 4) (ν.prod ν) := by
    apply (hi3.const_mul (2 * h)).mono' (by fun_prop)
    filter_upwards [h4point] with p hp
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (p.1 - p.2) ^ 4)] using hp
  have hb4 : (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 4 ∂ν.prod ν) ≤
      16 * h * (∫ a : ℝ, |a| ^ 3 ∂ν) := by
    have hm := integral_mono_ae hi4 (hi3.const_mul (2 * h)) h4point
    rw [integral_const_mul] at hm
    have ht := mul_le_mul_of_nonneg_left hb3 (show 0 ≤ 2 * h by positivity)
    nlinarith only [hm, ht]
  have hba : (∫ z : ℝ × ℝ, |z.1| ∂quadraticChordLaw ν) ≤ (4 / 3 : ℝ) * gamma := by
    rw [ha]
    dsimp [gamma]
    apply (div_le_iff₀ (show 0 < 6 * V by positivity)).2
    have hv : V ≠ 0 := hV.ne'
    calc
      _ ≤ 8 * (∫ a : ℝ, |a| ^ 3 ∂ν) := hb3
      _ = _ := by field_simp; ring
  have hby : (∫ z : ℝ × ℝ, |z.2| ∂quadraticChordLaw ν) ≤ (8 / 3 : ℝ) * h * gamma := by
    have hm := integral_mono_ae hya (hza.const_mul (2 * h)) (hz.mono fun _ hq => hq.2)
    rw [integral_const_mul] at hm
    have ht := mul_le_mul_of_nonneg_left hba (show 0 ≤ 2 * h by positivity)
    nlinarith only [hm, ht]
  have hbs : (∫ z : ℝ × ℝ, z.1 ^ 2 ∂quadraticChordLaw ν) ≤ (4 / 3 : ℝ) * h * gamma := by
    rw [hsq]
    dsimp [gamma]
    apply (div_le_iff₀ (show 0 < 12 * V by positivity)).2
    have hv : V ≠ 0 := hV.ne'
    calc
      _ ≤ 16 * h * (∫ a : ℝ, |a| ^ 3 ∂ν) := hb4
      _ = _ := by field_simp; ring
  exact ⟨hzi, hza, hzs, hya, hm, ha, hsq, hba, hby, hbs⟩

end Shao.Probability
