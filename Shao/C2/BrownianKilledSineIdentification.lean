import Shao.C2.IntervalSineInitialLimit

noncomputable section
namespace Shao.C2.BrownianKilledSineIdentification
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.BrownianKilledEndpointDensity Shao.C2.BrownianKilledKernel
open Shao.C2.BrownianSineStoppedLimit Shao.C2.IntervalSineInitialLimit
open Shao.C2.IntervalSineSeries Shao.C2.IntervalSineNormalizedDerivatives
open Shao.C2.IntervalReciprocalDerivatives Shao.C2.IntervalImageSineIdentity
open Shao.C2.IntervalImageCandidateSpatial

private theorem killed_density_data {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    Continuous (fun x : ℝ => gaussianPDFReal y T x *
      intervalCompletion (bridgeLaw B P) a y (T : ℝ) x) ∧
    (∃ M : ℝ, ∀ x : ℝ, |gaussianPDFReal y T x *
      intervalCompletion (bridgeLaw B P) a y (T : ℝ) x| ≤ M) ∧
    (∀ x : ℝ, 0 ≤ gaussianPDFReal y T x *
      intervalCompletion (bridgeLaw B P) a y (T : ℝ) x) ∧
    ∀ x : ℝ, x ∉ Icc (-a) a → gaussianPDFReal y T x *
      intervalCompletion (bridgeLaw B P) a y (T : ℝ) x = 0 := by
  let ν := bridgeLaw B P
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_bridgeLaw B P hB
  let f : ℝ → ℝ := fun x => gaussianPDFReal y T x * intervalCompletion ν a y (T : ℝ) x
  have hf : Continuous f := (killed_density_joint_continuous B P hB a T hT).comp
    (continuous_const.prodMk continuous_id)
  have hn (x : ℝ) : 0 ≤ f x := mul_nonneg (gaussianPDFReal_nonneg y T x)
    (completion_bounds ν a y (T : ℝ) x).2.2.2.2.1
  have hb (x : ℝ) : |f x| ≤ (Real.sqrt (2 * Real.pi * (T : ℝ)))⁻¹ := by
    rw [abs_of_nonneg (hn x)]
    calc
      f x ≤ gaussianPDFReal y T x * 1 := mul_le_mul_of_nonneg_left
        (completion_bounds ν a y (T : ℝ) x).2.2.2.2.2 (gaussianPDFReal_nonneg y T x)
      _ = gaussianPDFReal y T x := mul_one _
      _ ≤ _ := by
        unfold gaussianPDFReal
        have he : Real.exp (-(x - y) ^ 2 / (2 * (T : ℝ))) ≤ 1 :=
          Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he
          (inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi * (T : ℝ))))
  refine ⟨hf, ⟨_, hb⟩, hn, ?_⟩
  intro x hx
  have he : strictInterval a y (T : ℝ) x = ∅ := by
    apply strictInterval_exterior
    by_cases hl : x ≤ -a
    · exact Or.inr (Or.inr (Or.inl hl))
    · have hu : a ≤ x := le_of_lt (lt_of_not_ge (fun h => hx ⟨(lt_of_not_ge hl).le, h⟩))
      exact Or.inr (Or.inr (Or.inr hu))
  have hi : intervalCompletion ν a y (T : ℝ) x = 0 := by
    unfold intervalCompletion
    rw [he]
    simp
  rw [hi, mul_zero]

theorem actualIntervalKernel_sine_action_density {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a z H y : ℝ) (ha : 0 < a) (hH : 0 < H)
    (hy : |y| < a) (T : ℝ≥0) (hT : T ≠ 0) :
    Integrable (fun x : ℝ => mixedSineSeries 0 0 a z H x *
      (gaussianPDFReal y T x * intervalCompletion (bridgeLaw B P) a y (T : ℝ) x)) volume ∧
    (∫ x in Icc (-a) a, mixedSineSeries 0 0 a z H x *
      (gaussianPDFReal y T x * intervalCompletion (bridgeLaw B P) a y (T : ℝ) x)) =
      mixedSineSeries 0 0 a z (H + (T : ℝ)) y := by
  let f : ℝ → ℝ := fun x => gaussianPDFReal y T x * intervalCompletion (bridgeLaw B P) a y (T : ℝ) x
  obtain ⟨hf, hb, hn, hsupp⟩ := killed_density_data B P hB a y T hT
  obtain ⟨C, L, hC, hL, hbound⟩ := Shao.C2.SineStoppedWallBound.sineSeries_uniform_wall_bound a z H ha hH
  have hu : Continuous (mixedSineSeries 0 0 a z H) := continuous_iff_continuousAt.mpr
    (fun x => (mixedSineSeries_spatial_hasDerivAt 0 0 a z H x ha hH).continuousAt)
  have hi : Integrable (fun x => mixedSineSeries 0 0 a z H x * f x) volume := by
    apply ((integrable_killed_density B P hB a y T hT).const_mul C).mono'
      (hu.mul hf).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change |mixedSineSeries 0 0 a z H x * f x| ≤ C * f x
      rw [abs_mul, abs_of_nonneg (hn x)]
      exact mul_le_mul_of_nonneg_right ((hbound H le_rfl x).1) (hn x)
  refine ⟨hi, ?_⟩
  have hfull : (∫ x in Icc (-a) a, mixedSineSeries 0 0 a z H x * f x) =
      ∫ x : ℝ, mixedSineSeries 0 0 a z H x * f x := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ Icc (-a) a
      · exact Set.indicator_of_mem hx _
      · rw [Set.indicator_of_notMem hx]
        change 0 = mixedSineSeries 0 0 a z H x * f x
        have hz0 : f x = 0 := hsupp x hx
        rw [hz0, mul_zero]
  have hw : (∫ x : ℝ, mixedSineSeries 0 0 a z H x ∂actualIntervalKernel B P a T y) =
      ∫ x : ℝ, mixedSineSeries 0 0 a z H x * f x := by
    rw [actualIntervalKernel_apply_eq_density B P hB a y T hT]
    change (∫ x : ℝ, mixedSineSeries 0 0 a z H x ∂volume.withDensity (fun x => ENNReal.ofReal (f x))) = _
    calc
      _ = ∫ x : ℝ, (ENNReal.ofReal (f x)).toReal • mixedSineSeries 0 0 a z H x :=
        integral_withDensity_eq_integral_toReal_smul
          (show Measurable (fun x => ENNReal.ofReal (f x)) from ENNReal.measurable_ofReal.comp hf.measurable)
          (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (mixedSineSeries 0 0 a z H)
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change (ENNReal.ofReal (f x)).toReal • mixedSineSeries 0 0 a z H x = _
          rw [ENNReal.toReal_ofReal (hn x), smul_eq_mul, mul_comm]
  exact hfull.trans (hw.symm.trans (actualIntervalKernel_sine_action B P hB a z H y ha hH hy T hT).2)

theorem actual_killed_density_eq_sine {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y z : ℝ) (ha : 0 < a) (hy : |y| < a) (hz : |z| < a)
    (T : ℝ≥0) (hT : T ≠ 0) :
    gaussianPDFReal y T z * intervalCompletion (bridgeLaw B P) a y (T : ℝ) z =
      mixedSineSeries 0 0 a z (T : ℝ) y := by
  let f : ℝ → ℝ := fun x => gaussianPDFReal y T x * intervalCompletion (bridgeLaw B P) a y (T : ℝ) x
  obtain ⟨hf, hb, hn, hsupp⟩ := killed_density_data B P hB a y T hT
  have hi := sineSeries_initial_limit a z ha hz f hf hb
  have he : (fun H : ℝ≥0 => ∫ x in Icc (-a) a,
      mixedSineSeries 0 0 a z (H : ℝ) x * f x) =ᶠ[𝓝[>] 0]
      (fun H : ℝ≥0 => mixedSineSeries 0 0 a z ((H : ℝ) + (T : ℝ)) y) := by
    filter_upwards [self_mem_nhdsWithin] with H hH
    have hH' : 0 < (H : ℝ) := hH
    exact (actualIntervalKernel_sine_action_density B P hB a z (H : ℝ) y ha hH' hy T hT).2
  have hleft : Tendsto (fun H : ℝ≥0 => mixedSineSeries 0 0 a z ((H : ℝ) + (T : ℝ)) y)
      (𝓝[>] 0) (𝓝 (f z)) := hi.congr' he
  have hT' : 0 < (T : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hT : 0 < T)
  have ht : Tendsto (fun H : ℝ≥0 => (H : ℝ) + (T : ℝ)) (𝓝[>] 0) (𝓝 (T : ℝ)) := by
    have h0 : Tendsto (fun H : ℝ≥0 => (H : ℝ)) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
      (NNReal.continuous_coe.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa only [zero_add] using h0.add tendsto_const_nhds
  have hright := (mixedSineSeries_time_hasDerivAt 0 0 a z (T : ℝ) y ha hT').continuousAt.tendsto.comp ht
  exact tendsto_nhds_unique hleft hright

theorem bridge_interval_eq_image {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y U z : ℝ) (ha : 0 < a) (hy : |y| < a)
    (hU : 0 < U) (hz : |z| < a) :
    intervalCompletion (bridgeLaw B P) a y U z = intervalImageCandidate a z U y := by
  let T : ℝ≥0 := ⟨U, hU.le⟩
  have hT : T ≠ 0 := ne_of_gt (show (0 : ℝ≥0) < T from hU)
  have hd := actual_killed_density_eq_sine B P hB a y z ha hy hz T hT
  have hc : reciprocalFreeDensity z U y * gaussianPDFReal y T z = 1 := by
    change reciprocalFreeDensity z U y *
      ((Real.sqrt (2 * Real.pi * U))⁻¹ * Real.exp (-(z - y) ^ 2 / (2 * U))) = 1
    simpa only [one_div] using reciprocalFreeDensity_mul_free z U y hU
  calc
    _ = reciprocalFreeDensity z U y * (gaussianPDFReal y T z * intervalCompletion (bridgeLaw B P) a y U z) := by
      rw [← mul_assoc, hc, one_mul]
    _ = reciprocalFreeDensity z U y * mixedSineSeries 0 0 a z U y := congrArg (reciprocalFreeDensity z U y * ·) hd
    _ = normalizedSineCandidate a z U y := rfl
    _ = _ := (intervalImageCandidate_eq_normalizedSineCandidate a z U y ha hz.le hU hy.le).symm

end Shao.C2.BrownianKilledSineIdentification
