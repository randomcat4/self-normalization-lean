import Shao.C2.IntervalImageInitialProfile
import Shao.C2.IntervalImageSineIdentity

noncomputable section
namespace Shao.C2.IntervalSineInitialLimit
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
open Shao.C2.IntervalSineSeries Shao.C2.IntervalSineNormalizedDerivatives
open Shao.C2.IntervalReciprocalDerivatives Shao.C2.IntervalImageSineIdentity
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageInitialProfile
open Shao.C2.BrownianKilledEndpointDensity

private theorem normalizedSineCandidate_measurable (a z U : ℝ) (ha : 0 < a) (hU : 0 < U) :
    Measurable (normalizedSineCandidate a z U) := by
  have hr : Continuous (reciprocalFreeDensity z U) := continuous_iff_continuousAt.mpr
    (fun x => (reciprocalFreeDensity_spatial_hasDerivAt z U x hU).continuousAt)
  have hs : Continuous (mixedSineSeries 0 0 a z U) := continuous_iff_continuousAt.mpr
    (fun x => (mixedSineSeries_spatial_hasDerivAt 0 0 a z U x ha hU).continuousAt)
  exact (hr.mul hs).measurable

private theorem sine_gaussian_test_pointwise (a z w : ℝ) (ha : 0 < a) (hz : |z| < a)
    (f : ℝ → ℝ) (hf : Continuous f) :
    Tendsto (fun T : ℝ≥0 => (Icc (-a) a).indicator
      (fun x => normalizedSineCandidate a z (T : ℝ) x * f x)
      (z + Real.sqrt (T : ℝ) * w)) (𝓝[>] 0) (𝓝 (f z)) := by
  let x (T : ℝ≥0) : ℝ := z + Real.sqrt (T : ℝ) * w
  have hx : Tendsto x (𝓝 0) (𝓝 z) := by
    have hc : Continuous x := continuous_const.add
      ((Real.continuous_sqrt.comp NNReal.continuous_coe).mul continuous_const)
    simpa only [x, NNReal.coe_zero, Real.sqrt_zero, zero_mul, add_zero] using hc.tendsto (0 : ℝ≥0)
  have hfx : Tendsto (fun T : ℝ≥0 => f (x T)) (𝓝[>] 0) (𝓝 (f z)) :=
    (hf.continuousAt.tendsto.comp hx).mono_left nhdsWithin_le_nhds
  have hI := intervalImageCandidate_initial_diagonal a z w ha hz
  have hp : Tendsto (fun T : ℝ≥0 => intervalImageCandidate a z (T : ℝ) (x T) * f (x T))
      (𝓝[>] 0) (𝓝 (f z)) := by
    simpa only [one_mul] using hI.mul hfx
  apply hp.congr'
  have hinside : ∀ᶠ T in 𝓝[>] (0 : ℝ≥0), |x T| < a :=
    (hx.abs.eventually (gt_mem_nhds hz)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hinside, self_mem_nhdsWithin] with T hi hT
  have hT' : 0 < (T : ℝ) := hT
  have hm : x T ∈ Icc (-a) a := abs_le.mp hi.le
  rw [Set.indicator_of_mem hm,
    intervalImageCandidate_eq_normalizedSineCandidate a z (T : ℝ) (x T) ha hz.le hT' hi.le]

theorem sineSeries_action_standardGaussian (a z : ℝ) (ha : 0 < a) (hz : |z| ≤ a)
    (T : ℝ≥0) (hT : T ≠ 0) (hsmall : (T : ℝ) ≤ a ^ 2)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hbound : ∀ x : ℝ, |f x| ≤ M) :
    Integrable (fun x => mixedSineSeries 0 0 a z (T : ℝ) x * f x)
      (volume.restrict (Icc (-a) a)) ∧
    Integrable (fun w : ℝ => (Icc (-a) a).indicator
      (fun x => normalizedSineCandidate a z (T : ℝ) x * f x)
      (z + Real.sqrt (T : ℝ) * w)) (gaussianReal 0 1) ∧
    (∀ w : ℝ, |(Icc (-a) a).indicator
      (fun x => normalizedSineCandidate a z (T : ℝ) x * f x)
      (z + Real.sqrt (T : ℝ) * w)| ≤ 17 * M) ∧
    (∫ x in Icc (-a) a, mixedSineSeries 0 0 a z (T : ℝ) x * f x) =
      ∫ w : ℝ, (Icc (-a) a).indicator
        (fun x => normalizedSineCandidate a z (T : ℝ) x * f x)
        (z + Real.sqrt (T : ℝ) * w) ∂(gaussianReal 0 1) := by
  have hU : 0 < (T : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hT : 0 < T)
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hbound 0)
  let F : ℝ → ℝ := (Icc (-a) a).indicator (fun x => normalizedSineCandidate a z (T : ℝ) x * f x)
  have hFm : Measurable F := ((normalizedSineCandidate_measurable a z (T : ℝ) ha hU).mul hf).indicator measurableSet_Icc
  have hFb (x : ℝ) : |F x| ≤ 17 * M := by
    by_cases hx : x ∈ Icc (-a) a
    · dsimp only [F]
      rw [Set.indicator_of_mem hx, abs_mul]
      have hh : |normalizedSineCandidate a z (T : ℝ) x| ≤ 17 := by
        rw [← intervalImageCandidate_eq_normalizedSineCandidate a z (T : ℝ) x ha hz hU (abs_le.mpr hx)]
        exact intervalImageCandidate_small_time_bounded a z (T : ℝ) x ha hz hU (abs_le.mpr hx) hsmall
      exact mul_le_mul hh (hbound x) (abs_nonneg _) (by norm_num)
    · dsimp only [F]
      rw [Set.indicator_of_notMem hx, abs_zero]
      exact mul_nonneg (by norm_num) hM
  have hsm : Measurable (mixedSineSeries 0 0 a z (T : ℝ)) :=
    (continuous_iff_continuousAt.mpr (fun x =>
      (mixedSineSeries_spatial_hasDerivAt 0 0 a z (T : ℝ) x ha hU).continuousAt)).measurable
  obtain ⟨C, L, hC, hL, hb⟩ := Shao.C2.SineStoppedWallBound.sineSeries_uniform_wall_bound a z (T : ℝ) ha hU
  have hi : Integrable (fun x => mixedSineSeries 0 0 a z (T : ℝ) x * f x)
      (volume.restrict (Icc (-a) a)) := by
    apply Integrable.of_bound (hsm.mul hf).aestronglyMeasurable (C * M)
    exact Eventually.of_forall fun x => by
      change |mixedSineSeries 0 0 a z (T : ℝ) x * f x| ≤ C * M
      rw [abs_mul]
      exact mul_le_mul ((hb (T : ℝ) le_rfl x).1) (hbound x) (abs_nonneg _) hC
  have hg : Integrable (fun w : ℝ => F (z + Real.sqrt (T : ℝ) * w)) (gaussianReal 0 1) := by
    apply Integrable.of_bound (hFm.comp (by fun_prop)).aestronglyMeasurable (17 * M)
    exact Eventually.of_forall fun w => by
      change ‖F (z + Real.sqrt (T : ℝ) * w)‖ ≤ 17 * M
      simpa only [Real.norm_eq_abs] using hFb (z + Real.sqrt (T : ℝ) * w)
  refine ⟨hi, hg, fun w => hFb _, ?_⟩
  have hcancel (x : ℝ) : gaussianPDFReal z T x * normalizedSineCandidate a z (T : ℝ) x =
      mixedSineSeries 0 0 a z (T : ℝ) x := by
    have hh : reciprocalFreeDensity z (T : ℝ) x * gaussianPDFReal z T x = 1 := by
      change reciprocalFreeDensity z (T : ℝ) x *
        ((Real.sqrt (2 * Real.pi * (T : ℝ)))⁻¹ * Real.exp (-(x - z) ^ 2 / (2 * (T : ℝ)))) = 1
      rw [show (x - z) ^ 2 = (z - x) ^ 2 by ring]
      simpa only [one_div] using reciprocalFreeDensity_mul_free z (T : ℝ) x hU
    unfold normalizedSineCandidate
    calc
      _ = (reciprocalFreeDensity z (T : ℝ) x * gaussianPDFReal z T x) *
        mixedSineSeries 0 0 a z (T : ℝ) x := by ring
      _ = _ := by rw [hh, one_mul]
  symm
  calc
    _ = ∫ x : ℝ, F x ∂gaussianReal z T :=
      (standardGaussian_affine_hasLaw z T).integral_comp hFm.aestronglyMeasurable
    _ = ∫ x : ℝ, gaussianPDFReal z T x * F x := by
      simpa only [smul_eq_mul] using integral_gaussianReal_eq_integral_smul (μ := z) (v := T) (f := F) hT
    _ = ∫ x : ℝ, (Icc (-a) a).indicator (fun x => mixedSineSeries 0 0 a z (T : ℝ) x * f x) x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : x ∈ Icc (-a) a
        · dsimp only [F]
          rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, ← mul_assoc, hcancel x]
        · simp only [F, Set.indicator_of_notMem hx, mul_zero]
    _ = _ := integral_indicator measurableSet_Icc

theorem sineSeries_initial_limit (a z : ℝ) (ha : 0 < a) (hz : |z| < a)
    (f : ℝ → ℝ) (hf : Continuous f) (hbound : ∃ M : ℝ, ∀ x : ℝ, |f x| ≤ M) :
    Tendsto (fun T : ℝ≥0 => ∫ x in Icc (-a) a,
      mixedSineSeries 0 0 a z (T : ℝ) x * f x) (𝓝[>] 0) (𝓝 (f z)) := by
  obtain ⟨M, hM⟩ := hbound
  let F (T : ℝ≥0) (w : ℝ) : ℝ := (Icc (-a) a).indicator
    (fun x => normalizedSineCandidate a z (T : ℝ) x * f x)
    (z + Real.sqrt (T : ℝ) * w)
  have hs : ∀ᶠ (T : ℝ≥0) in 𝓝[>] (0 : ℝ≥0), (T : ℝ) < a ^ 2 :=
    ((NNReal.continuous_coe.tendsto 0).eventually
      (gt_mem_nhds (sq_pos_of_pos ha))).filter_mono nhdsWithin_le_nhds
  have he : ∀ᶠ (T : ℝ≥0) in 𝓝[>] (0 : ℝ≥0), T ≠ 0 ∧ (T : ℝ) ≤ a ^ 2 := by
    filter_upwards [hs, self_mem_nhdsWithin] with T hs hT
    exact ⟨ne_of_gt hT, hs.le⟩
  have hm : ∀ᶠ T in 𝓝[>] (0 : ℝ≥0), AEStronglyMeasurable (F T) (gaussianReal 0 1) := by
    filter_upwards [he] with T hT
    exact (sineSeries_action_standardGaussian a z ha hz.le T hT.1 hT.2 f hf.measurable M hM).2.1.aestronglyMeasurable
  have hb : ∀ᶠ T in 𝓝[>] (0 : ℝ≥0), ∀ᵐ w ∂gaussianReal 0 1, ‖F T w‖ ≤ 17 * M := by
    filter_upwards [he] with T hT
    apply Eventually.of_forall
    intro w
    simpa only [Real.norm_eq_abs] using
      (sineSeries_action_standardGaussian a z ha hz.le T hT.1 hT.2 f hf.measurable M hM).2.2.1 w
  have hl : ∀ᵐ w ∂gaussianReal 0 1, Tendsto (fun T : ℝ≥0 => F T w) (𝓝[>] 0) (𝓝 (f z)) :=
    Eventually.of_forall (fun w => sine_gaussian_test_pointwise a z w ha hz f hf)
  have hh := tendsto_integral_filter_of_dominated_convergence (μ := gaussianReal 0 1)
    (f := fun _ : ℝ => f z) (fun _ => 17 * M) hm hb (integrable_const _) hl
  have hi : Tendsto (fun T : ℝ≥0 => ∫ w : ℝ, F T w ∂gaussianReal 0 1) (𝓝[>] 0) (𝓝 (f z)) := by
    simpa using hh
  apply hi.congr'
  filter_upwards [he] with T hT
  exact (sineSeries_action_standardGaussian a z ha hz.le T hT.1 hT.2 f hf.measurable M hM).2.2.2.symm

end Shao.C2.IntervalSineInitialLimit
