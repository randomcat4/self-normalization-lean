import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology

namespace Shao

noncomputable def standardNormalDensity (x : ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 1 x

noncomputable def standardNormalTail (x : ℝ) : ℝ :=
  ((ProbabilityTheory.gaussianReal 0 1) (Set.Ioi x)).toReal

private theorem density_pos (x : ℝ) : 0 < standardNormalDensity x :=
  ProbabilityTheory.gaussianPDFReal_pos 0 1 x (by norm_num)

private theorem density_integrable : Integrable standardNormalDensity :=
  ProbabilityTheory.integrable_gaussianPDFReal 0 1

private theorem density_formula (x : ℝ) :
    standardNormalDensity x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  simp [standardNormalDensity, ProbabilityTheory.gaussianPDFReal]

private theorem density_deriv (x : ℝ) :
    HasDerivAt standardNormalDensity (-x * standardNormalDensity x) x := by
  have h := ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    (Real.sqrt (2 * Real.pi))⁻¹)
  have heq : standardNormalDensity = fun y =>
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := funext density_formula
  rw [heq]
  convert h using 1 <;> norm_num
  ring

private theorem density_continuous : Continuous standardNormalDensity :=
  continuous_iff_continuousAt.mpr fun x => (density_deriv x).continuousAt

theorem standardNormalTail_representation (x : ℝ) :
    standardNormalTail x =
        ((ProbabilityTheory.gaussianReal 0 1) (Set.Ici x)).toReal ∧
      standardNormalTail x =
        1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x ∧
      standardNormalTail x =
        ∫ a : ℝ in Set.Ioi x, standardNormalDensity a := by
  have : NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num)
  refine ⟨congrArg ENNReal.toReal (measure_congr Ioi_ae_eq_Ici), ?_, ?_⟩
  · rw [ProbabilityTheory.cdf_eq_real]
    simpa [standardNormalTail, Measure.real] using
      (measureReal_compl (μ := ProbabilityTheory.gaussianReal 0 1)
        (s := Iic x) measurableSet_Iic)
  · unfold standardNormalTail
    rw [ProbabilityTheory.gaussianReal_apply_eq_integral 0 (by norm_num),
      ENNReal.toReal_ofReal]
    · rfl
    · exact integral_nonneg fun a => (density_pos a).le

private theorem tail_positive (x : ℝ) : 0 < standardNormalTail x := by
  rw [(standardNormalTail_representation x).2.2]
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun a => (density_pos a).le) density_integrable.integrableOn).2
  have hs : Function.support standardNormalDensity = univ := by
    ext a
    simp [Function.mem_support, ne_of_gt (density_pos a)]
  simp [hs]

private theorem tail_reflection (x : ℝ) :
    standardNormalTail (-x) = 1 - standardNormalTail x := by
  have hmap := ProbabilityTheory.gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
  have heq : (fun a : ℝ => -a) ⁻¹' Ioi (-x) = Iio x := by
    ext a
    simp
  have hm := congrArg (fun μ : Measure ℝ => (μ (Ioi (-x))).toReal) hmap
  rw [Measure.map_apply measurable_neg measurableSet_Ioi, heq] at hm
  simp only [neg_zero] at hm
  change ((ProbabilityTheory.gaussianReal 0 1) (Ioi (-x))).toReal = _
  rw [← hm]
  have hc := measureReal_compl (μ := ProbabilityTheory.gaussianReal 0 1)
    (s := Ici x) measurableSet_Ici
  simp only [compl_Ici, probReal_univ] at hc
  change (ProbabilityTheory.gaussianReal 0 1).real (Iio x) = _
  rw [hc]
  change 1 - ((ProbabilityTheory.gaussianReal 0 1) (Ici x)).toReal = _
  rw [← (standardNormalTail_representation x).1]

theorem standardNormalTail_basic :
    Antitone standardNormalTail ∧
      standardNormalTail 0 = (1 / 2 : ℝ) ∧
      (∀ x : ℝ, 0 < standardNormalTail x ∧ standardNormalTail x < 1) ∧
      ∀ x : ℝ, standardNormalTail (-x) = 1 - standardNormalTail x := by
  refine ⟨?_, ?_, ?_, tail_reflection⟩
  · intro x y hxy
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Ioi_subset_Ioi hxy))
  · have h := tail_reflection 0
    simp only [neg_zero] at h
    linarith
  · intro x
    refine ⟨tail_positive x, ?_⟩
    have h := tail_positive (-x)
    rw [tail_reflection] at h
    linarith

theorem standardNormal_derivatives (x : ℝ) :
    HasDerivAt standardNormalDensity (-x * standardNormalDensity x) x ∧
      HasDerivAt standardNormalTail (-standardNormalDensity x) x := by
  refine ⟨density_deriv x, ?_⟩
  have hrep : standardNormalTail = fun t => standardNormalTail 0 -
      ∫ a in (0 : ℝ)..t, standardNormalDensity a := by
    funext t
    rw [(standardNormalTail_representation t).2.2,
      (standardNormalTail_representation 0).2.2]
    have h := intervalIntegral.integral_Ioi_sub_Ioi'
      (a := (0 : ℝ)) (b := t) density_integrable.integrableOn
      density_integrable.integrableOn
    linarith
  rw [hrep]
  exact (intervalIntegral.integral_hasDerivAt_right
    density_integrable.intervalIntegrable
    density_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    density_continuous.continuousAt).const_sub _

private theorem density_limit : Tendsto standardNormalDensity atTop (𝓝 0) := by
  have hp : Tendsto (fun t : ℝ => -t ^ 2 / 2) atTop atBot :=
    (tendsto_neg_atTop_atBot.comp
      (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))).atBot_div_const (by norm_num)
  have h := (Real.tendsto_exp_atBot.comp hp).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  rw [show standardNormalDensity = fun t =>
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2) from funext density_formula]
  simpa only [Function.comp_apply, mul_zero] using h

private theorem weight_bounds (t : ℝ) (ht : 0 ≤ t) :
    (3 / 4 : ℝ) ≤ (t ^ 2 + t + 1) / (1 + t) ^ 2 ∧
      (t ^ 2 + t + 1) / (1 + t) ^ 2 ≤ 1 := by
  have hd : 0 < (1 + t) ^ 2 := sq_pos_of_pos (by linarith)
  constructor
  · apply (le_div_iff₀ hd).2
    nlinarith [sq_nonneg (t - 1)]
  · apply (div_le_iff₀ hd).2
    nlinarith

theorem standardNormal_mills_bounds (x : ℝ) (hx : 0 ≤ x) :
    standardNormalDensity x / (1 + x) ≤ standardNormalTail x ∧
      standardNormalTail x ≤
        (4 / 3 : ℝ) * standardNormalDensity x / (1 + x) ∧
      standardNormalDensity x / standardNormalTail x ≤ 1 + x := by
  let f : ℝ → ℝ := fun t => standardNormalDensity t / (1 + t)
  let g : ℝ → ℝ := fun t =>
    standardNormalDensity t * ((t ^ 2 + t + 1) / (1 + t) ^ 2)
  have hgb : ∀ t ∈ Ioi x, 0 ≤ g t ∧ g t ≤ standardNormalDensity t := by
    intro t ht
    have hw := weight_bounds t (hx.trans ht.le)
    dsimp [g]
    constructor
    · exact mul_nonneg (density_pos t).le (by linarith [hw.1])
    · exact mul_le_of_le_one_right (density_pos t).le hw.2
  have hgi : IntegrableOn g (Ioi x) := by
    apply density_integrable.integrableOn.mono'
    · exact ((ProbabilityTheory.measurable_gaussianPDFReal 0 1).mul
        (by fun_prop)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (hgb t ht).1]
      exact (hgb t ht).2
  have hfd : ∀ t ∈ Ici x, HasDerivAt f (-g t) t := by
    intro t ht
    have ht' : 1 + t ≠ 0 := by linarith [hx.trans ht]
    have h := (density_deriv t).div ((hasDerivAt_id t).const_add 1) ht'
    simp only [id_eq, mul_one] at h
    change HasDerivAt f ((-t * standardNormalDensity t * (1 + t) -
      standardNormalDensity t) / (1 + t) ^ 2) t at h
    convert h using 1
    dsimp [g]
    field_simp
    ring
  have hfl : Tendsto f atTop (𝓝 0) := by
    apply squeeze_zero' _ _ density_limit
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact div_nonneg (density_pos t).le (by linarith)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact div_le_self (density_pos t).le (by linarith)
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hfd hgi.neg hfl
  have hid : (∫ t in Ioi x, g t) = standardNormalDensity x / (1 + x) := by
    rw [integral_neg] at hftc
    dsimp [f] at hftc
    linarith
  have hu : (∫ t in Ioi x, g t) ≤ ∫ t in Ioi x, standardNormalDensity t := by
    apply integral_mono_ae hgi density_integrable.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hgb t ht).2
  have hl : (∫ t in Ioi x, (3 / 4 : ℝ) * standardNormalDensity t) ≤
      ∫ t in Ioi x, g t := by
    apply integral_mono_ae (density_integrable.integrableOn.const_mul _) hgi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [g, mul_comm] using
      mul_le_mul_of_nonneg_left (weight_bounds t (hx.trans ht.le)).1
        (density_pos t).le
  rw [hid, ← (standardNormalTail_representation x).2.2] at hu
  rw [integral_const_mul, hid, ← (standardNormalTail_representation x).2.2] at hl
  have hx' : 0 < 1 + x := by linarith
  refine ⟨hu, ?_, ?_⟩
  · calc
      standardNormalTail x ≤ (4 / 3 : ℝ) *
          (standardNormalDensity x / (1 + x)) := by linarith only [hl]
      _ = (4 / 3 : ℝ) * standardNormalDensity x / (1 + x) := by ring
  · apply (div_le_iff₀ (tail_positive x)).2
    simpa only [mul_comm] using (div_le_iff₀ hx').1 hu

private theorem density_ratio (x y : ℝ) :
    standardNormalDensity y =
      Real.exp ((x ^ 2 - y ^ 2) / 2) * standardNormalDensity x := by
  rw [density_formula, density_formula]
  calc
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.exp ((x ^ 2 - y ^ 2) / 2) * Real.exp (-x ^ 2 / 2)) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ = _ := by ring

theorem standardNormalTail_ratio_bound (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    standardNormalTail y ≤
      (4 / 3 : ℝ) * ((1 + x) / (1 + y)) *
        Real.exp ((x ^ 2 - y ^ 2) / 2) * standardNormalTail x := by
  have hφ : standardNormalDensity x ≤ standardNormalTail x * (1 + x) :=
    (div_le_iff₀ (by linarith : 0 < 1 + x)).1
      (standardNormal_mills_bounds x hx).1
  calc
    standardNormalTail y ≤ (4 / 3 : ℝ) * standardNormalDensity y / (1 + y) :=
      (standardNormal_mills_bounds y hy).2.1
    _ = ((4 / 3 : ℝ) * Real.exp ((x ^ 2 - y ^ 2) / 2) / (1 + y)) *
        standardNormalDensity x := by rw [density_ratio x y]; ring
    _ ≤ ((4 / 3 : ℝ) * Real.exp ((x ^ 2 - y ^ 2) / 2) / (1 + y)) *
        (standardNormalTail x * (1 + x)) := by
      exact mul_le_mul_of_nonneg_left hφ (by positivity)
    _ = _ := by ring

theorem standardNormalTail_local_comparison (x t : ℝ)
    (hx : 0 ≤ x) (ht : 0 ≤ t)
    (hneigh : |t - x| ≤ 1 / (1 + x)) :
    Real.exp (-2) * standardNormalTail x ≤ standardNormalTail t ∧
      standardNormalTail t ≤ Real.exp 2 * standardNormalTail x := by
  let δ : ℝ := |t - x|
  have hδ : 0 ≤ δ := abs_nonneg _
  have hdx : δ * (1 + x) ≤ 1 := (le_div_iff₀ (by linarith)).1 hneigh
  have hd1 : δ ≤ 1 := by nlinarith [mul_nonneg hδ hx]
  have htx : t ≤ x + δ := by dsimp [δ]; linarith [le_abs_self (t - x)]
  have hlog (s : ℝ) : HasDerivAt (fun u => Real.log (standardNormalTail u))
      (-standardNormalDensity s / standardNormalTail s) s :=
    (standardNormal_derivatives s).2.log (ne_of_gt (tail_positive s))
  have hnorm (s : ℝ) :
      ‖deriv (fun u => Real.log (standardNormalTail u)) s‖ =
        standardNormalDensity s / standardNormalTail s := by
    rw [(hlog s).deriv, norm_div, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (density_pos s), abs_of_pos (tail_positive s)]
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (C := 1 + x + δ)
    (fun s (_ : s ∈ Icc 0 (x + δ)) => (hlog s).differentiableAt)
    (fun s (hs : s ∈ Icc 0 (x + δ)) => by
      rw [hnorm]
      exact ((standardNormal_mills_bounds s hs.1).2.2).trans (by linarith [hs.2]))
    (convex_Icc (0 : ℝ) (x + δ))
    (show x ∈ Icc 0 (x + δ) from ⟨hx, by linarith⟩)
    (show t ∈ Icc 0 (x + δ) from ⟨ht, htx⟩)
  have hbound : |Real.log (standardNormalTail t) - Real.log (standardNormalTail x)| ≤ 2 := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
    have hsq : δ ^ 2 ≤ 1 := by nlinarith
    change |Real.log (standardNormalTail t) - Real.log (standardNormalTail x)| ≤ _
    nlinarith [hmv]
  have hle := abs_le.mp hbound
  constructor
  · have h := Real.exp_le_exp.mpr (by linarith [hle.1] :
        -2 + Real.log (standardNormalTail x) ≤ Real.log (standardNormalTail t))
    simpa only [Real.exp_add, Real.exp_log (tail_positive x),
      Real.exp_log (tail_positive t)] using h
  · have h := Real.exp_le_exp.mpr (by linarith [hle.2] :
        Real.log (standardNormalTail t) ≤ 2 + Real.log (standardNormalTail x))
    simpa only [Real.exp_add, Real.exp_log (tail_positive x),
      Real.exp_log (tail_positive t)] using h

theorem standardNormalTail_deletion_comparison (j : ℕ) (x : ℝ)
    (hx : 0 ≤ x) (hj : (j : ℝ) ≤ x ^ 2 / 2) :
    standardNormalTail (Real.sqrt (x ^ 2 - (j : ℝ))) ≤
      3 * Real.exp ((j : ℝ) / 2) * standardNormalTail x := by
  let y := Real.sqrt (x ^ 2 - (j : ℝ))
  have hyr : 0 ≤ x ^ 2 - (j : ℝ) := by nlinarith [sq_nonneg x]
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hysq : y ^ 2 = x ^ 2 - (j : ℝ) := Real.sq_sqrt hyr
  have hxy : x / 2 ≤ y := by nlinarith [sq_nonneg (y - x / 2)]
  have hratio : (1 + x) / (1 + y) ≤ 2 :=
    (div_le_iff₀ (by linarith : 0 < 1 + y)).2 (by linarith)
  have hexp : (x ^ 2 - y ^ 2) / 2 = (j : ℝ) / 2 := by rw [hysq]; ring
  have h := standardNormalTail_ratio_bound x y hx hy
  rw [hexp] at h
  change standardNormalTail y ≤ _
  calc
    standardNormalTail y ≤ _ := h
    _ ≤ (4 / 3 : ℝ) * 2 * Real.exp ((j : ℝ) / 2) * standardNormalTail x := by
      have hp := (tail_positive x).le
      gcongr
    _ ≤ _ := by
      have hp : 0 ≤ Real.exp ((j : ℝ) / 2) * standardNormalTail x :=
        mul_nonneg (Real.exp_pos _).le (tail_positive x).le
      nlinarith

end Shao
