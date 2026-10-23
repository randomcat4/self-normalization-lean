import Shao.OQ4.VarianceScaling
import Shao.OQ4.TerminalNormalizedKernelLimit
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
# Actual varying-variance closed-strip asymptotic

The probability and moment hypotheses are on the original rows. The primitive
concentration and one-sided survival hypotheses are explicitly on their actual
standardized pushforwards. Those primitive producers remain unpaid.

This LOCAL source implements the frozen conditional adapter only. Its eventual
acceptance requires the qualified unit-variance producer, complete independent
review, and an exact-source server kernel and all-owned transitive audit receipt.
-/

set_option autoImplicit false
noncomputable section
namespace Shao.OQ4.VarianceKernelAsymptotic
open MeasureTheory Filter Set
open RademacherScalarBounds (lambda)
open scoped Topology

private theorem lower_moments_integrable
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν) :
    Integrable (fun x : ℝ => x) ν ∧ Integrable (fun x : ℝ => x ^ 2) ν := by
  have hdom : Integrable (fun x : ℝ => 1 + |x| ^ 3) ν :=
    (integrable_const (1 : ℝ)).add h3
  have hsmall (r : ℝ) (hr : 0 ≤ r) : r ≤ 1 + r ^ 3 ∧ r ^ 2 ≤ 1 + r ^ 3 := by
    by_cases hr1 : r ≤ 1
    · have hp := mul_nonneg hr (sub_nonneg.mpr hr1)
      have hr3 : 0 ≤ r ^ 3 := pow_nonneg hr 3
      constructor <;> nlinarith
    · have hlarge : 1 ≤ r := (lt_of_not_ge hr1).le
      have hp := mul_nonneg hr (sub_nonneg.mpr hlarge)
      have hq := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hlarge)
      constructor <;> nlinarith
  constructor
  · apply hdom.mono' measurable_id.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, id_eq] using (hsmall |x| (abs_nonneg x)).1
  · apply hdom.mono'
      (by fun_prop : Measurable (fun x : ℝ => x ^ 2)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_pow, id_eq] using (hsmall |x| (abs_nonneg x)).2

private theorem common_moment_bound_nonneg
    (νSeq : ℕ → Measure ℝ) (M : ℝ)
    (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M) :
    0 ≤ M := by
  have hβ : 0 ≤ ∫ x : ℝ, |x| ^ 3 ∂(νSeq 0) :=
    integral_nonneg fun x => pow_nonneg (abs_nonneg x) 3
  exact hβ.trans (hM 0)

private theorem sqrt_variance_uniform_bounds
    (v : ℝ) (hvlower : (1 / 2 : ℝ) ≤ v) (hvupper : v ≤ 2) :
    0 < Real.sqrt v ∧ (Real.sqrt v) ^ 2 = v ∧
      (1 / 2 : ℝ) ≤ Real.sqrt v ∧ Real.sqrt v ≤ 2 := by
  obtain ⟨hpos, hsq, hlower⟩ := sqrt_variance_parameters v hvlower hvupper
  refine ⟨hpos, hsq, hlower, ?_⟩
  nlinarith [Real.sqrt_nonneg v]

private theorem mapped_integrable_integral
    (ν : Measure ℝ) (σ : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hfi : Integrable (fun x : ℝ => f (x / σ)) ν) :
    Integrable f (ν.map (fun x : ℝ => x / σ)) ∧
      (∫ y : ℝ, f y ∂(ν.map (fun x : ℝ => x / σ))) =
        ∫ x : ℝ, f (x / σ) ∂ν := by
  have hg : Measurable (fun x : ℝ => x / σ) := measurable_id.div_const σ
  have hf' : AEStronglyMeasurable f (ν.map (fun x : ℝ => x / σ)) :=
    hf.aestronglyMeasurable
  refine ⟨(integrable_map_measure hf' hg.aemeasurable).mpr ?_, ?_⟩
  · simpa only [Function.comp_def] using hfi
  · exact integral_map hg.aemeasurable hf'

private theorem standardized_law_moments
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (v M : ℝ)
    (hvlower : (1 / 2 : ℝ) ≤ v) (hvupper : v ≤ 2)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = v)
    (hthird : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M) :
    let σ : ℝ := Real.sqrt v
    let η : Measure ℝ := ν.map (fun x : ℝ => x / σ)
    IsProbabilityMeasure η ∧
      Integrable (fun y : ℝ => y) η ∧
      Integrable (fun y : ℝ => y ^ 2) η ∧
      Integrable (fun y : ℝ => |y| ^ 3) η ∧
      (∫ y : ℝ, y ∂η) = 0 ∧
      (∫ y : ℝ, y ^ 2 ∂η) = 1 ∧
      (∫ y : ℝ, |y| ^ 3 ∂η) =
        (σ⁻¹) ^ 3 * (∫ x : ℝ, |x| ^ 3 ∂ν) ∧
      (∫ y : ℝ, |y| ^ 3 ∂η) ≤ 8 * M := by
  dsimp only
  have hM0 : 0 ≤ M :=
    common_moment_bound_nonneg (fun _ : ℕ => ν) M (fun _ => hthird)
  obtain ⟨hId, hSq⟩ := lower_moments_integrable ν h3
  obtain ⟨_, _, _, hZ, hZsq, hZcube, hZmean, hZsecond, hZthird, hZbound⟩ :=
    sqrt_variance_standardization ν (fun x : ℝ => x) v M hvlower hvupper hM0
      hId hSq h3 hmean hsecond hthird
  obtain ⟨hηId, hηmean⟩ :=
    mapped_integrable_integral ν (Real.sqrt v) (fun y : ℝ => y) measurable_id hZ
  obtain ⟨hηSq, hηsecond⟩ :=
    mapped_integrable_integral ν (Real.sqrt v) (fun y : ℝ => y ^ 2)
      (by fun_prop : Measurable (fun y : ℝ => y ^ 2)) hZsq
  obtain ⟨hηCube, hηthird⟩ :=
    mapped_integrable_integral ν (Real.sqrt v) (fun y : ℝ => |y| ^ 3)
      (by fun_prop : Measurable (fun y : ℝ => |y| ^ 3)) hZcube
  have hg : Measurable (fun x : ℝ => x / Real.sqrt v) :=
    measurable_id.div_const (Real.sqrt v)
  have hηprob : IsProbabilityMeasure (ν.map (fun x : ℝ => x / Real.sqrt v)) :=
    (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).mpr inferInstance
  refine ⟨hηprob, hηId, hηSq, hηCube, hηmean.trans hZmean,
    hηsecond.trans hZsecond, hηthird.trans hZthird, ?_⟩
  calc
    (∫ y : ℝ, |y| ^ 3 ∂(ν.map (fun x : ℝ => x / Real.sqrt v))) =
        ∫ x : ℝ, |x / Real.sqrt v| ^ 3 ∂ν := hηthird
    _ ≤ 8 * M := hZbound

/-- The actual finite product pushes forward to the product of actual mapped laws. -/
theorem finite_product_standardization_map
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) (σ : ℝ) :
    (Measure.pi (fun _ : Fin n => ν)).map
        (fun a : Shao.Path n => σ⁻¹ • a) =
      Measure.pi (fun _ : Fin n => ν.map (fun x : ℝ => x / σ)) := by
  have hfun : (fun a : Shao.Path n => σ⁻¹ • a) =
      (fun a : Shao.Path n => fun i : Fin n => a i / σ) := by
    funext a i
    change σ⁻¹ * a i = a i / σ
    rw [div_eq_mul_inv, mul_comm]
  rw [hfun]
  exact Measure.pi_map_pi
    (μ := fun _ : Fin n => ν)
    (f := fun _ : Fin n => fun x : ℝ => x / σ)
    (fun _ => (measurable_id.div_const σ).aemeasurable)

/-- Exact closed-strip probabilities retain time zero, atoms and weak endpoints. -/
theorem closedStrip_probability_standardization
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) (σ h : ℝ)
    (hσ : 0 < σ) (hh : 0 ≤ h) :
    (Measure.pi (fun _ : Fin n => ν)).real (@Shao.closedStrip n h) =
      (Measure.pi (fun _ : Fin n => ν.map (fun x : ℝ => x / σ))).real
        (@Shao.closedStrip n (h / σ)) := by
  have hscaled : Measurable (fun a : Shao.Path n => σ⁻¹ • a) := by
    apply measurable_pi_iff.mpr
    intro i
    change Measurable (fun a : Shao.Path n => σ⁻¹ * a i)
    exact measurable_const.mul (measurable_pi_apply i)
  have hC : MeasurableSet (@Shao.closedStrip n (h / σ)) := by
    rw [← shiftedClosedSurvival_eq_closedStrip n (h / σ) (div_nonneg hh hσ.le)]
    exact measurableSet_shiftedClosedSurvival n (h / σ) 0
  have hpreimage :
      (fun a : Shao.Path n => σ⁻¹ • a) ⁻¹' (@Shao.closedStrip n (h / σ)) =
        @Shao.closedStrip n h := by
    ext a
    change (∀ k : ℕ, k ≤ n → |Shao.prefixSum (σ⁻¹ • a) k| ≤ h / σ) ↔
      ∀ k : ℕ, k ≤ n → |Shao.prefixSum a k| ≤ h
    exact (path_variance_scaling a σ h hσ hh).2.2
  have hmeasure :
      (Measure.pi (fun _ : Fin n => ν.map (fun x : ℝ => x / σ)))
          (@Shao.closedStrip n (h / σ)) =
        (Measure.pi (fun _ : Fin n => ν)) (@Shao.closedStrip n h) := by
    rw [← finite_product_standardization_map ν n σ,
      Measure.map_apply hscaled hC, hpreimage]
  change ((Measure.pi (fun _ : Fin n => ν)) (@Shao.closedStrip n h)).toReal =
    ((Measure.pi (fun _ : Fin n => ν.map (fun x : ℝ => x / σ)))
      (@Shao.closedStrip n (h / σ))).toReal
  exact congrArg ENNReal.toReal hmeasure.symm

private theorem standardized_height_tendsto
    (vSeq hSeq : ℕ → ℝ)
    (hvlower : ∀ j, (1 / 2 : ℝ) ≤ vSeq j)
    (hvupper : ∀ j, vSeq j ≤ 2)
    (hpos : ∀ j, 0 < hSeq j)
    (hinfty : Tendsto hSeq atTop atTop) :
    (∀ j, 0 < hSeq j / Real.sqrt (vSeq j)) ∧
      Tendsto (fun j => hSeq j / Real.sqrt (vSeq j)) atTop atTop := by
  constructor
  · intro j
    exact div_pos (hpos j)
      (sqrt_variance_uniform_bounds (vSeq j) (hvlower j) (hvupper j)).1
  · apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [hinfty.eventually (eventually_ge_atTop (2 * b))] with j hj
    obtain ⟨hσpos, _, _, hσupper⟩ :=
      sqrt_variance_uniform_bounds (vSeq j) (hvlower j) (hvupper j)
    calc
      b ≤ hSeq j / 2 := by linarith
      _ ≤ hSeq j / Real.sqrt (vSeq j) := by
        apply (le_div_iff₀ hσpos).mpr
        have hp := mul_nonneg (hpos j).le (sub_nonneg.mpr hσupper)
        nlinarith

private theorem standardized_quadratic_ratio_tendsto
    (vSeq hSeq : ℕ → ℝ) (NSeq : ℕ → ℕ)
    (hvlower : ∀ j, (1 / 2 : ℝ) ≤ vSeq j)
    (hvupper : ∀ j, vSeq j ≤ 2)
    (hpos : ∀ j, 0 < hSeq j)
    (hlong : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 2) atTop atTop) :
    Tendsto (fun j => (NSeq j : ℝ) /
      (hSeq j / Real.sqrt (vSeq j)) ^ 2) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [hlong.eventually (eventually_ge_atTop (2 * b))] with j hj
  have hrnonneg : 0 ≤ (NSeq j : ℝ) / hSeq j ^ 2 :=
    div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hratio :=
    (sqrt_variance_scale_ratios (NSeq j) (vSeq j) (hSeq j)
      (hvlower j) (hvupper j) (hpos j)).1
  calc
    b ≤ (1 / 2 : ℝ) * ((NSeq j : ℝ) / hSeq j ^ 2) := by linarith
    _ ≤ vSeq j * ((NSeq j : ℝ) / hSeq j ^ 2) :=
      mul_le_mul_of_nonneg_right (hvlower j) hrnonneg
    _ = (NSeq j : ℝ) / (hSeq j / Real.sqrt (vSeq j)) ^ 2 := by
      rw [hratio]
      ring

private theorem standardized_cubic_ratio_tendsto
    (vSeq hSeq : ℕ → ℝ) (NSeq : ℕ → ℕ)
    (hvlower : ∀ j, (1 / 2 : ℝ) ≤ vSeq j)
    (hvupper : ∀ j, vSeq j ≤ 2)
    (hpos : ∀ j, 0 < hSeq j)
    (hshort : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 3)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j => (NSeq j : ℝ) /
      (hSeq j / Real.sqrt (vSeq j)) ^ 3) atTop (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp hshort) (ε / 8) (by linarith)
  refine ⟨J, ?_⟩
  intro j hj
  have hinput : |(NSeq j : ℝ) / hSeq j ^ 3| < ε / 8 := by
    simpa only [Real.dist_eq, sub_zero] using hJ j hj
  obtain ⟨hσpos, _, _, hσupper⟩ :=
    sqrt_variance_uniform_bounds (vSeq j) (hvlower j) (hvupper j)
  have hσsq : Real.sqrt (vSeq j) * Real.sqrt (vSeq j) ≤ (2 : ℝ) * 2 :=
    mul_le_mul hσupper hσupper hσpos.le (by norm_num)
  have hσcube : (Real.sqrt (vSeq j)) ^ 3 ≤ (8 : ℝ) := by
    have hc := mul_le_mul hσsq hσupper hσpos.le (by norm_num : (0 : ℝ) ≤ 2 * 2)
    nlinarith only [hc]
  have hsnonneg : 0 ≤ (NSeq j : ℝ) / hSeq j ^ 3 :=
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg (hpos j).le 3)
  have hanonneg : 0 ≤ (NSeq j : ℝ) /
      (hSeq j / Real.sqrt (vSeq j)) ^ 3 :=
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_pos (hpos j) hσpos).le 3)
  have hratio :=
    (sqrt_variance_scale_ratios (NSeq j) (vSeq j) (hSeq j)
      (hvlower j) (hvupper j) (hpos j)).2
  have hbound : (NSeq j : ℝ) / (hSeq j / Real.sqrt (vSeq j)) ^ 3 ≤
      8 * ((NSeq j : ℝ) / hSeq j ^ 3) := by
    calc
      (NSeq j : ℝ) / (hSeq j / Real.sqrt (vSeq j)) ^ 3 =
          (Real.sqrt (vSeq j)) ^ 3 * ((NSeq j : ℝ) / hSeq j ^ 3) := by
        rw [hratio]
        ring
      _ ≤ 8 * ((NSeq j : ℝ) / hSeq j ^ 3) :=
        mul_le_mul_of_nonneg_right hσcube hsnonneg
  have hsmall : |(NSeq j : ℝ) /
      (hSeq j / Real.sqrt (vSeq j)) ^ 3| < ε := by
    rw [abs_of_nonneg hanonneg]
    have hslt : (NSeq j : ℝ) / hSeq j ^ 3 < ε / 8 := by
      simpa only [abs_of_nonneg hsnonneg] using hinput
    exact hbound.trans_lt (by linarith)
  simpa only [Real.dist_eq, sub_zero] using hsmall

/-- Conditional Kv for varying laws and variances with one common third-moment bound. -/
theorem varying_row_variance_closedStrip_relative_asymptotic
    (νSeq : ℕ → Measure ℝ) (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (vSeq : ℕ → ℝ)
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = vSeq j)
    (hvlower : ∀ j, (1 / 2 : ℝ) ≤ vSeq j)
    (hvupper : ∀ j, vSeq j ≤ 2)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (Cq Cs : ℝ) (hCq : 0 ≤ Cq) (hCs : 0 ≤ Cs)
    (hAC : ∀ j,
      iidIntervalConcentration
        ((νSeq j).map (fun x : ℝ => x / Real.sqrt (vSeq j)))
        (∫ y : ℝ, |y| ^ 3
          ∂((νSeq j).map (fun x : ℝ => x / Real.sqrt (vSeq j)))) Cq)
    (hS : ∀ j,
      iidOneSidedSurvival
        ((νSeq j).map (fun x : ℝ => x / Real.sqrt (vSeq j)))
        (∫ y : ℝ, |y| ^ 3
          ∂((νSeq j).map (fun x : ℝ => x / Real.sqrt (vSeq j)))) Cs)
    (hSeq : ℕ → ℝ) (NSeq : ℕ → ℕ) (hpos : ∀ j, 0 < hSeq j)
    (hinfty : Tendsto hSeq atTop atTop)
    (hlong : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 3)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j =>
      (Measure.pi (fun _ : Fin (NSeq j) => νSeq j)).real
        (@Shao.closedStrip (NSeq j) (hSeq j)) /
          ((4 / Real.pi) *
            Real.exp (-lambda * vSeq j * (NSeq j : ℝ) / hSeq j ^ 2)))
      atTop (𝓝 (1 : ℝ)) := by
  let ηSeq : ℕ → Measure ℝ :=
    fun j => (νSeq j).map (fun x : ℝ => x / Real.sqrt (vSeq j))
  let aSeq : ℕ → ℝ := fun j => hSeq j / Real.sqrt (vSeq j)
  have hmom := fun j : ℕ =>
    @standardized_law_moments (νSeq j) (hprob j) (vSeq j) M
      (hvlower j) (hvupper j) (h3 j) (hmean j) (hsecond j) (hM j)
  have hprobη : ∀ j, IsProbabilityMeasure (ηSeq j) := fun j => (hmom j).1
  have h3η : ∀ j, Integrable (fun y : ℝ => |y| ^ 3) (ηSeq j) :=
    fun j => (hmom j).2.2.2.1
  have hmeanη : ∀ j, (∫ y : ℝ, y ∂(ηSeq j)) = 0 :=
    fun j => (hmom j).2.2.2.2.1
  have hsecondη : ∀ j, (∫ y : ℝ, y ^ 2 ∂(ηSeq j)) = 1 :=
    fun j => (hmom j).2.2.2.2.2.1
  have hMη : ∀ j, (∫ y : ℝ, |y| ^ 3 ∂(ηSeq j)) ≤ 8 * M :=
    fun j => (hmom j).2.2.2.2.2.2.2
  have hheight :=
    standardized_height_tendsto vSeq hSeq hvlower hvupper hpos hinfty
  have hquadratic :=
    standardized_quadratic_ratio_tendsto vSeq hSeq NSeq hvlower hvupper hpos hlong
  have hcubic :=
    standardized_cubic_ratio_tendsto vSeq hSeq NSeq hvlower hvupper hpos hshort
  have hresult :=
    TerminalNormalizedKernelLimit.varying_row_closedStrip_relative_asymptotic
      ηSeq hprobη h3η hmeanη hsecondη (8 * M) hMη Cq Cs hCq hCs hAC hS
      aSeq NSeq hheight.1 hheight.2 hquadratic hcubic
  have heq (j : ℕ) :
      (Measure.pi (fun _ : Fin (NSeq j) => ηSeq j)).real
          (@Shao.closedStrip (NSeq j) (aSeq j)) /
        ((4 / Real.pi) * Real.exp (-lambda * (NSeq j : ℝ) / aSeq j ^ 2)) =
      (Measure.pi (fun _ : Fin (NSeq j) => νSeq j)).real
          (@Shao.closedStrip (NSeq j) (hSeq j)) /
        ((4 / Real.pi) *
          Real.exp (-lambda * vSeq j * (NSeq j : ℝ) / hSeq j ^ 2)) := by
    have hσpos :=
      (sqrt_variance_uniform_bounds (vSeq j) (hvlower j) (hvupper j)).1
    have hnum :
        (Measure.pi (fun _ : Fin (NSeq j) => ηSeq j)).real
            (@Shao.closedStrip (NSeq j) (aSeq j)) =
          (Measure.pi (fun _ : Fin (NSeq j) => νSeq j)).real
            (@Shao.closedStrip (NSeq j) (hSeq j)) := by
      simpa only [ηSeq, aSeq] using
        (@closedStrip_probability_standardization (νSeq j) (hprob j) (NSeq j)
          (Real.sqrt (vSeq j)) (hSeq j) hσpos (hpos j).le).symm
    have hratio :=
      (sqrt_variance_scale_ratios (NSeq j) (vSeq j) (hSeq j)
        (hvlower j) (hvupper j) (hpos j)).1
    have hexponent : -lambda * (NSeq j : ℝ) / aSeq j ^ 2 =
        -lambda * vSeq j * (NSeq j : ℝ) / hSeq j ^ 2 := by
      change -lambda * (NSeq j : ℝ) /
        (hSeq j / Real.sqrt (vSeq j)) ^ 2 = _
      calc
        -lambda * (NSeq j : ℝ) / (hSeq j / Real.sqrt (vSeq j)) ^ 2 =
            -lambda * ((NSeq j : ℝ) / (hSeq j / Real.sqrt (vSeq j)) ^ 2) := by
          ring
        _ = -lambda * (vSeq j * (NSeq j : ℝ) / hSeq j ^ 2) := by rw [hratio]
        _ = -lambda * vSeq j * (NSeq j : ℝ) / hSeq j ^ 2 := by ring
    rw [hnum, hexponent]
  have hfun :
      (fun j : ℕ =>
        (Measure.pi (fun _ : Fin (NSeq j) => ηSeq j)).real
            (@Shao.closedStrip (NSeq j) (aSeq j)) /
          ((4 / Real.pi) * Real.exp (-lambda * (NSeq j : ℝ) / aSeq j ^ 2))) =
      (fun j : ℕ =>
        (Measure.pi (fun _ : Fin (NSeq j) => νSeq j)).real
            (@Shao.closedStrip (NSeq j) (hSeq j)) /
          ((4 / Real.pi) *
            Real.exp (-lambda * vSeq j * (NSeq j : ℝ) / hSeq j ^ 2))) :=
    funext heq
  rw [hfun] at hresult
  exact hresult

end Shao.OQ4.VarianceKernelAsymptotic
end
