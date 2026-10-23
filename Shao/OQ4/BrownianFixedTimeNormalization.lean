-- Complete LOCAL implementation of the exact parent freeze.
-- 20 owned heads, one literal transparent value; imports and statements unchanged.
-- No Lean command or import/object check is authorized at this stage.
-- Required upstream143/145/146 qualification and independent review remain pending.
import Shao.OQ4.BrownianKilledCosineIdentity
import Shao.OQ4.CanonicalBrownian
import Shao.OQ4.CosinePowers
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Order.Filter.AtTopBot.Tendsto

noncomputable section
namespace Shao.OQ4.BrownianFixedTimeNormalization
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

-- The sole new transparent value. Never replace this ceil by the monitored floor.
private def rowLength (h : ℝ) : ℕ := ⌈h ^ 2⌉₊

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
  have hid : AEStronglyMeasurable (fun x : ℝ => x) ν :=
    measurable_id.aestronglyMeasurable
  have hsq : AEStronglyMeasurable (fun x : ℝ => x ^ 2) ν :=
    (by fun_prop : Measurable (fun x : ℝ => x ^ 2)).aestronglyMeasurable
  refine ⟨hdom.mono' hid ?_, hdom.mono' hsq ?_⟩
  · exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using (hsmall |x| (abs_nonneg x)).1
  · exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x), sq_abs] using
        (hsmall |x| (abs_nonneg x)).2

private theorem third_moment_nonneg (ν : Measure ℝ) :
    0 ≤ ∫ x : ℝ, |x| ^ 3 ∂ν := by
  exact integral_nonneg fun x => pow_nonneg (abs_nonneg x) 3

private theorem rowLength_horizon (h : ℝ) :
    h ^ 2 ≤ (rowLength h : ℝ) := by
  exact Nat.le_ceil (h ^ 2)

private theorem stepCount_le_rowLength (h : ℝ) :
    ⌊h ^ 2⌋₊ ≤ rowLength h := by
  exact Nat.floor_le_ceil (h ^ 2)

private theorem stepCount_ratio_bounds (h : ℝ) (hh : 0 < h) :
    0 ≤ 1 - (⌊h ^ 2⌋₊ : ℝ) / h ^ 2 ∧
      1 - (⌊h ^ 2⌋₊ : ℝ) / h ^ 2 < 1 / h ^ 2 := by
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
  have hf : (⌊h ^ 2⌋₊ : ℝ) ≤ h ^ 2 := Nat.floor_le (sq_nonneg h)
  have hlt : h ^ 2 < (⌊h ^ 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hr : (⌊h ^ 2⌋₊ : ℝ) / h ^ 2 ≤ 1 := (div_le_one hh2).mpr hf
  refine ⟨sub_nonneg.mpr hr, ?_⟩
  apply (lt_div_iff₀ hh2).mpr
  have heq : (1 - (⌊h ^ 2⌋₊ : ℝ) / h ^ 2) * h ^ 2 =
      h ^ 2 - (⌊h ^ 2⌋₊ : ℝ) := by
    field_simp [ne_of_gt hh2] <;> ring
  rw [heq]
  linarith

private theorem stepCount_ratio_tendsto
    (hSeq : ℕ → ℝ) (hpos : ∀ j, 0 < hSeq j)
    (hinfty : Tendsto hSeq atTop atTop) :
    Tendsto (fun j => (⌊hSeq j ^ 2⌋₊ : ℝ) / hSeq j ^ 2) atTop (𝓝 (1 : ℝ)) := by
  have hi : Tendsto (fun j => (hSeq j)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hinfty
  have hb : Tendsto (fun j => 1 / hSeq j ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div, inv_pow] using hi.pow 2
  have hz : Tendsto (fun j => 1 - (⌊hSeq j ^ 2⌋₊ : ℝ) / hSeq j ^ 2)
      atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun j => (stepCount_ratio_bounds (hSeq j) (hpos j)).1)
      (fun j => (stepCount_ratio_bounds (hSeq j) (hpos j)).2.le) hb
  have ht := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ))).sub hz
  simpa only [sub_sub_cancel, sub_zero] using ht

private theorem large_h_eventually (M : ℝ) (hSeq : ℕ → ℝ)
    (hinfty : Tendsto hSeq atTop atTop) :
    ∀ᶠ j in atTop, 1 ≤ hSeq j ∧ Real.pi * (1 + M) ≤ hSeq j := by
  exact (hinfty.eventually (eventually_ge_atTop 1)).and
    (hinfty.eventually (eventually_ge_atTop (Real.pi * (1 + M))))

private theorem row_free_log_error
    (νSeq : ℕ → Measure ℝ) (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (hinfty : Tendsto hSeq atTop atTop) :
    ∀ᶠ j in atTop,
      ((3 : ℝ) / 4 ≤ cosineCoefficient (νSeq j) (Real.pi / (2 * hSeq j)) ∧
        cosineCoefficient (νSeq j) (Real.pi / (2 * hSeq j)) < 1) ∧
      |(⌊hSeq j ^ 2⌋₊ : ℝ) *
          Real.log (cosineCoefficient (νSeq j) (Real.pi / (2 * hSeq j))) +
        (Real.pi ^ 2 / 8) * ((⌊hSeq j ^ 2⌋₊ : ℝ) / hSeq j ^ 2)| ≤
          (Real.pi ^ 3 * M / 48 + Real.pi ^ 4 / 8) / hSeq j := by
  have hM0 : 0 ≤ M := (third_moment_nonneg (νSeq 0)).trans (hM 0)
  filter_upwards [large_h_eventually M hSeq hinfty] with j hj
  letI : IsProbabilityMeasure (νSeq j) := hprob j
  rcases lower_moments_integrable (νSeq j) (h3 j) with ⟨hId, hSq⟩
  have hb := cosineCoefficient_large_h_bounds (νSeq j) M (hSeq j)
    hId hSq (h3 j) (hmean j) (hsecond j) hM0 (hM j) hj.1 hj.2
  have he := cosineCoefficient_log_error_mul (νSeq j) M (hSeq j)
    hId hSq (h3 j) (hmean j) (hsecond j) hM0 (hM j) hj.1 hj.2 ⌊hSeq j ^ 2⌋₊
  refine ⟨⟨hb.2.2.1, hb.2.2.2⟩, ?_⟩
  have hh : 0 < hSeq j := lt_of_lt_of_le zero_lt_one hj.1
  have hC : 0 ≤ Real.pi ^ 3 * M / 48 + Real.pi ^ 4 / 8 := by positivity
  have hf : (⌊hSeq j ^ 2⌋₊ : ℝ) ≤ hSeq j ^ 2 := Nat.floor_le (sq_nonneg _)
  have hden :
      (Real.pi ^ 3 * M / 48 + Real.pi ^ 4 / 8) * (⌊hSeq j ^ 2⌋₊ : ℝ) / hSeq j ^ 3 ≤
        (Real.pi ^ 3 * M / 48 + Real.pi ^ 4 / 8) / hSeq j := by
    calc
      _ ≤ (Real.pi ^ 3 * M / 48 + Real.pi ^ 4 / 8) * hSeq j ^ 2 / hSeq j ^ 3 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hf hC)
          (pow_nonneg hh.le 3)
      _ = _ := by field_simp [ne_of_gt hh] <;> ring
  have heq : Real.pi ^ 2 * (⌊hSeq j ^ 2⌋₊ : ℝ) / (8 * hSeq j ^ 2) =
      (Real.pi ^ 2 / 8) * ((⌊hSeq j ^ 2⌋₊ : ℝ) / hSeq j ^ 2) := by
    field_simp [ne_of_gt hh] <;> ring
  rw [heq] at he
  exact he.trans hden

private theorem row_free_power_tendsto
    (νSeq : ℕ → Measure ℝ) (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (hpos : ∀ j, 0 < hSeq j)
    (hinfty : Tendsto hSeq atTop atTop) :
    Tendsto (fun j => cosineCoefficient (νSeq j) (Real.pi / (2 * hSeq j)) ^
      ⌊hSeq j ^ 2⌋₊) atTop (𝓝 (Real.exp (-(Real.pi ^ 2 / 8)))) := by
  have hevent := row_free_log_error νSeq hprob h3 hmean hsecond M hM hSeq hinfty
  have hb : Tendsto (fun j =>
      (Real.pi ^ 3 * M / 48 + Real.pi ^ 4 / 8) / hSeq j) atTop (𝓝 (0 : ℝ)) := by
    have ht : Tendsto (fun j =>
        (Real.pi ^ 3 * M / 48 + Real.pi ^ 4 / 8) * (hSeq j)⁻¹) atTop
        (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero, Function.comp_def] using
        (tendsto_inv_atTop_zero.comp hinfty).const_mul
          (Real.pi ^ 3 * M / 48 + Real.pi ^ 4 / 8)
    convert ht using 1
    funext j
    exact div_eq_mul_inv _ _
  have herr : Tendsto (fun j =>
      |(⌊hSeq j ^ 2⌋₊ : ℝ) *
          Real.log (cosineCoefficient (νSeq j) (Real.pi / (2 * hSeq j))) +
        (Real.pi ^ 2 / 8) * ((⌊hSeq j ^ 2⌋₊ : ℝ) / hSeq j ^ 2)|) atTop
      (𝓝 (0 : ℝ)) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
      (hevent.mono fun _ hj => hj.2) hb
  have hsum : Tendsto (fun j =>
      (⌊hSeq j ^ 2⌋₊ : ℝ) *
          Real.log (cosineCoefficient (νSeq j) (Real.pi / (2 * hSeq j))) +
        (Real.pi ^ 2 / 8) * ((⌊hSeq j ^ 2⌋₊ : ℝ) / hSeq j ^ 2)) atTop
      (𝓝 (0 : ℝ)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq, sub_zero] using herr
  have hratio := (stepCount_ratio_tendsto hSeq hpos hinfty).const_mul (Real.pi ^ 2 / 8)
  have hlog : Tendsto (fun j =>
      (⌊hSeq j ^ 2⌋₊ : ℝ) *
        Real.log (cosineCoefficient (νSeq j) (Real.pi / (2 * hSeq j)))) atTop
      (𝓝 (-(Real.pi ^ 2 / 8))) := by
    simpa only [add_sub_cancel_right, zero_sub, mul_one] using hsum.sub hratio
  have hexp : Tendsto (fun j => Real.exp
      ((⌊hSeq j ^ 2⌋₊ : ℝ) *
        Real.log (cosineCoefficient (νSeq j) (Real.pi / (2 * hSeq j))))) atTop
      (𝓝 (Real.exp (-(Real.pi ^ 2 / 8)))) :=
    (Real.continuous_exp.tendsto _).comp hlog
  have heq : ∀ᶠ j in atTop,
      cosineCoefficient (νSeq j) (Real.pi / (2 * hSeq j)) ^ ⌊hSeq j ^ 2⌋₊ =
        Real.exp ((⌊hSeq j ^ 2⌋₊ : ℝ) *
          Real.log (cosineCoefficient (νSeq j) (Real.pi / (2 * hSeq j)))) := by
    filter_upwards [hevent] with j hj
    have hρ : 0 < cosineCoefficient (νSeq j) (Real.pi / (2 * hSeq j)) :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4) hj.1.1
    rw [← Real.log_pow, Real.exp_log (pow_pos hρ _)]
  exact Filter.Tendsto.congr' (heq.mono fun _ hj => hj.symm) hexp

private theorem cosine_test_measurable (h : ℝ) :
    Measurable (fun w : ℝ => Real.cos ((Real.pi / (2 * h)) * w)) := by
  fun_prop

private theorem cosine_test_bound (h w : ℝ) :
    |Real.cos ((Real.pi / (2 * h)) * w)| ≤ 1 := by
  exact Real.abs_cos_le_one _

-- Exact producer145 bridge at physical start zero and radius one.
-- Both the actual killed integrability and exact finite-row equality are retained.
private theorem discrete_cosine_integral_eq_killed
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n l : ℕ) (hl : l ≤ n) (h : ℝ) (hh : 0 < h) :
    Integrable (fun w : ℝ => Real.cos ((Real.pi / (2 * h)) * w))
      (killedIterKernel ν h l 0) ∧
    (∫ a : Shao.Path n,
      PolygonalKilledFunctionalLimit.discreteKilledCosine n l h 0 1 a
        ∂Measure.pi (fun _ : Fin n => ν)) =
      killedAction ν h l (fun w => Real.cos ((Real.pi / (2 * h)) * w)) 0 := by
  classical
  have hz : |(0 : ℝ)| ≤ ((1 : ℝ≥0) : ℝ) * h := by simpa using hh.le
  have ht := BrownianKilledCosineIdentity.discrete_killed_test_integral
    ν n l hl h hh 1 0 hz
    (fun w : ℝ => Real.cos ((Real.pi / (2 * h)) * w))
    (cosine_test_measurable h) ⟨1, fun w => cosine_test_bound h w⟩
  have hcut (a : Shao.Path n) :
      PolygonalKilledFunctionalLimit.discreteKilledCosine n l h 0 1 a =
        (PolygonalKilledFunctionalLimit.discreteClosedSurvival n l h (0 / h) 1).indicator
          (fun a : Shao.Path n => Real.cos ((Real.pi / (2 * h)) *
            (0 + Shao.prefixSum a l))) a := by
    unfold PolygonalKilledFunctionalLimit.discreteKilledCosine
    simp only [zero_div]
    by_cases he : a ∈ PolygonalKilledFunctionalLimit.discreteClosedSurvival n l h 0 1
    · simp only [Set.indicator_of_mem he, zero_add]
      congr 1
      field_simp [ne_of_gt hh] <;> ring
    · simp only [Set.indicator_of_notMem he]
  refine ⟨?_, ?_⟩
  · simpa only [NNReal.coe_one, one_mul] using ht.1
  · calc
      _ = ∫ a : Shao.Path n,
          (PolygonalKilledFunctionalLimit.discreteClosedSurvival n l h (0 / h) 1).indicator
            (fun a => Real.cos ((Real.pi / (2 * h)) * (0 + Shao.prefixSum a l))) a
              ∂Measure.pi (fun _ : Fin n => ν) :=
        integral_congr_ae (Eventually.of_forall hcut)
      _ = _ := by simpa only [NNReal.coe_one, one_mul] using ht.2.2

-- Instantiate the actual frozen canonical146 values; no supplied process.
private theorem canonical_killed_cosine_integral :
    (∫ ω : CanonicalBrownian.Sample,
      PolygonalKilledFunctionalLimit.brownianKilledCosine
        CanonicalBrownian.B 1 0 ω ∂CanonicalBrownian.law) =
      Real.exp (-(Real.pi ^ 2 / 8)) := by
  simpa using BrownianKilledCosineIdentity.brownian_killed_cosine_identity
    CanonicalBrownian.B CanonicalBrownian.law CanonicalBrownian.isBrownianReal
    (1 : ℝ≥0) 0 (by norm_num)

private theorem row_killed_cosine_tendsto
    (νSeq : ℕ → Measure ℝ) (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (hpos : ∀ j, 0 < hSeq j)
    (hinfty : Tendsto hSeq atTop atTop) :
    Tendsto (fun j => @killedAction (νSeq j) (hprob j) (hSeq j) ⌊hSeq j ^ 2⌋₊
      (fun w => Real.cos ((Real.pi / (2 * hSeq j)) * w)) 0) atTop
        (𝓝 (Real.exp (-(Real.pi ^ 2 / 8)))) := by
  let nSeq : ℕ → ℕ := fun j => rowLength (hSeq j)
  have horizon (j : ℕ) : ((1 : ℝ≥0) : ℝ) * hSeq j ^ 2 ≤ (nSeq j : ℝ) := by
    simpa only [NNReal.coe_one, one_mul, nSeq] using rowLength_horizon (hSeq j)
  have hlim := PolygonalKilledFunctionalLimit.discrete_killed_cosine_tendsto_brownian
    CanonicalBrownian.B CanonicalBrownian.law CanonicalBrownian.isBrownianReal
    (1 : ℝ≥0) (by norm_num) nSeq hSeq νSeq hprob hpos horizon
    h3 hmean hsecond M hM hinfty
    (fun _ => (1 : ℝ≥0)) tendsto_const_nhds
    (fun _ => (0 : ℝ)) 0 tendsto_const_nhds (by norm_num)
  have hlim' : Tendsto (fun j => ∫ a : Shao.Path (nSeq j),
      PolygonalKilledFunctionalLimit.discreteKilledCosine
        (nSeq j) ⌊hSeq j ^ 2⌋₊ (hSeq j) 0 1 a
          ∂Measure.pi (fun _ : Fin (nSeq j) => νSeq j)) atTop
      (𝓝 (Real.exp (-(Real.pi ^ 2 / 8)))) := by
    simpa only [PolygonalKilledFunctionalLimit.floorHorizon, NNReal.coe_one, one_mul,
      canonical_killed_cosine_integral] using hlim
  have hrows (j : ℕ) :
      (∫ a : Shao.Path (nSeq j),
        PolygonalKilledFunctionalLimit.discreteKilledCosine
          (nSeq j) ⌊hSeq j ^ 2⌋₊ (hSeq j) 0 1 a
            ∂Measure.pi (fun _ : Fin (nSeq j) => νSeq j)) =
      @killedAction (νSeq j) (hprob j) (hSeq j) ⌊hSeq j ^ 2⌋₊
        (fun w => Real.cos ((Real.pi / (2 * hSeq j)) * w)) 0 := by
    letI : IsProbabilityMeasure (νSeq j) := hprob j
    exact (discrete_cosine_integral_eq_killed (νSeq j) (nSeq j) ⌊hSeq j ^ 2⌋₊
      (stepCount_le_rowLength (hSeq j)) (hSeq j) (hpos j)).2
  exact Filter.Tendsto.congr' (Eventually.of_forall hrows) hlim'

private theorem real_tendsto_atTop_of_positive_sequences
    (f : ℝ → ℝ) (a : ℝ)
    (hseq : ∀ hSeq : ℕ → ℝ, (∀ j, 0 < hSeq j) →
      Tendsto hSeq atTop atTop →
      Tendsto (fun j => f (hSeq j)) atTop (𝓝 a)) :
    Tendsto f atTop (𝓝 a) := by
  classical
  by_contra hn
  have hfail : ¬ (∀ ε > 0, ∃ H : ℝ, ∀ h ≥ H, dist (f h) a < ε) := by
    intro h
    exact hn (Metric.tendsto_atTop.mpr h)
  push_neg at hfail
  obtain ⟨ε, hε, hfail⟩ := hfail
  have hw (j : ℕ) : ∃ h : ℝ, (j : ℝ) + 1 ≤ h ∧ ε ≤ dist (f h) a :=
    hfail ((j : ℝ) + 1)
  let hSeq : ℕ → ℝ := fun j => Classical.choose (hw j)
  have hlow (j : ℕ) : (j : ℝ) + 1 ≤ hSeq j :=
    (Classical.choose_spec (hw j)).1
  have hbad (j : ℕ) : ε ≤ dist (f (hSeq j)) a :=
    (Classical.choose_spec (hw j)).2
  have hpos (j : ℕ) : 0 < hSeq j :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (j : ℝ) + 1) (hlow j)
  have hinfty : Tendsto hSeq atTop atTop :=
    tendsto_atTop_mono (fun j : ℕ => by have hj := hlow j; linarith)
      (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop)
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp (hseq hSeq hpos hinfty)) ε hε
  exact (not_lt_of_ge (hbad J)) (hJ J le_rfl)

-- PUBLIC strengthened sequential/common-M form, separately labelled.
-- An explicit hprob is used by each actual killedAction instance.
theorem varying_row_fixed_time_limits
    (νSeq : ℕ → Measure ℝ) (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (hpos : ∀ j, 0 < hSeq j)
    (hinfty : Tendsto hSeq atTop atTop) :
    Tendsto (fun j => cosineCoefficient (νSeq j) (Real.pi / (2 * hSeq j)) ^
      ⌊hSeq j ^ 2⌋₊) atTop (𝓝 (Real.exp (-(Real.pi ^ 2 / 8)))) ∧
    Tendsto (fun j => @killedAction (νSeq j) (hprob j) (hSeq j) ⌊hSeq j ^ 2⌋₊
      (fun w => Real.cos ((Real.pi / (2 * hSeq j)) * w)) 0) atTop
        (𝓝 (Real.exp (-(Real.pi ^ 2 / 8)))) ∧
    Tendsto (fun j =>
      (cosineCoefficient (νSeq j) (Real.pi / (2 * hSeq j)) ^ ⌊hSeq j ^ 2⌋₊)⁻¹ *
        @killedAction (νSeq j) (hprob j) (hSeq j) ⌊hSeq j ^ 2⌋₊
          (fun w => Real.cos ((Real.pi / (2 * hSeq j)) * w)) 0) atTop (𝓝 (1 : ℝ)) := by
  have hp := row_free_power_tendsto νSeq hprob h3 hmean hsecond M hM hSeq hpos hinfty
  have hk := row_killed_cosine_tendsto νSeq hprob h3 hmean hsecond M hM hSeq hpos hinfty
  have hc : Real.exp (-(Real.pi ^ 2 / 8)) ≠ 0 := ne_of_gt (Real.exp_pos _)
  refine ⟨hp, hk, ?_⟩
  simpa only [inv_mul_cancel₀ hc] using (hp.inv₀ hc).mul hk

-- PUBLIC actual free rho_h power limit, with first/second integrability derived.
theorem free_cosine_power_tendsto
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    Tendsto (fun h : ℝ => cosineCoefficient ν (Real.pi / (2 * h)) ^ ⌊h ^ 2⌋₊)
      atTop (𝓝 (Real.exp (-(Real.pi ^ 2 / 8)))) := by
  apply real_tendsto_atTop_of_positive_sequences
  intro hSeq hpos hinfty
  exact row_free_power_tendsto (fun _ => ν) (fun _ => inferInstance)
    (fun _ => h3) (fun _ => hmean) (fun _ => hsecond)
    (∫ x : ℝ, |x| ^ 3 ∂ν) (fun _ => le_rfl) hSeq hpos hinfty

-- PUBLIC actual killed numerator at the original start zero and floor(h^2).
theorem killed_cosine_tendsto
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    Tendsto (fun h : ℝ => killedAction ν h ⌊h ^ 2⌋₊
      (fun w => Real.cos ((Real.pi / (2 * h)) * w)) 0) atTop
        (𝓝 (Real.exp (-(Real.pi ^ 2 / 8)))) := by
  apply real_tendsto_atTop_of_positive_sequences
  intro hSeq hpos hinfty
  exact row_killed_cosine_tendsto (fun _ => ν) (fun _ => inferInstance)
    (fun _ => h3) (fun _ => hmean) (fun _ => hsecond)
    (∫ x : ℝ, |x| ^ 3 ∂ν) (fun _ => le_rfl) hSeq hpos hinfty

-- PUBLIC mandatory source B1. Pure actual kernel conclusion; no Brownian premise.
-- Inverse natural power is the source rho_h^(-m); eventual rho_h > 0 is proved.
theorem fixed_time_normalization
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    Tendsto (fun h : ℝ =>
      (cosineCoefficient ν (Real.pi / (2 * h)) ^ ⌊h ^ 2⌋₊)⁻¹ *
        killedAction ν h ⌊h ^ 2⌋₊
          (fun w => Real.cos ((Real.pi / (2 * h)) * w)) 0) atTop (𝓝 (1 : ℝ)) := by
  have hp := free_cosine_power_tendsto ν h3 hmean hsecond
  have hk := killed_cosine_tendsto ν h3 hmean hsecond
  have hc : Real.exp (-(Real.pi ^ 2 / 8)) ≠ 0 := ne_of_gt (Real.exp_pos _)
  simpa only [inv_mul_cancel₀ hc] using (hp.inv₀ hc).mul hk

end Shao.OQ4.BrownianFixedTimeNormalization
end
