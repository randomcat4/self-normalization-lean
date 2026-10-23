-- Complete LOCAL implementation of the parent-frozen six theorem heads.
-- Formal freeze SHA256 559fe9d75db2c25c79daa0f9cd7b81cb275f3a2bc7dc2daddd19222570d45811.
-- All eight imports and zero new top-level values are preserved.
-- UNQUALIFIED: root BE and exact149/150/154/156 qualifications remain pending.
-- No server/kernel/axiom check or independent implementation review is claimed.

import Shao.Probability.BerryEsseen
import Shao.Probability.SpitzerLaplace
import Shao.OQ4.SpitzerKernelBounds
import Shao.OQ4.TerminalNormalizedKernelLimit
import Shao.OQ4.VarianceKernelAsymptotic
import Shao.OQ4.VarianceScaling
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
noncomputable section
namespace Shao.OQ4.UnconditionalKernelAsymptotic
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
  · apply hdom.mono' (by fun_prop : Measurable (fun x : ℝ => x ^ 2)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_pow, id_eq] using (hsmall |x| (abs_nonneg x)).2

private theorem standardized_law_unit_moments
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (v : ℝ) (hv : 0 < v)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = v) :
    let σ : ℝ := Real.sqrt v
    let η : Measure ℝ := ν.map (fun x : ℝ => x / σ)
    IsProbabilityMeasure η ∧
      Integrable (fun y : ℝ => |y| ^ 3) η ∧
      (∫ y : ℝ, y ∂η) = 0 ∧
      (∫ y : ℝ, y ^ 2 ∂η) = 1 ∧
      (∫ y : ℝ, |y| ^ 3 ∂η) =
        (σ⁻¹) ^ 3 * (∫ x : ℝ, |x| ^ 3 ∂ν) := by
  dsimp only
  have hσ : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hσsq : (Real.sqrt v) ^ 2 = v := Real.sq_sqrt hv.le
  obtain ⟨hId, hSq⟩ := lower_moments_integrable ν h3
  have hsecond' : (∫ x : ℝ, x ^ 2 ∂ν) = (Real.sqrt v) ^ 2 :=
    hsecond.trans hσsq.symm
  obtain ⟨hZ, hZsq, hZcube, hZmean, hZsecond, hZthird⟩ :=
    standardized_moments ν (fun x : ℝ => x) (Real.sqrt v) hσ
      hId hSq h3 hmean hsecond'
  have hg : Measurable (fun x : ℝ => x / Real.sqrt v) :=
    measurable_id.div_const (Real.sqrt v)
  have hηprob : IsProbabilityMeasure (ν.map (fun x : ℝ => x / Real.sqrt v)) :=
    (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).mpr inferInstance
  have hfId : AEStronglyMeasurable (fun y : ℝ => y)
      (ν.map (fun x : ℝ => x / Real.sqrt v)) :=
    measurable_id.aestronglyMeasurable
  have hfSq : AEStronglyMeasurable (fun y : ℝ => y ^ 2)
      (ν.map (fun x : ℝ => x / Real.sqrt v)) :=
    (by fun_prop : Measurable (fun y : ℝ => y ^ 2)).aestronglyMeasurable
  have hfCube : AEStronglyMeasurable (fun y : ℝ => |y| ^ 3)
      (ν.map (fun x : ℝ => x / Real.sqrt v)) :=
    (by fun_prop : Measurable (fun y : ℝ => |y| ^ 3)).aestronglyMeasurable
  have hηId : Integrable (fun y : ℝ => y)
      (ν.map (fun x : ℝ => x / Real.sqrt v)) :=
    (integrable_map_measure hfId hg.aemeasurable).mpr (by
      simpa only [Function.comp_def] using hZ)
  have hηSq : Integrable (fun y : ℝ => y ^ 2)
      (ν.map (fun x : ℝ => x / Real.sqrt v)) :=
    (integrable_map_measure hfSq hg.aemeasurable).mpr (by
      simpa only [Function.comp_def] using hZsq)
  have hηCube : Integrable (fun y : ℝ => |y| ^ 3)
      (ν.map (fun x : ℝ => x / Real.sqrt v)) :=
    (integrable_map_measure hfCube hg.aemeasurable).mpr (by
      simpa only [Function.comp_def] using hZcube)
  have hηmean :
      (∫ y : ℝ, y ∂(ν.map (fun x : ℝ => x / Real.sqrt v))) =
        ∫ x : ℝ, x / Real.sqrt v ∂ν :=
    integral_map hg.aemeasurable hηId.aestronglyMeasurable
  have hηsecond :
      (∫ y : ℝ, y ^ 2 ∂(ν.map (fun x : ℝ => x / Real.sqrt v))) =
        ∫ x : ℝ, (x / Real.sqrt v) ^ 2 ∂ν :=
    integral_map hg.aemeasurable hηSq.aestronglyMeasurable
  have hηthird :
      (∫ y : ℝ, |y| ^ 3 ∂(ν.map (fun x : ℝ => x / Real.sqrt v))) =
        ∫ x : ℝ, |x / Real.sqrt v| ^ 3 ∂ν :=
    integral_map hg.aemeasurable hηCube.aestronglyMeasurable
  exact ⟨hηprob, hηCube, hηmean.trans hZmean,
    hηsecond.trans hZsecond, hηthird.trans hZthird⟩

theorem iid_unitVariance_kernel_probability_inputs
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    1 ≤ (∫ x : ℝ, |x| ^ 3 ∂ν) ∧
      0 ≤ Real.sqrt 2 * Real.exp (6 + 3 * (1024 : ℝ)) ∧
      0 ≤ (2049 : ℝ) ∧
      iidOneSidedSurvival ν (∫ x : ℝ, |x| ^ 3 ∂ν)
        (Real.sqrt 2 * Real.exp (6 + 3 * (1024 : ℝ))) ∧
      iidIntervalConcentration ν (∫ x : ℝ, |x| ^ 3 ∂ν) (2049 : ℝ) := by
  have hSq := (lower_moments_integrable ν h3).2
  have hCDF : ∀ t : ℕ, 1 ≤ t → ∀ x : ℝ,
      |(Measure.pi (fun _ : Fin t => ν)).real
          {a | Shao.prefixSum a t / Real.sqrt (t : ℝ) ≤ x} - standardNormalCDF x| ≤
        (1024 : ℝ) * (∫ x : ℝ, |x| ^ 3 ∂ν) / Real.sqrt (t : ℝ) := by
    intro t ht x
    exact Shao.Probability.iid_unitVariance_berryEsseen ν h3 hmean hsecond t ht x
  have hSP : ∀ L : ℝ, 0 < L → ∀ s : ℝ, 0 < s → s < 1 →
      laplaceG (maxLaplaceMean ν L) s =
        Real.exp (laplaceW (endpointLaplaceMean ν L) s) := by
    intro L hL s hs0 hs1
    exact Shao.Probability.actual_maximum_spitzer_laplace ν hL hs0 hs1
  have hSPneg : ∀ L : ℝ, 0 < L → ∀ s : ℝ, 0 < s → s < 1 →
      laplaceG (maxLaplaceMean (reflectedLaw ν) L) s =
        Real.exp (laplaceW (endpointLaplaceMean (reflectedLaw ν) L) s) := by
    intro L hL s hs0 hs1
    exact Shao.Probability.actual_maximum_spitzer_laplace (reflectedLaw ν) hL hs0 hs1
  have hinputs := spitzer_kernel_probability_inputs ν hSq h3 hsecond
    (1024 : ℝ) (by norm_num) hCDF hSP hSPneg
  have hnumeric : (1 + 2 * (1024 : ℝ)) = (2049 : ℝ) := by norm_num
  simpa only [hnumeric] using hinputs

theorem varying_row_normalized_kernel_mass_tendsto
    (νSeq : ℕ → Measure ℝ) (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (NSeq : ℕ → ℕ) (hpos : ∀ j, 0 < hSeq j)
    (hinfty : Tendsto hSeq atTop atTop)
    (hlong : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 3)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j => @normalizedKernelMass (νSeq j) (hprob j) (hSeq j) (NSeq j) 0)
      atTop (𝓝 (4 / Real.pi)) := by
  have hinputs := fun j : ℕ =>
    @iid_unitVariance_kernel_probability_inputs (νSeq j) (hprob j)
      (h3 j) (hmean j) (hsecond j)
  exact TerminalNormalizedKernelLimit.varying_row_normalized_kernel_mass_tendsto
    νSeq hprob h3 hmean hsecond M hM
    (2049 : ℝ) (Real.sqrt 2 * Real.exp (6 + 3 * (1024 : ℝ)))
    (hinputs 0).2.2.1 (hinputs 0).2.1
    (fun j => (hinputs j).2.2.2.2) (fun j => (hinputs j).2.2.2.1)
    hSeq NSeq hpos hinfty hlong hshort

theorem varying_row_closedStrip_relative_asymptotic
    (νSeq : ℕ → Measure ℝ) (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (NSeq : ℕ → ℕ) (hpos : ∀ j, 0 < hSeq j)
    (hinfty : Tendsto hSeq atTop atTop)
    (hlong : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 3)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j =>
      (Measure.pi (fun _ : Fin (NSeq j) => νSeq j)).real
        (@Shao.closedStrip (NSeq j) (hSeq j)) /
          ((4 / Real.pi) * Real.exp (-lambda * (NSeq j : ℝ) / hSeq j ^ 2)))
      atTop (𝓝 (1 : ℝ)) := by
  have hinputs := fun j : ℕ =>
    @iid_unitVariance_kernel_probability_inputs (νSeq j) (hprob j)
      (h3 j) (hmean j) (hsecond j)
  exact TerminalNormalizedKernelLimit.varying_row_closedStrip_relative_asymptotic
    νSeq hprob h3 hmean hsecond M hM
    (2049 : ℝ) (Real.sqrt 2 * Real.exp (6 + 3 * (1024 : ℝ)))
    (hinputs 0).2.2.1 (hinputs 0).2.1
    (fun j => (hinputs j).2.2.2.2) (fun j => (hinputs j).2.2.2.1)
    hSeq NSeq hpos hinfty hlong hshort

theorem varying_row_variance_closedStrip_relative_asymptotic
    (νSeq : ℕ → Measure ℝ) (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (vSeq : ℕ → ℝ)
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = vSeq j)
    (hvlower : ∀ j, (1 / 2 : ℝ) ≤ vSeq j)
    (hvupper : ∀ j, vSeq j ≤ 2)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
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
  have hvpos (j : ℕ) : 0 < vSeq j := by linarith [hvlower j]
  have hmom := fun j : ℕ =>
    @standardized_law_unit_moments (νSeq j) (hprob j) (vSeq j) (hvpos j)
      (h3 j) (hmean j) (hsecond j)
  have hprobη : ∀ j, IsProbabilityMeasure (ηSeq j) := fun j => (hmom j).1
  have h3η : ∀ j, Integrable (fun y : ℝ => |y| ^ 3) (ηSeq j) :=
    fun j => (hmom j).2.1
  have hmeanη : ∀ j, (∫ y : ℝ, y ∂(ηSeq j)) = 0 := fun j => (hmom j).2.2.1
  have hsecondη : ∀ j, (∫ y : ℝ, y ^ 2 ∂(ηSeq j)) = 1 :=
    fun j => (hmom j).2.2.2.1
  have hinputs := fun j : ℕ =>
    @iid_unitVariance_kernel_probability_inputs (ηSeq j) (hprobη j)
      (h3η j) (hmeanη j) (hsecondη j)
  exact VarianceKernelAsymptotic.varying_row_variance_closedStrip_relative_asymptotic
    νSeq hprob vSeq h3 hmean hsecond hvlower hvupper M hM
    (2049 : ℝ) (Real.sqrt 2 * Real.exp (6 + 3 * (1024 : ℝ)))
    (hinputs 0).2.2.1 (hinputs 0).2.1
    (fun j => (hinputs j).2.2.2.2) (fun j => (hinputs j).2.2.2.1)
    hSeq NSeq hpos hinfty hlong hshort

end Shao.OQ4.UnconditionalKernelAsymptotic
end
