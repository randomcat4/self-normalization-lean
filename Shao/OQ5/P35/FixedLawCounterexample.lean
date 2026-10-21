import Shao.OQ5.P35.ResidualOperator
import Shao.OQ5.P35.DominationFailure
import Shao.OQ5.P35.TailLimits

/-!
# The full original p35 fixed-law Studentized counterexample

Source: original p35 sections1-7 and the source-bound root contract.
All witnesses are the actual previously constructed fixed objects. This
certificate adds no probabilistic or asymptotic premise. It makes no OQ6,
p52/p53 or historical novelty claim.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- The complete original p35 contract, for the once-fixed actual witnesses. -/
def FixedLawCounterexample : Prop :=
  (IsProbabilityMeasure realLaw) ∧
  (IsProbabilityMeasure sampleLaw) ∧
  (∀ i : ℕ, Measurable (sampleCoordinate i)) ∧
  (∀ i : ℕ, Measure.map (sampleCoordinate i) sampleLaw = realLaw) ∧
  (iIndepFun sampleCoordinate sampleLaw) ∧
  (Measurable (fun xy : ℝ × ℝ => populationKernel xy.1 xy.2)) ∧
  (∀ x y : ℝ, populationKernel x y = populationKernel y x) ∧
  (Integrable (fun xy : ℝ × ℝ => populationKernel xy.1 xy.2) (realLaw.prod realLaw)) ∧
  (Integrable (fun xy : ℝ × ℝ => populationKernel xy.1 xy.2 ^ 2) (realLaw.prod realLaw)) ∧
  ((∫ xy : ℝ × ℝ, populationKernel xy.1 xy.2 ∂realLaw.prod realLaw) = populationMean) ∧
  (∀ x : ℝ, Integrable (populationKernel x) realLaw ∧
      ((∫ y, populationKernel x y ∂realLaw) - populationMean = populationProjection x)) ∧
  (Integrable populationProjection realLaw) ∧
  ((∫ x, populationProjection x ∂realLaw) = 0) ∧
  (Integrable (fun x => populationProjection x ^ 2) realLaw) ∧
  (0 < (∫ x, populationProjection x ^ 2 ∂realLaw)) ∧
  (Integrable (fun x => |populationProjection x| ^ 3) realLaw) ∧
  (Integrable observationFeature realLaw) ∧
  ((∫ x, observationFeature x ∂realLaw) = 0) ∧
  (Integrable (fun x => observationFeature x ^ 2) realLaw) ∧
  ((∫ x, observationFeature x ^ 2 ∂realLaw) = featureVariance) ∧
  (0 < featureVariance) ∧
  (∀ x y : ℝ, populationResidual x y = populationKernel x y - populationMean - populationProjection x - populationProjection y) ∧
  (∀ x : ℝ, Integrable (populationResidual x) realLaw ∧ (∫ y, populationResidual x y ∂realLaw) = 0) ∧
  (∀ f : ObservationL2,
      (∀ x : ℝ, Integrable (fun y => populationResidual x y * f y) realLaw) ∧
      ((residualOperator f : ℝ → ℝ) =ᵐ[realLaw] fun x => ∫ y, populationResidual x y * f y ∂realLaw)) ∧
  (LinearMap.range residualOperator.toLinearMap = Submodule.span ℝ ({featureL2} : Set ObservationL2)) ∧
  (residualOperator.toLinearMap.rank = 1) ∧
  ({lam : ℝ | lam ≠ 0 ∧ Module.End.HasEigenvalue residualOperator.toLinearMap lam} = {(-featureVariance)}) ∧
  (∀ c0 : ℝ, 0 < c0 → 0 < (realLaw.prod realLaw) (dominationFailureEvent c0)) ∧
  (∀ n : ℕ, 3 ≤ n → sampleLaw {ω | 0 < sampleStudentizer n ω} = 1) ∧
  (Tendsto counterexampleThreshold atTop atTop) ∧
  (Tendsto (fun n : ℕ => counterexampleThreshold n / (n : ℝ) ^ (1 / 6 : ℝ)) atTop (nhds 0)) ∧
  (Tendsto (fun n : ℕ => counterexampleThreshold n / Real.sqrt (n : ℝ)) atTop (nhds 0)) ∧
  (StrictMono rareSampleSize) ∧
  (Tendsto rareSampleSize atTop atTop) ∧
  (Tendsto (fun j : ℕ => Real.log (p35TailProbability (rareSampleSize j)) /
      (-(counterexampleThreshold (rareSampleSize j) ^ 2) / 2)) atTop (nhds 0)) ∧
  (Tendsto (fun j : ℕ => p35TailProbability (rareSampleSize j) /
      standardNormalUpperTail (counterexampleThreshold (rareSampleSize j))) atTop atTop) ∧
  (¬ Tendsto (fun n : ℕ => Real.log (p35TailProbability n) /
      (-(counterexampleThreshold n ^ 2) / 2)) atTop (nhds 1)) ∧
  (Tendsto (fun n : ℕ => counterexampleWindow n / (n : ℝ) ^ (1 / 6 : ℝ)) atTop (nhds 0)) ∧
  (∀ n : ℕ, 1 ≤ n → 0 ≤ counterexampleThreshold n ∧ counterexampleThreshold n < counterexampleWindow n) ∧
  (¬ (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ t : ℝ, 0 ≤ t → t < counterexampleWindow n →
        |sampleLaw.real {ω | t ≤ sampleStatistic n ω} / standardNormalUpperTail t - 1| ≤ ε))

/-- Every clause of the original p35 counterexample holds for these fixed witnesses. -/
theorem fixedLawCounterexample : FixedLawCounterexample := by
  unfold FixedLawCounterexample
  refine ⟨inferInstance, inferInstance, measurable_sampleCoordinate,
    map_sampleCoordinate, iIndepFun_sampleCoordinate, measurable_populationKernel,
    populationKernel_symmetric, integrable_populationKernel,
    integrable_populationKernel_sq, integral_populationKernel, ?_,
    integrable_populationProjection, integral_populationProjection,
    integrable_populationProjection_sq, integral_populationProjection_sq_pos,
    integrable_populationProjection_abs_cube, integrable_observationFeature,
    integral_observationFeature, integrable_observationFeature_sq,
    integral_observationFeature_sq, featureVariance_pos, ?_, ?_, ?_,
    residualOperator_range, residualOperator_rank, residualOperator_nonzero_eigenvalues,
    measure_dominationFailureEvent_pos, measure_sampleStudentizer_pos,
    counterexampleThreshold_tendsto, counterexampleThreshold_div_sixth_tendsto_zero,
    counterexampleThreshold_div_sqrt_tendsto_zero, strictMono_rareSampleSize,
    rareSampleSize_tendsto, p35LogTailRatio_tendsto_zero,
    p35RelativeTailRatio_tendsto_atTop, p35LogTailRatio_not_tendsto_one,
    counterexampleWindow_div_sixth_tendsto_zero, counterexampleThreshold_mem_window,
    p35WindowUniformApproximation_false⟩
  · intro x
    refine ⟨integrable_populationKernel_right x, ?_⟩
    rw [integral_populationKernel_right]
    ring
  · intro x y
    exact (populationResidual_decomposition x y).symm
  · intro x
    exact ⟨integrable_populationResidual_right x, integral_populationResidual_right x⟩
  · intro f
    exact ⟨integrable_residual_mul_Lp_right f, residualOperator_apply_ae f⟩

end

end Shao.OQ5.P35
