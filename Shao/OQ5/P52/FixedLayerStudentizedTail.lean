import Shao.OQ5.P52.FixedLayerConditionalConcentration
import Shao.OQ5.P52.FixedLayerTailScales

/-!
# The original Studentized statistic and its tail transfer

Finite Borel algebra retains the original full masked kernel and true root.
Positive pointwise division transfers the actual good event, and the exact
conditional-mass identity transfers the resulting lower bound to the SAME
original infinite sample law without an independence assumption.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

def fixedSampleStudentized {n : ℕ} (x : Fin n → LayerObs) : ℝ :=
  Real.sqrt (n : ℝ) * fixedSampleU x / fixedSampleStudentizer x

def fixedSampleStudentizedTailProbability (n : ℕ) (x : ℝ) : ℝ :=
  fixedSampleLaw.real
    {ω : ℕ → LayerObs |
      x ≤ fixedSampleStudentized
        (fun i : Fin n => fixedSampleCoordinate i.val ω)}

private theorem measurable_sample_U (n : ℕ) :
    Measurable (fun x : Fin n → LayerObs => fixedSampleU x) := by
  classical
  unfold fixedSampleU Shao.OQ6.FiniteRows.uStatistic Shao.OQ5.P35.unorderedPairSum
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro k _
  by_cases hik : i < k
  · simpa only [ite_eq_left hik, Function.comp_def] using
      measurable_fixedKernel.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply k))
  · simp only [ite_eq_right hik]
    exact measurable_const

private theorem measurable_sample_row (n : ℕ) (i : Fin n) :
    Measurable (fun x : Fin n → LayerObs =>
      Shao.OQ6.FiniteRows.rowMean (fun a b => fixedKernel (x a, x b)) i) := by
  classical
  unfold Shao.OQ6.FiniteRows.rowMean
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro k _
  exact measurable_fixedKernel.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply k))

private theorem measurable_sample_square (n : ℕ) :
    Measurable (fun x : Fin n → LayerObs => fixedSampleStudentizerSq x) := by
  unfold fixedSampleStudentizerSq Shao.OQ6.FiniteRows.jackknifeSq
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_sample_row n i).sub (measurable_sample_U n)).pow_const 2

private theorem real_N_gt_one (j : ℕ) : (1 : ℝ) < fixedLayerN j := by
  have h : (8 : ℝ) ≤ fixedLayerN j := by exact_mod_cast fixedLayerN_ge_eight j
  linarith

private theorem rare_cond_probability (j : ℕ) :
    IsProbabilityMeasure (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) :=
  fixedLayerExactEvent_cond_isProbabilityMeasure j (fixedLayerN j) 2
    (le_trans (by norm_num : 2 ≤ 8) (fixedLayerN_ge_eight j))

attribute [local instance] rare_cond_probability fixedSampleLaw_isProbabilityMeasure

theorem measurable_fixedSampleStudentized (n : ℕ) :
    Measurable (fun x : Fin n → LayerObs => fixedSampleStudentized x) := by
  exact ((measurable_sample_U n).const_mul (Real.sqrt (n : ℝ))).div
    (measurable_sample_square n).sqrt

theorem measurable_fixedSampleStudentized_sample (n : ℕ) :
    Measurable (fun ω : ℕ → LayerObs =>
      fixedSampleStudentized (fun i : Fin n => fixedSampleCoordinate i.val ω)) := by
  exact (measurable_fixedSampleStudentized n).comp
    (Measurable.of_eval (fun i => measurable_fixedSampleCoordinate i.val))

theorem fixedSampleStudentizedTailProbability_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ fixedSampleStudentizedTailProbability n x := by
  exact ENNReal.toReal_nonneg

theorem fixedSampleStudentizedTailProbability_le_one (n : ℕ) (x : ℝ) :
    fixedSampleStudentizedTailProbability n x ≤ 1 := by
  exact measureReal_le_one

theorem fixedSampleStudentized_ge_fixedLayerTailThreshold_of_good
    (j : ℕ) (x : Fin (fixedLayerN j) → LayerObs)
    (hU : (fixedLayerN j : ℝ) ^ (1 / 6 : ℝ) ≤
      Real.sqrt (fixedLayerN j : ℝ) * fixedSampleU x)
    (hR : 0 < fixedSampleStudentizer x)
    (hlog : fixedSampleStudentizer x ≤ Real.log (fixedLayerN j : ℝ)) :
    fixedLayerTailThreshold (fixedLayerN j) ≤ fixedSampleStudentized x := by
  have hL : 0 < Real.log (fixedLayerN j : ℝ) := Real.log_pos (real_N_gt_one j)
  have ha : 0 ≤ (fixedLayerN j : ℝ) ^ (1 / 6 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  change (fixedLayerN j : ℝ) ^ (1 / 6 : ℝ) / Real.log (fixedLayerN j : ℝ) ≤
    (Real.sqrt (fixedLayerN j : ℝ) * fixedSampleU x) / fixedSampleStudentizer x
  calc
    _ ≤ (fixedLayerN j : ℝ) ^ (1 / 6 : ℝ) / fixedSampleStudentizer x :=
      div_le_div_of_nonneg_left ha hR hlog
    _ ≤ _ := (div_le_div_iff_of_pos_right hR).mpr hU

theorem fixedLayerRareEvent_cond_studentized_tail_probability_lower (j : ℕ) :
    1 - ((4 / 3 : ℝ) + 4 *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂fixedObservationLaw.prod fixedObservationLaw)) *
        ((fixedLayerN j : ℝ) ^ (-1 / 3 : ℝ) +
          1 / (Real.log (fixedLayerN j : ℝ)) ^ 2) ≤
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)).real
        {ω : ℕ → LayerObs |
          fixedLayerTailThreshold (fixedLayerN j) ≤
            fixedSampleStudentized
              (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)} := by
  apply (fixedLayerRareEvent_cond_good_probability_lower j).trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  exact fixedSampleStudentized_ge_fixedLayerTailThreshold_of_good j _ hω.1 hω.2.1 hω.2.2

theorem fixedSampleStudentizedTailProbability_ge_fixedLayerRareEvent_mul (j : ℕ) :
    fixedSampleLaw.real (fixedLayerRareEvent j) *
      (1 - ((4 / 3 : ℝ) + 4 *
          (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
            ∂fixedObservationLaw.prod fixedObservationLaw)) *
          ((fixedLayerN j : ℝ) ^ (-1 / 3 : ℝ) +
            1 / (Real.log (fixedLayerN j : ℝ)) ^ 2)) ≤
      fixedSampleStudentizedTailProbability
        (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j)) := by
  let E := fixedLayerRareEvent j
  let A : Set (ℕ → LayerObs) := {ω | fixedLayerTailThreshold (fixedLayerN j) ≤
    fixedSampleStudentized (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)}
  have hE : MeasurableSet E := measurableSet_fixedLayerExactEvent j (fixedLayerN j) 2
  have _hA : MeasurableSet A :=
    measurableSet_le measurable_const (measurable_fixedSampleStudentized_sample (fixedLayerN j))
  have hmass : fixedSampleLaw.real E *
      (ProbabilityTheory.cond fixedSampleLaw E).real A = fixedSampleLaw.real (E ∩ A) := by
    have h := congrArg ENNReal.toReal
      (ProbabilityTheory.cond_mul_eq_inter hE A fixedSampleLaw)
    change ((ProbabilityTheory.cond fixedSampleLaw E) A * fixedSampleLaw E).toReal =
      (fixedSampleLaw (E ∩ A)).toReal at h
    rw [ENNReal.toReal_mul] at h
    simpa only [Measure.real, mul_comm] using h
  have hm := mul_le_mul_of_nonneg_left
    (fixedLayerRareEvent_cond_studentized_tail_probability_lower j)
    (show 0 ≤ fixedSampleLaw.real E from ENNReal.toReal_nonneg)
  calc
    _ ≤ fixedSampleLaw.real E * (ProbabilityTheory.cond fixedSampleLaw E).real A := hm
    _ = fixedSampleLaw.real (E ∩ A) := hmass
    _ ≤ fixedSampleLaw.real A := measureReal_mono Set.inter_subset_right
    _ = _ := rfl

end
end Shao.OQ5.P52
