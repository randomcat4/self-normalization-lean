import Shao.OQ5.P52.FixedLayerRareEvents
import Shao.Probability.ConditionalIID

/-!
# The actual conditional joint law at fixed categorical target positions

Positivity is derived from the actual fixed-position probability. The whole
observation prefix under its genuine normalized restriction has the product
of the corresponding whole-observation conditional marginal laws.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedSampleLaw_isProbabilityMeasure

theorem fixedLayerPositionEvent_probability_pos (j n : ℕ) (J : Finset (Fin n)) :
    0 < fixedSampleLaw.real (fixedLayerPositionEvent j n J) := by
  rw [fixedLayerPositionEvent_probability]
  have hp : 0 < fixedLayerP j := (fixedLayerP_bounds j).1
  have hzero : 0 < 1 - fixedLayerP j - fixedLayerQ j := by
    linarith [fixedLayerP_add_Q_lt_one j]
  exact mul_pos (pow_pos hp _) (pow_pos hzero _)

private theorem position_event_ne_zero (j n : ℕ) (J : Finset (Fin n)) :
    fixedSampleLaw (fixedLayerPositionEvent j n J) ≠ 0 := by
  intro hz
  have he : fixedSampleLaw.real (fixedLayerPositionEvent j n J) = 0 := by
    change (fixedSampleLaw (fixedLayerPositionEvent j n J)).toReal = 0
    rw [hz]
    rfl
  exact (ne_of_gt (fixedLayerPositionEvent_probability_pos j n J)) he

theorem fixedLayerPositionEvent_cond_isProbabilityMeasure
    (j n : ℕ) (J : Finset (Fin n)) :
    IsProbabilityMeasure (ProbabilityTheory.cond fixedSampleLaw (fixedLayerPositionEvent j n J)) :=
  ProbabilityTheory.cond_isProbabilityMeasure (position_event_ne_zero j n J)

private theorem position_event_eq_joint (j n : ℕ) (J : Finset (Fin n)) :
    fixedLayerPositionEvent j n J =
      ⋂ i : Fin n, (fixedSampleCoordinate i.val) ⁻¹'
        (if i ∈ J then {o : LayerObs | o.2 j = 1} else {o : LayerObs | o.2 j = 0}) := by
  ext ω
  simp only [fixedLayerPositionEvent, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  apply forall_congr'
  intro i
  by_cases hi : i ∈ J <;> simp [hi, fixedSampleCategory]

theorem map_fixedLayerPositionEvent_cond_prefix
    (j n : ℕ) (J : Finset (Fin n)) :
    (ProbabilityTheory.cond fixedSampleLaw (fixedLayerPositionEvent j n J)).map
      (fun ω (i : Fin n) => fixedSampleCoordinate i.val ω) =
      Measure.pi (fun i : Fin n =>
        if i ∈ J then ProbabilityTheory.cond fixedObservationLaw {o : LayerObs | o.2 j = 1}
        else ProbabilityTheory.cond fixedObservationLaw {o : LayerObs | o.2 j = 0}) := by
  let B : Fin n → Set LayerObs := fun i =>
    if i ∈ J then {o : LayerObs | o.2 j = 1} else {o : LayerObs | o.2 j = 0}
  have hcat : Measurable (fun o : LayerObs => o.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  have hB (i : Fin n) : MeasurableSet (B i) := by
    by_cases hi : i ∈ J
    · simpa only [B, hi, ite_true] using
        measurableSet_eq_fun hcat
          (measurable_const : Measurable (fun _ : LayerObs => (1 : Fin 3)))
    · simpa only [B, hi, ite_false] using
        measurableSet_eq_fun hcat
          (measurable_const : Measurable (fun _ : LayerObs => (0 : Fin 3)))
  have hi : iIndepFun (fun i : Fin n => fixedSampleCoordinate i.val) fixedSampleLaw :=
    iIndepFun.precomp Fin.val_injective iIndepFun_fixedSampleCoordinate
  have he : fixedLayerPositionEvent j n J =
      ⋂ i : Fin n, (fixedSampleCoordinate i.val) ⁻¹' B i := position_event_eq_joint j n J
  have hnz : fixedSampleLaw (⋂ i : Fin n, (fixedSampleCoordinate i.val) ⁻¹' B i) ≠ 0 := by
    rw [← he]
    exact position_event_ne_zero j n J
  calc
    _ = Measure.pi (fun i : Fin n =>
        ProbabilityTheory.cond (fixedSampleLaw.map (fixedSampleCoordinate i.val)) (B i)) := by
      rw [he]
      exact Shao.Probability.indep_cond_joint_map_eq_pi
        (fun i : Fin n => measurable_fixedSampleCoordinate i.val) hi B hB hnz
    _ = _ := by
      congr 1
      funext i
      rw [map_fixedSampleCoordinate]
      by_cases hiJ : i ∈ J <;> simp only [B, hiJ, ite_true, ite_false]

end
end Shao.OQ5.P52
