import Shao.OQ5.P52.FixedLayerConditionalLaw
import Shao.OQ5.P52.FixedLayerErasureLaw
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The actual erased finite prefix under fixed-position conditioning

Coordinatewise erasure transports the actual full observation-vector laws.
Every pushed conditional factor is the same genuine erased observation law;
the resulting statement concerns precisely the observed finite prefix.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedObservationLaw_isProbabilityMeasure
attribute [local instance] fixedErasedLaw_isProbabilityMeasure

private theorem measurable_observation_prefix (n : ℕ) :
    Measurable (fun ω (i : Fin n) => fixedSampleCoordinate i.val ω) :=
  measurable_pi_iff.mpr (fun i => measurable_fixedSampleCoordinate i.val)

private theorem measurable_erasure_vector (j n : ℕ) :
    Measurable (fun (x : Fin n → LayerObs) (i : Fin n) => fixedEraseLayer j (x i)) :=
  measurable_pi_iff.mpr (fun i =>
    (measurable_fixedEraseLayer j).comp (measurable_pi_apply i))

theorem map_fixedSamplePrefix_erase (j n : ℕ) :
    fixedSampleLaw.map
      (fun ω (i : Fin n) => fixedEraseLayer j (fixedSampleCoordinate i.val ω)) =
      Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
  let _ : ∀ _i : Fin n,
      SigmaFinite (fixedObservationLaw.map (fixedEraseLayer j)) :=
    fun _ => by change SigmaFinite (fixedErasedLaw j); infer_instance
  calc
    _ = (fixedSampleLaw.map
        (fun ω (i : Fin n) => fixedSampleCoordinate i.val ω)).map
        (fun (x : Fin n → LayerObs) (i : Fin n) => fixedEraseLayer j (x i)) := by
      rw [Measure.map_map (measurable_erasure_vector j n) (measurable_observation_prefix n)]
      rfl
    _ = (Measure.pi (fun _ : Fin n => fixedObservationLaw)).map
        (fun (x : Fin n → LayerObs) (i : Fin n) => fixedEraseLayer j (x i)) := by
      rw [map_fixedSamplePrefix]
    _ = Measure.pi (fun _ : Fin n => fixedErasedLaw j) :=
      Measure.pi_map_pi (μ := fun _ : Fin n => fixedObservationLaw)
        (f := fun _ => fixedEraseLayer j)
        (fun _ => (measurable_fixedEraseLayer j).aemeasurable)

theorem map_fixedLayerPositionEvent_cond_erasedPrefix
    (j n : ℕ) (J : Finset (Fin n)) :
    (ProbabilityTheory.cond fixedSampleLaw (fixedLayerPositionEvent j n J)).map
      (fun ω (i : Fin n) => fixedEraseLayer j (fixedSampleCoordinate i.val ω)) =
      Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
  let ν : Fin n → Measure LayerObs := fun i =>
    if i ∈ J then ProbabilityTheory.cond fixedObservationLaw {o : LayerObs | o.2 j = 1}
    else ProbabilityTheory.cond fixedObservationLaw {o : LayerObs | o.2 j = 0}
  have hν (i : Fin n) : (ν i).map (fixedEraseLayer j) = fixedErasedLaw j := by
    by_cases hi : i ∈ J
    · simpa only [ν, hi, ite_true] using map_cond_fixedObservation_fixedEraseLayer j 1
    · simpa only [ν, hi, ite_false] using map_cond_fixedObservation_fixedEraseLayer j 0
  let _ : ∀ i : Fin n, SigmaFinite ((ν i).map (fixedEraseLayer j)) :=
    fun i => by rw [hν i]; infer_instance
  calc
    _ = ((ProbabilityTheory.cond fixedSampleLaw (fixedLayerPositionEvent j n J)).map
        (fun ω (i : Fin n) => fixedSampleCoordinate i.val ω)).map
        (fun (x : Fin n → LayerObs) (i : Fin n) => fixedEraseLayer j (x i)) := by
      rw [Measure.map_map (measurable_erasure_vector j n) (measurable_observation_prefix n)]
      rfl
    _ = (Measure.pi ν).map
        (fun (x : Fin n → LayerObs) (i : Fin n) => fixedEraseLayer j (x i)) := by
      rw [map_fixedLayerPositionEvent_cond_prefix]
    _ = Measure.pi (fun i : Fin n => (ν i).map (fixedEraseLayer j)) :=
      Measure.pi_map_pi (μ := ν) (f := fun _ => fixedEraseLayer j)
        (fun _ => (measurable_fixedEraseLayer j).aemeasurable)
    _ = Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
      simp only [hν]

theorem map_fixedLayerPositionEvent_cond_erasedCoordinate
    (j n : ℕ) (J : Finset (Fin n)) (i : Fin n) :
    (ProbabilityTheory.cond fixedSampleLaw (fixedLayerPositionEvent j n J)).map
      (fun ω => fixedEraseLayer j (fixedSampleCoordinate i.val ω)) = fixedErasedLaw j := by
  have hp : Measurable
      (fun ω (k : Fin n) => fixedEraseLayer j (fixedSampleCoordinate k.val ω)) :=
    measurable_pi_iff.mpr (fun k =>
      (measurable_fixedEraseLayer j).comp (measurable_fixedSampleCoordinate k.val))
  calc
    _ = ((ProbabilityTheory.cond fixedSampleLaw (fixedLayerPositionEvent j n J)).map
        (fun ω (k : Fin n) => fixedEraseLayer j (fixedSampleCoordinate k.val ω))).map
        (Function.eval i) := by
      rw [Measure.map_map (measurable_pi_apply i) hp]
      rfl
    _ = (Measure.pi (fun _ : Fin n => fixedErasedLaw j)).map (Function.eval i) := by
      rw [map_fixedLayerPositionEvent_cond_erasedPrefix]
    _ = fixedErasedLaw j :=
      (measurePreserving_eval (μ := fun _ : Fin n => fixedErasedLaw j) i).map_eq

theorem iIndepFun_fixedLayerPositionEvent_cond_erasedPrefix
    (j n : ℕ) (J : Finset (Fin n)) :
    iIndepFun (fun i : Fin n =>
      fun ω => fixedEraseLayer j (fixedSampleCoordinate i.val ω))
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerPositionEvent j n J)) := by
  let _ := fixedLayerPositionEvent_cond_isProbabilityMeasure j n J
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (f := fun i : Fin n => fun ω => fixedEraseLayer j (fixedSampleCoordinate i.val ω))
    (fun i => ((measurable_fixedEraseLayer j).comp
      (measurable_fixedSampleCoordinate i.val)).aemeasurable)).mpr
  simpa only [map_fixedLayerPositionEvent_cond_erasedCoordinate] using
    map_fixedLayerPositionEvent_cond_erasedPrefix j n J

end
end Shao.OQ5.P52
