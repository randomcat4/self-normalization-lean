import Shao.OQ5.P52.FixedLayerModel
import Mathlib.Probability.Independence.InfinitePi

/-!
# One infinite iid sequence under the actual fixed p52 observation law

The entire sample law is fixed before the sample size. Coordinates and all
finite prefixes have the actual full observation laws, including the noise
and every categorical layer. Real Borel coding and rare events are separate.
-/

set_option autoImplicit false

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedObservationLaw_isProbabilityMeasure

def fixedSampleLaw : Measure (ℕ → LayerObs) :=
  Measure.infinitePi (fun _ : ℕ => fixedObservationLaw)

def fixedSampleCoordinate (i : ℕ) (ω : ℕ → LayerObs) : LayerObs := ω i

theorem fixedSampleLaw_isProbabilityMeasure :
    IsProbabilityMeasure fixedSampleLaw := by
  unfold fixedSampleLaw
  infer_instance

attribute [local instance] fixedSampleLaw_isProbabilityMeasure

theorem measurable_fixedSampleCoordinate (i : ℕ) :
    Measurable (fixedSampleCoordinate i) :=
  measurable_pi_apply i

theorem map_fixedSampleCoordinate (i : ℕ) :
    fixedSampleLaw.map (fixedSampleCoordinate i) = fixedObservationLaw := by
  exact Measure.infinitePi_map_eval (fun _ : ℕ => fixedObservationLaw) i

theorem iIndepFun_fixedSampleCoordinate :
    ProbabilityTheory.iIndepFun fixedSampleCoordinate fixedSampleLaw := by
  exact ProbabilityTheory.iIndepFun_infinitePi
    (P := fun _ : ℕ => fixedObservationLaw)
    (X := fun _ (o : LayerObs) => o) (fun _ => measurable_id)

theorem map_fixedSampleCoordinate_pair (i j : ℕ) (hij : i ≠ j) :
    fixedSampleLaw.map (fun ω => (fixedSampleCoordinate i ω, fixedSampleCoordinate j ω)) =
      fixedObservationLaw.prod fixedObservationLaw := by
  exact Measure.infinitePi_map_eval_prod (P := fun _ : ℕ => fixedObservationLaw) hij

theorem map_fixedSamplePrefix (n : ℕ) :
    fixedSampleLaw.map (fun ω (i : Fin n) => fixedSampleCoordinate i.val ω) =
      Measure.pi (fun _ : Fin n => fixedObservationLaw) := by
  have hi : ProbabilityTheory.iIndepFun
      (fun i : Fin n => fixedSampleCoordinate i.val) fixedSampleLaw :=
    ProbabilityTheory.iIndepFun.precomp Fin.val_injective iIndepFun_fixedSampleCoordinate
  simpa only [map_fixedSampleCoordinate] using
    ProbabilityTheory.iIndepFun.map_fun_eq_pi_map
      (fun i : Fin n => (measurable_fixedSampleCoordinate i.val).aemeasurable) hi

end
end Shao.OQ5.P52
