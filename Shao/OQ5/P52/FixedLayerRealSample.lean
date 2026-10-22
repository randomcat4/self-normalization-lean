import Shao.OQ5.P52.FixedLayerSample
import Shao.OQ5.P50.LayeredRealTransport

/-!
# The fixed real population and its entire original iid sample

The coordinatewise Borel encoding retains the full observation and every
sample position. Its global measurable decoder recovers the entire original
sample law. Finite sample statistics and population moments are separate.
-/

set_option autoImplicit false

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedObservationLaw_isProbabilityMeasure
attribute [local instance] fixedSampleLaw_isProbabilityMeasure

def fixedRealObservationLaw : Measure ℝ :=
  Shao.OQ5.P50.layerRealLaw fixedObservationLaw

def fixedRealKernel : ℝ × ℝ → ℝ :=
  Shao.OQ5.P50.layerRealKernel fixedKernel

def fixedRealSampleLaw : Measure (ℕ → ℝ) :=
  fixedSampleLaw.map
    (fun ω : ℕ → LayerObs => fun i : ℕ => Shao.OQ5.P50.layerEncode (ω i))

def fixedRealSampleCoordinate (i : ℕ) (ξ : ℕ → ℝ) : ℝ := ξ i

theorem fixedRealObservationLaw_isProbabilityMeasure :
    IsProbabilityMeasure fixedRealObservationLaw :=
  Shao.OQ5.P50.layerRealLaw_isProbabilityMeasure fixedObservationLaw

attribute [local instance] fixedRealObservationLaw_isProbabilityMeasure

theorem measurable_fixedRealKernel : Measurable fixedRealKernel :=
  Shao.OQ5.P50.measurable_layerRealKernel fixedKernel measurable_fixedKernel

theorem fixedRealKernel_symmetric (x y : ℝ) :
    fixedRealKernel (x, y) = fixedRealKernel (y, x) :=
  Shao.OQ5.P50.layerRealKernel_symmetric fixedKernel fixedKernel_symmetric x y

theorem fixedRealKernel_encode (o o' : LayerObs) :
    fixedRealKernel
      (Shao.OQ5.P50.layerEncode o, Shao.OQ5.P50.layerEncode o') =
        fixedKernel (o, o') :=
  Shao.OQ5.P50.layerRealKernel_encode fixedKernel o o'

theorem fixedRealObservationLaw_decode :
    fixedRealObservationLaw.map Shao.OQ5.P50.layerDecode = fixedObservationLaw :=
  Shao.OQ5.P50.layerRealLaw_decode fixedObservationLaw

private theorem real_sample_infinitePi :
    fixedRealSampleLaw = Measure.infinitePi (fun _ : ℕ => fixedRealObservationLaw) := by
  change (Measure.infinitePi (fun _ : ℕ => fixedObservationLaw)).map
    (fun ω : ℕ → LayerObs => fun i : ℕ => Shao.OQ5.P50.layerEncode (ω i)) = _
  exact Measure.infinitePi_map_pi (fun _ : ℕ => fixedObservationLaw)
    (fun _ => Shao.OQ5.P50.measurable_layerEncode)

theorem fixedRealSampleLaw_isProbabilityMeasure :
    IsProbabilityMeasure fixedRealSampleLaw := by
  rw [real_sample_infinitePi]
  infer_instance

attribute [local instance] fixedRealSampleLaw_isProbabilityMeasure

theorem measurable_fixedRealSampleCoordinate (i : ℕ) :
    Measurable (fixedRealSampleCoordinate i) :=
  measurable_pi_apply i

theorem map_fixedRealSampleCoordinate (i : ℕ) :
    fixedRealSampleLaw.map (fixedRealSampleCoordinate i) = fixedRealObservationLaw := by
  rw [real_sample_infinitePi]
  exact Measure.infinitePi_map_eval (fun _ : ℕ => fixedRealObservationLaw) i

theorem iIndepFun_fixedRealSampleCoordinate :
    ProbabilityTheory.iIndepFun fixedRealSampleCoordinate fixedRealSampleLaw := by
  rw [real_sample_infinitePi]
  exact ProbabilityTheory.iIndepFun_infinitePi
    (P := fun _ : ℕ => fixedRealObservationLaw)
    (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)

theorem map_fixedRealSampleCoordinate_pair (i j : ℕ) (hij : i ≠ j) :
    fixedRealSampleLaw.map
      (fun ξ => (fixedRealSampleCoordinate i ξ, fixedRealSampleCoordinate j ξ)) =
        fixedRealObservationLaw.prod fixedRealObservationLaw := by
  rw [real_sample_infinitePi]
  exact Measure.infinitePi_map_eval_prod (P := fun _ : ℕ => fixedRealObservationLaw) hij

theorem map_fixedRealSamplePrefix (n : ℕ) :
    fixedRealSampleLaw.map
      (fun ξ (i : Fin n) => fixedRealSampleCoordinate i.val ξ) =
        Measure.pi (fun _ : Fin n => fixedRealObservationLaw) := by
  have hi : ProbabilityTheory.iIndepFun
      (fun i : Fin n => fixedRealSampleCoordinate i.val) fixedRealSampleLaw :=
    ProbabilityTheory.iIndepFun.precomp Fin.val_injective iIndepFun_fixedRealSampleCoordinate
  simpa only [map_fixedRealSampleCoordinate] using
    ProbabilityTheory.iIndepFun.map_fun_eq_pi_map
      (fun i : Fin n => (measurable_fixedRealSampleCoordinate i.val).aemeasurable) hi

theorem fixedRealSampleLaw_decode :
    fixedRealSampleLaw.map
      (fun ξ : ℕ → ℝ => fun i : ℕ => Shao.OQ5.P50.layerDecode (ξ i)) =
        fixedSampleLaw := by
  unfold fixedRealSampleLaw
  have hdec : Measurable
      (fun ξ : ℕ → ℝ => fun i : ℕ => Shao.OQ5.P50.layerDecode (ξ i)) := by
    exact Measurable.of_eval (fun i =>
      Shao.OQ5.P50.measurable_layerDecode.comp (measurable_pi_apply i))
  have henc : Measurable
      (fun ω : ℕ → LayerObs => fun i : ℕ => Shao.OQ5.P50.layerEncode (ω i)) := by
    exact Measurable.of_eval (fun i =>
      Shao.OQ5.P50.measurable_layerEncode.comp (measurable_pi_apply i))
  rw [Measure.map_map hdec henc]
  have hcomp :
      (fun ξ : ℕ → ℝ => fun i : ℕ => Shao.OQ5.P50.layerDecode (ξ i)) ∘
        (fun ω : ℕ → LayerObs => fun i : ℕ => Shao.OQ5.P50.layerEncode (ω i)) = id := by
    funext ω i
    exact Shao.OQ5.P50.layerDecode_encode (ω i)
  rw [hcomp, Measure.map_id]

theorem fixedRealSampleLaw_ae_image :
    ∀ᵐ ξ ∂fixedRealSampleLaw,
      ∀ i : ℕ, ξ i ∈ Shao.OQ5.P50.layerEncodedSet := by
  rw [ae_all_iff]
  intro i
  have h : ∀ᵐ x ∂fixedRealSampleLaw.map (fixedRealSampleCoordinate i),
      x ∈ Shao.OQ5.P50.layerEncodedSet := by
    rw [map_fixedRealSampleCoordinate]
    exact Shao.OQ5.P50.layerRealLaw_ae_image fixedObservationLaw
  exact ae_of_ae_map (measurable_fixedRealSampleCoordinate i).aemeasurable h

end
end Shao.OQ5.P52
