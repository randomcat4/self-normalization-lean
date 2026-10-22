import Shao.OQ5.P52.FixedLayerRealSample
import Shao.OQ5.P52.FixedLayerProjection

/-!
# Honest row integrals and the actual real first projection

The same real law transports pair L1 and L2 before Fubini. Each source
honest row is transported through the single-observation encoder before
identifying the actual real row integral. Decoder values off its image
remain arbitrary; the noise identity and bound have their exact AE scope.
-/

set_option autoImplicit false

open MeasureTheory Filter

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedObservationLaw_isProbabilityMeasure
attribute [local instance] fixedRealObservationLaw_isProbabilityMeasure

def fixedRealFirstProjection (x : ℝ) : ℝ :=
  ∫ y : ℝ, fixedRealKernel (x, y) ∂fixedRealObservationLaw

private theorem real_encoder_embedding :
    MeasurableEmbedding Shao.OQ5.P50.layerEncode :=
  measurableEmbedding_embeddingReal LayerObs

theorem measurable_fixedRealFirstProjection :
    Measurable fixedRealFirstProjection := by
  exact measurable_fixedRealKernel.stronglyMeasurable.integral_prod_right'.measurable

theorem fixedRealKernel_memLp (ν : ℝ) (hν : 1 ≤ ν) :
    MemLp fixedRealKernel (ENNReal.ofReal ν)
      (fixedRealObservationLaw.prod fixedRealObservationLaw) := by
  exact (Shao.OQ5.P50.layerRealKernel_memLp_iff fixedObservationLaw fixedKernel
    (ENNReal.ofReal ν)).mpr (fixedKernel_memLp ν hν)

theorem integrable_fixedRealKernel :
    Integrable fixedRealKernel
      (fixedRealObservationLaw.prod fixedRealObservationLaw) := by
  apply memLp_one_iff_integrable.mp
  simpa only [ENNReal.ofReal_one] using fixedRealKernel_memLp 1 (by norm_num)

theorem integrable_fixedRealKernel_sq :
    Integrable (fun z : ℝ × ℝ => fixedRealKernel z ^ 2)
      (fixedRealObservationLaw.prod fixedRealObservationLaw) := by
  have h2 : MemLp fixedRealKernel 2
      (fixedRealObservationLaw.prod fixedRealObservationLaw) := by
    simpa using fixedRealKernel_memLp 2 (by norm_num)
  exact h2.integrable_sq

theorem integrable_fixedRealKernel_row_ae :
    ∀ᵐ x : ℝ ∂fixedRealObservationLaw,
      Integrable (fun y : ℝ => fixedRealKernel (x, y)) fixedRealObservationLaw := by
  exact integrable_fixedRealKernel.prod_right_ae

theorem fixedRealFirstProjection_encode_ae :
    ∀ᵐ o : LayerObs ∂fixedObservationLaw,
      fixedRealFirstProjection (Shao.OQ5.P50.layerEncode o) = fixedFirstProjection o := by
  filter_upwards [integrable_fixedKernel_row_ae] with o ho
  have hcomp : (fun y : ℝ => fixedRealKernel (Shao.OQ5.P50.layerEncode o, y)) ∘
      Shao.OQ5.P50.layerEncode = (fun o' : LayerObs => fixedKernel (o, o')) := by
    funext o'
    exact fixedRealKernel_encode o o'
  have hr : Integrable (fun y : ℝ => fixedRealKernel (Shao.OQ5.P50.layerEncode o, y))
      fixedRealObservationLaw := by
    change Integrable (fun y : ℝ => fixedRealKernel (Shao.OQ5.P50.layerEncode o, y))
      (fixedObservationLaw.map Shao.OQ5.P50.layerEncode)
    apply real_encoder_embedding.integrable_map_iff.mpr
    rw [hcomp]
    exact ho
  unfold fixedRealFirstProjection fixedFirstProjection
  change (∫ y : ℝ, fixedRealKernel (Shao.OQ5.P50.layerEncode o, y)
    ∂fixedObservationLaw.map Shao.OQ5.P50.layerEncode) = _
  rw [integral_map Shao.OQ5.P50.measurable_layerEncode.aemeasurable
    hr.aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall fun o' => fixedRealKernel_encode o o')

theorem fixedRealFirstProjection_ae_eq_decoded_first :
    fixedRealFirstProjection =ᵐ[fixedRealObservationLaw]
      (fun x : ℝ => (Shao.OQ5.P50.layerDecode x).1) := by
  change ∀ᵐ x : ℝ ∂fixedObservationLaw.map Shao.OQ5.P50.layerEncode,
    fixedRealFirstProjection x = (Shao.OQ5.P50.layerDecode x).1
  apply (ae_map_iff Shao.OQ5.P50.measurable_layerEncode.aemeasurable
    (measurableSet_eq_fun measurable_fixedRealFirstProjection
      (measurable_fst.comp Shao.OQ5.P50.measurable_layerDecode))).mpr
  filter_upwards [fixedRealFirstProjection_encode_ae,
    fixedFirstProjection_ae_eq_first] with o ho hg
  change fixedRealFirstProjection (Shao.OQ5.P50.layerEncode o) =
    (Shao.OQ5.P50.layerDecode (Shao.OQ5.P50.layerEncode o)).1
  rw [Shao.OQ5.P50.layerDecode_encode]
  exact ho.trans hg

theorem integral_fixedRealKernel_eq_zero :
    (∫ z : ℝ × ℝ, fixedRealKernel z
      ∂fixedRealObservationLaw.prod fixedRealObservationLaw) = 0 := by
  have hpair := Shao.OQ5.P50.layerRealLaw_pair fixedObservationLaw
  change fixedRealObservationLaw.prod fixedRealObservationLaw =
    (fixedObservationLaw.prod fixedObservationLaw).map
      (Prod.map Shao.OQ5.P50.layerEncode Shao.OQ5.P50.layerEncode) at hpair
  have hm : Measurable (Prod.map Shao.OQ5.P50.layerEncode Shao.OQ5.P50.layerEncode) :=
    Shao.OQ5.P50.measurable_layerEncode.prodMap Shao.OQ5.P50.measurable_layerEncode
  have hI : Integrable fixedRealKernel
      ((fixedObservationLaw.prod fixedObservationLaw).map
        (Prod.map Shao.OQ5.P50.layerEncode Shao.OQ5.P50.layerEncode)) := by
    rw [← hpair]
    exact integrable_fixedRealKernel
  calc
    _ = ∫ z : LayerObs × LayerObs, fixedRealKernel
        (Prod.map Shao.OQ5.P50.layerEncode Shao.OQ5.P50.layerEncode z)
        ∂fixedObservationLaw.prod fixedObservationLaw := by
      rw [hpair]
      exact integral_map hm.aemeasurable hI.aestronglyMeasurable
    _ = ∫ z : LayerObs × LayerObs, fixedKernel z
        ∂fixedObservationLaw.prod fixedObservationLaw :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => fixedRealKernel_encode z.1 z.2)
    _ = 0 := integral_fixedKernel_eq_zero

theorem fixedRealFirstProjection_memLp_two :
    MemLp fixedRealFirstProjection 2 fixedRealObservationLaw := by
  change MemLp fixedRealFirstProjection 2
    (fixedObservationLaw.map Shao.OQ5.P50.layerEncode)
  apply real_encoder_embedding.memLp_map_measure_iff.mpr
  have heq : (fun o : LayerObs => fixedRealFirstProjection (Shao.OQ5.P50.layerEncode o))
      =ᵐ[fixedObservationLaw] fixedFirstProjection := fixedRealFirstProjection_encode_ae
  exact MemLp.ae_eq heq.symm fixedFirstProjection_memLp_two

theorem integrable_fixedRealFirstProjection :
    Integrable fixedRealFirstProjection fixedRealObservationLaw := by
  exact integrable_fixedRealKernel.integral_prod_left

theorem integrable_fixedRealFirstProjection_sq :
    Integrable (fun x : ℝ => fixedRealFirstProjection x ^ 2) fixedRealObservationLaw := by
  exact fixedRealFirstProjection_memLp_two.integrable_sq

theorem integral_fixedRealFirstProjection_eq_zero :
    (∫ x : ℝ, fixedRealFirstProjection x ∂fixedRealObservationLaw) = 0 := by
  change (∫ x : ℝ, ∫ y : ℝ, fixedRealKernel (x, y)
    ∂fixedRealObservationLaw ∂fixedRealObservationLaw) = 0
  rw [← integral_prod fixedRealKernel integrable_fixedRealKernel]
  exact integral_fixedRealKernel_eq_zero

theorem integral_fixedRealFirstProjection_sq :
    (∫ x : ℝ, fixedRealFirstProjection x ^ 2 ∂fixedRealObservationLaw) = (1 / 3 : ℝ) := by
  have hI := integrable_fixedRealFirstProjection_sq
  change (∫ x : ℝ, fixedRealFirstProjection x ^ 2
    ∂fixedObservationLaw.map Shao.OQ5.P50.layerEncode) = (1 / 3 : ℝ)
  rw [integral_map Shao.OQ5.P50.measurable_layerEncode.aemeasurable
    hI.aestronglyMeasurable]
  calc
    _ = ∫ o : LayerObs, fixedFirstProjection o ^ 2 ∂fixedObservationLaw := by
      apply integral_congr_ae
      filter_upwards [fixedRealFirstProjection_encode_ae] with o ho
      exact congrArg (fun t : ℝ => t ^ 2) ho
    _ = (1 / 3 : ℝ) := integral_fixedFirstProjection_sq

theorem map_fixedRealFirstProjection :
    fixedRealObservationLaw.map fixedRealFirstProjection = Shao.OQ5.P50.layerNoiseLaw := by
  calc
    _ = fixedRealObservationLaw.map (fun x : ℝ => (Shao.OQ5.P50.layerDecode x).1) :=
      Measure.map_congr fixedRealFirstProjection_ae_eq_decoded_first
    _ = (fixedRealObservationLaw.map Shao.OQ5.P50.layerDecode).map
        (Prod.fst : LayerObs → ℝ) := by
      rw [Measure.map_map measurable_fst Shao.OQ5.P50.measurable_layerDecode]
      rfl
    _ = fixedObservationLaw.map Prod.fst := by rw [fixedRealObservationLaw_decode]
    _ = Shao.OQ5.P50.layerNoiseLaw := map_fixedObservation_first

theorem fixedRealFirstProjection_abs_le_one_ae :
    ∀ᵐ x : ℝ ∂fixedRealObservationLaw, |fixedRealFirstProjection x| ≤ 1 := by
  have hs : ∀ᵐ y : ℝ ∂fixedRealObservationLaw.map fixedRealFirstProjection,
      y ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [map_fixedRealFirstProjection]
    exact Shao.OQ5.P50.layerNoiseLaw_ae_mem
  filter_upwards [ae_of_ae_map measurable_fixedRealFirstProjection.aemeasurable hs] with x hx
  exact abs_le.mpr hx

theorem fixedRealFirstProjection_indep_categories :
    ProbabilityTheory.IndepFun fixedRealFirstProjection
      (fun x : ℝ => (Shao.OQ5.P50.layerDecode x).2) fixedRealObservationLaw := by
  have hf : Measurable (fun x : ℝ => (Shao.OQ5.P50.layerDecode x).1) :=
    measurable_fst.comp Shao.OQ5.P50.measurable_layerDecode
  have hc : Measurable (fun x : ℝ => (Shao.OQ5.P50.layerDecode x).2) :=
    measurable_snd.comp Shao.OQ5.P50.measurable_layerDecode
  have hfm : fixedRealObservationLaw.map (fun x : ℝ => (Shao.OQ5.P50.layerDecode x).1) =
      fixedObservationLaw.map (Prod.fst : LayerObs → ℝ) := by
    calc
      _ = (fixedRealObservationLaw.map Shao.OQ5.P50.layerDecode).map
          (Prod.fst : LayerObs → ℝ) := by
        rw [Measure.map_map measurable_fst Shao.OQ5.P50.measurable_layerDecode]
        rfl
      _ = _ := by rw [fixedRealObservationLaw_decode]
  have hcm : fixedRealObservationLaw.map (fun x : ℝ => (Shao.OQ5.P50.layerDecode x).2) =
      fixedObservationLaw.map (Prod.snd : LayerObs → (ℕ → Fin 3)) := by
    calc
      _ = (fixedRealObservationLaw.map Shao.OQ5.P50.layerDecode).map
          (Prod.snd : LayerObs → (ℕ → Fin 3)) := by
        rw [Measure.map_map measurable_snd Shao.OQ5.P50.measurable_layerDecode]
        rfl
      _ = _ := by rw [fixedRealObservationLaw_decode]
  have hp : fixedObservationLaw =
      (fixedObservationLaw.map (Prod.fst : LayerObs → ℝ)).prod
        (fixedObservationLaw.map (Prod.snd : LayerObs → (ℕ → Fin 3))) := by
    have h := fixedObservation_first_indep_categories.map_prod_eq_prod_map_map
      measurable_fst.aemeasurable measurable_snd.aemeasurable
    have hid : (fun o : LayerObs => (o.1, o.2)) = id := by
      funext o
      rfl
    rw [hid, Measure.map_id] at h
    exact h
  have hi : ProbabilityTheory.IndepFun
      (fun x : ℝ => (Shao.OQ5.P50.layerDecode x).1)
      (fun x : ℝ => (Shao.OQ5.P50.layerDecode x).2) fixedRealObservationLaw := by
    apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      hf.aemeasurable hc.aemeasurable).mpr
    calc
      _ = fixedObservationLaw := by
        change fixedRealObservationLaw.map Shao.OQ5.P50.layerDecode = fixedObservationLaw
        exact fixedRealObservationLaw_decode
      _ = _ := hp
      _ = _ := by rw [hfm, hcm]
  exact hi.congr fixedRealFirstProjection_ae_eq_decoded_first.symm Filter.EventuallyEq.rfl

end
end Shao.OQ5.P52
