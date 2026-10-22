import Shao.OQ5.P52.LayeredKernelVersion
import Shao.OQ5.P50.LayeredPairLaw

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

/-- The single source observation law, fixed before every exponent and sample size. -/
def fixedObservationLaw : Measure LayerObs :=
  Shao.OQ5.P50.layerObservationLaw fixedLayerP fixedLayerQ

private theorem fixedP_nonneg (j : ℕ) : 0 ≤ fixedLayerP j :=
  (fixedLayerP_bounds j).1.le

private theorem fixedQ_nonneg (j : ℕ) : 0 ≤ fixedLayerQ j :=
  (fixedLayerQ_bounds j).1.le

private theorem fixedPQ_le_one (j : ℕ) : fixedLayerP j + fixedLayerQ j ≤ 1 :=
  (fixedLayerP_add_Q_lt_one j).le

theorem fixedObservationLaw_isProbabilityMeasure :
    IsProbabilityMeasure fixedObservationLaw := by
  exact Shao.OQ5.P50.layerObservationLaw_isProbabilityMeasure fixedLayerP fixedLayerQ fixedP_nonneg fixedQ_nonneg fixedPQ_le_one

attribute [local instance] fixedObservationLaw_isProbabilityMeasure

theorem map_fixedObservation_first :
    fixedObservationLaw.map Prod.fst = Shao.OQ5.P50.layerNoiseLaw := by
  exact Shao.OQ5.P50.map_layerObservation_first fixedLayerP fixedLayerQ fixedP_nonneg fixedQ_nonneg fixedPQ_le_one

theorem map_fixedObservation_categories :
    fixedObservationLaw.map Prod.snd =
      Shao.OQ5.P50.layerCategoryProductLaw fixedLayerP fixedLayerQ := by
  exact Shao.OQ5.P50.map_layerObservation_categories fixedLayerP fixedLayerQ fixedP_nonneg fixedQ_nonneg fixedPQ_le_one

theorem map_fixedObservation_category (j : ℕ) :
    fixedObservationLaw.map (fun o => o.2 j) =
      Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j) := by
  exact Shao.OQ5.P50.map_layerObservation_category fixedLayerP fixedLayerQ fixedP_nonneg fixedQ_nonneg fixedPQ_le_one j

theorem fixedObservation_first_ae_mem :
    ∀ᵐ o ∂fixedObservationLaw, o.1 ∈ Set.Icc (-1 : ℝ) 1 := by
  exact Shao.OQ5.P50.layerObservation_first_ae_mem fixedLayerP fixedLayerQ fixedP_nonneg fixedQ_nonneg fixedPQ_le_one

theorem fixedObservation_first_indep_categories :
    ProbabilityTheory.IndepFun Prod.fst Prod.snd fixedObservationLaw := by
  exact Shao.OQ5.P50.layerObservation_first_indep_categories fixedLayerP fixedLayerQ fixedP_nonneg fixedQ_nonneg fixedPQ_le_one

theorem integrable_fixedLayerTerm_row (j : ℕ) (o : LayerObs) :
    Integrable (fun o' : LayerObs => fixedLayerTerm j (o, o')) fixedObservationLaw := by
  let f : Fin 3 → ℝ := fun b => Shao.OQ5.P50.layerKernel
    (fixedLayerN j) (fixedLayerT j) (fixedLayerP j) (fixedLayerQ j) (o.2 j) b
  have hI : Integrable f (Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j)) :=
    Shao.OQ5.P50.integrable_layerMeasure _ _ f
  have hI' : Integrable f (fixedObservationLaw.map (fun o' : LayerObs => o'.2 j)) := by
    rw [map_fixedObservation_category]
    exact hI
  exact hI'.comp_measurable ((measurable_pi_apply j).comp measurable_snd)

theorem integral_fixedLayerTerm_row_zero (j : ℕ) (o : LayerObs) :
    (∫ o' : LayerObs, fixedLayerTerm j (o, o') ∂fixedObservationLaw) = 0 := by
  let f : Fin 3 → ℝ := fun b => Shao.OQ5.P50.layerKernel
    (fixedLayerN j) (fixedLayerT j) (fixedLayerP j) (fixedLayerQ j) (o.2 j) b
  have hm : Measurable (fun o' : LayerObs => o'.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  have hf : AEStronglyMeasurable f (fixedObservationLaw.map (fun o' : LayerObs => o'.2 j)) :=
    (measurable_of_finite f).aestronglyMeasurable
  calc
    _ = ∫ b, f b ∂fixedObservationLaw.map (fun o' : LayerObs => o'.2 j) :=
      (integral_map hm.aemeasurable hf).symm
    _ = 0 := by
      rw [map_fixedObservation_category]
      exact Shao.OQ5.P50.integral_layerKernel_row_zero _ _ _ _
        (fixedP_nonneg j) (fixedQ_nonneg j) (fixedPQ_le_one j)
        (ne_of_gt (fixedLayerQ_bounds j).1) (o.2 j)

theorem fixedLayerTerm_memLp_two (j : ℕ) :
    MemLp (fixedLayerTerm j) 2 (fixedObservationLaw.prod fixedObservationLaw) := by
  have hm : Measurable (fun z : LayerObs × LayerObs => (z.1.2 j, z.2.2 j)) :=
    ((measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))
  have hpair := Shao.OQ5.P50.map_layerObservation_pair_category
    fixedLayerP fixedLayerQ fixedP_nonneg fixedQ_nonneg fixedPQ_le_one j
  change (fixedObservationLaw.prod fixedObservationLaw).map
    (fun z : LayerObs × LayerObs => (z.1.2 j, z.2.2 j)) = _ at hpair
  have hI := Shao.OQ5.P50.layerKernel_memLp_two
    (fixedLayerN j) (fixedLayerT j) (fixedLayerP j) (fixedLayerQ j)
  rw [← hpair] at hI
  exact hI.comp_of_map hm.aemeasurable

theorem iIndepFun_fixedLayerTerms :
    ProbabilityTheory.iIndepFun (fun j => fixedLayerTerm j)
      (fixedObservationLaw.prod fixedObservationLaw) := by
  have h := Shao.OQ5.P50.iIndepFun_layerObservation_pair_categories
    fixedLayerP fixedLayerQ fixedP_nonneg fixedQ_nonneg fixedPQ_le_one
  exact h.comp (fun j (s : Fin 3 × Fin 3) => Shao.OQ5.P50.layerKernel
    (fixedLayerN j) (fixedLayerT j) (fixedLayerP j) (fixedLayerQ j) s.1 s.2)
    (fun _ => measurable_of_finite _)

end
end Shao.OQ5.P52
