import Shao.OQ5.P52.FixedLayerErasureLaw
import Shao.OQ5.P52.FixedObservationNoiseMoments
import Mathlib.Probability.IdentDistrib

/-!
# Actual noise moments and full independence under the erased law

Erasure keeps the real noise coordinate. Its honest scalar distribution
transports integrability and moments, while the actual product pushforward
retains joint independence from the entire erased category sequence.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem map_fixedErasedLaw_first (j : ℕ) :
    (fixedErasedLaw j).map Prod.fst = Shao.OQ5.P50.layerNoiseLaw := by
  change (fixedObservationLaw.map (fixedEraseLayer j)).map Prod.fst = _
  rw [Measure.map_map measurable_fst (measurable_fixedEraseLayer j)]
  exact map_fixedObservation_first

private theorem fixedFirst_identDistrib_erased (j : ℕ) :
    IdentDistrib (Prod.fst : LayerObs → ℝ) (Prod.fst : LayerObs → ℝ)
      fixedObservationLaw (fixedErasedLaw j) := by
  refine ⟨measurable_fst.aemeasurable, measurable_fst.aemeasurable, ?_⟩
  rw [map_fixedObservation_first, map_fixedErasedLaw_first]

theorem integrable_fixedErasedLaw_first (j : ℕ) :
    Integrable (fun o : LayerObs => o.1) (fixedErasedLaw j) :=
  (fixedFirst_identDistrib_erased j).integrable_snd integrable_fixedObservation_first

theorem integral_fixedErasedLaw_first_eq_zero (j : ℕ) :
    (∫ o : LayerObs, o.1 ∂fixedErasedLaw j) = 0 := by
  calc
    _ = ∫ o : LayerObs, o.1 ∂fixedObservationLaw :=
      (fixedFirst_identDistrib_erased j).integral_eq.symm
    _ = 0 := integral_fixedObservation_first_eq_zero

theorem integrable_fixedErasedLaw_first_sq (j : ℕ) :
    Integrable (fun o : LayerObs => o.1 ^ 2) (fixedErasedLaw j) := by
  have h := (fixedFirst_identDistrib_erased j).comp (continuous_id.pow 2).measurable
  exact h.integrable_snd integrable_fixedObservation_first_sq

theorem integral_fixedErasedLaw_first_sq (j : ℕ) :
    (∫ o : LayerObs, o.1 ^ 2 ∂fixedErasedLaw j) = 1 / 3 := by
  have h := (fixedFirst_identDistrib_erased j).comp (continuous_id.pow 2).measurable
  calc
    _ = ∫ o : LayerObs, o.1 ^ 2 ∂fixedObservationLaw := h.integral_eq.symm
    _ = 1 / 3 := integral_fixedObservation_first_sq

theorem fixedErasedLaw_first_indep_categories (j : ℕ) :
    IndepFun Prod.fst Prod.snd (fixedErasedLaw j) := by
  let γ := Shao.OQ5.P50.layerNoiseLaw
  let ν := Shao.OQ5.P50.layerCategoryProductLaw fixedLayerP fixedLayerQ
  let e : (ℕ → Fin 3) → (ℕ → Fin 3) := fun s k => if k = j then 0 else s k
  let _ := Shao.OQ5.P50.layerNoiseLaw_isProbabilityMeasure
  let _ := Shao.OQ5.P50.layerCategoryProductLaw_isProbabilityMeasure
    fixedLayerP fixedLayerQ (fun k => (fixedLayerP_bounds k).1.le)
    (fun k => (fixedLayerQ_bounds k).1.le)
    (fun k => (fixedLayerP_add_Q_lt_one k).le)
  have he : Measurable e := by
    apply measurable_pi_iff.mpr
    intro k
    by_cases hk : k = j
    · simpa only [e, ite_eq_left hk] using
        (measurable_const : Measurable (fun _ : ℕ → Fin 3 => (0 : Fin 3)))
    · simpa only [e, ite_eq_right hk] using
        (measurable_pi_apply k : Measurable (fun s : ℕ → Fin 3 => s k))
  let _ : IsProbabilityMeasure (ν.map e) :=
    (Measure.isProbabilityMeasure_map_iff he.aemeasurable).mpr inferInstance
  have hβ : fixedErasedLaw j = γ.prod (ν.map e) := by
    change (γ.prod ν).map (Prod.map id e) = γ.prod (ν.map e)
    rw [← Measure.map_prod_map γ ν measurable_id he, Measure.map_id]
  rw [hβ]
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

end
end Shao.OQ5.P52
