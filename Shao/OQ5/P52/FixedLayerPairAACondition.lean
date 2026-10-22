import Shao.OQ5.P52.FixedLayerErasedProjection
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The actual positive AA pair condition and its full erased background

The event restricts only the chosen category at both endpoints. Products of
normalized restrictions give its genuine joint background law. The full-kernel
identity remains almost everywhere under that actual positive condition.
-/

set_option autoImplicit false

open MeasureTheory Filter

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedObservationLaw_isProbabilityMeasure

def fixedLayerPairAAEvent (j : ℕ) : Set (LayerObs × LayerObs) :=
  {z | z.1.2 j = 1 ∧ z.2.2 j = 1}

private theorem category_A_measurable (j : ℕ) :
    MeasurableSet {o : LayerObs | o.2 j = 1} :=
  ((measurable_pi_apply j).comp measurable_snd) (measurableSet_singleton 1)

private theorem category_A_mass (j : ℕ) :
    fixedObservationLaw {o : LayerObs | o.2 j = 1} = ENNReal.ofReal (fixedLayerP j) := by
  have hm : Measurable (fun o : LayerObs => o.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  change fixedObservationLaw ((fun o : LayerObs => o.2 j) ⁻¹' {1}) = _
  rw [← Measure.map_apply hm (measurableSet_singleton 1),
    map_fixedObservation_category, Shao.OQ5.P50.layerMeasure_singleton]
  simp [Shao.OQ5.P50.layerWeight]

private theorem category_A_ne_zero (j : ℕ) :
    fixedObservationLaw {o : LayerObs | o.2 j = 1} ≠ 0 := by
  rw [category_A_mass]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (fixedLayerP_bounds j).1)

theorem measurableSet_fixedLayerPairAAEvent (j : ℕ) :
    MeasurableSet (fixedLayerPairAAEvent j) :=
  (category_A_measurable j).prod (category_A_measurable j)

private theorem pairAA_mass (j : ℕ) :
    (fixedObservationLaw.prod fixedObservationLaw) (fixedLayerPairAAEvent j) =
      ENNReal.ofReal (fixedLayerP j) * ENNReal.ofReal (fixedLayerP j) := by
  change (fixedObservationLaw.prod fixedObservationLaw)
    ({o : LayerObs | o.2 j = 1} ×ˢ {o : LayerObs | o.2 j = 1}) = _
  rw [Measure.prod_prod, category_A_mass]

theorem fixedLayerPairAAEvent_probability (j : ℕ) :
    (fixedObservationLaw.prod fixedObservationLaw).real (fixedLayerPairAAEvent j) =
      (fixedLayerP j) ^ 2 := by
  change ((fixedObservationLaw.prod fixedObservationLaw) (fixedLayerPairAAEvent j)).toReal = _
  rw [pairAA_mass, ENNReal.toReal_mul, ENNReal.toReal_ofReal (fixedLayerP_bounds j).1.le]
  exact (pow_two _).symm

theorem fixedLayerPairAAEvent_probability_pos (j : ℕ) :
    0 < (fixedObservationLaw.prod fixedObservationLaw).real (fixedLayerPairAAEvent j) := by
  rw [fixedLayerPairAAEvent_probability]
  exact pow_pos (fixedLayerP_bounds j).1 2

private theorem pairAA_ne_zero (j : ℕ) :
    (fixedObservationLaw.prod fixedObservationLaw) (fixedLayerPairAAEvent j) ≠ 0 := by
  rw [pairAA_mass]
  exact mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr (fixedLayerP_bounds j).1))
    (ne_of_gt (ENNReal.ofReal_pos.mpr (fixedLayerP_bounds j).1))

theorem fixedLayerPairAAEvent_cond_isProbabilityMeasure (j : ℕ) :
    IsProbabilityMeasure
      (ProbabilityTheory.cond (fixedObservationLaw.prod fixedObservationLaw)
        (fixedLayerPairAAEvent j)) :=
  ProbabilityTheory.cond_isProbabilityMeasure (pairAA_ne_zero j)

private theorem pairAA_cond_product (j : ℕ) :
    ProbabilityTheory.cond (fixedObservationLaw.prod fixedObservationLaw)
        (fixedLayerPairAAEvent j) =
      (ProbabilityTheory.cond fixedObservationLaw {o : LayerObs | o.2 j = 1}).prod
        (ProbabilityTheory.cond fixedObservationLaw {o : LayerObs | o.2 j = 1}) := by
  let S : Set LayerObs := {o | o.2 j = 1}
  have hm0 : fixedObservationLaw S ≠ 0 := category_A_ne_zero j
  have hmfin : fixedObservationLaw S ≠ ⊤ := measure_ne_top fixedObservationLaw S
  change ProbabilityTheory.cond (fixedObservationLaw.prod fixedObservationLaw) (S ×ˢ S) =
    (ProbabilityTheory.cond fixedObservationLaw S).prod
      (ProbabilityTheory.cond fixedObservationLaw S)
  unfold ProbabilityTheory.cond
  rw [Measure.prod_prod, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, Measure.prod_restrict, ENNReal.mul_inv (Or.inl hm0) (Or.inl hmfin)]

theorem map_fixedLayerPairAAEvent_cond_erasedPair (j : ℕ) :
    (ProbabilityTheory.cond (fixedObservationLaw.prod fixedObservationLaw)
      (fixedLayerPairAAEvent j)).map
      (fun z : LayerObs × LayerObs => (fixedEraseLayer j z.1, fixedEraseLayer j z.2)) =
      (fixedErasedLaw j).prod (fixedErasedLaw j) := by
  let ν := ProbabilityTheory.cond fixedObservationLaw {o : LayerObs | o.2 j = 1}
  let _ : IsProbabilityMeasure ν :=
    ProbabilityTheory.cond_isProbabilityMeasure (category_A_ne_zero j)
  rw [pairAA_cond_product]
  change (ν.prod ν).map (Prod.map (fixedEraseLayer j) (fixedEraseLayer j)) = _
  rw [← Measure.map_prod_map ν ν (measurable_fixedEraseLayer j) (measurable_fixedEraseLayer j)]
  change ((ProbabilityTheory.cond fixedObservationLaw {o : LayerObs | o.2 j = 1}).map
    (fixedEraseLayer j)).prod
    ((ProbabilityTheory.cond fixedObservationLaw {o : LayerObs | o.2 j = 1}).map
      (fixedEraseLayer j)) = _
  rw [map_cond_fixedObservation_fixedEraseLayer j 1]

theorem fixedKernel_ae_eq_erased_sub_on_pairAA (j : ℕ) :
    ∀ᵐ z : LayerObs × LayerObs
      ∂ProbabilityTheory.cond (fixedObservationLaw.prod fixedObservationLaw)
        (fixedLayerPairAAEvent j),
      fixedKernel z = fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2) -
        (((fixedLayerN j : ℝ) - 4) * fixedLayerT j) := by
  have hd : ∀ᵐ z : LayerObs × LayerObs
      ∂ProbabilityTheory.cond (fixedObservationLaw.prod fixedObservationLaw)
        (fixedLayerPairAAEvent j),
      fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2) =
        fixedKernel z - fixedLayerTerm j z :=
    Measure.AbsolutelyContinuous.ae_eq ProbabilityTheory.cond_absolutelyContinuous
      (fixedKernel_erase_pair_ae_eq_sub j)
  filter_upwards [hd, ProbabilityTheory.ae_cond_mem (measurableSet_fixedLayerPairAAEvent j)]
    with z hz hA
  change z.1.2 j = 1 ∧ z.2.2 j = 1 at hA
  have ht : fixedLayerTerm j z = -(((fixedLayerN j : ℝ) - 4) * fixedLayerT j) := by
    rw [fixedLayerTerm, hA.1, hA.2, Shao.OQ5.P50.layerKernel,
      ite_eq_right (by decide : (1 : Fin 3) ≠ 0), ite_eq_left rfl,
      ite_eq_right (by decide : (1 : Fin 3) ≠ 0), ite_eq_left rfl]
    exact neg_mul _ _
  rw [ht] at hz
  linarith

end
end Shao.OQ5.P52
