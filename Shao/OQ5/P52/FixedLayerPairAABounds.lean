import Shao.OQ5.P52.FixedLayerPairAACondition

/-!
# Actual AA background square bounds and original-law small-event mass

The full conditional erasure map transports genuine square integrability.
Markov controls the strict complement of background smallness; conditional
normalization then gives an original-law intersection bound. The final
kernel implication uses the original-law masked deletion identity directly.
-/

set_option autoImplicit false

open MeasureTheory Filter

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedObservationLaw_isProbabilityMeasure

private theorem measurable_erasedPair (j : ℕ) :
    Measurable (fun z : LayerObs × LayerObs =>
      (fixedEraseLayer j z.1, fixedEraseLayer j z.2)) :=
  ((measurable_fixedEraseLayer j).comp measurable_fst).prodMk
    ((measurable_fixedEraseLayer j).comp measurable_snd)

private theorem measurableSet_background_small (j : ℕ) (b : ℝ) :
    MeasurableSet {z : LayerObs × LayerObs |
      |fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2)| ≤ b} :=
  by
    simpa only [Real.norm_eq_abs, Function.comp_apply] using
      (measurableSet_le (measurable_fixedKernel.comp (measurable_erasedPair j)).norm
        measurable_const)

theorem integrable_fixedKernel_erasedPair_sq_cond_pairAA (j : ℕ) :
    Integrable
      (fun z : LayerObs × LayerObs =>
        (fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2)) ^ 2)
      (ProbabilityTheory.cond (fixedObservationLaw.prod fixedObservationLaw)
        (fixedLayerPairAAEvent j)) := by
  have hi : Integrable (fun z : LayerObs × LayerObs => (fixedKernel z) ^ 2)
      ((ProbabilityTheory.cond (fixedObservationLaw.prod fixedObservationLaw)
        (fixedLayerPairAAEvent j)).map
        (fun z : LayerObs × LayerObs => (fixedEraseLayer j z.1, fixedEraseLayer j z.2))) := by
    rw [map_fixedLayerPairAAEvent_cond_erasedPair]
    exact (fixedKernel_memLp_two_fixedErasedLaw j).integrable_sq
  exact (integrable_map_measure hi.aestronglyMeasurable
    (measurable_erasedPair j).aemeasurable).mp hi

theorem integral_fixedKernel_erasedPair_sq_cond_pairAA_le (j : ℕ) :
    (∫ z : LayerObs × LayerObs,
      (fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2)) ^ 2
      ∂ProbabilityTheory.cond (fixedObservationLaw.prod fixedObservationLaw)
        (fixedLayerPairAAEvent j)) ≤
      2 / 3 + ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw := by
  have hi : Integrable (fun z : LayerObs × LayerObs => (fixedKernel z) ^ 2)
      ((ProbabilityTheory.cond (fixedObservationLaw.prod fixedObservationLaw)
        (fixedLayerPairAAEvent j)).map
        (fun z : LayerObs × LayerObs => (fixedEraseLayer j z.1, fixedEraseLayer j z.2))) := by
    rw [map_fixedLayerPairAAEvent_cond_erasedPair]
    exact (fixedKernel_memLp_two_fixedErasedLaw j).integrable_sq
  calc
    _ = ∫ z : LayerObs × LayerObs, (fixedKernel z) ^ 2
        ∂(ProbabilityTheory.cond (fixedObservationLaw.prod fixedObservationLaw)
          (fixedLayerPairAAEvent j)).map
          (fun z : LayerObs × LayerObs => (fixedEraseLayer j z.1, fixedEraseLayer j z.2)) :=
      (integral_map (measurable_erasedPair j).aemeasurable hi.aestronglyMeasurable).symm
    _ = ∫ z : LayerObs × LayerObs, (fixedKernel z) ^ 2
        ∂(fixedErasedLaw j).prod (fixedErasedLaw j) := by
      rw [map_fixedLayerPairAAEvent_cond_erasedPair]
    _ ≤ _ := integral_fixedKernel_sq_fixedErasedLaw_le j

theorem fixedLayerPairAAEvent_background_small_probability
    (j : ℕ) (b : ℝ) (hb : 0 < b) :
    1 - (2 / 3 + ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
      ∂fixedObservationLaw.prod fixedObservationLaw) / b ^ 2 ≤
      (ProbabilityTheory.cond (fixedObservationLaw.prod fixedObservationLaw)
        (fixedLayerPairAAEvent j)).real
        {z : LayerObs × LayerObs |
          |fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2)| ≤ b} := by
  let ν := ProbabilityTheory.cond (fixedObservationLaw.prod fixedObservationLaw)
    (fixedLayerPairAAEvent j)
  let _ : IsProbabilityMeasure ν := fixedLayerPairAAEvent_cond_isProbabilityMeasure j
  let F : LayerObs × LayerObs → ℝ :=
    fun z => fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2)
  let B : Set (LayerObs × LayerObs) := {z | |F z| ≤ b}
  have hB : MeasurableSet B := measurableSet_background_small j b
  have hb2 : 0 < b ^ 2 := pow_pos hb 2
  have hsub : Bᶜ ⊆ {z | b ^ 2 ≤ (F z) ^ 2} := by
    intro z hz
    change b ^ 2 ≤ (F z) ^ 2
    have hgt : b < |F z| := lt_of_not_ge hz
    have hsq := (sq_le_sq₀ hb.le (abs_nonneg (F z))).mpr hgt.le
    simpa only [sq_abs] using hsq
  have hmono : ν.real Bᶜ ≤ ν.real {z | b ^ 2 ≤ (F z) ^ 2} :=
    measureReal_mono hsub
  have hMarkov : b ^ 2 * ν.real {z | b ^ 2 ≤ (F z) ^ 2} ≤
      ∫ z, (F z) ^ 2 ∂ν :=
    mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall (fun z => sq_nonneg (F z)))
      (integrable_fixedKernel_erasedPair_sq_cond_pairAA j) (b ^ 2)
  have hbound : b ^ 2 * ν.real Bᶜ ≤
      2 / 3 + ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw :=
    (mul_le_mul_of_nonneg_left hmono hb2.le).trans
      (hMarkov.trans (integral_fixedKernel_erasedPair_sq_cond_pairAA_le j))
  have hdiv : ν.real Bᶜ ≤
      (2 / 3 + ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw) / b ^ 2 :=
    (le_div_iff₀ hb2).mpr (by simpa only [mul_comm] using hbound)
  have hcompl : ν.real Bᶜ = 1 - ν.real B := probReal_compl_eq_one_sub hB
  change 1 - _ / b ^ 2 ≤ ν.real B
  linarith

theorem fixedLayerPairAAEvent_background_small_original_probability
    (j : ℕ) (b : ℝ) (hb : 0 < b) :
    (fixedLayerP j) ^ 2 *
      (1 - (2 / 3 + ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw) / b ^ 2) ≤
      (fixedObservationLaw.prod fixedObservationLaw).real
        (fixedLayerPairAAEvent j ∩
          {z : LayerObs × LayerObs |
            |fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2)| ≤ b}) := by
  let μ := fixedObservationLaw.prod fixedObservationLaw
  let ν := ProbabilityTheory.cond μ (fixedLayerPairAAEvent j)
  let _ : IsProbabilityMeasure ν := fixedLayerPairAAEvent_cond_isProbabilityMeasure j
  let B : Set (LayerObs × LayerObs) :=
    {z | |fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2)| ≤ b}
  have hmass : ν.real B * μ.real (fixedLayerPairAAEvent j) =
      μ.real (fixedLayerPairAAEvent j ∩ B) := by
    have he := congrArg ENNReal.toReal
      (ProbabilityTheory.cond_mul_eq_inter (measurableSet_fixedLayerPairAAEvent j) B μ)
    simpa only [ν, Measure.real, ENNReal.toReal_mul] using he
  have hmul := mul_le_mul_of_nonneg_left
    (fixedLayerPairAAEvent_background_small_probability j b hb)
    (sq_nonneg (fixedLayerP j))
  rw [fixedLayerPairAAEvent_probability] at hmass
  change (fixedLayerP j) ^ 2 * (1 - _ / b ^ 2) ≤ μ.real (fixedLayerPairAAEvent j ∩ B)
  calc
    _ ≤ (fixedLayerP j) ^ 2 * ν.real B := hmul
    _ = μ.real (fixedLayerPairAAEvent j ∩ B) := by
      rw [mul_comm]
      exact hmass

theorem fixedKernel_abs_ge_on_pairAA_background_small_ae (j : ℕ) (b : ℝ) :
    ∀ᵐ z : LayerObs × LayerObs ∂fixedObservationLaw.prod fixedObservationLaw,
      z ∈ fixedLayerPairAAEvent j →
        |fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2)| ≤ b →
          (((fixedLayerN j : ℝ) - 4) * fixedLayerT j) - b ≤ |fixedKernel z| := by
  filter_upwards [fixedKernel_erase_pair_ae_eq_sub j] with z hz
  intro hA hsmall
  change z.1.2 j = 1 ∧ z.2.2 j = 1 at hA
  have ht : fixedLayerTerm j z = -(((fixedLayerN j : ℝ) - 4) * fixedLayerT j) := by
    rw [fixedLayerTerm, hA.1, hA.2, Shao.OQ5.P50.layerKernel,
      ite_eq_right (by decide : (1 : Fin 3) ≠ 0), ite_eq_left rfl,
      ite_eq_right (by decide : (1 : Fin 3) ≠ 0), ite_eq_left rfl]
    exact neg_mul _ _
  rw [ht] at hz
  have htri := abs_sub (fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2))
    (fixedKernel z)
  have he : fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2) - fixedKernel z =
      ((fixedLayerN j : ℝ) - 4) * fixedLayerT j := by linarith
  rw [he] at htri
  have hle := le_abs_self (((fixedLayerN j : ℝ) - 4) * fixedLayerT j)
  linarith

end
end Shao.OQ5.P52
