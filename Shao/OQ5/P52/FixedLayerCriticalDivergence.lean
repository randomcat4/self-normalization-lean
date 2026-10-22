import Shao.OQ5.P52.FixedLayerPairAABounds
import Shao.OQ5.P52.FixedLayerCriticalScales

/-!
# Genuine infinite critical exponential moment of the actual fixed kernel

Original-law events give lower bounds for one nonnegative Lebesgue integral.
Their real floors are unbounded; no sum of events or integral limit exchange
is used. Positivity then gives genuine failure of real integrability.
-/

set_option autoImplicit false

open MeasureTheory Filter

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedObservationLaw_isProbabilityMeasure

private theorem critical_radius_pos (j : ℕ) :
    0 < (fixedLayerN j : ℝ) ^ (5 / 3 : ℝ) / 4 := by
  have hN : (8 : ℝ) ≤ (fixedLayerN j : ℝ) := by
    exact_mod_cast fixedLayerN_ge_eight j
  exact div_pos (Real.rpow_pos_of_pos (by linarith) _) (by norm_num)

private theorem measurableSet_erased_small (j : ℕ) (b : ℝ) :
    MeasurableSet {z : LayerObs × LayerObs |
      |fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2)| ≤ b} := by
  have he : Measurable (fun z : LayerObs × LayerObs =>
      (fixedEraseLayer j z.1, fixedEraseLayer j z.2)) :=
    ((measurable_fixedEraseLayer j).comp measurable_fst).prodMk
      ((measurable_fixedEraseLayer j).comp measurable_snd)
  simpa only [Real.norm_eq_abs, Function.comp_apply] using
    measurableSet_le (measurable_fixedKernel.comp he).norm measurable_const

theorem fixedKernel_critical_lintegral_layer_lower_bound
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal
        ((1 / 2 : ℝ) * (fixedLayerP j) ^ 2 *
          Real.exp (lambda * (4 : ℝ) ^ (-1 / 5 : ℝ) *
            (fixedLayerN j : ℝ) ^ (1 / 3 : ℝ))) ≤
        ∫⁻ z : LayerObs × LayerObs,
          ENNReal.ofReal (Real.exp (lambda * |fixedKernel z| ^ (1 / 5 : ℝ)))
          ∂fixedObservationLaw.prod fixedObservationLaw := by
  classical
  let M := fixedObservationLaw.prod fixedObservationLaw
  let C : ℝ := 2 / 3 + ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2 ∂M
  let b : ℕ → ℝ := fun j => (fixedLayerN j : ℝ) ^ (5 / 3 : ℝ) / 4
  have hb2 : Tendsto (fun j : ℕ => (b j) ^ 2) atTop atTop := by
    simpa only [b] using
      fixedLayer_critical_radius_tendsto.atTop_pow₀ (by decide : (2 : ℕ) ≠ 0)
  have hratio : Tendsto (fun j : ℕ => C / (b j) ^ 2) atTop (nhds 0) :=
    hb2.const_div_atTop C
  have hevent : ∀ᶠ j : ℕ in atTop, C / (b j) ^ 2 ≤ 1 / 2 :=
    hratio.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hevent] with j hj
  let E : Set (LayerObs × LayerObs) := fixedLayerPairAAEvent j ∩
    {z | |fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2)| ≤ b j}
  have hE : MeasurableSet E :=
    (measurableSet_fixedLayerPairAAEvent j).inter (measurableSet_erased_small j (b j))
  have hhalf : (1 / 2 : ℝ) * (fixedLayerP j) ^ 2 ≤ M.real E := by
    have hfactor : (1 / 2 : ℝ) ≤ 1 - C / (b j) ^ 2 := by linarith
    calc
      _ = (fixedLayerP j) ^ 2 * (1 / 2 : ℝ) := mul_comm _ _
      _ ≤ (fixedLayerP j) ^ 2 * (1 - C / (b j) ^ 2) :=
        mul_le_mul_of_nonneg_left hfactor (sq_nonneg (fixedLayerP j))
      _ ≤ M.real E := fixedLayerPairAAEvent_background_small_original_probability
        j (b j) (critical_radius_pos j)
  let q : ℝ := Real.exp (lambda * (b j) ^ (1 / 5 : ℝ))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hfloor : ENNReal.ofReal q * M E ≤
      ∫⁻ z : LayerObs × LayerObs,
        ENNReal.ofReal (Real.exp (lambda * |fixedKernel z| ^ (1 / 5 : ℝ))) ∂M := by
    rw [← lintegral_indicator_const (μ := M) hE (ENNReal.ofReal q)]
    apply lintegral_mono_ae
    filter_upwards [fixedKernel_abs_ge_on_pairAA_background_small_ae j (b j)] with z hz
    by_cases hzE : z ∈ E
    · rw [Set.indicator_of_mem hzE]
      have hlarge : b j ≤ |fixedKernel z| := by
        have hker := hz hzE.1 hzE.2
        have hshift := fixedLayer_pairAA_shift_lower j
        dsimp only [b] at hker ⊢
        linarith
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (critical_radius_pos j).le hlarge (by norm_num)) hlambda.le))
    · rw [Set.indicator_of_notMem hzE]
      exact bot_le
  have hconv : ENNReal.ofReal (q * M.real E) = ENNReal.ofReal q * M E := by
    rw [measureReal_def, ENNReal.ofReal_mul hq0,
      ENNReal.ofReal_toReal (measure_ne_top M E)]
  have hq : q = Real.exp (lambda * (4 : ℝ) ^ (-1 / 5 : ℝ) *
      (fixedLayerN j : ℝ) ^ (1 / 3 : ℝ)) := by
    dsimp only [q, b]
    rw [fixedLayer_critical_radius_rpow]
    congr 1
    ring
  rw [← hq]
  calc
    _ ≤ ENNReal.ofReal (q * M.real E) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = q * ((1 / 2 : ℝ) * (fixedLayerP j) ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hhalf hq0
    _ = ENNReal.ofReal q * M E := hconv
    _ ≤ _ := hfloor

theorem lintegral_fixedKernel_critical_exp_eq_top
    (lambda : ℝ) (hlambda : 0 < lambda) :
    (∫⁻ z : LayerObs × LayerObs,
      ENNReal.ofReal (Real.exp (lambda * |fixedKernel z| ^ (1 / 5 : ℝ)))
      ∂fixedObservationLaw.prod fixedObservationLaw) = ⊤ := by
  let I := ∫⁻ z : LayerObs × LayerObs,
    ENNReal.ofReal (Real.exp (lambda * |fixedKernel z| ^ (1 / 5 : ℝ)))
    ∂fixedObservationLaw.prod fixedObservationLaw
  change I = ⊤
  by_contra hI
  have hbound : ∀ᶠ j : ℕ in atTop,
      (1 / 2 : ℝ) * (fixedLayerP j) ^ 2 *
        Real.exp (lambda * (4 : ℝ) ^ (-1 / 5 : ℝ) *
          (fixedLayerN j : ℝ) ^ (1 / 3 : ℝ)) ≤ I.toReal := by
    filter_upwards [fixedKernel_critical_lintegral_layer_lower_bound lambda hlambda] with j hj
    exact (ENNReal.ofReal_le_iff_le_toReal hI).mp hj
  have hgt := (fixedLayer_critical_mass_exp_tendsto lambda hlambda).eventually_gt_atTop I.toReal
  obtain ⟨j, hj, hjgt⟩ := (hbound.and hgt).exists
  exact (not_lt_of_ge hj) hjgt

theorem not_integrable_fixedKernel_critical_exp
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ¬ Integrable
      (fun z : LayerObs × LayerObs =>
        Real.exp (lambda * |fixedKernel z| ^ (1 / 5 : ℝ)))
      (fixedObservationLaw.prod fixedObservationLaw) := by
  intro hf
  have hfin := hf.hasFiniteIntegral
  change (∫⁻ z : LayerObs × LayerObs,
    ‖Real.exp (lambda * |fixedKernel z| ^ (1 / 5 : ℝ))‖ₑ
    ∂fixedObservationLaw.prod fixedObservationLaw) < ⊤ at hfin
  have heq : (∫⁻ z : LayerObs × LayerObs,
      ‖Real.exp (lambda * |fixedKernel z| ^ (1 / 5 : ℝ))‖ₑ
      ∂fixedObservationLaw.prod fixedObservationLaw) =
      ∫⁻ z : LayerObs × LayerObs,
        ENNReal.ofReal (Real.exp (lambda * |fixedKernel z| ^ (1 / 5 : ℝ)))
        ∂fixedObservationLaw.prod fixedObservationLaw :=
    lintegral_congr (fun _ => Real.enorm_of_nonneg (Real.exp_pos _).le)
  rw [heq, lintegral_fixedKernel_critical_exp_eq_top lambda hlambda] at hfin
  exact (lt_irrefl _) hfin

end
end Shao.OQ5.P52
