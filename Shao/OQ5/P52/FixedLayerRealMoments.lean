import Shao.OQ5.P52.FixedLayerRealProjection
import Shao.OQ5.P52.FixedLayerCriticalDivergence

/-!
# Polynomial and exponential moments of the same actual real kernel

Transport through the actual pair pushforward preserves exp(0) = 1.
The critical nonnegative integral is transported without an L1 assumption.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedObservationLaw_isProbabilityMeasure
attribute [local instance] fixedRealObservationLaw_isProbabilityMeasure

private theorem real_pair_encoder_embedding :
    MeasurableEmbedding
      (Prod.map Shao.OQ5.P50.layerEncode Shao.OQ5.P50.layerEncode) :=
  (measurableEmbedding_embeddingReal LayerObs).prodMap
    (measurableEmbedding_embeddingReal LayerObs)

private theorem real_pair_law :
    fixedRealObservationLaw.prod fixedRealObservationLaw =
      (fixedObservationLaw.prod fixedObservationLaw).map
        (Prod.map Shao.OQ5.P50.layerEncode Shao.OQ5.P50.layerEncode) :=
  Shao.OQ5.P50.layerRealLaw_pair fixedObservationLaw

theorem integrable_fixedRealKernel_abs_pow (m : ℕ) :
    Integrable (fun z : ℝ × ℝ => |fixedRealKernel z| ^ m)
      (fixedRealObservationLaw.prod fixedRealObservationLaw) := by
  by_cases hm : m = 0
  · subst m
    simpa only [pow_zero] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ × ℝ => (1 : ℝ))
        (fixedRealObservationLaw.prod fixedRealObservationLaw))
  · have hm1 : 1 ≤ (m : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    have hp : MemLp fixedRealKernel (m : ℝ≥0∞)
        (fixedRealObservationLaw.prod fixedRealObservationLaw) := by
      simpa only [ENNReal.ofReal_natCast] using fixedRealKernel_memLp (m : ℝ) hm1
    simpa only [Real.norm_eq_abs] using hp.integrable_norm_pow hm

theorem integrable_fixedRealKernel_subcritical_exp (η lambda : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 5) (hlambda : 0 < lambda) :
    Integrable (fun z : ℝ × ℝ => Real.exp (lambda * |fixedRealKernel z| ^ η))
      (fixedRealObservationLaw.prod fixedRealObservationLaw) := by
  rw [real_pair_law]
  apply real_pair_encoder_embedding.integrable_map_iff.mpr
  have hc :
      (fun z : ℝ × ℝ => Real.exp (lambda * |fixedRealKernel z| ^ η)) ∘
        Prod.map Shao.OQ5.P50.layerEncode Shao.OQ5.P50.layerEncode =
      (fun z : LayerObs × LayerObs => Real.exp (lambda * |fixedKernel z| ^ η)) := by
    funext z
    change Real.exp (lambda * |fixedRealKernel
      (Shao.OQ5.P50.layerEncode z.1, Shao.OQ5.P50.layerEncode z.2)| ^ η) = _
    rw [fixedRealKernel_encode]
  rw [hc]
  exact integrable_fixedKernelExp η lambda hη0 hη hlambda

theorem lintegral_fixedRealKernel_critical_exp_eq_top
    (lambda : ℝ) (hlambda : 0 < lambda) :
    (∫⁻ z : ℝ × ℝ,
      ENNReal.ofReal (Real.exp (lambda * |fixedRealKernel z| ^ (1 / 5 : ℝ)))
      ∂fixedRealObservationLaw.prod fixedRealObservationLaw) = ⊤ := by
  rw [real_pair_law, real_pair_encoder_embedding.lintegral_map]
  calc
    _ = ∫⁻ z : LayerObs × LayerObs,
        ENNReal.ofReal (Real.exp (lambda * |fixedKernel z| ^ (1 / 5 : ℝ)))
        ∂fixedObservationLaw.prod fixedObservationLaw := by
      apply lintegral_congr
      intro z
      change ENNReal.ofReal (Real.exp (lambda * |fixedRealKernel
        (Shao.OQ5.P50.layerEncode z.1, Shao.OQ5.P50.layerEncode z.2)| ^
          (1 / 5 : ℝ))) = _
      rw [fixedRealKernel_encode]
    _ = ⊤ := lintegral_fixedKernel_critical_exp_eq_top lambda hlambda

theorem not_integrable_fixedRealKernel_critical_exp
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ¬ Integrable (fun z : ℝ × ℝ =>
      Real.exp (lambda * |fixedRealKernel z| ^ (1 / 5 : ℝ)))
      (fixedRealObservationLaw.prod fixedRealObservationLaw) := by
  intro hf
  have hfin := hf.hasFiniteIntegral
  change (∫⁻ z : ℝ × ℝ,
    ‖Real.exp (lambda * |fixedRealKernel z| ^ (1 / 5 : ℝ))‖ₑ
    ∂fixedRealObservationLaw.prod fixedRealObservationLaw) < ⊤ at hfin
  have heq : (∫⁻ z : ℝ × ℝ,
      ‖Real.exp (lambda * |fixedRealKernel z| ^ (1 / 5 : ℝ))‖ₑ
      ∂fixedRealObservationLaw.prod fixedRealObservationLaw) =
      ∫⁻ z : ℝ × ℝ,
        ENNReal.ofReal (Real.exp (lambda * |fixedRealKernel z| ^ (1 / 5 : ℝ)))
        ∂fixedRealObservationLaw.prod fixedRealObservationLaw :=
    lintegral_congr (fun _ => Real.enorm_of_nonneg (Real.exp_pos _).le)
  rw [heq, lintegral_fixedRealKernel_critical_exp_eq_top lambda hlambda] at hfin
  exact (lt_irrefl _) hfin

end
end Shao.OQ5.P52
