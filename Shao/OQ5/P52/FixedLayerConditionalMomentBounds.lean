import Shao.OQ5.P52.FixedLayerConditionalStatisticsMoments
import Shao.OQ5.P52.FixedLayerErasedVariance

/-!
# A fixed original-law bound for both original conditional moments

The exact nonzero conditional mean dominates the source sixth-root scale.
The actual background variance is bounded by the genuine original residual
second moment, giving the same fixed bound for the centered numerator
variance and the original randomly centered jackknife-square expectation.
-/

set_option autoImplicit false

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

private theorem original_square_integrable :
    Integrable (fun z : LayerObs × LayerObs => (fixedResidualKernel z) ^ 2)
      (fixedObservationLaw.prod fixedObservationLaw) := by
  have h : MemLp fixedResidualKernel 2
      (fixedObservationLaw.prod fixedObservationLaw) := by
    simpa using fixedResidualKernel_memLp 2 (by norm_num)
  exact h.integrable_sq

private theorem coefficient_product_le_four
    (d v w a : ℝ) (hd : 1 ≤ d) (hv : 0 ≤ v) (hvw : v ≤ w) (ha : a ≤ 4) :
    (a / d) * v ≤ 4 * w := by
  have hdpos : 0 < d := by linarith
  have hc : a / d ≤ 4 := (div_le_iff₀ hdpos).mpr (by linarith)
  exact mul_le_mul hc hvw hv (by norm_num)

theorem fixedLayerRareNumeratorMean_ge (j : ℕ) :
    2 * (fixedLayerN j : ℝ) ^ (1 / 6 : ℝ) ≤
      (2 * fixedLayerT j * Real.sqrt (fixedLayerN j : ℝ)) /
        ((fixedLayerN j : ℝ) - 1) := by
  have hN : (8 : ℝ) ≤ fixedLayerN j := by exact_mod_cast fixedLayerN_ge_eight j
  have hNpos : 0 < (fixedLayerN j : ℝ) := by linarith
  have hpower : fixedLayerT j * Real.sqrt (fixedLayerN j : ℝ) =
      (fixedLayerN j : ℝ) * (fixedLayerN j : ℝ) ^ (1 / 6 : ℝ) := by
    rw [fixedLayerT_eq_rpow_N, Real.sqrt_eq_rpow, ← Real.rpow_add hNpos,
      show (2 / 3 : ℝ) + 1 / 2 = 1 + 1 / 6 by norm_num,
      Real.rpow_add hNpos, Real.rpow_one]
  apply (le_div_iff₀ (by linarith : 0 < (fixedLayerN j : ℝ) - 1)).mpr
  have ha := Real.rpow_nonneg hNpos.le (1 / 6 : ℝ)
  have hscaled : 2 * fixedLayerT j * Real.sqrt (fixedLayerN j : ℝ) =
      2 * ((fixedLayerN j : ℝ) * (fixedLayerN j : ℝ) ^ (1 / 6 : ℝ)) := by
    calc
      _ = 2 * (fixedLayerT j * Real.sqrt (fixedLayerN j : ℝ)) := by ring
      _ = _ := by rw [hpower]
  rw [hscaled]
  nlinarith

theorem integral_fixedSampleNumerator_centered_sq_fixedLayerRareEvent_cond_le (j : ℕ) :
    (∫ ω : ℕ → LayerObs,
      (Real.sqrt (fixedLayerN j : ℝ) *
          fixedSampleU (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω) -
        (2 * fixedLayerT j * Real.sqrt (fixedLayerN j : ℝ)) /
          ((fixedLayerN j : ℝ) - 1)) ^ 2
      ∂ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) ≤
      (4 / 3 : ℝ) + 4 *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂fixedObservationLaw.prod fixedObservationLaw) := by
  have _hOriginalSquare := original_square_integrable
  have hN : (8 : ℝ) ≤ fixedLayerN j := by exact_mod_cast fixedLayerN_ge_eight j
  rw [integral_fixedSampleNumerator_centered_sq_fixedLayerRareEvent_cond]
  have hbound :=
    coefficient_product_le_four ((fixedLayerN j : ℝ) - 1) _ _ 2 (by linarith)
      (integral_nonneg (fun z => sq_nonneg (fixedResidualKernel z)))
      (integral_fixedResidualKernel_sq_fixedErasedLaw_le j) (by norm_num)
  linarith

theorem integral_fixedSampleStudentizerSq_fixedLayerRareEvent_cond_le (j : ℕ) :
    (∫ ω : ℕ → LayerObs,
      fixedSampleStudentizerSq
        (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)
      ∂ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) ≤
      (4 / 3 : ℝ) + 4 *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂fixedObservationLaw.prod fixedObservationLaw) := by
  have _hOriginalSquare := original_square_integrable
  have _hOriginalR := integrable_fixedSampleStudentizerSq_fixedLayerRareEvent_cond j
  have hN : (8 : ℝ) ≤ fixedLayerN j := by exact_mod_cast fixedLayerN_ge_eight j
  rw [integral_fixedSampleStudentizerSq_fixedLayerRareEvent_cond]
  have hbound :=
    coefficient_product_le_four ((fixedLayerN j : ℝ) - 2) _ _ 4 (by linarith)
      (integral_nonneg (fun z => sq_nonneg (fixedResidualKernel z)))
      (integral_fixedResidualKernel_sq_fixedErasedLaw_le j) (by norm_num)
  linarith

end
end Shao.OQ5.P52
