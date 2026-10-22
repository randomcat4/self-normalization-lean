# Actual fixed-model critical exponential boundary — frozen catalogs

ACCEPTED FROZEN CATALOGS. Exactly13 public theorems and0 public definitions.
Only70/71/72 are included; future51/73 are excluded.

## Unit70: FixedLayerPairAABounds

Original freeze SHA256 a736d4df58fd3cc5cc32156c117d0329ea65ed70a2027a15cbff995932a392c7; 5 public theorems,0definitions.

```lean
import Shao.OQ5.P52.FixedLayerPairAACondition

open MeasureTheory Filter

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem integrable_fixedKernel_erasedPair_sq_cond_pairAA (j : ℕ) :
    Integrable
      (fun z : LayerObs × LayerObs =>
        (fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2)) ^ 2)
      (ProbabilityTheory.cond (fixedObservationLaw.prod fixedObservationLaw)
        (fixedLayerPairAAEvent j))

theorem integral_fixedKernel_erasedPair_sq_cond_pairAA_le (j : ℕ) :
    (∫ z : LayerObs × LayerObs,
      (fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2)) ^ 2
      ∂ProbabilityTheory.cond (fixedObservationLaw.prod fixedObservationLaw)
        (fixedLayerPairAAEvent j)) ≤
      2 / 3 + ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw

theorem fixedLayerPairAAEvent_background_small_probability
    (j : ℕ) (b : ℝ) (hb : 0 < b) :
    1 - (2 / 3 + ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
      ∂fixedObservationLaw.prod fixedObservationLaw) / b ^ 2 ≤
      (ProbabilityTheory.cond (fixedObservationLaw.prod fixedObservationLaw)
        (fixedLayerPairAAEvent j)).real
        {z : LayerObs × LayerObs |
          |fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2)| ≤ b}

theorem fixedLayerPairAAEvent_background_small_original_probability
    (j : ℕ) (b : ℝ) (hb : 0 < b) :
    (fixedLayerP j) ^ 2 *
      (1 - (2 / 3 + ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw) / b ^ 2) ≤
      (fixedObservationLaw.prod fixedObservationLaw).real
        (fixedLayerPairAAEvent j ∩
          {z : LayerObs × LayerObs |
            |fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2)| ≤ b})

theorem fixedKernel_abs_ge_on_pairAA_background_small_ae (j : ℕ) (b : ℝ) :
    ∀ᵐ z : LayerObs × LayerObs ∂fixedObservationLaw.prod fixedObservationLaw,
      z ∈ fixedLayerPairAAEvent j →
        |fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2)| ≤ b →
          (((fixedLayerN j : ℝ) - 4) * fixedLayerT j) - b ≤ |fixedKernel z|

end
end Shao.OQ5.P52
```

## Unit71: FixedLayerCriticalScales

Original freeze SHA256 b7779d48ff05ff12cff63e06c5db9e889f78986c415304d58dddde23bb793c73; 5 public theorems,0definitions.

```lean
import Shao.OQ5.P52.FixedLayerGrowth

open Filter
open scoped Topology

namespace Shao.OQ5.P52

noncomputable section

theorem fixedLayer_pairAA_shift_lower (j : ℕ) :
    (fixedLayerN j : ℝ) ^ (5 / 3 : ℝ) / 2 ≤
      ((fixedLayerN j : ℝ) - 4) * fixedLayerT j

theorem fixedLayer_critical_radius_tendsto :
    Tendsto (fun j : ℕ => (fixedLayerN j : ℝ) ^ (5 / 3 : ℝ) / 4)
      atTop atTop

theorem fixedLayer_critical_radius_rpow (j : ℕ) :
    ((fixedLayerN j : ℝ) ^ (5 / 3 : ℝ) / 4) ^ (1 / 5 : ℝ) =
      (4 : ℝ) ^ (-1 / 5 : ℝ) * (fixedLayerN j : ℝ) ^ (1 / 3 : ℝ)

theorem fixedLayer_critical_mass_exp_identity (j : ℕ) (lambda : ℝ) :
    (1 / 2 : ℝ) * (fixedLayerP j) ^ 2 *
      Real.exp (lambda * (4 : ℝ) ^ (-1 / 5 : ℝ) *
        (fixedLayerN j : ℝ) ^ (1 / 3 : ℝ)) =
      (1 / 2 : ℝ) * Real.exp
        ((fixedLayerN j : ℝ) ^ (1 / 3 : ℝ) *
          (lambda * (4 : ℝ) ^ (-1 / 5 : ℝ) -
            2 * (fixedLayerN j : ℝ) ^ (-1 / ((j + 6 : ℕ) : ℝ))))

theorem fixedLayer_critical_mass_exp_tendsto (lambda : ℝ) (hlambda : 0 < lambda) :
    Tendsto (fun j : ℕ =>
      (1 / 2 : ℝ) * (fixedLayerP j) ^ 2 *
        Real.exp (lambda * (4 : ℝ) ^ (-1 / 5 : ℝ) *
          (fixedLayerN j : ℝ) ^ (1 / 3 : ℝ)))
      atTop atTop

end
end Shao.OQ5.P52
```

## Unit72: FixedLayerCriticalDivergence

Original freeze SHA256 d1d1f24b60dfeebe2069591a991cdb8365c49dc39c6d3cdf9e737102ff3d8068; 3 public theorems,0definitions.

```lean
import Shao.OQ5.P52.FixedLayerPairAABounds
import Shao.OQ5.P52.FixedLayerCriticalScales

open MeasureTheory Filter

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem fixedKernel_critical_lintegral_layer_lower_bound
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal
        ((1 / 2 : ℝ) * (fixedLayerP j) ^ 2 *
          Real.exp (lambda * (4 : ℝ) ^ (-1 / 5 : ℝ) *
            (fixedLayerN j : ℝ) ^ (1 / 3 : ℝ))) ≤
        ∫⁻ z : LayerObs × LayerObs,
          ENNReal.ofReal (Real.exp (lambda * |fixedKernel z| ^ (1 / 5 : ℝ)))
          ∂fixedObservationLaw.prod fixedObservationLaw

theorem lintegral_fixedKernel_critical_exp_eq_top
    (lambda : ℝ) (hlambda : 0 < lambda) :
    (∫⁻ z : LayerObs × LayerObs,
      ENNReal.ofReal (Real.exp (lambda * |fixedKernel z| ^ (1 / 5 : ℝ)))
      ∂fixedObservationLaw.prod fixedObservationLaw) = ⊤

theorem not_integrable_fixedKernel_critical_exp
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ¬ Integrable
      (fun z : LayerObs × LayerObs =>
        Real.exp (lambda * |fixedKernel z| ^ (1 / 5 : ℝ)))
      (fixedObservationLaw.prod fixedObservationLaw)

end
end Shao.OQ5.P52
```
