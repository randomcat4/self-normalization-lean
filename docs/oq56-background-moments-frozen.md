# Actual erased-background population moments — frozen catalogs

ACCEPTED FROZEN CATALOGS. Exact immutable catalogs; all independent gates passed as documented separately. Unit51 and66/67 excluded.

## Unit63: FixedLayerErasedCanonical

Original freeze SHA256 1545714eaf7fc7efc306701e0c6bb209bb47bd9752eea4afac8196789e4aa8eb. Zero public definitions.

```lean
import Shao.OQ5.P52.FixedLayerErasureKernel
import Shao.OQ5.P52.FixedLayerCanonicalRows

open MeasureTheory Filter

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem map_fixedEraseLayer_pair (j : ℕ) :
    (fixedObservationLaw.prod fixedObservationLaw).map
      (fun z : LayerObs × LayerObs => (fixedEraseLayer j z.1, fixedEraseLayer j z.2)) =
      (fixedErasedLaw j).prod (fixedErasedLaw j)

theorem fixedResidualKernel_memLp_two_fixedErasedLaw (j : ℕ) :
    MemLp fixedResidualKernel 2 ((fixedErasedLaw j).prod (fixedErasedLaw j))

theorem integrable_fixedResidualKernel_row_fixedErasedLaw_ae (j : ℕ) :
    ∀ᵐ o : LayerObs ∂fixedErasedLaw j,
      Integrable (fun o' : LayerObs => fixedResidualKernel (o, o')) (fixedErasedLaw j)

theorem integral_fixedResidualKernel_row_fixedErasedLaw_eq_zero_ae (j : ℕ) :
    ∀ᵐ o : LayerObs ∂fixedErasedLaw j,
      (∫ o' : LayerObs, fixedResidualKernel (o, o') ∂fixedErasedLaw j) = 0

theorem integral_fixedResidualKernel_fixedErasedLaw_eq_zero (j : ℕ) :
    (∫ z : LayerObs × LayerObs, fixedResidualKernel z
      ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) = 0

end
end Shao.OQ5.P52
```

## Unit64: FixedLayerErasedVariance

Original freeze SHA256 ba6f2dfcccc87cd89a7df9e4d3ae09e4f55db096322d2b2d3ed2fe2071ec5092. Zero public definitions.

```lean
import Shao.OQ5.P52.FixedLayerErasedCanonical
import Shao.OQ5.P52.FixedLayerVariance

open MeasureTheory Filter

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem integral_fixedResidualKernel_mul_fixedLayerTerm (j : ℕ) :
    (∫ z : LayerObs × LayerObs, fixedResidualKernel z * fixedLayerTerm j z
      ∂fixedObservationLaw.prod fixedObservationLaw) =
      ∫ z : LayerObs × LayerObs, (fixedLayerTerm j z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw

theorem integral_fixedResidualKernel_sq_fixedErasedLaw_eq_sub (j : ℕ) :
    (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
      ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) =
      (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw) -
      ∫ z : LayerObs × LayerObs, (fixedLayerTerm j z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw

theorem integral_fixedResidualKernel_sq_fixedErasedLaw_le (j : ℕ) :
    (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
      ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) ≤
      ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw

end
end Shao.OQ5.P52
```

## Unit65: FixedLayerErasedNoise

Original freeze SHA256 37782a944fab156e6f20e2c1b345b6dad6d5091380c77f9b66934cd9f7c8233b. Zero public definitions.

```lean
import Shao.OQ5.P52.FixedLayerErasureLaw
import Shao.OQ5.P52.FixedObservationNoiseMoments

open MeasureTheory ProbabilityTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem map_fixedErasedLaw_first (j : ℕ) :
    (fixedErasedLaw j).map Prod.fst = Shao.OQ5.P50.layerNoiseLaw

theorem integrable_fixedErasedLaw_first (j : ℕ) :
    Integrable (fun o : LayerObs => o.1) (fixedErasedLaw j)

theorem integral_fixedErasedLaw_first_eq_zero (j : ℕ) :
    (∫ o : LayerObs, o.1 ∂fixedErasedLaw j) = 0

theorem integrable_fixedErasedLaw_first_sq (j : ℕ) :
    Integrable (fun o : LayerObs => o.1 ^ 2) (fixedErasedLaw j)

theorem integral_fixedErasedLaw_first_sq (j : ℕ) :
    (∫ o : LayerObs, o.1 ^ 2 ∂fixedErasedLaw j) = 1 / 3

theorem fixedErasedLaw_first_indep_categories (j : ℕ) :
    IndepFun Prod.fst Prod.snd (fixedErasedLaw j)

end
end Shao.OQ5.P52
```
