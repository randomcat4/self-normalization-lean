# Actual rare-condition background law and full-kernel projection — frozen catalogs

ACCEPTED FROZEN CATALOGS. Exact immutable catalogs; independent final66/67 gates passed and documented separately. Unit51 and68 excluded.

## Unit66: FixedLayerErasedMixture

OriginalfreezeSHA256d55aa3677df4fca0ff5bde306f2c3eaff53bc204125ec201c38f3b533abe340a,0publicdefinitions.

```lean
import Shao.OQ5.P52.FixedLayerErasedSample

open MeasureTheory ProbabilityTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem fixedLayerExactEvent_probability_pos (j n K : ℕ) (hK : K ≤ n) :
    0 < fixedSampleLaw.real (fixedLayerExactEvent j n K)

theorem fixedLayerExactEvent_cond_isProbabilityMeasure
    (j n K : ℕ) (hK : K ≤ n) :
    IsProbabilityMeasure (ProbabilityTheory.cond fixedSampleLaw (fixedLayerExactEvent j n K))

theorem map_fixedLayerExactEvent_cond_erasedPrefix
    (j n K : ℕ) (hK : K ≤ n) :
    (ProbabilityTheory.cond fixedSampleLaw (fixedLayerExactEvent j n K)).map
      (fun ω (i : Fin n) => fixedEraseLayer j (fixedSampleCoordinate i.val ω)) =
      Measure.pi (fun _ : Fin n => fixedErasedLaw j)

theorem map_fixedLayerRareEvent_cond_erasedPrefix (j : ℕ) :
    (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)).map
      (fun ω (i : Fin (fixedLayerN j)) =>
        fixedEraseLayer j (fixedSampleCoordinate i.val ω)) =
      Measure.pi (fun _ : Fin (fixedLayerN j) => fixedErasedLaw j)

theorem iIndepFun_fixedLayerRareEvent_cond_erasedPrefix (j : ℕ) :
    iIndepFun (fun i : Fin (fixedLayerN j) =>
      fun ω => fixedEraseLayer j (fixedSampleCoordinate i.val ω))
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j))

end
end Shao.OQ5.P52
```

## Unit67: FixedLayerErasedProjection

OriginalfreezeSHA25679a5b5218571b17780ee7ba245b3b04fae13aeeb4f31cb91b27a8270fc029de8,0publicdefinitions.

```lean
import Shao.OQ5.P52.FixedLayerErasedVariance
import Shao.OQ5.P52.FixedLayerErasedNoise

open MeasureTheory Filter

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem fixedKernel_memLp_two_fixedErasedLaw (j : ℕ) :
    MemLp fixedKernel 2 ((fixedErasedLaw j).prod (fixedErasedLaw j))

theorem integrable_fixedKernel_row_fixedErasedLaw_ae (j : ℕ) :
    ∀ᵐ o : LayerObs ∂fixedErasedLaw j,
      Integrable (fun o' : LayerObs => fixedKernel (o, o')) (fixedErasedLaw j)

theorem integral_fixedKernel_row_fixedErasedLaw_eq_first_ae (j : ℕ) :
    ∀ᵐ o : LayerObs ∂fixedErasedLaw j,
      (∫ o' : LayerObs, fixedKernel (o, o') ∂fixedErasedLaw j) = o.1

theorem integral_fixedKernel_fixedErasedLaw_eq_zero (j : ℕ) :
    (∫ z : LayerObs × LayerObs, fixedKernel z
      ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) = 0

theorem integral_fixedKernel_sq_fixedErasedLaw (j : ℕ) :
    (∫ z : LayerObs × LayerObs, (fixedKernel z) ^ 2
      ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) =
      2 / 3 + ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
        ∂(fixedErasedLaw j).prod (fixedErasedLaw j)

theorem integral_fixedKernel_sq_fixedErasedLaw_le (j : ℕ) :
    (∫ z : LayerObs × LayerObs, (fixedKernel z) ^ 2
      ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) ≤
      2 / 3 + ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw

end
end Shao.OQ5.P52
```
