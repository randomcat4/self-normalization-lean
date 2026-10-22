# Actual erased canonical edges and positive AA pair condition — frozen catalogs

ACCEPTED FROZEN CATALOGS. Exactly10 public theorems and1 public definition. Original source catalog hashes and separate independent reports are recorded below. Future51/70/71 are excluded.

## Unit68: FixedLayerErasedEdgeMoments

Original freeze SHA256 277f319feda262508b388e160152d8d938920d77717a9946ff2164863b7d9bd7; 4 public theorems and 0 public definitions.

```lean
import Shao.OQ5.P52.FixedLayerErasedCanonical

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem fixedErasedResidualEdge_memLp_two (j n : ℕ) (a b : Fin n) (hab : a ≠ b) :
    MemLp (fun x : Fin n → LayerObs => fixedResidualKernel (x a, x b)) 2
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j))

theorem integral_fixedErasedResidualEdge_eq_zero
    (j n : ℕ) (a b : Fin n) (hab : a ≠ b) :
    (∫ x : Fin n → LayerObs, fixedResidualKernel (x a, x b)
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0

theorem integrable_fixedErasedResidualEdge_mul
    (j n : ℕ) (a b c d : Fin n) (hab : a ≠ b) (hcd : c ≠ d) :
    Integrable (fun x : Fin n → LayerObs =>
      fixedResidualKernel (x a, x b) * fixedResidualKernel (x c, x d))
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j))

theorem integral_fixedErasedResidualEdge_mul
    (j n : ℕ) (a b c d : Fin n) (hab : a ≠ b) (hcd : c ≠ d) :
    (∫ x : Fin n → LayerObs,
      fixedResidualKernel (x a, x b) * fixedResidualKernel (x c, x d)
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      if ({a, b} : Finset (Fin n)) = {c, d} then
        ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j)
      else 0

end
end Shao.OQ5.P52
```

## Unit69: FixedLayerPairAACondition

Original freeze SHA256 af31ef65d0d6b2498ff463e40db62a23f1d05b5419e3ec432cbf141dc4719e28; 6 public theorems and 1 public definitions.

```lean
import Shao.OQ5.P52.FixedLayerErasedProjection

open MeasureTheory Filter

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

def fixedLayerPairAAEvent (j : ℕ) : Set (LayerObs × LayerObs) :=
  {z | z.1.2 j = 1 ∧ z.2.2 j = 1}

theorem measurableSet_fixedLayerPairAAEvent (j : ℕ) :
    MeasurableSet (fixedLayerPairAAEvent j)

theorem fixedLayerPairAAEvent_probability (j : ℕ) :
    (fixedObservationLaw.prod fixedObservationLaw).real (fixedLayerPairAAEvent j) =
      (fixedLayerP j) ^ 2

theorem fixedLayerPairAAEvent_probability_pos (j : ℕ) :
    0 < (fixedObservationLaw.prod fixedObservationLaw).real (fixedLayerPairAAEvent j)

theorem fixedLayerPairAAEvent_cond_isProbabilityMeasure (j : ℕ) :
    IsProbabilityMeasure
      (ProbabilityTheory.cond (fixedObservationLaw.prod fixedObservationLaw)
        (fixedLayerPairAAEvent j))

theorem map_fixedLayerPairAAEvent_cond_erasedPair (j : ℕ) :
    (ProbabilityTheory.cond (fixedObservationLaw.prod fixedObservationLaw)
      (fixedLayerPairAAEvent j)).map
      (fun z : LayerObs × LayerObs => (fixedEraseLayer j z.1, fixedEraseLayer j z.2)) =
      (fixedErasedLaw j).prod (fixedErasedLaw j)

theorem fixedKernel_ae_eq_erased_sub_on_pairAA (j : ℕ) :
    ∀ᵐ z : LayerObs × LayerObs
      ∂ProbabilityTheory.cond (fixedObservationLaw.prod fixedObservationLaw)
        (fixedLayerPairAAEvent j),
      fixedKernel z = fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2) -
        (((fixedLayerN j : ℝ) - 4) * fixedLayerT j)

end
end Shao.OQ5.P52
```
