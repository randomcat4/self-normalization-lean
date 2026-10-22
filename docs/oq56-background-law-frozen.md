# Actual erased background law, kernel and conditional iid prefix — frozen catalogs

ACCEPTED FROZEN CATALOGS. Exact copies from immutable original freezes; independent proof gates are documented separately.

## Unit59

Freeze SHA256 6c7fe980f04fbfe3d02ec536f14161d910cae2c03e06c2f7ba401df17743e057.

```lean
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory ProbabilityTheory

namespace Shao.OQ5.P52

noncomputable section

theorem indepFun_product_noise_lift
    {G C A B : Type*} [MeasurableSpace G] [MeasurableSpace C]
    [MeasurableSpace A] [MeasurableSpace B]
    (γ : Measure G) (ν : Measure C)
    [IsProbabilityMeasure γ] [IsProbabilityMeasure ν]
    {X : C → A} {Y : C → B}
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y ν) :
    IndepFun (fun z : G × C => X z.2)
      (fun z : G × C => (z.1, Y z.2)) (γ.prod ν)

theorem map_cond_indep_eq_map
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → A} {Y : Ω → B}
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y μ)
    (D : Set A) (hD : MeasurableSet D) (hA : μ (X ⁻¹' D) ≠ 0) :
    (ProbabilityTheory.cond μ (X ⁻¹' D)).map Y = μ.map Y

end
end Shao.OQ5.P52
```

## Unit60

Freeze SHA256 700805567132a42ccc176e43ab67b7179c91c8a4063e60af40b26dfe55ea1b72.

```lean
import Shao.OQ5.P52.FixedLayerModel
import Shao.OQ5.P52.BackgroundMeasureBridges
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

def fixedEraseLayer (j : ℕ) (o : LayerObs) : LayerObs :=
  (o.1, fun k : ℕ => if k = j then 0 else o.2 k)

def fixedErasedLaw (j : ℕ) : Measure LayerObs :=
  fixedObservationLaw.map (fixedEraseLayer j)

theorem measurable_fixedEraseLayer (j : ℕ) :
    Measurable (fixedEraseLayer j)

theorem fixedErasedLaw_isProbabilityMeasure (j : ℕ) :
    IsProbabilityMeasure (fixedErasedLaw j)

theorem fixedObservation_category_indep_fixedEraseLayer (j : ℕ) :
    IndepFun (fun o : LayerObs => o.2 j) (fixedEraseLayer j) fixedObservationLaw

theorem map_cond_fixedObservation_fixedEraseLayer (j : ℕ) (a : Fin 3) :
    (ProbabilityTheory.cond fixedObservationLaw {o : LayerObs | o.2 j = a}).map
      (fixedEraseLayer j) = fixedErasedLaw j

theorem fixedErasedLaw_eq_cond_zero (j : ℕ) :
    fixedErasedLaw j =
      ProbabilityTheory.cond fixedObservationLaw {o : LayerObs | o.2 j = 0}

theorem fixedErasedLaw_absolutelyContinuous (j : ℕ) :
    fixedErasedLaw j ≪ fixedObservationLaw

end
end Shao.OQ5.P52
```

## Unit61

Freeze SHA256 d95dcc36a08e1d373aa7a1bd4d760d64472403f5a7a1121acf0e2f272d768a59.

```lean
import Shao.OQ5.P52.FixedLayerErasureLaw
import Shao.OQ5.P52.FixedLayerAbsoluteMoments

open MeasureTheory Filter
open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem fixedLayerTerm_erase_pair (j k : ℕ) (z : LayerObs × LayerObs) :
    fixedLayerTerm k (fixedEraseLayer j z.1, fixedEraseLayer j z.2) =
      if k = j then 0 else fixedLayerTerm k z

theorem fixedAbsoluteConvergenceSet_erase_pair_iff
    (j : ℕ) (z : LayerObs × LayerObs) :
    (fixedEraseLayer j z.1, fixedEraseLayer j z.2) ∈ fixedAbsoluteConvergenceSet ↔
      z ∈ fixedAbsoluteConvergenceSet

theorem fixedResidualKernel_erase_pair_eq_sub (j : ℕ) (z : LayerObs × LayerObs)
    (hz : z ∈ fixedAbsoluteConvergenceSet) :
    fixedResidualKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2) =
      fixedResidualKernel z - fixedLayerTerm j z

theorem fixedKernel_erase_pair_eq_sub (j : ℕ) (z : LayerObs × LayerObs)
    (hz : z ∈ fixedAbsoluteConvergenceSet) :
    fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2) =
      fixedKernel z - fixedLayerTerm j z

theorem fixedResidualKernel_erase_pair_ae_eq_sub (j : ℕ) :
    (fun z : LayerObs × LayerObs =>
      fixedResidualKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2))
      =ᵐ[fixedObservationLaw.prod fixedObservationLaw]
        (fun z : LayerObs × LayerObs => fixedResidualKernel z - fixedLayerTerm j z)

theorem fixedKernel_erase_pair_ae_eq_sub (j : ℕ) :
    (fun z : LayerObs × LayerObs =>
      fixedKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2))
      =ᵐ[fixedObservationLaw.prod fixedObservationLaw]
        (fun z : LayerObs × LayerObs => fixedKernel z - fixedLayerTerm j z)

end
end Shao.OQ5.P52
```

## Unit62

Freeze SHA256 de25310b49d9a2a5b3097b4ac0eecd0cb95dbf32648441d1b1b1dfc4dfde5080.

```lean
import Shao.OQ5.P52.FixedLayerConditionalLaw
import Shao.OQ5.P52.FixedLayerErasureLaw
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory ProbabilityTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem map_fixedSamplePrefix_erase (j n : ℕ) :
    fixedSampleLaw.map
      (fun ω (i : Fin n) => fixedEraseLayer j (fixedSampleCoordinate i.val ω)) =
      Measure.pi (fun _ : Fin n => fixedErasedLaw j)

theorem map_fixedLayerPositionEvent_cond_erasedPrefix
    (j n : ℕ) (J : Finset (Fin n)) :
    (ProbabilityTheory.cond fixedSampleLaw (fixedLayerPositionEvent j n J)).map
      (fun ω (i : Fin n) => fixedEraseLayer j (fixedSampleCoordinate i.val ω)) =
      Measure.pi (fun _ : Fin n => fixedErasedLaw j)

theorem map_fixedLayerPositionEvent_cond_erasedCoordinate
    (j n : ℕ) (J : Finset (Fin n)) (i : Fin n) :
    (ProbabilityTheory.cond fixedSampleLaw (fixedLayerPositionEvent j n J)).map
      (fun ω => fixedEraseLayer j (fixedSampleCoordinate i.val ω)) = fixedErasedLaw j

theorem iIndepFun_fixedLayerPositionEvent_cond_erasedPrefix
    (j n : ℕ) (J : Finset (Fin n)) :
    iIndepFun (fun i : Fin n =>
      fun ω => fixedEraseLayer j (fixedSampleCoordinate i.val ω))
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerPositionEvent j n J))

end
end Shao.OQ5.P52
```
