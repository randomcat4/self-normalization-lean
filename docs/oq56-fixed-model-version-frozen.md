# Frozen public declarations: fixed model, independent-copy pairs and Borel version

Exact definition bodies and theorem headers below omit proof bodies. Pending gates are not acceptance claims. Original p50 SHAde553dc827eeadbc1e863c1778caa9bdeb00bca84110b4666b06cab053d7b768; p52 SHA615209f8501e14a6bfaee220899c30891510fef5987c9abf7f74ac52b6538b45.

## Unit41

Exactfreeze SHA256 375965cadbd637732858bf180ab423784c2522306ea96f774a06f34067491c3a.

```lean
import Shao.OQ5.P50.ThreeStateLayer
import Shao.OQ5.P52.FixedLayerCoefficients
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

open MeasureTheory
open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

/-- The actual fixed layer matrix on the two complete observations. -/
def fixedLayerTerm (j : ℕ) (z : LayerObs × LayerObs) : ℝ :=
  Shao.OQ5.P50.layerKernel (fixedLayerN j) (fixedLayerT j) (fixedLayerP j) (fixedLayerQ j)
    (z.1.2 j) (z.2.2 j)

/-- Exactly the source absolute-convergence set, with all layers retained. -/
def fixedAbsoluteConvergenceSet : Set (LayerObs × LayerObs) :=
  {z | Summable (fun j : ℕ => |fixedLayerTerm j z|)}

/-- The actual residual series on absolute convergence, zero everywhere else. -/
def fixedResidualKernel (z : LayerObs × LayerObs) : ℝ :=
  if z ∈ fixedAbsoluteConvergenceSet then ∑' j, fixedLayerTerm j z else 0

/-- The everywhere-real source kernel, before any real-encoding transport. -/
def fixedKernel (z : LayerObs × LayerObs) : ℝ :=
  z.1.1 + z.2.1 + fixedResidualKernel z

theorem measurable_fixedLayerTerm (j : ℕ) : Measurable (fixedLayerTerm j)

theorem fixedLayerTerm_symmetric (j : ℕ) (o o' : LayerObs) :
    fixedLayerTerm j (o, o') = fixedLayerTerm j (o', o)

theorem measurableSet_fixedAbsoluteConvergenceSet :
    MeasurableSet fixedAbsoluteConvergenceSet

theorem fixedAbsoluteConvergenceSet_swap (o o' : LayerObs) :
    (o, o') ∈ fixedAbsoluteConvergenceSet ↔ (o', o) ∈ fixedAbsoluteConvergenceSet

theorem fixedResidualKernel_eq_tsum (z : LayerObs × LayerObs)
    (hz : z ∈ fixedAbsoluteConvergenceSet) :
    fixedResidualKernel z = ∑' j, fixedLayerTerm j z

theorem fixedResidualKernel_eq_zero (z : LayerObs × LayerObs)
    (hz : z ∉ fixedAbsoluteConvergenceSet) : fixedResidualKernel z = 0

theorem measurable_fixedResidualKernel : Measurable fixedResidualKernel

theorem fixedResidualKernel_symmetric (o o' : LayerObs) :
    fixedResidualKernel (o, o') = fixedResidualKernel (o', o)

theorem measurable_fixedKernel : Measurable fixedKernel

theorem fixedKernel_symmetric (o o' : LayerObs) :
    fixedKernel (o, o') = fixedKernel (o', o)

end
end Shao.OQ5.P52
```

## Unit42

Exactfreeze SHA256 ef055298de5f3f08883353edf4b6f21c4665b2173eec27c102c033643ce69839.

```lean
import Shao.OQ5.P50.LayeredProductLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory
open scoped BigOperators

namespace Shao.OQ5.P50

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem map_layerObservation_pair_category (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) (j : ℕ) :
    ((layerObservationLaw p q).prod (layerObservationLaw p q)).map
      (fun z : LayerObs × LayerObs => (z.1.2 j, z.2.2 j)) =
        (layerMeasure (p j) (q j)).prod (layerMeasure (p j) (q j))

theorem map_layerObservation_pair_category_restrict (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1)
    (J : Finset ℕ) :
    ((layerObservationLaw p q).prod (layerObservationLaw p q)).map
      (fun (z : LayerObs × LayerObs) (j : J) => (z.1.2 j, z.2.2 j)) =
        Measure.pi (fun j : J =>
          (layerMeasure (p j) (q j)).prod (layerMeasure (p j) (q j)))

theorem iIndepFun_layerObservation_pair_categories (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) :
    ProbabilityTheory.iIndepFun
      (fun j (z : LayerObs × LayerObs) => (z.1.2 j, z.2.2 j))
      ((layerObservationLaw p q).prod (layerObservationLaw p q))

theorem map_layerObservation_pair_categories (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) :
    ((layerObservationLaw p q).prod (layerObservationLaw p q)).map
      (fun (z : LayerObs × LayerObs) (j : ℕ) => (z.1.2 j, z.2.2 j)) =
        Measure.infinitePi (fun j : ℕ =>
          (layerMeasure (p j) (q j)).prod (layerMeasure (p j) (q j)))

theorem integrable_layerObservation_pair_finiteProduct (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1)
    (J : Finset ℕ) (F : ℕ → Fin 3 × Fin 3 → ℝ) :
    Integrable (fun z : LayerObs × LayerObs =>
      ∏ j ∈ J, F j (z.1.2 j, z.2.2 j))
      ((layerObservationLaw p q).prod (layerObservationLaw p q))

theorem integral_layerObservation_pair_finiteProduct (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1)
    (J : Finset ℕ) (F : ℕ → Fin 3 × Fin 3 → ℝ) :
    (∫ z : LayerObs × LayerObs, ∏ j ∈ J, F j (z.1.2 j, z.2.2 j)
      ∂(layerObservationLaw p q).prod (layerObservationLaw p q)) =
        ∏ j ∈ J, ∫ s : Fin 3 × Fin 3, F j s
          ∂(layerMeasure (p j) (q j)).prod (layerMeasure (p j) (q j))

end
end Shao.OQ5.P50
```

## Unit43

Exactfreeze SHA256 ec7a1921da93b114a710cbd4a447900c01fc1587904994ca3e3c09669727845c.

```lean
import Shao.OQ5.P52.LayeredKernelVersion
import Shao.OQ5.P50.LayeredPairLaw

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

/-- The single source observation law, fixed before every exponent and sample size. -/
def fixedObservationLaw : Measure LayerObs :=
  Shao.OQ5.P50.layerObservationLaw fixedLayerP fixedLayerQ

theorem fixedObservationLaw_isProbabilityMeasure :
    IsProbabilityMeasure fixedObservationLaw

theorem map_fixedObservation_first :
    fixedObservationLaw.map Prod.fst = Shao.OQ5.P50.layerNoiseLaw

theorem map_fixedObservation_categories :
    fixedObservationLaw.map Prod.snd =
      Shao.OQ5.P50.layerCategoryProductLaw fixedLayerP fixedLayerQ

theorem map_fixedObservation_category (j : ℕ) :
    fixedObservationLaw.map (fun o => o.2 j) =
      Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j)

theorem fixedObservation_first_ae_mem :
    ∀ᵐ o ∂fixedObservationLaw, o.1 ∈ Set.Icc (-1 : ℝ) 1

theorem fixedObservation_first_indep_categories :
    ProbabilityTheory.IndepFun Prod.fst Prod.snd fixedObservationLaw

theorem integrable_fixedLayerTerm_row (j : ℕ) (o : LayerObs) :
    Integrable (fun o' : LayerObs => fixedLayerTerm j (o, o')) fixedObservationLaw

theorem integral_fixedLayerTerm_row_zero (j : ℕ) (o : LayerObs) :
    (∫ o' : LayerObs, fixedLayerTerm j (o, o') ∂fixedObservationLaw) = 0

theorem fixedLayerTerm_memLp_two (j : ℕ) :
    MemLp (fixedLayerTerm j) 2 (fixedObservationLaw.prod fixedObservationLaw)

theorem iIndepFun_fixedLayerTerms :
    ProbabilityTheory.iIndepFun (fun j => fixedLayerTerm j)
      (fixedObservationLaw.prod fixedObservationLaw)

end
end Shao.OQ5.P52
```
