# Frozen catalogs — canonical projection and residual variance

Authoritative original freezes are immutable. These exact catalog copies all received independent original-source reviews before implementation and independent final gates; evidence is in the review document.

## Unit50

Original freeze SHA256 3dbf9a9dfcdd8753d3b9ee385db278d2672973ea94165e324d97f5a917dea0ac.

```lean
import Shao.OQ5.P52.FixedLayerAbsoluteMoments
import Mathlib.MeasureTheory.Function.UniformIntegrable

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem fixedLayerAbsSum_memLp (ν : ℝ) (hν : 1 ≤ ν) :
    MemLp (fun z : LayerObs × LayerObs => ∑' j : ℕ, |fixedLayerTerm j z|)
      (ENNReal.ofReal ν) (fixedObservationLaw.prod fixedObservationLaw)

theorem fixedResidualKernel_memLp (ν : ℝ) (hν : 1 ≤ ν) :
    MemLp fixedResidualKernel (ENNReal.ofReal ν)
      (fixedObservationLaw.prod fixedObservationLaw)

theorem fixedKernel_memLp (ν : ℝ) (hν : 1 ≤ ν) :
    MemLp fixedKernel (ENNReal.ofReal ν)
      (fixedObservationLaw.prod fixedObservationLaw)

theorem fixedLayerPartialSum_tendsto_eLpNorm (ν : ℝ) (hν : 1 ≤ ν) :
    Tendsto (fun n : ℕ =>
      eLpNorm (fun z : LayerObs × LayerObs =>
        (∑ j ∈ Finset.range n, fixedLayerTerm j z) - fixedResidualKernel z)
        (ENNReal.ofReal ν) (fixedObservationLaw.prod fixedObservationLaw))
      atTop (nhds 0)

end
end Shao.OQ5.P52
```

## Unit52

Original freeze SHA256 7a4f94eb21f563cf85fb27beab6abc7d08fa288513d1d29b7aba2f9add3516f1.

```lean
import Shao.OQ5.P52.FixedLayerLpLimits
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem summable_integral_abs_fixedLayerTerm :
    Summable (fun j : ℕ =>
      ∫ z : LayerObs × LayerObs, |fixedLayerTerm j z|
        ∂fixedObservationLaw.prod fixedObservationLaw)

theorem integrable_fixedResidualKernel_row_ae :
    ∀ᵐ o : LayerObs ∂fixedObservationLaw,
      Integrable (fun o' : LayerObs => fixedResidualKernel (o, o')) fixedObservationLaw

theorem integral_fixedResidualKernel_row_eq_zero_ae :
    ∀ᵐ o : LayerObs ∂fixedObservationLaw,
      (∫ o' : LayerObs, fixedResidualKernel (o, o') ∂fixedObservationLaw) = 0

theorem integral_fixedResidualKernel_eq_zero :
    (∫ z : LayerObs × LayerObs, fixedResidualKernel z
      ∂fixedObservationLaw.prod fixedObservationLaw) = 0

end
end Shao.OQ5.P52
```

## Unit53

Original freeze SHA256 649c07e802e019c07962d4934ad196c82d6b24c1a3432b9e153cfdfcc3469698.

```lean
import Shao.OQ5.P52.FixedLayerModel
import Shao.OQ5.P35.NoiseMoments

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem integrable_fixedObservation_first :
    Integrable (fun o : LayerObs => o.1) fixedObservationLaw

theorem integral_fixedObservation_first_eq_zero :
    (∫ o : LayerObs, o.1 ∂fixedObservationLaw) = 0

theorem integrable_fixedObservation_first_sq :
    Integrable (fun o : LayerObs => o.1 ^ 2) fixedObservationLaw

theorem integral_fixedObservation_first_sq :
    (∫ o : LayerObs, o.1 ^ 2 ∂fixedObservationLaw) = (1 / 3 : ℝ)

end
end Shao.OQ5.P52
```

## Unit54

Original freeze SHA256 1c70e3ce919b83cfb9b58edb824e258175309b2412ce82ce2099263b5d0bd3a3.

```lean
import Shao.OQ5.P52.FixedLayerCanonicalRows
import Shao.OQ5.P52.FixedObservationNoiseMoments

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

def fixedFirstProjection (o : LayerObs) : ℝ :=
  ∫ o' : LayerObs, fixedKernel (o, o') ∂fixedObservationLaw

theorem integrable_fixedKernel_row_ae :
    ∀ᵐ o : LayerObs ∂fixedObservationLaw,
      Integrable (fun o' : LayerObs => fixedKernel (o, o')) fixedObservationLaw

theorem fixedFirstProjection_ae_eq_first :
    fixedFirstProjection =ᵐ[fixedObservationLaw] (fun o : LayerObs => o.1)

theorem integral_fixedKernel_eq_zero :
    (∫ z : LayerObs × LayerObs, fixedKernel z
      ∂fixedObservationLaw.prod fixedObservationLaw) = 0

theorem fixedFirstProjection_memLp_two :
    MemLp fixedFirstProjection 2 fixedObservationLaw

theorem integral_fixedFirstProjection_sq :
    (∫ o : LayerObs, fixedFirstProjection o ^ 2 ∂fixedObservationLaw) = (1 / 3 : ℝ)

theorem fixedFirstProjection_indep_categories :
    ProbabilityTheory.IndepFun fixedFirstProjection Prod.snd fixedObservationLaw

end
end Shao.OQ5.P52
```

## Unit55

Original freeze SHA256 67512ccd05a08bbb8320bae2de0207b52768faebe101e80a5bc200cad972e2b2.

```lean
import Shao.OQ5.P52.FixedLayerLpLimits
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Integration

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem summable_integral_fixedLayerTerm_sq :
    Summable (fun j : ℕ =>
      ∫ z : LayerObs × LayerObs, (fixedLayerTerm j z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw)

theorem integral_fixedResidualKernel_sq_eq_tsum :
    (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
      ∂fixedObservationLaw.prod fixedObservationLaw) =
      ∑' j : ℕ, ∫ z : LayerObs × LayerObs, (fixedLayerTerm j z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw

end
end Shao.OQ5.P52
```
