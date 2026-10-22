# Exact frozen declarations and pre-code original-source gates

CORRECT / LEAN_FULLY_CHECKED for all exact component contracts below.

Exactly7 complete public theorem types and0definitions.

## Unit77

Pre-code freeze SHA256812bde497df39dbc34df18b83c976b14992b0b0585b63d95d6a30e4141f7ade4; independent ORIGINAL-source CORRECT
reportc04b2a693e15e9f4c349b7c35201ed8b35b5281adb8039b129af7f04ebadd2a5, FULLlead-read BEFOREimplementation.

```lean
import Shao.OQ5.P52.FixedLayerErasedNoiseEdges
import Shao.OQ5.P52.FixedLayerSampleStatistics

open MeasureTheory
open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem fixedSampleU_memLp_two_fixedErasedLaw
    (j n : ℕ) (hn : 3 ≤ n) :
    MemLp (fun x : Fin n → LayerObs => fixedSampleU x) 2
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j))

theorem integrable_fixedSampleStudentizerSq_fixedErasedLaw
    (j n : ℕ) (hn : 3 ≤ n) :
    Integrable (fun x : Fin n → LayerObs => fixedSampleStudentizerSq x)
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j))

theorem integral_fixedSampleU_fixedErasedLaw_eq_zero
    (j n : ℕ) (hn : 3 ≤ n) :
    (∫ x : Fin n → LayerObs, fixedSampleU x
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0

theorem integral_fixedSampleU_scaled_sq_fixedErasedLaw
    (j n : ℕ) (hn : 3 ≤ n) :
    (∫ x : Fin n → LayerObs, (n : ℝ) * (fixedSampleU x) ^ 2
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      (4 / 3 : ℝ) + (2 / ((n : ℝ) - 1)) *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j))

theorem integral_fixedSampleStudentizerSq_fixedErasedLaw
    (j n : ℕ) (hn : 3 ≤ n) :
    (∫ x : Fin n → LayerObs, fixedSampleStudentizerSq x
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      (4 / 3 : ℝ) + (4 / ((n : ℝ) - 2)) *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j))

end
end Shao.OQ5.P52
```

## Unit78

Pre-code freeze SHA2561f4a08a83394ff68446beea757e2121d9fa44ab0e211ead637d828f9e96138e7; independent ORIGINAL-source CORRECT
reportf12b43e7cfdaa55cee3ddafb2a97b583f90f131bb391759a81dd2a5e6730ddff, FULLlead-read BEFOREimplementation.

```lean
import Shao.OQ5.P52.FixedLayerErasedMixture
import Shao.OQ5.P52.FixedLayerSampleStatistics

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem fixedSampleU_fixedLayerRareEvent_cond_ae_eq (j : ℕ) :
    (fun ω : ℕ → LayerObs =>
      fixedSampleU (fun i : Fin (fixedLayerN j) =>
        fixedSampleCoordinate i.val ω))
      =ᵐ[ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)]
        (fun ω : ℕ → LayerObs =>
          fixedSampleU (fun i : Fin (fixedLayerN j) =>
            fixedEraseLayer j (fixedSampleCoordinate i.val ω)) +
          (2 * fixedLayerT j) / ((fixedLayerN j : ℝ) - 1))

theorem fixedSampleStudentizerSq_fixedLayerRareEvent_cond_ae_eq (j : ℕ) :
    (fun ω : ℕ → LayerObs =>
      fixedSampleStudentizerSq (fun i : Fin (fixedLayerN j) =>
        fixedSampleCoordinate i.val ω))
      =ᵐ[ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)]
        (fun ω : ℕ → LayerObs =>
          fixedSampleStudentizerSq (fun i : Fin (fixedLayerN j) =>
            fixedEraseLayer j (fixedSampleCoordinate i.val ω)))

end
end Shao.OQ5.P52
```

Original p50de553dc827eeadbc1e863c1778caa9bdeb00bca84110b4666b06cab053d7b768;
p52615209f8501e14a6bfaee220899c30891510fef5987c9abf7f74ac52b6538b45.
Only generic P35 counting/mean/center is reused. Actual masked H/r, beta/product
and genuine original rare-event law are literal. Honest L1 before integration,
random sample centering, allj/n>=3 and exact coefficients are retained. Target
U shift2T/(N-1) and original R² invariance are conditional AE. Actual conditional
moment transport, trueR>0, ratios/tails and real coding remain OPEN.
