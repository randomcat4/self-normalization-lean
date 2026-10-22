# Exact complete frozen public contracts

All complete independent FINAL79/80 gates and full lead-read accepted.
No source edits authorized; original freezes and stopped bytes immutable.

## Unit79

Freeze SHA256 133cc40b1527a41b1d23b5f2b493255808232a3b7ed0bbbb708a59e851842386; pre-code ORIGINAL-source review SHA256 c2a9911d52ce7a6abb1a5e59a575b201bb7a978a8af1589620da29a15ca925bc.

```lean
import Shao.OQ5.P52.FixedLayerErasedStatisticsMoments
import Shao.OQ5.P52.FixedLayerRareStatistics

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem fixedSampleU_memLp_two_fixedLayerRareEvent_cond (j : ℕ) :
    MemLp (fun ω : ℕ → LayerObs =>
      fixedSampleU (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)) 2
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j))

theorem integrable_fixedSampleStudentizerSq_fixedLayerRareEvent_cond (j : ℕ) :
    Integrable (fun ω : ℕ → LayerObs =>
      fixedSampleStudentizerSq
        (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω))
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j))

theorem integral_fixedSampleNumerator_fixedLayerRareEvent_cond (j : ℕ) :
    (∫ ω : ℕ → LayerObs,
      Real.sqrt (fixedLayerN j : ℝ) *
        fixedSampleU (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)
      ∂ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) =
      (2 * fixedLayerT j * Real.sqrt (fixedLayerN j : ℝ)) /
        ((fixedLayerN j : ℝ) - 1)

theorem integral_fixedSampleNumerator_centered_sq_fixedLayerRareEvent_cond (j : ℕ) :
    (∫ ω : ℕ → LayerObs,
      (Real.sqrt (fixedLayerN j : ℝ) *
          fixedSampleU (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω) -
        (2 * fixedLayerT j * Real.sqrt (fixedLayerN j : ℝ)) /
          ((fixedLayerN j : ℝ) - 1)) ^ 2
      ∂ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) =
      (4 / 3 : ℝ) + (2 / ((fixedLayerN j : ℝ) - 1)) *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j))

theorem integral_fixedSampleStudentizerSq_fixedLayerRareEvent_cond (j : ℕ) :
    (∫ ω : ℕ → LayerObs,
      fixedSampleStudentizerSq
        (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)
      ∂ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) =
      (4 / 3 : ℝ) + (4 / ((fixedLayerN j : ℝ) - 2)) *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j))

end
end Shao.OQ5.P52
```

## Unit80

Freeze SHA256 4cac38865d130c49739e0b97b00d0f25cca9cde6b64a0f8ad5e2cdeed9a0443e; pre-code ORIGINAL-source review SHA256 e8b19be6d734e9a13960dced913eb234ac53647124d4870b1b0377ccb6f8d8b7.

```lean
import Shao.OQ5.P52.FixedLayerErasedMixture
import Shao.OQ5.P52.FixedLayerSampleStatistics

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

def fixedSampleStudentizer {n : ℕ} (x : Fin n → LayerObs) : ℝ :=
  Real.sqrt (fixedSampleStudentizerSq x)

theorem fixedSampleStudentizer_nonneg
    {n : ℕ} (x : Fin n → LayerObs) :
    0 ≤ fixedSampleStudentizer x

theorem fixedSampleStudentizer_sq
    (n : ℕ) (hn : 3 ≤ n) (x : Fin n → LayerObs) :
    (fixedSampleStudentizer x) ^ 2 = fixedSampleStudentizerSq x

theorem fixedSampleStudentizer_pos_ae
    (n : ℕ) (hn : 3 ≤ n) :
    ∀ᵐ x : Fin n → LayerObs
      ∂Measure.pi (fun _ : Fin n => fixedObservationLaw),
      0 < fixedSampleStudentizer x

theorem fixedSampleStudentizer_prefix_pos_ae
    (n : ℕ) (hn : 3 ≤ n) :
    ∀ᵐ ω : ℕ → LayerObs ∂fixedSampleLaw,
      0 < fixedSampleStudentizer
        (fun i : Fin n => fixedSampleCoordinate i.val ω)

theorem fixedSampleStudentizer_fixedLayerRareEvent_cond_pos_ae (j : ℕ) :
    ∀ᵐ ω : ℕ → LayerObs
      ∂ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j),
      0 < fixedSampleStudentizer
        (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)

end
end Shao.OQ5.P52
```
