# Frozen contracts — original conditional moment bounds and tail scales

The following two independently source-reviewed complete declaration blocks
were frozen BEFORE their corresponding implementations. Their original
freeze documents are retained at the exact hashes below; this document
reproduces every exact public type and definition body without weakening.

| Unit | Original freeze SHA256 | Never-author source gate SHA256 |
|---|---|---|
|81|f6bca8f4f3cde8db1c006beb7431c116152c02823c8e3e9aa1d9484220e84a35|da053eb39e3e8a55c647816cde470cc3d029e97c0575ecdc3dd811a6420772ab|
|83|b3d6e5f7febd76d05abecbc561384fcf184d6361b2512a45f650b0444cd87497|4fcfd2272fe17e3ac5ba7d2bf18ad0e7b738da43ff43497356016e6e0c2d4a26|

Original source p52.md SHA615209f8501e14a6bfaee220899c30891510fef5987c9abf7f74ac52b6538b45
and p50.md SHAde553dc827eeadbc1e863c1778caa9bdeb00bca84110b4666b06cab053d7b768.
Source reindexing J=j+6 and SAME fixed original full law/model are retained.

## Unit81 — complete frozen declaration block

```lean
import Shao.OQ5.P52.FixedLayerConditionalStatisticsMoments
import Shao.OQ5.P52.FixedLayerErasedVariance

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem fixedLayerRareNumeratorMean_ge (j : ℕ) :
    2 * (fixedLayerN j : ℝ) ^ (1 / 6 : ℝ) ≤
      (2 * fixedLayerT j * Real.sqrt (fixedLayerN j : ℝ)) /
        ((fixedLayerN j : ℝ) - 1)

theorem integral_fixedSampleNumerator_centered_sq_fixedLayerRareEvent_cond_le (j : ℕ) :
    (∫ ω : ℕ → LayerObs,
      (Real.sqrt (fixedLayerN j : ℝ) *
          fixedSampleU (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω) -
        (2 * fixedLayerT j * Real.sqrt (fixedLayerN j : ℝ)) /
          ((fixedLayerN j : ℝ) - 1)) ^ 2
      ∂ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) ≤
      (4 / 3 : ℝ) + 4 *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂fixedObservationLaw.prod fixedObservationLaw)

theorem integral_fixedSampleStudentizerSq_fixedLayerRareEvent_cond_le (j : ℕ) :
    (∫ ω : ℕ → LayerObs,
      fixedSampleStudentizerSq
        (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)
      ∂ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) ≤
      (4 / 3 : ℝ) + 4 *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂fixedObservationLaw.prod fixedObservationLaw)

end
end Shao.OQ5.P52
```

## Unit83 — complete frozen declaration block

```lean
import Shao.OQ5.P52.FixedLayerGrowth
import Shao.OQ5.P52.FixedLayerCostScales

open Filter
open scoped Topology

namespace Shao.OQ5.P52

noncomputable section

def fixedLayerTailThreshold (n : ℕ) : ℝ :=
  (n : ℝ) ^ (1 / 6 : ℝ) / Real.log (n : ℝ)

theorem fixedLayerTailThreshold_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < fixedLayerTailThreshold n

theorem fixedLayerTailThreshold_tendsto :
    Tendsto fixedLayerTailThreshold atTop atTop

theorem fixedLayerTailThreshold_div_sixth_tendsto_zero :
    Tendsto (fun n : ℕ => fixedLayerTailThreshold n / (n : ℝ) ^ (1 / 6 : ℝ))
      atTop (nhds 0)

theorem fixedLayerTailThreshold_div_sqrt_tendsto_zero :
    Tendsto (fun n : ℕ => fixedLayerTailThreshold n / Real.sqrt (n : ℝ))
      atTop (nhds 0)

theorem fixedLayerTailThreshold_cost_identity (j : ℕ) :
    (fixedLayerN j : ℝ) ^ fixedLayerTau j /
        (fixedLayerTailThreshold (fixedLayerN j)) ^ 2 =
      (fixedLayerN j : ℝ) ^ (-1 / ((j + 6 : ℕ) : ℝ)) *
        (Real.log (fixedLayerN j : ℝ)) ^ 2

theorem fixedLayerTailThreshold_cost_tendsto_zero :
    Tendsto (fun j : ℕ =>
      (fixedLayerN j : ℝ) ^ fixedLayerTau j /
        (fixedLayerTailThreshold (fixedLayerN j)) ^ 2) atTop (nhds 0)

theorem fixedLayer_N_mul_Q_tendsto_zero :
    Tendsto (fun j : ℕ => (fixedLayerN j : ℝ) * fixedLayerQ j) atTop (nhds 0)

theorem fixedLayer_N_mul_P_add_Q_tendsto_zero :
    Tendsto (fun j : ℕ =>
      (fixedLayerN j : ℝ) * (fixedLayerP j + fixedLayerQ j)) atTop (nhds 0)

theorem fixedLayer_conditional_error_scale_tendsto_zero :
    Tendsto (fun j : ℕ =>
      (fixedLayerN j : ℝ) ^ (-1 / 3 : ℝ) +
        1 / (Real.log (fixedLayerN j : ℝ)) ^ 2) atTop (nhds 0)

end
end Shao.OQ5.P52
```

The exact source types carry no new moment/probability/independence premise.
Unit81 uses the actual nonzero conditional mean and same original rho².
Unit83 is deterministic and distinguishes full-n threshold from actual fixed
layer subsequences; it never asserts positivity atn0/1. Honest original
conditional integrability belongs to accepted79 before the81 bounds. Actual
64 bounds erased variance by the honest original residual-square moment.

This freeze is scoped to12theorems and1definition. No source root, probability
floor, actual T-tail, log/relative failure or real observation transfer is
asserted by these declarations alone. Fullp52/p53/OQ6/RS2 remain OPEN.
