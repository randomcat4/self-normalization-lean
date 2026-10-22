# Original fixed p52 tail chain — frozen public contracts

The package contains four new production modules and exactly22 public theorem targets plus2 public definitions. It stacks on frozen PR115/head286ffc261cae0f8c3c8bbc3c0997eff409dcdf75. Complete p52/p53/OQ6/RS2 remain OPEN. Real sample87/statistics88/projection89 are excluded.

The following declarations preserve their original preimplementation freezes. A theorem target is counted once regardless of conjunctions; private/generated/audit constants do not enter the public target count. Definitions are recorded separately.

## Shao.OQ5.P52.FixedLayerConditionalConcentration

Original freeze SHA256 `a4d05f37adeb89e1328314517d62a1e2fb767b5b6633226bfb8e954f2572b049`. Public theorem targets3; public definitions0.

```lean
import Shao.OQ5.P52.FixedLayerConditionalMomentBounds
import Shao.OQ5.P52.FixedLayerPositiveStudentizer

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem fixedLayerRareEvent_cond_numerator_small_probability (j : ℕ) :
    (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)).real
      {ω : ℕ → LayerObs |
        Real.sqrt (fixedLayerN j : ℝ) *
            fixedSampleU (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω) <
          (fixedLayerN j : ℝ) ^ (1 / 6 : ℝ)} ≤
      ((4 / 3 : ℝ) + 4 *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂fixedObservationLaw.prod fixedObservationLaw)) *
        (fixedLayerN j : ℝ) ^ (-1 / 3 : ℝ)

theorem fixedLayerRareEvent_cond_studentizer_large_probability (j : ℕ) :
    (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)).real
      {ω : ℕ → LayerObs |
        Real.log (fixedLayerN j : ℝ) <
          fixedSampleStudentizer
            (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)} ≤
      ((4 / 3 : ℝ) + 4 *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂fixedObservationLaw.prod fixedObservationLaw)) /
        (Real.log (fixedLayerN j : ℝ)) ^ 2

theorem fixedLayerRareEvent_cond_good_probability_lower (j : ℕ) :
    1 - ((4 / 3 : ℝ) + 4 *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂fixedObservationLaw.prod fixedObservationLaw)) *
        ((fixedLayerN j : ℝ) ^ (-1 / 3 : ℝ) +
          1 / (Real.log (fixedLayerN j : ℝ)) ^ 2) ≤
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)).real
        {ω : ℕ → LayerObs |
          (fixedLayerN j : ℝ) ^ (1 / 6 : ℝ) ≤
              Real.sqrt (fixedLayerN j : ℝ) *
                fixedSampleU
                  (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω) ∧
          0 < fixedSampleStudentizer
              (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω) ∧
          fixedSampleStudentizer
              (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω) ≤
            Real.log (fixedLayerN j : ℝ)}

end
end Shao.OQ5.P52
```

## Shao.OQ5.P52.FixedLayerStudentizedTail

Original freeze SHA256 `845077e2e2939bf9e9380ac320a8ad06c19d406d4eb9c3e72bb20c124305ecd0`. Public theorem targets7; public definitions2.

```lean
import Shao.OQ5.P52.FixedLayerConditionalConcentration
import Shao.OQ5.P52.FixedLayerTailScales

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

def fixedSampleStudentized {n : ℕ} (x : Fin n → LayerObs) : ℝ :=
  Real.sqrt (n : ℝ) * fixedSampleU x / fixedSampleStudentizer x

def fixedSampleStudentizedTailProbability (n : ℕ) (x : ℝ) : ℝ :=
  fixedSampleLaw.real
    {ω : ℕ → LayerObs |
      x ≤ fixedSampleStudentized
        (fun i : Fin n => fixedSampleCoordinate i.val ω)}

theorem measurable_fixedSampleStudentized (n : ℕ) :
    Measurable (fun x : Fin n → LayerObs => fixedSampleStudentized x)

theorem measurable_fixedSampleStudentized_sample (n : ℕ) :
    Measurable (fun ω : ℕ → LayerObs =>
      fixedSampleStudentized (fun i : Fin n => fixedSampleCoordinate i.val ω))

theorem fixedSampleStudentizedTailProbability_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ fixedSampleStudentizedTailProbability n x

theorem fixedSampleStudentizedTailProbability_le_one (n : ℕ) (x : ℝ) :
    fixedSampleStudentizedTailProbability n x ≤ 1

theorem fixedSampleStudentized_ge_fixedLayerTailThreshold_of_good
    (j : ℕ) (x : Fin (fixedLayerN j) → LayerObs)
    (hU : (fixedLayerN j : ℝ) ^ (1 / 6 : ℝ) ≤
      Real.sqrt (fixedLayerN j : ℝ) * fixedSampleU x)
    (hR : 0 < fixedSampleStudentizer x)
    (hlog : fixedSampleStudentizer x ≤ Real.log (fixedLayerN j : ℝ)) :
    fixedLayerTailThreshold (fixedLayerN j) ≤ fixedSampleStudentized x

theorem fixedLayerRareEvent_cond_studentized_tail_probability_lower (j : ℕ) :
    1 - ((4 / 3 : ℝ) + 4 *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂fixedObservationLaw.prod fixedObservationLaw)) *
        ((fixedLayerN j : ℝ) ^ (-1 / 3 : ℝ) +
          1 / (Real.log (fixedLayerN j : ℝ)) ^ 2) ≤
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)).real
        {ω : ℕ → LayerObs |
          fixedLayerTailThreshold (fixedLayerN j) ≤
            fixedSampleStudentized
              (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)}

theorem fixedSampleStudentizedTailProbability_ge_fixedLayerRareEvent_mul (j : ℕ) :
    fixedSampleLaw.real (fixedLayerRareEvent j) *
      (1 - ((4 / 3 : ℝ) + 4 *
          (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
            ∂fixedObservationLaw.prod fixedObservationLaw)) *
          ((fixedLayerN j : ℝ) ^ (-1 / 3 : ℝ) +
            1 / (Real.log (fixedLayerN j : ℝ)) ^ 2)) ≤
      fixedSampleStudentizedTailProbability
        (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j))

end
end Shao.OQ5.P52
```

## Shao.OQ5.P52.FixedLayerRareMassAsymptotics

Original freeze SHA256 `4ee2e041c591e79e24fb96746866676acd0aeb9d4fd900f6158b4f85d1ecad33`. Public theorem targets4; public definitions0.

```lean
import Shao.OQ5.P52.FixedLayerRareEvents
import Shao.OQ5.P52.FixedLayerTailScales

open MeasureTheory Filter
open scoped Topology

namespace Shao.OQ5.P52

noncomputable section

theorem fixedLayerRare_survival_tendsto_one :
    Tendsto (fun j : ℕ =>
      (1 - fixedLayerP j - fixedLayerQ j) ^ (fixedLayerN j - 2))
      atTop (nhds 1)

theorem fixedLayerRareEvent_mass_ge_half_P_sq_eventually :
    ∀ᶠ j : ℕ in atTop,
      (1 / 2 : ℝ) * (fixedLayerP j) ^ 2 ≤
        fixedSampleLaw.real (fixedLayerRareEvent j)

theorem fixedLayerRareEvent_mass_ge_half_exp_eventually :
    ∀ᶠ j : ℕ in atTop,
      (1 / 2 : ℝ) * Real.exp
        (-2 * (fixedLayerN j : ℝ) ^ fixedLayerTau j) ≤
        fixedSampleLaw.real (fixedLayerRareEvent j)

theorem fixedLayerRareEvent_log_mass_asymptotic :
    Tendsto (fun j : ℕ =>
      Real.log (fixedSampleLaw.real (fixedLayerRareEvent j)) +
        2 * (fixedLayerN j : ℝ) ^ fixedLayerTau j -
        2 * Real.log (fixedLayerN j : ℝ) + Real.log 2)
      atTop (nhds 0)

end
end Shao.OQ5.P52
```

## Shao.OQ5.P52.FixedLayerTailLimits

Original freeze SHA256 `8103b6ea2a0bbf235ddbace49f218ba35ccce2d1788dd74326fbcbff59cf10b7`. Public theorem targets8; public definitions0.

```lean
import Shao.OQ5.P52.FixedLayerStudentizedTail
import Shao.OQ5.P52.FixedLayerRareMassAsymptotics
import Shao.OQ5.P35.GaussianTail

open Filter
open scoped Topology

namespace Shao.OQ5.P52

noncomputable section

theorem fixedSampleStudentizedTailProbability_ge_quarter_exp_eventually :
    ∀ᶠ j : ℕ in atTop,
      (1 / 4 : ℝ) * Real.exp
        (-2 * (fixedLayerN j : ℝ) ^ fixedLayerTau j) ≤
        fixedSampleStudentizedTailProbability
          (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j))

theorem fixedSampleStudentizedTailProbability_eventually_pos :
    ∀ᶠ j : ℕ in atTop,
      0 < fixedSampleStudentizedTailProbability
        (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j))

theorem fixedLayer_log_tail_ratio_tendsto_zero :
    Tendsto (fun j : ℕ =>
      Real.log (fixedSampleStudentizedTailProbability
          (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j))) /
        (-((fixedLayerTailThreshold (fixedLayerN j)) ^ 2) / 2))
      atTop (nhds 0)

theorem fixedLayer_relative_tail_ratio_tendsto_atTop :
    Tendsto (fun j : ℕ =>
      fixedSampleStudentizedTailProbability
          (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j)) /
        Shao.OQ5.P35.standardNormalUpperTail
          (fixedLayerTailThreshold (fixedLayerN j)))
      atTop atTop

theorem fixedLayer_full_log_tail_ratio_not_tendsto_one :
    ¬ Tendsto (fun n : ℕ =>
      Real.log (fixedSampleStudentizedTailProbability n (fixedLayerTailThreshold n)) /
        (-((fixedLayerTailThreshold n) ^ 2) / 2))
      atTop (nhds 1)

theorem fixedLayer_full_relative_tail_ratio_not_tendsto_one :
    ¬ Tendsto (fun n : ℕ =>
      fixedSampleStudentizedTailProbability n (fixedLayerTailThreshold n) /
        Shao.OQ5.P35.standardNormalUpperTail (fixedLayerTailThreshold n))
      atTop (nhds 1)

theorem fixedLayer_double_threshold_div_sixth_tendsto_zero :
    Tendsto (fun n : ℕ =>
      (2 * fixedLayerTailThreshold n) / (n : ℝ) ^ (1 / 6 : ℝ))
      atTop (nhds 0)

theorem fixedLayer_uniform_relative_tail_window_fails :
    ¬ (∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        ∀ x : ℝ, 0 ≤ x → x ≤ 2 * fixedLayerTailThreshold n →
          |fixedSampleStudentizedTailProbability n x /
            Shao.OQ5.P35.standardNormalUpperTail x - 1| ≤ ε)

end
end Shao.OQ5.P52
```
