import Shao.C2.BridgeUpperAffineIdentification

noncomputable section
namespace Shao.C2.BridgeLowerIdentification
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.BridgeUpperAffineIdentification Shao.C2.SourceHalfLineCompletion

theorem ae_bridgeNoise_neg {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : BridgeTime, (bridgeNoise (-B) ω).val t = -(bridgeNoise B ω).val t := by
  filter_upwards [ae_bridgeNoise_eq B P hB, ae_bridgeNoise_eq (-B) P hB.neg] with ω hω hn
  intro t
  rw [hn t, hω t]
  change -(B ⟨(t : ℝ), t.property.1⟩ ω) - (t : ℝ) * (-B 1 ω) =
    -(B ⟨(t : ℝ), t.property.1⟩ ω - (t : ℝ) * B 1 ω)
  ring

theorem lowerCompletion_eq_upper_neg {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T z : ℝ) :
    lowerCompletion (bridgeLaw B P) a y T z =
      upperCompletion (bridgeLaw (-B) P) a (-y) T (-z) := by
  change ((P.map (bridgeNoise B)) (strictLower a y T z)).toReal =
    ((P.map (bridgeNoise (-B))) (strictUpper a (-y) T (-z))).toReal
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_bridgeNoise B P hB)
    (measurableSet_strictLower a y T z),
    Measure.map_apply_of_aemeasurable (aemeasurable_bridgeNoise (-B) P hB.neg)
      (measurableSet_strictUpper a (-y) T (-z))]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [ae_bridgeNoise_neg B P hB] with ω hω
  have hp (t : BridgeTime) :
      bridgePath (-y) T (-z) (bridgeNoise (-B) ω) t =
        -bridgePath y T z (bridgeNoise B ω) t := by
    change (1 - (t : ℝ)) * (-y) + (t : ℝ) * (-z) + Real.sqrt T *
      (bridgeNoise (-B) ω).val t =
      -((1 - (t : ℝ)) * y + (t : ℝ) * z + Real.sqrt T * (bridgeNoise B ω).val t)
    rw [hω t]
    ring
  apply propext
  change (∀ t : BridgeTime, -a < bridgePath y T z (bridgeNoise B ω) t) ↔
    ∀ t : BridgeTime, bridgePath (-y) T (-z) (bridgeNoise (-B) ω) t < a
  constructor
  · intro h t
    rw [hp t]
    linarith [h t]
  · intro h t
    have ht := h t
    rw [hp t] at ht
    linarith

theorem bridge_lower_formula {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T z : ℝ)
    (hT : 0 < T) (hy : -a < y) (hz : -a < z) :
    lowerCompletion (bridgeLaw B P) a y T z =
      1 - Real.exp (-2 * (a + y) * (a + z) / T) := by
  rw [lowerCompletion_eq_upper_neg B P hB a y T z]
  have h := bridge_upper_formula (-B) P hB.neg a (-y) T (-z) hT (by linarith) (by linarith)
  simpa only [sub_neg_eq_add] using h

theorem source_lower_eq_scalar {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a z : ℝ) (ha : 0 < a) (hz : -a < z) :
    (fun y T : ℝ => sourceLowerCompletion (bridgeLaw B P) a y T z) =
      (fun y T : ℝ => Shao.C2.HalfLinePhysicalGaussian.lowerCompletion a y T z) := by
  apply sourceLowerCompletion_eq_scalar_of_reflection (bridgeLaw B P) a z ha hz
  intro T hT y hy
  exact bridge_lower_formula B P hB a y T z hT hy hz

end Shao.C2.BridgeLowerIdentification
