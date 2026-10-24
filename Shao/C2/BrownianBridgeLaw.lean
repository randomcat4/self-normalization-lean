import Shao.C2.BridgeDomination
import Shao.OQ4.PolygonalBrownianWeakLimit

noncomputable section
namespace Shao.C2.BrownianBridgeLaw
open MeasureTheory ProbabilityTheory Set
open Shao.C2.BridgeDomination
open scoped NNReal

def leftWeight : C(BridgeTime, ℝ) :=
  ⟨fun t => 1 - (t : ℝ), by fun_prop⟩

def rightWeight : C(BridgeTime, ℝ) :=
  ⟨fun t => (t : ℝ), by fun_prop⟩

def pinPath (f : C(BridgeTime, ℝ)) : BridgeNoise :=
  ⟨f - f 0 • leftWeight - f 1 • rightWeight,
    by constructor <;> simp [leftWeight, rightWeight]⟩

def bridgeNoise {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : BridgeNoise :=
  pinPath (Shao.OQ4.PolygonalBrownianWeakLimit.brownianUnitPath B 1 ω)

def bridgeLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Measure BridgeNoise :=
  P.map (bridgeNoise B)

theorem continuous_pinPath : Continuous pinPath := by
  apply Continuous.subtype_mk
  change Continuous (fun f : C(BridgeTime, ℝ) =>
    f - f 0 • leftWeight - f 1 • rightWeight)
  fun_prop

theorem aemeasurable_bridgeNoise {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) : AEMeasurable (bridgeNoise B) P := by
  exact continuous_pinPath.measurable.comp_aemeasurable
    (Shao.OQ4.PolygonalBrownianWeakLimit.aemeasurable_brownianUnitPath B 1 P hB)

theorem isProbabilityMeasure_bridgeLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) : IsProbabilityMeasure (bridgeLaw B P) := by
  exact (Measure.isProbabilityMeasure_map_iff (aemeasurable_bridgeNoise B P hB)).mpr
    inferInstance

theorem ae_bridgeNoise_eq {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : BridgeTime,
      (bridgeNoise B ω).val t =
        B ⟨(t : ℝ), t.property.1⟩ ω - (t : ℝ) * B 1 ω := by
  filter_upwards
    [Shao.OQ4.PolygonalBrownianWeakLimit.ae_brownianUnitPath_eq B 1 P hB,
      hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hp hzero
  have hp' (u : BridgeTime) :
      Shao.OQ4.PolygonalBrownianWeakLimit.brownianUnitPath B 1 ω u =
        B ⟨(u : ℝ), u.property.1⟩ ω := by
    calc
      _ = B (1 * ⟨(u : ℝ), u.property.1⟩) ω := hp u
      _ = _ := congrArg (fun s : ℝ≥0 => B s ω) (one_mul _)
  have hz : Shao.OQ4.PolygonalBrownianWeakLimit.brownianUnitPath B 1 ω 0 = 0 := by
    rw [hp']
    change B 0 ω = 0
    exact hzero
  have ho : Shao.OQ4.PolygonalBrownianWeakLimit.brownianUnitPath B 1 ω 1 = B 1 ω := by
    rw [hp']
    rfl
  intro t
  change (Shao.OQ4.PolygonalBrownianWeakLimit.brownianUnitPath B 1 ω -
    Shao.OQ4.PolygonalBrownianWeakLimit.brownianUnitPath B 1 ω 0 • leftWeight -
    Shao.OQ4.PolygonalBrownianWeakLimit.brownianUnitPath B 1 ω 1 • rightWeight) t = _
  simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul,
    hp' t, hz, ho, leftWeight, rightWeight, ContinuousMap.coe_mk]
  ring

theorem actual_interval_completion {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T z : ℝ) :
    intervalCompletion (bridgeLaw B P) a y T z =
      P.real {ω | ∀ t : BridgeTime,
        |(1 - (t : ℝ)) * y + (t : ℝ) * z + Real.sqrt T *
          (B ⟨(t : ℝ), t.property.1⟩ ω - (t : ℝ) * B 1 ω)| < a} := by
  change ((P.map (bridgeNoise B)) (strictInterval a y T z)).toReal = _
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_bridgeNoise B P hB)
    (measurableSet_strictInterval a y T z)]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [ae_bridgeNoise_eq B P hB] with ω hω
  simp only [Set.mem_preimage, strictInterval, strictUpper, strictLower,
    Set.mem_inter_iff, Set.mem_ofPred_eq, bridgePath, ContinuousMap.coe_mk, hω]
  apply propext
  constructor
  · rintro ⟨hu, hl⟩ t
    exact abs_lt.mpr ⟨hl t, hu t⟩
  · intro h
    exact ⟨fun t => (abs_lt.mp (h t)).2, fun t => (abs_lt.mp (h t)).1⟩

theorem actual_initial_variation {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a : ℝ) :
    eVariationOn (fun w : ℝ => intervalCompletion (bridgeLaw B P) a 0 1 w) Set.univ ≤ 2 := by
  letI := isProbabilityMeasure_bridgeLaw B P hB
  exact initial_interval_variation (bridgeLaw B P) a

end Shao.C2.BrownianBridgeLaw
