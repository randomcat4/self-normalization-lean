import Shao.C2.BrownianBridgeProductKernel

noncomputable section
namespace Shao.C2.BrownianSurvivalSplit
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.PhysicalBrownianEndpointDensity Shao.C2.ScaledBrownianIdentity
open Shao.C2.BrownianBridgeProductKernel
open Shao.OQ4.PolygonalBrownianWeakLimit

def splitSurvivalEvent (a y S : ℝ) (A : Set ℝ) :
    Set ((BridgeNoise × ℝ) × C(BridgeTime, ℝ)) :=
  {p | ‖ContinuousMap.const BridgeTime y + p.2‖ < a ∧
    p.1 ∈ scaledInitialSurvival a (y + p.2 1) S ∧
      y + p.2 1 + Real.sqrt S * p.1.2 ∈ A}

private theorem unit_survival_iff_physical (Z : ℝ≥0 → ℝ) (a : ℝ)
    (U : ℝ≥0) (hU : U ≠ 0) :
    (∀ s : ℝ≥0, s ≤ U → |Z s| < a) ↔
      ∀ t : BridgeTime, |Z (U * ⟨(t : ℝ), t.property.1⟩)| < a := by
  have hUpos : 0 < (U : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hU : 0 < U)
  constructor
  · intro h t
    apply h
    let u : ℝ≥0 := ⟨(t : ℝ), t.property.1⟩
    change U * u ≤ U
    have he : u ≤ 1 := by
      apply NNReal.coe_le_coe.mp
      change (t : ℝ) ≤ 1
      exact t.property.2
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left he (show (0 : ℝ≥0) ≤ U from zero_le)
  · intro h s hsU
    let t : BridgeTime := ⟨(s : ℝ) / (U : ℝ), div_nonneg s.property U.property,
      (div_le_one hUpos).2 (by exact_mod_cast hsU)⟩
    let u : ℝ≥0 := ⟨(t : ℝ), t.property.1⟩
    have heq : U * u = s := by
      apply NNReal.eq
      change (U : ℝ) * ((s : ℝ) / (U : ℝ)) = (s : ℝ)
      field_simp
    have ht := h t
    change |Z (U * u)| < a at ht
    simpa only [heq] using ht

theorem physical_survival_split {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (a y : ℝ)
    (T S : ℝ≥0) (ω : Ω) :
    (∀ s : ℝ≥0, s ≤ T + S → |y + B s ω| < a) ↔
      (∀ t : ℝ≥0, t ≤ T → |y + B t ω| < a) ∧
        ∀ u : ℝ≥0, u ≤ S → |y + B (T + u) ω| < a := by
  constructor
  · intro h
    constructor
    · intro t ht
      exact h t (ht.trans (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ S from zero_le)))
    · intro u hu
      exact h (T + u) (add_le_add le_rfl hu)
  · rintro ⟨hPast, hFuture⟩ s hs
    by_cases hsT : s ≤ T
    · exact hPast s hsT
    · have hTs : T ≤ s := (lt_of_not_ge hsT).le
      let u : ℝ≥0 := ⟨(s : ℝ) - (T : ℝ), sub_nonneg.mpr (by exact_mod_cast hTs)⟩
      have hu : u ≤ S := by
        apply NNReal.coe_le_coe.mp
        change (s : ℝ) - (T : ℝ) ≤ (S : ℝ)
        have hs' : (s : ℝ) ≤ (T : ℝ) + (S : ℝ) := by exact_mod_cast hs
        linarith
      have heq : T + u = s := by
        apply NNReal.eq
        change (T : ℝ) + ((s : ℝ) - (T : ℝ)) = (s : ℝ)
        ring
      simpa only [heq] using hFuture u hu

theorem measurableSet_splitSurvivalEvent (a y S : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    MeasurableSet (splitSurvivalEvent a y S A) := by
  have hp : Continuous (fun p : (BridgeNoise × ℝ) × C(BridgeTime, ℝ) =>
      ContinuousMap.const BridgeTime y + p.2) :=
    continuous_const.add continuous_snd
  have hx : Continuous (fun p : (BridgeNoise × ℝ) × C(BridgeTime, ℝ) => y + p.2 1) := by fun_prop
  have hz : Continuous (fun p : (BridgeNoise × ℝ) × C(BridgeTime, ℝ) =>
      y + p.2 1 + Real.sqrt S * p.1.2) := by fun_prop
  have hg : Continuous (fun p : (BridgeNoise × ℝ) × C(BridgeTime, ℝ) => p.1.1.val) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  have hf : Continuous (fun p : (BridgeNoise × ℝ) × C(BridgeTime, ℝ) => (y + p.2 1) • leftWeight +
      (y + p.2 1 + Real.sqrt S * p.1.2) • rightWeight + Real.sqrt S • p.1.1.val) :=
    ((hx.smul continuous_const).add (hz.smul continuous_const)).add (hg.const_smul (Real.sqrt S))
  exact ((isOpen_lt hp.norm continuous_const).measurableSet).inter
    (((isOpen_lt hf.norm continuous_const).measurableSet).inter (hA.preimage hz.measurable))

private theorem actual_joint_ae_splitSurvivalEvent {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T S : ℝ≥0) (hT : T ≠ 0) (hS : S ≠ 0)
    (A : Set ℝ) :
    {ω | (∀ s : ℝ≥0, s ≤ T + S → |y + B s ω| < a) ∧ y + B (T + S) ω ∈ A} =ᵐ[P]
      (fun ω =>
        ((bridgeNoise (normalizedPhysicalBrownian (fun t ω => B (T + t) ω - B T ω) S) ω,
          normalizedPhysicalBrownian (fun t ω => B (T + t) ω - B T ω) S 1 ω),
          brownianUnitPath B T ω)) ⁻¹' splitSurvivalEvent a y (S : ℝ) A := by
  let C := normalizedPhysicalBrownian (fun t ω => B (T + t) ω - B T ω) S
  have hC : IsBrownianReal C P :=
    isBrownianReal_normalizedPhysicalBrownian _ P (hB.shift T) S hS
  have hSpos : 0 < (S : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hS : 0 < S)
  have hsqrt : Real.sqrt (S : ℝ) ≠ 0 := (Real.sqrt_pos.2 hSpos).ne'
  filter_upwards [ae_brownianUnitPath_eq B T P hB, ae_bridgeNoise_eq C P hC] with ω hp hb
  have hp' (t : BridgeTime) : brownianUnitPath B T ω t =
      B (T * ⟨(t : ℝ), t.property.1⟩) ω := hp t
  have hp1 : brownianUnitPath B T ω 1 = B T ω := by
    rw [hp']
    change B (T * 1) ω = B T ω
    rw [mul_one]
  have hrec (u : ℝ≥0) : Real.sqrt (S : ℝ) * C u ω =
      B (T + S * u) ω - B T ω := by
    dsimp only [C, normalizedPhysicalBrownian]
    rw [← mul_assoc, mul_inv_cancel₀ hsqrt, one_mul]
  have hend : y + brownianUnitPath B T ω 1 + Real.sqrt (S : ℝ) * C 1 ω =
      y + B (T + S) ω := by
    rw [hp1, hrec, mul_one]
    ring
  have hpath (t : BridgeTime) :
      bridgePath (y + brownianUnitPath B T ω 1) (S : ℝ)
        (y + brownianUnitPath B T ω 1 + Real.sqrt (S : ℝ) * C 1 ω)
        (bridgeNoise C ω) t = y + B (T + S * ⟨(t : ℝ), t.property.1⟩) ω := by
    have hre := hrec ⟨(t : ℝ), t.property.1⟩
    simp only [bridgePath, ContinuousMap.coe_mk]
    rw [hb t, hp1]
    calc
      _ = y + B T ω + Real.sqrt (S : ℝ) * C ⟨(t : ℝ), t.property.1⟩ ω := by ring
      _ = _ := by linarith only [hre]
  have hpast : (∀ t : ℝ≥0, t ≤ T → |y + B t ω| < a) ↔
      ‖ContinuousMap.const BridgeTime y + brownianUnitPath B T ω‖ < a := by
    rw [unit_survival_iff_physical (fun t => y + B t ω) a T hT,
      ContinuousMap.norm_lt_iff_of_nonempty]
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, Real.norm_eq_abs, hp']
  have hfuture : (∀ u : ℝ≥0, u ≤ S → |y + B (T + u) ω| < a) ↔
      (bridgeNoise C ω, C 1 ω) ∈
        scaledInitialSurvival a (y + brownianUnitPath B T ω 1) (S : ℝ) := by
    rw [unit_survival_iff_physical (fun u => y + B (T + u) ω) a S hS,
      mem_scaledInitialSurvival_iff]
    simp only [hpath]
  apply propext
  change ((∀ s : ℝ≥0, s ≤ T + S → |y + B s ω| < a) ∧ y + B (T + S) ω ∈ A) ↔
    (‖ContinuousMap.const BridgeTime y + brownianUnitPath B T ω‖ < a ∧
      (bridgeNoise C ω, C 1 ω) ∈ scaledInitialSurvival a (y + brownianUnitPath B T ω 1) (S : ℝ) ∧
        y + brownianUnitPath B T ω 1 + Real.sqrt (S : ℝ) * C 1 ω ∈ A)
  rw [physical_survival_split B a y T S ω, hpast, hfuture, hend]
  exact and_assoc

theorem brownian_split_event_probability {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T S : ℝ≥0) (hT : T ≠ 0) (hS : S ≠ 0)
    (A : Set ℝ) (hA : MeasurableSet A) :
    P.real {ω | (∀ s : ℝ≥0, s ≤ T + S → |y + B s ω| < a) ∧ y + B (T + S) ω ∈ A} =
      (((bridgeLaw B P).prod (gaussianReal 0 1)).prod (brownianUnitPathLaw B T P)).real
        (splitSurvivalEvent a y (S : ℝ) A) := by
  have hevent := actual_joint_ae_splitSurvivalEvent B P hB a y T S hT hS A
  calc
    _ = P.real ((fun ω =>
        ((bridgeNoise (normalizedPhysicalBrownian (fun t ω => B (T + t) ω - B T ω) S) ω,
          normalizedPhysicalBrownian (fun t ω => B (T + t) ω - B T ω) S 1 ω),
          brownianUnitPath B T ω)) ⁻¹' splitSurvivalEvent a y (S : ℝ) A) :=
      measureReal_congr hevent
    _ = _ := (normalized_future_past_hasLaw B P hB T S hS).measureReal_eq
      (measurableSet_splitSurvivalEvent a y (S : ℝ) A hA)

end Shao.C2.BrownianSurvivalSplit
