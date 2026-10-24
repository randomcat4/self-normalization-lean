import Shao.C2.BrownianPathWeakMarkov

noncomputable section
namespace Shao.C2.BrownianBridgeProductKernel
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.PhysicalBrownianEndpointDensity Shao.C2.BrownianBridgeLawUniversality
open Shao.C2.BrownianKilledKernel Shao.C2.BrownianKilledAction
open Shao.C2.BrownianPathWeakMarkov Shao.C2.ScaledBrownianIdentity
open Shao.OQ4.PolygonalBrownianWeakLimit

def bridgeProductEndpointMeasure (ν : Measure BridgeNoise) (a y T : ℝ) : Measure ℝ :=
  ((ν.prod (gaussianReal 0 1)).restrict (scaledInitialSurvival a y T)).map
    (fun p : BridgeNoise × ℝ => y + Real.sqrt T * p.2)

private theorem physical_survival_iff_normalized {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (a y : ℝ) (T : ℝ≥0) (hT : T ≠ 0) (ω : Ω) :
    (∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a) ↔
      ∀ t : BridgeTime, |y + Real.sqrt (T : ℝ) *
        normalizedPhysicalBrownian B T ⟨(t : ℝ), t.property.1⟩ ω| < a := by
  have hTpos : 0 < (T : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hT : 0 < T)
  have hs : Real.sqrt (T : ℝ) ≠ 0 := (Real.sqrt_pos.2 hTpos).ne'
  have hrec (t : ℝ≥0) : Real.sqrt (T : ℝ) * normalizedPhysicalBrownian B T t ω = B (T * t) ω := by
    unfold normalizedPhysicalBrownian
    rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  constructor
  · intro h t
    rw [hrec ⟨(t : ℝ), t.property.1⟩]
    apply h
    let u : ℝ≥0 := ⟨(t : ℝ), t.property.1⟩
    have he : u ≤ 1 := by
      apply NNReal.coe_le_coe.mp
      change (t : ℝ) ≤ 1
      exact t.property.2
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left he (show (0 : ℝ≥0) ≤ T from zero_le)
  · intro h s hsT
    let t : BridgeTime := ⟨(s : ℝ) / (T : ℝ), div_nonneg s.property T.property,
      (div_le_one hTpos).2 (by exact_mod_cast hsT)⟩
    let u : ℝ≥0 := ⟨(t : ℝ), t.property.1⟩
    have heq : T * u = s := by
      apply NNReal.eq
      change (T : ℝ) * ((s : ℝ) / (T : ℝ)) = (s : ℝ)
      field_simp
    have ht := h t
    rw [hrec ⟨(t : ℝ), t.property.1⟩] at ht
    change |y + B (T * u) ω| < a at ht
    simpa only [heq] using ht

private theorem physical_survival_ae_bridgeProduct {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    {ω | ∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a} =ᵐ[P]
      (fun ω => (bridgeNoise (normalizedPhysicalBrownian B T) ω,
        normalizedPhysicalBrownian B T 1 ω)) ⁻¹' scaledInitialSurvival a y (T : ℝ) := by
  let C := normalizedPhysicalBrownian B T
  have hC := isBrownianReal_normalizedPhysicalBrownian B P hB T hT
  filter_upwards [ae_bridgeNoise_eq C P hC] with ω hω
  apply propext
  rw [physical_survival_iff_normalized B a y T hT ω]
  change (∀ t : BridgeTime, |y + Real.sqrt (T : ℝ) * C ⟨(t : ℝ), t.property.1⟩ ω| < a) ↔
    (bridgeNoise C ω, C 1 ω) ∈ scaledInitialSurvival a y (T : ℝ)
  rw [mem_scaledInitialSurvival_iff]
  have heq (t : BridgeTime) : bridgePath y (T : ℝ) (y + Real.sqrt (T : ℝ) * C 1 ω)
      (bridgeNoise C ω) t = y + Real.sqrt (T : ℝ) * C ⟨(t : ℝ), t.property.1⟩ ω := by
    simp only [bridgePath, ContinuousMap.coe_mk]
    rw [hω t]
    ring
  simp only [heq]

theorem actualIntervalKernel_eq_bridgeProductEndpointMeasure {Ω : Type*}
    [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    actualIntervalKernel B P a T y =
      bridgeProductEndpointMeasure (bridgeLaw B P) a y (T : ℝ) := by
  let C := normalizedPhysicalBrownian B T
  let J : Ω → BridgeNoise × ℝ := fun ω => (bridgeNoise C ω, C 1 ω)
  let E : BridgeNoise × ℝ → ℝ := fun p => y + Real.sqrt (T : ℝ) * p.2
  let S : Set Ω := {ω | ∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a}
  have hC := isBrownianReal_normalizedPhysicalBrownian B P hB T hT
  have hLaw : HasLaw J ((bridgeLaw B P).prod (gaussianReal 0 1)) P := by
    have hh := bridge_endpoint_hasLaw C P hC
    rw [bridgeLaw_normalizedPhysicalBrownian B P hB T hT] at hh
    exact hh
  have hE : Measurable E := by fun_prop
  have hSurv : S =ᵐ[P] J ⁻¹' scaledInitialSurvival a y (T : ℝ) :=
    physical_survival_ae_bridgeProduct B P hB a y T hT
  have hEnd (ω : Ω) : E (J ω) = y + B T ω := by
    have hTpos : 0 < (T : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hT : 0 < T)
    have hs : Real.sqrt (T : ℝ) ≠ 0 := (Real.sqrt_pos.2 hTpos).ne'
    dsimp only [E, J, C, normalizedPhysicalBrownian]
    rw [mul_one, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  calc
    actualIntervalKernel B P a T y = (P.restrict S).map (fun ω => y + B T ω) :=
      actualIntervalKernel_row_eq_map_restrict B P hB a y T hT
    _ = (P.restrict (J ⁻¹' scaledInitialSurvival a y (T : ℝ)) ).map (E ∘ J) := by
      rw [Measure.restrict_congr_set hSurv]
      apply Measure.map_congr
      exact Eventually.of_forall fun ω => (hEnd ω).symm
    _ = ((P.map J).restrict (scaledInitialSurvival a y (T : ℝ))).map E := by
      rw [Measure.restrict_map_of_aemeasurable hLaw.aemeasurable
        (measurableSet_scaledInitialSurvival a y (T : ℝ))]
      exact (AEMeasurable.map_map_of_aemeasurable hE.aemeasurable
        (hLaw.aemeasurable.mono_measure Measure.restrict_le_self)).symm
    _ = bridgeProductEndpointMeasure (bridgeLaw B P) a y (T : ℝ) := by
      rw [hLaw.map_eq]
      rfl

theorem bridgeProduct_initial_joint_real {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T : ℝ≥0) (hT : T ≠ 0)
    (A : Set ℝ) (hA : MeasurableSet A) :
    ((bridgeLaw B P).prod (gaussianReal 0 1)).real
      (scaledInitialSurvival a y (T : ℝ) ∩
        {p : BridgeNoise × ℝ | y + Real.sqrt (T : ℝ) * p.2 ∈ A}) =
      (actualIntervalKernel B P a T y).real A := by
  have hE : Measurable (fun p : BridgeNoise × ℝ => y + Real.sqrt (T : ℝ) * p.2) := by fun_prop
  rw [actualIntervalKernel_eq_bridgeProductEndpointMeasure B P hB a y T hT,
    bridgeProductEndpointMeasure]
  simp only [measureReal_def, Measure.map_apply hE hA, Measure.restrict_apply (hA.preimage hE)]
  congr 1
  congr 1
  ext p
  exact and_comm

theorem normalized_future_past_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T S : ℝ≥0) (hS : S ≠ 0) :
    HasLaw (fun ω =>
      ((bridgeNoise (normalizedPhysicalBrownian (fun t ω => B (T + t) ω - B T ω) S) ω,
        normalizedPhysicalBrownian (fun t ω => B (T + t) ω - B T ω) S 1 ω),
        brownianUnitPath B T ω))
      (((bridgeLaw B P).prod (gaussianReal 0 1)).prod (brownianUnitPathLaw B T P)) P := by
  let C := normalizedPhysicalBrownian (fun t ω => B (T + t) ω - B T ω) S
  have hC : IsBrownianReal C P :=
    isBrownianReal_normalizedPhysicalBrownian _ P (hB.shift T) S hS
  have hFuture : HasLaw (fun ω => (bridgeNoise C ω, C 1 ω))
      ((bridgeLaw B P).prod (gaussianReal 0 1)) P := by
    have hh := bridge_endpoint_hasLaw C P hC
    rw [bridgeLaw_eq_of_isBrownianReal C B P P hC hB] at hh
    exact hh
  have hPast : HasLaw (brownianUnitPath B T) (brownianUnitPathLaw B T P) P :=
    { aemeasurable := aemeasurable_brownianUnitPath B T P hB, map_eq := rfl }
  apply (indepFun_iff_hasLaw_prodMk_prod hFuture hPast).mp
  exact normalized_bridge_endpoint_indep_past B P hB T S hS

end Shao.C2.BrownianBridgeProductKernel
