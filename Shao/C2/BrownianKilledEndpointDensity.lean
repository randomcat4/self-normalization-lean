import Shao.C2.BrownianBridgeLawUniversality

noncomputable section
namespace Shao.C2.BrownianKilledEndpointDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.ScaledBrownianIdentity Shao.C2.BridgeCompletionGlobalContinuity
open Shao.C2.PhysicalBrownianEndpointDensity Shao.C2.BrownianBridgeLawUniversality
attribute [local instance] Classical.propDecidable

theorem standardGaussian_affine_hasLaw (y : ℝ) (T : ℝ≥0) :
    HasLaw (fun w : ℝ => y + Real.sqrt (T : ℝ) * w)
      (gaussianReal y T) (gaussianReal 0 1) := by
  constructor
  · change AEMeasurable (fun w : ℝ => y + Real.sqrt (T : ℝ) * w) (gaussianReal 0 1)
    exact (show Measurable (fun w : ℝ => y + Real.sqrt (T : ℝ) * w) by fun_prop).aemeasurable
  · have hvar : NNReal.mk (Real.sqrt (T : ℝ) ^ 2) (sq_nonneg _) * 1 = T := by
      apply NNReal.eq
      rw [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one]
      exact Real.sq_sqrt T.property
    calc
      (gaussianReal 0 1).map (fun w : ℝ => y + Real.sqrt (T : ℝ) * w) =
          ((gaussianReal 0 1).map (fun w : ℝ => Real.sqrt (T : ℝ) * w)).map (fun z => y + z) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = (gaussianReal 0 T).map (fun z => y + z) := by
        rw [gaussianReal_map_const_mul, hvar, mul_zero]
      _ = gaussianReal y T := by
        simpa only [zero_add] using gaussianReal_map_const_add (μ := 0) (v := T) y

private theorem product_real_section (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (S : Set (BridgeNoise × ℝ)) (hS : MeasurableSet S) :
    (ν.prod ρ).real S = ∫ w : ℝ, ν.real {g | (g, w) ∈ S} ∂ρ := by
  let F : BridgeNoise × ℝ → ℝ := S.indicator (fun _ => 1)
  have hF : Integrable F (ν.prod ρ) := (integrable_const 1).indicator hS
  calc
    (ν.prod ρ).real S = ∫ p, F p ∂(ν.prod ρ) := (integral_indicator_one hS).symm
    _ = ∫ w : ℝ, ∫ g : BridgeNoise, F (g, w) ∂ν ∂ρ := integral_prod_symm F hF
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun w => by
        have hsec : MeasurableSet {g : BridgeNoise | (g, w) ∈ S} :=
          hS.preimage (measurable_id.prodMk measurable_const)
        change (∫ g, ({g : BridgeNoise | (g, w) ∈ S}).indicator (fun _ => (1 : ℝ)) g ∂ν) = _
        exact integral_indicator_one hsec

private theorem product_scaled_initial_set
    (ν : Measure BridgeNoise) [IsProbabilityMeasure ν] (a y T : ℝ)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (ν.prod (gaussianReal 0 1)).real
      (scaledInitialSurvival a y T ∩ {p : BridgeNoise × ℝ | y + Real.sqrt T * p.2 ∈ A}) =
      ∫ w : ℝ, (if y + Real.sqrt T * w ∈ A then
        intervalCompletion ν a y T (y + Real.sqrt T * w) else 0) ∂(gaussianReal 0 1) := by
  classical
  let S : Set (BridgeNoise × ℝ) :=
    scaledInitialSurvival a y T ∩ {p : BridgeNoise × ℝ | y + Real.sqrt T * p.2 ∈ A}
  have hS : MeasurableSet S := (measurableSet_scaledInitialSurvival a y T).inter
    (hA.preimage (by fun_prop))
  change (ν.prod (gaussianReal 0 1)).real S = _
  rw [product_real_section ν (gaussianReal 0 1) S hS]
  apply integral_congr_ae
  exact Eventually.of_forall fun w => by
    change ν.real {g : BridgeNoise | (g, w) ∈ S} =
      (if y + Real.sqrt T * w ∈ A then intervalCompletion ν a y T (y + Real.sqrt T * w) else 0)
    by_cases hw : y + Real.sqrt T * w ∈ A
    · have hsec : {g : BridgeNoise | (g, w) ∈ S} =
          strictInterval a y T (y + Real.sqrt T * w) := by
        ext g
        simp only [S, Set.mem_setOf_eq, Set.mem_inter_iff, hw, and_true]
        rw [mem_scaledInitialSurvival_iff]
        change (∀ t : BridgeTime, |bridgePath y T (y + Real.sqrt T * w) g t| < a) ↔
          (∀ t : BridgeTime, bridgePath y T (y + Real.sqrt T * w) g t < a) ∧
            ∀ t : BridgeTime, -a < bridgePath y T (y + Real.sqrt T * w) g t
        simp only [abs_lt, forall_and, and_comm]
      rw [hsec, if_pos hw]
      rfl
    · have hsec : {g : BridgeNoise | (g, w) ∈ S} = ∅ := by
        ext g
        simp only [S, Set.mem_setOf_eq, Set.mem_inter_iff, hw, and_false, Set.mem_empty_iff_false]
      rw [hsec, measureReal_empty, if_neg hw]

private theorem brownian_scaled_initial_set {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    P.real {ω | (∀ t : BridgeTime,
      |y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧
        y + Real.sqrt T * B 1 ω ∈ A} =
      ∫ w : ℝ, (if y + Real.sqrt T * w ∈ A then
        intervalCompletion (bridgeLaw B P) a y T (y + Real.sqrt T * w) else 0)
          ∂(gaussianReal 0 1) := by
  classical
  letI := isProbabilityMeasure_bridgeLaw B P hB
  let S : Set (BridgeNoise × ℝ) :=
    scaledInitialSurvival a y T ∩ {p : BridgeNoise × ℝ | y + Real.sqrt T * p.2 ∈ A}
  have hS : MeasurableSet S := (measurableSet_scaledInitialSurvival a y T).inter
    (hA.preimage (by fun_prop))
  have hevent : {ω | (∀ t : BridgeTime,
      |y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧
        y + Real.sqrt T * B 1 ω ∈ A} =ᵐ[P]
      (fun ω => (bridgeNoise B ω, B 1 ω)) ⁻¹' S := by
    filter_upwards [ae_bridgeNoise_eq B P hB] with ω hω
    apply propext
    change ((∀ t : BridgeTime, |y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧
      y + Real.sqrt T * B 1 ω ∈ A) ↔
        ((bridgeNoise B ω, B 1 ω) ∈ scaledInitialSurvival a y T ∧ y + Real.sqrt T * B 1 ω ∈ A)
    apply and_congr _ Iff.rfl
    rw [mem_scaledInitialSurvival_iff]
    have heq (t : BridgeTime) : bridgePath y T (y + Real.sqrt T * B 1 ω) (bridgeNoise B ω) t =
        y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω := by
      simp only [bridgePath, ContinuousMap.coe_mk]
      rw [hω t]
      ring
    simp only [heq]
  calc
    _ = P.real ((fun ω => (bridgeNoise B ω, B 1 ω)) ⁻¹' S) := measureReal_congr hevent
    _ = ((bridgeLaw B P).prod (gaussianReal 0 1)).real S :=
      (bridge_endpoint_hasLaw B P hB).measureReal_eq hS
    _ = _ := product_scaled_initial_set (bridgeLaw B P) a y T A hA

private theorem physical_joint_event_eq_scaled {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (a y : ℝ) (T : ℝ≥0) (hT : T ≠ 0) (A : Set ℝ) :
    {ω | (∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a) ∧ y + B T ω ∈ A} =
      {ω | (∀ t : BridgeTime, |y + Real.sqrt (T : ℝ) *
        normalizedPhysicalBrownian B T ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧
          y + Real.sqrt (T : ℝ) * normalizedPhysicalBrownian B T 1 ω ∈ A} := by
  have hTpos : 0 < (T : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hT : 0 < T)
  have hs : Real.sqrt (T : ℝ) ≠ 0 := (Real.sqrt_pos.2 hTpos).ne'
  have hrec (t : ℝ≥0) (ω : Ω) :
      Real.sqrt (T : ℝ) * normalizedPhysicalBrownian B T t ω = B (T * t) ω := by
    unfold normalizedPhysicalBrownian
    rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  ext ω
  change ((∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a) ∧ y + B T ω ∈ A) ↔
    ((∀ t : BridgeTime, |y + Real.sqrt (T : ℝ) *
      normalizedPhysicalBrownian B T ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧
        y + Real.sqrt (T : ℝ) * normalizedPhysicalBrownian B T 1 ω ∈ A)
  rw [hrec 1 ω, mul_one]
  apply and_congr _ Iff.rfl
  constructor
  · intro h t
    rw [hrec ⟨(t : ℝ), t.property.1⟩ ω]
    apply h
    have hh : (T : ℝ) * (t : ℝ) ≤ (T : ℝ) := by nlinarith [t.property.2]
    exact_mod_cast hh
  · intro h s hsT
    let t : BridgeTime := ⟨(s : ℝ) / (T : ℝ), div_nonneg s.property T.property,
      (div_le_one hTpos).2 (by exact_mod_cast hsT)⟩
    let u : ℝ≥0 := ⟨(t : ℝ), t.property.1⟩
    have heq : T * u = s := by
      apply NNReal.eq
      change (T : ℝ) * ((s : ℝ) / (T : ℝ)) = (s : ℝ)
      field_simp
    have ht := h t
    rw [hrec ⟨(t : ℝ), t.property.1⟩ ω] at ht
    change |y + B (T * u) ω| < a at ht
    simpa only [heq] using ht

theorem integrable_killed_density {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    Integrable (fun z : ℝ => gaussianPDFReal y T z *
      intervalCompletion (bridgeLaw B P) a y (T : ℝ) z) := by
  letI : IsProbabilityMeasure (bridgeLaw B P) := isProbabilityMeasure_bridgeLaw B P hB
  have hTpos : 0 < (T : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hT : 0 < T)
  have hf := bridge_interval_continuous_endpoint B P hB a y (T : ℝ) hTpos
  have hc : Continuous (fun z : ℝ => gaussianPDFReal y T z *
      intervalCompletion (bridgeLaw B P) a y (T : ℝ) z) := by
    apply Continuous.mul _ hf
    unfold gaussianPDFReal
    fun_prop
  apply (integrable_gaussianPDFReal y T).mono' hc.aestronglyMeasurable
  filter_upwards [] with z
  have hp := gaussianPDFReal_nonneg y T z
  have hb := (completion_bounds (bridgeLaw B P) a y (T : ℝ) z).2.2.2.2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp hb.1)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hb.2 hp

theorem brownian_physical_interval_joint_eq_integral {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T : ℝ≥0) (hT : T ≠ 0)
    (A : Set ℝ) (hA : MeasurableSet A) :
    P.real {ω | (∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a) ∧ y + B T ω ∈ A} =
      ∫ z : ℝ in A, gaussianPDFReal y T z *
        intervalCompletion (bridgeLaw B P) a y (T : ℝ) z := by
  classical
  have hTpos : 0 < (T : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hT : 0 < T)
  have hC := isBrownianReal_normalizedPhysicalBrownian B P hB T hT
  rw [physical_joint_event_eq_scaled B a y T hT A,
    brownian_scaled_initial_set (normalizedPhysicalBrownian B T) P hC a y (T : ℝ) A hA,
    bridgeLaw_normalizedPhysicalBrownian B P hB T hT]
  let f : ℝ → ℝ := fun z => intervalCompletion (bridgeLaw B P) a y (T : ℝ) z
  have hf : Continuous f := bridge_interval_continuous_endpoint B P hB a y (T : ℝ) hTpos
  have hInd : AEStronglyMeasurable (A.indicator f) (gaussianReal y T) :=
    (hf.stronglyMeasurable.indicator hA).aestronglyMeasurable
  calc
    _ = ∫ w : ℝ, (A.indicator f) (y + Real.sqrt (T : ℝ) * w) ∂(gaussianReal 0 1) := rfl
    _ = ∫ z : ℝ, (A.indicator f) z ∂(gaussianReal y T) :=
      (standardGaussian_affine_hasLaw y T).integral_comp hInd
    _ = ∫ z : ℝ, gaussianPDFReal y T z * (A.indicator f) z := by
      simpa only [smul_eq_mul] using
        (integral_gaussianReal_eq_integral_smul (μ := y) (v := T) (f := A.indicator f) hT)
    _ = ∫ z : ℝ, A.indicator (fun z => gaussianPDFReal y T z * f z) z := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        by_cases hz : z ∈ A <;> simp [hz]
    _ = _ := integral_indicator hA

end Shao.C2.BrownianKilledEndpointDensity
