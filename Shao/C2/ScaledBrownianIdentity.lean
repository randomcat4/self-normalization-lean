import Shao.C2.InitialBrownianIdentity
import Shao.C2.BridgeIntervalEndpointDensity

noncomputable section
namespace Shao.C2.ScaledBrownianIdentity
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw

def scaledInitialSurvival (a y T : ℝ) : Set (BridgeNoise × ℝ) :=
  {p | ‖y • leftWeight + (y + Real.sqrt T * p.2) • rightWeight + Real.sqrt T • p.1.val‖ < a}

theorem mem_scaledInitialSurvival_iff (a y T : ℝ) (g : BridgeNoise) (w : ℝ) :
    (g, w) ∈ scaledInitialSurvival a y T ↔
      ∀ t : BridgeTime, |bridgePath y T (y + Real.sqrt T * w) g t| < a := by
  change ‖y • leftWeight + (y + Real.sqrt T * w) • rightWeight + Real.sqrt T • g.val‖ < a ↔ _
  rw [ContinuousMap.norm_lt_iff_of_nonempty]
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul,
    leftWeight, rightWeight, ContinuousMap.coe_mk, bridgePath, Real.norm_eq_abs]
  apply forall_congr'
  intro t
  congr 1
  ring

theorem measurableSet_scaledInitialSurvival (a y T : ℝ) :
    MeasurableSet (scaledInitialSurvival a y T) := by
  have hg : Continuous (fun p : BridgeNoise × ℝ => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hw : Continuous (fun p : BridgeNoise × ℝ => y + Real.sqrt T * p.2) :=
    continuous_const.add (continuous_const.mul continuous_snd)
  have hs : Continuous (fun p : BridgeNoise × ℝ => Real.sqrt T • p.1.val) :=
    hg.const_smul (Real.sqrt T)
  have hc : Continuous (fun p : BridgeNoise × ℝ =>
      y • leftWeight + (y + Real.sqrt T * p.2) • rightWeight + Real.sqrt T • p.1.val) :=
    (continuous_const.add (hw.smul continuous_const)).add hs
  exact (isOpen_lt hc.norm continuous_const).measurableSet

private theorem product_real_section
    (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
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

private theorem scaled_section_eq (a y T w : ℝ) :
    {g : BridgeNoise | (g, w) ∈ scaledInitialSurvival a y T} =
      strictInterval a y T (y + Real.sqrt T * w) := by
  ext g
  rw [Set.mem_setOf_eq, mem_scaledInitialSurvival_iff]
  change (∀ t : BridgeTime, |bridgePath y T (y + Real.sqrt T * w) g t| < a) ↔
    (∀ t : BridgeTime, bridgePath y T (y + Real.sqrt T * w) g t < a) ∧
      ∀ t : BridgeTime, -a < bridgePath y T (y + Real.sqrt T * w) g t
  simp only [abs_lt, forall_and, and_comm]

theorem product_scaled_initial_joint
    (ν : Measure BridgeNoise) [IsProbabilityMeasure ν] (a y T v : ℝ) :
    (ν.prod (gaussianReal 0 1)).real
      (scaledInitialSurvival a y T ∩ {p : BridgeNoise × ℝ | y + Real.sqrt T * p.2 ≤ v}) =
      ∫ w : ℝ, (if y + Real.sqrt T * w ≤ v then
        intervalCompletion ν a y T (y + Real.sqrt T * w) else 0) ∂(gaussianReal 0 1) := by
  let S : Set (BridgeNoise × ℝ) :=
    scaledInitialSurvival a y T ∩ {p : BridgeNoise × ℝ | y + Real.sqrt T * p.2 ≤ v}
  have hS : MeasurableSet S := (measurableSet_scaledInitialSurvival a y T).inter
    (measurableSet_le (by fun_prop) measurable_const)
  change (ν.prod (gaussianReal 0 1)).real S = _
  rw [product_real_section ν (gaussianReal 0 1) S hS]
  apply integral_congr_ae
  exact Eventually.of_forall fun w => by
    change ν.real {g : BridgeNoise | (g, w) ∈ S} =
      (if y + Real.sqrt T * w ≤ v then intervalCompletion ν a y T (y + Real.sqrt T * w) else 0)
    by_cases hw : y + Real.sqrt T * w ≤ v
    · have hsec : {g : BridgeNoise | (g, w) ∈ S} =
          {g : BridgeNoise | (g, w) ∈ scaledInitialSurvival a y T} := by
        ext g
        simp only [S, Set.mem_setOf_eq, Set.mem_inter_iff, hw, and_true]
      rw [hsec, scaled_section_eq, if_pos hw]
      rfl
    · have hsec : {g : BridgeNoise | (g, w) ∈ S} = ∅ := by
        ext g
        simp only [S, Set.mem_setOf_eq, Set.mem_inter_iff, hw, and_false, Set.mem_empty_iff_false]
      rw [hsec, measureReal_empty, if_neg hw]

private theorem actual_scaled_event_ae {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T : ℝ) :
    {ω | ∀ t : BridgeTime, |y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω| < a} =ᵐ[P]
      (fun ω => (bridgeNoise B ω, B 1 ω)) ⁻¹' scaledInitialSurvival a y T := by
  filter_upwards [ae_bridgeNoise_eq B P hB] with ω hω
  apply propext
  change (∀ t : BridgeTime, |y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω| < a) ↔
    (bridgeNoise B ω, B 1 ω) ∈ scaledInitialSurvival a y T
  rw [mem_scaledInitialSurvival_iff]
  have heq (t : BridgeTime) : bridgePath y T (y + Real.sqrt T * B 1 ω) (bridgeNoise B ω) t =
      y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω := by
    simp only [bridgePath, ContinuousMap.coe_mk]
    rw [hω t]
    ring
  simp only [heq]

theorem brownian_scaled_initial_joint {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T v : ℝ) :
    P.real {ω | (∀ t : BridgeTime, |y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧
      y + Real.sqrt T * B 1 ω ≤ v} =
      ∫ w : ℝ, (if y + Real.sqrt T * w ≤ v then
        intervalCompletion (bridgeLaw B P) a y T (y + Real.sqrt T * w) else 0)
        ∂(gaussianReal 0 1) := by
  letI := isProbabilityMeasure_bridgeLaw B P hB
  let S : Set (BridgeNoise × ℝ) :=
    scaledInitialSurvival a y T ∩ {p : BridgeNoise × ℝ | y + Real.sqrt T * p.2 ≤ v}
  have hS : MeasurableSet S := (measurableSet_scaledInitialSurvival a y T).inter
    (measurableSet_le (by fun_prop) measurable_const)
  have hevent :
      {ω | (∀ t : BridgeTime, |y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧
        y + Real.sqrt T * B 1 ω ≤ v} =ᵐ[P]
      (fun ω => (bridgeNoise B ω, B 1 ω)) ⁻¹' S := by
    filter_upwards [actual_scaled_event_ae B P hB a y T] with ω hω
    apply propext
    change ((∀ t : BridgeTime, |y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧
        y + Real.sqrt T * B 1 ω ≤ v) ↔
      ((bridgeNoise B ω, B 1 ω) ∈ scaledInitialSurvival a y T ∧ y + Real.sqrt T * B 1 ω ≤ v)
    exact and_congr (Iff.of_eq hω) Iff.rfl
  calc
    _ = P.real ((fun ω => (bridgeNoise B ω, B 1 ω)) ⁻¹' S) := measureReal_congr hevent
    _ = ((bridgeLaw B P).prod (gaussianReal 0 1)).real S :=
      (bridge_endpoint_hasLaw B P hB).measureReal_eq hS
    _ = _ := product_scaled_initial_joint (bridgeLaw B P) a y T v

end Shao.C2.ScaledBrownianIdentity
