import Shao.C2.BridgeEndpointIndependence
import Mathlib.MeasureTheory.Integral.Prod

open scoped NNReal
noncomputable section
namespace Shao.C2.BrownianBridgeLaw
open MeasureTheory ProbabilityTheory Set
open Shao.C2.BridgeDomination

def initialSurvival (a : ℝ) : Set (BridgeNoise × ℝ) :=
  {p | ‖p.1.val + p.2 • rightWeight‖ < a}

theorem mem_initialSurvival_iff (a : ℝ) (g : BridgeNoise) (w : ℝ) :
    (g, w) ∈ initialSurvival a ↔ ∀ t : BridgeTime, |bridgePath 0 1 w g t| < a := by
  change ‖g.val + w • rightWeight‖ < a ↔ _
  rw [ContinuousMap.norm_lt_iff_of_nonempty]
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul,
    rightWeight, ContinuousMap.coe_mk, bridgePath, mul_zero, zero_add,
    Real.sqrt_one, one_mul, Real.norm_eq_abs, add_comm, mul_comm, zero_mul, add_zero]

theorem measurableSet_initialSurvival (a : ℝ) : MeasurableSet (initialSurvival a) := by
  have hc : Continuous (fun p : BridgeNoise × ℝ => p.1.val + p.2 • rightWeight) :=
    (continuous_subtype_val.comp continuous_fst).add (continuous_snd.smul continuous_const)
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
      exact Filter.Eventually.of_forall fun w => by
        have hsec : MeasurableSet {g : BridgeNoise | (g, w) ∈ S} :=
          hS.preimage (measurable_id.prodMk measurable_const)
        change (∫ g, ({g : BridgeNoise | (g, w) ∈ S}).indicator (fun _ => (1 : ℝ)) g ∂ν) = _
        exact integral_indicator_one hsec

private theorem initial_section_eq (a w : ℝ) :
    {g : BridgeNoise | (g, w) ∈ initialSurvival a} = strictInterval a 0 1 w := by
  ext g
  rw [Set.mem_setOf_eq, mem_initialSurvival_iff]
  change (∀ t : BridgeTime, |bridgePath 0 1 w g t| < a) ↔
    (∀ t : BridgeTime, bridgePath 0 1 w g t < a) ∧
      ∀ t : BridgeTime, -a < bridgePath 0 1 w g t
  simp only [abs_lt, forall_and, and_comm]

theorem product_initial_marginal
    (ν : Measure BridgeNoise) [IsProbabilityMeasure ν] (a : ℝ) :
    (ν.prod (gaussianReal 0 1)).real (initialSurvival a) =
      ∫ w : ℝ, intervalCompletion ν a 0 1 w ∂(gaussianReal 0 1) := by
  rw [product_real_section ν (gaussianReal 0 1) (initialSurvival a)
    (measurableSet_initialSurvival a)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    change ν.real {g : BridgeNoise | (g, w) ∈ initialSurvival a} = intervalCompletion ν a 0 1 w
    rw [initial_section_eq]
    rfl

theorem product_initial_joint
    (ν : Measure BridgeNoise) [IsProbabilityMeasure ν] (a v : ℝ) :
    (ν.prod (gaussianReal 0 1)).real
      (initialSurvival a ∩ {p : BridgeNoise × ℝ | p.2 ≤ v}) =
      ∫ w : ℝ, (if w ≤ v then intervalCompletion ν a 0 1 w else 0)
        ∂(gaussianReal 0 1) := by
  let S : Set (BridgeNoise × ℝ) := initialSurvival a ∩ {p : BridgeNoise × ℝ | p.2 ≤ v}
  have hS : MeasurableSet S := (measurableSet_initialSurvival a).inter
    (measurableSet_le measurable_snd measurable_const)
  change (ν.prod (gaussianReal 0 1)).real S = _
  rw [product_real_section ν (gaussianReal 0 1) S hS]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    change ν.real {g : BridgeNoise | (g, w) ∈ S} =
      (if w ≤ v then intervalCompletion ν a 0 1 w else 0)
    by_cases hw : w ≤ v
    · have hsec : {g : BridgeNoise | (g, w) ∈ S} =
          {g : BridgeNoise | (g, w) ∈ initialSurvival a} := by
        ext g
        simp only [S, Set.mem_setOf_eq, Set.mem_inter_iff, hw, and_true]
      rw [hsec, initial_section_eq, if_pos hw]
      rfl
    · have hsec : {g : BridgeNoise | (g, w) ∈ S} = ∅ := by
        ext g
        simp only [S, Set.mem_setOf_eq, Set.mem_inter_iff, hw, and_false, Set.mem_empty_iff_false]
      rw [hsec, measureReal_empty, if_neg hw]

private theorem actual_initial_event_ae {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a : ℝ) :
    {ω | ∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ ω| < a} =ᵐ[P]
      (fun ω => (bridgeNoise B ω, B 1 ω)) ⁻¹' initialSurvival a := by
  filter_upwards [ae_bridgeNoise_eq B P hB] with ω hω
  apply propext
  change (∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ ω| < a) ↔
    (bridgeNoise B ω, B 1 ω) ∈ initialSurvival a
  rw [mem_initialSurvival_iff]
  have heq (t : BridgeTime) : bridgePath 0 1 (B 1 ω) (bridgeNoise B ω) t =
      B ⟨(t : ℝ), t.property.1⟩ ω := by
    simp only [bridgePath, ContinuousMap.coe_mk, mul_zero, zero_add, Real.sqrt_one, one_mul]
    rw [hω t]
    ring
  simp only [heq]

theorem brownian_initial_marginal {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a : ℝ) :
    P.real {ω | ∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ ω| < a} =
      ∫ w : ℝ, intervalCompletion (bridgeLaw B P) a 0 1 w ∂(gaussianReal 0 1) := by
  letI := isProbabilityMeasure_bridgeLaw B P hB
  calc
    _ = P.real ((fun ω => (bridgeNoise B ω, B 1 ω)) ⁻¹' initialSurvival a) :=
      measureReal_congr (actual_initial_event_ae B P hB a)
    _ = ((bridgeLaw B P).prod (gaussianReal 0 1)).real (initialSurvival a) :=
      (bridge_endpoint_hasLaw B P hB).measureReal_eq (measurableSet_initialSurvival a)
    _ = _ := product_initial_marginal (bridgeLaw B P) a

theorem brownian_initial_joint {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a v : ℝ) :
    P.real {ω | (∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧ B 1 ω ≤ v} =
      ∫ w : ℝ, (if w ≤ v then intervalCompletion (bridgeLaw B P) a 0 1 w else 0)
        ∂(gaussianReal 0 1) := by
  letI := isProbabilityMeasure_bridgeLaw B P hB
  let S : Set (BridgeNoise × ℝ) := initialSurvival a ∩ {p : BridgeNoise × ℝ | p.2 ≤ v}
  have hS : MeasurableSet S := (measurableSet_initialSurvival a).inter
    (measurableSet_le measurable_snd measurable_const)
  have hevent :
      {ω | (∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧ B 1 ω ≤ v} =ᵐ[P]
        (fun ω => (bridgeNoise B ω, B 1 ω)) ⁻¹' S := by
    filter_upwards [actual_initial_event_ae B P hB a] with ω hω
    apply propext
    change ((∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧ B 1 ω ≤ v) ↔
      ((bridgeNoise B ω, B 1 ω) ∈ initialSurvival a ∧ B 1 ω ≤ v)
    exact and_congr (Iff.of_eq hω) Iff.rfl
  calc
    _ = P.real ((fun ω => (bridgeNoise B ω, B 1 ω)) ⁻¹' S) := measureReal_congr hevent
    _ = ((bridgeLaw B P).prod (gaussianReal 0 1)).real S :=
      (bridge_endpoint_hasLaw B P hB).measureReal_eq hS
    _ = _ := product_initial_joint (bridgeLaw B P) a v

end Shao.C2.BrownianBridgeLaw
