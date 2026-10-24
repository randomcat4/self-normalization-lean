import Shao.C2.InitialBrownianIdentity

open scoped NNReal
noncomputable section
namespace Shao.C2.BridgeHalfLineJointLaw
open MeasureTheory ProbabilityTheory Set
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw

def upperJointEvent (a y T v : ℝ) : Set (BridgeNoise × ℝ) :=
  {p | p.1 ∈ strictUpper a y T (y + Real.sqrt T * p.2) ∧
    y + Real.sqrt T * p.2 ≤ v}

def lowerJointEvent (a y T v : ℝ) : Set (BridgeNoise × ℝ) :=
  {p | p.1 ∈ strictLower a y T (y + Real.sqrt T * p.2) ∧
    y + Real.sqrt T * p.2 ≤ v}

theorem measurableSet_upperJointEvent (a y T v : ℝ) :
    MeasurableSet (upperJointEvent a y T v) := by
  have hc : Continuous (fun p : BridgeNoise × ℝ => bridgePath y T (y + Real.sqrt T * p.2) p.1) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun q : (BridgeNoise × ℝ) × BridgeTime =>
      (1 - (q.2 : ℝ)) * y + (q.2 : ℝ) * (y + Real.sqrt T * q.1.2) +
        Real.sqrt T * q.1.1.val q.2)
    fun_prop
  have ho := ContinuousMap.isOpen_setOfPred_mapsTo
    (X := BridgeTime) isCompact_univ (isOpen_Iio (a := a))
  have hs : MeasurableSet {p : BridgeNoise × ℝ | ∀ t : BridgeTime, bridgePath y T (y + Real.sqrt T * p.2) p.1 t < a} := by
    simpa [Set.MapsTo] using (ho.preimage hc).measurableSet
  change MeasurableSet ({p : BridgeNoise × ℝ | ∀ t : BridgeTime, bridgePath y T (y + Real.sqrt T * p.2) p.1 t < a} ∩
    {p : BridgeNoise × ℝ | y + Real.sqrt T * p.2 ≤ v})
  exact hs.inter (measurableSet_le (by fun_prop) measurable_const)

theorem measurableSet_lowerJointEvent (a y T v : ℝ) :
    MeasurableSet (lowerJointEvent a y T v) := by
  have hc : Continuous (fun p : BridgeNoise × ℝ => bridgePath y T (y + Real.sqrt T * p.2) p.1) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun q : (BridgeNoise × ℝ) × BridgeTime =>
      (1 - (q.2 : ℝ)) * y + (q.2 : ℝ) * (y + Real.sqrt T * q.1.2) +
        Real.sqrt T * q.1.1.val q.2)
    fun_prop
  have ho := ContinuousMap.isOpen_setOfPred_mapsTo
    (X := BridgeTime) isCompact_univ (isOpen_Ioi (a := -a))
  have hs : MeasurableSet {p : BridgeNoise × ℝ | ∀ t : BridgeTime, -a < bridgePath y T (y + Real.sqrt T * p.2) p.1 t} := by
    simpa [Set.MapsTo] using (ho.preimage hc).measurableSet
  change MeasurableSet ({p : BridgeNoise × ℝ | ∀ t : BridgeTime, -a < bridgePath y T (y + Real.sqrt T * p.2) p.1 t} ∩
    {p : BridgeNoise × ℝ | y + Real.sqrt T * p.2 ≤ v})
  exact hs.inter (measurableSet_le (by fun_prop) measurable_const)

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
      exact Filter.Eventually.of_forall fun w => by
        have hsec : MeasurableSet {g : BridgeNoise | (g, w) ∈ S} :=
          hS.preimage (measurable_id.prodMk measurable_const)
        change (∫ g, ({g : BridgeNoise | (g, w) ∈ S}).indicator (fun _ => (1 : ℝ)) g ∂ν) = _
        exact integral_indicator_one hsec

theorem product_upper_joint (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y T v : ℝ) :
    (ν.prod (gaussianReal 0 1)).real (upperJointEvent a y T v) =
      ∫ w : ℝ, (if y + Real.sqrt T * w ≤ v then
        upperCompletion ν a y T (y + Real.sqrt T * w) else 0) ∂(gaussianReal 0 1) := by
  rw [product_real_section ν (gaussianReal 0 1) (upperJointEvent a y T v)
    (measurableSet_upperJointEvent a y T v)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    change ν.real {g : BridgeNoise | (g, w) ∈ upperJointEvent a y T v} =
      (if y + Real.sqrt T * w ≤ v then upperCompletion ν a y T (y + Real.sqrt T * w) else 0)
    by_cases hw : y + Real.sqrt T * w ≤ v
    · have hsec : {g : BridgeNoise | (g, w) ∈ upperJointEvent a y T v} =
          strictUpper a y T (y + Real.sqrt T * w) := by
        ext g
        simp only [upperJointEvent, Set.mem_setOf_eq, hw, and_true]
      rw [hsec, if_pos hw]
      rfl
    · have hsec : {g : BridgeNoise | (g, w) ∈ upperJointEvent a y T v} = ∅ := by
        ext g
        simp only [upperJointEvent, Set.mem_setOf_eq, hw, and_false, Set.mem_empty_iff_false]
      rw [hsec, measureReal_empty, if_neg hw]

theorem product_lower_joint (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y T v : ℝ) :
    (ν.prod (gaussianReal 0 1)).real (lowerJointEvent a y T v) =
      ∫ w : ℝ, (if y + Real.sqrt T * w ≤ v then
        lowerCompletion ν a y T (y + Real.sqrt T * w) else 0) ∂(gaussianReal 0 1) := by
  rw [product_real_section ν (gaussianReal 0 1) (lowerJointEvent a y T v)
    (measurableSet_lowerJointEvent a y T v)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    change ν.real {g : BridgeNoise | (g, w) ∈ lowerJointEvent a y T v} =
      (if y + Real.sqrt T * w ≤ v then lowerCompletion ν a y T (y + Real.sqrt T * w) else 0)
    by_cases hw : y + Real.sqrt T * w ≤ v
    · have hsec : {g : BridgeNoise | (g, w) ∈ lowerJointEvent a y T v} =
          strictLower a y T (y + Real.sqrt T * w) := by
        ext g
        simp only [lowerJointEvent, Set.mem_setOf_eq, hw, and_true]
      rw [hsec, if_pos hw]
      rfl
    · have hsec : {g : BridgeNoise | (g, w) ∈ lowerJointEvent a y T v} = ∅ := by
        ext g
        simp only [lowerJointEvent, Set.mem_setOf_eq, hw, and_false, Set.mem_empty_iff_false]
      rw [hsec, measureReal_empty, if_neg hw]

theorem brownian_upper_joint {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T v : ℝ) :
    P.real {ω | (∀ t : BridgeTime,
        y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω < a) ∧
        y + Real.sqrt T * B 1 ω ≤ v} =
      ∫ w : ℝ, (if y + Real.sqrt T * w ≤ v then
        upperCompletion (bridgeLaw B P) a y T (y + Real.sqrt T * w) else 0)
        ∂(gaussianReal 0 1) := by
  letI := isProbabilityMeasure_bridgeLaw B P hB
  have hevent : {ω | (∀ t : BridgeTime, y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω < a) ∧
      y + Real.sqrt T * B 1 ω ≤ v} =ᵐ[P]
      (fun ω => (bridgeNoise B ω, B 1 ω)) ⁻¹' upperJointEvent a y T v := by
    filter_upwards [ae_bridgeNoise_eq B P hB] with ω hω
    apply propext
    have hp (t : BridgeTime) : bridgePath y T (y + Real.sqrt T * B 1 ω) (bridgeNoise B ω) t =
        y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω := by
      change (1 - (t : ℝ)) * y + (t : ℝ) * (y + Real.sqrt T * B 1 ω) +
        Real.sqrt T * (bridgeNoise B ω).val t = _
      rw [hω t]
      ring
    change ((∀ t : BridgeTime, y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω < a) ∧ _) ↔
      ((∀ t : BridgeTime, bridgePath y T (y + Real.sqrt T * B 1 ω) (bridgeNoise B ω) t < a) ∧ _)
    simp only [hp]
  calc
    _ = P.real ((fun ω => (bridgeNoise B ω, B 1 ω)) ⁻¹' upperJointEvent a y T v) :=
      measureReal_congr hevent
    _ = ((bridgeLaw B P).prod (gaussianReal 0 1)).real (upperJointEvent a y T v) :=
      (bridge_endpoint_hasLaw B P hB).measureReal_eq (measurableSet_upperJointEvent a y T v)
    _ = _ := product_upper_joint (bridgeLaw B P) a y T v

theorem brownian_lower_joint {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T v : ℝ) :
    P.real {ω | (∀ t : BridgeTime,
        -a < y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω) ∧
        y + Real.sqrt T * B 1 ω ≤ v} =
      ∫ w : ℝ, (if y + Real.sqrt T * w ≤ v then
        lowerCompletion (bridgeLaw B P) a y T (y + Real.sqrt T * w) else 0)
        ∂(gaussianReal 0 1) := by
  letI := isProbabilityMeasure_bridgeLaw B P hB
  have hevent : {ω | (∀ t : BridgeTime, -a < y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω) ∧
      y + Real.sqrt T * B 1 ω ≤ v} =ᵐ[P]
      (fun ω => (bridgeNoise B ω, B 1 ω)) ⁻¹' lowerJointEvent a y T v := by
    filter_upwards [ae_bridgeNoise_eq B P hB] with ω hω
    apply propext
    have hp (t : BridgeTime) : bridgePath y T (y + Real.sqrt T * B 1 ω) (bridgeNoise B ω) t =
        y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω := by
      change (1 - (t : ℝ)) * y + (t : ℝ) * (y + Real.sqrt T * B 1 ω) +
        Real.sqrt T * (bridgeNoise B ω).val t = _
      rw [hω t]
      ring
    change ((∀ t : BridgeTime, -a < y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω) ∧ _) ↔
      ((∀ t : BridgeTime, -a < bridgePath y T (y + Real.sqrt T * B 1 ω) (bridgeNoise B ω) t) ∧ _)
    simp only [hp]
  calc
    _ = P.real ((fun ω => (bridgeNoise B ω, B 1 ω)) ⁻¹' lowerJointEvent a y T v) :=
      measureReal_congr hevent
    _ = ((bridgeLaw B P).prod (gaussianReal 0 1)).real (lowerJointEvent a y T v) :=
      (bridge_endpoint_hasLaw B P hB).measureReal_eq (measurableSet_lowerJointEvent a y T v)
    _ = _ := product_lower_joint (bridgeLaw B P) a y T v

end Shao.C2.BridgeHalfLineJointLaw
