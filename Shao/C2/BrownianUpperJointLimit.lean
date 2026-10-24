import Shao.C2.BrownianUpperBoundary
import Mathlib.MeasureTheory.Measure.Portmanteau

noncomputable section
namespace Shao.C2.BrownianUpperJointLimit
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
open Shao.C2.BridgeDomination Shao.C2.BrownianUpperBoundary
open Shao.OQ4.PolygonalBrownianWeakLimit

def upperJointSet (a v : ℝ) : Set C(BridgeTime, ℝ) :=
  {f | (∀ t : BridgeTime, f t ≤ a) ∧ f 1 ≤ v}

def upperBoundarySet (a : ℝ) : Set C(BridgeTime, ℝ) :=
  {f | ∀ t : BridgeTime, f t ≤ a} \ {f | ∀ t : BridgeTime, f t < a}

private theorem ae_unitPath_eq {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : BridgeTime,
      brownianUnitPath B 1 ω t = B ⟨(t : ℝ), t.property.1⟩ ω := by
  filter_upwards [ae_brownianUnitPath_eq B 1 P hB] with ω hω
  intro t
  calc
    _ = B (1 * ⟨(t : ℝ), t.property.1⟩) ω := hω t
    _ = _ := congrArg (fun s : ℝ≥0 => B s ω) (one_mul _)

theorem isClosed_upperJointSet (a v : ℝ) : IsClosed (upperJointSet a v) := by
  have hc : IsClosed {f : C(BridgeTime, ℝ) | ∀ t : BridgeTime, f t ≤ a} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => isClosed_le (by fun_prop) continuous_const
  have he : IsClosed {f : C(BridgeTime, ℝ) | f 1 ≤ v} :=
    isClosed_le (by fun_prop) continuous_const
  exact hc.inter he

theorem measurableSet_upperBoundarySet (a : ℝ) : MeasurableSet (upperBoundarySet a) := by
  have hc : IsClosed {f : C(BridgeTime, ℝ) | ∀ t : BridgeTime, f t ≤ a} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => isClosed_le (by fun_prop) continuous_const
  have hs : IsOpen {f : C(BridgeTime, ℝ) | ∀ t : BridgeTime, f t < a} := by
    simpa [Set.MapsTo] using ContinuousMap.isOpen_setOfPred_mapsTo
      (X := BridgeTime) isCompact_univ (isOpen_Iio (a := a))
  exact hc.measurableSet.diff hs.measurableSet

theorem frontier_upperJointSet_subset (a v : ℝ) :
    frontier (upperJointSet a v) ⊆ upperBoundarySet a ∪ {f : C(BridgeTime, ℝ) | f 1 = v} := by
  intro f hf
  rw [(isClosed_upperJointSet a v).frontier_eq] at hf
  change ((∀ t : BridgeTime, f t ≤ a) ∧ f 1 ≤ v) ∧ f ∉ interior (upperJointSet a v) at hf
  by_cases hb : f ∈ upperBoundarySet a
  · exact Or.inl hb
  · apply Or.inr
    change f 1 = v
    by_contra hn
    have hv : f 1 < v := lt_of_le_of_ne hf.1.2 hn
    have hs : ∀ t : BridgeTime, f t < a := by
      by_contra hnot
      exact hb ⟨hf.1.1, hnot⟩
    have ho : IsOpen ({g : C(BridgeTime, ℝ) | ∀ t : BridgeTime, g t < a} ∩
        {g : C(BridgeTime, ℝ) | g 1 < v}) := by
      have hstrict : IsOpen {g : C(BridgeTime, ℝ) | ∀ t : BridgeTime, g t < a} := by
        simpa [Set.MapsTo] using ContinuousMap.isOpen_setOfPred_mapsTo
          (X := BridgeTime) isCompact_univ (isOpen_Iio (a := a))
      exact hstrict.inter (isOpen_lt (by fun_prop) continuous_const)
    have hsub : {g : C(BridgeTime, ℝ) | ∀ t : BridgeTime, g t < a} ∩
        {g : C(BridgeTime, ℝ) | g 1 < v} ⊆ upperJointSet a v := by
      intro g hg
      exact ⟨fun t => (hg.1 t).le, hg.2.le⟩
    have hnhds : upperJointSet a v ∈ 𝓝 f :=
      Filter.mem_of_superset (ho.mem_nhds ⟨hs, hv⟩) hsub
    exact hf.2 (mem_interior_iff_mem_nhds.mpr hnhds)

theorem brownianUnitPathLaw_upperBoundary_zero {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a : ℝ) (ha : 0 < a) :
    brownianUnitPathLaw B 1 P (upperBoundarySet a) = 0 := by
  rw [brownianUnitPathLaw, Measure.map_apply_of_aemeasurable
    (aemeasurable_brownianUnitPath B 1 P hB) (measurableSet_upperBoundarySet a)]
  have he : brownianUnitPath B 1 ⁻¹' upperBoundarySet a =ᵐ[P]
      {ω | (∀ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ ω ≤ a) ∧
        ∃ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ ω = a} := by
    filter_upwards [ae_unitPath_eq B P hB] with ω hω
    apply propext
    change ((∀ t : BridgeTime, brownianUnitPath B 1 ω t ≤ a) ∧
      ¬∀ t : BridgeTime, brownianUnitPath B 1 ω t < a) ↔ _
    simp only [hω]
    constructor
    · rintro ⟨hc, hn⟩
      push_neg at hn
      obtain ⟨t, ht⟩ := hn
      exact ⟨hc, t, le_antisymm (hc t) ht⟩
    · rintro ⟨hc, ⟨t, ht⟩⟩
      refine ⟨hc, ?_⟩
      intro hs
      have hlt := hs t
      linarith
  exact (measure_congr he).trans (by
    simpa only [Real.sqrt_one, one_mul, zero_add] using
      brownian_upperTouch_zero B P hB a 0 1 ha (by norm_num))

theorem brownianUnitPathLaw_endpoint_zero {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (v : ℝ) :
    brownianUnitPathLaw B 1 P {f : C(BridgeTime, ℝ) | f 1 = v} = 0 := by
  have hs : MeasurableSet {f : C(BridgeTime, ℝ) | f 1 = v} :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  rw [brownianUnitPathLaw, Measure.map_apply_of_aemeasurable
    (aemeasurable_brownianUnitPath B 1 P hB) hs]
  have he : brownianUnitPath B 1 ⁻¹' {f : C(BridgeTime, ℝ) | f 1 = v} =ᵐ[P]
      B 1 ⁻¹' {v} := by
    filter_upwards [ae_unitPath_eq B P hB] with ω hω
    apply propext
    change (brownianUnitPath B 1 ω 1 = v) ↔ B 1 ω = v
    have h1 := hω (1 : BridgeTime)
    change brownianUnitPath B 1 ω 1 = B 1 ω at h1
    rw [h1]
  rw [measure_congr he]
  change P {ω | B 1 ω = v} = 0
  rw [(hB.toIsPreBrownianReal.hasLaw_eval 1).measure_eq (measurableSet_singleton v)]
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  exact measure_singleton v

theorem brownianUnitPathLaw_joint_frontier_zero {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a v : ℝ) (ha : 0 < a) :
    brownianUnitPathLaw B 1 P (frontier (upperJointSet a v)) = 0 := by
  exact measure_mono_null (frontier_upperJointSet_subset a v)
    (measure_union_null (brownianUnitPathLaw_upperBoundary_zero B P hB a ha)
      (brownianUnitPathLaw_endpoint_zero B P hB v))

theorem brownianUnitPathLaw_upperJoint_real {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a v : ℝ) (ha : 0 < a) :
    (brownianUnitPathLaw B 1 P).real (upperJointSet a v) =
      P.real {ω | (∀ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ ω < a) ∧ B 1 ω ≤ v} := by
  have hz := brownian_upperTouch_zero B P hB a 0 1 ha (by norm_num)
  have hae : ∀ᵐ ω ∂P, ¬((∀ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ ω ≤ a) ∧
      ∃ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ ω = a) := by
    apply ae_iff.mpr
    simpa only [not_not, Real.sqrt_one, one_mul, zero_add] using hz
  rw [brownianUnitPathLaw, measureReal_def, Measure.map_apply_of_aemeasurable
    (aemeasurable_brownianUnitPath B 1 P hB) (isClosed_upperJointSet a v).measurableSet]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [ae_unitPath_eq B P hB, hae] with ω hω hno
  apply propext
  change ((∀ t : BridgeTime, brownianUnitPath B 1 ω t ≤ a) ∧ brownianUnitPath B 1 ω 1 ≤ v) ↔
    ((∀ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ ω < a) ∧ B 1 ω ≤ v)
  have h1 := hω (1 : BridgeTime)
  change brownianUnitPath B 1 ω 1 = B 1 ω at h1
  rw [h1]
  simp only [hω]
  constructor
  · rintro ⟨hc, hend⟩
    refine ⟨?_, hend⟩
    intro t
    by_contra hn
    exact hno ⟨hc, t, le_antisymm (hc t) (le_of_not_gt hn)⟩
  · rintro ⟨hs, hend⟩
    exact ⟨fun t => (hs t).le, hend⟩

theorem row_upper_joint_tendsto_brownian {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (νSeq : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (νSeq j)]
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hbound : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (hpos : ∀ j, 0 < hSeq j)
    (hh : Tendsto hSeq atTop atTop) (NSeq : ℕ → ℕ)
    (hN : ∀ j, (hSeq j) ^ 2 ≤ (NSeq j : ℝ))
    (a v : ℝ) (ha : 0 < a) :
    Tendsto (fun j =>
      (Shao.OQ4.PolygonalPathTightness.polygonalPathLaw 1 (NSeq j) (hSeq j) (νSeq j)).real
        (upperJointSet a v)) atTop
      (𝓝 (P.real {ω | (∀ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ ω < a) ∧ B 1 ω ≤ v})) := by
  letI := isProbabilityMeasure_brownianUnitPathLaw B 1 P hB
  have ht := tendsto_polygonalPathLaw_brownianUnitPathLaw B 1 P hB νSeq h3 hmean hsecond
    M hbound hSeq hpos hh NSeq (by intro j; simpa using hN j)
  have hset := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' ht
    (brownianUnitPathLaw_joint_frontier_zero B P hB a v ha)
  have hreal := (ENNReal.continuousAt_toReal
    (measure_ne_top (brownianUnitPathLaw B 1 P) (upperJointSet a v))).tendsto.comp hset
  change Tendsto (fun j =>
    (Shao.OQ4.PolygonalPathTightness.polygonalPathLaw 1 (NSeq j) (hSeq j) (νSeq j)).real
      (upperJointSet a v)) atTop (𝓝 ((brownianUnitPathLaw B 1 P).real (upperJointSet a v))) at hreal
  rw [brownianUnitPathLaw_upperJoint_real B P hB a v ha] at hreal
  exact hreal

end Shao.C2.BrownianUpperJointLimit
