import Shao.C2.RademacherReflectionProbability

noncomputable section
namespace Shao.C2.BrownianUpperBoundary
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw

def upperTouch (a y T : ℝ) : Set (BridgeNoise × ℝ) :=
  {p | (∀ t : BridgeTime, bridgePath y T (y + Real.sqrt T * p.2) p.1 t ≤ a) ∧
    ∃ t : BridgeTime, bridgePath y T (y + Real.sqrt T * p.2) p.1 t = a}

theorem upperTouch_section_subsingleton (a y T : ℝ) (g : BridgeNoise)
    (hy : y < a) (hT : 0 < T) :
    ({w : ℝ | (g, w) ∈ upperTouch a y T}).Subsingleton := by
  have horder (q r : ℝ) (hq : (g, q) ∈ upperTouch a y T)
      (hr : (g, r) ∈ upperTouch a y T) : r ≤ q := by
    by_contra hnot
    have hqr : q < r := lt_of_not_ge hnot
    change ((∀ t : BridgeTime, bridgePath y T (y + Real.sqrt T * q) g t ≤ a) ∧
      ∃ t : BridgeTime, bridgePath y T (y + Real.sqrt T * q) g t = a) at hq
    change ((∀ t : BridgeTime, bridgePath y T (y + Real.sqrt T * r) g t ≤ a) ∧
      ∃ t : BridgeTime, bridgePath y T (y + Real.sqrt T * r) g t = a) at hr
    obtain ⟨_, ⟨t, ht⟩⟩ := hq
    have ht0 : t ≠ 0 := by
      intro he
      subst t
      rw [(bridgePath_endpoints y T (y + Real.sqrt T * q) g).1] at ht
      linarith
    have htpos : 0 < (t : ℝ) := by
      have hne : (t : ℝ) ≠ 0 := by intro hz; exact ht0 (Subtype.ext hz)
      exact lt_of_le_of_ne t.property.1 hne.symm
    have hprod := mul_pos (mul_pos htpos (Real.sqrt_pos.mpr hT)) (sub_pos.mpr hqr)
    have hpath : bridgePath y T (y + Real.sqrt T * q) g t <
        bridgePath y T (y + Real.sqrt T * r) g t := by
      change (1 - (t : ℝ)) * y + (t : ℝ) * (y + Real.sqrt T * q) + Real.sqrt T * g.val t <
        (1 - (t : ℝ)) * y + (t : ℝ) * (y + Real.sqrt T * r) + Real.sqrt T * g.val t
      nlinarith only [hprod]
    have hclosed := hr.1 t
    linarith
  intro q hq r hr
  exact le_antisymm (horder r q hr hq) (horder q r hq hr)

theorem measurableSet_upperTouch (a y T : ℝ) : MeasurableSet (upperTouch a y T) := by
  have hc : Continuous (fun p : BridgeNoise × ℝ => bridgePath y T (y + Real.sqrt T * p.2) p.1) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun q : (BridgeNoise × ℝ) × BridgeTime =>
      (1 - (q.2 : ℝ)) * y + (q.2 : ℝ) * (y + Real.sqrt T * q.1.2) +
        Real.sqrt T * q.1.1.val q.2)
    fun_prop
  have heval (t : BridgeTime) : Continuous (fun p : BridgeNoise × ℝ =>
      bridgePath y T (y + Real.sqrt T * p.2) p.1 t) := by
    change Continuous (fun p : BridgeNoise × ℝ =>
      (1 - (t : ℝ)) * y + (t : ℝ) * (y + Real.sqrt T * p.2) + Real.sqrt T * p.1.val t)
    fun_prop
  have ho := ContinuousMap.isOpen_setOfPred_mapsTo
    (X := BridgeTime) isCompact_univ (isOpen_Iio (a := a))
  have hs : MeasurableSet {p : BridgeNoise × ℝ | ∀ t : BridgeTime,
      bridgePath y T (y + Real.sqrt T * p.2) p.1 t < a} := by
    simpa [Set.MapsTo] using (ho.preimage hc).measurableSet
  have hcl : IsClosed {p : BridgeNoise × ℝ | ∀ t : BridgeTime,
      bridgePath y T (y + Real.sqrt T * p.2) p.1 t ≤ a} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => isClosed_le (heval t) continuous_const
  have he : upperTouch a y T =
      {p : BridgeNoise × ℝ | ∀ t : BridgeTime, bridgePath y T (y + Real.sqrt T * p.2) p.1 t ≤ a} \
      {p : BridgeNoise × ℝ | ∀ t : BridgeTime, bridgePath y T (y + Real.sqrt T * p.2) p.1 t < a} := by
    ext p
    change ((∀ t : BridgeTime, bridgePath y T (y + Real.sqrt T * p.2) p.1 t ≤ a) ∧
      (∃ t : BridgeTime, bridgePath y T (y + Real.sqrt T * p.2) p.1 t = a)) ↔
      ((∀ t : BridgeTime, bridgePath y T (y + Real.sqrt T * p.2) p.1 t ≤ a) ∧
        ¬∀ t : BridgeTime, bridgePath y T (y + Real.sqrt T * p.2) p.1 t < a)
    constructor
    · rintro ⟨hc, ⟨t, ht⟩⟩
      refine ⟨hc, ?_⟩
      intro hall
      have hlt := hall t
      linarith
    · rintro ⟨hc, hn⟩
      push_neg at hn
      obtain ⟨t, ht⟩ := hn
      exact ⟨hc, t, le_antisymm (hc t) ht⟩
  rw [he]
  exact hcl.measurableSet.diff hs

theorem product_upperTouch_zero (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y T : ℝ) (hy : y < a) (hT : 0 < T) :
    (ν.prod (gaussianReal 0 1)) (upperTouch a y T) = 0 := by
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hsec (g : BridgeNoise) : (gaussianReal 0 1) (Prod.mk g ⁻¹' upperTouch a y T) = 0 := by
    change (gaussianReal 0 1) {w : ℝ | (g, w) ∈ upperTouch a y T} = 0
    have hs := upperTouch_section_subsingleton a y T g hy hT
    by_cases hn : ({w : ℝ | (g, w) ∈ upperTouch a y T}).Nonempty
    · obtain ⟨w, hw⟩ := hn
      have hsub : {v : ℝ | (g, v) ∈ upperTouch a y T} ⊆ {w} := by
        intro v hv
        exact Set.mem_singleton_iff.mpr (hs hv hw)
      exact measure_mono_null hsub (measure_singleton w)
    · have he : {w : ℝ | (g, w) ∈ upperTouch a y T} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro w hw
        exact hn ⟨w, hw⟩
      rw [he]
      exact measure_empty
  rw [Measure.prod_apply (measurableSet_upperTouch a y T)]
  simp_rw [hsec]
  simp

theorem brownian_upperTouch_zero {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T : ℝ) (hy : y < a) (hT : 0 < T) :
    P {ω | (∀ t : BridgeTime, y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω ≤ a) ∧
      ∃ t : BridgeTime, y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω = a} = 0 := by
  letI := isProbabilityMeasure_bridgeLaw B P hB
  have hevent : {ω | (∀ t : BridgeTime, y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω ≤ a) ∧
      ∃ t : BridgeTime, y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω = a} =ᵐ[P]
      (fun ω => (bridgeNoise B ω, B 1 ω)) ⁻¹' upperTouch a y T := by
    filter_upwards [ae_bridgeNoise_eq B P hB] with ω hω
    apply propext
    have hp (t : BridgeTime) : bridgePath y T (y + Real.sqrt T * B 1 ω) (bridgeNoise B ω) t =
        y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω := by
      change (1 - (t : ℝ)) * y + (t : ℝ) * (y + Real.sqrt T * B 1 ω) +
        Real.sqrt T * (bridgeNoise B ω).val t = _
      rw [hω t]
      ring
    change ((∀ t : BridgeTime, y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω ≤ a) ∧
      (∃ t : BridgeTime, y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω = a)) ↔
      ((∀ t : BridgeTime, bridgePath y T (y + Real.sqrt T * B 1 ω) (bridgeNoise B ω) t ≤ a) ∧
        (∃ t : BridgeTime, bridgePath y T (y + Real.sqrt T * B 1 ω) (bridgeNoise B ω) t = a))
    simp only [hp]
  calc
    _ = P ((fun ω => (bridgeNoise B ω, B 1 ω)) ⁻¹' upperTouch a y T) := measure_congr hevent
    _ = ((bridgeLaw B P).prod (gaussianReal 0 1)) (upperTouch a y T) :=
      (bridge_endpoint_hasLaw B P hB).measure_eq (measurableSet_upperTouch a y T)
    _ = 0 := product_upperTouch_zero (bridgeLaw B P) a y T hy hT

theorem brownian_upper_strict_closed {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T : ℝ) (hy : y < a) (hT : 0 < T) :
    P.real {ω | ∀ t : BridgeTime, y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω < a} =
      P.real {ω | ∀ t : BridgeTime, y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω ≤ a} := by
  have hz := brownian_upperTouch_zero B P hB a y T hy hT
  have hae : ∀ᵐ ω ∂P, ¬((∀ t : BridgeTime, y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω ≤ a) ∧
      ∃ t : BridgeTime, y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω = a) := by
    apply ae_iff.mpr
    simpa only [not_not] using hz
  apply measureReal_congr
  filter_upwards [hae] with ω hno
  apply propext
  constructor
  · intro hs t
    exact (hs t).le
  · intro hc t
    by_contra hn
    have he : y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω = a :=
      le_antisymm (hc t) (le_of_not_gt hn)
    exact hno ⟨hc, t, he⟩

end Shao.C2.BrownianUpperBoundary
