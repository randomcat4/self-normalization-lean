import Shao.OQ4.SparseStrictCriticalDenominator
import Shao.OQ4.SparseOriginalIIDTransport
import Shao.OQ4.RademacherOriginalStrictBoundary

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
universe uX uB

namespace Shao.OQ4.SparseOriginalStrictCritical
variable {ΩX : Type uX} [MeasurableSpace ΩX]
variable {ΩB : Type uB} [MeasurableSpace ΩB]

-- The self event is reused, with no new definition:
-- RademacherOriginalStrictBoundary.sourceStrictEvent n X s =
-- {ω | ∀ r : ℕ, 1 ≤ r → r ≤ n →
--   |∑ i ∈ Finset.range r, X (i+1) ω| <
--     s * Real.sqrt (OriginalIIDWindow.sourceEnergy n X ω)}.
-- Its definition and source_strict_pullback are generic; its old
-- source_strict_probability is Rademacher-specific and MUST NOT be used.

def sourceDetStrictEvent (n : ℕ) (X : ℕ → ΩX → ℝ) (s : ℝ) : Set ΩX :=
  {ω | ∀ r : ℕ, 1 ≤ r → r ≤ n →
    |∑ i ∈ Finset.range r, X (i + 1) ω| < s * Real.sqrt (n : ℝ)}

theorem source_event_pullbacks (n : ℕ) (X : ℕ → ΩX → ℝ) (s : ℝ) :
    RademacherOriginalStrictBoundary.sourceStrictEvent n X s =
      OriginalIIDWindow.sourcePath n X ⁻¹'
        SparseStrictCriticalDenominator.selfEvent n s ∧
    sourceDetStrictEvent n X s = OriginalIIDWindow.sourcePath n X ⁻¹'
      SparseStrictCriticalDenominator.detEvent n s ∧
    RademacherOriginalStrictBoundary.sourceStrictEvent 0 X s = Set.univ ∧
    sourceDetStrictEvent 0 X s = Set.univ := by
  classical
  have hprefix (r : ℕ) (hr : r ≤ n) (ω : ΩX) :
      Shao.prefixSum (OriginalIIDWindow.sourcePath n X ω) r =
        ∑ i ∈ Finset.range r, X (i + 1) ω := by
    unfold Shao.prefixSum OriginalIIDWindow.sourcePath
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i hi
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    · intro i hi j hj hij
      exact Fin.ext hij
    · intro j hj
      have hjr := Finset.mem_range.mp hj
      refine ⟨⟨j, lt_of_lt_of_le hjr hr⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjr⟩
    · intro i hi
      rfl
  refine ⟨?_, ?_,
    (RademacherOriginalStrictBoundary.source_strict_pullback n X s).2, ?_⟩
  · simpa only [SparseStrictCriticalDenominator.selfEvent] using
      (RademacherOriginalStrictBoundary.source_strict_pullback n X s).1
  · ext ω
    change (∀ r : ℕ, 1 ≤ r → r ≤ n →
        |∑ i ∈ Finset.range r, X (i + 1) ω| < s * Real.sqrt (n : ℝ)) ↔
      (∀ r : ℕ, 1 ≤ r → r ≤ n →
        |Shao.prefixSum (OriginalIIDWindow.sourcePath n X ω) r| <
          s * Real.sqrt (n : ℝ))
    constructor
    · intro h r hr hrn
      simpa only [hprefix r hrn ω] using h r hr hrn
    · intro h r hr hrn
      simpa only [hprefix r hrn ω] using h r hr hrn
  · ext ω
    simp only [sourceDetStrictEvent, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro r hr hr0
    omega

theorem source_event_bridges (n : ℕ) (hn : 0 < n)
    (X : ℕ → ΩX → ℝ) (s : ℝ) (ω : ΩX) :
    (ω ∈ RademacherOriginalStrictBoundary.sourceStrictEvent n X s ↔
      OriginalIIDWindow.sourceMaximum n X ω <
        s * Real.sqrt (OriginalIIDWindow.sourceEnergy n X ω)) ∧
    (ω ∈ sourceDetStrictEvent n X s ↔
      OriginalIIDWindow.sourceMaximum n X ω < s * Real.sqrt (n : ℝ)) ∧
    (OriginalIIDWindow.sourceEnergy n X ω = 0 →
      ω ∉ RademacherOriginalStrictBoundary.sourceStrictEvent n X s ∧
        (0 < s → ω ∈ sourceDetStrictEvent n X s)) := by
  have hp := source_event_pullbacks n X s
  rw [hp.1, hp.2.1]
  simpa only [Set.mem_preimage, OriginalIIDWindow.sourceMaximum, dif_pos hn,
    OriginalIIDWindow.sourceEnergy] using
    SparseStrictCriticalDenominator.actual_event_bridges n hn s
      (OriginalIIDWindow.sourcePath n X ω)

theorem source_probability_pair
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ SparseCriticalDenominator.law)
    (n : ℕ) (s : ℝ) :
    μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X s) =
      (SparseCriticalDenominator.pathLaw n).real
        (SparseStrictCriticalDenominator.selfEvent n s) ∧
    μ.real (sourceDetStrictEvent n X s) =
      (SparseCriticalDenominator.pathLaw n).real
        (SparseStrictCriticalDenominator.detEvent n s) := by
  have hpath := SparseOriginalIIDTransport.sourcePath_identDistrib μ X hIndep hLaw n
  have hm := SparseStrictCriticalDenominator.measurable_events n s
  have hp := source_event_pullbacks n X s
  constructor
  · rw [hp.1]
    exact congrArg ENNReal.toReal (hpath.measure_mem_eq hm.1)
  · rw [hp.2.1]
    exact congrArg ENNReal.toReal (hpath.measure_mem_eq hm.2)

theorem original_sparse_strict_critical_limits
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ SparseCriticalDenominator.law) :
    Tendsto (fun m : ℕ =>
      μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent ((2 * m) ^ 3) X
        (1 / Real.sqrt (2 * (m : ℝ)))) /
      Shao.Probability.BrownianSup.probability B P hB
        (1 / Real.sqrt (2 * (m : ℝ)))) atTop
      (𝓝 ((1 + Real.exp (Real.pi ^ 2 / 2)) / 2)) ∧
    Tendsto (fun m : ℕ =>
      μ.real (sourceDetStrictEvent ((2 * m) ^ 3) X
        (1 / Real.sqrt (2 * (m : ℝ)))) /
      Shao.Probability.BrownianSup.probability B P hB
        (1 / Real.sqrt (2 * (m : ℝ)))) atTop (𝓝 (1 : ℝ)) := by
  have hc := SparseStrictCriticalDenominator.critical_limits B P hB
  have hr : (fun m : ℕ =>
      μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent ((2 * m) ^ 3) X
        (1 / Real.sqrt (2 * (m : ℝ)))) /
      Shao.Probability.BrownianSup.probability B P hB
        (1 / Real.sqrt (2 * (m : ℝ)))) =ᶠ[atTop]
      SparseStrictCriticalDenominator.randomRatio B P hB := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hx := (SparseCriticalDenominator.critical_scale m hm).2.2.2.1
    have hp := source_probability_pair μ X hIndep hLaw
      (SparseCriticalDenominator.time m) (SparseCriticalDenominator.criticalX m)
    change μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent ((2 * m) ^ 3) X
        (1 / Real.sqrt (2 * (m : ℝ)))) /
      Shao.Probability.BrownianSup.probability B P hB
        (1 / Real.sqrt (2 * (m : ℝ))) =
      (SparseCriticalDenominator.pathLaw (SparseCriticalDenominator.time m)).real
        (SparseStrictCriticalDenominator.selfEvent (SparseCriticalDenominator.time m)
          (SparseCriticalDenominator.criticalX m)) /
      Shao.Probability.BrownianSup.probability B P hB
        (SparseCriticalDenominator.criticalX m)
    rw [← hx]
    exact congrArg (fun z : ℝ => z /
      Shao.Probability.BrownianSup.probability B P hB
        (SparseCriticalDenominator.criticalX m))
      (by simpa only [SparseCriticalDenominator.time] using hp.1)
  have hd : (fun m : ℕ =>
      μ.real (sourceDetStrictEvent ((2 * m) ^ 3) X
        (1 / Real.sqrt (2 * (m : ℝ)))) /
      Shao.Probability.BrownianSup.probability B P hB
        (1 / Real.sqrt (2 * (m : ℝ)))) =ᶠ[atTop]
      SparseStrictCriticalDenominator.detRatio B P hB := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hx := (SparseCriticalDenominator.critical_scale m hm).2.2.2.1
    have hp := source_probability_pair μ X hIndep hLaw
      (SparseCriticalDenominator.time m) (SparseCriticalDenominator.criticalX m)
    change μ.real (sourceDetStrictEvent ((2 * m) ^ 3) X
        (1 / Real.sqrt (2 * (m : ℝ)))) /
      Shao.Probability.BrownianSup.probability B P hB
        (1 / Real.sqrt (2 * (m : ℝ))) =
      (SparseCriticalDenominator.pathLaw (SparseCriticalDenominator.time m)).real
        (SparseStrictCriticalDenominator.detEvent (SparseCriticalDenominator.time m)
          (SparseCriticalDenominator.criticalX m)) /
      Shao.Probability.BrownianSup.probability B P hB
        (SparseCriticalDenominator.criticalX m)
    rw [← hx]
    exact congrArg (fun z : ℝ => z /
      Shao.Probability.BrownianSup.probability B P hB
        (SparseCriticalDenominator.criticalX m))
      (by simpa only [SparseCriticalDenominator.time] using hp.2)
  exact ⟨hc.1.congr' hr.symm, hc.2.congr' hd.symm⟩

end Shao.OQ4.SparseOriginalStrictCritical
