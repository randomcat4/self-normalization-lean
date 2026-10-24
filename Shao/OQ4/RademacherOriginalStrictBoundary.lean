/- Exact lead freeze before implementation: 2 definitions, 3 theorems.
   Body-local have/let permitted; no other top-level declaration.
   Original source: oq4/c01/spectrum01.md section 4. -/
import Shao.OQ4.RademacherOriginalIIDTransport
import Shao.OQ4.RademacherStrictCube

set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
universe uX uB

namespace Shao.OQ4.RademacherOriginalStrictBoundary
variable {ΩX : Type uX} [MeasurableSpace ΩX]
variable {ΩB : Type uB} [MeasurableSpace ΩB]

def sourceStrictEvent (n : ℕ) (X : ℕ → ΩX → ℝ) (s : ℝ) : Set ΩX :=
  {ω | ∀ k : ℕ, 1 ≤ k → k ≤ n →
    |∑ i ∈ Finset.range k, X (i + 1) ω| <
      s * Real.sqrt (OriginalIIDWindow.sourceEnergy n X ω)}

def sourceStrictRatio
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (μ : Measure ΩX) (X : ℕ → ΩX → ℝ)
    (j : ℕ) : ℝ :=
  μ.real (sourceStrictEvent (RademacherStrictCube.n j) X
    (RademacherStrictCube.x j)) /
    Shao.Probability.BrownianSup.probability B P hB (RademacherStrictCube.x j)

theorem source_strict_pullback (n : ℕ) (X : ℕ → ΩX → ℝ) (s : ℝ) :
    sourceStrictEvent n X s = OriginalIIDWindow.sourcePath n X ⁻¹'
      RademacherStrictCube.strictSelfNormalizedEvent n s ∧
    sourceStrictEvent 0 X s = Set.univ := by
  classical
  have hprefix (k : ℕ) (hk : k ≤ n) (ω : ΩX) :
      Shao.prefixSum (OriginalIIDWindow.sourcePath n X ω) k =
        ∑ i ∈ Finset.range k, X (i + 1) ω := by
    unfold Shao.prefixSum OriginalIIDWindow.sourcePath
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i hi
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    · intro i hi j hj hij
      exact Fin.ext hij
    · intro j hj
      have hjk := Finset.mem_range.mp hj
      refine ⟨⟨j, lt_of_lt_of_le hjk hk⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjk⟩
    · intro i hi
      rfl
  constructor
  · ext ω
    change (∀ k : ℕ, 1 ≤ k → k ≤ n →
        |∑ i ∈ Finset.range k, X (i + 1) ω| <
          s * Real.sqrt (OriginalIIDWindow.sourceEnergy n X ω)) ↔
      (∀ k : ℕ, 1 ≤ k → k ≤ n →
        |Shao.prefixSum (OriginalIIDWindow.sourcePath n X ω) k| <
          s * RademacherS5Assembly.V (OriginalIIDWindow.sourcePath n X ω))
    constructor
    · intro h k hk hkn
      simpa only [hprefix k hkn ω, RademacherS5Assembly.V,
        OriginalIIDWindow.sourceEnergy] using h k hk hkn
    · intro h k hk hkn
      simpa only [hprefix k hkn ω, RademacherS5Assembly.V,
        OriginalIIDWindow.sourceEnergy] using h k hk hkn
  · ext ω
    simp only [sourceStrictEvent, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro k hk hk0
    omega


theorem source_strict_probability
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) (n : ℕ) (s : ℝ) :
    μ.real (sourceStrictEvent n X s) =
      (RademacherS5Assembly.pathLaw n).real
        (RademacherStrictCube.strictSelfNormalizedEvent n s) := by
  have hpath := RademacherOriginalIIDTransport.sourcePath_identDistrib μ X hIndep hLaw n
  have hm : MeasurableSet (RademacherStrictCube.strictSelfNormalizedEvent n s) :=
    (RademacherStrictCube.measurable_events n 0 s).2.2
  rw [(source_strict_pullback n X s).1]
  exact congrArg ENNReal.toReal (hpath.measure_mem_eq hm)


theorem original_strict_cube_comparison
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) :
    Tendsto (sourceStrictRatio B P hB μ X) atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun j : ℕ => Real.log (sourceStrictRatio B P hB μ X j))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun j : ℕ => RademacherOriginalIIDTransport.sourceRatio B P hB μ X 1
      (RademacherStrictCube.n j)) atTop (𝓝 (Real.exp (Real.pi ^ 2 / 4))) ∧
    Tendsto (fun j : ℕ =>
      μ.real (OriginalIIDWindow.sourceEvent (RademacherStrictCube.n j) X
        (RademacherStrictCube.x j)) /
      μ.real (sourceStrictEvent (RademacherStrictCube.n j) X
        (RademacherStrictCube.x j)))
      atTop (𝓝 (Real.exp (Real.pi ^ 2 / 4))) ∧
    Tendsto (fun j : ℕ =>
      Real.log (μ.real (OriginalIIDWindow.sourceEvent (RademacherStrictCube.n j) X
        (RademacherStrictCube.x j))) -
      Real.log (μ.real (sourceStrictEvent (RademacherStrictCube.n j) X
        (RademacherStrictCube.x j)))) atTop (𝓝 (Real.pi ^ 2 / 4)) ∧
    Tendsto (fun j : ℕ => Real.log (sourceStrictRatio B P hB μ X j) /
      RademacherStrictCube.mainRate j) atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun j : ℕ =>
      Real.log (RademacherOriginalIIDTransport.sourceRatio B P hB μ X 1
        (RademacherStrictCube.n j)) / RademacherStrictCube.mainRate j)
      atTop (𝓝 (0 : ℝ)) := by
  have hstrict (j : ℕ) : sourceStrictRatio B P hB μ X j =
      RademacherStrictCube.strictRatio B P hB j := by
    rw [sourceStrictRatio, source_strict_probability μ X hIndep hLaw]
    change RademacherStrictCube.sourceRatio B P hB j =
      RademacherStrictCube.strictRatio B P hB j
    exact (RademacherStrictCube.strict_source_bridge B P hB j).2.2.2.2
  have hweak (j : ℕ) : RademacherOriginalIIDTransport.sourceRatio B P hB μ X 1
      (RademacherStrictCube.n j) = RademacherStrictCube.weakRatio B P hB j := by
    rcases (RademacherStrictCube.weak_cube_shift B P hB).2 j with
      ⟨hindex, hheight, hx, hbase, hp, hratio⟩
    have hn : 1 ≤ RademacherStrictCube.n j := by
      have h8 := (RademacherStrictCube.cube_geometry.2.1 j).2.1
      omega
    calc
      RademacherOriginalIIDTransport.sourceRatio B P hB μ X 1
          (RademacherStrictCube.n j) =
          RademacherS5Assembly.Qsource B P hB 1 (RademacherStrictCube.n j) := by
        rw [RademacherOriginalIIDTransport.sourceRatio,
          RademacherOriginalIIDTransport.source_probability_eq_product μ X hIndep hLaw]
        rfl
      _ = RademacherS5Assembly.Q B P hB 1 (RademacherStrictCube.n j) :=
        (RademacherS5Assembly.actual_source_event B P hB (by norm_num : (0 : ℝ) < 1) hn).2.2.2.2
      _ = RademacherStrictCube.weakRatio B P hB j := by
        rw [hindex]
        exact hratio.symm
  have hweakprob (j : ℕ) :
      μ.real (OriginalIIDWindow.sourceEvent (RademacherStrictCube.n j) X
        (RademacherStrictCube.x j)) =
      RademacherS5Assembly.p (RademacherStrictCube.n j) (RademacherStrictCube.k j : ℝ) := by
    rcases (RademacherStrictCube.weak_cube_shift B P hB).2 j with
      ⟨hindex, hheight, hx, hbase, hp, hratio⟩
    have hn : 1 ≤ RademacherStrictCube.n j := by
      have h8 := (RademacherStrictCube.cube_geometry.2.1 j).2.1
      omega
    rw [RademacherOriginalIIDTransport.source_probability_eq_product μ X hIndep hLaw]
    simpa only [hx, hheight] using
      (RademacherS5Assembly.actual_source_event B P hB (by norm_num : (0 : ℝ) < 1) hn).2.2.2.1
  have hstrictprob (j : ℕ) :
      μ.real (sourceStrictEvent (RademacherStrictCube.n j) X
        (RademacherStrictCube.x j)) =
      RademacherStrictCube.strictP (RademacherStrictCube.n j)
        (RademacherStrictCube.k j : ℝ) := by
    rw [source_strict_probability μ X hIndep hLaw]
    exact (RademacherStrictCube.strict_source_bridge B P hB j).2.2.2.1
  have hs := RademacherStrictCube.F3_STRICT B P hB
  have hw := RademacherStrictCube.F3_WEAK B P hB
  have ha := RademacherStrictCube.F4_ADJACENT B P hB
  have hn := RademacherStrictCube.F4_NORMALIZED B P hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hs.1.congr' (Eventually.of_forall fun j => (hstrict j).symm)
  · exact hs.2.congr' (Eventually.of_forall fun j => congrArg Real.log (hstrict j).symm)
  · simpa only [RademacherStrictCube.a] using
      hw.1.congr' (Eventually.of_forall fun j => (hweak j).symm)
  · simpa only [RademacherStrictCube.a] using
      ha.1.congr' (Eventually.of_forall fun j => by rw [hweakprob j, hstrictprob j])
  · simpa only [RademacherStrictCube.a] using
      ha.2.congr' (Eventually.of_forall fun j => by rw [hweakprob j, hstrictprob j])
  · exact hn.1.congr' (Eventually.of_forall fun j =>
      congrArg (fun z : ℝ => Real.log z / RademacherStrictCube.mainRate j) (hstrict j).symm)
  · exact hn.2.congr' (Eventually.of_forall fun j =>
      congrArg (fun z : ℝ => Real.log z / RademacherStrictCube.mainRate j) (hweak j).symm)


end Shao.OQ4.RademacherOriginalStrictBoundary
