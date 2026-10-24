import Shao.OQ4.RademacherOriginalStrictBoundary
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
universe uX

namespace Shao.OQ4.RademacherRealStrictBoundary

def sourceDeterministicStrictEvent {ΩX : Type uX}
    (n : ℕ) (X : ℕ → ΩX → ℝ) (h : ℝ) : Set ΩX :=
  {ω | ∀ r : ℕ, 1 ≤ r → r ≤ n →
    |∑ i ∈ Finset.range r, X (i + 1) ω| < h}

theorem ceil_boundary_bridge (N : ℕ) (h : ℝ) (hh : 0 < h) :
    1 ≤ Nat.ceil h ∧
    (((Nat.ceil h - 1 : ℕ) : ℝ) = (Nat.ceil h : ℝ) - 1) ∧
    ((Nat.ceil h - 1 : ℕ) : ℝ) < h ∧
    h ≤ (Nat.ceil h : ℝ) ∧
    (∀ v : Shao.Path N,
      (∀ r : ℕ, r ≤ N → ∃ z : ℤ, Shao.prefixSum v r = (z : ℝ)) →
      (v ∈ RademacherStrictCube.strictEvent N h ↔
        v ∈ @Shao.closedStrip N ((Nat.ceil h - 1 : ℕ) : ℝ))) ∧
    (∀ᵐ v ∂(RademacherS5Assembly.pathLaw N),
      v ∈ RademacherStrictCube.strictEvent N h ↔
        v ∈ @Shao.closedStrip N ((Nat.ceil h - 1 : ℕ) : ℝ)) ∧
    RademacherStrictCube.strictP N h =
      RademacherS5Assembly.p N ((Nat.ceil h - 1 : ℕ) : ℝ)
 := by
  classical
  have hC : 1 ≤ Nat.ceil h := Nat.one_le_ceil_iff.mpr hh
  have hcast : ((Nat.ceil h - 1 : ℕ) : ℝ) = (Nat.ceil h : ℝ) - 1 := by
    rw [Nat.cast_sub hC]
    norm_num
  have hsmall : ((Nat.ceil h - 1 : ℕ) : ℝ) < h := by
    apply Nat.lt_ceil.mp
    omega
  have hle : h ≤ (Nat.ceil h : ℝ) := Nat.le_ceil h
  have hscalar (z : ℤ) : |(z : ℝ)| < h ↔
      |(z : ℝ)| ≤ ((Nat.ceil h - 1 : ℕ) : ℝ) := by
    have hz : |(z : ℝ)| = (z.natAbs : ℝ) := by
      calc
        |(z : ℝ)| = ((|z| : ℤ) : ℝ) := Int.cast_abs.symm
        _ = (((z.natAbs : ℕ) : ℤ) : ℝ) :=
          congrArg (fun k : ℤ => (k : ℝ)) (Int.natCast_natAbs z).symm
        _ = (z.natAbs : ℝ) := Int.cast_natCast z.natAbs
    rw [hz, ← Nat.lt_ceil, Nat.cast_le]
    omega
  have hpoint (v : Shao.Path N)
      (hv : ∀ r : ℕ, r ≤ N → ∃ z : ℤ, Shao.prefixSum v r = (z : ℝ)) :
      v ∈ RademacherStrictCube.strictEvent N h ↔
        v ∈ @Shao.closedStrip N ((Nat.ceil h - 1 : ℕ) : ℝ) := by
    change (∀ r : ℕ, 1 ≤ r → r ≤ N → |Shao.prefixSum v r| < h) ↔
      ∀ r : ℕ, r ≤ N → |Shao.prefixSum v r| ≤ ((Nat.ceil h - 1 : ℕ) : ℝ)
    have hi (r : ℕ) (hr : r ≤ N) : |Shao.prefixSum v r| < h ↔
        |Shao.prefixSum v r| ≤ ((Nat.ceil h - 1 : ℕ) : ℝ) := by
      rcases hv r hr with ⟨z, hz⟩
      rw [hz]
      exact hscalar z
    constructor
    · intro hv' r hr
      by_cases h0 : r = 0
      · subst r
        simp [Shao.prefixSum]
      · exact (hi r hr).1 (hv' r (by omega) hr)
    · intro hv' r _ hr
      exact (hi r hr).2 (hv' r hr)
  have he : ∀ᵐ v ∂(RademacherS5Assembly.pathLaw N),
      v ∈ RademacherStrictCube.strictEvent N h ↔
        v ∈ @Shao.closedStrip N ((Nat.ceil h - 1 : ℕ) : ℝ) := by
    filter_upwards [(RademacherStrictCube.actual_path_support N).2.2] with v hv
    exact hpoint v hv.2.1
  refine ⟨hC, hcast, hsmall, hle, hpoint, he, ?_⟩
  change ((RademacherS5Assembly.pathLaw N)
      (RademacherStrictCube.strictEvent N h)).toReal =
    ((RademacherS5Assembly.pathLaw N)
      (@Shao.closedStrip N ((Nat.ceil h - 1 : ℕ) : ℝ))).toReal
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [he] with v hv
  exact propext hv

theorem source_ceil_boundary_bridge
    {ΩX : Type uX} [MeasurableSpace ΩX]
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) (n : ℕ) (h : ℝ) (hh : 0 < h) :
    sourceDeterministicStrictEvent n X h =
      OriginalIIDWindow.sourcePath n X ⁻¹'
        RademacherStrictCube.strictEvent n h ∧
    (∀ᵐ ω ∂μ,
      ω ∈ sourceDeterministicStrictEvent n X h ↔
        ∀ r : ℕ, r ≤ n →
          |∑ i ∈ Finset.range r, X (i + 1) ω| ≤
            ((Nat.ceil h - 1 : ℕ) : ℝ)) ∧
    μ.real (sourceDeterministicStrictEvent n X h) =
      RademacherStrictCube.strictP n h ∧
    μ.real (sourceDeterministicStrictEvent n X h) =
      RademacherS5Assembly.p n ((Nat.ceil h - 1 : ℕ) : ℝ)
 := by
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
  have hpull : sourceDeterministicStrictEvent n X h =
      OriginalIIDWindow.sourcePath n X ⁻¹'
        RademacherStrictCube.strictEvent n h := by
    ext ω
    change (∀ r : ℕ, 1 ≤ r → r ≤ n →
        |∑ i ∈ Finset.range r, X (i + 1) ω| < h) ↔
      (∀ r : ℕ, 1 ≤ r → r ≤ n →
        |Shao.prefixSum (OriginalIIDWindow.sourcePath n X ω) r| < h)
    constructor
    · intro hω r h1 hr
      simpa only [hprefix r hr ω] using hω r h1 hr
    · intro hω r h1 hr
      simpa only [hprefix r hr ω] using hω r h1 hr
  have hpath := RademacherOriginalIIDTransport.sourcePath_identDistrib μ X hIndep hLaw n
  have hmA := (RademacherStrictCube.measurable_events n h 0).1
  have hmB := (RademacherStrictCube.measurable_events n
    ((Nat.ceil h - 1 : ℕ) : ℝ) 0).2.1
  let D : Set (Shao.Path n) :=
    (RademacherStrictCube.strictEvent n h \ @Shao.closedStrip n ((Nat.ceil h - 1 : ℕ) : ℝ)) ∪
    (@Shao.closedStrip n ((Nat.ceil h - 1 : ℕ) : ℝ) \ RademacherStrictCube.strictEvent n h)
  have hmD : MeasurableSet D := (hmA.diff hmB).union (hmB.diff hmA)
  have hDzero : RademacherS5Assembly.pathLaw n D = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [(ceil_boundary_bridge n h hh).2.2.2.2.2.1] with v hv
    simp only [D, Set.mem_union, Set.mem_sdiff]
    tauto
  have hsourcezero : μ (OriginalIIDWindow.sourcePath n X ⁻¹' D) = 0 := by
    rw [hpath.measure_mem_eq hmD]
    exact hDzero
  have he : ∀ᵐ ω ∂μ,
      ω ∈ sourceDeterministicStrictEvent n X h ↔
        ∀ r : ℕ, r ≤ n → |∑ i ∈ Finset.range r, X (i + 1) ω| ≤
          ((Nat.ceil h - 1 : ℕ) : ℝ) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hsourcezero] with ω hω
    have hiff : OriginalIIDWindow.sourcePath n X ω ∈ RademacherStrictCube.strictEvent n h ↔
        OriginalIIDWindow.sourcePath n X ω ∈ @Shao.closedStrip n ((Nat.ceil h - 1 : ℕ) : ℝ) := by
      change OriginalIIDWindow.sourcePath n X ω ∉ D at hω
      simp only [D, Set.mem_union, Set.mem_sdiff] at hω
      tauto
    rw [hpull]
    change (OriginalIIDWindow.sourcePath n X ω ∈ RademacherStrictCube.strictEvent n h) ↔ _
    rw [hiff]
    change (∀ r : ℕ, r ≤ n →
      |Shao.prefixSum (OriginalIIDWindow.sourcePath n X ω) r| ≤ _) ↔ _
    constructor <;> intro hω r hr <;> simpa only [hprefix r hr ω] using hω r hr
  have hprob : μ.real (sourceDeterministicStrictEvent n X h) =
      RademacherStrictCube.strictP n h := by
    rw [hpull]
    exact congrArg ENNReal.toReal (hpath.measure_mem_eq hmA)
  exact ⟨hpull, he, hprob, hprob.trans (ceil_boundary_bridge n h hh).2.2.2.2.2.2⟩

theorem noninteger_boundary
    {ΩX : Type uX} [MeasurableSpace ΩX]
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law)
    (n : ℕ) (h : ℝ) (hh : 0 < h)
    (hNoninteger : ∀ z : ℤ, h ≠ (z : ℝ)) :
    (∀ᵐ v ∂(RademacherS5Assembly.pathLaw n),
      v ∈ RademacherStrictCube.strictEvent n h ↔
        v ∈ @Shao.closedStrip n h) ∧
    RademacherStrictCube.strictP n h = RademacherS5Assembly.p n h ∧
    (∀ᵐ ω ∂μ,
      ω ∈ sourceDeterministicStrictEvent n X h ↔
        ∀ r : ℕ, r ≤ n →
          |∑ i ∈ Finset.range r, X (i + 1) ω| ≤ h) ∧
    μ.real (sourceDeterministicStrictEvent n X h) =
      μ.real {ω | ∀ r : ℕ, r ≤ n →
        |∑ i ∈ Finset.range r, X (i + 1) ω| ≤ h} ∧
    μ.real (sourceDeterministicStrictEvent n X h) =
      RademacherS5Assembly.p n h
 := by
  classical
  have hpoint (v : Shao.Path n)
      (hv : ∀ r : ℕ, r ≤ n → ∃ z : ℤ, Shao.prefixSum v r = (z : ℝ)) :
      v ∈ RademacherStrictCube.strictEvent n h ↔ v ∈ @Shao.closedStrip n h := by
    change (∀ r : ℕ, 1 ≤ r → r ≤ n → |Shao.prefixSum v r| < h) ↔
      ∀ r : ℕ, r ≤ n → |Shao.prefixSum v r| ≤ h
    constructor
    · intro hω r hr
      by_cases h0 : r = 0
      · subst r
        simpa only [Shao.prefixSum_zero, abs_zero] using hh.le
      · exact (hω r (by omega) hr).le
    · intro hω r _ hr
      apply lt_of_le_of_ne (hω r hr)
      rcases hv r hr with ⟨z, hz⟩
      rw [hz, ← Int.cast_abs]
      exact Ne.symm (hNoninteger |z|)
  have he : ∀ᵐ v ∂(RademacherS5Assembly.pathLaw n),
      v ∈ RademacherStrictCube.strictEvent n h ↔ v ∈ @Shao.closedStrip n h := by
    filter_upwards [(RademacherStrictCube.actual_path_support n).2.2] with v hv
    exact hpoint v hv.2.1
  have hp : RademacherStrictCube.strictP n h = RademacherS5Assembly.p n h := by
    change ((RademacherS5Assembly.pathLaw n) (RademacherStrictCube.strictEvent n h)).toReal =
      ((RademacherS5Assembly.pathLaw n) (@Shao.closedStrip n h)).toReal
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [he] with v hv
    exact propext hv
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
  have hpull := (source_ceil_boundary_bridge μ X hIndep hLaw n h hh).1
  have hpath := RademacherOriginalIIDTransport.sourcePath_identDistrib μ X hIndep hLaw n
  have hmA := (RademacherStrictCube.measurable_events n h 0).1
  have hmB := (RademacherStrictCube.measurable_events n h 0).2.1
  let D : Set (Shao.Path n) :=
    (RademacherStrictCube.strictEvent n h \ @Shao.closedStrip n h) ∪
    (@Shao.closedStrip n h \ RademacherStrictCube.strictEvent n h)
  have hmD : MeasurableSet D := (hmA.diff hmB).union (hmB.diff hmA)
  have hDzero : RademacherS5Assembly.pathLaw n D = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [he] with v hv
    simp only [D, Set.mem_union, Set.mem_sdiff]
    tauto
  have hsourcezero : μ (OriginalIIDWindow.sourcePath n X ⁻¹' D) = 0 := by
    rw [hpath.measure_mem_eq hmD]
    exact hDzero
  have hesource : ∀ᵐ ω ∂μ,
      ω ∈ sourceDeterministicStrictEvent n X h ↔
        ∀ r : ℕ, r ≤ n → |∑ i ∈ Finset.range r, X (i + 1) ω| ≤ h := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hsourcezero] with ω hω
    have hiff : OriginalIIDWindow.sourcePath n X ω ∈ RademacherStrictCube.strictEvent n h ↔
        OriginalIIDWindow.sourcePath n X ω ∈ @Shao.closedStrip n h := by
      change OriginalIIDWindow.sourcePath n X ω ∉ D at hω
      simp only [D, Set.mem_union, Set.mem_sdiff] at hω
      tauto
    rw [hpull]
    change (OriginalIIDWindow.sourcePath n X ω ∈ RademacherStrictCube.strictEvent n h) ↔ _
    rw [hiff]
    change (∀ r : ℕ, r ≤ n →
      |Shao.prefixSum (OriginalIIDWindow.sourcePath n X ω) r| ≤ h) ↔ _
    constructor <;> intro hω r hr <;> simpa only [hprefix r hr ω] using hω r hr
  have hpsource : μ.real (sourceDeterministicStrictEvent n X h) =
      RademacherStrictCube.strictP n h :=
    (source_ceil_boundary_bridge μ X hIndep hLaw n h hh).2.2.1
  refine ⟨he, hp, hesource, ?_, hpsource.trans hp⟩
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hesource] with ω hω
  exact propext hω

end Shao.OQ4.RademacherRealStrictBoundary
end
