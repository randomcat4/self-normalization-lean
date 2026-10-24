import Shao.OQ4.RademacherStrictCriticalPhase
import Shao.OQ4.RademacherRealStrictBoundary

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology
universe uX uB

namespace Shao.OQ4.RademacherOriginalStrictCriticalPhase

def sourceRatio {ΩX : Type uX} [MeasurableSpace ΩX]
    {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (μ : Measure ΩX) (X : ℕ → ΩX → ℝ)
    (c : ℝ) (n : ℕ) : ℝ :=
  μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X
    (RademacherS5Assembly.x c n)) /
    Shao.Probability.BrownianSup.probability B P hB
      (RademacherS5Assembly.x c n)

theorem source_probability
    {ΩX : Type uX} [MeasurableSpace ΩX]
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X
      (RademacherS5Assembly.x c n)) =
      RademacherStrictCube.strictP n (RademacherCriticalPhase.height c n) ∧
    μ.real (RademacherRealStrictBoundary.sourceDeterministicStrictEvent n X
      (RademacherCriticalPhase.height c n)) =
      RademacherStrictCube.strictP n (RademacherCriticalPhase.height c n) := by
  constructor
  · rw [RademacherOriginalStrictBoundary.source_strict_probability μ X hIndep hLaw
      n (RademacherS5Assembly.x c n)]
    exact RademacherStrictCriticalPhase.canonical_probability hc n
  · by_cases hn : n = 0
    · subst n
      have he : RademacherRealStrictBoundary.sourceDeterministicStrictEvent 0 X
          (RademacherCriticalPhase.height c 0) = Set.univ := by
        ext ω
        constructor
        · intro _
          trivial
        · intro _ r hr hle
          omega
      rw [he, (RademacherStrictCube.zero_time
        (RademacherCriticalPhase.height c 0) (RademacherS5Assembly.x c 0)).2.1]
      simp
    · exact (RademacherRealStrictBoundary.source_ceil_boundary_bridge μ X hIndep hLaw
        n (RademacherCriticalPhase.height c n)
        (RademacherCriticalPhase.positive_time hc
          (Nat.one_le_iff_ne_zero.mpr hn)).2.1).2.2.1

theorem sourceRatio_eq
    {ΩX : Type uX} [MeasurableSpace ΩX]
    {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    sourceRatio B P hB μ X c n = RademacherStrictCriticalPhase.Q B P hB c n ∧
    μ.real (RademacherRealStrictBoundary.sourceDeterministicStrictEvent n X
      (RademacherCriticalPhase.height c n)) /
        Shao.Probability.BrownianSup.probability B P hB
          (RademacherS5Assembly.x c n) = RademacherStrictCriticalPhase.Q B P hB c n := by
  obtain ⟨hs, hd⟩ := source_probability μ X hIndep hLaw hc n
  constructor
  · unfold sourceRatio RademacherStrictCriticalPhase.Q
    rw [hs]
  · unfold RademacherStrictCriticalPhase.Q
    rw [hd]

theorem original_main
    {ΩX : Type uX} [MeasurableSpace ΩX]
    {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) {c : ℝ} (hc : 0 < c) :
    (∀ᶠ n : ℕ in atTop,
      0 < μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X
        (RademacherS5Assembly.x c n)) ∧
      0 < μ.real (RademacherRealStrictBoundary.sourceDeterministicStrictEvent n X
        (RademacherCriticalPhase.height c n)) ∧
      0 < Shao.Probability.BrownianSup.probability B P hB
        (RademacherS5Assembly.x c n) ∧
      0 < sourceRatio B P hB μ X c n) ∧
    Tendsto (fun n : ℕ => Real.log (sourceRatio B P hB μ X c n) -
      RademacherStrictCriticalPhase.exponent c n) atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun n : ℕ => sourceRatio B P hB μ X c n /
      RademacherStrictCriticalPhase.factor c n) atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun n : ℕ => sourceRatio B P hB μ X c n -
      RademacherStrictCriticalPhase.factor c n) atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨hp, hl, hr, hd⟩ := RademacherStrictCriticalPhase.critical_main B P hB hc
  have hR : sourceRatio B P hB μ X c = RademacherStrictCriticalPhase.Q B P hB c := by
    funext n
    exact (sourceRatio_eq B P hB μ X hIndep hLaw hc n).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hp] with n hn
    obtain ⟨hs, hdet⟩ := source_probability μ X hIndep hLaw hc n
    refine ⟨?_, ?_, hn.2.1, ?_⟩
    · rw [hs]
      exact hn.1
    · rw [hdet]
      exact hn.1
    · rw [congrFun hR n]
      exact hn.2.2
  · simpa only [hR] using hl
  · simpa only [hR] using hr
  · simpa only [hR] using hd

theorem original_cluster
    {ΩX : Type uX} [MeasurableSpace ΩX]
    {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) {c : ℝ} (hc : 0 < c) :
    RademacherCriticalPhase.Cluster (sourceRatio B P hB μ X c) =
      Set.Icc (1 : ℝ) (Real.exp (RademacherCriticalPhase.q c)) ∧
    RademacherCriticalPhase.Cluster (fun n : ℕ =>
      μ.real (RademacherRealStrictBoundary.sourceDeterministicStrictEvent n X
        (RademacherCriticalPhase.height c n)) /
        Shao.Probability.BrownianSup.probability B P hB
          (RademacherS5Assembly.x c n)) =
      Set.Icc (1 : ℝ) (Real.exp (RademacherCriticalPhase.q c)) ∧
    (¬ ∃ L : ℝ, Tendsto (sourceRatio B P hB μ X c) atTop (𝓝 L)) ∧
    (¬ ∃ L : ℝ, Tendsto (fun n : ℕ =>
      μ.real (RademacherRealStrictBoundary.sourceDeterministicStrictEvent n X
        (RademacherCriticalPhase.height c n)) /
        Shao.Probability.BrownianSup.probability B P hB
          (RademacherS5Assembly.x c n)) atTop (𝓝 L)) := by
  have hR : sourceRatio B P hB μ X c = RademacherStrictCriticalPhase.Q B P hB c := by
    funext n
    exact (sourceRatio_eq B P hB μ X hIndep hLaw hc n).1
  have hD : (fun n : ℕ =>
      μ.real (RademacherRealStrictBoundary.sourceDeterministicStrictEvent n X
        (RademacherCriticalPhase.height c n)) /
        Shao.Probability.BrownianSup.probability B P hB
          (RademacherS5Assembly.x c n)) = RademacherStrictCriticalPhase.Q B P hB c := by
    funext n
    exact (sourceRatio_eq B P hB μ X hIndep hLaw hc n).2
  have hC := (RademacherStrictCriticalPhase.cluster_sets B P hB hc).2.2.2
  have hN := (RademacherStrictCriticalPhase.not_convergent B P hB hc).2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hR] using hC
  · simpa only [hD] using hC
  · simpa only [hR] using hN
  · simpa only [hD] using hN

end Shao.OQ4.RademacherOriginalStrictCriticalPhase
end
