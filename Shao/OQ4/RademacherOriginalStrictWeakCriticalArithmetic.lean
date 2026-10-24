import Shao.OQ4.RademacherStrictWeakCriticalArithmetic
import Shao.OQ4.RademacherOriginalStrictWeakBoundary

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
universe uX

namespace Shao.OQ4.RademacherOriginalStrictWeakCriticalArithmetic

def sourceRatio {ΩX : Type uX} [MeasurableSpace ΩX]
    (μ : Measure ΩX) (X : ℕ → ΩX → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  μ.real (OriginalIIDWindow.sourceEvent n X (RademacherS5Assembly.x c n)) /
    μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X
      (RademacherS5Assembly.x c n))

theorem source_probabilities
    {ΩX : Type uX} [MeasurableSpace ΩX]
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    μ.real (OriginalIIDWindow.sourceEvent n X (RademacherS5Assembly.x c n)) =
      RademacherS5Assembly.p n (RademacherCriticalPhase.height c n) ∧
    μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X
      (RademacherS5Assembly.x c n)) =
      RademacherStrictCube.strictP n (RademacherCriticalPhase.height c n) := by
  by_cases hn : n = 0
  · subst n
    have hew : OriginalIIDWindow.sourceEvent 0 X
        (RademacherS5Assembly.x c 0) = Set.univ := by
      ext ω
      simp [OriginalIIDWindow.sourceEvent, OriginalIIDWindow.sourceMaximum,
        OriginalIIDWindow.sourceEnergy, Shao.energy]
    have hw : μ.real (OriginalIIDWindow.sourceEvent 0 X
        (RademacherS5Assembly.x c 0)) = 1 := by
      rw [hew]
      simp
    have hs : μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent 0 X
        (RademacherS5Assembly.x c 0)) = 1 := by
      rw [(RademacherOriginalStrictBoundary.source_strict_pullback 0 X
        (RademacherS5Assembly.x c 0)).2]
      simp
    have hp0' : RademacherS5Assembly.p 0 (RademacherS5Assembly.height c 0) = 1 := by
      have hz := RademacherS5Assembly.zero_time c
      tauto
    have hp0 : RademacherS5Assembly.p 0 (RademacherCriticalPhase.height c 0) = 1 := by
      simpa only [RademacherS5Assembly.height, RademacherS5Assembly.root,
        RademacherCriticalPhase.height, RademacherCriticalPhase.root] using hp0'
    have hs0 : RademacherStrictCube.strictP 0 (RademacherCriticalPhase.height c 0) = 1 :=
      (RademacherStrictCube.zero_time (RademacherCriticalPhase.height c 0) (0 : ℝ)).2.1
    exact ⟨hw.trans hp0.symm, hs.trans hs0.symm⟩
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hpos := RademacherS5Assembly.positive_time hc hn1
    have hx0 : RademacherS5Assembly.x c n = RademacherS5Assembly.height c n /
        Real.sqrt (RademacherS5Assembly.N n) := by
      unfold RademacherS5Assembly.PositiveTime at hpos
      tauto
    have hx : RademacherS5Assembly.x c n = RademacherCriticalPhase.height c n /
        Real.sqrt (n : ℝ) := by
      exact hx0
    rw [hx]
    exact RademacherOriginalStrictWeakBoundary.source_probabilities μ X hIndep hLaw
      n (RademacherCriticalPhase.height c n)
      (mul_nonneg hc.le (RademacherCriticalPhase.root_spec n).1)

theorem sourceRatio_eq
    {ΩX : Type uX} [MeasurableSpace ΩX]
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    sourceRatio μ X c n = RademacherStrictWeakBoundary.criticalRatio c n := by
  obtain ⟨hw, hs⟩ := source_probabilities μ X hIndep hLaw hc n
  unfold sourceRatio RademacherStrictWeakBoundary.criticalRatio
    RademacherStrictWeakBoundary.ratio
  rw [hw, hs]

theorem original_main
    {ΩX : Type uX} [MeasurableSpace ΩX]
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) {c : ℝ} (hc : 0 < c) :
    (∀ᶠ n : ℕ in atTop,
      0 < μ.real (OriginalIIDWindow.sourceEvent n X (RademacherS5Assembly.x c n)) ∧
      0 < μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X
        (RademacherS5Assembly.x c n)) ∧
      0 < sourceRatio μ X c n) ∧
    Tendsto (fun n : ℕ => Real.log (sourceRatio μ X c n) -
      RademacherCriticalPhase.q c * RademacherStrictWeakBoundary.integerIndicator
        (RademacherCriticalPhase.height c n)) atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun n : ℕ => sourceRatio μ X c n /
      Real.exp (RademacherCriticalPhase.q c *
        RademacherStrictWeakBoundary.integerIndicator
          (RademacherCriticalPhase.height c n))) atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun n : ℕ => sourceRatio μ X c n -
      Real.exp (RademacherCriticalPhase.q c *
        RademacherStrictWeakBoundary.integerIndicator
          (RademacherCriticalPhase.height c n))) atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨hp, hl, hr, hd⟩ := RademacherStrictWeakBoundary.critical_main hc
  have heq : sourceRatio μ X c = RademacherStrictWeakBoundary.criticalRatio c := by
    funext n
    exact sourceRatio_eq μ X hIndep hLaw hc n
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hp] with n hn
    obtain ⟨hw, hs⟩ := source_probabilities μ X hIndep hLaw hc n
    refine ⟨?_, ?_, ?_⟩
    · rw [hw]
      exact hn.1
    · rw [hs]
      exact hn.2.1
    · rw [congrFun heq n]
      exact hn.2.2
  · simpa only [heq] using hl
  · simpa only [heq] using hr
  · simpa only [heq] using hd

theorem original_arithmetic
    {ΩX : Type uX} [MeasurableSpace ΩX]
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) {c : ℝ} (hc : 0 < c) :
    ((∃ r : ℚ, (r : ℝ) = c ^ 3) →
      RademacherCriticalPhase.Cluster (sourceRatio μ X c) =
        ({(1 : ℝ), Real.exp (RademacherCriticalPhase.q c)} : Set ℝ) ∧
      (¬ ∃ L : ℝ, Tendsto (sourceRatio μ X c) atTop (𝓝 L))) ∧
    ((¬ ∃ r : ℚ, (r : ℝ) = c ^ 3) →
      (∀ n : ℕ, 1 ≤ n →
        μ.real (OriginalIIDWindow.sourceEvent n X (RademacherS5Assembly.x c n)) =
          μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X
            (RademacherS5Assembly.x c n))) ∧
      (∀ᶠ n : ℕ in atTop, sourceRatio μ X c n = 1) ∧
      Tendsto (sourceRatio μ X c) atTop (𝓝 (1 : ℝ)) ∧
      RademacherCriticalPhase.Cluster (sourceRatio μ X c) = ({(1 : ℝ)} : Set ℝ)) := by
  have heq : sourceRatio μ X c = RademacherStrictWeakBoundary.criticalRatio c := by
    funext n
    exact sourceRatio_eq μ X hIndep hLaw hc n
  constructor
  · intro hRat
    have h := RademacherStrictWeakBoundary.critical_rational hc hRat
    simpa only [heq] using h
  · intro hIrr
    obtain ⟨hfinite, hevent, hlim, hcluster⟩ :=
      RademacherStrictWeakBoundary.critical_irrational hc hIrr
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n hn
      obtain ⟨hw, hs⟩ := source_probabilities μ X hIndep hLaw hc n
      rw [hw, hs]
      exact (hfinite n hn).2
    · simpa only [heq] using hevent
    · simpa only [heq] using hlim
    · simpa only [heq] using hcluster

end Shao.OQ4.RademacherOriginalStrictWeakCriticalArithmetic
end
