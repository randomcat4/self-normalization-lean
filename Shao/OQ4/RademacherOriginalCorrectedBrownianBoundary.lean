import Shao.OQ4.RademacherCorrectedBrownianBoundary
import Shao.OQ4.RademacherOriginalIIDTransport
import Shao.OQ4.RademacherOriginalStrictS4
import Shao.OQ4.StrictIIDWindow

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
universe uX uB

namespace Shao.OQ4.RademacherOriginalCorrectedBrownianBoundary

private theorem source_weak_probability
    {ΩX : Type uX} [MeasurableSpace ΩX]
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) (n : ℕ) (hn : 0 < n) (h : ℝ) :
    μ.real (OriginalIIDWindow.sourceEvent n X (h / Real.sqrt (n : ℝ))) =
      RademacherS4Assembly.p n h := by
  rw [RademacherOriginalIIDTransport.source_probability_eq_product
    μ X hIndep hLaw n (h / Real.sqrt (n : ℝ))]
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have hsets : RademacherS5Assembly.selfNormalizedEvent n
      (h / Real.sqrt (n : ℝ)) =ᵐ[RademacherS5Assembly.pathLaw n]
      @Shao.closedStrip n h := by
    filter_upwards [(RademacherS5Assembly.actual_path_energy n).2] with a ha
    have hv : RademacherS5Assembly.V a = Real.sqrt (n : ℝ) := ha.2.2
    have hmul : (h / Real.sqrt (n : ℝ)) * RademacherS5Assembly.V a = h := by
      rw [hv]
      exact div_mul_cancel₀ h hsqrt
    simp only [RademacherS5Assembly.selfNormalizedEvent, Shao.closedStrip,
      Set.mem_setOf_eq, hmul]
  change ((RademacherS5Assembly.pathLaw n)
      (RademacherS5Assembly.selfNormalizedEvent n (h / Real.sqrt (n : ℝ)))).toReal =
    ((RademacherS5Assembly.pathLaw n) (@Shao.closedStrip n h)).toReal
  exact congrArg ENNReal.toReal (measure_congr hsets)

-- Proof: qualified original/product transport, actual_path_energy, sqrt n>0,
-- and almost-everywhere equality with the actual closedStrip.

private theorem source_strict_max_probability
    {ΩX : Type uX} [MeasurableSpace ΩX]
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) (n : ℕ) (hn : 0 < n) (h : ℝ) :
    μ.real {ω | OriginalIIDWindow.sourceMaximum n X ω <
      (h / Real.sqrt (n : ℝ)) *
        Real.sqrt (OriginalIIDWindow.sourceEnergy n X ω)} =
      RademacherStrictCube.strictP n h := by
  rw [← StrictIIDWindow.source_strict_event_eq_max n hn X
    (h / Real.sqrt (n : ℝ))]
  exact RademacherOriginalStrictS4.source_strict_probability
    μ X hIndep hLaw n h

-- Proof: exact qualified deterministic positive-time max/prefix bridge,
-- then qualified original strict probability identity.

theorem original_weak_corrected_boundary
    {ΩX : Type uX} [MeasurableSpace ΩX]
    {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law)
    (n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hh : Tendsto h_ atTop atTop)
    (hscale2 : Tendsto
      (fun k : ℕ => (n_ k : ℝ) / (h_ k) ^ 2) atTop atTop)
    (hscale3 : ∃ M : ℝ, 0 < M ∧
      ∃ K_M : ℕ, ∀ k : ℕ, K_M ≤ k →
        (n_ k : ℝ) / (h_ k) ^ 3 ≤ M) :
    (∀ᶠ k : ℕ in atTop,
      0 < μ.real (OriginalIIDWindow.sourceEvent (n_ k) X
        (h_ k / Real.sqrt (n_ k : ℝ))) ∧
      0 < Shao.Probability.BrownianSup.probability B P hB
        (RademacherCorrectedBrownianBoundary.weakHeight (h_ k) /
          Real.sqrt (n_ k : ℝ))) ∧
    Tendsto (fun k : ℕ =>
      μ.real (OriginalIIDWindow.sourceEvent (n_ k) X
        (h_ k / Real.sqrt (n_ k : ℝ))) /
      Shao.Probability.BrownianSup.probability B P hB
        (RademacherCorrectedBrownianBoundary.weakHeight (h_ k) /
          Real.sqrt (n_ k : ℝ))) atTop (𝓝 (1 : ℝ)) := by
  have hnpos : ∀ᶠ k : ℕ in atTop, 0 < n_ k := by
    filter_upwards [hscale2.eventually_gt_atTop (0 : ℝ)] with k hk
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, Nat.cast_zero, zero_div] at hk
    exact (lt_irrefl (0 : ℝ)) hk
  have hc := RademacherCorrectedBrownianBoundary.weak_corrected_boundary
    B P hB n_ h_ hh hscale2 hscale3
  refine ⟨?_, ?_⟩
  · filter_upwards [hnpos, hc.1] with k hk hp
    rw [source_weak_probability μ X hIndep hLaw (n_ k) hk (h_ k)]
    exact hp
  · apply hc.2.congr'
    filter_upwards [hnpos] with k hk
    rw [source_weak_probability μ X hIndep hLaw (n_ k) hk (h_ k)]

-- Proof: derive eventual n_>0 from hscale2; transfer qualified canonical
-- positivity and ratio limit by the first finite identity on that tail.

theorem original_strict_corrected_boundary
    {ΩX : Type uX} [MeasurableSpace ΩX]
    {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law)
    (n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hh : Tendsto h_ atTop atTop)
    (hscale2 : Tendsto
      (fun k : ℕ => (n_ k : ℝ) / (h_ k) ^ 2) atTop atTop)
    (hscale3 : ∃ M : ℝ, 0 < M ∧
      ∃ K_M : ℕ, ∀ k : ℕ, K_M ≤ k →
        (n_ k : ℝ) / (h_ k) ^ 3 ≤ M) :
    (∀ᶠ k : ℕ in atTop,
      0 < μ.real {ω | OriginalIIDWindow.sourceMaximum (n_ k) X ω <
        (h_ k / Real.sqrt (n_ k : ℝ)) *
          Real.sqrt (OriginalIIDWindow.sourceEnergy (n_ k) X ω)} ∧
      0 < Shao.Probability.BrownianSup.probability B P hB
        (RademacherCorrectedBrownianBoundary.strictHeight (h_ k) /
          Real.sqrt (n_ k : ℝ))) ∧
    Tendsto (fun k : ℕ =>
      μ.real {ω | OriginalIIDWindow.sourceMaximum (n_ k) X ω <
        (h_ k / Real.sqrt (n_ k : ℝ)) *
          Real.sqrt (OriginalIIDWindow.sourceEnergy (n_ k) X ω)} /
      Shao.Probability.BrownianSup.probability B P hB
        (RademacherCorrectedBrownianBoundary.strictHeight (h_ k) /
          Real.sqrt (n_ k : ℝ))) atTop (𝓝 (1 : ℝ)) := by
  have hnpos : ∀ᶠ k : ℕ in atTop, 0 < n_ k := by
    filter_upwards [hscale2.eventually_gt_atTop (0 : ℝ)] with k hk
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, Nat.cast_zero, zero_div] at hk
    exact (lt_irrefl (0 : ℝ)) hk
  have hc := RademacherCorrectedBrownianBoundary.strict_corrected_boundary
    B P hB n_ h_ hh hscale2 hscale3
  refine ⟨?_, ?_⟩
  · filter_upwards [hnpos, hc.1] with k hk hp
    rw [source_strict_max_probability μ X hIndep hLaw (n_ k) hk (h_ k)]
    exact hp
  · apply hc.2.congr'
    filter_upwards [hnpos] with k hk
    rw [source_strict_max_probability μ X hIndep hLaw (n_ k) hk (h_ k)]

-- Proof: derive eventual n_>0 from hscale2; transfer qualified canonical
-- positivity and ratio limit by the second finite identity on that tail.

end Shao.OQ4.RademacherOriginalCorrectedBrownianBoundary
end
