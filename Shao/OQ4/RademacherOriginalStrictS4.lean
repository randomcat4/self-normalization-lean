import Shao.OQ4.RademacherGeneralStrictS4

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology
universe uX uB

namespace Shao.OQ4.RademacherOriginalStrictS4

def sourceQ {ΩX : Type uX} [MeasurableSpace ΩX]
    {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (μ : Measure ΩX) (X : ℕ → ΩX → ℝ)
    (n : ℕ) (h : ℝ) : ℝ :=
  μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X
    (h / Real.sqrt (n : ℝ))) /
    Shao.Probability.BrownianSup.probability B P hB
      (h / Real.sqrt (n : ℝ))

theorem source_strict_probability
    {ΩX : Type uX} [MeasurableSpace ΩX]
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) (n : ℕ) (h : ℝ) :
    μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X
      (h / Real.sqrt (n : ℝ))) = RademacherStrictCube.strictP n h := by
  rw [RademacherOriginalStrictBoundary.source_strict_probability μ X hIndep hLaw
    n (h / Real.sqrt (n : ℝ))]
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero]
    rw [(RademacherStrictCube.zero_time h (h / Real.sqrt (0 : ℝ))).2.2.2,
      (RademacherStrictCube.zero_time h (h / Real.sqrt (0 : ℝ))).2.1]
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnpos).ne'
    change ((RademacherS5Assembly.pathLaw n)
      (RademacherStrictCube.strictSelfNormalizedEvent n (h / Real.sqrt (n : ℝ)))).toReal =
      ((RademacherS5Assembly.pathLaw n) (RademacherStrictCube.strictEvent n h)).toReal
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [(RademacherStrictCube.actual_path_support n).2.2] with v hv
    have hnorm : (h / Real.sqrt (n : ℝ)) * RademacherS5Assembly.V v = h := by
      rw [hv.2.2.2]
      exact div_mul_cancel₀ h hsqrt
    change (∀ r : ℕ, 1 ≤ r → r ≤ n →
      |Shao.prefixSum v r| < (h / Real.sqrt (n : ℝ)) * RademacherS5Assembly.V v) =
      (∀ r : ℕ, 1 ≤ r → r ≤ n → |Shao.prefixSum v r| < h)
    rw [hnorm]


theorem original_strict_S4
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
    (∀ k : ℕ, sourceQ B P hB μ X (n_ k) (h_ k) =
      RademacherGeneralStrictS4.Q B P hB (n_ k) (h_ k)) ∧
    (∀ᶠ k : ℕ in atTop,
      0 < μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent (n_ k) X
        (h_ k / Real.sqrt (n_ k : ℝ))) ∧
      0 < μ.real (RademacherRealStrictBoundary.sourceDeterministicStrictEvent
        (n_ k) X (h_ k)) ∧
      0 < Shao.Probability.BrownianSup.probability B P hB
        (h_ k / Real.sqrt (n_ k : ℝ)) ∧
      0 < sourceQ B P hB μ X (n_ k) (h_ k) ∧
      0 < μ.real (RademacherRealStrictBoundary.sourceDeterministicStrictEvent
        (n_ k) X (h_ k)) /
        Shao.Probability.BrownianSup.probability B P hB
          (h_ k / Real.sqrt (n_ k : ℝ))) ∧
    Tendsto (fun k : ℕ =>
      Real.log (sourceQ B P hB μ X (n_ k) (h_ k)) -
        RademacherGeneralStrictS4.correction (n_ k) (h_ k))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun k : ℕ =>
      sourceQ B P hB μ X (n_ k) (h_ k) /
        Real.exp (RademacherGeneralStrictS4.correction (n_ k) (h_ k)))
      atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun k : ℕ =>
      Real.log (μ.real (RademacherRealStrictBoundary.sourceDeterministicStrictEvent
        (n_ k) X (h_ k)) /
        Shao.Probability.BrownianSup.probability B P hB
          (h_ k / Real.sqrt (n_ k : ℝ))) -
        RademacherGeneralStrictS4.correction (n_ k) (h_ k))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun k : ℕ =>
      (μ.real (RademacherRealStrictBoundary.sourceDeterministicStrictEvent
        (n_ k) X (h_ k)) /
        Shao.Probability.BrownianSup.probability B P hB
          (h_ k / Real.sqrt (n_ k : ℝ))) /
        Real.exp (RademacherGeneralStrictS4.correction (n_ k) (h_ k)))
      atTop (𝓝 (1 : ℝ)) := by
  obtain ⟨hpos, hlog, hratio⟩ :=
    RademacherGeneralStrictS4.strict_S4_EVENTUAL B P hB n_ h_ hh hscale2 hscale3
  have hsource (n : ℕ) (h : ℝ) :
      μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X
        (h / Real.sqrt (n : ℝ))) = RademacherStrictCube.strictP n h :=
    source_strict_probability μ X hIndep hLaw n h
  have hQ (k : ℕ) : sourceQ B P hB μ X (n_ k) (h_ k) =
      RademacherGeneralStrictS4.Q B P hB (n_ k) (h_ k) := by
    unfold sourceQ RademacherGeneralStrictS4.Q
    rw [hsource]
  have hdet : ∀ᶠ k : ℕ in atTop,
      μ.real (RademacherRealStrictBoundary.sourceDeterministicStrictEvent
        (n_ k) X (h_ k)) = RademacherStrictCube.strictP (n_ k) (h_ k) := by
    have hhp : ∀ᶠ k : ℕ in atTop, 0 < h_ k :=
      hh.eventually (eventually_gt_atTop (0 : ℝ))
    filter_upwards [hhp] with k hk
    exact (RademacherRealStrictBoundary.source_ceil_boundary_bridge
      μ X hIndep hLaw (n_ k) (h_ k) hk).2.2.1
  have hsourceLog : Tendsto (fun k : ℕ =>
      Real.log (sourceQ B P hB μ X (n_ k) (h_ k)) -
        RademacherGeneralStrictS4.correction (n_ k) (h_ k))
      atTop (𝓝 (0 : ℝ)) := by
    apply hlog.congr'
    exact Filter.Eventually.of_forall fun k =>
      congrArg (fun z : ℝ => Real.log z -
        RademacherGeneralStrictS4.correction (n_ k) (h_ k)) (hQ k).symm
  have hsourceRatio : Tendsto (fun k : ℕ =>
      sourceQ B P hB μ X (n_ k) (h_ k) /
        Real.exp (RademacherGeneralStrictS4.correction (n_ k) (h_ k)))
      atTop (𝓝 (1 : ℝ)) := by
    apply hratio.congr'
    exact Filter.Eventually.of_forall fun k =>
      congrArg (fun z : ℝ => z /
        Real.exp (RademacherGeneralStrictS4.correction (n_ k) (h_ k))) (hQ k).symm
  have hdetRatioEq : (fun k : ℕ =>
      μ.real (RademacherRealStrictBoundary.sourceDeterministicStrictEvent
        (n_ k) X (h_ k)) /
        Shao.Probability.BrownianSup.probability B P hB
          (h_ k / Real.sqrt (n_ k : ℝ))) =ᶠ[atTop]
      (fun k : ℕ => sourceQ B P hB μ X (n_ k) (h_ k)) := by
    filter_upwards [hdet] with k hk
    unfold sourceQ
    rw [hk, hsource]
  have hdetLog : Tendsto (fun k : ℕ =>
      Real.log (μ.real (RademacherRealStrictBoundary.sourceDeterministicStrictEvent
        (n_ k) X (h_ k)) /
        Shao.Probability.BrownianSup.probability B P hB
          (h_ k / Real.sqrt (n_ k : ℝ))) -
        RademacherGeneralStrictS4.correction (n_ k) (h_ k))
      atTop (𝓝 (0 : ℝ)) := by
    apply hsourceLog.congr'
    exact hdetRatioEq.symm.mono fun k hk =>
      congrArg (fun z : ℝ => Real.log z -
        RademacherGeneralStrictS4.correction (n_ k) (h_ k)) hk
  have hdetRatio : Tendsto (fun k : ℕ =>
      (μ.real (RademacherRealStrictBoundary.sourceDeterministicStrictEvent
        (n_ k) X (h_ k)) /
        Shao.Probability.BrownianSup.probability B P hB
          (h_ k / Real.sqrt (n_ k : ℝ))) /
        Real.exp (RademacherGeneralStrictS4.correction (n_ k) (h_ k)))
      atTop (𝓝 (1 : ℝ)) := by
    apply hsourceRatio.congr'
    exact hdetRatioEq.symm.mono fun k hk =>
      congrArg (fun z : ℝ => z /
        Real.exp (RademacherGeneralStrictS4.correction (n_ k) (h_ k))) hk
  refine ⟨hQ, ?_, hsourceLog, hsourceRatio, hdetLog, hdetRatio⟩
  filter_upwards [hpos, hdet] with k hk hd
  have hpsource : 0 < μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent
      (n_ k) X (h_ k / Real.sqrt (n_ k : ℝ))) := by
    rw [hsource]
    exact hk.1
  have hpdet : 0 < μ.real
      (RademacherRealStrictBoundary.sourceDeterministicStrictEvent (n_ k) X (h_ k)) := by
    rw [hd]
    exact hk.1
  have hqsource : 0 < sourceQ B P hB μ X (n_ k) (h_ k) := by
    rw [hQ]
    exact hk.2.2
  exact ⟨hpsource, hpdet, hk.2.1, hqsource, div_pos hpdet hk.2.1⟩


end Shao.OQ4.RademacherOriginalStrictS4
end
