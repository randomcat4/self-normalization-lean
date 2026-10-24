import Shao.OQ4.RademacherStrictWeakBoundary
import Shao.OQ4.RademacherOriginalStrictS4

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
universe uX

namespace Shao.OQ4.RademacherOriginalStrictWeakBoundary

def sourceRatio {ΩX : Type uX} [MeasurableSpace ΩX]
    (μ : Measure ΩX) (X : ℕ → ΩX → ℝ) (n : ℕ) (h : ℝ) : ℝ :=
  μ.real (OriginalIIDWindow.sourceEvent n X (h / Real.sqrt (n : ℝ))) /
    μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X
      (h / Real.sqrt (n : ℝ)))

theorem source_probabilities
    {ΩX : Type uX} [MeasurableSpace ΩX]
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) (n : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    μ.real (OriginalIIDWindow.sourceEvent n X (h / Real.sqrt (n : ℝ))) =
      RademacherS5Assembly.p n h ∧
    μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X
      (h / Real.sqrt (n : ℝ))) = RademacherStrictCube.strictP n h := by
  constructor
  · rw [RademacherOriginalIIDTransport.source_probability_eq_product μ X hIndep hLaw
      n (h / Real.sqrt (n : ℝ))]
    have hp : RademacherS5Assembly.p n h =
        (RademacherS5Assembly.pathLaw n).real (@Shao.closedStrip n h) := by
      have hd := RademacherS5Assembly.definition_bridges CanonicalBrownian.B
        CanonicalBrownian.law CanonicalBrownian.isBrownianReal (0 : ℝ) n h
      tauto
    rw [hp]
    by_cases hn : n = 0
    · subst n
      have he : RademacherS5Assembly.selfNormalizedEvent 0
          (h / Real.sqrt (0 : ℝ)) = Set.univ := by
        ext v
        constructor
        · intro _
          trivial
        · intro _ r hr
          have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
          subst r
          simp [Shao.prefixSum]
      have hec : @Shao.closedStrip 0 h = Set.univ := by
        ext v
        constructor
        · intro _
          trivial
        · intro _ r hr
          have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
          subst r
          simpa [Shao.prefixSum] using hh
      simp only [Nat.cast_zero]
      rw [he, hec]
    · have hnp : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnp).ne'
      change ((RademacherS5Assembly.pathLaw n)
        (RademacherS5Assembly.selfNormalizedEvent n (h / Real.sqrt (n : ℝ)))).toReal =
        ((RademacherS5Assembly.pathLaw n) (@Shao.closedStrip n h)).toReal
      apply congrArg ENNReal.toReal
      apply measure_congr
      filter_upwards [(RademacherStrictCube.actual_path_support n).2.2] with v hv
      have hnorm : (h / Real.sqrt (n : ℝ)) * RademacherS5Assembly.V v = h := by
        rw [hv.2.2.2]
        exact div_mul_cancel₀ h hsqrt
      change (∀ r : ℕ, r ≤ n →
        |Shao.prefixSum v r| ≤ (h / Real.sqrt (n : ℝ)) * RademacherS5Assembly.V v) =
        (∀ r : ℕ, r ≤ n → |Shao.prefixSum v r| ≤ h)
      rw [hnorm]
  · exact RademacherOriginalStrictS4.source_strict_probability μ X hIndep hLaw n h

theorem sourceRatio_eq
    {ΩX : Type uX} [MeasurableSpace ΩX]
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) (n : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    sourceRatio μ X n h = RademacherStrictWeakBoundary.ratio n h := by
  obtain ⟨hw, hs⟩ := source_probabilities μ X hIndep hLaw n h hh
  unfold sourceRatio RademacherStrictWeakBoundary.ratio
  rw [hw, hs]

theorem original_main
    {ΩX : Type uX} [MeasurableSpace ΩX]
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
      2 ≤ h_ k ∧ 1 ≤ n_ k ∧
      0 < μ.real (OriginalIIDWindow.sourceEvent (n_ k) X
        (h_ k / Real.sqrt (n_ k : ℝ))) ∧
      0 < μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent (n_ k) X
        (h_ k / Real.sqrt (n_ k : ℝ))) ∧
      0 < sourceRatio μ X (n_ k) (h_ k) ∧
      Real.log (sourceRatio μ X (n_ k) (h_ k)) =
        Real.log (μ.real (OriginalIIDWindow.sourceEvent (n_ k) X
          (h_ k / Real.sqrt (n_ k : ℝ)))) -
        Real.log (μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent
          (n_ k) X (h_ k / Real.sqrt (n_ k : ℝ))))) ∧
    Tendsto (fun k : ℕ =>
      Real.log (sourceRatio μ X (n_ k) (h_ k)) -
        (Real.pi ^ 2 / 4) * ((n_ k : ℝ) / (h_ k) ^ 3) *
          RademacherStrictWeakBoundary.integerIndicator (h_ k)) atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun k : ℕ => sourceRatio μ X (n_ k) (h_ k) /
      Real.exp ((Real.pi ^ 2 / 4) * ((n_ k : ℝ) / (h_ k) ^ 3) *
        RademacherStrictWeakBoundary.integerIndicator (h_ k))) atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun k : ℕ => sourceRatio μ X (n_ k) (h_ k) -
      Real.exp ((Real.pi ^ 2 / 4) * ((n_ k : ℝ) / (h_ k) ^ 3) *
        RademacherStrictWeakBoundary.integerIndicator (h_ k))) atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨hp, hl, hr, hd⟩ :=
    RademacherStrictWeakBoundary.boundary_main n_ h_ hh hscale2 hscale3
  have hhn : ∀ᶠ k : ℕ in atTop, 0 ≤ h_ k :=
    hh.eventually (eventually_ge_atTop (0 : ℝ))
  have heq : (fun k : ℕ => sourceRatio μ X (n_ k) (h_ k)) =ᶠ[atTop]
      (fun k : ℕ => RademacherStrictWeakBoundary.ratio (n_ k) (h_ k)) := by
    filter_upwards [hhn] with k hk
    exact sourceRatio_eq μ X hIndep hLaw (n_ k) (h_ k) hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hp] with k hk
    have hk0 : 0 ≤ h_ k := le_trans (by norm_num) hk.1
    obtain ⟨hw, hs⟩ := source_probabilities μ X hIndep hLaw (n_ k) (h_ k) hk0
    have hq := sourceRatio_eq μ X hIndep hLaw (n_ k) (h_ k) hk0
    refine ⟨hk.1, hk.2.1, ?_, ?_, ?_, ?_⟩
    · rw [hw]
      exact hk.2.2.1
    · rw [hs]
      exact hk.2.2.2.1
    · rw [hq]
      exact hk.2.2.2.2.1
    · rw [hq, hw, hs]
      exact hk.2.2.2.2.2
  · apply hl.congr'
    exact heq.symm.mono fun k hk => congrArg
      (fun z : ℝ => Real.log z - (Real.pi ^ 2 / 4) *
        ((n_ k : ℝ) / (h_ k) ^ 3) *
          RademacherStrictWeakBoundary.integerIndicator (h_ k)) hk
  · apply hr.congr'
    exact heq.symm.mono fun k hk => congrArg
      (fun z : ℝ => z / Real.exp ((Real.pi ^ 2 / 4) *
        ((n_ k : ℝ) / (h_ k) ^ 3) *
          RademacherStrictWeakBoundary.integerIndicator (h_ k))) hk
  · apply hd.congr'
    exact heq.symm.mono fun k hk => congrArg
      (fun z : ℝ => z - Real.exp ((Real.pi ^ 2 / 4) *
        ((n_ k : ℝ) / (h_ k) ^ 3) *
          RademacherStrictWeakBoundary.integerIndicator (h_ k))) hk

theorem original_tendsto_iff
    {ΩX : Type uX} [MeasurableSpace ΩX]
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
        (n_ k : ℝ) / (h_ k) ^ 3 ≤ M) (L : ℝ) :
    Tendsto (fun k : ℕ => sourceRatio μ X (n_ k) (h_ k)) atTop (𝓝 L) ↔
      1 ≤ L ∧
      Tendsto (fun k : ℕ =>
        ((n_ k : ℝ) / (h_ k) ^ 3) *
          RademacherStrictWeakBoundary.integerIndicator (h_ k))
        atTop (𝓝 ((4 / Real.pi ^ 2) * Real.log L)) := by
  have hhn : ∀ᶠ k : ℕ in atTop, 0 ≤ h_ k :=
    hh.eventually (eventually_ge_atTop (0 : ℝ))
  have heq : (fun k : ℕ => sourceRatio μ X (n_ k) (h_ k)) =ᶠ[atTop]
      (fun k : ℕ => RademacherStrictWeakBoundary.ratio (n_ k) (h_ k)) := by
    filter_upwards [hhn] with k hk
    exact sourceRatio_eq μ X hIndep hLaw (n_ k) (h_ k) hk
  constructor
  · intro hs
    exact (RademacherStrictWeakBoundary.boundary_tendsto_iff n_ h_ hh hscale2
      hscale3 L).mp (hs.congr' heq)
  · intro hL
    exact ((RademacherStrictWeakBoundary.boundary_tendsto_iff n_ h_ hh hscale2
      hscale3 L).mpr hL).congr' heq.symm

end Shao.OQ4.RademacherOriginalStrictWeakBoundary
end
