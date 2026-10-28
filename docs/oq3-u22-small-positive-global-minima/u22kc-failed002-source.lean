import Shao.OQ3.BoundedParabolaLegendreZeroSet
import Shao.OQ3.BoundedParabolaLegendreCompactSublevels

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem bounded_parabola_legendre_gap_away_mean
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (r : ℝ) (hr : 0 < r) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ z : ℝ × ℝ,
      r ≤ dist z (∫ x : ℝ, x ∂mu, ∫ x : ℝ, x ^ 2 ∂mu) →
        (gap : EReal) ≤ Shao.Probability.bivariateLegendreRate mu
          (fun x : ℝ => (x, x ^ 2)) z := by
  let I : (ℝ × ℝ) → EReal :=
    Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
  let m : ℝ × ℝ := (∫ x : ℝ, x ∂mu, ∫ x : ℝ, x ^ 2 ∂mu)
  have henergy : ∀ᵐ x ∂mu, (0 : ℝ) ≤ x ^ 2 ∧ x ^ 2 ≤ M ^ 2 := by
    filter_upwards [hb] with x hx
    refine ⟨sq_nonneg x, ?_⟩
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hcompact : IsCompact {z : ℝ × ℝ | I z ≤ (1 : EReal)} := by
    simpa using
      (bounded_parabola_legendre_compact_sublevels mu M hM hb 0 (M ^ 2) henergy).2 1
  let C : Set (ℝ × ℝ) := {z | I z ≤ (1 : EReal)} ∩ {z | r ≤ dist z m}
  have hclosed : IsClosed C :=
    ((bivariate_legendre_rate_lower_semicontinuous mu (fun x : ℝ => (x, x ^ 2))).isClosed_preimage
      (1 : EReal)).inter (isClosed_le continuous_const (by fun_prop))
  have hCcompact : IsCompact C := hcompact.of_isClosed_subset hclosed Set.inter_subset_left
  by_cases hnonempty : C.Nonempty
  · obtain ⟨z0, hz0, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hnonempty hCcompact
      ((bivariate_legendre_rate_lower_semicontinuous mu
        (fun x : ℝ => (x, x ^ 2))).lowerSemicontinuousOn C)
    have hne : z0 ≠ m := by
      intro heq
      have h := hz0.2
      simp only [heq] at h
      exact hr.not_ge h
    have hpos : 0 < I z0 :=
      (bounded_parabola_legendre_zero_and_strictly_positive mu M hM hb z0).2.2 hne
    obtain ⟨g, hg0, hglt⟩ := EReal.exists_between_coe_real hpos
    have hg : 0 < g := by exact_mod_cast hg0
    refine ⟨min 1 g, lt_min zero_lt_one hg, ?_⟩
    intro z hz
    by_cases hrate : I z ≤ (1 : EReal)
    · have hcg : ((min 1 g : ℝ) : EReal) ≤ (g : EReal) := by
        exact_mod_cast min_le_right (1 : ℝ) g
      exact hcg.trans (hglt.le.trans (hmin ⟨hrate, hz⟩))
    · have hc1 : ((min 1 g : ℝ) : EReal) ≤ (1 : EReal) := by
        exact_mod_cast min_le_left (1 : ℝ) g
      exact hc1.trans (lt_of_not_ge hrate).le
  · refine ⟨1, zero_lt_one, ?_⟩
    intro z hz
    have hrate : ¬ I z ≤ (1 : EReal) := fun h => hnonempty ⟨z, h, hz⟩
    exact (lt_of_not_ge hrate).le

theorem bounded_parabola_low_rate_localization
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (r : ℝ) (hr : 0 < r) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ z : ℝ × ℝ,
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z ≤
        (delta : EReal) →
      dist z (∫ x : ℝ, x ∂mu, ∫ x : ℝ, x ^ 2 ∂mu) < r := by
  obtain ⟨gap, hgap, hbound⟩ := bounded_parabola_legendre_gap_away_mean mu M hM hb r hr
  refine ⟨gap / 2, half_pos hgap, ?_⟩
  intro z hz
  by_contra hnot
  have hlower := hbound z (le_of_not_gt hnot)
  have hhalf : ((gap / 2 : ℝ) : EReal) < (gap : EReal) := by
    exact_mod_cast half_lt_self hgap
  exact hhalf.not_ge (hlower.trans hz)

end
end Shao.OQ3
