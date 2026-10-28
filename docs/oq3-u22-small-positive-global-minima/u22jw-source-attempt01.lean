import Shao.OQ3.BoundedParabolaRectangleSeparation
import Shao.OQ3.ParabolaCellRateAnchor

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem bounded_parabola_legendre_compact_sublevels
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (lower upper : ℝ)
    (henergy : ∀ᵐ x ∂mu, lower ≤ x ^ 2 ∧ x ^ 2 ≤ upper) :
    (∀ z : ℝ × ℝ, (z.1 < -M ∨ M < z.1 ∨ z.2 < lower ∨ upper < z.2) →
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z = ⊤) ∧
      ∀ L : ℝ, IsCompact {z : ℝ × ℝ |
        Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z ≤
          (L : EReal)} := by
  let I : (ℝ × ℝ) → EReal :=
    Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
  have hout (z : ℝ × ℝ)
      (hz : z.1 < -M ∨ M < z.1 ∨ z.2 < lower ∨ upper < z.2) : I z = ⊤ := by
    apply (EReal.eq_top_iff_forall_lt (I z)).2
    intro L
    obtain ⟨theta, htheta⟩ :=
      (bounded_parabola_rectangle_exponential_separation mu M hM hb lower upper henergy).2 z hz L
    exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr htheta)
      (Shao.Probability.bivariateLegendreRate_test_le mu (fun x : ℝ => (x, x ^ 2)) z theta)
  refine ⟨hout, ?_⟩
  intro L
  have hclosed : IsClosed {z : ℝ × ℝ | I z ≤ (L : EReal)} :=
    (bivariate_legendre_rate_lower_semicontinuous mu (fun x : ℝ => (x, x ^ 2))).isClosed_preimage
      (L : EReal)
  have hsubset : {z : ℝ × ℝ | I z ≤ (L : EReal)} ⊆
      Set.Icc (-M) M ×ˢ Set.Icc lower upper := by
    intro z hz
    have hnotOutside
        (hbad : z.1 < -M ∨ M < z.1 ∨ z.2 < lower ∨ upper < z.2) : False := by
      rw [hout z hbad] at hz
      exact (EReal.coe_lt_top L).not_ge hz
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · by_contra h
      exact hnotOutside (Or.inl (lt_of_not_ge h))
    · by_contra h
      exact hnotOutside (Or.inr (Or.inl (lt_of_not_ge h)))
    · by_contra h
      exact hnotOutside (Or.inr (Or.inr (Or.inl (lt_of_not_ge h))))
    · by_contra h
      exact hnotOutside (Or.inr (Or.inr (Or.inr (lt_of_not_ge h))))
  exact (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hclosed hsubset

end
end Shao.OQ3
