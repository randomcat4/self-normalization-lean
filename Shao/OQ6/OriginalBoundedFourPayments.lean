import Shao.OQ6.OriginalGoodEventBridge
import Shao.OQ5.P51.BoundedRemainderPayments
set_option autoImplicit false
open Filter MeasureTheory
namespace Shao.OQ6.OriginalBoundedFourPayments

theorem eventually_original_boundedPolylog_four_payments
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o : Ω, g o ∂μ) = 0)
    (hgsecond : (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1)
    (C a t0 M : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (ht0 : 0 < t0) (hM0 : 0 ≤ M) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (r : Ω → Ω → ℝ) (w : Ω → ℝ),
      Measurable (Function.uncurry r) →
      Integrable (Function.uncurry r) (μ.prod μ) →
      (∀ᵐ a ∂μ, (∫ b : Ω, r a b ∂μ) = 0) →
      (∀ᵐ b ∂μ, (∫ a : Ω, r a b ∂μ) = 0) →
      (∀ᵐ o ∂μ, 0 ≤ w o) →
      (∀ᵐ o ∂μ, w o ≤ Shao.OQ5.P51.boundedPolylogHeight C a n) →
      Integrable (fun o : Ω => (w o) ^ (2 : ℕ)) μ →
      (∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ≤ M →
      (∀ᵐ z ∂μ.prod μ, |r z.1 z.2| ≤ w z.1 * w z.2) →
      (∀ a b : Ω, r a b = r b a) →
      ∀ y : ℝ, (1 : ℝ) ≤ y →
      y ≤ Shao.OQ5.P51.remainderWindowScale
        (Shao.OQ6.BoundedProductEnvelopeTails.tailScale M) t0 *
          Real.rpow (n : ℝ) ((1 : ℝ) / 6) →
      (Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ).real
        (Shao.OQ5.P51.projectionGood n g y)ᶜ +
        Shao.OQ5.P51.remainderPayment n
          (Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ) g r y ≤
        Real.exp (-c * (n : ℝ)) +
          (4 : ℝ) * Real.exp (-(y * Real.sqrt (n : ℝ)) / (2 : ℝ)) +
          (9 : ℝ) * Real.exp (-Shao.OQ5.P51.boundedPolylogMomentOrder t0 n) := by
  obtain ⟨c, hc, hBound⟩ :=
    Shao.OQ6.OriginalGoodEventProbability.original_good_event_complement_bound
      μ g hg hg2 hgmean hgsecond
  refine ⟨c, hc, ?_⟩
  filter_upwards [Shao.OQ5.P51.eventually_boundedPolylog_remainder_payments
    C a t0 M hC ha ht0 hM0, Filter.eventually_ge_atTop (4 : ℕ)] with n hnPayment hn4
  intro r w hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hsym y hy hyWindow
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < (4 : ℕ)) hn4
  have hGood :
      (Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ).real
        (Shao.OQ5.P51.projectionGood n g y)ᶜ ≤
          Real.exp (-c * (n : ℝ)) +
            (4 : ℝ) * Real.exp (-(y * Real.sqrt (n : ℝ)) / (2 : ℝ)) := by
    rw [← Shao.OQ6.OriginalGoodEventBridge.normalizedGoodEvent_eq_projectionGood n g y]
    exact hBound n hnpos y hy
  have hPayment :
      Shao.OQ5.P51.remainderPayment n
        (Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ) g r y ≤
          (9 : ℝ) * Real.exp (-Shao.OQ5.P51.boundedPolylogMomentOrder t0 n) :=
    (hnPayment μ g r w hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hsym
      y hy hyWindow).2.2.2.1
  exact add_le_add hGood hPayment

end Shao.OQ6.OriginalBoundedFourPayments
