import Shao.OQ5.P51.LiteralClippedComparison
import Shao.OQ6.OriginalGoodEventBridge
import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false
universe u
open Filter MeasureTheory
open scoped BigOperators Classical ENNReal
open Shao.OQ5.P51
open Shao.OQ6.BoundedProductEnvelopeTails (tailScale)
open Shao.OQ6.CanonicalDoubleGhostRowMoments (sampleLaw)
namespace Shao.OQ6.OriginalRetainedClipComparisonPayment
noncomputable section

theorem fixed_original_retained_clip_comparison_payment
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o : Ω, g o ∂μ) = 0)
    (hgsecond : (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1) :
    ∃ cg : ℝ, 0 < cg ∧
      ∀ (C a t0 M : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a)
        (ht0 : 0 < t0) (hM : 0 ≤ M),
        ∀ᶠ n : ℕ in atTop,
          4 ≤ n ∧
          ∀ (r : Ω → Ω → ℝ) (w : Ω → ℝ)
            (hr : Measurable (Function.uncurry r))
            (hr1 : Integrable (Function.uncurry r) (μ.prod μ))
            (hcR : ∀ᵐ o : Ω ∂μ, (∫ y : Ω, r o y ∂μ) = 0)
            (hcL : ∀ᵐ y : Ω ∂μ, (∫ o : Ω, r o y ∂μ) = 0)
            (hW : ∀ᵐ o : Ω ∂μ, 0 ≤ w o)
            (hWR : ∀ᵐ o : Ω ∂μ, w o ≤ boundedPolylogHeight C a n)
            (hSq : Integrable (fun o : Ω => (w o) ^ (2 : ℕ)) μ)
            (hSqBound : (∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ≤ M)
            (hEnv : ∀ᵐ p : Ω × Ω ∂μ.prod μ,
              |r p.1 p.2| ≤ w p.1 * w p.2)
            (hsym : ∀ o y : Ω, r o y = r y o)
            (rho : ℝ) (hrho : 0 ≤ rho)
            (hStudentizerWindow : 1 + rho ≤ Real.sqrt (n : ℝ))
            (hSmallWindow : (1 : ℝ) ≤ remainderWindowScale (tailScale M) t0 *
              Real.rpow (n : ℝ) (1 / 6 : ℝ)),
            let q : ℝ := boundedPolylogMomentOrder t0 n
            let physical : (Fin n → Ω) → ℝ := fun x =>
              if Real.sqrt (centeredSq n g r x) = 0 then 0 else
                (projectionW n g x + residualStatisticD n r x) /
                  Real.sqrt (centeredSq n g r x)
            let clipped : (Fin n → Ω) → ℝ :=
              clippedCenteredStatistic n g r 512 rho 1
            let Eclip : Set (Fin n → Ω) := {x | clipped x ≠ physical x}
            Eclip ⊆ (projectionGood n g 1)ᶜ ∪ lowerStudentizerBad n g r 1 ∧
              (sampleLaw n μ).real Eclip ≤
                (3 : ℝ) * Real.exp (-q) + Real.exp (-cg * (n : ℝ)) +
                  (4 : ℝ) * Real.exp (-(Real.sqrt (n : ℝ)) / (2 : ℝ)) := by
  classical
  rcases Shao.OQ6.OriginalGoodEventProbability.original_good_event_complement_bound
    μ g hg hg2 hgmean hgsecond with ⟨cg, hcg, hGoodAll⟩
  refine ⟨cg, hcg, ?_⟩
  intro C a t0 M hC ha ht0 hM
  filter_upwards [eventually_ge_atTop (4 : ℕ),
    eventually_boundedPolylog_remainder_payments C a t0 M hC ha ht0 hM]
    with n hn hPay
  refine ⟨hn, ?_⟩
  intro r w hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hsym
    rho hrho hStudentizerWindow hSmallWindow
  let q : ℝ := boundedPolylogMomentOrder t0 n
  let physical : (Fin n → Ω) → ℝ := fun x =>
    if Real.sqrt (centeredSq n g r x) = 0 then 0 else
      (projectionW n g x + residualStatisticD n r x) /
        Real.sqrt (centeredSq n g r x)
  let clipped : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho 1
  let Eclip : Set (Fin n → Ω) := {x | clipped x ≠ physical x}
  let Pn : Measure (Fin n → Ω) := sampleLaw n μ
  let G : Set (Fin n → Ω) := projectionGood n g 1
  let A : Set (Fin n → Ω) := lowerStudentizerBad n g r 1
  letI instPn : IsProbabilityMeasure Pn :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ)))
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 4) hn
  have hWindow : (1 + rho) * (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    simpa only [mul_one] using hStudentizerWindow
  have hSubset : Eclip ⊆ Gᶜ ∪ A := by
    exact literal_clippedCentered_comparison_exception_subset n g r rho 1
      hn (le_refl (1 : ℝ)) hsym hrho hWindow
  have hLow : Pn.real A ≤ (3 : ℝ) * Real.exp (-q) :=
    (hPay μ g r w hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hsym
      1 (le_refl (1 : ℝ)) hSmallWindow).1
  have hG : Pn.real Gᶜ ≤ Real.exp (-cg * (n : ℝ)) +
      (4 : ℝ) * Real.exp (-(Real.sqrt (n : ℝ)) / (2 : ℝ)) := by
    have hOriginal := hGoodAll n hnpos 1 (le_refl (1 : ℝ))
    rw [Shao.OQ6.OriginalGoodEventBridge.normalizedGoodEvent_eq_projectionGood
      n g 1] at hOriginal
    simpa only [one_mul] using hOriginal
  change Eclip ⊆ Gᶜ ∪ A ∧ Pn.real Eclip ≤
    (3 : ℝ) * Real.exp (-q) + Real.exp (-cg * (n : ℝ)) +
      (4 : ℝ) * Real.exp (-(Real.sqrt (n : ℝ)) / (2 : ℝ))
  refine ⟨hSubset, ?_⟩
  calc
    Pn.real Eclip ≤ Pn.real (Gᶜ ∪ A) := measureReal_mono (μ := Pn) hSubset
    _ ≤ Pn.real Gᶜ + Pn.real A := measureReal_union_le (μ := Pn) Gᶜ A
    _ ≤ (Real.exp (-cg * (n : ℝ)) +
        (4 : ℝ) * Real.exp (-(Real.sqrt (n : ℝ)) / (2 : ℝ))) +
          (3 : ℝ) * Real.exp (-q) := add_le_add hG hLow
    _ = (3 : ℝ) * Real.exp (-q) + Real.exp (-cg * (n : ℝ)) +
        (4 : ℝ) * Real.exp (-(Real.sqrt (n : ℝ)) / (2 : ℝ)) := by ring


end
end Shao.OQ6.OriginalRetainedClipComparisonPayment
