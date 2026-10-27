import Shao.OQ6.P54ActualGoodsetFrontier
import Shao.OQ6.OriginalRetainedClipComparisonPayment
import Shao.OQ6.OriginalExceptionalTailAbsorption
import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false
universe u
open Filter MeasureTheory
open scoped BigOperators Classical ENNReal
open Shao.OQ5.P51
open Shao.OQ6.BoundedProductEnvelopeTails (tailScale)
open Shao.OQ6.CanonicalDoubleGhostRowMoments (sampleLaw originalRows)
open Shao.OQ6.CanonicalDoubleGhostScalarMoments (originalUpper)

namespace Shao.OQ6.ActualGoodsetPhysicalUnion
noncomputable section

theorem fixed_original_goodset_physical_exceptional_union
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o : Ω, g o ∂μ) = 0)
    (hgsecond : (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1) :
    ∃ cg : ℝ, 0 < cg ∧
      ∀ (C a t0 M : ℝ)
        (hC : 0 ≤ C) (ha : 0 ≤ a) (ht0 : 0 < t0) (hM : 0 ≤ M),
        let cCommon : ℝ :=
          min (remainderWindowScale (tailScale M) t0)
            (min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ)))
        0 < cCommon ∧
          ∀ᶠ n : ℕ in atTop,
            4 ≤ n ∧
              (1 : ℝ) ≤ cCommon * Real.rpow (n : ℝ) (1 / 6 : ℝ) ∧
              ∀ (r : Ω → Ω → ℝ) (w : Ω → ℝ)
                (hr : Measurable (Function.uncurry r))
                (hr1 : Integrable (Function.uncurry r) (μ.prod μ))
                (hcR : ∀ᵐ o : Ω ∂μ, (∫ o' : Ω, r o o' ∂μ) = 0)
                (hcL : ∀ᵐ o' : Ω ∂μ, (∫ o : Ω, r o o' ∂μ) = 0)
                (hW : ∀ᵐ o : Ω ∂μ, 0 ≤ w o)
                (hWR : ∀ᵐ o : Ω ∂μ, w o ≤ boundedPolylogHeight C a n)
                (hSq : Integrable (fun o : Ω => (w o) ^ (2 : ℕ)) μ)
                (hSqBound : (∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ≤ M)
                (hEnv : ∀ᵐ p : Ω × Ω ∂μ.prod μ,
                  |r p.1 p.2| ≤ w p.1 * w p.2)
                (hsym : ∀ o o' : Ω, r o o' = r o' o)
                (rho : ℝ) (hrho : 0 ≤ rho)
                (hStudentizerWindow : 1 + rho ≤ Real.sqrt (n : ℝ))
                (z : ℝ) (hz : (1 : ℝ) ≤ z)
                (hzWindow : z ≤ cCommon * Real.rpow (n : ℝ) (1 / 6 : ℝ)),
                let q : ℝ := boundedPolylogMomentOrder t0 n
                let K : ℝ := tailScale M
                let Gz : Set (Fin n → Ω) := projectionGood n g z
                let C2 : Set (Fin n → Ω) :=
                  {x : Fin n → Ω |
                    |originalUpper n r x| ≤ K * (n : ℝ) * q ∧
                    ‖originalRows n r x‖ ^ (2 : ℕ) ≤
                      K * (n : ℝ) ^ (2 : ℕ) * q}
                let H : Set (Fin n → Ω) := Gz ∩ C2
                let e1 : (Fin n → Ω) → ℝ :=
                  fun x : Fin n → Ω => clippedCenteredDelta n g r 512 rho 1 x
                let physical : (Fin n → Ω) → ℝ := fun x : Fin n → Ω =>
                  if Real.sqrt (centeredSq n g r x) = 0 then 0 else
                    (projectionW n g x + residualStatisticD n r x) /
                      Real.sqrt (centeredSq n g r x)
                let clipped : (Fin n → Ω) → ℝ :=
                  clippedCenteredStatistic n g r 512 rho 1
                let Eclip : Set (Fin n → Ω) := {x : Fin n → Ω | clipped x ≠ physical x}
                let J : Set (Fin n → Ω) := H \ Eclip
                MeasurableSet H ∧
                  (∀ x : Fin n → Ω, x ∈ H →
                    0 < projectionV n g x ∧
                    (1 / 2 : ℝ) ≤ projectionEnergy n g x ∧
                    z * |residualStatisticD n r x| ≤ projectionV n g x / 8 ∧
                    z * |residualStatisticD n r x| < projectionV n g x / 4 ∧
                    z ^ (2 : ℕ) * |centeredDelta n g r x| ≤ (1 / 32 : ℝ) ∧
                    |centeredDelta n g r x| ≤ (1 / 32 : ℝ) ∧
                    -(1 / 8 : ℝ) < centeredDelta n g r x ∧
                    |e1 x| ≤ |centeredDelta n g r x| ∧
                    z ^ (2 : ℕ) * |e1 x| ≤ (1 / 32 : ℝ) ∧
                    z ^ (2 : ℕ) * |e1 x| < (1 / 8 : ℝ) ∧
                    |e1 x| ≤ (1 / 32 : ℝ) ∧
                    0 < projectionV n g x * Real.sqrt (1 + e1 x) ∧
                    0 < Real.sqrt (centeredSq n g r x) ∧
                    Real.sqrt (centeredSq n g r x) =
                      projectionV n g x * Real.sqrt (1 + centeredDelta n g r x)) ∧
                  (∀ x : Fin n → Ω, x ∈ J → clipped x = physical x) ∧
                  (({x : Fin n → Ω | projectionV n g x = 0} ∪
                      {x : Fin n → Ω | Real.sqrt (centeredSq n g r x) = 0}) ⊆ Jᶜ) ∧
                  (Eclip ⊆ (projectionGood n g 1)ᶜ ∪ lowerStudentizerBad n g r 1) ∧
                  Jᶜ = Hᶜ ∪ Eclip ∧
                  (sampleLaw n μ).real Jᶜ ≤
                    (6 : ℝ) * Real.exp (-q) +
                      (2 : ℝ) * Real.exp (-cg * (n : ℝ)) +
                      (8 : ℝ) * Real.exp (-(Real.sqrt (n : ℝ)) / (2 : ℝ)) ∧
                  (sampleLaw n μ).real Jᶜ ≤
                    Real.exp (-(t0 / (2 : ℝ)) *
                      Real.rpow (n : ℝ) (1 / 3 : ℝ)) * Shao.standardNormalTail z := by
  classical
  let cgGood : ℝ :=
    Classical.choose
      (Shao.OQ6.P54.fixed_original_boundedPolylog_goodset_frontier
        μ g hg hg2 hgmean hgsecond)
  have hGood := Classical.choose_spec
    (Shao.OQ6.P54.fixed_original_boundedPolylog_goodset_frontier
      μ g hg hg2 hgmean hgsecond)
  have hCgGoodPos : 0 < cgGood := hGood.1
  let cgClip : ℝ :=
    Classical.choose
      (Shao.OQ6.OriginalRetainedClipComparisonPayment.fixed_original_retained_clip_comparison_payment
        μ g hg hg2 hgmean hgsecond)
  have hClip := Classical.choose_spec
    (Shao.OQ6.OriginalRetainedClipComparisonPayment.fixed_original_retained_clip_comparison_payment
      μ g hg hg2 hgmean hgsecond)
  have hCgClipPos : 0 < cgClip := hClip.1
  let cg : ℝ := min cgGood cgClip
  have hCgPos : 0 < cg := lt_min hCgGoodPos hCgClipPos
  have hCgGoodLe : cg ≤ cgGood := min_le_left _ _
  have hCgClipLe : cg ≤ cgClip := min_le_right _ _
  refine ⟨cg, hCgPos, ?_⟩
  intro C a t0 M hC ha ht0 hM
  let cCommon : ℝ :=
    min (remainderWindowScale (tailScale M) t0)
      (min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ)))
  change 0 < cCommon ∧ _
  have hKPos : 0 < tailScale M :=
    (Shao.OQ6.BoundedProductEnvelopeTails.bounded_scales_pos M hM).2.2.2.2.2
  have hRemPos : 0 < remainderWindowScale (tailScale M) t0 :=
    (remainderWindowScale_bounds (tailScale M) t0 hKPos.le ht0).1
  have hTailPos : 0 < min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ)) :=
    lt_min zero_lt_one (div_pos (Real.sqrt_pos.mpr ht0) (by norm_num))
  have hCommonPos : 0 < cCommon := lt_min hRemPos hTailPos
  have hCommonRem : cCommon ≤ remainderWindowScale (tailScale M) t0 :=
    min_le_left _ _
  have hCommonTail : cCommon ≤ min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ)) :=
    min_le_right _ _
  have hPower : Tendsto
      (fun n : ℕ => Real.rpow (n : ℝ) (1 / 6 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hCommonLarge : ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) ≤ cCommon * Real.rpow (n : ℝ) (1 / 6 : ℝ) := by
    filter_upwards
      [Filter.Tendsto.eventually_ge_atTop hPower ((1 : ℝ) / cCommon)]
      with n hn
    have hm : (1 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 6 : ℝ) * cCommon :=
      (div_le_iff₀ hCommonPos).mp hn
    simpa only [mul_comm] using hm
  have hAbsorb :=
    (Shao.OQ6.OriginalExceptionalTailAbsorption.eventually_original_exceptional_payment_absorbed
      t0 cg ht0 hCgPos).2
  refine ⟨hCommonPos, ?_⟩
  filter_upwards
    [hGood.2 C a t0 M hC ha ht0 hM,
      hClip.2 C a t0 M hC ha ht0 hM, hAbsorb, hCommonLarge]
    with n hGoodN hClipN hAbsorbN hCommonN
  refine ⟨hGoodN.1, hCommonN, ?_⟩
  intro r w hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hsym
    rho hrho hStudentizerWindow z hz hzWindow
  have hnNonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hPowerNonneg : 0 ≤ Real.rpow (n : ℝ) (1 / 6 : ℝ) :=
    Real.rpow_nonneg hnNonneg _
  have hzRemainder :
      z ≤ remainderWindowScale (tailScale M) t0 *
        Real.rpow (n : ℝ) (1 / 6 : ℝ) :=
    hzWindow.trans (mul_le_mul_of_nonneg_right hCommonRem hPowerNonneg)
  have hSmallWindow :
      (1 : ℝ) ≤ remainderWindowScale (tailScale M) t0 *
        Real.rpow (n : ℝ) (1 / 6 : ℝ) :=
    hCommonN.trans (mul_le_mul_of_nonneg_right hCommonRem hPowerNonneg)
  have hzTail :
      z ≤ min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ)) *
        Real.rpow (n : ℝ) (1 / 6 : ℝ) :=
    hzWindow.trans (mul_le_mul_of_nonneg_right hCommonTail hPowerNonneg)
  let q : ℝ := boundedPolylogMomentOrder t0 n
  let K : ℝ := tailScale M
  let Gz : Set (Fin n → Ω) := projectionGood n g z
  let C2 : Set (Fin n → Ω) :=
    {x : Fin n → Ω |
      |originalUpper n r x| ≤ K * (n : ℝ) * q ∧
      ‖originalRows n r x‖ ^ (2 : ℕ) ≤ K * (n : ℝ) ^ (2 : ℕ) * q}
  let H : Set (Fin n → Ω) := Gz ∩ C2
  let e1 : (Fin n → Ω) → ℝ :=
    fun x : Fin n → Ω => clippedCenteredDelta n g r 512 rho 1 x
  let physical : (Fin n → Ω) → ℝ := fun x : Fin n → Ω =>
    if Real.sqrt (centeredSq n g r x) = 0 then 0 else
      (projectionW n g x + residualStatisticD n r x) /
        Real.sqrt (centeredSq n g r x)
  let clipped : (Fin n → Ω) → ℝ :=
    clippedCenteredStatistic n g r 512 rho 1
  let Eclip : Set (Fin n → Ω) := {x : Fin n → Ω | clipped x ≠ physical x}
  let J : Set (Fin n → Ω) := H \ Eclip
  rcases hGoodN.2 r w hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hsym
      (512 : ℝ) rho z (by norm_num) hrho hz hzRemainder with
    ⟨hHMeas, hMargins, hZeroH, hPayH⟩
  rcases hClipN.2 r w hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hsym
      rho hrho hStudentizerWindow hSmallWindow with
    ⟨hEclipSubset, hPayE⟩
  change MeasurableSet H at hHMeas
  change
    (sampleLaw n μ).real Hᶜ ≤
      (3 : ℝ) * Real.exp (-q) + Real.exp (-cgGood * (n : ℝ)) +
        (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ))
    at hPayH
  change
    (sampleLaw n μ).real Eclip ≤
      (3 : ℝ) * Real.exp (-q) + Real.exp (-cgClip * (n : ℝ)) +
        (4 : ℝ) * Real.exp (-(Real.sqrt (n : ℝ)) / (2 : ℝ))
    at hPayE
  have hAgreement : ∀ x : Fin n → Ω, x ∈ J → clipped x = physical x := by
    intro x hx
    by_contra hne
    exact hx.2 hne
  have hZeroJ :
      ({x : Fin n → Ω | projectionV n g x = 0} ∪
        {x : Fin n → Ω | Real.sqrt (centeredSq n g r x) = 0}) ⊆ Jᶜ := by
    intro x hx hxJ
    exact hZeroH hx hxJ.1
  have hComplement : Jᶜ = Hᶜ ∪ Eclip := by
    ext x
    change (¬ (x ∈ H ∧ x ∉ Eclip)) ↔ (x ∉ H ∨ x ∈ Eclip)
    constructor
    · intro hx
      by_cases hxH : x ∈ H
      · right
        by_contra hxE
        exact hx ⟨hxH, hxE⟩
      · exact Or.inl hxH
    · rintro (hxH | hxE) hxJ
      · exact hxH hxJ.1
      · exact hxJ.2 hxE
  have hUnion :
      (sampleLaw n μ).real Jᶜ ≤
        (sampleLaw n μ).real Hᶜ + (sampleLaw n μ).real Eclip := by
    rw [hComplement]
    exact measureReal_union_le Hᶜ Eclip
  have hExpGood :
      Real.exp (-cgGood * (n : ℝ)) ≤ Real.exp (-cg * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right hCgGoodLe hnNonneg]
  have hExpClip :
      Real.exp (-cgClip * (n : ℝ)) ≤ Real.exp (-cg * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right hCgClipLe hnNonneg]
  have hExpLevel :
      Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ)) ≤
        Real.exp (-(Real.sqrt (n : ℝ)) / (2 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right hz (Real.sqrt_nonneg (n : ℝ))]
  have hPayment :
      (sampleLaw n μ).real Jᶜ ≤
        (6 : ℝ) * Real.exp (-q) +
          (2 : ℝ) * Real.exp (-cg * (n : ℝ)) +
          (8 : ℝ) * Real.exp (-(Real.sqrt (n : ℝ)) / (2 : ℝ)) := by
    linarith only [hUnion, hPayH, hPayE, hExpGood, hExpClip, hExpLevel]
  have hAbsorbZ :
      (6 : ℝ) * Real.exp (-q) +
          (2 : ℝ) * Real.exp (-cg * (n : ℝ)) +
          (8 : ℝ) * Real.exp (-(Real.sqrt (n : ℝ)) / (2 : ℝ)) ≤
        Real.exp (-(t0 / (2 : ℝ)) * Real.rpow (n : ℝ) (1 / 3 : ℝ)) *
          Shao.standardNormalTail z :=
    hAbsorbN.2.2 z hz hzTail
  change MeasurableSet H ∧ _
  exact ⟨hHMeas, hMargins, hAgreement, hZeroJ, hEclipSubset, hComplement,
    hPayment, hPayment.trans hAbsorbZ⟩


end
end Shao.OQ6.ActualGoodsetPhysicalUnion
