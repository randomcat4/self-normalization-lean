import Shao.OQ6.UniformPMomentActualGoodsetFrontier
import Shao.OQ5.P51.LiteralClippedComparison
import Shao.OQ6.OriginalPhysicalClippedTailTransfer

set_option autoImplicit false
universe u
open Filter MeasureTheory
open scoped BigOperators Classical ENNReal
open Shao.OQ5.P51
open Shao.OQ6.BoundedProductEnvelopeTails (tailScale)
open Shao.OQ6.CanonicalDoubleGhostRowMoments (sampleLaw originalRows)
open Shao.OQ6.CanonicalDoubleGhostScalarMoments (originalUpper)
namespace Shao.OQ6.UniformPMomentGoodsetPhysicalPayment
noncomputable section

theorem uniform_pmoment_original_current_level_goodset_physical_payment
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (B : ℝ) (hB : 1 ≤ B) :
    let tB : ℝ := Real.rpow (1 / (4 * B)) (2 / (p - 2))
    let cg : ℝ := tB / 4
    0 < cg ∧
      ∀ (C a t0 M : ℝ)
        (hC : 0 ≤ C) (ha : 0 ≤ a) (ht0 : 0 < t0) (hM : 0 ≤ M),
        ∃ N : ℕ, 4 ≤ N ∧
          ∀ (n : ℕ), N ≤ n →
            ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω]
              (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
              (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
              (hgmean : (∫ o : Ω, g o ∂μ) = 0)
              (hgsecond : (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1)
              (hgp : Integrable (fun o : Ω => Real.rpow |g o| p) μ)
              (hβBound : (∫ o : Ω, Real.rpow |g o| p ∂μ) ≤ B)
              (r : Ω → Ω → ℝ) (w : Ω → ℝ)
              (hr : Measurable (Function.uncurry r))
              (hr1 : Integrable (Function.uncurry r) (μ.prod μ))
              (hcR : ∀ᵐ o : Ω ∂μ, (∫ o' : Ω, r o o' ∂μ) = 0)
              (hcL : ∀ᵐ o' : Ω ∂μ, (∫ o : Ω, r o o' ∂μ) = 0)
              (hW : ∀ᵐ o : Ω ∂μ, 0 ≤ w o)
              (hWR : ∀ᵐ o : Ω ∂μ, w o ≤ boundedPolylogHeight C a n)
              (hSq : Integrable (fun o : Ω => (w o) ^ (2 : ℕ)) μ)
              (hSqBound : (∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ≤ M)
              (hEnv : ∀ᵐ o : Ω × Ω ∂μ.prod μ,
                |r o.1 o.2| ≤ w o.1 * w o.2)
              (hsym : ∀ o o' : Ω, r o o' = r o' o)
              (rho z : ℝ) (hrho : 0 ≤ rho) (hz : (1 : ℝ) ≤ z)
              (hzWindow : z ≤ remainderWindowScale (tailScale M) t0 *
                Real.rpow (n : ℝ) (1 / 6 : ℝ))
              (hGeometry : (1 + rho) * z ≤ Real.sqrt (n : ℝ)),
              let q : ℝ := boundedPolylogMomentOrder t0 n
              let K : ℝ := tailScale M
              let P : Measure (Fin n → Ω) := sampleLaw n μ
              let G : Set (Fin n → Ω) := projectionGood n g z
              let C2 : Set (Fin n → Ω) :=
                {x : Fin n → Ω |
                  |originalUpper n r x| ≤ K * (n : ℝ) * q ∧
                  ‖originalRows n r x‖ ^ (2 : ℕ) ≤
                    K * (n : ℝ) ^ (2 : ℕ) * q}
              let Hsource : Set (Fin n → Ω) := G ∩ C2
              let V0 : (Fin n → Ω) → ℝ := projectionV n g
              let D1 : (Fin n → Ω) → ℝ := residualStatisticD n r
              let D2z : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho z
              let Ssafe : Set (Fin n → Ω) := {x : Fin n → Ω |
                0 < V0 x ∧ z * |D1 x| ≤ V0 x / 8 ∧
                  z ^ 2 * |D2z x| ≤ (1 / 8 : ℝ)}
              let physical : (Fin n → Ω) → ℝ := fun x : Fin n → Ω =>
                if Real.sqrt (centeredSq n g r x) = 0 then 0 else
                  (projectionW n g x + residualStatisticD n r x) /
                    Real.sqrt (centeredSq n g r x)
              let clipped : (Fin n → Ω) → ℝ :=
                clippedCenteredStatistic n g r 512 rho z
              let Eclip : Set (Fin n → Ω) := {x : Fin n → Ω | clipped x ≠ physical x}
              let E2 : Set (Fin n → Ω) :=
                {x : Fin n → Ω | z ^ 2 * |D2z x| > (1 / 4 : ℝ)}
              let Z0 : Set (Fin n → Ω) := {x : Fin n → Ω | V0 x = 0}
              let Zphysical : Set (Fin n → Ω) :=
                {x : Fin n → Ω | Real.sqrt (centeredSq n g r x) = 0}
              let payment : ℝ :=
                (3 : ℝ) * Real.exp (-q) + Real.exp (-cg * (n : ℝ)) +
                  (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ))
              MeasurableSet Hsource ∧
              Measurable physical ∧ Measurable clipped ∧ MeasurableSet Eclip ∧
              Hsource ⊆ Ssafe ∧
              (∀ x : Fin n → Ω, x ∈ Hsource →
                0 < V0 x ∧
                z * |D1 x| ≤ V0 x / 8 ∧
                z ^ 2 * |D2z x| ≤ (1 / 32 : ℝ) ∧
                0 < Real.sqrt (centeredSq n g r x) ∧
                Real.sqrt (centeredSq n g r x) =
                  V0 x * Real.sqrt (1 + centeredDelta n g r x) ∧
                D2z x = centeredDelta n g r x ∧
                clipped x = physical x) ∧
              (Ssafeᶜ ∪ Eclip ∪ Zphysical) ⊆ Hsourceᶜ ∧
              (E2 ∪ Z0) ⊆ Ssafeᶜ ∧
              P.real Hsourceᶜ ≤ payment ∧
              P.real Ssafeᶜ ≤ payment ∧
              P.real (E2 ∪ Z0 ∪ Eclip ∪ Zphysical) ≤ payment ∧
              P.real Eclip ≤ payment
:= by
  classical
  intro tB cg
  rcases
    Shao.OQ6.UniformPMomentActualGoodsetFrontier.uniform_pmoment_original_boundedPolylog_goodset_frontier.{u}
      p hp2 hp3 B hB with ⟨hcg, hFrontier⟩
  refine ⟨hcg, ?_⟩
  intro C a t0 M hC ha ht0 hM
  obtain ⟨N, hN4, hAll⟩ := hFrontier C a t0 M hC ha ht0 hM
  refine ⟨N, hN4, ?_⟩
  intro n hn Ω mΩ μ hμ g hg hg2 hgmean hgsecond hgp hβBound
    r w hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hsym
    rho z hrho hz hzWindow hGeometry
  intro q K P G C2 Hsource V0 D1 D2z Ssafe physical clipped Eclip E2 Z0
    Zphysical payment
  letI instP : IsProbabilityMeasure P :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ)))
  have hn4 : 4 ≤ n := hN4.trans hn
  have h512 : (0 : ℝ) ≤ 512 := by norm_num
  have hz0 : (0 : ℝ) ≤ z := le_trans (by norm_num : (0 : ℝ) ≤ 1) hz
  rcases hAll n hn μ g hg hg2 hgmean hgsecond hgp hβBound
    r w hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hsym
    512 rho z h512 hrho hz hzWindow with
    ⟨hHMeas, hCommonOn, _hCommonZero, hHfee⟩
  have hmeas :=
    Shao.OQ6.OriginalPhysicalClippedTailTransfer.physical_clipped_globally_measurable
      n g r hg hr 512 rho z
  have hPhysicalMeas : Measurable physical := hmeas.1
  have hClippedMeas : Measurable clipped := hmeas.2.1
  have hEclipMeas : MeasurableSet Eclip := hmeas.2.2
  have hOn (x : Fin n → Ω) (hx : x ∈ Hsource) :
      0 < V0 x ∧
      z * |D1 x| ≤ V0 x / 8 ∧
      z ^ 2 * |D2z x| ≤ (1 / 32 : ℝ) ∧
      0 < Real.sqrt (centeredSq n g r x) ∧
      Real.sqrt (centeredSq n g r x) =
        V0 x * Real.sqrt (1 + centeredDelta n g r x) ∧
      D2z x = centeredDelta n g r x ∧
      clipped x = physical x := by
    rcases hCommonOn x hx with
      ⟨hVpos, _hEnergy, hNum, _hNumStrict, hRawScaled, _hRawAbs, hRawLower,
        _hOldContract, _hOldScaled, _hOldStrict, _hOldAbs, _hOldClipPos,
        _hSourcePos, hFactor⟩
    have hCurrentClip := clippedCenteredDelta_bounds n g r 512 rho z x
      h512 hrho hz0
    have hContract : |D2z x| ≤ |centeredDelta n g r x| :=
      hCurrentClip.2.2.1
    have hScaled : z ^ 2 * |D2z x| ≤ (1 / 32 : ℝ) :=
      (mul_le_mul_of_nonneg_left hContract (sq_nonneg z)).trans hRawScaled
    have hLower : -(1 / 2 : ℝ) ≤ centeredDelta n g r x := by
      linarith only [hRawLower]
    have hLiteral := literal_clippedCentered_comparison_on_projectionGood
      n g r rho z x hn4 hz hsym hrho hGeometry hx.1 hLower
    exact ⟨hVpos, hNum, hScaled, hLiteral.2.2.1, hFactor,
      hLiteral.1, hLiteral.2.2.2.2⟩
  have hSafeSubset : Hsource ⊆ Ssafe := by
    intro x hx
    have hxOn := hOn x hx
    refine ⟨hxOn.1, hxOn.2.1, ?_⟩
    linarith only [hxOn.2.2.1]
  have hUnionSubset : (Ssafeᶜ ∪ Eclip ∪ Zphysical) ⊆ Hsourceᶜ := by
    intro x hx hxH
    have hxOn := hOn x hxH
    rcases hx with (hxSafe | hxClip) | hxPhysical
    · exact hxSafe (hSafeSubset hxH)
    · exact hxClip hxOn.2.2.2.2.2.2
    · exact (ne_of_gt hxOn.2.2.2.1) hxPhysical
  have hRemainderSubset : (E2 ∪ Z0) ⊆ Ssafeᶜ := by
    intro x hx hxSafe
    rcases hx with hxE2 | hxZ0
    · change (1 / 4 : ℝ) < z ^ 2 * |D2z x| at hxE2
      linarith only [hxSafe.2.2, hxE2]
    · exact (ne_of_gt hxSafe.1) hxZ0
  have hSafeComplSubset : Ssafeᶜ ⊆ Hsourceᶜ := by
    intro x hx hxH
    exact hx (hSafeSubset hxH)
  have hAllSubset : (E2 ∪ Z0 ∪ Eclip ∪ Zphysical) ⊆ Hsourceᶜ := by
    intro x hx
    rcases hx with ((hxE2 | hxZ0) | hxClip) | hxPhysical
    · exact hSafeComplSubset (hRemainderSubset (Or.inl hxE2))
    · exact hSafeComplSubset (hRemainderSubset (Or.inr hxZ0))
    · exact hUnionSubset (Or.inl (Or.inr hxClip))
    · exact hUnionSubset (Or.inr hxPhysical)
  have hEclipSubset : Eclip ⊆ Hsourceᶜ := by
    intro x hx
    exact hUnionSubset (Or.inl (Or.inr hx))
  have hSafeFee : P.real Ssafeᶜ ≤ payment :=
    (measureReal_mono (μ := P) hSafeComplSubset
      (measure_ne_top P Hsourceᶜ)).trans hHfee
  have hAllFee : P.real (E2 ∪ Z0 ∪ Eclip ∪ Zphysical) ≤ payment :=
    (measureReal_mono (μ := P) hAllSubset
      (measure_ne_top P Hsourceᶜ)).trans hHfee
  have hEclipFee : P.real Eclip ≤ payment :=
    (measureReal_mono (μ := P) hEclipSubset
      (measure_ne_top P Hsourceᶜ)).trans hHfee
  exact ⟨hHMeas, hPhysicalMeas, hClippedMeas, hEclipMeas, hSafeSubset,
    hOn, hUnionSubset, hRemainderSubset, hHfee, hSafeFee, hAllFee, hEclipFee⟩
end
end Shao.OQ6.UniformPMomentGoodsetPhysicalPayment
