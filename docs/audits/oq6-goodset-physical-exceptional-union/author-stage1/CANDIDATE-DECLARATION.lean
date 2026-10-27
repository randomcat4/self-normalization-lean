/- Stage1 prospective declaration only. Not frozen, proved, elaborated or accepted.
   Unit236 is an unqualified prospective interface dependency.
   This file intentionally ends at the theorem head, with no proof body. -/
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
                      Real.rpow (n : ℝ) (1 / 3 : ℝ)) * Shao.standardNormalTail z
