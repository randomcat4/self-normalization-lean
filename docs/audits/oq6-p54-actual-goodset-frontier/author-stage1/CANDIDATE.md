# Unit233 Stage1: fixed-original-law actual goodset frontier candidate

Status: DECLARATION_SOURCE_API_DESIGN_ONLY. This is one complete proposed declaration head, with no proof body and no declaration freeze. Parent approval/freeze, proof implementation, independent complete review, server kernel and whole-owned transitive-axiom checks remain later stages. The actual ACK predates this file.

The mathematical object is the actual p54 F4/F5 goodset for the bounded-polylog product-envelope branch of p51 S16–S17. Fix the original probability law μ and its actual measurable projection g, with mean zero and second moment one. Choose cg from the qualified original-good-event probability theorem **before** all concentration constants, eventual sample sizes, residual/envelope choices and target levels. For sufficiently large n, the residual r and envelope w may vary with n, but the original μ and g do not vary. No assertion about a family of conditional laws μn/gn or a simultaneous uniform cg is made.

The event is specified by its exact ordinary-data expression. Let q = t0 n^(1/3), K = tailScale M, G = projectionGood n g z, and let C2 require the actual original upper sum and the actual original row norm squared to meet their concentration thresholds. Set H = G ∩ C2. C2 contains no squareSum(w) test: that observable is unused by the deterministic small-window geometry. The full qualified boundedProductFailure remains a probability payer through C2ᶜ ⊆ boundedProductFailure. H is measurable using only globally measurable g and uncurry r, with **no** global measurability assumption on w.

The retained clip parameter is the literal last parameter `1` in `clippedCenteredDelta n g r C0 rho 1`. It is distinct from the target z. The head gives absolute contraction, smallness and positivity; it does not assert equality to the actual centeredDelta or equality of physical and clipped statistics. In particular, arbitrary nonnegative C0/rho are sufficient for contraction, but do not supply a budget domination theorem.

Proposed context and single theorem head (the final colon introduces the result; the excerpt deliberately ends without a proof assignment):

```lean
import Shao.OQ5.P51.ClippedStudentizer
import Shao.OQ6.OriginalGoodEventBridge
import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false
universe u
open Filter MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ5.P51
open Shao.OQ6.BoundedProductEnvelopeTails (tailScale)
open Shao.OQ6.CanonicalDoubleGhostRowMoments (sampleLaw originalRows)
open Shao.OQ6.CanonicalDoubleGhostScalarMoments (originalUpper)

namespace Shao.OQ6.P54

theorem fixed_original_boundedPolylog_goodset_frontier
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o : Ω, g o ∂μ) = 0)
    (hgsecond : (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1) :
    ∃ cg : ℝ, 0 < cg ∧
      ∀ (C a t0 M : ℝ)
        (hC : 0 ≤ C) (ha : 0 ≤ a) (ht0 : 0 < t0) (hM : 0 ≤ M),
        ∀ᶠ n : ℕ in atTop,
          4 ≤ n ∧
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
            (C0 rho z : ℝ) (hC0 : 0 ≤ C0) (hrho : 0 ≤ rho)
            (hz : (1 : ℝ) ≤ z)
            (hzWindow : z ≤ remainderWindowScale (tailScale M) t0 *
              Real.rpow (n : ℝ) (1 / 6 : ℝ)),
            let q : ℝ := boundedPolylogMomentOrder t0 n
            let K : ℝ := tailScale M
            let G : Set (Fin n → Ω) := projectionGood n g z
            let C2 : Set (Fin n → Ω) :=
              {x : Fin n → Ω |
                |originalUpper n r x| ≤ K * (n : ℝ) * q ∧
                ‖originalRows n r x‖ ^ (2 : ℕ) ≤
                  K * (n : ℝ) ^ (2 : ℕ) * q}
            let H : Set (Fin n → Ω) := G ∩ C2
            let e1 : (Fin n → Ω) → ℝ :=
              fun x : Fin n → Ω => clippedCenteredDelta n g r C0 rho 1 x
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
                  projectionV n g x *
                    Real.sqrt (1 + centeredDelta n g r x)) ∧
              (({x : Fin n → Ω | projectionV n g x = 0} ∪
                  {x : Fin n → Ω | Real.sqrt (centeredSq n g r x) = 0}) ⊆ Hᶜ) ∧
              (sampleLaw n μ).real Hᶜ ≤
                (3 : ℝ) * Real.exp (-q) + Real.exp (-cg * (n : ℝ)) +
                  (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ))

end Shao.OQ6.P54
```

There is no existential H supplied by the caller, nor any premise asserting H's measurability, goodness or payment. Its let RHS fixes the actual event. The theorem's only existential witness is cg; its source is the qualified original-good-event theorem for the fixed μ/g. The eventual threshold can be taken from the qualified concentration threshold and n ≥ 4, independently of r, w, C0, rho and z. The head places cg even before C/a/t0/M, making its fixed-law dependence explicit.

All real divisions and square roots are Lean's total functions. No positivity is hidden in ordinary-data definitions. The eventual n ≥ 4, G-energy condition and returned V positivity provide the relevant positive denominators at their uses. At V = 0 the existing definitions explicitly set centeredDelta and the retained clipped delta to zero; the candidate makes no ratio claim there. The zero-V and true zero-studentizer events are included in Hᶜ, rather than discarded by an almost-everywhere reinterpretation.

The constants 1/8 and 1/32 supply strict slack relative to the source upper thresholds 1/4 and lower cutoff −1/2. The source F4 projection lower bound V ≥ 1/√2 follows from energy ≥ 1/2 and V = sqrt(energy); the head retains energy ≥ 1/2 and V > 0 directly. The returned d bound is stronger than the F4 lower and scaled-d margins. The candidate returns the literal three-term F5 payment, with coefficient 3 on exp(−q), on the original product law.

Unclaimed scope: no clip1 = d identity; no physical/clipped T identity; no full-model/m0/canonical-eta binding; no original/trim/augmented same-witness transfer; no epsilon coding limit; no source Shao–Zhou theorem application; no CDF, relative-tail or original OQ6 root closure; no conditional-law uniform cg; no new p-moment variation rate; no DC S18 extension. This is a design-ready candidate, not a mathematical or machine acceptance certificate.
