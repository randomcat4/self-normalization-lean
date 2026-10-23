# Frozen actual threshold/Fourier parameter payment

Root completely read the literal candidate, full contract, and original main LF373-379/638-642 plus supplement LF2370-2384/2471-2476/2501-2505/2517-2520. Exactly one public theorem is approved. Full candidate SHA2568da1c0ef097f0a69409634ebc2d4ffbb96c106ff4875b1b8d9f24d7e7e48322f; complete contract SHA2568c5ccfbe26e40c07abceb85a9b293971e0f60d6a6ab70a05d45e107a5ced953e.

The genuine threshold window pays h_x<=h=epsilon0/(1+y); actual source support and gamma bounds must be derived for the same conditional law. Positive kappa/delta precede epsilon0; epsilon0 precedes all law and scale parameters. The uniform smallness guards and exact cone inclusion are outputs, not hypotheses. This is an adapter for the actual growing-y/source-threshold chain, independent of the currently authored five-region kernel module. No probability, root or novelty conclusion is certified by it. The complete literal declaration follows unchanged.

# Actual threshold-to-Fourier parameter payment

State: PROPOSED_ONLY_AWAITING_ROOT_FREEZE_ACTIVATION. No new production source.
Proposed module: Shao.Probability.SourceFourierParameterPayment.

```lean
import Shao.Probability.SourceFourierScale
set_option autoImplicit false
namespace Shao.Probability
open MeasureTheory ProbabilityTheory

theorem sourceTruncation_threshold_fourier_parameter_payment
    (kappa delta : ℝ) (hkappa : 0 < kappa) (hdelta : 0 < delta) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 4 : ℝ) ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
          (∫ z : ℝ, z ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ epsilon0 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ y : ℝ, 0 < y → |y - x| ≤ 1 / (2 * (1 + x)) →
              let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
              let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
              let h : ℝ := epsilon0 / (1 + y)
              0 < h ∧ h ≤ (1 / 4 : ℝ) ∧ epsilon / (1 + x) ≤ h ∧
                (∀ᵐ z : ℝ ∂ρ, |z| ≤ h) ∧
                0 < gamma ∧ gamma ≤ 2 * h ∧
                h * y ≤ delta ∧ (gamma / kappa) * y ≤ delta ∧ (4 * h) * y ≤ delta ∧
                ∀ u v : ℝ, u ≠ 0 → |v| ≤ |u| / (4 * h) →
                  |v| ≤ |u| / (4 * (epsilon / (1 + x)))

end Shao.Probability
```
