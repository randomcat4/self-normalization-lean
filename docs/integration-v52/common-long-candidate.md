# Actual source conditional-law kernel: early and long-time full-space bounds

Status: CANDIDATE_PENDING_ROOT_FREEZE. Proposed module Shao/Probability/SourceLongKernelBounds.lean. One public theorem, no new public definitions. One common tuple of absolute constants serves both source realkernel(i)/(ii) bounds.

```lean
namespace Shao.Probability

open MeasureTheory ProbabilityTheory

theorem sourceTruncation_futureNoise_early_long_kernel_bounds :
    ∃ C epsilon0 L2 : ℝ, 0 < C ∧ 0 < epsilon0 ∧ epsilon0 ≤ 1 / 2 ∧
      (16384 : ℝ) ≤ L2 ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
          (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ epsilon0 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            let ρ : Measure ℝ :=
              ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
            let mu : ℝ := ∫ a : ℝ, a ∂ρ
            let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
            let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
            let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
            ∀ y : ℝ, gamma ≤ y → y ≤ 2 →
              ∀ i : ℕ, 1 ≤ i → i ≤ n →
                let m : ℕ := n - i
                let T : ℝ := (m : ℝ) * m2
                let f : ℝ → ℝ → ℝ := fun q w => sourceFutureNoiseKernel ρ m y (w, q)
                let o : ℝ → ℝ → ℝ := fun q w => (f q w - f q (-w)) / 2
                let e : ℝ → ℝ → ℝ := fun q w => (f q w + f q (-w)) / 2
                (∀ w q : ℝ,
                  DifferentiableAt ℝ (o q) w ∧
                  DifferentiableAt ℝ (e q) w ∧
                  DifferentiableAt ℝ (fun r : ℝ => deriv (e q) r) w) ∧
                (i ≤ n / 2 → ∀ w q : ℝ,
                  |deriv (o q) w| ≤ C * ((n : ℝ) * |mu| + (n : ℝ) * m3) ∧
                  |deriv (fun r : ℝ => deriv (e q) r) w| ≤ C) ∧
                (n / 2 < i → max (L2 * gamma ^ 2) (y ^ 2) ≤ T →
                  ∀ w q : ℝ,
                    |deriv (o q) w| ≤ C * y *
                      ((n : ℝ) * |mu| / Real.sqrt T +
                        (n : ℝ) * m3 / (Real.sqrt T) ^ 3) ∧
                    |deriv (fun r : ℝ => deriv (e q) r) w| ≤
                      C * y / (Real.sqrt T) ^ 3)

end Shao.Probability
```

The last denominators are exactly T^(1/2) and T^(3/2) for the actual positive long-time T. Pointwise bounds for every real w,q express the source's full-space supremum claim. No short-time local w guard occurs. The universal differentiability assertion retains m=0; the late positive-clock branch excludes it by its actual hypotheses, rather than by dropping the endpoint from the quantifiers.
