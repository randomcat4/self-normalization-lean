# Actual source conditional-law kernel: short-time weighted sums

Status: CANDIDATE_PENDING_ROOT_FREEZE. No production source, proof implementation
or Lean command has started for this module.

Proposed module: `Shao/Probability/SourceShortTimeKernelBounds.lean`.
One public theorem, no new public definitions. The theorem is the actual
realkernel(iii) target, expressed by arbitrary index-dependent choices of q/w
instead of a totalized supremum over an unbounded set.

```lean
import Shao.Probability.SourceOddEvenMarkedIBP
import Shao.Probability.QuadraticFullNoiseMarkedLowRegions
import Shao.Probability.QuadraticFullNoiseMarkedOutside
import Shao.Probability.QuadraticFullNoiseMarkedRegionFour
import Shao.Probability.SourceShortTimeGrid

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

theorem sourceTruncation_futureNoise_short_kernel_sums :
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
              let T : ℕ → ℝ := fun i => ((n - i : ℕ) : ℝ) * m2
              let J : Finset ℕ := (Finset.range (n + 1)).filter
                (fun i => n / 2 < i ∧ L2 * gamma ^ 2 ≤ T i ∧
                  T i < max (L2 * gamma ^ 2) (y ^ 2))
              let f : ℕ → ℝ → ℝ → ℝ := fun i q w =>
                sourceFutureNoiseKernel ρ (n - i) y (w, q)
              let o : ℕ → ℝ → ℝ → ℝ := fun i q w =>
                (f i q w - f i q (-w)) / 2
              let e : ℕ → ℝ → ℝ → ℝ := fun i q w =>
                (f i q w + f i q (-w)) / 2
              (∀ i ∈ J, ∀ w q : ℝ, |w| ≤ y / 16 →
                DifferentiableAt ℝ (o i q) w ∧
                  DifferentiableAt ℝ (e i q) w ∧
                  DifferentiableAt ℝ (fun r : ℝ => deriv (e i q) r) w) ∧
              (∀ q w : ℕ → ℝ, (∀ i ∈ J, |w i| ≤ y / 16) →
                m2 * (∑ i ∈ J, |deriv (o i (q i)) (w i)|) ≤
                    C * ((n : ℝ) * |mu| + (n : ℝ) * m3) ∧
                  m2 * (∑ i ∈ J,
                    |deriv (fun r : ℝ => deriv (e i (q i)) r) (w i)|) ≤ C)

end Shao.Probability
```

The arbitrary q/w functions allow a different spatial point at each selected
index, so the conclusion retains the finite sum-of-uniform-bounds strength of
the source sum of suprema. It is stronger than using one common q,w for the
whole sum. The origin and m=0 endpoints are retained in the definitions;
actual positive-clock membership excludes m=0 without an extra premise.
