# Next source consumer: actual local shifts with summable uniform budgets

Status: CANDIDATE_PENDING_ROOT_FREEZE. No implementation, production module or
Lean command has begun for this next unit. Current SourceShortTimeKernelBounds
source/object remain frozen at their author receipt.

Proposed new module: `Shao/Probability/SourceShortTimeKernelTaylor.lean`.
One public theorem, no new public definitions. The uniform budgets are chosen
before every spatial point or regulator size, so the shift bound can be
integrated against the genuine regulator law in the later probability bridge.

```lean
import Shao.Probability.SourceShortTimeKernelBounds

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

theorem sourceTruncation_futureNoise_short_kernel_local_shift_budgets :
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
              ∃ O E : ℕ → ℝ,
                (∀ i : ℕ, 0 ≤ O i ∧ 0 ≤ E i) ∧
                (∀ i ∈ J,
                  (∀ w q : ℝ, |w| ≤ y / 16 →
                    |deriv (o i q) w| ≤ O i ∧
                      |deriv (fun r : ℝ => deriv (e i q) r) w| ≤ E i) ∧
                  (∀ u q : ℝ, 0 ≤ u → u ≤ y / 16 →
                    |f i q 0 - f i q (-u)| ≤ u * O i + u ^ 2 / 2 * E i)) ∧
                m2 * (∑ i ∈ J, O i) ≤
                  C * ((n : ℝ) * |mu| + (n : ℝ) * m3) ∧
                m2 * (∑ i ∈ J, E i) ≤ C

end Shao.Probability
```

The existence of O/E is a conclusion, not supplied derivative or kernel data.
No regulator moment, regional estimate, Fourier identity or time sum appears
as a premise. The actual local shift is evaluated at every q and every
nonnegative u up to the closed source threshold y/16.
