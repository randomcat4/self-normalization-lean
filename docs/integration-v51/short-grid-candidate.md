# Actual short-time integrals and conditional remaining-clock sums

State: AWAITING_ROOT_FREEZE; no new production source or Lean gate started.
Proposed module: Shao.Probability.SourceShortTimeGrid.

```lean
import Shao.Probability.SourceFourierScale
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false
namespace Shao.Probability
open MeasureTheory ProbabilityTheory
theorem sourceShortTime_R_integrals (y : ℝ) (hy : 0 < y) :
    let R : ℝ → ℝ := fun T => 1 + Real.sqrt y * T ^ (-(1 / 4 : ℝ))
    IntegrableOn R (Set.Ioo 0 (y ^ 2)) ∧
      IntegrableOn (fun T => T * R T) (Set.Ioo 0 (y ^ 2)) ∧
      (1 / y ^ 2) * (∫ T in Set.Ioo 0 (y ^ 2), R T) = (7 / 3 : ℝ) ∧
      (1 / y ^ 2) * (∫ T in Set.Ioo 0 (y ^ 2), T * R T) = (15 / 14 : ℝ) * y ^ 2

theorem sourceTruncation_remainingClock_power_integral_comparison :
    ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
      ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
        (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
        (∫ z : ℝ, z ∂ν0) = 0 →
        ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
          Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
          ∀ L2 y a : ℝ, 2 ≤ L2 → 0 < y →
            let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
            let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂ρ
            let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
            let T : ℕ → ℝ := fun i => ((n - i : ℕ) : ℝ) * m2
            let J : Finset ℕ := (Finset.range (n + 1)).filter
              (fun i => n / 2 < i ∧ L2 * gamma ^ 2 ≤ T i ∧ T i < y ^ 2)
            IntegrableOn (fun t : ℝ => t ^ a) (Set.Icc (L2 * gamma ^ 2 / 2) (y ^ 2)) ∧
              m2 * (∑ i ∈ J, T i ^ a) ≤
                (2 : ℝ) ^ |a| * (∫ t in Set.Icc (L2 * gamma ^ 2 / 2) (y ^ 2), t ^ a)

theorem sourceTruncation_shortClock_R_sums :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
          (∫ z : ℝ, z ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ L2 y : ℝ, 2 ≤ L2 → 0 < y →
              let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
              let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂ρ
              let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
              let T : ℕ → ℝ := fun i => ((n - i : ℕ) : ℝ) * m2
              let J : Finset ℕ := (Finset.range (n + 1)).filter
                (fun i => n / 2 < i ∧ L2 * gamma ^ 2 ≤ T i ∧ T i < y ^ 2)
              let R : ℝ → ℝ := fun t => 1 + Real.sqrt y * t ^ (-(1 / 4 : ℝ))
              m2 / y ^ 2 * (∑ i ∈ J, R (T i)) ≤ C ∧
                m2 / y ^ 2 * (∑ i ∈ J, T i * R (T i)) ≤ C * y ^ 2
end Shao.Probability
```
