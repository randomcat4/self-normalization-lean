# Frozen actual short-time source kernel sums

Root completely read the literal declaration and full source/payment contract below on 2026-10-23. Exactly one public theorem, sourceTruncation_futureNoise_short_kernel_sums, is APPROVED FOR IMPLEMENTATION. Candidate SHA256 e45e8bd4964377fbb5ec07aee971be7f51747fcdc5bfbc7570b40dcefffb41b1; full contract SHA256 ee0c497e27cc5118ca21b090bd119d17eb52a9e7a83a6ae56ca582295f9d83bb.

The actual max clock index set, arbitrary index-dependent spatial choices, genuine nested derivatives, original source hypotheses and constant-before-law order are fixed. h=h_x is an allowed internal specialization of the actual regional interfaces; all support/positivity/smallness premises must be proved for it. The strict high-frequency partition must be derived from the accepted closed Region4 bound without double counting. Genuine pair integrability and exactly one y^-2 factor precede norm addition. All R/TR and a=-5 clock payments are proof obligations. SourceShortTimeGrid needs its independent final CORRECT before this consumer can be accepted. No target regional, time-sum, kernel or probability estimate is an input. Original C1/C2/probability/desmoothing remain OPEN.

The declaration is frozen exactly as follows; the source-contract.md above is the complete binding proof contract.

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
