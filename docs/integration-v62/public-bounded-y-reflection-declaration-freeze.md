# Frozen actual bounded-y reflection producers

Root fully read proof-candidate.md, candidate-declarations.md and candidate-check.md once, checked the source fixed-truncation/nonzero-conditional-drift objects, true scalar-density smoothing, large-push positive-clock count, terminal-inclusive micro-clock and max(Llong,Lshort) subset payment. Mathematical candidate approved for production; no kernel or final acceptance claimed yet.

Owner: /root/common_bounded_y_probability_candidate. Only new module Shao/Probability/SourceBoundedYReflection.lean plus its assigned draft outputs. Old accepted sources/objects and pending qualified energy-square source are read-only. Four complete public heads below are frozen literally, including every let. Zero new global/private definitions. Extra private helper THEOREMS are permitted under this freeze and require complete source/type/axiom coverage in the final independent review; this supersedes the candidate's suggested local-have-only implementation restriction. No new public head or changed assumptions/constants without literal addendum before implementation.

The true fixed scalar density supplies both derivatives and Lipschitz for arbitrary future length including0; derivative bounds are not caller hypotheses. Full sourceFourierTest/actual chord+scalar noise, original finite second moment/normalization/mean0/budget, same fixed-x conditional law and its nonzero mu, true regulator, prefix energy and same product P remain fixed. No root closure beyond the exact bounded-y smoothed comparison is claimed. Existing OQ3 accepted A and bounded compact-tilt C scopes stay unchanged.

All Lean/heavy server-only, pinned Lean/mathlib/cache, CPU10-13/root-heavy.lock/M8192/j4/autoImplicitfalse; first whole-source success emits original-o and directrc immediately. Failed logs retained; no successful producer/audit replays. New UTF8 LF from first write. Fresh complete source-to-statement/proof/types/allvalues/private/generated/transitiveAX review required; allowed axioms propext/Classical.choice/Quot.sound. No sorry/admit/newaxiom/unsafe/native_decide. Continue to next source-bound dependency after each completed head.

```lean
theorem sourceFutureNoiseKernel_scalar_rough_bounds :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun a : ℝ => |a| ^ 3) ν →
        0 < variance (id : ℝ → ℝ) ν →
        ∀ h : ℝ, 0 < h → (∀ᵐ a : ℝ ∂ν, |a| ≤ h) →
          let gamma : ℝ :=
            (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν
          ∀ (m : ℕ) (y : ℝ), 0 ≤ y →
            (∀ p : ℝ × ℝ,
              0 ≤ sourceFutureNoiseKernel ν m y p ∧
                sourceFutureNoiseKernel ν m y p ≤ 1) ∧
            (∀ q : ℝ,
              let f : ℝ → ℝ := fun w => sourceFutureNoiseKernel ν m y (w, q)
              (∀ w : ℝ,
                DifferentiableAt ℝ f w ∧
                  DifferentiableAt ℝ (fun r : ℝ => deriv f r) w ∧
                  |deriv f w| ≤ C / gamma ∧
                  |deriv (fun r : ℝ => deriv f r) w| ≤ C / gamma ^ 2) ∧
              (∀ w v : ℝ, |f w - f v| ≤ C / gamma * |w - v|))
```

```lean
theorem sourceTruncation_lindleyDelta_large_push_sum :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
          (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            let ρ : Measure ℝ :=
              ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
            let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
            let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ρ)
            ∀ y : ℝ, 0 < y →
              let ψ : ℝ × ℝ → ℝ := fun p =>
                ∫ z : ℝ × ℝ,
                  sourceFourierTest y (p.1 + z.1, p.2 + z.2)
                  ∂quadraticFullNoiseLaw ρ
              let T : Fin n → ℝ := fun j =>
                (((n - (j.val + 1) : ℕ) : ℝ)) * m2
              let J : Finset (Fin n) := Finset.univ.filter
                (fun j => n / 2 < j.val + 1 ∧ 0 < T j ∧ T j < y ^ 2)
              (∑ j ∈ J,
                ∫ a : Shao.Path n,
                  (if y / 16 < lindleyRegulator a j then
                    |lindleyDelta ρ ψ a j| else 0) ∂P) ≤
                (∑ j ∈ J,
                  (P {a : Shao.Path n | y / 16 < lindleyRegulator a j}).toReal) ∧
              (∑ j ∈ J,
                (P {a : Shao.Path n | y / 16 < lindleyRegulator a j}).toReal) ≤
                  C * (n : ℝ) * m3
```

```lean
theorem sourceTruncation_lindleyDelta_micro_clock_sum :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
          (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            let ρ : Measure ℝ :=
              ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
            let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
            let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
            let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ρ)
            ∀ L y : ℝ, 1 ≤ L → 0 ≤ y →
              let ψ : ℝ × ℝ → ℝ := fun p =>
                ∫ z : ℝ × ℝ,
                  sourceFourierTest y (p.1 + z.1, p.2 + z.2)
                  ∂quadraticFullNoiseLaw ρ
              let T : Fin n → ℝ := fun j =>
                (((n - (j.val + 1) : ℕ) : ℝ)) * m2
              let J : Finset (Fin n) := Finset.univ.filter
                (fun j => n / 2 < j.val + 1 ∧ T j < L * gamma ^ 2)
              (∑ j ∈ J, ∫ a : Shao.Path n, |lindleyDelta ρ ψ a j| ∂P) ≤
                C * (L + 1) * ((n : ℝ) * m3)
```

```lean
theorem sourceTruncation_bounded_y_reflection_comparison :
    ∃ C epsilon0 : ℝ, 0 < C ∧ 0 < epsilon0 ∧ epsilon0 ≤ 1 / 2 ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
          (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ epsilon0 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            let ρ : Measure ℝ :=
              ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
            let mu : ℝ := ∫ a : ℝ, a ∂ρ
            let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
            let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ρ)
            ∀ y : ℝ, gamma ≤ y → y ≤ 2 →
              let ψ : ℝ × ℝ → ℝ := fun p =>
                ∫ z : ℝ × ℝ,
                  sourceFourierTest y (p.1 + z.1, p.2 + z.2)
                  ∂quadraticFullNoiseLaw ρ
              (∀ j : Fin n,
                Integrable (fun a : Shao.Path n => |lindleyDelta ρ ψ a j|) P) ∧
              (∑ j : Fin n, ∫ a : Shao.Path n, |lindleyDelta ρ ψ a j| ∂P) ≤
                C * ((n : ℝ) * |mu| + (n : ℝ) * m3) ∧
              ((∫ a : Shao.Path n,
                  ψ (Shao.lindleyState a n le_rfl, Shao.energy a) ∂P) -
                (∫ a : Shao.Path n,
                  ψ (Shao.prefixSum a n, Shao.energy a) ∂P) =
                ∑ j : Fin n, ∫ a : Shao.Path n, lindleyDelta ρ ψ a j ∂P) ∧
              |(∫ a : Shao.Path n,
                  ψ (Shao.lindleyState a n le_rfl, Shao.energy a) ∂P) -
                (∫ a : Shao.Path n,
                  ψ (Shao.prefixSum a n, Shao.energy a) ∂P)| ≤
                C * ((n : ℝ) * |mu| + (n : ℝ) * m3)
```
