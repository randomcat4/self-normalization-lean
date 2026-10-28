# GQ280: Gaussian damping preserves the actual weighted Fourier error norm bound

Frozen before implementation at 2026-10-27T23:07:19.182613+00:00. Module Shao.OQ3.GaussianDampedWeightedErrorIntegral. One full theorem/3statementlets. QualifiedFK248 true oscillatory integral API is directdependency, no oldcheck replay. Continuous arbitrarycomplexerror e on actualR², anyset s, naturalEuclideanradiuspower k, b>=0. Given true weightednorm IntegrableOn, actualGaussian damping exp(-b*Q) produces true dampedweightednorm integrability, no larger integral, and forallx true negativephase oscillatory integral/no larger norm. This interface transfers already-proven actualFL log-cubic window norm error into Gaussian-smoothed inversion without adding desired error bound to a root theorem. It does not itself instantiate the whole actualcanonicalFL packet or glue central/tail Hermite density errors. It remains an auxiliary analytic lemma, b0 and arbitrarys/k0 included. Originalweighteddesmoothing/exterior/B-D/positiveOQ3root remainOPEN. No noveltyclaim or externalSong axiom.

## Complete frozen declaration

```lean
theorem pair_gaussian_damped_weighted_error_integral_bound
    (e : (ℝ × ℝ) → ℂ) (he : Continuous e)
    (s : Set (ℝ × ℝ)) (k : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hInt : IntegrableOn (fun z : ℝ × ℝ =>
      Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ k * ‖e z‖) s) :
    let weight : (ℝ × ℝ) → ℝ := fun z =>
      Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ k
    let damping : (ℝ × ℝ) → ℝ := fun z => Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2))
    let kernel : (ℝ × ℝ) → (ℝ × ℝ) → ℂ := fun x z =>
      Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ))
    IntegrableOn (fun z => weight z * ‖(damping z : ℂ) * e z‖) s ∧
      (∫ z in s, weight z * ‖(damping z : ℂ) * e z‖) ≤
        ∫ z in s, weight z * ‖e z‖ ∧
      ∀ x : ℝ × ℝ,
        IntegrableOn (fun z => kernel x z * (weight z : ℂ) *
          ((damping z : ℂ) * e z)) s ∧
          ‖∫ z in s, kernel x z * (weight z : ℂ) * ((damping z : ℂ) * e z)‖ ≤
            ∫ z in s, weight z * ‖e z‖
```
