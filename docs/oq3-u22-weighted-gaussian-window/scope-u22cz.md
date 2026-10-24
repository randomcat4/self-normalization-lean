# U22CZ185 complete exact declaration freeze

Freeze before implementation. Honest integration bridge: for an actual pair probability law and an explicitly supplied pointwise actual CF Gaussian comparison on the exact scaled ball, produce genuine weighted-error IntegrableOn and a nonnegative weighted Lebesgue integral bounded by the actual genuinely integrable whole-plane Gaussian moment. EVERY natural polynomial weight k, explicit B/sqrt(n), no hidden finite-integral premise. The supplied pointwise error is a modular hypothesis ONLY for this helper; canonical caller must derive it from CX183 (already authorPASS), never assume it for originalB/D. Consumes qualified CI168 actualpairCF continuity and CY184 genuineGaussianpolynomialintegrability (CYauthorPASS mustqualifybeforeacceptance). ALL4statementletvalues frozen. Nextcanonicalfullpacket actualweightederror integral will discharge the helper hypothesis. No rootEdgeworth/inversion/exterior/Laplace closure. ALLheavyserveronly CPU14-17 max1 -M8192 -j4, nooldPASSgate replay.

```lean
theorem pair_characteristic_small_frequency_weighted_integral_bound
    (rho : Measure (ℝ × ℝ)) [IsProbabilityMeasure rho]
    (n : ℕ) (hn : 1 ≤ n) (delta B : ℝ) (hB : 0 ≤ B)
    (herror : ∀ xi eta : ℝ,
      Real.sqrt ((xi / Real.sqrt (n : ℝ)) ^ 2 +
        (eta / Real.sqrt (n : ℝ)) ^ 2) ≤ delta →
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho) -
          ((Real.exp (-(xi ^ 2 + eta ^ 2) / 2) : ℝ) : ℂ)‖ ≤
        B / Real.sqrt (n : ℝ) * (Real.sqrt (xi ^ 2 + eta ^ 2)) ^ 3 *
          Real.exp (-(xi ^ 2 + eta ^ 2) / 8))
    (k : ℕ) :
    let small : Set (ℝ × ℝ) := {w |
      Real.sqrt ((w.1 / Real.sqrt (n : ℝ)) ^ 2 +
        (w.2 / Real.sqrt (n : ℝ)) ^ 2) ≤ delta}
    let error : (ℝ × ℝ) → ℝ := fun z =>
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho) -
          ((Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) : ℝ) : ℂ)‖
    let weight : (ℝ × ℝ) → ℝ := fun z => (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k
    let envelope : (ℝ × ℝ) → ℝ := fun z =>
      (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ (k + 3) *
        Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)
    Integrable envelope ∧ IntegrableOn (fun z => weight z * error z) small ∧
      0 ≤ (∫ z in small, weight z * error z) ∧
      (∫ z in small, weight z * error z) ≤
        B / Real.sqrt (n : ℝ) * (∫ z : ℝ × ℝ, envelope z)
```
