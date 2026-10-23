# OQ3 unit165 CF — common polynomially weighted far-frequency damping
Exact THREE full declarations and ALL statement let values frozen BEFORE implementation. Module Shao.OQ3.NormalizedIIDPairSuperpolynomialDecay. Imports Shao.OQ3.NormalizedIIDPairFrequencyDecay and Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics; namespace Shao.OQ3; open MeasureTheory ProbabilityTheory Filter; scoped Topology BigOperators; noncomputable section. ZERO definitions.

Source obligation: turn CE actual normalized iid-law far-annulus exponential damping into a genuinely common arbitrary-polynomial weighted small bound. The N is chosen BEFORE the actual law and frequencies, so depends only on the frozen scalar inputs, not any choice of actual probability law. Input remains the genuine one-observation WC of that law. The exact Euclidean annulus sqrt(n)*R < sqrt(xi²+eta²) <= n³ and strict beta<2/5 stay visible; no assumed normalizedsum error, moments, atomlessness, density, mean or covariance. p is ANY REAL exponent and epsilon is ANY positive real tolerance. No Edgeworth error, frequency integration, annular nonlattice gap, or original root closure. Original strict0<beta<2/5/attribution/accepted correctedA-boundedC/p54 unchanged. CE is source9dcb0009, first kernel/AXPASS, independent fullreview ACTIVE at freeze; it must qualify before acceptance. CD qualified source22120e10 report9adffbf2 all123lines parentread. Rootv59 exact checked receipt30f1cbf1/code29c9804c; PR221e730ce57 frozen rootintake. No shared write or old gate replay.

```lean
theorem tendsto_real_power_mul_stretched_exponential
    (alpha c p : ℝ) (halpha : 0 < alpha) (hc : 0 < c) :
    Filter.Tendsto (fun n : ℕ =>
      Real.rpow (n : ℝ) p * Real.exp (-c * Real.rpow (n : ℝ) alpha))
      Filter.atTop (𝓝 (0 : ℝ))

theorem eventually_real_power_mul_stretched_exponential_lt
    (alpha c p epsilon : ℝ) (halpha : 0 < alpha) (hc : 0 < c)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.rpow (n : ℝ) p * Real.exp (-c * Real.rpow (n : ℝ) alpha) < epsilon

theorem normalized_iid_pair_uniform_far_frequency_decay
    (beta c R p epsilon : ℝ)
    (hbeta : 0 ≤ beta) (hbetaUpper : beta < (2 : ℝ) / 5)
    (hc : 0 < c) (hR : 0 ≤ R) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ law : Measure (ℝ × ℝ), IsProbabilityMeasure law →
        (∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
          ‖(∫ w : ℝ × ℝ,
            Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤
              1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta)) →
        ∀ xi eta : ℝ,
          Real.sqrt (n : ℝ) * R < Real.sqrt (xi ^ 2 + eta ^ 2) →
          Real.sqrt (xi ^ 2 + eta ^ 2) ≤ (n : ℝ) ^ 3 →
          let Q : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
          let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun z =>
            (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, z i
          let rho : Measure (ℝ × ℝ) := Q.map S
          Real.rpow (n : ℝ) p *
            ‖(∫ w : ℝ × ℝ,
              Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ <
                epsilon
```
