# U22CY184 complete exact declaration freeze

Freeze before implementation. Genuine Lebesgue integrability of EVERY natural Euclidean radial polynomial times exp(-a*radius²), for EVERY a>0, on literal real-pair frequency space. Supporting nonnegative power bound and genuine one-dimensional even/polynomial Gaussian integrability from pinned primary Mathlib GaussianIntegral and Integral.Prod. No finite-volume/truncation, assumed finite integral, or substitution of Prod max norm for the literal Euclidean radius. Mathlib-only helper is an actual envelope integrability producer for the next canonical actual small-frequency error integral, not originalB/D or Edgeworth closure. ALLheavy serverONLY CPU14-17 max1 -M8192 -j4, nooldPASSgate replay, existing exact pinned package objects reused readonly.

```lean
theorem one_add_nonnegative_power_bound (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (1 + x) ^ k ≤ (2 : ℝ) ^ k * (1 + x ^ k)

theorem integrable_even_power_gaussian (k : ℕ) (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ => x ^ (2 * k) * Real.exp (-a * x ^ 2))

theorem integrable_one_add_square_power_gaussian (k : ℕ) (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ => (1 + x ^ 2) ^ k * Real.exp (-a * x ^ 2))

theorem integrable_euclidean_radius_power_gaussian (k : ℕ) (a : ℝ) (ha : 0 < a) :
    Integrable (fun w : ℝ × ℝ =>
      (Real.sqrt (w.1 ^ 2 + w.2 ^ 2)) ^ k * Real.exp (-a * (w.1 ^ 2 + w.2 ^ 2)))
```
