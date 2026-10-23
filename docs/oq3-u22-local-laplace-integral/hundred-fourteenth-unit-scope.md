# OQ3 U22ag — exact source constant and natural-number normalization

DECLARATIONS_FROZEN_BEFORE_IMPLEMENTATION. repair01.md183-210 equation14 and vcorr (SHA2569d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd). Proves exact source leading coefficient and integer n>=1 specialization of real t normalized integral, with external n/(2pi), exp(-nJ0), 1/sqrt(n) relative rate. Real input is the exact property already produced by actual AF, not assumed as original root. No actual random-sample probability, physical tail-event equivalence, exterior rate-gap, Edgeworth/cells or B/D closure.

Module Shao.OQ3.BoundaryLaplaceNatNormalization; imports BoundaryLaplaceNormalization and Mathlib.Analysis.SpecialFunctions.Sqrt. Namespace Shao.OQ3; MeasureTheory open; Topology scoped.

```lean
theorem boundary_laplace_source_leading_constant (det lambda Lambda1 : ℝ) :
    ((Real.sqrt det)⁻¹ * (Real.sqrt (2 * Real.pi / Lambda1) / lambda)) / (2 * Real.pi) =
      1 / (Real.sqrt (2 * Real.pi) * lambda * Real.sqrt det * Real.sqrt Lambda1) ∧
    ∀ (n : ℕ) (J0 : ℝ),
      Real.exp (-(n : ℝ) * J0) *
        (((Real.sqrt det)⁻¹ * (Real.sqrt (2 * Real.pi / Lambda1) / lambda)) / (2 * Real.pi)) /
          Real.sqrt (n : ℝ) =
        Real.exp (-(n : ℝ) * J0) /
          (Real.sqrt (2 * Real.pi * (n : ℝ)) * lambda * Real.sqrt det * Real.sqrt Lambda1)

theorem boundary_laplace_nat_scale (n : ℕ) (hn : 1 ≤ n) :
    let t : ℝ := (Real.sqrt (n : ℝ))⁻¹
    0 < t ∧ t ≤ 1 ∧ t ^ 2 = 1 / (n : ℝ) ∧
      1 / (2 * Real.pi * t ^ 2) = (n : ℝ) / (2 * Real.pi) ∧
      ∀ J0 C0 : ℝ,
        Real.exp (-J0 / t ^ 2) = Real.exp (-(n : ℝ) * J0) ∧
        t * Real.exp (-J0 / t ^ 2) * (C0 / (2 * Real.pi)) =
          Real.exp (-(n : ℝ) * J0) * (C0 / (2 * Real.pi)) / Real.sqrt (n : ℝ)

theorem boundary_laplace_nat_normalization
    (J B : (ℝ × ℝ) → ℝ) (V : Set (ℝ × ℝ)) (J0 C0 C : ℝ)
    (hreal : ∀ t : ℝ, 0 < t → t ≤ 1 →
      let m0 : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
      let W : (ℝ × ℝ) → ℝ := fun w => B w * Real.exp (-J w / t ^ 2)
      let Ln : ℝ := (1 / (2 * Real.pi * t ^ 2)) * ∫ w : ℝ × ℝ in V, W w ∂m0
      let main : ℝ := t * Real.exp (-J0 / t ^ 2) * (C0 / (2 * Real.pi))
      IntegrableOn W V m0 ∧ 0 < main ∧ |Ln / main - 1| ≤ C * t) :
    let m0 : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
    ∀ n : ℕ, 1 ≤ n →
      let W : (ℝ × ℝ) → ℝ := fun w => B w * Real.exp (-(n : ℝ) * J w)
      let Ln : ℝ := ((n : ℝ) / (2 * Real.pi)) * ∫ w : ℝ × ℝ in V, W w ∂m0
      let main : ℝ := Real.exp (-(n : ℝ) * J0) * (C0 / (2 * Real.pi)) / Real.sqrt (n : ℝ)
      IntegrableOn W V m0 ∧ 0 < main ∧ |Ln / main - 1| ≤ C / Real.sqrt (n : ℝ)
```

Proof plan: actual sqrt_div/sqrt_div_self and sqrt_mul yield source denominator identities without silent sign assumptions; these are algebra identities under ordinary totalized division, while actual AF separately proves positive leading main. For n>=1, prove sqrt(n)>0 and>=1, t=1/sqrt(n) admissible, t²=1/n, then exact external coefficient/exponent/main substitutions. Apply the given realt integral theorem at this genuine t, transport function equality and positive main, and convert C*t to C/sqrt(n). All integrability conclusions inherited from a genuine proved realt property, never from default-zero integral. Zero n excluded for analytic specialization.

Three publicTHM/0defs, fullactualowner generated/private counts derived; independent complete proof/type/value review plus server-only kernel/recursiveAX required, CPU14-17,M8192,j4,autoImplicit=false,maxone heavy. No repeated unchanged accepted checks. UTF8LF before first gate.
