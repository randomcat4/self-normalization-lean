# OQ3 unit167 CH — genuine one-observation WC excludes unit modulus at every nonzero pair frequency
Exact TWO complete declarations frozen BEFORE implementation, ALL values explicit; ZERO named definitions and ZERO statement lets. Module Shao.OQ3.WeakCramerPairNonlattice. Imports Mathlib.Analysis.Convex.Integral, Mathlib.Analysis.InnerProductSpace.Basic, Mathlib.Analysis.Complex.Trigonometric; namespace Shao.OQ3; open MeasureTheory; scoped Topology; noncomputable section.

Source-bound middle-frequency prerequisite: a modulus-one probability Fourier integral has actual bounded/measurable/unit-norm kernel a.e. constant. Its natural frequency multiples then have modulusone, contradicting the GENUINE one-observation Euclidean weak-Cramer inequality at sufficiently large multiple. NO positiveatoms/fixedAtom/density/moment/desirednormalizedCF-gap premise. Arbitrary actual pair probability law, explicit literal phase and Euclidean frequency length; no Hilbert assumption on ordinaryProd/MAXnorm. hbeta>=0 retained matching existingWCauxiliary, strict0<beta<2/5 remains rootcondition but is not needed to exclude a lattice. No compact-family uniform gap, integral, Edgeworth or originalroot closure. Existing qualified JointNonlattice source51ce9392 exposes positive-atom result, which is NOT invoked or imported by this generic result. Reuse primary Mathlib Jensen integral strict-convex dichotomy, exponential natural powers and Archimedean natural-multiple selection. Source r2/report.md Fourier ledger and repair01 actualWC/strictrootthreshold retained. Rootv59receipt30f1cbf1 checked29c9804c pinLean4.36.0-rc1/mathlib807d3836; PR221 frozene730ce57/rootintake. CF qualified full101line reportb1c009a8; CG actualfamilyfirstkernel/AXPASS independentreviewACTIVE separately. No old check replay/sharedwrite.

```lean
theorem pair_characteristic_modulus_one_ae_constant
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law]
    (u v : ℝ)
    (hmod : ‖(∫ w : ℝ × ℝ,
      Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ = 1) :
    Integrable (fun w : ℝ × ℝ =>
      Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I)) law ∧
      ∀ᵐ w ∂law,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) =
          ∫ z : ℝ × ℝ,
            Complex.exp (((u * z.1 + v * z.2 : ℝ) : ℂ) * Complex.I) ∂law

theorem weak_cramer_pair_characteristic_norm_lt_one
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law]
    (beta c R : ℝ) (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤
          1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta))
    (u v : ℝ) (hne : u ≠ 0 ∨ v ≠ 0) :
    ‖(∫ w : ℝ × ℝ,
      Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ < 1
```
