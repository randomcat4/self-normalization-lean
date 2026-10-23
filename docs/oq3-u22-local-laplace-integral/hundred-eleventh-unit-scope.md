# OQ3 U22ad — anisotropic half-space measure and genuine rectangle integral scaling

DECLARATIONS_FROZEN_BEFORE_IMPLEMENTATION. Original repair01.md183-200 r=t*u,z=t²*v with t=1/sqrt(n). SourceSHA2569d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd. This unit proves actual product/restricted Lebesgue pushforward scaling t^(-3), integrability equivalence, and genuine fixed-rectangle integral=t³ times scaled cutoff integral. It does not assume desired integral identity/integrability and does not use a probability measure substitute. No original root B/D closure, n/exponential normalization or actual exterior probability claim.

Module Shao.OQ3.BoundaryLaplaceScaling; imports BoundaryLaplaceCoordinates and BoundaryLaplaceIntegral. Namespace Shao.OQ3; MeasureTheory open; Topology scoped.

```lean
theorem boundary_anisotropic_halfspace_scaling (t : ℝ) (ht : 0 < t) :
    let m : Measure (ℝ × ℝ) :=
      (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))
    let T : (ℝ × ℝ) → (ℝ × ℝ) := fun p => (t * p.1, t ^ 2 * p.2)
    Measure.map T m = ENNReal.ofReal ((t ^ 3)⁻¹) • m ∧ MeasurableEmbedding T ∧
      ∀ f : (ℝ × ℝ) → ℝ,
        (Integrable (fun p => f (T p)) m ↔ Integrable f m) ∧
        (∫ p : ℝ × ℝ, f (T p) ∂m) = (t ^ 3)⁻¹ * ∫ p : ℝ × ℝ, f p ∂m

theorem boundary_cutoff_rectangle_integral_scaling
    (f : (ℝ × ℝ) → ℝ) (rho t : ℝ) (ht : 0 < t) :
    let m : Measure (ℝ × ℝ) :=
      (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))
    let m0 : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
    let R : Set (ℝ × ℝ) := {w | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho}
    let H : (ℝ × ℝ) → ℝ := fun p =>
      if |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho then f (t * p.1, t ^ 2 * p.2) else 0
    (Integrable H m ↔ IntegrableOn f R m0) ∧
      (∫ w : ℝ × ℝ in R, f w ∂m0) = t ^ 3 * ∫ p : ℝ × ℝ, H p ∂m
```

Proof plan: positive real coordinate multiplication maps full Lebesgue to its inverse scalar, and preserves the nonnegative half-line after restriction. Map-product and finite nonzero measure scaling yield the first map/integrability/integral facts via a true measurable embedding. For the second, identify the half-space measure restricted to the upper/lateral cutoff with full product Lebesgue restricted to the exact nonnegative rectangle, then use the first genuine equivalence and integral identity. Keep all t>0 conditions; no zero-scale division.

Two publicTHM/0defs; derive actual full-owner counts; complete fresh independent proof/type/value/source review and server-only kernel/all-owner recursive AX, CPU14-17,M8192,j4,autoImplicit=false,maxone heavy. Preserve exact old source evidence, no replay. UTF8LF before first gate.
