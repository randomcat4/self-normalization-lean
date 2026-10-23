# OQ3 U22aa — frozen cutoff measurability and common analytic window

Status: DECLARATIONS_FROZEN_BEFORE_IMPLEMENTATION. Author: current OQ3 lead; independent final review required. Source-bound dependency: repair01.md lines135-210, SHA2569d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd. This unit removes the explicit AE measurability input of qualified Z using genuine local continuity. It also creates a common positive closed rectangle under any existing cap while preserving an actual eventual property Q. It does not assert original B/D closure, coordinate Jacobian, scaling or probability tails.

Exact declarations (module Shao.OQ3.BoundaryLaplaceMeasurability), namespace Shao.OQ3, MeasureTheory open, Topology scoped:

```lean
theorem boundary_laplace_cutoff_aestronglyMeasurable_of_continuousOn
    (F A : (ℝ × ℝ) → ℝ) (rho t : ℝ)
    (hF : ContinuousOn F {w : ℝ × ℝ | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho})
    (hA : ContinuousOn A {w : ℝ × ℝ | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho}) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      if |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho then
        A (t * p.1, t ^ 2 * p.2) *
          Real.exp (-((F (t * p.1, t ^ 2 * p.2) - F (0, 0)) / t ^ 2)) else 0)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0)))

theorem exists_boundary_continuous_cutoff_window
    (F A : (ℝ × ℝ) → ℝ)
    (hF : ContDiffAt ℝ 1 F (0, 0)) (hA : ContDiffAt ℝ 1 A (0, 0))
    (Q : (ℝ × ℝ) → Prop) (hQ : ∀ᶠ w in 𝓝 (0, 0), Q w)
    (rho0 : ℝ) (hrho0 : 0 < rho0) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ rho0 ∧
      (∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho → Q (r, z)) ∧
      ContinuousOn F {w : ℝ × ℝ | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho} ∧
      ContinuousOn A {w : ℝ × ℝ | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho} ∧
      ∀ t : ℝ, AEStronglyMeasurable (fun p : ℝ × ℝ =>
        if |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho then
          A (t * p.1, t ^ 2 * p.2) *
            Real.exp (-((F (t * p.1, t ^ 2 * p.2) - F (0, 0)) / t ^ 2)) else 0)
        ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0)))
```

Proof plan: restrict a continuous scaled uncut kernel to the Borel set that additionally imposes p.2≥0; use its measurable indicator, then AE equality under the actual product/restricted Lebesgue measure to restore Z's exact cutoff. No control of F/A at negative normal coordinates or outside the rectangle is assumed. For the second declaration, finite order1 permits eventual ContDiffAt1; obtain a metric neighborhood of continuity and Q and shrink under rho0. No desired measurability, integrability, Taylor or error estimate is an input.

All Lean and recursive axiom audits server-only CPU14-17 /8192MiB/j4, maxone heavy. Frozen two public theorems/0defs; all actual owners including any private/generated values must be independently covered. Standard three axioms only; no successful unchanged gate replay.
