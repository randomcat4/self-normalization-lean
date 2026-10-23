# OQ3 U22ac — exact original-coordinate boundary chart measure and domain

DECLARATIONS_FROZEN_BEFORE_IMPLEMENTATION. Original repair01.md section5-6, especially original coordinate r=a-a0,z=a²/level²-b and subsequent equation(14). SourceSHA2569d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd. No new source assumption: these coordinate identities hold for any real a0/level/rho under Lean's ordinary totalized real division; original positive-level specialization remains the source application.

Module Shao.OQ3.BoundaryLaplaceCoordinates. Namespace Shao.OQ3; open MeasureTheory; Topology scoped. Imports Mathlib.MeasureTheory.Group.Prod, Mathlib.MeasureTheory.Integral.Bochner.Set, Mathlib.MeasureTheory.Measure.Haar.NormedSpace.

```lean
theorem boundary_rate_chart_measure_and_integral (a0 level : ℝ) :
    let m : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
    let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
      (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
    MeasurePreserving G m m ∧ MeasurableEmbedding G ∧
      ∀ (s : Set (ℝ × ℝ)) (f : (ℝ × ℝ) → ℝ),
        (IntegrableOn f (G '' s) m ↔ IntegrableOn (fun w => f (G w)) s m) ∧
        (∫ w : ℝ × ℝ in G '' s, f w ∂m) = ∫ w : ℝ × ℝ in s, f (G w) ∂m

theorem boundary_rate_chart_rectangle_image (a0 level rho : ℝ) :
    let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
      (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
    G '' {w : ℝ × ℝ | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho} =
      {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
        w.1 ^ 2 / level ^ 2 - rho ≤ w.2 ∧ w.2 ≤ w.1 ^ 2 / level ^ 2}
```

Proof plan: composition of first-coordinate translation, second-coordinate reflection and continuous quadratic skew translation preserves actual product Lebesgue measure. Construct the genuine inverse (a-a0,a²/level²-b) as a local homeomorphism to obtain a measurable embedding; apply exact restricted measure change of variables to derive BOTH integrability equivalence and set integral identity. No desired integral equality, Jacobian assumption or probability substitution is an input. Prove exact parabolic strip image by both explicit inverses. This establishes unit absolute Jacobian measure behavior and exact local coordinate domain, but does not prove scaled t³/n factors, relative normalization, actual exterior probability or original rootB/D closure.

Two publicTHM/0defs; any generated/private owners included in full source-to-statement/proof/alltype+value independent review and server kernel/recursive AX audit. CPU14-17,M8192,j4,autoImplicit=false,maxone heavy lane. No unchanged accepted gates replayed; future source UTF8LF before first gate.
