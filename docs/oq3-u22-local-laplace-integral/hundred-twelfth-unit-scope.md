# OQ3 U22ae — original-coordinate strip, exponential factor and external normalization transfer

DECLARATION_FROZEN_BEFORE_IMPLEMENTATION. Source repair01.md183-210, especially equation14: fixed local coordinate rectangle and r=t*u,z=t²*v yield exp(-J0/t²)*t³; external1/(2pi*t²) leaves t*exp(-J0/t²)/(2pi). SourceSHA2569d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd.

This is an explicit transfer consumer of the already produced scaled cutoff Integrable/relative bound, not a replacement producer or root closure. J and B arbitrary functions, C0 proved positive input, rho/C arbitrary; an actual source application must instantiate SAME actual J/B/mean chart with qualified AB. No assumed original strip integrability, Jacobian, scaling, exponential-factor identity or desired normalized error. It derives all these from AC/AD and the scaled input. Original a/q tail-event positivity/equivalence, actual exterior probability/rate gap, Edgeworth/cells and B/D remain OPEN.

Module Shao.OQ3.BoundaryLaplaceNormalization; imports BoundaryLaplaceScaling. Namespace Shao.OQ3; MeasureTheory open; Topology scoped.

```lean
theorem boundary_laplace_original_strip_transfer
    (J B : (ℝ × ℝ) → ℝ) (a0 level rho C0 C : ℝ) (hC0 : 0 < C0)
    (hscaled : ∀ t : ℝ, 0 < t → t ≤ 1 →
      let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
        (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
      let m : Measure (ℝ × ℝ) :=
        (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))
      let H : (ℝ × ℝ) → ℝ := fun p =>
        if |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho then
          B (G (t * p.1, t ^ 2 * p.2)) *
            Real.exp (-((J (G (t * p.1, t ^ 2 * p.2)) - J (G (0, 0))) / t ^ 2)) else 0
      Integrable H m ∧ |(∫ p : ℝ × ℝ, H p ∂m) / C0 - 1| ≤ C * t) :
    let m0 : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
    let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
      w.1 ^ 2 / level ^ 2 - rho ≤ w.2 ∧ w.2 ≤ w.1 ^ 2 / level ^ 2}
    let J0 : ℝ := J (a0, a0 ^ 2 / level ^ 2)
    ∀ t : ℝ, 0 < t → t ≤ 1 →
      let W : (ℝ × ℝ) → ℝ := fun w => B w * Real.exp (-J w / t ^ 2)
      let Ln : ℝ := (1 / (2 * Real.pi * t ^ 2)) * ∫ w : ℝ × ℝ in V, W w ∂m0
      let main : ℝ := t * Real.exp (-J0 / t ^ 2) * (C0 / (2 * Real.pi))
      IntegrableOn W V m0 ∧ 0 < main ∧ |Ln / main - 1| ≤ C * t
```

Proof plan: AD derives actual fixed rectangle integrability and t³ integral. AC gives exact original parabolic strip, integrability and measure-preserving set integral. Split exp(-J/t²) into exp(-J0/t²)*exp(-(J-J0)/t²), valid for the actual same functions. Prove positive normalization main from t>0,C0>0,pi>0 andexp>0, then cancel ONLY proved-nonzero factors in the ratio. Actual integrability precedes normalized integral manipulation. No zero-scale case is claimed.

One publicTHM/0defs; actual allowners inclgenerated/private checked in server kernel/recursive AX and fresh independent fullproof/type/value review. CPU14-17,M8192,j4,autoImplicit=false,maxone heavy. Preserve accepted bytes/evidence; no replay. UTF8LF before gate.
