# OQ3 U22ah — actual natural-sample local integral and exact source leading denominator

DECLARATION_FROZEN_BEFORE_IMPLEMENTATION. repair01.md135-210 equation14 and vcorr (SHA2569d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd). Instantiate actual AF's same L/e/J/tiltedcovariance amplitude and positive fixedparabolicstrip into AG's n>=1 transfer and exact constantidentity. Export external n/(2pi), actual exp(-nJ), exact positive main exp(-nJ0)/(sqrt(2pi*n)*lambda*sqrt(detD)*sqrt(Lambda1)) and true relative <=C/sqrt(n). Original actualcenterdeterminant>0 and chosen actualLambda1>0 remain EXPLICIT. No desired scaled/realn error, Taylor/coercivity/measurability/integrability is an input.

Module Shao.OQ3.OpenDomainBoundaryLaplaceNatNormalization; imports OpenDomainBoundaryLaplaceNormalization and BoundaryLaplaceNatNormalization. Namespace Shao.OQ3; MeasureTheory open; Matrix Topology ContDiff scoped.

```lean
theorem open_domain_boundary_laplace_nat_original_strip
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : 0 < (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det)
    (level a0 : ℝ) (hlevel : 0 < level) (ha0 : 0 < a0) (hnegative : theta.2 < 0)
    (hmean : (∫ x : ℝ, x ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2),
      ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) =
        (a0, a0 ^ 2 / level ^ 2))
    (hsaddle : theta.1 = -2 * a0 * theta.2 / level ^ 2) :
    let Omega : Set (ℝ × ℝ) := interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
      (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (nu theta)
    let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
    let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
    let row0 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 0 • pr0 + D 0 1 • pr1
    let row1 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 1 • pr0 + D 1 1 • pr1
    ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = row0.prod row1 ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = means ∧ theta ∈ e.source ∧ e.source ⊆ Omega ∧
      let K : (ℝ × ℝ) → ℝ := fun p => Real.log
        (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
      let J : (ℝ × ℝ) → ℝ := fun w =>
        (e.symm w).1 * w.1 + (e.symm w).2 * w.2 - K (e.symm w)
      let B : (ℝ × ℝ) → ℝ := fun w =>
        (Real.sqrt (parabolaCovariance (nu (e.symm w))).det)⁻¹
      let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
      let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
        (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
      let C0 : ℝ := (Real.sqrt D.det)⁻¹ * (Real.sqrt (2 * Real.pi / Lambda1) / (-theta.2))
      let J0 : ℝ := J (a0, a0 ^ 2 / level ^ 2)
      let m0 : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
      0 < -theta.2 ∧ (0 < Lambda1 → 0 < C0 ∧ ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧
        let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
          w.1 ^ 2 / level ^ 2 - rho ≤ w.2 ∧ w.2 ≤ w.1 ^ 2 / level ^ 2}
        (∀ w ∈ V, w ∈ e.target ∧ e.symm w ∈ e.source ∧ e.symm w ∈ Omega ∧
          means (e.symm w) = w ∧ 0 < (parabolaCovariance (nu (e.symm w))).det ∧
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w = (J w : EReal)) ∧
        ∀ n : ℕ, 1 ≤ n →
          let W : (ℝ × ℝ) → ℝ := fun w => B w * Real.exp (-(n : ℝ) * J w)
          let Ln : ℝ := ((n : ℝ) / (2 * Real.pi)) * ∫ w : ℝ × ℝ in V, W w ∂m0
          let main : ℝ := Real.exp (-(n : ℝ) * J0) /
            (Real.sqrt (2 * Real.pi * (n : ℝ)) * (-theta.2) * Real.sqrt D.det * Real.sqrt Lambda1)
          IntegrableOn W V m0 ∧ 0 < main ∧ |Ln / main - 1| ≤ C / Real.sqrt (n : ℝ))
```

Proof plan: call AF once, preserve exact SAME chart/curvature/window and all trueglobalrate/positiveactualcovariance facts, apply AG's actualn normalization to its proved genuine realt property, then rewrite the main via the source constantidentity. This proves the source local continuous integral's n-version, not the actual sample tail probability. Physical a/qpositive tail-event equivalence/localneighborhood shrink, exterior realprobability rate gap, Edgeworth/cells and original B/D remain OPEN. No new mathematical novelty claim.

One publicTHM/0defs; derive allactualowners/generated/private, full source-to-statement/proof/types/localvalues and kernel/transitiveAX before qualified acceptance. Serveronly CPU14-17,M8192,j4,autoImplicit=false,maxone heavy; no replay accepted checks. UTF8LF before first gate.
