# OQ3 U22ab — actual same-chart quantitative cutoff Laplace integral

DECLARATION_FROZEN_BEFORE_IMPLEMENTATION. Source repair01.md135-210 (SHA2569d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd). Actual source-bound assembly of qualified T/U/Z and new AA: same L and actual mean partial homeomorphism e, exact G/P/F/A, genuine common positive rectangle, forward/inverse chart identity and true global EReal rate on that rectangle; cutoff integrability, exact leading constant and absolute/relative order-t error. Actual center covariance determinant positivity and actual tangential curvature positivity remain explicit source conditions. No conditional Taylor/coercivity/amplitude/measurability/desired integral error is an input. No change to original assumptions is inferred; this auxiliary conditional theorem does not close original B/D.

Module Shao.OQ3.OpenDomainBoundaryLaplaceIntegral; imports OpenDomainBoundaryLowerBound, OpenDomainCovarianceAmplitude, BoundaryLaplaceMeasurability. Namespace Shao.OQ3; open MeasureTheory; scoped Matrix Topology ContDiff.

```lean
theorem open_domain_boundary_laplace_cutoff_integral
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
      let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
        (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
      let P : (ℝ × ℝ) → (ℝ × ℝ) := fun w => e.symm (G w)
      let F : (ℝ × ℝ) → ℝ := fun w =>
        (P w).1 * (G w).1 + (P w).2 * (G w).2 - K (P w)
      let detF : (ℝ × ℝ) → ℝ := fun w => (parabolaCovariance (nu (P w))).det
      let A : (ℝ × ℝ) → ℝ := fun w => (Real.sqrt (detF w))⁻¹
      let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
      let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
        (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
      let C0 : ℝ := A (0, 0) * (Real.sqrt (2 * Real.pi / Lambda1) / (-theta.2))
      let m : Measure (ℝ × ℝ) :=
        (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))
      0 < -theta.2 ∧ P (0, 0) = theta ∧
        A (0, 0) = (Real.sqrt D.det)⁻¹ ∧ 0 < A (0, 0) ∧
        (0 < Lambda1 → 0 < C0 ∧ ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧
          (∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
            G (r, z) ∈ e.target ∧ P (r, z) ∈ e.source ∧ P (r, z) ∈ Omega ∧
              means (P (r, z)) = G (r, z) ∧ 0 < detF (r, z) ∧
              Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
                (G (r, z)) = (F (r, z) : EReal)) ∧
          ∀ t : ℝ, 0 < t → t ≤ 1 →
            let H : (ℝ × ℝ) → ℝ := fun p =>
              if |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho then
                A (t * p.1, t ^ 2 * p.2) *
                  Real.exp (-((F (t * p.1, t ^ 2 * p.2) - F (0, 0)) / t ^ 2)) else 0
            Integrable H m ∧ |(∫ p : ℝ × ℝ, H p ∂m) - C0| ≤ C * t ∧
              |(∫ p : ℝ × ℝ, H p ∂m) / C0 - 1| ≤ C * t)
```

Proof plan: consume T once obtaining L/e and actual F jet/Taylor/coercivity; consume U with that SAME e obtaining actual inverse chart and covariance amplitude. Use cap min(Taylor radius, coercivity radius, amplitude radius), C1 germs, eventual true global rate from T and eventual G target membership to obtain AA's single shared window. Shrink all proven bounds, choose common decay d=min(c,min(lambda,Lambda1/2)), supply AA measurability to Z. Actual A0 positive from center determinant; exact C0 positive from lambda/Lambda1. Divide the derived absolute bound by this proved-positive C0 for relative error. No original-coordinate Jacobian/scaling, exterior real probability, Edgeworth/cells or root closure claim.

Server-only CPU14-17,8192MiB,j4,autoImplicit=false,maxone heavy. Complete fresh independent final proof/type/value review and all-owned transitive axiom audit required. Existing accepted sources remain exact; no replay. Freeze one public theorem/0defs; whole-owner count derived after gate. All future transferred source UTF8 LF before first gate.
