# OQ3 U22aj — actual analytic cutoff below an arbitrary prescribed positive radius

DECLARATION_FROZEN_BEFORE_IMPLEMENTATION. Source repair01.md122-210 (SHA2569d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd), especially shrinkU before coordinate integration. Existing AB/AH exports a positive analytic radius but no prescribed-cap guarantee. AI produces a physical positive a/q neighborhood. This new moregeneral actual analytic producer chooses its radius below arbitrary rmax>0 so that the two genuine scopes can be combined. It does not claim existing AH radius was automatically physical. No existing accepted source or mathematical hypothesis changed; rmax is user-of-theorem geometric data, not a new law/tilt condition.

Module Shao.OQ3.OpenDomainBoundaryLaplaceWindow; imports OpenDomainBoundaryLowerBound, OpenDomainCovarianceAmplitude, BoundaryLaplaceMeasurability. Namespace Shao.OQ3; MeasureTheory open; Matrix Topology ContDiff scoped.

```lean
theorem open_domain_boundary_laplace_cutoff_integral_below
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : 0 < (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det)
    (level a0 : ℝ) (hlevel : 0 < level) (ha0 : 0 < a0) (hnegative : theta.2 < 0)
    (hmean : (∫ x : ℝ, x ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2),
      ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) =
        (a0, a0 ^ 2 / level ^ 2))
    (hsaddle : theta.1 = -2 * a0 * theta.2 / level ^ 2)
    (rmax : ℝ) (hrmax : 0 < rmax) :
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
        (0 < Lambda1 → 0 < C0 ∧ ∃ rho C : ℝ, 0 < rho ∧ rho ≤ rmax ∧ 0 < C ∧
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
              |(∫ p : ℝ × ℝ, H p ∂m) / C0 - 1| ≤ C * t)```

Proof plan: same genuine T/U producers and SAME chart witnesses as AB; AA common window gets cap=min(rmax, rhoTaylor, rhoCoercivity, rhoAmplitude), retaining original actualrate+targetQ. Derive radius<=rmax and every smaller-radius Taylor/coercivity/amplitude condition explicitly; prove exact cutoff measurable/Integrable, positive leading constant and absolute+relativeerror by qualified Z. This is new cap-selectable scope, not a repeat gate or rewrite of accepted AB. Physical event equivalence is not asserted yet; next actual consumer will use AI's cap then this producer. Explicit actual determinant and actual Lambda1 positivity remain, exteriorprobability/Edgeworth/rootB/DOPEN.

One publicTHM/0defs, actual allowner generated/private types/values reviewed and server kernel/recursiveAX before acceptance. CPU14-17,M8192,j4,autoImplicit=false,maxone heavy; UTF8LF. No unchanged old check/review replay.
