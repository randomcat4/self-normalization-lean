# U22r — actual source boundary Taylor estimate

Complete declarations frozen before implementation. Module Shao.OQ3.OpenDomainBoundaryTaylor; one public theorem, one private helper, zero definitions. Source: read-only repair01.md equations (8)–(11), lines124–159, with O's exact actual rate/chart/covariance witnesses. The generic Q bound is specialized to the SAME O witness. Tangent first/second derivatives are proved to be actual Frechet evaluations; saddle cancellation gives zero first tangent derivative, full actual Hessian plus curvature gives exact source Lambda1. Positivity of Lambda1 is NOT deduced here or silently supplied. Source original positivity remains a separate actual assumption for the next lower-bound consumer. No amplitude/Jacobian/tail equivalence/Laplace/probability/root closure claim. The true global EReal equality and full jet remain in the conclusion alongside the new fixed closed-rectangle remainder.

```lean
import Shao.OQ3.OpenDomainBoundaryJet
import Shao.OQ3.LocalBoundaryTaylor

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

private theorem boundary_tangent_derivatives
    (F : (ℝ × ℝ) → ℝ) (hF : ContDiffAt ℝ 2 F (0, 0)) :
    deriv (fun t : ℝ => F (t, 0)) 0 = fderiv ℝ F (0, 0) (1, 0) ∧
      deriv (deriv (fun t : ℝ => F (t, 0))) 0 =
        (fderiv ℝ (fun w => fderiv ℝ F w) (0, 0) (1, 0)) (1, 0)

theorem open_domain_quadratic_tilt_boundary_taylor
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det ≠ 0)
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
    let K : (ℝ × ℝ) → ℝ := fun p => Real.log
      (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (nu theta)
    let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
    let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
    let row0 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 0 • pr0 + D 0 1 • pr1
    let row1 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 1 • pr0 + D 1 1 • pr1
    let B : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
      pr0.prod ((2 * a0 / level ^ 2) • pr0 - pr1)
    ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = row0.prod row1 ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = means ∧
      theta ∈ e.source ∧ means theta ∈ e.target ∧ e.source ⊆ Omega ∧
      let J : (ℝ × ℝ) → ℝ := fun z =>
        (e.symm z).1 * z.1 + (e.symm z).2 * z.2 - K (e.symm z)
      let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
        (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
      let F : (ℝ × ℝ) → ℝ := fun w => J (G w)
      let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
      let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
        (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
      0 < -theta.2 ∧ ContDiffAt ℝ ∞ F (0, 0) ∧
        HasFDerivAt F ((-theta.2) • pr1) (0, 0) ∧
        (∀ u v : ℝ × ℝ,
          (fderiv ℝ (fun w => fderiv ℝ F w) (0, 0) u) v =
            (L.symm (B u)).1 * (B v).1 + (L.symm (B u)).2 * (B v).2 +
              (2 * theta.2 / level ^ 2) * u.1 * v.1) ∧
        (∀ᶠ w in 𝓝 (0, 0),
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) (G w) = (F w : EReal)) ∧
        ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧ ∀ r z : ℝ,
          |r| ≤ rho → 0 ≤ z → z ≤ rho →
          |F (r, z) - F (0, 0) - (-theta.2) * z - Lambda1 / 2 * r ^ 2| ≤
            C * (|r| ^ 3 + |r| * z + z ^ 2)

end
end Shao.OQ3
```
