import Shao.OQ3.OpenDomainBoundaryTaylor
import Shao.OQ3.LocalBoundaryLowerBound

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_quadratic_tilt_boundary_lower_bound
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
        (∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧ ∀ r z : ℝ,
          |r| ≤ rho → 0 ≤ z → z ≤ rho →
          |F (r, z) - F (0, 0) - (-theta.2) * z - Lambda1 / 2 * r ^ 2| ≤
            C * (|r| ^ 3 + |r| * z + z ^ 2) ) ∧
        (0 < Lambda1 → ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧ ∀ r z : ℝ,
          |r| ≤ delta → 0 ≤ z → z ≤ delta →
          c * (z + r ^ 2) ≤ F (r, z) - F (0, 0))
 := by
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
  obtain ⟨L, e, hL, he, hs, ht, hsource, hpositive, hsmooth, hfirst, hsecond,
      hglobal, rho, C, hrho, hC, hbound⟩ :=
    open_domain_quadratic_tilt_boundary_taylor
      mu theta htheta hdet level a0 hlevel ha0 hnegative hmean hsaddle
  let J : (ℝ × ℝ) → ℝ := fun z =>
    (e.symm z).1 * z.1 + (e.symm z).2 * z.2 - K (e.symm z)
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
    (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
  let F : (ℝ × ℝ) → ℝ := fun w => J (G w)
  let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
  let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
    (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
  have hb : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (0, 0) - (-theta.2) * z - Lambda1 / 2 * r ^ 2| ≤
        C * (|r| ^ 3 + |r| * z + z ^ 2) := hbound
  refine ⟨L, e, hL, he, hs, ht, hsource, hpositive, hsmooth, hfirst, hsecond,
    hglobal, ⟨rho, C, hrho, hC, hbound⟩, ?_⟩
  intro hcurvature
  change ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧ ∀ r z : ℝ,
    |r| ≤ delta → 0 ≤ z → z ≤ delta →
    c * (z + r ^ 2) ≤ F (r, z) - F (0, 0)
  obtain ⟨delta, c, hd, _, hc, hmargin⟩ := exists_positive_boundary_lower_bound_of_taylor
    F (-theta.2) Lambda1 rho C hpositive hcurvature hrho hC hb
  exact ⟨delta, c, hd, hc, hmargin⟩

end
end Shao.OQ3
