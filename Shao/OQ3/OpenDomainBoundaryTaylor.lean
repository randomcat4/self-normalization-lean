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
 := by
  let g : ℝ → ℝ := fun t => F (t, 0)
  let gamma : ℝ → (ℝ × ℝ) := fun t => (t, 0)
  have hp (t : ℝ) : HasDerivAt gamma (1, 0) t := by
    exact (hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : ℝ))
  have hfirst : HasDerivAt g (fderiv ℝ F (0, 0) (1, 0)) 0 :=
    (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt (f := gamma) (0 : ℝ) (hp 0)
  have hD : DifferentiableAt ℝ (fun w => fderiv ℝ F w) (0, 0) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hpath : HasDerivAt (fun t => fderiv ℝ F (gamma t))
      (fderiv ℝ (fun w => fderiv ℝ F w) (0, 0) (1, 0)) 0 :=
    hD.hasFDerivAt.comp_hasDerivAt (f := gamma) (0 : ℝ) (hp 0)
  have heval := hpath.clm_apply (hasDerivAt_const 0 ((1, 0) : ℝ × ℝ))
  have heval' : HasDerivAt (fun t => (fderiv ℝ F (gamma t)) (1, 0))
      ((fderiv ℝ (fun w => fderiv ℝ F w) (0, 0) (1, 0)) (1, 0)) 0 := by
    simpa only [map_zero, add_zero] using heval
  have hnear : ∀ᶠ w in 𝓝 (0, 0), DifferentiableAt ℝ F w :=
    (hF.eventually (by norm_num)).mono fun _ hw => hw.differentiableAt (by norm_num)
  have htend : Filter.Tendsto gamma (𝓝 0) (𝓝 (0, 0)) := by
    exact (hp 0).continuousAt
  have heq : deriv g =ᶠ[𝓝 0] (fun t => (fderiv ℝ F (gamma t)) (1, 0)) := by
    filter_upwards [htend.eventually hnear] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hp t)).deriv
  exact ⟨hfirst.deriv, (heq.hasDerivAt_iff.mpr heval').deriv⟩

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
  obtain ⟨L, e, hL, he, hs, ht, hsource, hpositive, hsmooth, hfirst, hsecond, hglobal⟩ :=
    open_domain_quadratic_tilt_boundary_coordinate_jet
      mu theta htheta hdet level a0 hlevel ha0 hnegative hmean hsaddle
  let J : (ℝ × ℝ) → ℝ := fun z =>
    (e.symm z).1 * z.1 + (e.symm z).2 * z.2 - K (e.symm z)
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
    (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
  let F : (ℝ × ℝ) → ℝ := fun w => J (G w)
  let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
  let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
    (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
  have hFsmooth : ContDiffAt ℝ ∞ F (0, 0) := hsmooth
  have hFfirst : HasFDerivAt F ((-theta.2) • pr1) (0, 0) := hfirst
  have hT := boundary_tangent_derivatives F (hFsmooth.of_le (by simp))
  have hzero : deriv (fun t : ℝ => F (t, 0)) 0 = 0 := by
    rw [hT.1, hFfirst.fderiv]
    simp [pr1]
  have hnormal : fderiv ℝ F (0, 0) (0, 1) = -theta.2 := by
    rw [hFfirst.fderiv]
    simp [pr1]
  have hBv : B (1, 0) = v := by simp [B, v, pr0, pr1]
  have hcurvature : deriv (deriv (fun t : ℝ => F (t, 0))) 0 = Lambda1 := by
    rw [hT.2, hsecond (1, 0) (1, 0), hBv]
    change (L.symm v).1 * 1 + (L.symm v).2 * (2 * a0 / level ^ 2) +
      (2 * theta.2 / level ^ 2) * 1 * 1 = Lambda1
    dsimp [Lambda1]
    ring
  obtain ⟨rho, C, hrho, hC, hbound⟩ :=
    exists_uniform_boundary_taylor_bound_at_zero F (hFsmooth.of_le (by simp))
  refine ⟨L, e, hL, he, hs, ht, hsource, hpositive, hsmooth, hfirst,
    hsecond, hglobal, rho, C, hrho, hC, ?_⟩
  intro r z hr hz hzr
  change |F (r, z) - F (0, 0) - (-theta.2) * z - Lambda1 / 2 * r ^ 2| ≤
    C * (|r| ^ 3 + |r| * z + z ^ 2)
  simpa only [hzero, zero_mul, sub_zero, hnormal, hcurvature] using hbound r z hr hz hzr

end
end Shao.OQ3
