import Shao.OQ3.OpenDomainLegendre

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_quadratic_tilt_local_rate_derivatives
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det ≠ 0) :
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
    let covector : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
      pr0.smulRight pr0 + pr1.smulRight pr1
    ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = row0.prod row1 ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = means ∧
      theta ∈ e.source ∧ means theta ∈ e.target ∧ e.source ⊆ Omega ∧
      let J : (ℝ × ℝ) → ℝ := fun z =>
        (e.symm z).1 * z.1 + (e.symm z).2 * z.2 - K (e.symm z)
      ContDiffAt ℝ ∞ J (means theta) ∧
        HasFDerivAt J (theta.1 • pr0 + theta.2 • pr1) (means theta) ∧
        HasFDerivAt (fun z => fderiv ℝ J z)
          (covector.comp (L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) (means theta) ∧
        ∀ z ∈ e.target,
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z = (J z : EReal) := by
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
  let covector : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
    pr0.smulRight pr0 + pr1.smulRight pr1
  obtain ⟨L, e, hL, he, hs, ht, hsource, hinverse, hstrict⟩ :=
    open_domain_quadratic_tilt_local_mean_inverse mu theta htheta hdet
  have hmeans : (e : (ℝ × ℝ) → (ℝ × ℝ)) = means := he
  have hcenter : e.symm (means theta) = theta := by
    rw [← hmeans]
    exact e.left_inv hs
  let J : (ℝ × ℝ) → ℝ := fun z =>
    (e.symm z).1 * z.1 + (e.symm z).2 * z.2 - K (e.symm z)
  have hKtheta : ContDiffAt ℝ ∞ K theta :=
    ((open_domain_quadratic_tilt_smooth_and_strict mu).2.1 theta htheta).contDiffAt
      (isOpen_interior.mem_nhds htheta)
  have hKg : ContDiffAt ℝ ∞ K (e.symm (means theta)) := by
    rw [hcenter]
    exact hKtheta
  have hsmooth : ContDiffAt ℝ ∞ J (means theta) :=
    ((hinverse.fst.mul contDiffAt_fst).add (hinverse.snd.mul contDiffAt_snd)).sub
      (hKg.comp (means theta) hinverse)
  have hgradient (z : ℝ × ℝ) (hz : z ∈ e.target)
      (hgz : DifferentiableAt ℝ (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) z) :
      HasFDerivAt J (covector (e.symm z)) z := by
    have hparam : e.symm z ∈ Omega := hsource (e.map_target hz)
    have hm : means (e.symm z) = z := by
      rw [← hmeans]
      exact e.right_inv hz
    have hK := (open_domain_quadratic_tilt_frechet_cumulants mu (e.symm z) hparam).2.2.2.2.1
    change HasFDerivAt K ((means (e.symm z)).1 • pr0 + (means (e.symm z)).2 • pr1)
      (e.symm z) at hK
    rw [hm] at hK
    have hraw := ((hgz.hasFDerivAt.fst.mul pr0.hasFDerivAt).add
      (hgz.hasFDerivAt.snd.mul pr1.hasFDerivAt)).sub (hK.comp z hgz.hasFDerivAt)
    convert hraw using 1
    · funext v
      rfl
    · apply ContinuousLinearMap.ext
      intro v
      simp [covector, pr0, pr1, ContinuousLinearMap.smulRight_apply]
      ring
  have hfirst : HasFDerivAt J (theta.1 • pr0 + theta.2 • pr1) (means theta) := by
    have hh := hgradient (means theta) ht (hinverse.differentiableAt (by simp))
    rw [hcenter] at hh
    exact hh
  have hfinite : ContDiffAt ℝ (1 : WithTop ENat)
      (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) (means theta) := hinverse.of_le (by simp)
  have hnear : ∀ᶠ z in 𝓝 (means theta),
      DifferentiableAt ℝ (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) z :=
    (hfinite.eventually (by norm_num)).mono (fun _ hz => hz.differentiableAt (by norm_num))
  have heq : (fun z => fderiv ℝ J z) =ᶠ[𝓝 (means theta)]
      (fun z => covector (e.symm z)) := by
    filter_upwards [e.open_target.mem_nhds ht, hnear] with z hz hgz
    exact (hgradient z hz hgz).fderiv
  have hcov : HasFDerivAt (fun z => covector (e.symm z))
      (covector.comp (L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) (means theta) :=
    covector.hasFDerivAt.comp (means theta) hstrict.hasFDerivAt
  have hsecond := heq.hasFDerivAt_iff.mpr hcov
  refine ⟨L, e, hL, he, hs, ht, hsource, hsmooth, hfirst, hsecond, ?_⟩
  intro z hz
  have hm : means (e.symm z) = z := by
    rw [← hmeans]
    exact e.right_inv hz
  have hvalue := (open_domain_quadratic_tilt_legendre_attained mu (e.symm z)
    (hsource (e.map_target hz))).2
  change Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
      (means (e.symm z)) =
    (((e.symm z).1 * (means (e.symm z)).1 + (e.symm z).2 * (means (e.symm z)).2 -
      K (e.symm z) : ℝ) : EReal) at hvalue
  rw [hm] at hvalue
  exact hvalue

end
end Shao.OQ3
