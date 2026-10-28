import Shao.OQ3.OpenDomainLegendre
import Shao.OQ3.OpenDomainCovarianceAmplitude
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

set_option maxHeartbeats 2000000 in
theorem actual_mean_chart_rate_covariance_derivatives
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (he : (e : (ℝ × ℝ) → (ℝ × ℝ)) = fun p =>
      (∫ x : ℝ, x ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2),
        ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)))
    (hsource : e.source ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (w : ℝ × ℝ) (hw : w ∈ e.target)
    (hdet : 0 < (parabolaCovariance
      (mu.tilted (fun x => (e.symm w).1 * x + (e.symm w).2 * x ^ 2))).det) :
    let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
      (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
    let p : ℝ × ℝ := e.symm w
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (nu p)
    let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
    let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
    let row0 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 0 • pr0 + D 0 1 • pr1
    let row1 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 1 • pr0 + D 1 1 • pr1
    let covector : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
      pr0.smulRight pr0 + pr1.smulRight pr1
    let K : (ℝ × ℝ) → ℝ := fun q => Real.log
      (∫ x : ℝ, Real.exp (q.1 * x + q.2 * x ^ 2) ∂mu)
    let J : (ℝ × ℝ) → ℝ := fun z =>
      (e.symm z).1 * z.1 + (e.symm z).2 * z.2 - K (e.symm z)
    let A : (ℝ × ℝ) → ℝ := fun z =>
      (Real.sqrt (parabolaCovariance (nu (e.symm z))).det)⁻¹
    ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = row0.prod row1 ∧
      ContDiffAt ℝ ∞ (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) w ∧
      HasFDerivAt (e.symm : (ℝ × ℝ) → (ℝ × ℝ))
        (L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) w ∧
      ContDiffAt ℝ ∞ J w ∧
      HasFDerivAt J (p.1 • pr0 + p.2 • pr1) w ∧
      HasFDerivAt (fun z => fderiv ℝ J z)
        (covector.comp (L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) w ∧
      (∀ v : ℝ × ℝ, (fderiv ℝ (fun z => fderiv ℝ J z) w v) v =
        (D 1 1 * v.1 ^ 2 - 2 * D 0 1 * v.1 * v.2 + D 0 0 * v.2 ^ 2) / D.det) ∧
      ContDiffAt ℝ ∞ A w ∧
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w =
        (J w : EReal) := by
  intro nu means p D pr0 pr1 row0 row1 covector K J A
  have hemeans : (e : (ℝ × ℝ) → (ℝ × ℝ)) = means := he
  have hp : p ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) :=
    hsource (e.map_target hw)
  obtain ⟨L, _, hL, _, _, _, _, _, _⟩ :=
    open_domain_quadratic_tilt_local_mean_inverse mu p hp hdet.ne'
  have hd : HasFDerivAt means (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
    rw [hL]
    exact ((open_domain_quadratic_tilt_smooth_and_strict mu).2.2.2 p hp).hasFDerivAt
  have hdE : HasFDerivAt (e : (ℝ × ℝ) → (ℝ × ℝ))
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (e.symm w) := by
    rw [hemeans]
    exact hd
  have hmeans : ContDiffAt ℝ ∞ means p :=
    ((open_domain_quadratic_tilt_smooth_and_strict mu).2.2.1 p hp).contDiffAt
      (isOpen_interior.mem_nhds hp)
  have hinverse : ContDiffAt ℝ ∞ (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) w := by
    apply e.contDiffAt_symm (f₀' := L) hw hdE
    rw [hemeans]
    exact hmeans
  have hInverseD : HasFDerivAt (e.symm : (ℝ × ℝ) → (ℝ × ℝ))
      (L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) w := e.hasFDerivAt_symm hw hdE
  have hKp : ContDiffAt ℝ ∞ K p :=
    ((open_domain_quadratic_tilt_smooth_and_strict mu).2.1 p hp).contDiffAt
      (isOpen_interior.mem_nhds hp)
  have hsmooth : ContDiffAt ℝ ∞ J w :=
    ((hinverse.fst.mul contDiffAt_fst).add (hinverse.snd.mul contDiffAt_snd)).sub
      (hKp.comp w hinverse)
  have hgradient (z : ℝ × ℝ) (hz : z ∈ e.target)
      (hgz : DifferentiableAt ℝ (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) z) :
      HasFDerivAt J (covector (e.symm z)) z := by
    have hparam := hsource (e.map_target hz)
    have hm : means (e.symm z) = z := by
      rw [← hemeans]
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
  have hfirst : HasFDerivAt J (p.1 • pr0 + p.2 • pr1) w :=
    hgradient w hw (hinverse.differentiableAt (by simp))
  have hfinite : ContDiffAt ℝ (1 : WithTop ENat)
      (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) w := hinverse.of_le (by simp)
  have hnear : ∀ᶠ z in 𝓝 w,
      DifferentiableAt ℝ (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) z :=
    (hfinite.eventually (by norm_num)).mono (fun _ hz => hz.differentiableAt (by norm_num))
  have heq : (fun z => fderiv ℝ J z) =ᶠ[𝓝 w]
      (fun z => covector (e.symm z)) := by
    filter_upwards [e.open_target.mem_nhds hw, hnear] with z hz hgz
    exact (hgradient z hz hgz).fderiv
  have hcov : HasFDerivAt (fun z => covector (e.symm z))
      (covector.comp (L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) w :=
    covector.hasFDerivAt.comp w hInverseD
  have hsecond := heq.hasFDerivAt_iff.mpr hcov
  have hD10 : D 1 0 = D 0 1 := rfl
  have hD : D.det = D 0 0 * D 1 1 - (D 0 1) ^ 2 := by
    rw [Matrix.det_fin_two, hD10]
    ring
  have hForward (v : ℝ × ℝ) :
      (D 0 0 * (L.symm v).1 + D 0 1 * (L.symm v).2,
        D 0 1 * (L.symm v).1 + D 1 1 * (L.symm v).2) = v := by
    have hh := L.apply_symm_apply v
    change (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (L.symm v) = v at hh
    rw [hL] at hh
    simpa [row0, row1, pr0, pr1] using hh
  have hInverseRows (v : ℝ × ℝ) :
      (L.symm v).1 = (D 1 1 * v.1 - D 0 1 * v.2) / D.det ∧
      (L.symm v).2 = (D 0 0 * v.2 - D 0 1 * v.1) / D.det := by
    have h0 := congrArg Prod.fst (hForward v)
    have h1 := congrArg Prod.snd (hForward v)
    constructor
    · apply (eq_div_iff hdet.ne').mpr
      rw [hD]
      nlinarith [congrArg (fun r : ℝ => D 1 1 * r) h0,
        congrArg (fun r : ℝ => D 0 1 * r) h1]
    · apply (eq_div_iff hdet.ne').mpr
      rw [hD]
      nlinarith [congrArg (fun r : ℝ => D 0 0 * r) h1,
        congrArg (fun r : ℝ => D 0 1 * r) h0]
  have hQuadratic (v : ℝ × ℝ) :
      (fderiv ℝ (fun z => fderiv ℝ J z) w v) v =
        (D 1 1 * v.1 ^ 2 - 2 * D 0 1 * v.1 * v.2 + D 0 0 * v.2 ^ 2) / D.det := by
    rw [hsecond.fderiv]
    change (L.symm v).1 * v.1 + (L.symm v).2 * v.2 = _
    rw [(hInverseRows v).1, (hInverseRows v).2]
    ring
  let detParam : (ℝ × ℝ) → ℝ := fun q => (parabolaCovariance (nu q)).det
  have hDetParam : ContDiffAt ℝ ∞ detParam p :=
    ((open_domain_quadratic_covariance_det_contDiffOn mu) p hp).contDiffAt
      (isOpen_interior.mem_nhds hp)
  have hDetComp : ContDiffAt ℝ ∞ (fun z => detParam (e.symm z)) w :=
    hDetParam.comp w hinverse
  have hAmplitude : ContDiffAt ℝ ∞ A w :=
    (hDetComp.sqrt hdet.ne').inv (Real.sqrt_pos.mpr hdet).ne'
  have hm : means p = w := by
    rw [← hemeans]
    exact e.right_inv hw
  have hValue := (open_domain_quadratic_tilt_legendre_attained mu p hp).2
  change Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) (means p) =
    ((p.1 * (means p).1 + p.2 * (means p).2 - K p : ℝ) : EReal) at hValue
  rw [hm] at hValue
  exact ⟨L, hL, hinverse, hInverseD, hsmooth, hfirst, hsecond, hQuadratic,
    hAmplitude, hValue⟩

end
end Shao.OQ3
