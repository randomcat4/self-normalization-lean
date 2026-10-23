import Shao.OQ3.OpenDomainRateDerivatives

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_quadratic_tilt_boundary_rate_derivatives
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det ≠ 0)
    (level a0 : ℝ) (hlevel : 0 < level) (ha0 : 0 < a0)
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
    ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = row0.prod row1 ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = means ∧
      theta ∈ e.source ∧ means theta ∈ e.target ∧ e.source ⊆ Omega ∧
      let J : (ℝ × ℝ) → ℝ := fun z =>
        (e.symm z).1 * z.1 + (e.symm z).2 * z.2 - K (e.symm z)
      let f : ℝ → ℝ := fun a => J (a, a ^ 2 / level ^ 2)
      let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
      let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
        (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
      ContDiffAt ℝ ∞ f a0 ∧ HasDerivAt f 0 a0 ∧
        HasDerivAt (deriv f) Lambda1 a0 ∧
        ∀ᶠ a in 𝓝 a0,
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
            (a, a ^ 2 / level ^ 2) = (f a : EReal) := by
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
  obtain ⟨L, e, hL, he, hs, ht, hsource, hJsmooth, hJfirst, hJsecond, hglobal⟩ :=
    open_domain_quadratic_tilt_local_rate_derivatives mu theta htheta hdet
  let J : (ℝ × ℝ) → ℝ := fun z =>
    (e.symm z).1 * z.1 + (e.symm z).2 * z.2 - K (e.symm z)
  let gamma : ℝ → (ℝ × ℝ) := fun a => (a, a ^ 2 / level ^ 2)
  let V : ℝ → (ℝ × ℝ) := fun a => (1, 2 * a / level ^ 2)
  let f : ℝ → ℝ := fun a => J (gamma a)
  let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
  let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
    (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
  have hcenter : gamma a0 = means theta := hmean.symm
  have hsmoothJ : ContDiffAt ℝ ∞ J (means theta) := hJsmooth
  have hfirstJ : HasFDerivAt J (theta.1 • pr0 + theta.2 • pr1) (means theta) := hJfirst
  have hsecondJ : HasFDerivAt (fun z => fderiv ℝ J z)
      (covector.comp (L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) (means theta) := hJsecond
  have hgamma (a : ℝ) : HasDerivAt gamma (V a) a := by
    have hh := (hasDerivAt_id a).prodMk (((hasDerivAt_id a).pow 2).div_const (level ^ 2))
    simpa [gamma, V] using hh
  have hV : HasDerivAt V (0, 2 / level ^ 2) a0 := by
    have hh := (hasDerivAt_const a0 (1 : ℝ)).prodMk
      (((hasDerivAt_id a0).const_mul 2).div_const (level ^ 2))
    simpa [V] using hh
  have hgammasmooth : ContDiff ℝ ∞ gamma := by dsimp [gamma]; fun_prop
  have hsmooth : ContDiffAt ℝ ∞ f a0 := by
    have hh : ContDiffAt ℝ ∞ J (gamma a0) := by rw [hcenter]; exact hsmoothJ
    exact hh.comp a0 hgammasmooth.contDiffAt
  have hzero : (theta.1 • pr0 + theta.2 • pr1) v = 0 := by
    change theta.1 * 1 + theta.2 * (2 * a0 / level ^ 2) = 0
    rw [hsaddle]
    ring
  have hfirst : HasDerivAt f 0 a0 := by
    have hh : HasFDerivAt J (theta.1 • pr0 + theta.2 • pr1) (gamma a0) := by
      rw [hcenter]
      exact hfirstJ
    have hd := hh.comp_hasDerivAt a0 (hgamma a0)
    change HasDerivAt f ((theta.1 • pr0 + theta.2 • pr1) v) a0 at hd
    rw [hzero] at hd
    exact hd
  have hpathD : HasDerivAt (fun a => fderiv ℝ J (gamma a))
      ((covector.comp (L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) v) a0 := by
    have hh : HasFDerivAt (fun z => fderiv ℝ J z)
        (covector.comp (L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) (gamma a0) := by
      rw [hcenter]
      exact hsecondJ
    exact hh.comp_hasDerivAt a0 (hgamma a0)
  have hcoeff : ((covector.comp (L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) v) (V a0) +
      (fderiv ℝ J (gamma a0)) (0, 2 / level ^ 2) = Lambda1 := by
    rw [hcenter, hfirstJ.fderiv]
    change ((L.symm v).1 * 1 + (L.symm v).2 * (2 * a0 / level ^ 2)) +
      (theta.1 * 0 + theta.2 * (2 / level ^ 2)) =
        2 * theta.2 / level ^ 2 + (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
    ring
  have hEval := hpathD.clm_apply hV
  rw [hcoeff] at hEval
  have hfinite : ContDiffAt ℝ (1 : WithTop ENat) J (means theta) := hsmoothJ.of_le (by simp)
  have hnear : ∀ᶠ z in 𝓝 (means theta), DifferentiableAt ℝ J z :=
    (hfinite.eventually (by norm_num)).mono (fun _ hz => hz.differentiableAt (by norm_num))
  have htend : Filter.Tendsto gamma (𝓝 a0) (𝓝 (means theta)) := by
    rw [← hcenter]
    exact hgammasmooth.continuous.continuousAt
  have heq : deriv f =ᶠ[𝓝 a0] (fun a => (fderiv ℝ J (gamma a)) (V a)) := by
    filter_upwards [htend.eventually hnear] with a ha
    exact (ha.hasFDerivAt.comp_hasDerivAt a (hgamma a)).deriv
  have hsecond : HasDerivAt (deriv f) Lambda1 a0 := heq.hasDerivAt_iff.mpr hEval
  refine ⟨L, e, hL, he, hs, ht, hsource, hsmooth, hfirst, hsecond, ?_⟩
  filter_upwards [htend.eventually (e.open_target.mem_nhds ht)] with a ha
  exact hglobal (gamma a) ha

end
end Shao.OQ3
