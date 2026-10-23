import Shao.OQ3.OpenDomainRateDerivatives
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_quadratic_tilt_boundary_coordinate_jet
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
      0 < -theta.2 ∧ ContDiffAt ℝ ∞ F (0, 0) ∧
        HasFDerivAt F ((-theta.2) • pr1) (0, 0) ∧
        (∀ u v : ℝ × ℝ,
          (fderiv ℝ (fun w => fderiv ℝ F w) (0, 0) u) v =
            (L.symm (B u)).1 * (B v).1 + (L.symm (B u)).2 * (B v).2 +
              (2 * theta.2 / level ^ 2) * u.1 * v.1) ∧
        ∀ᶠ w in 𝓝 (0, 0),
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) (G w) = (F w : EReal) := by
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
  let covector : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
    pr0.smulRight pr0 + pr1.smulRight pr1
  obtain ⟨L, e, hL, he, hs, ht, hsource, hJsmooth, hJfirst, hJsecond, hglobal⟩ :=
    open_domain_quadratic_tilt_local_rate_derivatives mu theta htheta hdet
  let J : (ℝ × ℝ) → ℝ := fun z =>
    (e.symm z).1 * z.1 + (e.symm z).2 * z.2 - K (e.symm z)
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
    (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
  let F : (ℝ × ℝ) → ℝ := fun w => J (G w)
  let Bfield : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) := fun w =>
    pr0.prod ((2 * (a0 + w.1) / level ^ 2) • pr0 - pr1)
  let T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod pr0
  have hcenter : G (0, 0) = means theta := by
    have hh : (a0, a0 ^ 2 / level ^ 2) = means theta := hmean.symm
    simpa only [G, add_zero, sub_zero] using hh
  have hsmoothJ : ContDiffAt ℝ ∞ J (means theta) := hJsmooth
  have hfirstJ : HasFDerivAt J (theta.1 • pr0 + theta.2 • pr1) (means theta) := hJfirst
  have hsecondJ : HasFDerivAt (fun z => fderiv ℝ J z)
      (covector.comp (L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) (means theta) := hJsecond
  have hG (w : ℝ × ℝ) : HasFDerivAt G (Bfield w) w := by
    have hA : HasFDerivAt (fun v : ℝ × ℝ => a0 + v.1) pr0 w := by
      convert! (pr0.hasFDerivAt.const_add a0) using 1
    have hh := hA.prodMk (((hA.mul hA).mul_const ((level ^ 2)⁻¹)).sub pr1.hasFDerivAt)
    convert hh using 1
    · funext u
      apply Prod.ext
      · rfl
      · simp [G, pr1, pow_two, div_eq_mul_inv]
    · apply ContinuousLinearMap.ext
      intro u
      apply Prod.ext <;> simp [Bfield, pr0, pr1, div_eq_mul_inv] <;> ring
  have hBzero : Bfield (0, 0) = B := by simp [Bfield, B]
  have hGzero : HasFDerivAt G B (0, 0) := by simpa only [hBzero] using hG (0, 0)
  have hGsmooth : ContDiff ℝ ∞ G := by dsimp [G]; fun_prop
  have hsmooth : ContDiffAt ℝ ∞ F (0, 0) := by
    have hh : ContDiffAt ℝ ∞ J (G (0, 0)) := by rw [hcenter]; exact hsmoothJ
    exact hh.comp (0, 0) hGsmooth.contDiffAt
  have hfirst : HasFDerivAt F ((-theta.2) • pr1) (0, 0) := by
    have hh : HasFDerivAt J (theta.1 • pr0 + theta.2 • pr1) (G (0, 0)) := by
      rw [hcenter]
      exact hfirstJ
    have hd := hh.comp (0, 0) hGzero
    have hc : (theta.1 • pr0 + theta.2 • pr1).comp B = (-theta.2) • pr1 := by
      apply ContinuousLinearMap.ext
      intro u
      change theta.1 * u.1 + theta.2 * ((2 * a0 / level ^ 2) * u.1 - u.2) = -theta.2 * u.2
      rw [hsaddle]
      ring
    rw [hc] at hd
    exact hd
  have hBeq : Bfield = fun w : ℝ × ℝ => B + ((2 / level ^ 2) * w.1) • T := by
    funext w
    apply ContinuousLinearMap.ext
    intro u
    apply Prod.ext <;> simp [Bfield, B, T, pr0, pr1] <;> ring
  have hBd : HasFDerivAt Bfield (((2 / level ^ 2) • pr0).smulRight T) (0, 0) := by
    let Q : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) :=
      ((2 / level ^ 2) • pr0).smulRight T
    have hh : HasFDerivAt (fun w : ℝ × ℝ => B + Q w) Q (0, 0) := by
      convert! Q.hasFDerivAt.const_add B using 1
    have hfun : (fun w : ℝ × ℝ => B + Q w) = Bfield := by
      rw [hBeq]
      rfl
    rw [hfun] at hh
    exact hh
  have hJpath : HasFDerivAt (fun w => fderiv ℝ J (G w))
      ((covector.comp (L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))).comp B) (0, 0) := by
    have hh : HasFDerivAt (fun z => fderiv ℝ J z)
        (covector.comp (L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) (G (0, 0)) := by
      rw [hcenter]
      exact hsecondJ
    exact hh.comp (0, 0) hGzero
  have hComp := hJpath.clm_comp hBd
  have hfinite : ContDiffAt ℝ (1 : WithTop ENat) J (means theta) := hsmoothJ.of_le (by simp)
  have hnear : ∀ᶠ z in 𝓝 (means theta), DifferentiableAt ℝ J z :=
    (hfinite.eventually (by norm_num)).mono (fun _ hz => hz.differentiableAt (by norm_num))
  have htend : Filter.Tendsto G (𝓝 (0, 0)) (𝓝 (means theta)) := by
    rw [← hcenter]
    exact hGsmooth.continuous.continuousAt
  have heq : (fun w => fderiv ℝ F w) =ᶠ[𝓝 (0, 0)]
      (fun w => (fderiv ℝ J (G w)).comp (Bfield w)) := by
    filter_upwards [htend.eventually hnear] with w hw
    exact (hw.hasFDerivAt.comp w (hG w)).fderiv
  have hsecond := heq.hasFDerivAt_iff.mpr hComp
  refine ⟨L, e, hL, he, hs, ht, hsource, neg_pos.mpr hnegative, hsmooth, hfirst, ?_, ?_⟩
  · intro u v
    rw [hsecond.fderiv]
    change (fderiv ℝ J (G (0, 0))) ((((2 / level ^ 2) • pr0).smulRight T u) v) +
      (covector (L.symm (B u))) (Bfield (0, 0) v) = _
    rw [hcenter, hfirstJ.fderiv, hBzero]
    simp [B, covector, T, pr0, pr1, ContinuousLinearMap.smulRight_apply] <;> ring
  · filter_upwards [htend.eventually (e.open_target.mem_nhds ht)] with w hw
    exact hglobal (G w) hw

end
end Shao.OQ3
