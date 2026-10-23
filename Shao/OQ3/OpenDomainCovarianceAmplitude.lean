import Shao.OQ3.OpenDomainMeanInverse
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_quadratic_covariance_det_contDiffOn
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ =>
        (parabolaCovariance (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))).det)
      (interior (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
 := by
  let Omega : Set (ℝ × ℝ) := interior
    (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
  let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
    mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
    (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
  let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (nu p)
  let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  let Q : (ℝ × ℝ) → ℝ := fun p =>
    ((fderiv ℝ means p) (1, 0)).1 * ((fderiv ℝ means p) (0, 1)).2 -
      ((fderiv ℝ means p) (0, 1)).1 * ((fderiv ℝ means p) (1, 0)).2
  obtain ⟨_, _, hmeans, hstrict⟩ := open_domain_quadratic_tilt_smooth_and_strict mu
  have hm : ContDiffOn ℝ ∞ means Omega := hmeans
  have hd (p : ℝ × ℝ) (hp : p ∈ Omega) :
      fderiv ℝ means p =
        (D p 0 0 • pr0 + D p 0 1 • pr1).prod (D p 0 1 • pr0 + D p 1 1 • pr1) := by
    have hh : HasStrictFDerivAt means
        ((D p 0 0 • pr0 + D p 0 1 • pr1).prod (D p 0 1 • pr0 + D p 1 1 • pr1)) p :=
      hstrict p hp
    exact hh.hasFDerivAt.fderiv
  have heq (p : ℝ × ℝ) (hp : p ∈ Omega) : (D p).det = Q p := by
    have h10 : D p 1 0 = D p 0 1 := rfl
    dsimp only [Q]
    rw [hd p hp, Matrix.det_fin_two, h10]
    simp [pr0, pr1]
  intro p hp
  have hpO : p ∈ Omega := hp
  have hma : ContDiffAt ℝ ∞ means p :=
    (hm p hpO).contDiffAt (isOpen_interior.mem_nhds hpO)
  have hdf : ContDiffAt ℝ ∞ (fun q => fderiv ℝ means q) p :=
    hma.fderiv_right (by simp)
  have h0 : ContDiffAt ℝ ∞ (fun q => (fderiv ℝ means q) (1, 0)) p :=
    hdf.clm_apply contDiffAt_const
  have h1 : ContDiffAt ℝ ∞ (fun q => (fderiv ℝ means q) (0, 1)) p :=
    hdf.clm_apply contDiffAt_const
  have hQ : ContDiffAt ℝ ∞ Q p := (h0.fst.mul h1.snd).sub (h1.fst.mul h0.snd)
  have hlocal : (fun q => (D q).det) =ᶠ[𝓝 p] Q := by
    filter_upwards [isOpen_interior.mem_nhds hpO] with q hq
    exact heq q hq
  exact (hQ.congr_of_eventuallyEq hlocal).contDiffWithinAt

theorem open_domain_chart_covariance_amplitude
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (level a0 : ℝ) (hlevel : 0 < level) (ha0 : 0 < a0)
    (hmean : (∫ x : ℝ, x ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2),
      ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) =
        (a0, a0 ^ 2 / level ^ 2))
    (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (he : (e : (ℝ × ℝ) → (ℝ × ℝ)) = fun p =>
      (∫ x : ℝ, x ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2),
        ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)))
    (hsource : theta ∈ e.source)
    (hpositive : 0 < (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det) :
    let Omega : Set (ℝ × ℝ) := interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
      (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
    let P : (ℝ × ℝ) → (ℝ × ℝ) := fun w => e.symm (G w)
    let detF : (ℝ × ℝ) → ℝ := fun w =>
      (parabolaCovariance
        (mu.tilted (fun x => (P w).1 * x + (P w).2 * x ^ 2))).det
    let A : (ℝ × ℝ) → ℝ := fun w => (Real.sqrt (detF w))⁻¹
    P (0, 0) = theta ∧ ContDiffAt ℝ ∞ P (0, 0) ∧
      ContDiffAt ℝ ∞ A (0, 0) ∧
      A (0, 0) = (Real.sqrt (parabolaCovariance
        (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det)⁻¹ ∧
      ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧ ∀ r z : ℝ,
        |r| ≤ rho → 0 ≤ z → z ≤ rho →
        P (r, z) ∈ Omega ∧ 0 < detF (r, z) ∧
          |A (r, z) - A (0, 0)| ≤ C * (|r| + z)
 := by
  let Omega : Set (ℝ × ℝ) := interior
    (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
  let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
    mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
    (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
  let detParam : (ℝ × ℝ) → ℝ := fun p => (parabolaCovariance (nu p)).det
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
    (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
  let P : (ℝ × ℝ) → (ℝ × ℝ) := fun w => e.symm (G w)
  let detF : (ℝ × ℝ) → ℝ := fun w => detParam (P w)
  let A : (ℝ × ℝ) → ℝ := fun w => (Real.sqrt (detF w))⁻¹
  have hemeans : (e : (ℝ × ℝ) → (ℝ × ℝ)) = means := he
  have hcenter : e.symm (means theta) = theta := by
    rw [← hemeans]
    exact e.left_inv hsource
  have ht : means theta ∈ e.target := by
    rw [← hemeans]
    exact e.map_source hsource
  obtain ⟨L, _, hL, _, _, _, _, _, _⟩ :=
    open_domain_quadratic_tilt_local_mean_inverse mu theta htheta hpositive.ne'
  obtain ⟨_, _, hmeans, hstrict⟩ := open_domain_quadratic_tilt_smooth_and_strict mu
  have hma : ContDiffAt ℝ ∞ means theta :=
    (hmeans theta htheta).contDiffAt (isOpen_interior.mem_nhds htheta)
  have hd : HasFDerivAt means (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) theta := by
    rw [hL]
    exact (hstrict theta htheta).hasFDerivAt
  have hi : ContDiffAt ℝ ∞ (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) (means theta) := by
    apply e.contDiffAt_symm (f₀' := L) ht
    · rw [hcenter, hemeans]
      exact hd
    · rw [hcenter, hemeans]
      exact hma
  have hGcenter : G (0, 0) = means theta := by
    have hh : (a0, a0 ^ 2 / level ^ 2) = means theta := hmean.symm
    simpa only [G, add_zero, sub_zero] using hh
  have hPcenter : P (0, 0) = theta := by dsimp [P]; rw [hGcenter, hcenter]
  have hG : ContDiff ℝ ∞ G := by dsimp [G]; fun_prop
  have hP : ContDiffAt ℝ ∞ P (0, 0) := by
    have hh : ContDiffAt ℝ ∞ (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) (G (0, 0)) := by
      rw [hGcenter]
      exact hi
    exact hh.comp (f := G) (0, 0) hG.contDiffAt
  have hdetAt : ContDiffAt ℝ ∞ detParam theta :=
    ((open_domain_quadratic_covariance_det_contDiffOn mu) theta htheta).contDiffAt
      (isOpen_interior.mem_nhds htheta)
  have hdetF : ContDiffAt ℝ ∞ detF (0, 0) := by
    have hh : ContDiffAt ℝ ∞ detParam (P (0, 0)) := by rw [hPcenter]; exact hdetAt
    exact hh.comp (f := P) (0, 0) hP
  have hdet0 : 0 < detF (0, 0) := by change 0 < detParam (P (0, 0)); rw [hPcenter]; exact hpositive
  have hA : ContDiffAt ℝ ∞ A (0, 0) :=
    (hdetF.sqrt hdet0.ne').inv (Real.sqrt_pos.mpr hdet0).ne'
  have hAcenter : A (0, 0) = (Real.sqrt (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det)⁻¹ := by
    dsimp only [A, detF]
    rw [hPcenter]
  obtain ⟨C, hC, hbound⟩ := (hA.differentiableAt (by simp)).isBigO_sub.exists_pos
  have htend : Filter.Tendsto P (𝓝 (0, 0)) (𝓝 theta) := by
    rw [← hPcenter]
    exact hP.continuousAt
  have hdom : ∀ᶠ w in 𝓝 (0, 0), P w ∈ Omega :=
    htend.eventually (isOpen_interior.mem_nhds htheta)
  have hpos : ∀ᶠ w in 𝓝 (0, 0), 0 < detF w :=
    hdetF.continuousAt.eventually (lt_mem_nhds hdet0)
  have hnear : ∀ᶠ w in 𝓝 (0, 0),
      P w ∈ Omega ∧ 0 < detF w ∧ |A w - A (0, 0)| ≤ C * ‖w‖ := by
    filter_upwards [hdom, hpos, hbound.bound] with w hw hp hb
    exact ⟨hw, hp, by simpa only [show (0, 0) = (0 : ℝ × ℝ) from rfl,
      sub_zero, Real.norm_eq_abs] using hb⟩
  obtain ⟨delta, hdelta, hpoint⟩ := Metric.eventually_nhds_iff.mp hnear
  let rho : ℝ := delta / 2
  refine ⟨hPcenter, hP, hA, hAcenter, rho, C, by dsimp [rho]; linarith, hC, ?_⟩
  intro r z hr hz hzr
  have hinside : dist (r, z) (0, 0) < delta := by
    rw [show (0, 0) = (0 : ℝ × ℝ) from rfl, dist_zero_right, Prod.norm_def,
      Real.norm_eq_abs, Real.norm_eq_abs, max_lt_iff]
    dsimp [rho] at hr hzr
    constructor
    · linarith
    · rw [abs_of_nonneg hz]; linarith
  have hh := hpoint hinside
  have hn : ‖(r, z)‖ ≤ |r| + z := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hz]
    exact max_le (by linarith) (by linarith [abs_nonneg r])
  exact ⟨hh.1, hh.2.1, hh.2.2.trans (mul_le_mul_of_nonneg_left hn hC.le)⟩

end
end Shao.OQ3
