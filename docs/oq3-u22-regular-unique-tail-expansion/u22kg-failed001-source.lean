import Shao.OQ3.BoundedCenteredParabolaMinimumLocalization
import Shao.OQ3.BoundedCenteredParabolaMinimumBoundary
import Shao.OQ3.BoundedCenteredParabolaBoundaryTiltSign
import Shao.OQ3.OpenDomainCovarianceAmplitude

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem bounded_centered_parabola_small_positive_global_boundary_tilt
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (lower upper : ℝ) (hlower : 0 < lower)
    (henergy : ∀ᵐ x ∂mu, lower ≤ x ^ 2 ∧ x ^ 2 ≤ upper)
    (hmean : (∫ x : ℝ, x ∂mu) = 0) (hdet : 0 < (parabolaCovariance mu).det) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      ∀ level : ℝ, 0 < level → level < epsilon → ∃ (a0 : ℝ) (theta : ℝ × ℝ),
        0 < a0 ∧ theta ∈ interior
          (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) ∧
        (∫ x : ℝ, x ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2),
          ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) =
            (a0, a0 ^ 2 / level ^ 2) ∧
        0 < (parabolaCovariance
          (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det ∧
        theta.1 = -2 * a0 * theta.2 / level ^ 2 ∧ 0 < theta.1 ∧ theta.2 < 0 ∧
        0 < Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
          (a0, a0 ^ 2 / level ^ 2) ∧
        Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
          (a0, a0 ^ 2 / level ^ 2) < ⊤ ∧
        ∀ y : ℝ × ℝ, 0 < y.2 → level * Real.sqrt y.2 ≤ y.1 →
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
              (a0, a0 ^ 2 / level ^ 2) ≤
            Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y := by
  let m : ℝ × ℝ := (0, ∫ x : ℝ, x ^ 2 ∂mu)
  let detTilt : (ℝ × ℝ) → ℝ := fun p =>
    (parabolaCovariance (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))).det
  have hdomain := (bounded_parabola_rectangle_exponential_separation mu M hM hb
    lower upper henergy).1
  have hzero : ((0 : ℝ), (0 : ℝ)) ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) := by
    rw [hdomain, interior_univ]
    exact Set.mem_univ _
  have htilt0 : mu.tilted (fun x => (0 : ℝ) * x + 0 * x ^ 2) = mu := by
    simpa only [zero_mul, add_zero] using (tilted_const mu 0)
  have hdet0 : 0 < detTilt (0, 0) := by simpa only [detTilt, htilt0] using hdet
  obtain ⟨e, R, hR, he, hs, hsource, hball, _hrest⟩ :=
    open_domain_quadratic_tilt_compact_legendre_chart mu (0, 0) hzero hdet0.ne'
  have he0 : e (0, 0) = m := by
    simpa only [htilt0, hmean, m] using congrFun he (0, 0)
  have hsymm : e.symm m = (0, 0) := by
    rw [← he0]
    exact e.left_inv hs
  have hball' : Metric.closedBall m R ⊆ e.target := by
    simpa only [htilt0, hmean, m] using hball
  have hmTarget : m ∈ e.target := hball' (Metric.mem_closedBall_self hR.le)
  have hcont : ContinuousAt (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) m :=
    e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hmTarget)
  have hDet0 : ContinuousAt detTilt (0, 0) :=
    (((open_domain_quadratic_covariance_det_contDiffOn mu) (0, 0) hzero).contDiffAt
      (isOpen_interior.mem_nhds hzero)).continuousAt
  have hDetMean : ContinuousAt detTilt (e.symm m) := by rw [hsymm]; exact hDet0
  have hcomp : ContinuousAt (fun z => detTilt (e.symm z)) m := hDetMean.comp hcont
  have hpositive : 0 < detTilt (e.symm m) := by simpa only [hsymm] using hdet0
  have hnear : {z : ℝ × ℝ | z ∈ e.target ∧ 0 < detTilt (e.symm z)} ∈ 𝓝 m :=
    (e.open_target.mem_nhds hmTarget).inter (hcomp (lt_mem_nhds hpositive))
  obtain ⟨rho, hrho, hinside⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨epsilon, hepsilon, hepsilon1, hsmall⟩ :=
    bounded_centered_parabola_global_minima_localize mu M hM hb lower upper hlower
      henergy hmean hdet.ne' rho hrho
  refine ⟨epsilon, hepsilon, hepsilon1, ?_⟩
  intro level hlevel hlevelSmall
  obtain ⟨z, hzq, hzcone, hzpos, hzfinite, hzglobal, hzloc⟩ :=
    hsmall level hlevel hlevelSmall
  have hzball : z ∈ Metric.ball m rho := Metric.mem_ball.mpr (hzloc z (le_refl _))
  have hzinside := hinside hzball
  let theta : ℝ × ℝ := e.symm z
  let a0 : ℝ := z.1
  have htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) :=
    hsource (e.map_target hzinside.1)
  have hcov : 0 < (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det := hzinside.2
  have hactualMean :
      (∫ x : ℝ, x ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2),
        ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) = z :=
    (congrFun he theta).symm.trans (e.right_inv hzinside.1)
  have ha0 : 0 < a0 := (mul_pos hlevel (Real.sqrt_pos.2 hzq)).trans_le hzcone
  have hboundary := bounded_centered_parabola_global_minimum_on_boundary mu M hM hb hmean
    level hlevel z hzq hzcone hzfinite hzglobal
  have hz2 : z.2 = a0 ^ 2 / level ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hlevel.ne')).mpr
    have hsq := congrArg (fun a : ℝ => a ^ 2) hboundary
    rw [mul_pow, Real.sq_sqrt hzq.le] at hsq
    change z.2 * level ^ 2 = z.1 ^ 2
    nlinarith only [hsq]
  have hpoint : z = (a0, a0 ^ 2 / level ^ 2) := Prod.ext rfl hz2
  have hmeanPoint := hactualMean.trans hpoint
  have hglobalPoint : ∀ y : ℝ × ℝ, 0 < y.2 → level * Real.sqrt y.2 ≤ y.1 →
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
          (a0, a0 ^ 2 / level ^ 2) ≤
        Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y := by
    intro y hyq hycone
    rw [← hpoint]
    exact hzglobal y hyq hycone
  obtain ⟨hsaddle, hfirst, hnegative⟩ := bounded_centered_parabola_global_boundary_tilt_sign
    mu M hM hb hmean theta htheta hcov.ne' level a0 hlevel ha0 hmeanPoint hglobalPoint
  refine ⟨a0, theta, ha0, htheta, hmeanPoint, hcov, hsaddle, hfirst, hnegative, ?_, ?_, hglobalPoint⟩
  · rw [← hpoint]
    exact hzpos
  · rw [← hpoint]
    exact hzfinite

end
end Shao.OQ3
