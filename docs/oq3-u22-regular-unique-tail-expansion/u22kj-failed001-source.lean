import Shao.OQ3.ParabolaEnergyCurvatureNeighborhood
import Shao.OQ3.ActualMeanChartRateDerivatives
import Shao.OQ3.BoundedParabolaRectangleSeparation

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem bounded_centered_parabola_uniform_energy_curvature
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (lower upper : ℝ) (hlower : 0 < lower)
    (henergy : ∀ᵐ x ∂mu, lower ≤ x ^ 2 ∧ x ^ 2 ≤ upper)
    (hmean : (∫ x : ℝ, x ∂mu) = 0) (hdet : 0 < (parabolaCovariance mu).det) :
    ∃ (F : (ℝ × ℝ) → ℝ) (eta rho : ℝ),
      0 < eta ∧ 0 < rho ∧ rho < (∫ x : ℝ, x ^ 2 ∂mu) ∧ ∀ level q : ℝ,
        |level| ≤ eta → |q - (∫ x : ℝ, x ^ 2 ∂mu)| ≤ rho →
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
            (level * Real.sqrt q, q) = (F (level, q) : EReal) ∧
          ContDiffAt ℝ (2 : WithTop ENat) (fun energy : ℝ => F (level, energy)) q ∧
            0 < deriv (deriv (fun energy : ℝ => F (level, energy))) q := by
  let q0 : ℝ := ∫ x : ℝ, x ^ 2 ∂mu
  have hsqbound : ∀ᵐ x ∂mu, |x ^ 2| ≤ M ^ 2 := hb.mono fun x hx => by
    simpa only [abs_pow, sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hsqi : Integrable (fun x : ℝ => x ^ 2) mu :=
    Integrable.of_bound (by fun_prop) (M ^ 2) hsqbound
  have hqLower : lower ≤ q0 := by
    have hi := integral_mono_ae (integrable_const lower) hsqi
      (henergy.mono fun _ hx => hx.1)
    simpa [q0] using hi
  have hq0 : 0 < q0 := hlower.trans_le hqLower
  have hdomain := (bounded_parabola_rectangle_exponential_separation mu M hM hb
    lower upper henergy).1
  have htheta0 : ((0 : ℝ), (0 : ℝ)) ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) := by
    rw [hdomain, interior_univ]
    exact Set.mem_univ _
  have htilt0 : mu.tilted (fun x => (0 : ℝ) * x + 0 * x ^ 2) = mu := by
    simpa only [zero_mul, add_zero] using (tilted_const mu 0)
  have hdet0 : 0 < (parabolaCovariance
      (mu.tilted (fun x => (0 : ℝ) * x + 0 * x ^ 2))).det := by
    simpa only [htilt0] using hdet
  obtain ⟨e, R, hR, he, hs, hsource, hclosed, hrest⟩ :=
    open_domain_quadratic_tilt_compact_legendre_chart mu (0, 0) htheta0 hdet0.ne'
  have he0 : e ((0 : ℝ), (0 : ℝ)) = (0, q0) := by
    rw [he]
    simp only [htilt0, hmean]
  have hinv : e.symm ((0 : ℝ), q0) = (0, 0) := by
    rw [← he0]
    exact e.left_inv hs
  have hw : ((0 : ℝ), q0) ∈ e.target := by
    apply hclosed
    simpa only [htilt0, hmean] using (Metric.mem_closedBall_self hR.le :
      ((0 : ℝ), q0) ∈ Metric.closedBall ((0 : ℝ), q0) R)
  have hdetw : 0 < (parabolaCovariance
      (mu.tilted (fun x => (e.symm ((0 : ℝ), q0)).1 * x +
        (e.symm ((0 : ℝ), q0)).2 * x ^ 2))).det := by
    simpa only [hinv, htilt0] using hdet
  let K : (ℝ × ℝ) → ℝ := fun p => Real.log
    (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
  let J : (ℝ × ℝ) → ℝ := fun z =>
    (e.symm z).1 * z.1 + (e.symm z).2 * z.2 - K (e.symm z)
  obtain ⟨L, _hL, _hi, _hdi, hJ, _hg, _hH, hquad, _hA, _hI⟩ :=
    actual_mean_chart_rate_covariance_derivatives mu e he hsource (0, q0) hw hdetw
  change ContDiffAt ℝ ∞ J (0, q0) at hJ
  have hD00 : parabolaCovariance mu 0 0 = q0 := by
    change ProbabilityTheory.variance (fun x : ℝ => x) mu = q0
    rw [ProbabilityTheory.variance_eq_integral measurable_id.aemeasurable]
    simp only [hmean, sub_zero]
  have hcurvature : 0 <
      (fderiv ℝ (fun z => fderiv ℝ J z) (0, q0) (0, 1)) (0, 1) := by
    have henergyHessian :
        (fderiv ℝ (fun z => fderiv ℝ J z) (0, q0) (0, 1)) (0, 1) =
          q0 / (parabolaCovariance mu).det := by
      simpa [hinv, htilt0, hD00] using hquad ((0 : ℝ), 1)
    rw [henergyHessian]
    exact div_pos hq0 hdet
  obtain ⟨eta, rho, heta, hrho, hrhoq, hrect⟩ :=
    parabola_energy_positive_curvature_neighborhood J q0 hq0
      (hJ.of_le (by simp)) hcurvature
  have hvalue (z : ℝ × ℝ) (hz : z ∈ Metric.closedBall ((0 : ℝ), q0) R) :
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z =
        (J z : EReal) := by
    exact (hrest.2.2.2 z (by simpa only [htilt0, hmean] using hz)).2.2
  have hmap : Filter.Tendsto
      (fun p : ℝ × ℝ => (p.1 * Real.sqrt p.2, p.2))
      (𝓝 ((0 : ℝ), q0)) (𝓝 ((0 : ℝ), q0)) := by
    simpa only [zero_mul] using (show ContinuousAt
      (fun p : ℝ × ℝ => (p.1 * Real.sqrt p.2, p.2)) ((0 : ℝ), q0) from by fun_prop)
  have hnear : ∀ᶠ p in 𝓝 ((0 : ℝ), q0),
      (p.1 * Real.sqrt p.2, p.2) ∈ Metric.closedBall ((0 : ℝ), q0) R :=
    hmap.eventually (Metric.closedBall_mem_nhds _ hR)
  obtain ⟨d, hd, hpoint⟩ := Metric.eventually_nhds_iff.mp hnear
  let F : (ℝ × ℝ) → ℝ := fun p => J (p.1 * Real.sqrt p.2, p.2)
  refine ⟨F, min eta (d / 2), min rho (d / 2),
    lt_min heta (half_pos hd), lt_min hrho (half_pos hd),
    (min_le_left _ _).trans_lt hrhoq, ?_⟩
  intro level q hlevel hq
  have hdist : dist (level, q) ((0 : ℝ), q0) < d := by
    rw [Prod.dist_eq, max_lt_iff]
    constructor
    · simpa only [Real.dist_eq, sub_zero] using
        hlevel.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hd))
    · simpa only [Real.dist_eq] using
        hq.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hd))
  have hcurv := hrect level q (hlevel.trans (min_le_left _ _))
    (hq.trans (min_le_left _ _))
  exact ⟨hvalue _ (hpoint hdist), hcurv.1, hcurv.2⟩

end
end Shao.OQ3
