import Shao.OQ3.BoundedParabolaMeanRateGap
import Shao.OQ3.BoundedParabolaTailGlobalMinimum
import Shao.OQ3.OpenDomainLegendre

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem bounded_centered_parabola_global_minima_localize
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (lower upper : ℝ) (hlower : 0 < lower)
    (henergy : ∀ᵐ x ∂mu, lower ≤ x ^ 2 ∧ x ^ 2 ≤ upper)
    (hmean : (∫ x : ℝ, x ∂mu) = 0) (hdet : (parabolaCovariance mu).det ≠ 0)
    (r : ℝ) (hr : 0 < r) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      ∀ level : ℝ, 0 < level → level < epsilon → ∃ z : ℝ × ℝ,
        0 < z.2 ∧ level * Real.sqrt z.2 ≤ z.1 ∧
          0 < Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z ∧
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z < ⊤ ∧
          (∀ y : ℝ × ℝ, 0 < y.2 → level * Real.sqrt y.2 ≤ y.1 →
            Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z ≤
              Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y) ∧
          ∀ y : ℝ × ℝ,
            Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y ≤
              Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z →
            dist y (0, ∫ x : ℝ, x ^ 2 ∂mu) < r := by
  let q : ℝ := ∫ x : ℝ, x ^ 2 ∂mu
  let m : ℝ × ℝ := (0, q)
  let K : (ℝ × ℝ) → ℝ := fun p =>
    Real.log (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
  let I : (ℝ × ℝ) → EReal :=
    Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
  have hsqbound : ∀ᵐ x ∂mu, |x ^ 2| ≤ M ^ 2 := hb.mono fun x hx => by
    simpa only [abs_pow, sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hsqi : Integrable (fun x : ℝ => x ^ 2) mu :=
    Integrable.of_bound (by fun_prop) (M ^ 2) hsqbound
  have hqLower : lower ≤ q := by
    have hi := integral_mono_ae (integrable_const lower) hsqi
      (henergy.mono fun _ hx => hx.1)
    simpa [q] using hi
  have hq : 0 < q := hlower.trans_le hqLower
  have hdomain := (bounded_parabola_rectangle_exponential_separation mu M hM hb
    lower upper henergy).1
  have hzero : ((0 : ℝ), (0 : ℝ)) ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) := by
    rw [hdomain, interior_univ]
    exact Set.mem_univ _
  have htilt0 : mu.tilted (fun x => (0 : ℝ) * x + 0 * x ^ 2) = mu := by
    simpa only [zero_mul, add_zero] using (tilted_const mu 0)
  have hdet0 : (parabolaCovariance
      (mu.tilted (fun x => (0 : ℝ) * x + 0 * x ^ 2))).det ≠ 0 := by
    simpa only [htilt0] using hdet
  obtain ⟨e, R, hR, he, hs, _hsub, hball, hrest⟩ :=
    open_domain_quadratic_tilt_compact_legendre_chart mu (0, 0) hzero hdet0
  have he0 : e (0, 0) = m := by
    simpa only [htilt0, hmean, m, q] using congrFun he (0, 0)
  have hsymm : e.symm m = (0, 0) := by
    rw [← he0]
    exact e.left_inv hs
  have hball' : Metric.closedBall m R ⊆ e.target := by
    simpa only [htilt0, hmean, m, q] using hball
  have hmTarget : m ∈ e.target := hball' (Metric.mem_closedBall_self hR.le)
  have hcont : ContinuousAt (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) m :=
    e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hmTarget)
  have hK0 : ContinuousAt K (0, 0) := by
    simpa only [K] using
      (open_domain_quadratic_tilt_frechet_cumulants mu (0, 0) hzero).2.2.2.2.1.continuousAt
  let L : (ℝ × ℝ) → ℝ := fun z =>
    (e.symm z).1 * z.1 + (e.symm z).2 * z.2 - K (e.symm z)
  have hKsymm : ContinuousAt K (e.symm m) := by rw [hsymm]; exact hK0
  have hL : ContinuousAt L m :=
    ((hcont.fst.mul continuousAt_fst).add (hcont.snd.mul continuousAt_snd)).sub
      (hKsymm.comp m hcont)
  have hL0 : L m = 0 := by simp [L, hsymm, K]
  obtain ⟨delta, hdelta, hloc⟩ := bounded_parabola_low_rate_localization mu M hM hb r hr
  have hnear : {z : ℝ × ℝ | L z < delta} ∈ 𝓝 m :=
    hL (gt_mem_nhds (by simpa only [hL0] using hdelta))
  obtain ⟨rho, hrho, hsubrho⟩ := Metric.mem_nhds_iff.mp hnear
  let epsilon : ℝ := min 1 (min R rho / (Real.sqrt q + 1))
  have hepsilon : 0 < epsilon :=
    lt_min zero_lt_one (div_pos (lt_min hR hrho) (by positivity))
  refine ⟨epsilon, hepsilon, min_le_left _ _, ?_⟩
  intro level hlevel hsmall
  have hlevelBound : level * (Real.sqrt q + 1) < min R rho :=
    (lt_div_iff₀ (by positivity : 0 < Real.sqrt q + 1)).mp
      (hsmall.trans_le (min_le_right _ _))
  have hsmallq : level * Real.sqrt q < min R rho := by
    nlinarith only [hlevelBound, hlevel]
  let w : ℝ × ℝ := (level * Real.sqrt q, q)
  have hdist : dist w m = level * Real.sqrt q := by
    dsimp only [w, m]
    simp only [Prod.dist_eq, Real.dist_eq, sub_zero, sub_self, abs_zero,
      abs_of_nonneg (mul_nonneg hlevel.le (Real.sqrt_nonneg q)),
      max_eq_left (mul_nonneg hlevel.le (Real.sqrt_nonneg q))]
  have hw : w ∈ Metric.closedBall m R := by
    apply Metric.mem_closedBall.mpr
    rw [hdist]
    exact (hsmallq.trans_le (min_le_left _ _)).le
  have hLw : L w < delta := hsubrho (Metric.mem_ball.mpr (by
    rw [hdist]
    exact hsmallq.trans_le (min_le_right _ _)))
  have hwvalue := (hrest.2.2.2 w (by
    simpa only [htilt0, hmean, m, q] using hw)).2.2
  change I w = ((L w : ℝ) : EReal) at hwvalue
  have hwfinite : I w ≤ (delta : EReal) := by
    rw [hwvalue]
    exact (EReal.coe_lt_coe_iff.mpr hLw).le
  obtain ⟨z, hzq, hzcone, hzbound, hglobal⟩ :=
    bounded_parabola_tail_global_minimum_of_finite_test mu M hM hb lower upper hlower
      henergy level delta w (le_refl _) hwfinite
  have hzpos := bounded_centered_parabola_positive_tail_rate mu M hM hb hmean
    level hlevel z hzq hzcone
  refine ⟨z, hzq, hzcone, hzpos, lt_of_le_of_lt hzbound (EReal.coe_lt_top delta), hglobal, ?_⟩
  intro y hy
  simpa only [hmean] using hloc y (hy.trans hzbound)

end
end Shao.OQ3
