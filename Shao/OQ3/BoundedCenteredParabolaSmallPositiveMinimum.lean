import Shao.OQ3.BoundedParabolaTailGlobalMinimum
import Shao.OQ3.OpenDomainLegendre

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem bounded_centered_parabola_small_positive_global_minimum
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (lower upper : ℝ) (hlower : 0 < lower)
    (henergy : ∀ᵐ x ∂mu, lower ≤ x ^ 2 ∧ x ^ 2 ≤ upper)
    (hmean : (∫ x : ℝ, x ∂mu) = 0) (hdet : (parabolaCovariance mu).det ≠ 0) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      ∀ level : ℝ, 0 < level → level < epsilon → ∃ z : ℝ × ℝ,
        0 < z.2 ∧ level * Real.sqrt z.2 ≤ z.1 ∧
          0 ≤ Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z ∧
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z < ⊤ ∧
          ∀ y : ℝ × ℝ, 0 < y.2 → level * Real.sqrt y.2 ≤ y.1 →
            Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z ≤
              Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y := by
  let q : ℝ := ∫ x : ℝ, x ^ 2 ∂mu
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
  have htheta0 : ((0 : ℝ), (0 : ℝ)) ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) := by
    rw [hdomain, interior_univ]
    exact Set.mem_univ _
  have htilt0 : mu.tilted (fun x => (0 : ℝ) * x + 0 * x ^ 2) = mu := by
    simpa only [zero_mul, add_zero] using (tilted_const mu 0)
  have hdet0 : (parabolaCovariance
      (mu.tilted (fun x => (0 : ℝ) * x + 0 * x ^ 2))).det ≠ 0 := by
    simpa only [htilt0] using hdet
  obtain ⟨e, r, hr, _he, _hs, _hsub, _htarget, hrest⟩ :=
    open_domain_quadratic_tilt_compact_legendre_chart mu (0, 0) htheta0 hdet0
  let epsilon : ℝ := min 1 (r / (Real.sqrt q + 1))
  have hepsilon : 0 < epsilon := lt_min (by norm_num) (div_pos hr (by positivity))
  refine ⟨epsilon, hepsilon, min_le_left _ _, ?_⟩
  intro level hlevel hsmall
  have hlevelBound : level * (Real.sqrt q + 1) < r :=
    (lt_div_iff₀ (by positivity : 0 < Real.sqrt q + 1)).mp
      (hsmall.trans_le (min_le_right _ _))
  have hsmallq : level * Real.sqrt q < r := by nlinarith only [hlevelBound, hlevel]
  let w : ℝ × ℝ := (level * Real.sqrt q, q)
  have hw : w ∈ Metric.closedBall ((0 : ℝ), q) r := by
    apply Metric.mem_closedBall.mpr
    change dist (level * Real.sqrt q, q) (0, q) ≤ r
    simpa only [Prod.dist_eq, Real.dist_eq, sub_zero, sub_self, abs_zero,
      abs_of_nonneg (mul_nonneg hlevel.le (Real.sqrt_nonneg q)),
      max_eq_left (mul_nonneg hlevel.le (Real.sqrt_nonneg q))] using hsmallq.le
  have hrw := (hrest.2.2.2 w (by simpa only [htilt0, hmean] using hw)).2.2
  let L : ℝ := (e.symm w).1 * w.1 + (e.symm w).2 * w.2 - Real.log
    (∫ x : ℝ, Real.exp ((e.symm w).1 * x + (e.symm w).2 * x ^ 2) ∂mu)
  have hwfinite : Shao.Probability.bivariateLegendreRate mu
      (fun x : ℝ => (x, x ^ 2)) w ≤ (L : EReal) := by
    simpa only [L] using hrw.le
  obtain ⟨z, hzq, hzcone, hzbound, hmin⟩ :=
    bounded_parabola_tail_global_minimum_of_finite_test mu M hM hb lower upper hlower
      henergy level L w (le_refl _) hwfinite
  have hnonneg : 0 ≤ Shao.Probability.bivariateLegendreRate mu
      (fun x : ℝ => (x, x ^ 2)) z := by
    have ht := Shao.Probability.bivariateLegendreRate_test_le mu
      (fun x : ℝ => (x, x ^ 2)) z ⟨(0, 0), by rw [hdomain]; exact Set.mem_univ _⟩
    simpa [Shao.Probability.bivariateLogMGF] using ht
  exact ⟨z, hzq, hzcone, hnonneg, lt_of_le_of_lt hzbound (EReal.coe_lt_top L), hmin⟩

end
end Shao.OQ3
