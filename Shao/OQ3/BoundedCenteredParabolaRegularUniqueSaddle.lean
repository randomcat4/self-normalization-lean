import Shao.OQ3.ScaledTangentCurvatureNeighborhood
import Shao.OQ3.BoundedCenteredParabolaUniqueMinimum
import Shao.OQ3.BoundedCenteredParabolaBoundaryTiltSign
import Shao.OQ3.ActualMeanChartRateDerivatives
import Shao.OQ3.BoundedParabolaRectangleSeparation

namespace Shao.OQ3
open MeasureTheory
open scoped Topology ContDiff
noncomputable section

theorem bounded_centered_parabola_small_positive_regular_unique_saddle
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (lower upper : ℝ) (hlower : 0 < lower)
    (henergy : ∀ᵐ x ∂mu, lower ≤ x ^ 2 ∧ x ^ 2 ≤ upper)
    (hmean : (∫ x : ℝ, x ∂mu) = 0) (hdet : 0 < (parabolaCovariance mu).det) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      ∀ level : ℝ, 0 < level → level < epsilon →
        ∃ (a0 : ℝ) (theta : ℝ × ℝ) (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)),
          let D := parabolaCovariance
            (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))
          0 < a0 ∧ theta ∈ interior
            (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) ∧
          0 < D.det ∧
          (∫ x : ℝ, x ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2),
            ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) =
              (a0, a0 ^ 2 / level ^ 2) ∧
          theta.1 = -2 * a0 * theta.2 / level ^ 2 ∧ 0 < theta.1 ∧ theta.2 < 0 ∧
          (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) =
            (D 0 0 • ContinuousLinearMap.fst ℝ ℝ ℝ +
              D 0 1 • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
            (D 0 1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
              D 1 1 • ContinuousLinearMap.snd ℝ ℝ ℝ) ∧
          0 < 2 * theta.2 / level ^ 2 +
            (L.symm (1, 2 * a0 / level ^ 2)).1 +
              (2 * a0 / level ^ 2) * (L.symm (1, 2 * a0 / level ^ 2)).2 ∧
          0 < Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
            (a0, a0 ^ 2 / level ^ 2) ∧
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
            (a0, a0 ^ 2 / level ^ 2) < ⊤ ∧
          (∀ y : ℝ × ℝ, 0 < y.2 → level * Real.sqrt y.2 ≤ y.1 →
            Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
              (a0, a0 ^ 2 / level ^ 2) ≤
              Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y) ∧
          ∀ y : ℝ × ℝ, 0 < y.2 → level * Real.sqrt y.2 ≤ y.1 →
            Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y ≤
              Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
                (a0, a0 ^ 2 / level ^ 2) → y = (a0, a0 ^ 2 / level ^ 2) := by
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
    rfl
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
  obtain ⟨Lbase, _hLbase, _hiBase, _hdiBase, hJ, _hgBase, _hHBase, hquad, _hABase, _hIBase⟩ :=
    actual_mean_chart_rate_covariance_derivatives mu e he hsource (0, q0) hw hdetw
  change ContDiffAt ℝ ∞ J (0, q0) at hJ
  have hD00 : parabolaCovariance mu 0 0 = q0 := by
    change ProbabilityTheory.variance (fun x : ℝ => x) mu = q0
    have hmeas : AEMeasurable (fun x : ℝ => x) mu := measurable_id.aemeasurable
    rw [ProbabilityTheory.variance_eq_integral hmeas]
    simp only [hmean, sub_zero]
    rfl
  have hcurvature : 0 <
      (fderiv ℝ (fun z => fderiv ℝ J z) (0, q0) (0, 1)) (0, 1) := by
    have henergyHessian :
        (fderiv ℝ (fun z => fderiv ℝ J z) (0, q0) (0, 1)) (0, 1) =
          q0 / (parabolaCovariance mu).det := by
      simpa [hinv, htilt0, hD00] using hquad ((0 : ℝ), 1)
    rw [henergyHessian]
    exact div_pos hq0 hdet
  have hP : ContinuousAt (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) (0, q0) :=
    e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hw)
  obtain ⟨eta, rho, heta, hrho, _hrhoq, hscaled⟩ :=
    scaled_tangent_positive_curvature_neighborhood J e.symm q0 hq0
      (hJ.of_le (by simp)) hP hinv hcurvature
  let detTilt : (ℝ × ℝ) → ℝ := fun p =>
    (parabolaCovariance (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))).det
  have hdetCont : ContinuousAt detTilt ((0 : ℝ), (0 : ℝ)) :=
    (((open_domain_quadratic_covariance_det_contDiffOn mu) (0, 0) htheta0).contDiffAt
      (isOpen_interior.mem_nhds htheta0)).continuousAt
  have hdetP : ContinuousAt (fun z : ℝ × ℝ => detTilt (e.symm z)) (0, q0) := by
    have hh : ContinuousAt detTilt (e.symm ((0 : ℝ), q0)) := by
      rw [hinv]
      exact hdetCont
    exact hh.comp (f := (e.symm : (ℝ × ℝ) → (ℝ × ℝ))) hP
  have hbase : 0 < detTilt (e.symm ((0 : ℝ), q0)) := by
    simpa only [hinv] using hdet0
  have hgood : ∀ᶠ z in 𝓝 ((0 : ℝ), q0), z ∈ e.target ∧ 0 < detTilt (e.symm z) :=
    Filter.inter_mem (e.open_target.mem_nhds hw) (hdetP.eventually (lt_mem_nhds hbase))
  obtain ⟨d, hd, hnear⟩ := Metric.eventually_nhds_iff.mp hgood
  obtain ⟨epsD, hepsD, hepsD1, hmins⟩ :=
    bounded_centered_parabola_global_minima_localize mu M hM hb lower upper hlower
      henergy hmean hdet.ne' (min rho (d / 2)) (lt_min hrho (half_pos hd))
  obtain ⟨epsU, hepsU, _hepsU1, hunique⟩ :=
    bounded_centered_parabola_small_positive_unique_global_minimum mu M hM hb
      lower upper hlower henergy hmean hdet
  refine ⟨min epsD (min eta epsU), lt_min hepsD (lt_min heta hepsU),
    (min_le_left _ _).trans hepsD1, ?_⟩
  intro level hlevel hsmall
  have hsmallD := hsmall.trans_le (min_le_left _ _)
  have hsmallEta := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hsmallU := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hlevelBound : |level| ≤ eta := by simpa only [abs_of_pos hlevel] using hsmallEta.le
  obtain ⟨z, hzq, hzcone, hzpos, hzfinite, hzglobal, hlocal⟩ := hmins level hlevel hsmallD
  have hzdist := hlocal z (le_refl _)
  have hgoodz := hnear ((hzdist.trans_le (min_le_right _ _)).trans (half_lt_self hd))
  obtain ⟨w, hwq, hwb, _hwpos, _hwfinite, _hwglobal, hwunique⟩ :=
    hunique level hlevel hsmallU
  have hzw : z = w := hwunique z hzq hzcone
    (hzglobal w hwq (by rw [hwb]))
  have hzb : z.1 = level * Real.sqrt z.2 := by rw [hzw]; exact hwb
  have hzunique (y : ℝ × ℝ) (hyq : 0 < y.2) (hycone : level * Real.sqrt y.2 ≤ y.1)
      (hyle : Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y ≤
        Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z) : y = z := by
    have hylew : Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y ≤
        Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w := by
      simpa only [hzw] using hyle
    exact (hwunique y hyq hycone hylew).trans hzw.symm
  let theta : ℝ × ℝ := e.symm z
  let a0 : ℝ := z.1
  have htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) :=
    hsource (e.map_target hgoodz.1)
  have hcov : 0 < (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det := hgoodz.2
  have hmeanZ : (∫ x : ℝ, x ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2),
      ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) = z := by
    rw [← congrFun he theta]
    exact e.right_inv hgoodz.1
  have ha0 : 0 < a0 :=
    (mul_pos hlevel (Real.sqrt_pos.mpr hzq)).trans_le hzcone
  have henergyPoint : a0 ^ 2 / level ^ 2 = z.2 := by
    apply (div_eq_iff (pow_ne_zero 2 hlevel.ne')).mpr
    change z.1 ^ 2 = z.2 * level ^ 2
    rw [hzb, mul_pow, Real.sq_sqrt hzq.le]
    ring
  have hpoint : z = (a0, a0 ^ 2 / level ^ 2) := Prod.ext rfl henergyPoint.symm
  have hmeanPoint := hmeanZ.trans hpoint
  have hglobalPoint (y : ℝ × ℝ) (hyq : 0 < y.2)
      (hycone : level * Real.sqrt y.2 ≤ y.1) :
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
        (a0, a0 ^ 2 / level ^ 2) ≤
        Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y := by
    rw [← hpoint]
    exact hzglobal y hyq hycone
  obtain ⟨hstationary, htheta1, htheta2⟩ :=
    bounded_centered_parabola_global_boundary_tilt_sign mu M hM hb hmean theta htheta
      hcov.ne' level a0 hlevel ha0 hmeanPoint hglobalPoint
  obtain ⟨L, hL, _hiZ, _hdiZ, _hJZ, _hgZ, hHessZ, _hquadZ, _hAZ, _hIZ⟩ :=
    actual_mean_chart_rate_covariance_derivatives mu e he hsource z hgoodz.1 hcov
  let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
  let H : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ)) :=
    fun z => fderiv ℝ (fun y => fderiv ℝ J y) z
  have hHv : H z v v = (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2 := by
    change (fderiv ℝ (fun w => fderiv ℝ J w) z v) v = _
    rw [hHessZ.fderiv]
    change (L.symm v).1 * v.1 + (L.symm v).2 * v.2 = _
    dsimp only [v]
    ring
  have hscaledVector : (level, 2 * Real.sqrt z.2) = level • v := by
    apply Prod.ext
    · simp [v]
    · change 2 * Real.sqrt z.2 = level * (2 * a0 / level ^ 2)
      have ha : a0 = level * Real.sqrt z.2 := hzb
      rw [ha]
      field_simp [hlevel.ne']
      <;> ring
  have hscaledH : H z (level, 2 * Real.sqrt z.2) (level, 2 * Real.sqrt z.2) =
      level ^ 2 * H z v v := by
    rw [hscaledVector]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hpositive := hscaled level z hlevelBound (hzdist.le.trans (min_le_left _ _))
  change 0 < 2 * theta.2 + H z (level, 2 * Real.sqrt z.2) (level, 2 * Real.sqrt z.2)
    at hpositive
  rw [hscaledH, hHv] at hpositive
  have hlambda : 0 < 2 * theta.2 / level ^ 2 +
      (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2 := by
    have hprod : 0 < level ^ 2 * (2 * theta.2 / level ^ 2 +
        (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2) := by
      convert hpositive using 1 <;> field_simp [hlevel.ne'] <;> ring
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg level) (not_lt.mp hn)
    linarith
  refine ⟨a0, theta, L, ha0, htheta, hcov, hmeanPoint, hstationary, htheta1, htheta2,
    hL, hlambda, ?_, ?_, hglobalPoint, ?_⟩
  · simpa only [hpoint] using hzpos
  · simpa only [hpoint] using hzfinite
  · intro y hyq hycone hyle
    have hylez : Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y ≤
        Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z := by
      simpa only [hpoint] using hyle
    exact (hzunique y hyq hycone hylez).trans hpoint

end
end Shao.OQ3
