import Shao.OQ3.OpenDomainCompactMeanChart
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_quadratic_tilt_legendre_attained
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    let nu : Measure ℝ := mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)
    let m : ℝ × ℝ := (∫ x : ℝ, x ∂nu, ∫ x : ℝ, x ^ 2 ∂nu)
    let Ktheta : ℝ := Real.log
      (∫ x : ℝ, Real.exp (theta.1 * x + theta.2 * x ^ 2) ∂mu)
    let I : ℝ := theta.1 * m.1 + theta.2 * m.2 - Ktheta
    (∀ p : Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)),
      (p : ℝ × ℝ).1 * m.1 + (p : ℝ × ℝ).2 * m.2 -
        Shao.Probability.bivariateLogMGF mu (fun x : ℝ => (x, x ^ 2)) p ≤ I) ∧
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) m = (I : EReal) := by
  let nu : Measure ℝ := mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)
  let m : ℝ × ℝ := (∫ x : ℝ, x ∂nu, ∫ x : ℝ, x ^ 2 ∂nu)
  let Z : (ℝ × ℝ) → ℝ := fun p => ∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu
  let I : ℝ := theta.1 * m.1 + theta.2 * m.2 - Real.log (Z theta)
  have hfull := open_domain_quadratic_tilt_directional_cumulants mu theta htheta
  letI : IsProbabilityMeasure nu := hfull.1
  have hx : Integrable (fun x : ℝ => x) nu := hfull.2.1.integrable (by norm_num)
  have hx2 : Integrable (fun x : ℝ => x ^ 2) nu := hfull.2.2.1.integrable (by norm_num)
  have hupper : ∀ p : Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)),
      (p : ℝ × ℝ).1 * m.1 + (p : ℝ × ℝ).2 * m.2 -
        Shao.Probability.bivariateLogMGF mu (fun x : ℝ => (x, x ^ 2)) p ≤ I := by
    intro p
    let d : ℝ × ℝ := (p : ℝ × ℝ) - theta
    let F : ℝ → ℝ := fun x => d.1 * x + d.2 * x ^ 2
    have hbase := quadratic_tilt_mgf_identity mu theta d (interior_subset htheta)
    have hshift : (theta.1 + 1 * d.1, theta.2 + 1 * d.2) = (p : ℝ × ℝ) := by
      apply Prod.ext <;> dsimp [d] <;> ring
    have hiexp : Integrable (fun x : ℝ => Real.exp (F x)) nu := by
      have hh := ((hbase.2.2 1).1).mpr (by rw [hshift]; exact p.property)
      simpa only [one_mul] using hh
    have hmgf : (∫ x : ℝ, Real.exp (F x) ∂nu) = Z (p : ℝ × ℝ) / Z theta := by
      have hh := (hbase.2.2 1).2
      change (∫ x : ℝ, Real.exp (1 * F x) ∂nu) =
        Z (theta.1 + 1 * d.1, theta.2 + 1 * d.2) / Z theta at hh
      rw [hshift] at hh
      simpa only [one_mul] using hh
    have hFi : Integrable F nu := (hx.const_mul d.1).add (hx2.const_mul d.2)
    have hj : Real.exp (∫ x : ℝ, F x ∂nu) ≤ ∫ x : ℝ, Real.exp (F x) ∂nu :=
      convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
        (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hFi hiexp
    have hZp : 0 < Z (p : ℝ × ℝ) := integral_exp_pos p.property
    have hZtheta : 0 < Z theta := hbase.2.1
    have hlog : (∫ x : ℝ, F x ∂nu) ≤ Real.log (Z (p : ℝ × ℝ)) - Real.log (Z theta) := by
      have hh := Real.log_le_log (Real.exp_pos (∫ x : ℝ, F x ∂nu)) hj
      rw [Real.log_exp, hmgf, Real.log_div hZp.ne' hZtheta.ne'] at hh
      exact hh
    have hEF : (∫ x : ℝ, F x ∂nu) = d.1 * m.1 + d.2 * m.2 := by
      change (∫ x : ℝ, d.1 * x + d.2 * x ^ 2 ∂nu) = _
      rw [integral_add (hx.const_mul d.1) (hx2.const_mul d.2),
        integral_const_mul, integral_const_mul]
    rw [hEF] at hlog
    change (p : ℝ × ℝ).1 * m.1 + (p : ℝ × ℝ).2 * m.2 - Real.log (Z (p : ℝ × ℝ)) ≤
      theta.1 * m.1 + theta.2 * m.2 - Real.log (Z theta)
    dsimp [d] at hlog
    nlinarith only [hlog]
  refine ⟨hupper, ?_⟩
  exact Shao.Probability.bivariateLegendreRate_eq_of_attained_bound mu
    (fun x : ℝ => (x, x ^ 2)) m I hupper ⟨theta, interior_subset htheta⟩ rfl

theorem open_domain_quadratic_tilt_compact_legendre_chart
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
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ), ∃ epsilon : ℝ,
      0 < epsilon ∧ (e : (ℝ × ℝ) → (ℝ × ℝ)) = means ∧
      theta ∈ e.source ∧ e.source ⊆ Omega ∧
      Metric.closedBall (means theta) epsilon ⊆ e.target ∧
      let Theta : Set (ℝ × ℝ) := e.symm '' Metric.closedBall (means theta) epsilon
      IsCompact Theta ∧ theta ∈ Theta ∧ Theta ⊆ Omega ∧
        ∀ z ∈ Metric.closedBall (means theta) epsilon,
          e.symm z ∈ Theta ∧ means (e.symm z) = z ∧
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z =
            (((e.symm z).1 * z.1 + (e.symm z).2 * z.2 - Real.log
              (∫ x : ℝ, Real.exp ((e.symm z).1 * x + (e.symm z).2 * x ^ 2) ∂mu) : ℝ) : EReal) := by
  let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
    mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
    (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
  obtain ⟨e, epsilon, hepsilon, he, hs, hsource, hclosed, _hinverse, hrest⟩ :=
    open_domain_quadratic_tilt_compact_mean_chart mu theta htheta hdet
  obtain ⟨_hUopen, _hmU, hcompact, hcenter, hTheta, _hcont, hright, _hleft, _himage, _himgU⟩ := hrest
  refine ⟨e, epsilon, hepsilon, he, hs, hsource, hclosed, hcompact, hcenter, hTheta, ?_⟩
  intro z hz
  have hzdata := hright z hz
  have hm : means (e.symm z) = z := hzdata.2
  have hleg := (open_domain_quadratic_tilt_legendre_attained mu (e.symm z)
    (hTheta hzdata.1)).2
  change Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
      (means (e.symm z)) =
    (((e.symm z).1 * (means (e.symm z)).1 + (e.symm z).2 * (means (e.symm z)).2 - Real.log
      (∫ x : ℝ, Real.exp ((e.symm z).1 * x + (e.symm z).2 * x ^ 2) ∂mu) : ℝ) : EReal) at hleg
  rw [hm] at hleg
  exact ⟨hzdata.1, hzdata.2, hleg⟩

end
end Shao.OQ3
