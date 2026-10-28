import Shao.OQ3.ActualMeanChartLocalCompatibility
import Shao.OQ3.OpenDomainBoundaryTaylor

namespace Shao.OQ3
open MeasureTheory Filter
open scoped Matrix Topology ContDiff
noncomputable section

set_option maxHeartbeats 2000000 in
theorem actual_mean_chart_boundary_taylor
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : 0 < (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det)
    (level a0 : ℝ) (hlevel : 0 < level) (ha0 : 0 < a0) (hnegative : theta.2 < 0)
    (hmean : (∫ x : ℝ, x ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2),
      ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) =
        (a0, a0 ^ 2 / level ^ 2))
    (hsaddle : theta.1 = -2 * a0 * theta.2 / level ^ 2)
    (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (he : (e : (ℝ × ℝ) → (ℝ × ℝ)) = fun p =>
      (∫ x : ℝ, x ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2),
        ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)))
    (hte : theta ∈ e.source)
    (hsource : e.source ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
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
    ∀ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = row0.prod row1 →
      let J : (ℝ × ℝ) → ℝ := fun w =>
        (e.symm w).1 * w.1 + (e.symm w).2 * w.2 - K (e.symm w)
      let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
        (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
      let F : (ℝ × ℝ) → ℝ := fun w => J (G w)
      let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
      let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
        (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
      ContDiffAt ℝ ∞ F (0, 0) ∧
        ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧ ∀ r z : ℝ,
          |r| ≤ rho → 0 ≤ z → z ≤ rho →
          |F (r, z) - F (0, 0) - (-theta.2) * z - Lambda1 / 2 * r ^ 2| ≤
            C * (|r| ^ 3 + |r| * z + z ^ 2) := by
  intro Omega nu means K D pr0 pr1 row0 row1 L hL J G F v Lambda1
  obtain ⟨L0, f, hL0, hf, htf, hTarget, hOldSource, hnegative',
      hSmooth, hFirst, hSecond, hGlobal, rho0, C, hrho0, hC, hTaylor⟩ :=
    open_domain_quadratic_tilt_boundary_taylor mu theta htheta hdet.ne'
      level a0 hlevel ha0 hnegative hmean hsaddle
  have hLsame : L0 = L := by
    apply ContinuousLinearEquiv.ext
    intro u
    exact congrArg (fun T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) => T u) (hL0.trans hL.symm)
  subst L0
  let Jold : (ℝ × ℝ) → ℝ := fun w =>
    (f.symm w).1 * w.1 + (f.symm w).2 * w.2 - K (f.symm w)
  let Fold : (ℝ × ℝ) → ℝ := fun w => Jold (G w)
  have hFoldSmooth : ContDiffAt ℝ ∞ Fold (0, 0) := hSmooth
  have hOldBound : ∀ r z : ℝ, |r| ≤ rho0 → 0 ≤ z → z ≤ rho0 →
      |Fold (r, z) - Fold (0, 0) - (-theta.2) * z - Lambda1 / 2 * r ^ 2| ≤
        C * (|r| ^ 3 + |r| * z + z ^ 2) := hTaylor
  obtain ⟨_, _, hCompat⟩ := actual_mean_chart_local_compatibility mu theta e f he hf hte htf
  have hGzero : G (0, 0) = means theta := by
    simpa only [G, add_zero, sub_zero] using hmean.symm
  have hGcont : Continuous G := by dsimp only [G]; fun_prop
  have hGtend : Tendsto G (𝓝 (0, 0)) (𝓝 (means theta)) := by
    rw [← hGzero]
    exact hGcont.continuousAt
  have hNear : F =ᶠ[𝓝 (0, 0)] Fold := by
    filter_upwards [hGtend.eventually hCompat] with w hw
    exact hw.2.2.2.1
  obtain ⟨delta, hdelta, hPoint⟩ := Metric.eventually_nhds_iff.mp hNear
  have hZero : F (0, 0) = Fold (0, 0) := hPoint (by simpa using hdelta)
  let rho : ℝ := min rho0 (delta / 2)
  have hrho : 0 < rho := lt_min hrho0 (half_pos hdelta)
  refine ⟨hFoldSmooth.congr_of_eventuallyEq hNear, rho, C, hrho, hC, ?_⟩
  intro r z hr hz hzr
  have hDist : dist (r, z) (0, 0) < delta := by
    rw [show (0, 0) = (0 : ℝ × ℝ) from rfl, dist_zero_right, Prod.norm_def,
      Real.norm_eq_abs, Real.norm_eq_abs, max_lt_iff]
    have hSmall : rho < delta := lt_of_le_of_lt (min_le_right rho0 (delta / 2))
      (by linarith)
    exact ⟨hr.trans_lt hSmall, by rw [abs_of_nonneg hz]; exact hzr.trans_lt hSmall⟩
  rw [hPoint hDist, hZero]
  exact hOldBound r z (hr.trans (min_le_left _ _)) hz (hzr.trans (min_le_left _ _))

end
end Shao.OQ3
