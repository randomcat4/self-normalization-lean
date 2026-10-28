import Shao.OQ3.ActualMeanChartBoundaryTaylor
import Shao.OQ3.ActualMeanChartRateDerivatives
import Shao.OQ3.OpenDomainCovarianceAmplitude
import Shao.OQ3.LocalBoundaryLowerBound
import Shao.OQ3.BoundaryLaplaceMeasurability

namespace Shao.OQ3
open MeasureTheory Filter
open scoped Matrix Topology ContDiff
noncomputable section

set_option maxHeartbeats 2000000 in
theorem actual_mean_chart_laplace_cutoff_all_small_windows
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
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (rmax : ℝ) (hrmax : 0 < rmax) :
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
      let P : (ℝ × ℝ) → (ℝ × ℝ) := fun w => e.symm (G w)
      let F : (ℝ × ℝ) → ℝ := fun w => J (G w)
      let detF : (ℝ × ℝ) → ℝ := fun w => (parabolaCovariance (nu (P w))).det
      let A : (ℝ × ℝ) → ℝ := fun w => (Real.sqrt (detF w))⁻¹
      let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
      let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
        (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
      let C0 : ℝ := A (0, 0) * (Real.sqrt (2 * Real.pi / Lambda1) / (-theta.2))
      let m : Measure (ℝ × ℝ) :=
        (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))
      0 < -theta.2 ∧ P (0, 0) = theta ∧
        A (0, 0) = (Real.sqrt D.det)⁻¹ ∧ 0 < A (0, 0) ∧
        (0 < Lambda1 → ∃ cap : ℝ, 0 < cap ∧ cap ≤ rmax ∧ 0 < C0 ∧
          ∀ rho : ℝ, 0 < rho → rho ≤ cap →
            (∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
              G (r, z) ∈ e.target ∧ P (r, z) ∈ e.source ∧ P (r, z) ∈ Omega ∧
                means (P (r, z)) = G (r, z) ∧ 0 < detF (r, z) ∧
                Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
                  (G (r, z)) = (F (r, z) : EReal)) ∧
            ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
              let H : (ℝ × ℝ) → ℝ := fun p =>
                if |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho then
                  A (t * p.1, t ^ 2 * p.2) *
                    Real.exp (-((F (t * p.1, t ^ 2 * p.2) - F (0, 0)) / t ^ 2)) else 0
              Integrable H m ∧ |(∫ p : ℝ × ℝ, H p ∂m) - C0| ≤ C * t ∧
                |(∫ p : ℝ × ℝ, H p ∂m) / C0 - 1| ≤ C * t) := by
  classical
  intro Omega nu means K D pr0 pr1 row0 row1 L hL J G P F detF A v Lambda1 C0 m
  obtain ⟨hFsmooth, rhoT, CF, hrhoT, hCF, hbound⟩ :=
    actual_mean_chart_boundary_taylor mu theta htheta hdet level a0 hlevel ha0
      hnegative hmean hsaddle e he hte hsource L hL
  obtain ⟨hP0, _, hAsmooth, hA0, rhoA, CA, hrhoA, hCA, hAmp⟩ :=
    open_domain_chart_covariance_amplitude mu theta htheta level a0 hlevel ha0 hmean e he hte hdet
  have hemeans : (e : (ℝ × ℝ) → (ℝ × ℝ)) = means := he
  have hA0exact : A (0, 0) = (Real.sqrt D.det)⁻¹ := hA0
  have hlambda : 0 < -theta.2 := neg_pos.mpr hnegative
  have hApos : 0 < A (0, 0) := by
    rw [hA0exact]
    exact inv_pos.mpr (Real.sqrt_pos.mpr hdet)
  refine ⟨hlambda, hP0, hA0exact, hApos, ?_⟩
  intro hcurvature
  have hC0 : 0 < C0 := mul_pos hApos (div_pos
    (Real.sqrt_pos.mpr (div_pos (mul_pos (by norm_num) Real.pi_pos) hcurvature)) hlambda)
  obtain ⟨rhoC, c, hrhoC, _, hc, hmargin⟩ :=
    exists_positive_boundary_lower_bound_of_taylor F (-theta.2) Lambda1 rhoT CF
      hlambda hcurvature hrhoT hCF hbound
  let bound : ℝ := min rmax (min rhoT (min rhoC rhoA))
  have hboundpos : 0 < bound := lt_min hrmax (lt_min hrhoT (lt_min hrhoC hrhoA))
  have hGcont : Continuous G := by dsimp only [G]; fun_prop
  have hG0 : G (0, 0) = means theta := by
    simpa only [G, add_zero, sub_zero] using hmean.symm
  have hGt : Tendsto G (𝓝 (0, 0)) (𝓝 (means theta)) := by
    rw [← hG0]
    exact hGcont.continuousAt
  have hTarget0 : means theta ∈ e.target := by
    rw [← hemeans]
    exact e.map_source hte
  have hQ : ∀ᶠ w in 𝓝 (0, 0), G w ∈ e.target :=
    hGt.eventually (e.open_target.mem_nhds hTarget0)
  obtain ⟨cap, hcap, hcapBound, hQrect, hFc, hAc, _⟩ :=
    exists_boundary_continuous_cutoff_window F A
      (hFsmooth.of_le (by norm_num)) (hAsmooth.of_le (by norm_num))
      (fun w => G w ∈ e.target) hQ bound hboundpos
  have hcapT : cap ≤ rhoT :=
    hcapBound.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcapC : cap ≤ rhoC :=
    hcapBound.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hcapA : cap ≤ rhoA :=
    hcapBound.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨cap, hcap, hcapBound.trans (min_le_left _ _), hC0, ?_⟩
  intro rho hrho hrhocap
  have hrT : rho ≤ rhoT := hrhocap.trans hcapT
  have hrC : rho ≤ rhoC := hrhocap.trans hcapC
  have hrA : rho ≤ rhoA := hrhocap.trans hcapA
  have hb : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (0, 0) - (-theta.2) * z - Lambda1 / 2 * r ^ 2| ≤
        CF * (|r| ^ 3 + |r| * z + z ^ 2) :=
    fun r z hr hz hzr => hbound r z (hr.trans hrT) hz (hzr.trans hrT)
  have hm : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      c * (z + r ^ 2) ≤ F (r, z) - F (0, 0) :=
    fun r z hr hz hzr => hmargin r z (hr.trans hrC) hz (hzr.trans hrC)
  have ha : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |A (r, z) - A (0, 0)| ≤ CA * (|r| + z) :=
    fun r z hr hz hzr => (hAmp r z (hr.trans hrA) hz (hzr.trans hrA)).2.2
  have hSub : {w : ℝ × ℝ | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho} ⊆
      {w : ℝ × ℝ | |w.1| ≤ cap ∧ 0 ≤ w.2 ∧ w.2 ≤ cap} :=
    fun _ hw => ⟨hw.1.trans hrhocap, hw.2.1, hw.2.2.trans hrhocap⟩
  have hmeas (t : ℝ) := boundary_laplace_cutoff_aestronglyMeasurable_of_continuousOn
    F A rho t (hFc.mono hSub) (hAc.mono hSub)
  let d : ℝ := min c (min (-theta.2) (Lambda1 / 2))
  have hd : 0 < d := lt_min hc (lt_min hlambda (by linarith))
  obtain ⟨Cabs, hCabs, herr⟩ := boundary_laplace_cutoff_integral_error
    F A (-theta.2) Lambda1 rho CF CA c d hCF.le hCA.le hrho hd
      (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_right _ _)) hb hm ha (fun t _ _ => hmeas t)
  let C : ℝ := max Cabs (Cabs / C0)
  refine ⟨?_, C, hCabs.trans_le (le_max_left _ _), ?_⟩
  · intro r z hr hz hzr
    have htarg := hQrect r z (hr.trans hrhocap) hz (hzr.trans hrhocap)
    have hap := hAmp r z (hr.trans hrA) hz (hzr.trans hrA)
    have hidentity : means (P (r, z)) = G (r, z) := by
      rw [← hemeans]
      exact e.right_inv htarg
    obtain ⟨_, _, _, _, _, _, _, _, _, hGlobal⟩ :=
      actual_mean_chart_rate_covariance_derivatives mu e he hsource (G (r, z)) htarg hap.2.1
    exact ⟨htarg, e.map_target htarg, hap.1, hidentity, hap.2.1, hGlobal⟩
  · intro t ht ht1 H
    obtain ⟨hI, herror⟩ := herr t ht ht1
    refine ⟨hI, herror.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le), ?_⟩
    let I : ℝ := ∫ p : ℝ × ℝ, H p ∂m
    change |I / C0 - 1| ≤ C * t
    have heq : I / C0 - 1 = (I - C0) / C0 := by field_simp
    rw [heq, abs_div, abs_of_pos hC0]
    calc
      |I - C0| / C0 ≤ (Cabs * t) / C0 := div_le_div_of_nonneg_right herror hC0.le
      _ = (Cabs / C0) * t := by ring
      _ ≤ C * t := mul_le_mul_of_nonneg_right (le_max_right _ _) ht.le

end
end Shao.OQ3
