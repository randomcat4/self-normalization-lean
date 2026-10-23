import Shao.OQ3.OpenDomainBoundaryLowerBound
import Shao.OQ3.OpenDomainCovarianceAmplitude
import Shao.OQ3.BoundaryLaplaceMeasurability

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_boundary_laplace_cutoff_integral
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : 0 < (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det)
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
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (nu theta)
    let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
    let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
    let row0 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 0 • pr0 + D 0 1 • pr1
    let row1 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 1 • pr0 + D 1 1 • pr1
    ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = row0.prod row1 ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = means ∧ theta ∈ e.source ∧ e.source ⊆ Omega ∧
      let K : (ℝ × ℝ) → ℝ := fun p => Real.log
        (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
      let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
        (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
      let P : (ℝ × ℝ) → (ℝ × ℝ) := fun w => e.symm (G w)
      let F : (ℝ × ℝ) → ℝ := fun w =>
        (P w).1 * (G w).1 + (P w).2 * (G w).2 - K (P w)
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
        (0 < Lambda1 → 0 < C0 ∧ ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧
          (∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
            G (r, z) ∈ e.target ∧ P (r, z) ∈ e.source ∧ P (r, z) ∈ Omega ∧
              means (P (r, z)) = G (r, z) ∧ 0 < detF (r, z) ∧
              Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
                (G (r, z)) = (F (r, z) : EReal)) ∧
          ∀ t : ℝ, 0 < t → t ≤ 1 →
            let H : (ℝ × ℝ) → ℝ := fun p =>
              if |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho then
                A (t * p.1, t ^ 2 * p.2) *
                  Real.exp (-((F (t * p.1, t ^ 2 * p.2) - F (0, 0)) / t ^ 2)) else 0
            Integrable H m ∧ |(∫ p : ℝ × ℝ, H p ∂m) - C0| ≤ C * t ∧
              |(∫ p : ℝ × ℝ, H p ∂m) / C0 - 1| ≤ C * t) := by
  let Omega : Set (ℝ × ℝ) := interior
    (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
  let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
    mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
    (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
  let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (nu theta)
  let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  let row0 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 0 • pr0 + D 0 1 • pr1
  let row1 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 1 • pr0 + D 1 1 • pr1
  obtain ⟨L, e, hL, he, hs, ht, hsOmega, hlambda, hFsmooth, _, _, hglobal,
      hTaylor, hCoercive⟩ := open_domain_quadratic_tilt_boundary_lower_bound
        mu theta htheta hdet.ne' level a0 hlevel ha0 hnegative hmean hsaddle
  let K : (ℝ × ℝ) → ℝ := fun p => Real.log
    (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
    (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
  let P : (ℝ × ℝ) → (ℝ × ℝ) := fun w => e.symm (G w)
  let F : (ℝ × ℝ) → ℝ := fun w =>
    (P w).1 * (G w).1 + (P w).2 * (G w).2 - K (P w)
  let detF : (ℝ × ℝ) → ℝ := fun w => (parabolaCovariance (nu (P w))).det
  let A : (ℝ × ℝ) → ℝ := fun w => (Real.sqrt (detF w))⁻¹
  let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
  let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
    (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
  let C0 : ℝ := A (0, 0) * (Real.sqrt (2 * Real.pi / Lambda1) / (-theta.2))
  let m : Measure (ℝ × ℝ) :=
    (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))
  obtain ⟨hP0, _, hAsmooth, hA0, rhoA, CA, hrhoA, hCA, hAmp⟩ :=
    open_domain_chart_covariance_amplitude mu theta htheta level a0 hlevel ha0 hmean e he hs hdet
  have hA0exact : A (0, 0) = (Real.sqrt D.det)⁻¹ := hA0
  have hemeans : (e : (ℝ × ℝ) → (ℝ × ℝ)) = means := he
  have hApos : 0 < A (0, 0) := by
    rw [hA0exact]
    exact inv_pos.mpr (Real.sqrt_pos.mpr hdet)
  refine ⟨L, e, hL, he, hs, hsOmega, hlambda, hP0, hA0, hApos, ?_⟩
  intro hcurvature
  have hC0 : 0 < C0 := by
    exact mul_pos hApos (div_pos
      (Real.sqrt_pos.mpr (div_pos (mul_pos (by norm_num) Real.pi_pos) hcurvature)) hlambda)
  obtain ⟨rhoT, CF, hrhoT, hCF, hbound⟩ := hTaylor
  obtain ⟨rhoC, c, hrhoC, hc, hmargin⟩ := hCoercive hcurvature
  let cap : ℝ := min rhoT (min rhoC rhoA)
  have hcap : 0 < cap := lt_min hrhoT (lt_min hrhoC hrhoA)
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hG0 : G (0, 0) = means theta := by
    simpa only [G, add_zero, sub_zero] using hmean.symm
  have hGt : Filter.Tendsto G (𝓝 (0, 0)) (𝓝 (means theta)) := by
    rw [← hG0]
    exact hG.continuousAt
  have htarget : ∀ᶠ w in 𝓝 (0, 0), G w ∈ e.target :=
    hGt.eventually (e.open_target.mem_nhds ht)
  let Q : (ℝ × ℝ) → Prop := fun w =>
    Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) (G w) = (F w : EReal) ∧
      G w ∈ e.target
  have hQ : ∀ᶠ w in 𝓝 (0, 0), Q w := by
    filter_upwards [hglobal, htarget] with w hw htarg
    exact ⟨hw, htarg⟩
  obtain ⟨rho, hrho, hrcap, hQrect, _, _, hmeas⟩ :=
    exists_boundary_continuous_cutoff_window F A
      (hFsmooth.of_le (by norm_num)) (hAsmooth.of_le (by norm_num)) Q hQ cap hcap
  have hrT : rho ≤ rhoT := hrcap.trans (min_le_left _ _)
  have hrC : rho ≤ rhoC := hrcap.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrA : rho ≤ rhoA := hrcap.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hb : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (0, 0) - (-theta.2) * z - Lambda1 / 2 * r ^ 2| ≤
        CF * (|r| ^ 3 + |r| * z + z ^ 2) := by
    intro r z hr hz hzr
    exact hbound r z (hr.trans hrT) hz (hzr.trans hrT)
  have hm : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      c * (z + r ^ 2) ≤ F (r, z) - F (0, 0) := by
    intro r z hr hz hzr
    exact hmargin r z (hr.trans hrC) hz (hzr.trans hrC)
  have ha : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |A (r, z) - A (0, 0)| ≤ CA * (|r| + z) := by
    intro r z hr hz hzr
    exact (hAmp r z (hr.trans hrA) hz (hzr.trans hrA)).2.2
  let d : ℝ := min c (min (-theta.2) (Lambda1 / 2))
  have hd : 0 < d := lt_min hc (lt_min hlambda (by linarith))
  have hdc : d ≤ c := min_le_left _ _
  have hdl : d ≤ -theta.2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdq : d ≤ Lambda1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨Cabs, hCabs, herr⟩ := boundary_laplace_cutoff_integral_error
    F A (-theta.2) Lambda1 rho CF CA c d hCF.le hCA.le hrho hd hdc hdl hdq hb hm ha
      (fun t _ _ => hmeas t)
  let C : ℝ := max Cabs (Cabs / C0)
  refine ⟨hC0, rho, C, hrho, hCabs.trans_le (le_max_left _ _), ?_, ?_⟩
  · intro r z hr hz hzr
    have hq := hQrect r z hr hz hzr
    have hap := hAmp r z (hr.trans hrA) hz (hzr.trans hrA)
    have hidentity : means (P (r, z)) = G (r, z) := by
      rw [← hemeans]
      exact e.right_inv hq.2
    exact ⟨hq.2, e.map_target hq.2, hap.1, hidentity, hap.2.1, hq.1⟩
  · intro t ht ht1
    obtain ⟨hI, herror⟩ := herr t ht ht1
    refine ⟨hI, herror.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le), ?_⟩
    let I : ℝ := ∫ p : ℝ × ℝ,
      (if |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho then
        A (t * p.1, t ^ 2 * p.2) *
          Real.exp (-((F (t * p.1, t ^ 2 * p.2) - F (0, 0)) / t ^ 2)) else 0) ∂m
    change |I / C0 - 1| ≤ C * t
    have heq : I / C0 - 1 = (I - C0) / C0 := by field_simp
    rw [heq, abs_div, abs_of_pos hC0]
    calc
      |I - C0| / C0 ≤ (Cabs * t) / C0 := div_le_div_of_nonneg_right herror hC0.le
      _ = (Cabs / C0) * t := by ring
      _ ≤ C * t := mul_le_mul_of_nonneg_right (le_max_right _ _) ht.le

end
end Shao.OQ3
