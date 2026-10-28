import Shao.OQ3.ActualMeanChartLaplaceNatPhysicalWindow
import Shao.OQ3.ActualMeanChartBoundaryTaylor
import Shao.OQ3.LocalBoundaryLowerBound
import Shao.OQ3.BoundaryLaplaceEventGeometry
import Shao.OQ3.ParabolaFiniteGridCover
import Shao.OQ3.ParabolaCellRateAnchor

namespace Shao.OQ3
open MeasureTheory Filter
open scoped Matrix Topology ContDiff
noncomputable section

set_option maxHeartbeats 2000000 in
theorem actual_mean_chart_compact_laplace_tilt_windows
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
      let B : (ℝ × ℝ) → ℝ := fun w =>
        (Real.sqrt (parabolaCovariance (nu (e.symm w))).det)⁻¹
      let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
      let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
        (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
      let C0 : ℝ := (Real.sqrt D.det)⁻¹ * (Real.sqrt (2 * Real.pi / Lambda1) / (-theta.2))
      let J0 : ℝ := J (a0, a0 ^ 2 / level ^ 2)
      let m0 : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
      0 < -theta.2 ∧ (0 < Lambda1 →
        ∃ cap : ℝ, 0 < cap ∧ cap ≤ rmax ∧ 0 < C0 ∧
          ∀ rho : ℝ, 0 < rho → rho ≤ cap →
            let U : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
              |w.1 ^ 2 / level ^ 2 - w.2| ≤ rho}
            let Tail : Set (ℝ × ℝ) := {w | 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
            let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
              0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
            let Theta : Set (ℝ × ℝ) := e.symm '' V
            IsCompact Theta ∧ theta ∈ Theta ∧ Theta ⊆ Omega ∧
              (∀ p ∈ Theta, p ∈ e.source ∧ means p ∈ V ∧
                0 < (parabolaCovariance (nu p)).det) ∧
              (∀ w ∈ V, e.symm w ∈ Theta) ∧
              V = U ∩ Tail ∧ IsCompact V ∧
              (∀ w ∈ V, 0 < w.1 ∧ 0 < w.2 ∧ w ∈ e.target ∧ e.symm w ∈ e.source ∧
                e.symm w ∈ Omega ∧ means (e.symm w) = w ∧
                0 < (parabolaCovariance (nu (e.symm w))).det ∧
                Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w =
                  (J w : EReal)) ∧
              (∀ w ∈ V, J0 ≤ J w) ∧
              (∀ aL aR qL qR : ℝ,
                let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩ V
                let Q : Set (ℝ × ℝ) := Set.Icc aL aR ×ˢ Set.Icc qL qR
                A.Nonempty →
                ∃ y ∈ closure A, y ∈ Q ∩ V ∧
                  0 < y.1 ∧ 0 < y.2 ∧ y ∈ e.target ∧ e.symm y ∈ e.source ∧
                  e.symm y ∈ Omega ∧ means (e.symm y) = y ∧
                  0 < (parabolaCovariance (nu (e.symm y))).det ∧
                  Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y =
                    (J y : EReal) ∧
                  ∀ w ∈ closure A,
                    Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y ≤
                      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w ∧
                    J y ≤ J w) ∧
              ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
                let W : (ℝ × ℝ) → ℝ := fun w => B w * Real.exp (-(n : ℝ) * J w)
                let T : (ℝ × ℝ) → ℝ := fun w => B w * Real.exp (-(n : ℝ) * (J w - J0))
                let Ln : ℝ := ((n : ℝ) / (2 * Real.pi)) * ∫ w : ℝ × ℝ in V, T w ∂m0
                let main : ℝ := 1 /
                  (Real.sqrt (2 * Real.pi * (n : ℝ)) * (-theta.2) * Real.sqrt D.det *
                    Real.sqrt Lambda1)
                IntegrableOn W V m0 ∧ IntegrableOn T V m0 ∧ 0 ≤ Ln ∧ 0 < main ∧
                  |Ln / main - 1| ≤ C / Real.sqrt (n : ℝ)) := by
  classical
  intro Omega nu means K D pr0 pr1 row0 row1 L hL J B v Lambda1 C0 J0 m0
  have hemeans : (e : (ℝ × ℝ) → (ℝ × ℝ)) = means := he
  obtain ⟨hlambda, H⟩ := actual_mean_chart_laplace_nat_physical_windows
    mu theta htheta hdet level a0 hlevel ha0 hnegative hmean hsaddle
      e he hte hsource rmax hrmax L hL
  refine ⟨hlambda, ?_⟩
  intro hcurvature
  obtain ⟨capL, hcapL, hcapLMax, hC0, hAll⟩ := H hcurvature
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
    (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
  let F : (ℝ × ℝ) → ℝ := fun w => J (G w)
  obtain ⟨_, rhoT, CF, hrhoT, hCF, hTaylor⟩ :=
    actual_mean_chart_boundary_taylor mu theta htheta hdet level a0 hlevel ha0
      hnegative hmean hsaddle e he hte hsource L hL
  obtain ⟨rhoC, c, hrhoC, _, hc, hMargin⟩ :=
    exists_positive_boundary_lower_bound_of_taylor F (-theta.2) Lambda1 rhoT CF
      hlambda hcurvature hrhoT hCF hTaylor
  obtain ⟨eta, heta, hetaCap, hPhysical⟩ :=
    exists_positive_parabola_window level a0 capL hlevel ha0 hcapL
  let cap : ℝ := min eta rhoC
  have hcap : 0 < cap := lt_min heta hrhoC
  refine ⟨cap, hcap, ((min_le_left _ _).trans hetaCap).trans hcapLMax, hC0, ?_⟩
  intro rho hrho hrhocap U Tail V Theta
  have hrEta : rho ≤ eta := hrhocap.trans (min_le_left _ _)
  have hrC : rho ≤ rhoC := hrhocap.trans (min_le_right _ _)
  have hrL : rho ≤ capL := hrEta.trans hetaCap
  have hVstrip : V = {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
      w.1 ^ 2 / level ^ 2 - rho ≤ w.2 ∧ w.2 ≤ w.1 ^ 2 / level ^ 2} := by
    ext w
    constructor
    · rintro ⟨ha, hz, hzr⟩
      exact ⟨ha, by linarith, by linarith⟩
    · rintro ⟨ha, hl, hu⟩
      exact ⟨ha, by linarith, by linarith⟩
  have hLap := hAll rho hrho hrL
  rw [← hVstrip] at hLap
  obtain ⟨hPatch, C, hC, hLaplace⟩ := hLap
  have hPhysicalRho : ∀ r z : ℝ, |r| ≤ rho → |z| ≤ rho →
      0 < a0 + r ∧ 0 < (a0 + r) ^ 2 / level ^ 2 - z := by
    intro r z hr hz
    have h := hPhysical r z (hr.trans hrEta) (hz.trans hrEta)
    exact ⟨h.1, h.2.1⟩
  obtain ⟨_, _, hUpositive, hStripEvent⟩ :=
    positive_parabola_window_event_geometry level a0 rho hlevel hrho hPhysicalRho
  have hVeq : V = U ∩ Tail := hVstrip.trans hStripEvent
  have hCompact : IsCompact V := actual_parabola_window_isCompact level a0 rho hrho.le
  have hPoints : ∀ w ∈ V, 0 < w.1 ∧ 0 < w.2 ∧ w ∈ e.target ∧
      e.symm w ∈ e.source ∧ e.symm w ∈ Omega ∧ means (e.symm w) = w ∧
      0 < (parabolaCovariance (nu (e.symm w))).det ∧
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w =
        (J w : EReal) := by
    intro w hw
    have hwU : w ∈ U := (hVeq ▸ hw).1
    exact ⟨(hUpositive w hwU).1, (hUpositive w hwU).2, hPatch w hw⟩
  have hTarget : V ⊆ e.target := fun w hw => (hPoints w hw).2.2.1
  have hThetaCompact : IsCompact Theta :=
    hCompact.image_of_continuousOn (e.continuousOn_symm.mono hTarget)
  have hCenterV : (a0, a0 ^ 2 / level ^ 2) ∈ V :=
    ⟨by simpa only [sub_self, abs_zero] using hrho.le,
      by simp, by simpa only [sub_self] using hrho.le⟩
  have hThetaCenter : theta ∈ Theta := by
    refine ⟨(a0, a0 ^ 2 / level ^ 2), hCenterV, ?_⟩
    have hThetaImage : e theta = (a0, a0 ^ 2 / level ^ 2) := by
      rw [hemeans]
      exact hmean
    rw [← hThetaImage]
    exact e.left_inv hte
  have hThetaSub : Theta ⊆ Omega := by
    rintro p ⟨w, hw, rfl⟩
    exact (hPoints w hw).2.2.2.2.1
  have hThetaPoints : ∀ p ∈ Theta, p ∈ e.source ∧ means p ∈ V ∧
      0 < (parabolaCovariance (nu p)).det := by
    rintro p ⟨w, hw, rfl⟩
    obtain ⟨_, _, _, hp, _, hm, hd, _⟩ := hPoints w hw
    exact ⟨hp, hm.symm ▸ hw, hd⟩
  have hFloor : ∀ w ∈ V, J0 ≤ J w := by
    intro w hw
    let r : ℝ := w.1 - a0
    let z : ℝ := w.1 ^ 2 / level ^ 2 - w.2
    have hG : G (r, z) = w := by
      apply Prod.ext <;> dsimp only [G, r, z] <;> ring
    have hG0 : G (0, 0) = (a0, a0 ^ 2 / level ^ 2) := by simp only [G, add_zero, sub_zero]
    have hg := hMargin r z (hw.1.trans hrC) hw.2.1 (hw.2.2.trans hrC)
    change c * (z + r ^ 2) ≤ J (G (r, z)) - J (G (0, 0)) at hg
    rw [hG, hG0] at hg
    exact sub_nonneg.mp ((mul_nonneg hc.le (add_nonneg hw.2.1 (sq_nonneg r))).trans hg)
  refine ⟨hThetaCompact, hThetaCenter, hThetaSub, hThetaPoints,
    (fun w hw => ⟨w, hw, rfl⟩), hVeq, hCompact, hPoints, hFloor, ?_, C, hC, hLaplace⟩
  intro aL aR qL qR A Q hA
  obtain ⟨_, y, hy, hyQV, hmin⟩ :=
    actual_parabola_cell_closure_rate_anchor mu aL aR qL qR level a0 rho hA
  have hClosureV : closure A ⊆ V := closure_minimal (fun _ hw => hw.2) hCompact.isClosed
  obtain ⟨hya, hyq, hyt, hys, hyo, hym, hyd, hyI⟩ := hPoints y hyQV.2
  refine ⟨y, hy, hyQV, hya, hyq, hyt, hys, hyo, hym, hyd, hyI, ?_⟩
  intro w hw
  have hwI := (hPoints w (hClosureV hw)).2.2.2.2.2.2.2
  refine ⟨hmin w hw, EReal.coe_le_coe_iff.mp ?_⟩
  rw [← hyI, ← hwI]
  exact hmin w hw

end
end Shao.OQ3
