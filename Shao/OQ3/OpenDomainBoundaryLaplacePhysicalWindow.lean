import Shao.OQ3.OpenDomainBoundaryLaplaceWindow
import Shao.OQ3.BoundaryLaplaceEventGeometry
import Shao.OQ3.BoundaryLaplaceNatNormalization

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_boundary_laplace_nat_physical_window
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
      0 < -theta.2 ∧ (0 < Lambda1 → 0 < C0 ∧ ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧
        let U : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
          |w.1 ^ 2 / level ^ 2 - w.2| ≤ rho}
        let Tail : Set (ℝ × ℝ) := {w | 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
        let V : Set (ℝ × ℝ) := U ∩ Tail
        IsClosed U ∧ (a0, a0 ^ 2 / level ^ 2) ∈ interior U ∧
        (∀ w ∈ U, 0 < w.1 ∧ 0 < w.2) ∧
        V = {w | |w.1 - a0| ≤ rho ∧
          w.1 ^ 2 / level ^ 2 - rho ≤ w.2 ∧ w.2 ≤ w.1 ^ 2 / level ^ 2} ∧
        (∀ w ∈ V, w ∈ e.target ∧ e.symm w ∈ e.source ∧ e.symm w ∈ Omega ∧
          means (e.symm w) = w ∧ 0 < (parabolaCovariance (nu (e.symm w))).det ∧
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w = (J w : EReal)) ∧
        ∀ n : ℕ, 1 ≤ n →
          let W : (ℝ × ℝ) → ℝ := fun w => B w * Real.exp (-(n : ℝ) * J w)
          let Ln : ℝ := ((n : ℝ) / (2 * Real.pi)) * ∫ w : ℝ × ℝ in V, W w ∂m0
          let main : ℝ := Real.exp (-(n : ℝ) * J0) /
            (Real.sqrt (2 * Real.pi * (n : ℝ)) * (-theta.2) * Real.sqrt D.det * Real.sqrt Lambda1)
          IntegrableOn W V m0 ∧ 0 < main ∧ |Ln / main - 1| ≤ C / Real.sqrt (n : ℝ)) := by
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
  obtain ⟨eta, heta, _, hphysical⟩ := exists_positive_parabola_window
    level a0 1 hlevel ha0 (by norm_num)
  obtain ⟨L, e, hL, he, hs, hsOmega, hlambda, _, hA0, _, hresult⟩ :=
    open_domain_boundary_laplace_cutoff_integral_below mu theta htheta hdet
      level a0 hlevel ha0 hnegative hmean hsaddle eta heta
  let K : (ℝ × ℝ) → ℝ := fun p => Real.log
    (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
  let J : (ℝ × ℝ) → ℝ := fun w =>
    (e.symm w).1 * w.1 + (e.symm w).2 * w.2 - K (e.symm w)
  let B : (ℝ × ℝ) → ℝ := fun w =>
    (Real.sqrt (parabolaCovariance (nu (e.symm w))).det)⁻¹
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
    (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
  let A : (ℝ × ℝ) → ℝ := fun w => B (G w)
  let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
  let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
    (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
  let C0 : ℝ := (Real.sqrt D.det)⁻¹ * (Real.sqrt (2 * Real.pi / Lambda1) / (-theta.2))
  let J0 : ℝ := J (a0, a0 ^ 2 / level ^ 2)
  let m0 : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
  refine ⟨L, e, hL, he, hs, hsOmega, hlambda, ?_⟩
  intro hcurvature
  obtain ⟨hCs, rho, C, hrho, hrEta, hC, hwindow, hscaled⟩ := hresult hcurvature
  let Cs : ℝ := A (0, 0) * (Real.sqrt (2 * Real.pi / Lambda1) / (-theta.2))
  have hA0exact : A (0, 0) = (Real.sqrt D.det)⁻¹ := hA0
  have hC0eq : Cs = C0 := by dsimp only [Cs, C0]; rw [hA0exact]
  have hC0 : 0 < C0 := by rw [← hC0eq]; exact hCs
  let strip : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
    w.1 ^ 2 / level ^ 2 - rho ≤ w.2 ∧ w.2 ≤ w.1 ^ 2 / level ^ 2}
  let U : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
    |w.1 ^ 2 / level ^ 2 - w.2| ≤ rho}
  let Tail : Set (ℝ × ℝ) := {w | 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
  let V : Set (ℝ × ℝ) := U ∩ Tail
  have hphysicalRho : ∀ r z : ℝ, |r| ≤ rho → |z| ≤ rho →
      0 < a0 + r ∧ 0 < (a0 + r) ^ 2 / level ^ 2 - z := by
    intro r z hr hz
    have hp := hphysical r z (hr.trans hrEta) (hz.trans hrEta)
    exact ⟨hp.1, hp.2.1⟩
  obtain ⟨hUclosed, hUinterior, hUpositive, hstripEq⟩ :=
    positive_parabola_window_event_geometry level a0 rho hlevel hrho hphysicalRho
  have hVeq : V = strip := hstripEq.symm
  let R : Set (ℝ × ℝ) := {w | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho}
  have himage : G '' R = strip := boundary_rate_chart_rectangle_image a0 level rho
  have hreal := boundary_laplace_original_strip_transfer J B a0 level rho C0 C hC0 (by
    intro t ht ht1
    obtain ⟨hI, _, hRel⟩ := hscaled t ht ht1
    refine ⟨hI, ?_⟩
    rw [← hC0eq]
    exact hRel)
  have hnat := boundary_laplace_nat_normalization J B strip J0 C0 C hreal
  refine ⟨hC0, rho, C, hrho, hC, hUclosed, hUinterior, hUpositive, hVeq, ?_, ?_⟩
  · intro w hw
    have hwStrip : w ∈ strip := by rw [← hVeq]; exact hw
    rw [← himage] at hwStrip
    obtain ⟨u, hu, huEq⟩ := hwStrip
    rw [← huEq]
    exact hwindow u.1 u.2 hu.1 hu.2.1 hu.2.2
  · intro n hn
    obtain ⟨hI, hP, hE⟩ := hnat n hn
    have hconstant : Real.exp (-(n : ℝ) * J0) * (C0 / (2 * Real.pi)) / Real.sqrt (n : ℝ) =
        Real.exp (-(n : ℝ) * J0) /
          (Real.sqrt (2 * Real.pi * (n : ℝ)) * (-theta.2) * Real.sqrt D.det * Real.sqrt Lambda1) :=
      (boundary_laplace_source_leading_constant D.det (-theta.2) Lambda1).2 n J0
    rw [← hVeq] at hI hE
    rw [hconstant] at hP hE
    exact ⟨hI, hP, hE⟩

end
end Shao.OQ3
