import Shao.OQ3.OpenDomainBoundaryLaplaceIntegral
import Shao.OQ3.BoundaryLaplaceNormalization

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_boundary_laplace_original_strip
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
        let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
          w.1 ^ 2 / level ^ 2 - rho ≤ w.2 ∧ w.2 ≤ w.1 ^ 2 / level ^ 2}
        (∀ w ∈ V, w ∈ e.target ∧ e.symm w ∈ e.source ∧ e.symm w ∈ Omega ∧
          means (e.symm w) = w ∧ 0 < (parabolaCovariance (nu (e.symm w))).det ∧
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w = (J w : EReal)) ∧
        ∀ t : ℝ, 0 < t → t ≤ 1 →
          let W : (ℝ × ℝ) → ℝ := fun w => B w * Real.exp (-J w / t ^ 2)
          let Ln : ℝ := (1 / (2 * Real.pi * t ^ 2)) * ∫ w : ℝ × ℝ in V, W w ∂m0
          let main : ℝ := t * Real.exp (-J0 / t ^ 2) * (C0 / (2 * Real.pi))
          IntegrableOn W V m0 ∧ 0 < main ∧ |Ln / main - 1| ≤ C * t) := by
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
  obtain ⟨L, e, hL, he, hs, hsOmega, hlambda, _, hA0, _, hresult⟩ :=
    open_domain_boundary_laplace_cutoff_integral mu theta htheta hdet
      level a0 hlevel ha0 hnegative hmean hsaddle
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
  obtain ⟨hCs, rho, C, hrho, hC, hwindow, hscaled⟩ := hresult hcurvature
  let Cs : ℝ := A (0, 0) * (Real.sqrt (2 * Real.pi / Lambda1) / (-theta.2))
  have hA0exact : A (0, 0) = (Real.sqrt D.det)⁻¹ := hA0
  have hC0eq : Cs = C0 := by dsimp only [Cs, C0]; rw [hA0exact]
  have hC0 : 0 < C0 := by rw [← hC0eq]; exact hCs
  let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
    w.1 ^ 2 / level ^ 2 - rho ≤ w.2 ∧ w.2 ≤ w.1 ^ 2 / level ^ 2}
  let R : Set (ℝ × ℝ) := {w | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho}
  have himage : G '' R = V := boundary_rate_chart_rectangle_image a0 level rho
  refine ⟨hC0, rho, C, hrho, hC, ?_, ?_⟩
  · intro w hw
    have hwV : w ∈ V := hw
    rw [← himage] at hwV
    obtain ⟨u, hu, huEq⟩ := hwV
    rw [← huEq]
    exact hwindow u.1 u.2 hu.1 hu.2.1 hu.2.2
  · apply boundary_laplace_original_strip_transfer J B a0 level rho C0 C hC0
    intro t ht ht1
    obtain ⟨hI, _, hRel⟩ := hscaled t ht ht1
    refine ⟨hI, ?_⟩
    rw [← hC0eq]
    exact hRel

end
end Shao.OQ3
