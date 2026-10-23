import Shao.OQ3.OpenDomainBoundaryLaplacePhysicalWindow
import Shao.OQ3.ParabolaCellRateAnchor
import Shao.OQ3.ParabolaFiniteGridCover

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_physical_window_cell_rate_anchors
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
      let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
      let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
        (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
      0 < -theta.2 ∧ (0 < Lambda1 → ∃ rho : ℝ, 0 < rho ∧
        let U : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
          |w.1 ^ 2 / level ^ 2 - w.2| ≤ rho}
        let Tail : Set (ℝ × ℝ) := {w | 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
        let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
          0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
        V = U ∩ Tail ∧ IsCompact V ∧
        (∀ w ∈ V, 0 < w.1 ∧ 0 < w.2 ∧ w ∈ e.target ∧ e.symm w ∈ e.source ∧
          e.symm w ∈ Omega ∧ means (e.symm w) = w ∧
          0 < (parabolaCovariance (nu (e.symm w))).det ∧
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w =
            (J w : EReal)) ∧
        ∀ aL aR qL qR : ℝ,
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
              J y ≤ J w) := by
  dsimp only
  obtain ⟨L, e, hL, he, ht, hs, H⟩ :=
    open_domain_boundary_laplace_nat_physical_window mu theta htheta hdet
      level a0 hlevel ha0 hnegative hmean hsaddle
  refine ⟨L, e, hL, he, ht, hs, H.1, ?_⟩
  intro hLambda
  obtain ⟨_, rho, C, hrho, hC, hwindow⟩ := H.2 hLambda
  obtain ⟨hclosed, hcenter, hpos, hVeq, hpatch, hLaplace⟩ := hwindow
  let Omega : Set (ℝ × ℝ) := interior
    (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
  let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
    mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
    (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
  let K : (ℝ × ℝ) → ℝ := fun p => Real.log
    (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
  let J : (ℝ × ℝ) → ℝ := fun w =>
    (e.symm w).1 * w.1 + (e.symm w).2 * w.2 - K (e.symm w)
  let U : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
    |w.1 ^ 2 / level ^ 2 - w.2| ≤ rho}
  let Tail : Set (ℝ × ℝ) := {w | 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
  let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
    0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
  have hphysical : U ∩ Tail = {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
      w.1 ^ 2 / level ^ 2 - rho ≤ w.2 ∧ w.2 ≤ w.1 ^ 2 / level ^ 2} := hVeq
  have heq : V = U ∩ Tail := by
    rw [hphysical]
    ext w
    constructor
    · intro hw
      exact ⟨hw.1, by linarith [hw.2.2], by linarith [hw.2.1]⟩
    · intro hw
      exact ⟨hw.1, by linarith [hw.2.2], by linarith [hw.2.1]⟩
  have hcompact : IsCompact V :=
    actual_parabola_window_isCompact level a0 rho hrho.le
  have hpv : ∀ w ∈ V, 0 < w.1 ∧ 0 < w.2 ∧
      w ∈ e.target ∧ e.symm w ∈ e.source ∧ e.symm w ∈ Omega ∧
      means (e.symm w) = w ∧ 0 < (parabolaCovariance (nu (e.symm w))).det ∧
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w =
        (J w : EReal) := by
    intro w hw
    have hwphysical : w ∈ U ∩ Tail := heq ▸ hw
    have hp := hpos w hwphysical.1
    exact ⟨hp.1, hp.2, hpatch w hwphysical⟩
  refine ⟨rho, hrho, heq, hcompact, hpv, ?_⟩
  intro aL aR qL qR
  let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩ V
  let Q : Set (ℝ × ℝ) := Set.Icc aL aR ×ˢ Set.Icc qL qR
  change A.Nonempty → ∃ y ∈ closure A, y ∈ Q ∩ V ∧
    0 < y.1 ∧ 0 < y.2 ∧ y ∈ e.target ∧ e.symm y ∈ e.source ∧
    e.symm y ∈ Omega ∧ means (e.symm y) = y ∧
    0 < (parabolaCovariance (nu (e.symm y))).det ∧
    Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y =
      (J y : EReal) ∧
    ∀ w ∈ closure A,
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y ≤
        Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w ∧
      J y ≤ J w
  intro hA
  obtain ⟨_, y, hy, hyQV, hmin⟩ :=
    actual_parabola_cell_closure_rate_anchor mu aL aR qL qR level a0 rho hA
  have hclosureV : closure A ⊆ V :=
    closure_minimal (fun w hw => hw.2) hcompact.isClosed
  obtain ⟨hya, hyq, hyt, hys, hyo, hym, hyd, hyI⟩ := hpv y hyQV.2
  refine ⟨y, hy, hyQV, hya, hyq, hyt, hys, hyo, hym, hyd, hyI, ?_⟩
  intro w hw
  have hwI := (hpv w (hclosureV hw)).2.2.2.2.2.2.2
  refine ⟨hmin w hw, EReal.coe_le_coe_iff.mp ?_⟩
  rw [← hyI, ← hwI]
  exact hmin w hw

end
end Shao.OQ3
