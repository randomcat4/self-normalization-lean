import Shao.OQ3.PhysicalWindowCellRateAnchors
import Shao.OQ3.PhysicalWindowRateFloor

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_physical_window_rate_floor_anchors
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
      0 < -theta.2 ∧ (0 < Lambda1 → ∃ cap rho : ℝ, 0 < cap ∧ 0 < rho ∧ rho ≤ cap ∧
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
        (∀ w ∈ V, J (a0, a0 ^ 2 / level ^ 2) ≤ J w) ∧
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
    open_domain_physical_window_cell_rate_anchors mu theta htheta hdet
      level a0 hlevel ha0 hnegative hmean hsaddle
  refine ⟨L, e, hL, he, ht, hs, H.1, ?_⟩
  intro hLambda
  obtain ⟨cap, hcap, hVcap, _, hpCap, _⟩ := H.2 hLambda
  obtain ⟨Lt, et, hLt, _, _, _, _, Ht⟩ :=
    open_domain_quadratic_tilt_boundary_lower_bound mu theta htheta hdet.ne'
      level a0 hlevel ha0 hnegative hmean hsaddle
  have hLeq : Lt = L := by
    apply DFunLike.ext
    intro x
    exact congrArg (fun f : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) => f x)
      (hLt.trans hL.symm)
  subst Lt
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
  let Ft : (ℝ × ℝ) → ℝ := fun u =>
    let w : ℝ × ℝ := (a0 + u.1, (a0 + u.1) ^ 2 / level ^ 2 - u.2)
    (et.symm w).1 * w.1 + (et.symm w).2 * w.2 - K (et.symm w)
  have hlocal : ∀ᶠ u : ℝ × ℝ in 𝓝 (0, 0),
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
        (a0 + u.1, (a0 + u.1) ^ 2 / level ^ 2 - u.2) = (Ft u : EReal) :=
    Ht.2.2.2.2.1
  obtain ⟨delta, c, hdelta, hc, hgrowth⟩ := Ht.2.2.2.2.2.2 hLambda
  obtain ⟨rho, hrho, hrhocap, _, hfloor⟩ :=
    actual_parabola_analytic_rate_floor_of_boundary_lower_bound
      mu level a0 cap delta c hcap hdelta hc Ft hlocal hgrowth J
      (fun w hw => (hpCap w hw).2.2.2.2.2.2.2)
  let Ucap : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ cap ∧
    |w.1 ^ 2 / level ^ 2 - w.2| ≤ cap}
  let Vcap : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ cap ∧
    0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ cap}
  let U : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
    |w.1 ^ 2 / level ^ 2 - w.2| ≤ rho}
  let Tail : Set (ℝ × ℝ) := {w | 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
  let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
    0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
  let Theta : Set (ℝ × ℝ) := e.symm '' V
  have hsubset : V ⊆ Vcap := fun w hw =>
    ⟨hw.1.trans hrhocap, hw.2.1, hw.2.2.trans hrhocap⟩
  have hVeq : V = U ∩ Tail := by
    ext w
    constructor
    · intro hw
      have hold : w ∈ Ucap ∩ Tail := hVcap ▸ hsubset hw
      exact ⟨⟨hw.1, by
        rw [abs_of_nonneg hw.2.1]
        exact hw.2.2⟩, hold.2⟩
    · intro hw
      have hucap : w ∈ Ucap := ⟨hw.1.1.trans hrhocap, hw.1.2.trans hrhocap⟩
      have heqcap : Vcap = Ucap ∩ Tail := hVcap
      have hold : w ∈ Vcap := heqcap.symm ▸
        (show w ∈ Ucap ∩ Tail from ⟨hucap, hw.2⟩)
      exact ⟨hw.1.1, hold.2.1, (le_abs_self _).trans hw.1.2⟩
  have hcompact : IsCompact V :=
    actual_parabola_window_isCompact level a0 rho hrho.le
  have hpv : ∀ w ∈ V, 0 < w.1 ∧ 0 < w.2 ∧ w ∈ e.target ∧
      e.symm w ∈ e.source ∧ e.symm w ∈ Omega ∧ means (e.symm w) = w ∧
      0 < (parabolaCovariance (nu (e.symm w))).det ∧
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w =
        (J w : EReal) := fun w hw => hpCap w (hsubset hw)
  have hVtarget : V ⊆ e.target := fun w hw => (hpv w hw).2.2.1
  have hThetaCompact : IsCompact Theta :=
    hcompact.image_of_continuousOn (e.continuousOn_symm.mono hVtarget)
  have hcenterV : (a0, a0 ^ 2 / level ^ 2) ∈ V := by
    exact ⟨by simpa only [sub_self, abs_zero] using hrho.le,
      by simp, by simpa only [sub_self] using hrho.le⟩
  have hthetaImage : e theta = (a0, a0 ^ 2 / level ^ 2) := by
    rw [he]
    exact hmean
  have hThetaCenter : theta ∈ Theta := by
    refine ⟨(a0, a0 ^ 2 / level ^ 2), hcenterV, ?_⟩
    rw [← hthetaImage]
    exact e.left_inv ht
  have hThetaSubset : Theta ⊆ Omega := by
    intro p hp
    obtain ⟨w, hw, rfl⟩ := hp
    exact (hpv w hw).2.2.2.2.1
  have hThetaPoints : ∀ p ∈ Theta, p ∈ e.source ∧ means p ∈ V ∧
      0 < (parabolaCovariance (nu p)).det := by
    intro p hp
    obtain ⟨w, hw, rfl⟩ := hp
    obtain ⟨_, _, _, hsource, _, hm, hdet', _⟩ := hpv w hw
    exact ⟨hsource, hm.symm ▸ hw, hdet'⟩
  refine ⟨cap, rho, hcap, hrho, hrhocap, hThetaCompact, hThetaCenter,
    hThetaSubset, hThetaPoints, (fun w hw => ⟨w, hw, rfl⟩), hVeq,
    hcompact, hpv, hfloor, ?_⟩
  intro aL aR qL qR
  let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩ V
  let Q : Set (ℝ × ℝ) := Set.Icc aL aR ×ˢ Set.Icc qL qR
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
