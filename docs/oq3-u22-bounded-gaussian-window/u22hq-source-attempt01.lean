import Shao.OQ3.PhysicalWindowRateFloorAnchors
import Shao.OQ3.BoundedCompactPhysicalCellGaussian

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators RealInnerProductSpace NNReal Topology ContDiff
noncomputable section

set_option maxHeartbeats 2000000 in
theorem bounded_physical_window_actual_gaussian_anchors
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
    (supportRadius : ℝ) (hSupport : 0 ≤ supportRadius)
    (hbounded : ∀ᵐ x ∂mu, |x| ≤ supportRadius)
    (beta c R : ℝ) (hbeta : 0 < beta) (hbetaUpper : beta < (2 : ℝ) / 5)
    (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
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
        (
        let cov : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (nu p)
        let sd : (ℝ × ℝ) → ℝ := fun p =>
          Real.sqrt (cov p 0 0 * cov p 1 1 - (cov p 0 1) ^ 2)
        let tr : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (cov p 0 0 + cov p 1 1 + 2 * sd p)
        let whitening : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
          ![![(cov p 1 1 + sd p) / (sd p * tr p), -(cov p 0 1) / (sd p * tr p)],
            ![-(cov p 0 1) / (sd p * tr p), (cov p 0 0 + sd p) / (sd p * tr p)]]
        let pOf : V → Theta := fun y => ⟨e.symm y, ⟨y, y.property, rfl⟩⟩
        let phi : (ℝ × ℝ) → ℝ := fun z =>
          (1 / (2 * Real.pi)) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)
        ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
          (∀ p ∈ Theta, ∀ xi eta : ℝ,
            lo * (xi ^ 2 + eta ^ 2) ≤
                xi ^ 2 * cov p 0 0 + 2 * xi * eta * cov p 0 1 + eta ^ 2 * cov p 1 1 ∧
              xi ^ 2 * cov p 0 0 + 2 * xi * eta * cov p 0 1 + eta ^ 2 * cov p 1 1 ≤
                hi * (xi ^ 2 + eta ^ 2)) ∧
        ∃ E : Theta → ((ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)),
          (∀ p : Theta,
            (∀ w : ℝ × ℝ, E p w =
              (whitening p 0 0 * w.1 + whitening p 0 1 * w.2,
                whitening p 1 0 * w.1 + whitening p 1 1 * w.2)) ∧
            ‖(E p : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 2 * (1 / Real.sqrt lo) ∧
            ‖((E p).symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 4 * hi * (1 / Real.sqrt lo)) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, 2 ≤ N ∧
          ∀ n : ℕ, N ≤ n → ∀ aL aR qL qR : ℝ,
            aR - aL ≤ 1 / (n : ℝ) → qR - qL ≤ 1 / (n : ℝ) →
            let cellA : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩ V
            let Q : Set (ℝ × ℝ) := Set.Icc aL aR ×ˢ Set.Icc qL qR
            cellA.Nonempty → ∃ y : V,
              (y : ℝ × ℝ) ∈ closure cellA ∧ (y : ℝ × ℝ) ∈ Q ∧
              (∀ w ∈ closure cellA, J y ≤ J w) ∧
              let Qsample : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => nu (pOf y))
              let M : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
                ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
              let T : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
                Real.sqrt (n : ℝ) • E (pOf y) (M z - means (pOf y))
              let law : Measure (ℝ × ℝ) := Qsample.map T
              let P : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => mu)
              let stdCell : Set (ℝ × ℝ) :=
                (fun w : ℝ × ℝ => Real.sqrt (n : ℝ) •
                  E (pOf y) (w - means (pOf y))) '' cellA
              let g : (ℝ × ℝ) → ℝ := fun z => Real.exp (-Real.sqrt (n : ℝ) *
                ((pOf y : ℝ × ℝ).1 * ((E (pOf y)).symm z).1 +
                  (pOf y : ℝ × ℝ).2 * ((E (pOf y)).symm z).2))
              let f : (ℝ × ℝ) → ℝ := stdCell.indicator g
              let J0 : ℝ := ∫ z : ℝ × ℝ, f z * phi z
              IsProbabilityMeasure law ∧ Measurable f ∧ Integrable f ∧ Integrable f law ∧
                Integrable (fun z : ℝ × ℝ => f z * phi z) ∧ 0 ≤ J0 ∧
                  P.real (M ⁻¹' cellA) = Real.exp (-(n : ℝ) * J y) *
                    (∫ z : ℝ × ℝ, f z ∂law) ∧
                  |Real.exp ((n : ℝ) * J y) * P.real (M ⁻¹' cellA) - J0| <
                    (C / (n : ℝ)) * J0 + epsilon / (n : ℝ) ^ 3
        ) ∧
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
  classical
  intro Omega nu means D pr0 pr1 row0 row1
  obtain ⟨L, e, hL, he, ht, hs, H⟩ :=
    open_domain_physical_window_rate_floor_anchors mu theta htheta hdet
      level a0 hlevel ha0 hnegative hmean hsaddle
  refine ⟨L, e, hL, he, ht, hs, ?_⟩
  intro K J v Lambda1
  refine ⟨H.1, ?_⟩
  intro hLambda
  obtain ⟨cap, rho, hcap, hrho, hrhocap, hCompactTheta, hThetaCenter, hThetaSub,
      hThetaPoints, hImage, hVeq, hVCompact, hVPoints, hRateFloor, hAnchors⟩ := H.2 hLambda
  refine ⟨cap, rho, hcap, hrho, hrhocap, ?_⟩
  intro U Tail V Theta
  refine ⟨?_, hCompactTheta, hThetaCenter, hThetaSub, hThetaPoints, hImage,
    hVeq, hVCompact, hVPoints, hRateFloor, hAnchors⟩
  intro cov sd tr whitening pOf phi
  obtain ⟨lo, hi, hlo, hhi, hbounds, E, hE, C, hC, hApprox⟩ :=
    bounded_compact_actual_cell_physical_gaussian_approximation
      mu supportRadius hSupport hbounded theta Theta hCompactTheta hThetaSub
        beta c R hbeta hbetaUpper hc hR level a0 rho hrho.le
          (fun p hp => (hThetaPoints p hp).2.2) hWC
  refine ⟨lo, hi, hlo, hhi, hbounds, E,
    (fun p => ⟨(hE p).1, (hE p).2.1, (hE p).2.2.1⟩), C, hC, ?_⟩
  intro epsilon hepsilon
  obtain ⟨N, hN, hSmall⟩ := hApprox epsilon hepsilon
  refine ⟨N, hN, ?_⟩
  intro n hn aL aR qL qR hawidth hqwidth cellA Q hnonempty
  obtain ⟨y, hyClosure, hyQV, hya, hyq, hyt, hys, hyo, hyMean, hyd, hyRate, hyMin⟩ :=
    hAnchors aL aR qL qR hnonempty
  let yV : V := ⟨y, hyQV.2⟩
  refine ⟨yV, hyClosure, hyQV.1, (fun w hw => (hyMin w hw).2), ?_⟩
  intro Qsample M T law P stdCell g f J0
  have hAtP := hSmall n hn (pOf yV)
  have hyRect : ((∫ x : ℝ, x ∂nu (pOf yV)),
      (∫ x : ℝ, x ^ 2 ∂nu (pOf yV))) ∈ Set.Icc aL aR ×ˢ Set.Icc qL qR := by
    change means (e.symm y) ∈ Q
    rw [hyMean]
    exact hyQV.1
  have hCell := hAtP.2 aL aR qL qR hyRect hawidth hqwidth
  have hRate : (pOf yV : ℝ × ℝ).1 * (∫ x : ℝ, x ∂nu (pOf yV)) +
      (pOf yV : ℝ × ℝ).2 * (∫ x : ℝ, x ^ 2 ∂nu (pOf yV)) - K (pOf yV) = J yV := by
    change (e.symm y).1 * (means (e.symm y)).1 +
      (e.symm y).2 * (means (e.symm y)).2 - K (e.symm y) = J y
    rw [hyMean]
    rfl
  have hData : Measurable f ∧ Integrable f ∧ Integrable f law ∧
      Integrable (fun z : ℝ × ℝ => f z * phi z) ∧ 0 ≤ J0 ∧
        P.real (M ⁻¹' cellA) = Real.exp (-(n : ℝ) *
          ((pOf yV : ℝ × ℝ).1 * (∫ x : ℝ, x ∂nu (pOf yV)) +
            (pOf yV : ℝ × ℝ).2 * (∫ x : ℝ, x ^ 2 ∂nu (pOf yV)) - K (pOf yV))) *
              (∫ z : ℝ × ℝ, f z ∂law) ∧
        |Real.exp ((n : ℝ) *
          ((pOf yV : ℝ × ℝ).1 * (∫ x : ℝ, x ∂nu (pOf yV)) +
            (pOf yV : ℝ × ℝ).2 * (∫ x : ℝ, x ^ 2 ∂nu (pOf yV)) - K (pOf yV))) *
                P.real (M ⁻¹' cellA) - J0| <
                  (C / (n : ℝ)) * J0 + epsilon / (n : ℝ) ^ 3 := hCell
  rw [hRate] at hData
  exact ⟨hAtP.1, hData⟩

end
end Shao.OQ3
