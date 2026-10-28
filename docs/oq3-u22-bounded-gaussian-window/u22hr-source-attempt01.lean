import Shao.OQ3.BoundedPhysicalWindowActualGaussian
import Shao.OQ3.PhysicalGridWeightedReconstruction

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators RealInnerProductSpace NNReal Topology ContDiff
noncomputable section

set_option maxHeartbeats 2000000 in
theorem bounded_physical_window_actual_gaussian_grid_sum
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
          ∀ n : ℕ, N ≤ n →
            let cell : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
              (Set.Ioc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
                Set.Ioc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))) ∩ V
            let B : ℝ := (2 * rho + 2) * ((|a0| + rho) ^ 2 / level ^ 2 + rho + 2)
            let P : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => mu)
            let M : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
              ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
            0 < B ∧ ∃ Kcells : Finset (ℤ × ℤ),
              (∀ k : ℤ × ℤ, k ∈ Kcells ↔ (cell k).Nonempty) ∧
              (Kcells.card : ℝ) ≤ B * (n : ℝ) ^ 2 ∧
              ∃ y : Kcells → V,
                (∀ k : Kcells,
                  (y k : ℝ × ℝ) ∈ closure (cell k) ∧
                  (y k : ℝ × ℝ) ∈
                    Set.Icc ((k.val.1 : ℝ) / (n : ℝ)) (((k.val.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
                    Set.Icc ((k.val.2 : ℝ) / (n : ℝ)) (((k.val.2 : ℝ) + 1) / (n : ℝ)) ∧
                  ∀ w ∈ closure (cell k), J (y k) ≤ J w) ∧
                let F : Kcells → (ℝ × ℝ) → (ℝ × ℝ) := fun k w =>
                  Real.sqrt (n : ℝ) • E (pOf (y k)) (w - means (pOf (y k)))
                let g : Kcells → (ℝ × ℝ) → ℝ := fun k z =>
                  Real.exp (-Real.sqrt (n : ℝ) *
                    ((pOf (y k) : ℝ × ℝ).1 * ((E (pOf (y k))).symm z).1 +
                      (pOf (y k) : ℝ × ℝ).2 * ((E (pOf (y k))).symm z).2))
                let JG : Kcells → ℝ := fun k =>
                  ∫ z : ℝ × ℝ, ((F k '' cell k).indicator (g k)) z * phi z
                let W : Kcells → ℝ := fun k =>
                  Real.exp ((n : ℝ) * (J (a0, a0 ^ 2 / level ^ 2) - J (y k)))
                let G : ℝ := ∑ k : Kcells, W k * JG k
                (∀ k : Kcells, 0 ≤ JG k ∧ 0 < W k ∧ W k ≤ 1) ∧ 0 ≤ G ∧
                  |Real.exp ((n : ℝ) * J (a0, a0 ^ 2 / level ^ 2)) * P.real (M ⁻¹' V) - G| ≤
                    (C / (n : ℝ)) * G + B * epsilon / (n : ℝ)
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
    bounded_physical_window_actual_gaussian_anchors mu theta htheta hdet
      level a0 hlevel ha0 hnegative hmean hsaddle
        supportRadius hSupport hbounded beta c R hbeta hbetaUpper hc hR hWC
  refine ⟨L, e, hL, he, ht, hs, ?_⟩
  intro K J v Lambda1
  refine ⟨H.1, ?_⟩
  intro hLambda
  obtain ⟨cap, rho, hcap, hrho, hrhocap, hGaussian, hCompactTheta, hThetaCenter,
      hThetaSub, hThetaPoints, hImage, hVeq, hVCompact, hVPoints,
      hRateFloor, hAnchors⟩ := H.2 hLambda
  refine ⟨cap, rho, hcap, hrho, hrhocap, ?_⟩
  intro U Tail V Theta
  refine ⟨?_, hCompactTheta, hThetaCenter, hThetaSub, hThetaPoints,
    hImage, hVeq, hVCompact, hVPoints, hRateFloor, hAnchors⟩
  intro cov sd tr whitening pOf phi
  obtain ⟨lo, hi, hlo, hhi, hbounds, E, hE, C, hC, hApprox⟩ := hGaussian
  refine ⟨lo, hi, hlo, hhi, hbounds, E, hE, C, hC, ?_⟩
  intro epsilon hepsilon
  obtain ⟨N, hN, hSmall⟩ := hApprox epsilon hepsilon
  refine ⟨N, hN, ?_⟩
  intro n hn cell B P M
  have hn1 : 1 ≤ n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨hB, Kcells, hK, hcard, hsum, _⟩ :=
    iid_parabola_finite_grid_weighted_reconstruction mu n hn1 level a0 rho hrho.le
  refine ⟨hB, Kcells, hK, hcard, ?_⟩
  have hwidth (k : ℤ) : ((k : ℝ) + 1) / (n : ℝ) - (k : ℝ) / (n : ℝ) ≤
      1 / (n : ℝ) := by
    have hid : ((k : ℝ) + 1) / (n : ℝ) - (k : ℝ) / (n : ℝ) =
        1 / (n : ℝ) := by ring
    exact hid.le
  have hc (k : Kcells) := hSmall n hn
    ((k.val.1 : ℝ) / (n : ℝ)) (((k.val.1 : ℝ) + 1) / (n : ℝ))
    ((k.val.2 : ℝ) / (n : ℝ)) (((k.val.2 : ℝ) + 1) / (n : ℝ))
    (hwidth k.val.1) (hwidth k.val.2) ((hK k.val).1 k.property)
  let y : Kcells → V := fun k => Classical.choose (hc k)
  refine ⟨y, (fun k => ⟨(Classical.choose_spec (hc k)).1,
    (Classical.choose_spec (hc k)).2.1, (Classical.choose_spec (hc k)).2.2.1⟩), ?_⟩
  intro F g JG W G
  have hLocal (k : Kcells) : 0 ≤ JG k ∧
      |Real.exp ((n : ℝ) * J (y k)) * P.real (M ⁻¹' cell k) - JG k| ≤
        (C / (n : ℝ)) * JG k + epsilon / (n : ℝ) ^ 3 := by
    have h := (Classical.choose_spec (hc k)).2.2.2
    dsimp only at h
    rcases h with ⟨_, _, _, _, _, hJG, _, herr⟩
    exact ⟨hJG, herr.le⟩
  have hWpos (k : Kcells) : 0 < W k := Real.exp_pos _
  have hWle (k : Kcells) : W k ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonneg_of_nonpos hnpos.le
      (sub_nonpos.mpr (hRateFloor (y k) (y k).property))
  have hG : 0 ≤ G := Finset.sum_nonneg
    (fun k _ => mul_nonneg (hWpos k).le (hLocal k).1)
  refine ⟨(fun k => ⟨(hLocal k).1, hWpos k, hWle k⟩), hG, ?_⟩
  have hScale (k : Kcells) :
      W k * Real.exp ((n : ℝ) * J (y k)) =
        Real.exp ((n : ℝ) * J (a0, a0 ^ 2 / level ^ 2)) := by
    change Real.exp ((n : ℝ) * (J (a0, a0 ^ 2 / level ^ 2) - J (y k))) * _ = _
    rw [← Real.exp_add]
    congr 1
    ring
  have herror (k : Kcells) :
      |Real.exp ((n : ℝ) * J (a0, a0 ^ 2 / level ^ 2)) *
        P.real (M ⁻¹' cell k) - W k * JG k| ≤
          (C / (n : ℝ)) * (W k * JG k) + epsilon / (n : ℝ) ^ 3 := by
    have hid : Real.exp ((n : ℝ) * J (a0, a0 ^ 2 / level ^ 2)) *
        P.real (M ⁻¹' cell k) - W k * JG k =
          W k * (Real.exp ((n : ℝ) * J (y k)) * P.real (M ⁻¹' cell k) - JG k) := by
      rw [mul_sub, ← mul_assoc, hScale]
    rw [hid, abs_mul, abs_of_pos (hWpos k)]
    calc
      W k * |Real.exp ((n : ℝ) * J (y k)) * P.real (M ⁻¹' cell k) - JG k|
          ≤ W k * ((C / (n : ℝ)) * JG k + epsilon / (n : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left (hLocal k).2 (hWpos k).le
      _ = (C / (n : ℝ)) * (W k * JG k) + W k * (epsilon / (n : ℝ) ^ 3) := by ring
      _ ≤ (C / (n : ℝ)) * (W k * JG k) + epsilon / (n : ℝ) ^ 3 := by
        apply add_le_add_left
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hWle k)
          (div_nonneg hepsilon.le (pow_nonneg hnpos.le 3))
  have hSumP : P.real (M ⁻¹' V) = ∑ k : Kcells, P.real (M ⁻¹' cell k) := by
    simpa only [Finset.sum_coe_sort] using hsum
  have hSumError : Real.exp ((n : ℝ) * J (a0, a0 ^ 2 / level ^ 2)) *
      P.real (M ⁻¹' V) - G =
        ∑ k : Kcells, (Real.exp ((n : ℝ) * J (a0, a0 ^ 2 / level ^ 2)) *
          P.real (M ⁻¹' cell k) - W k * JG k) := by
    rw [hSumP, Finset.mul_sum, Finset.sum_sub_distrib]
  calc
    |Real.exp ((n : ℝ) * J (a0, a0 ^ 2 / level ^ 2)) * P.real (M ⁻¹' V) - G|
        = |∑ k : Kcells, (Real.exp ((n : ℝ) * J (a0, a0 ^ 2 / level ^ 2)) *
          P.real (M ⁻¹' cell k) - W k * JG k)| := congrArg abs hSumError
    _ ≤ ∑ k : Kcells, |Real.exp ((n : ℝ) * J (a0, a0 ^ 2 / level ^ 2)) *
          P.real (M ⁻¹' cell k) - W k * JG k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Kcells, ((C / (n : ℝ)) * (W k * JG k) + epsilon / (n : ℝ) ^ 3) :=
      Finset.sum_le_sum (fun k _ => herror k)
    _ = (C / (n : ℝ)) * G + (Kcells.card : ℝ) * (epsilon / (n : ℝ) ^ 3) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ (C / (n : ℝ)) * G + (B * (n : ℝ) ^ 2) * (epsilon / (n : ℝ) ^ 3) :=
      add_le_add_left (mul_le_mul_of_nonneg_right hcard
        (div_nonneg hepsilon.le (pow_nonneg hnpos.le 3))) _
    _ = (C / (n : ℝ)) * G + B * epsilon / (n : ℝ) := by
      congr 1
      field_simp [ne_of_gt hnpos]
      <;> ring

end
end Shao.OQ3
