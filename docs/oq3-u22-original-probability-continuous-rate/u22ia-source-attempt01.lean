import Shao.OQ3.BoundedPhysicalWindowCovarianceGaussianSum
import Shao.OQ3.ActualGaussianIntegralSumComparison

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators RealInnerProductSpace NNReal Topology ContDiff
noncomputable section

set_option maxHeartbeats 2000000 in
theorem bounded_physical_window_continuous_rate_integral
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
        let A : (ℝ × ℝ) → ℝ := fun w =>
          (Real.sqrt (parabolaCovariance (nu (e.symm w))).det)⁻¹
        ∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, 2 ≤ N ∧
          ∀ n : ℕ, N ≤ n →
            let B : ℝ := (2 * rho + 2) * ((|a0| + rho) ^ 2 / level ^ 2 + rho + 2)
            let P : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => mu)
            let M : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
              ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
            let T : (ℝ × ℝ) → ℝ := fun w =>
              A w * Real.exp (-(n : ℝ) * (J w - J (a0, a0 ^ 2 / level ^ 2)))
            let Ln : ℝ := ((n : ℝ) / (2 * Real.pi)) * ∫ w : ℝ × ℝ in V, T w
            0 < B ∧ IntegrableOn T V ∧ 0 ≤ Ln ∧
              |Real.exp ((n : ℝ) * J (a0, a0 ^ 2 / level ^ 2)) * P.real (M ⁻¹' V) - Ln| ≤
                (C / (n : ℝ)) * Ln + B * epsilon / (n : ℝ)
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
    bounded_physical_window_covariance_gaussian_grid_sum mu theta htheta hdet
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
  intro A
  obtain ⟨lo, hi, hlo, hhi, hbounds, E, hE, C0, hC0, hApprox⟩ := hGaussian
  have hTarget : V ⊆ e.target := fun w hw => (hVPoints w hw).2.2.1
  have hPositive : ∀ w ∈ V, 0 < (parabolaCovariance (nu (e.symm w))).det :=
    fun w hw => (hVPoints w hw).2.2.2.2.2.2.1
  obtain ⟨C1, hC1, N1, hN1, hIntegral⟩ :=
    actual_mean_chart_gaussian_grid_integral_comparison mu e he hs
      V hVCompact hTarget hPositive
  let C : ℝ := C0 * (1 + C1) + C1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro epsilon hepsilon
  obtain ⟨N0, hN0, hSmall⟩ := hApprox epsilon hepsilon
  refine ⟨max N0 N1, by omega, ?_⟩
  intro n hn B P M T Ln
  have hn0 : N0 ≤ n := (le_max_left N0 N1).trans hn
  have hn1 : N1 ≤ n := (le_max_right N0 N1).trans hn
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  let cell : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
    (Set.Ioc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
      Set.Ioc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))) ∩ V
  obtain ⟨hB, Kcells, hK, hcard, y, hy, hOld⟩ := hSmall n hn0
  let cov : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (nu p)
  let Q : Kcells → (ℝ × ℝ) → ℝ := fun k z =>
    (cov (e.symm (y k)) 1 1 * z.1 ^ 2 -
      2 * cov (e.symm (y k)) 0 1 * z.1 * z.2 +
      cov (e.symm (y k)) 0 0 * z.2 ^ 2) / (cov (e.symm (y k))).det
  let JG : Kcells → ℝ := fun k =>
    ((n : ℝ) / (2 * Real.pi * Real.sqrt (cov (e.symm (y k))).det)) *
      ∫ w : ℝ × ℝ in cell k,
        Real.exp (-(n : ℝ) * ((e.symm (y k)).1 * (w - y k).1 +
          (e.symm (y k)).2 * (w - y k).2) - ((n : ℝ) / 2) * Q k (w - y k))
  let W : Kcells → ℝ := fun k =>
    Real.exp ((n : ℝ) * (J (a0, a0 ^ 2 / level ^ 2) - J (y k)))
  let Gold : ℝ := ∑ k : Kcells, W k * JG k
  have hOldError :
      |Real.exp ((n : ℝ) * J (a0, a0 ^ 2 / level ^ 2)) * P.real (M ⁻¹' V) - Gold| ≤
        (C0 / (n : ℝ)) * Gold + B * epsilon / (n : ℝ) := hOld.2.2
  let g : Kcells → (ℝ × ℝ) → ℝ := fun k w =>
    A (y k) * Real.exp (-(n : ℝ) * (J (y k) +
      ((e.symm (y k)).1 * (w - y k).1 + (e.symm (y k)).2 * (w - y k).2) +
        Q k (w - y k) / 2 - J (a0, a0 ^ 2 / level ^ 2)))
  let Gnew : ℝ := ((n : ℝ) / (2 * Real.pi)) *
    ∑ k : Kcells, ∫ w : ℝ × ℝ in cell k, g k w
  have hInt := hIntegral n hn1 Kcells hK y (fun k => (hy k).2.1)
    (J (a0, a0 ^ 2 / level ^ 2))
  change IntegrableOn T V ∧ (∀ k : Kcells, IntegrableOn (g k) (cell k)) ∧
    0 ≤ Ln ∧ |Gnew - Ln| ≤ (C1 / (n : ℝ)) * Ln at hInt
  have hIdent (k : Kcells) : W k * JG k =
      ((n : ℝ) / (2 * Real.pi)) * ∫ w : ℝ × ℝ in cell k, g k w := by
    let f : (ℝ × ℝ) → ℝ := fun w =>
      Real.exp (-(n : ℝ) * ((e.symm (y k)).1 * (w - y k).1 +
        (e.symm (y k)).2 * (w - y k).2) - ((n : ℝ) / 2) * Q k (w - y k))
    have hFun : g k = fun w => (W k * A (y k)) * f w := by
      funext w
      dsimp only [g, W, f]
      rw [show -(n : ℝ) * (J (y k) +
          ((e.symm (y k)).1 * (w - y k).1 + (e.symm (y k)).2 * (w - y k).2) +
            Q k (w - y k) / 2 - J (a0, a0 ^ 2 / level ^ 2)) =
          (n : ℝ) * (J (a0, a0 ^ 2 / level ^ 2) - J (y k)) +
            (-(n : ℝ) * ((e.symm (y k)).1 * (w - y k).1 +
              (e.symm (y k)).2 * (w - y k).2) - ((n : ℝ) / 2) * Q k (w - y k)) by ring,
        Real.exp_add]
      ring
    have hCoef : (n : ℝ) / (2 * Real.pi * Real.sqrt (cov (e.symm (y k))).det) =
        ((n : ℝ) / (2 * Real.pi)) * A (y k) := by
      simp only [A, cov, div_eq_mul_inv, _root_.mul_inv_rev]
      ring
    change W k * (_ * ∫ w : ℝ × ℝ in cell k, f w) = _
    rw [hCoef, hFun, integral_const_mul]
    ring
  have hGold : Gold = Gnew := by
    dsimp only [Gold, Gnew]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => hIdent k)
  have hError : |Gold - Ln| ≤ (C1 / (n : ℝ)) * Ln := by
    rw [hGold]
    exact hInt.2.2.2
  have hLn : 0 ≤ Ln := hInt.2.2.1
  have hGoldUpper : Gold ≤ (1 + C1) * Ln := by
    have hSub : Gold - Ln ≤ (C1 / (n : ℝ)) * Ln := (le_abs_self _).trans hError
    have hRatio : C1 / (n : ℝ) ≤ C1 := div_le_self hC1.le hnR
    have hBound := mul_le_mul_of_nonneg_right hRatio hLn
    nlinarith
  refine ⟨hB, hInt.1, hLn, ?_⟩
  calc
    |Real.exp ((n : ℝ) * J (a0, a0 ^ 2 / level ^ 2)) * P.real (M ⁻¹' V) - Ln| ≤
        |Real.exp ((n : ℝ) * J (a0, a0 ^ 2 / level ^ 2)) * P.real (M ⁻¹' V) - Gold| +
          |Gold - Ln| := abs_sub_le _ _ _
    _ ≤ ((C0 / (n : ℝ)) * Gold + B * epsilon / (n : ℝ)) +
          (C1 / (n : ℝ)) * Ln := add_le_add hOldError hError
    _ ≤ ((C0 / (n : ℝ)) * ((1 + C1) * Ln) + B * epsilon / (n : ℝ)) +
          (C1 / (n : ℝ)) * Ln :=
      add_le_add_right (add_le_add_right
        (mul_le_mul_of_nonneg_left hGoldUpper (div_nonneg hC0.le hnpos.le)) _) _
    _ = (C / (n : ℝ)) * Ln + B * epsilon / (n : ℝ) := by dsimp only [C]; ring

end
end Shao.OQ3
