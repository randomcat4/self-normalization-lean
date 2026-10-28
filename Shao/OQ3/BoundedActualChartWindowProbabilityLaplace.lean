import Shao.OQ3.ActualMeanChartCompactLaplaceTiltWindows
import Shao.OQ3.BoundedCompactPhysicalCellGaussian
import Shao.OQ3.PhysicalGridWeightedReconstruction
import Shao.OQ3.StandardizedGaussianCellPullback
import Shao.OQ3.CanonicalPairWhiteningJacobian
import Shao.OQ3.ActualGaussianIntegralSumComparison

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators RealInnerProductSpace NNReal Topology ContDiff
noncomputable section

set_option maxHeartbeats 3000000 in
theorem bounded_actual_chart_window_probability_laplace
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
    (rmax : ℝ) (hrmax : 0 < rmax)
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
      let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
      let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
        (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
      let J0 : ℝ := J (a0, a0 ^ 2 / level ^ 2)
      0 < -theta.2 ∧ (0 < Lambda1 →
        ∃ cap : ℝ, 0 < cap ∧ cap ≤ rmax ∧
          ∀ rho : ℝ, 0 < rho → rho ≤ cap →
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
              (∀ w ∈ V, J0 ≤ J w) ∧
              ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
                let P : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => mu)
                let M : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
                  ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
                let main : ℝ := 1 /
                  (Real.sqrt (2 * Real.pi * (n : ℝ)) * (-theta.2) * Real.sqrt D.det *
                    Real.sqrt Lambda1)
                0 < main ∧
                  |(Real.exp ((n : ℝ) * J0) * P.real (M ⁻¹' V)) / main - 1| ≤
                    C / Real.sqrt (n : ℝ)) := by
  classical
  intro Omega nu means K D pr0 pr1 row0 row1 L hL J v Lambda1 J0
  obtain ⟨hlambda, H⟩ := actual_mean_chart_compact_laplace_tilt_windows
    mu theta htheta hdet level a0 hlevel ha0 hnegative hmean hsaddle
      e he hte hsource rmax hrmax L hL
  refine ⟨hlambda, ?_⟩
  intro hcurvature
  obtain ⟨cap, hcap, hcapMax, _, hAll⟩ := H hcurvature
  refine ⟨cap, hcap, hcapMax, ?_⟩
  intro rho hrho hrhocap U Tail V
  let Theta : Set (ℝ × ℝ) := e.symm '' V
  obtain ⟨hCompactTheta, hThetaCenter, hThetaSub, hThetaPoints, hImage,
      hVeq, hVCompact, hVPoints, hRateFloor, hAnchors, CL, hCL, hLaplace⟩ :=
    hAll rho hrho hrhocap
  refine ⟨hVeq, hVCompact, hVPoints, hRateFloor, ?_⟩
  let cov : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (nu p)
  let pOf : V → Theta := fun y => ⟨e.symm y, ⟨y, y.property, rfl⟩⟩
  let phi : (ℝ × ℝ) → ℝ := fun z =>
    (1 / (2 * Real.pi)) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)
  obtain ⟨lo, hi, hlo, hhi, hbounds, E, hE, CE, hCE, hApprox⟩ :=
    bounded_compact_actual_cell_physical_gaussian_approximation
      mu supportRadius hSupport hbounded theta Theta hCompactTheta hThetaSub
        beta c R hbeta hbetaUpper hc hR level a0 rho hrho.le
          (fun p hp => (hThetaPoints p hp).2.2) hWC
  obtain ⟨NC, hNC, hSmall⟩ := hApprox 1 (by norm_num)
  have hTarget : V ⊆ e.target := fun w hw => (hVPoints w hw).2.2.1
  have hPositive : ∀ w ∈ V, 0 < (parabolaCovariance (nu (e.symm w))).det :=
    fun w hw => (hVPoints w hw).2.2.2.2.2.2.1
  obtain ⟨CV, hCV, NV, hNV, hIntegral⟩ :=
    actual_mean_chart_gaussian_grid_integral_comparison mu e he hsource
      V hVCompact hTarget hPositive
  let CP : ℝ := CE * (1 + CV) + CV
  let Bgrid : ℝ := (2 * rho + 2) * ((|a0| + rho) ^ 2 / level ^ 2 + rho + 2)
  let kDen : ℝ := Real.sqrt (2 * Real.pi) * (-theta.2) * Real.sqrt D.det * Real.sqrt Lambda1
  let Cfinal : ℝ := CP * (1 + CL) + CL + Bgrid * kDen
  have hCP : 0 < CP := by dsimp only [CP]; positivity
  have hBgrid : 0 < Bgrid := by dsimp only [Bgrid]; positivity
  have hkDen : 0 < kDen := by dsimp only [kDen]; positivity
  have hCfinal : 0 < Cfinal := by dsimp only [Cfinal]; positivity
  refine ⟨Cfinal, hCfinal, max NC NV, by omega, ?_⟩
  intro n hn P M main
  have hnC : NC ≤ n := (le_max_left NC NV).trans hn
  have hnV : NV ≤ n := (le_max_right NC NV).trans hn
  have hn1 : 1 ≤ n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let cell : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
    (Set.Ioc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
      Set.Ioc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))) ∩ V
  obtain ⟨_, Kcells, hK, hcard, hsum, _⟩ :=
    iid_parabola_finite_grid_weighted_reconstruction mu n hn1 level a0 rho hrho.le
  have hwidth (k : ℤ) : ((k : ℝ) + 1) / (n : ℝ) - (k : ℝ) / (n : ℝ) ≤
      1 / (n : ℝ) := by
    have hid : ((k : ℝ) + 1) / (n : ℝ) - (k : ℝ) / (n : ℝ) = 1 / (n : ℝ) := by ring
    exact hid.le
  have hChoose (k : Kcells) : ∃ y : V,
      (y : ℝ × ℝ) ∈ closure (cell k) ∧
      (y : ℝ × ℝ) ∈ Set.Icc ((k.val.1 : ℝ) / (n : ℝ)) (((k.val.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
        Set.Icc ((k.val.2 : ℝ) / (n : ℝ)) (((k.val.2 : ℝ) + 1) / (n : ℝ)) ∧
      ∀ w ∈ closure (cell k), J y ≤ J w := by
    obtain ⟨y, hy, hyQV, hya, hyq, hyt, hys, hyo, hym, hyd, hyI, hmin⟩ :=
      hAnchors ((k.val.1 : ℝ) / (n : ℝ)) (((k.val.1 : ℝ) + 1) / (n : ℝ))
        ((k.val.2 : ℝ) / (n : ℝ)) (((k.val.2 : ℝ) + 1) / (n : ℝ))
        ((hK k.val).1 k.property)
    exact ⟨⟨y, hyQV.2⟩, hy, hyQV.1, fun w hw => (hmin w hw).2⟩
  let y : Kcells → V := fun k => Classical.choose (hChoose k)
  have hy (k : Kcells) := Classical.choose_spec (hChoose k)
  let F : Kcells → (ℝ × ℝ) → (ℝ × ℝ) := fun k w =>
    Real.sqrt (n : ℝ) • E (pOf (y k)) (w - means (pOf (y k)))
  let g : Kcells → (ℝ × ℝ) → ℝ := fun k z =>
    Real.exp (-Real.sqrt (n : ℝ) *
      ((pOf (y k) : ℝ × ℝ).1 * ((E (pOf (y k))).symm z).1 +
        (pOf (y k) : ℝ × ℝ).2 * ((E (pOf (y k))).symm z).2))
  let JGold : Kcells → ℝ := fun k =>
    ∫ z : ℝ × ℝ, ((F k '' cell k).indicator (g k)) z * phi z
  let W : Kcells → ℝ := fun k => Real.exp ((n : ℝ) * (J0 - J (y k)))
  let Gold : ℝ := ∑ k : Kcells, W k * JGold k
  let Z : ℝ := Real.exp ((n : ℝ) * J0) * P.real (M ⁻¹' V)
  have hLocal (k : Kcells) : 0 ≤ JGold k ∧
      |Real.exp ((n : ℝ) * J (y k)) * P.real (M ⁻¹' cell k) - JGold k| ≤
        (CE / (n : ℝ)) * JGold k + 1 / (n : ℝ) ^ 3 := by
    have hMean : means (pOf (y k)) = (y k : ℝ × ℝ) :=
      (hVPoints (y k) (y k).property).2.2.2.2.2.1
    have hp := hSmall n hnC (pOf (y k))
    have hRect : ((∫ x : ℝ, x ∂nu (pOf (y k))),
        (∫ x : ℝ, x ^ 2 ∂nu (pOf (y k)))) ∈
          Set.Icc ((k.val.1 : ℝ) / (n : ℝ)) (((k.val.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
          Set.Icc ((k.val.2 : ℝ) / (n : ℝ)) (((k.val.2 : ℝ) + 1) / (n : ℝ)) := by
      change means (pOf (y k)) ∈ _
      rw [hMean]
      exact (hy k).2.1
    have h := hp.2 _ _ _ _ hRect (hwidth k.val.1) (hwidth k.val.2)
    rcases h with ⟨_, _, _, _, hJG, _, hErr⟩
    have hRate : (pOf (y k) : ℝ × ℝ).1 * (∫ x : ℝ, x ∂nu (pOf (y k))) +
        (pOf (y k) : ℝ × ℝ).2 * (∫ x : ℝ, x ^ 2 ∂nu (pOf (y k))) - K (pOf (y k)) =
          J (y k) := by
      change (pOf (y k) : ℝ × ℝ).1 * (means (pOf (y k))).1 +
        (pOf (y k) : ℝ × ℝ).2 * (means (pOf (y k))).2 - K (pOf (y k)) = J (y k)
      rw [hMean]
    change |Real.exp ((n : ℝ) *
      ((pOf (y k) : ℝ × ℝ).1 * (∫ x : ℝ, x ∂nu (pOf (y k))) +
        (pOf (y k) : ℝ × ℝ).2 * (∫ x : ℝ, x ^ 2 ∂nu (pOf (y k))) - K (pOf (y k)))) *
        P.real (M ⁻¹' cell k) - JGold k| <
      (CE / (n : ℝ)) * JGold k + 1 / (n : ℝ) ^ 3 at hErr
    rw [hRate] at hErr
    exact ⟨hJG, hErr.le⟩
  have hWpos (k : Kcells) : 0 < W k := Real.exp_pos _
  have hWle (k : Kcells) : W k ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonneg_of_nonpos hnpos.le
      (sub_nonpos.mpr (hRateFloor (y k) (y k).property))
  have hScale (k : Kcells) :
      W k * Real.exp ((n : ℝ) * J (y k)) =
        Real.exp ((n : ℝ) * J0) := by
    change Real.exp ((n : ℝ) * (J0 - J (y k))) * _ = _
    rw [← Real.exp_add]
    congr 1
    ring
  have herror (k : Kcells) :
      |Real.exp ((n : ℝ) * J0) *
        P.real (M ⁻¹' cell k) - W k * JGold k| ≤
          (CE / (n : ℝ)) * (W k * JGold k) + (1 : ℝ) / (n : ℝ) ^ 3 := by
    have hid : Real.exp ((n : ℝ) * J0) *
        P.real (M ⁻¹' cell k) - W k * JGold k =
          W k * (Real.exp ((n : ℝ) * J (y k)) * P.real (M ⁻¹' cell k) - JGold k) := by
      calc
        _ = (W k * Real.exp ((n : ℝ) * J (y k))) * P.real (M ⁻¹' cell k) - W k * JGold k :=
          congrArg (fun t : ℝ => t * P.real (M ⁻¹' cell k) - W k * JGold k) (hScale k).symm
        _ = _ := by ring
    rw [hid, abs_mul, abs_of_pos (hWpos k)]
    calc
      W k * |Real.exp ((n : ℝ) * J (y k)) * P.real (M ⁻¹' cell k) - JGold k|
          ≤ W k * ((CE / (n : ℝ)) * JGold k + (1 : ℝ) / (n : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left (hLocal k).2 (hWpos k).le
      _ = (CE / (n : ℝ)) * (W k * JGold k) + W k * ((1 : ℝ) / (n : ℝ) ^ 3) := by ring
      _ ≤ (CE / (n : ℝ)) * (W k * JGold k) + (1 : ℝ) / (n : ℝ) ^ 3 := by
        apply add_le_add le_rfl
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hWle k)
          (div_nonneg zero_le_one (pow_nonneg hnpos.le 3))
  have hProbOld : |Z - Gold| ≤ (CE / (n : ℝ)) * Gold + Bgrid / (n : ℝ) := by
    have hSumP : P.real (M ⁻¹' V) = ∑ k : Kcells, P.real (M ⁻¹' cell k) := by
      calc
        _ = ∑ k ∈ Kcells, P.real (M ⁻¹' cell k) := hsum
        _ = _ := (Finset.sum_coe_sort Kcells (fun k => P.real (M ⁻¹' cell k))).symm
    have hSumError : Real.exp ((n : ℝ) * J0) *
        P.real (M ⁻¹' V) - Gold =
          ∑ k : Kcells, (Real.exp ((n : ℝ) * J0) *
            P.real (M ⁻¹' cell k) - W k * JGold k) := by
      rw [hSumP, Finset.mul_sum, Finset.sum_sub_distrib]
    calc
      |Real.exp ((n : ℝ) * J0) * P.real (M ⁻¹' V) - Gold|
          = |∑ k : Kcells, (Real.exp ((n : ℝ) * J0) *
            P.real (M ⁻¹' cell k) - W k * JGold k)| := congrArg abs hSumError
      _ ≤ ∑ k : Kcells, |Real.exp ((n : ℝ) * J0) *
            P.real (M ⁻¹' cell k) - W k * JGold k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Kcells, ((CE / (n : ℝ)) * (W k * JGold k) + (1 : ℝ) / (n : ℝ) ^ 3) :=
        Finset.sum_le_sum (fun k _ => herror k)
      _ = (CE / (n : ℝ)) * Gold + (Kcells.card : ℝ) * ((1 : ℝ) / (n : ℝ) ^ 3) := by
        simp only [Gold, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      _ ≤ (CE / (n : ℝ)) * Gold + (Bgrid * (n : ℝ) ^ 2) * ((1 : ℝ) / (n : ℝ) ^ 3) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard
          (div_nonneg zero_le_one (pow_nonneg hnpos.le 3)))
      _ = (CE / (n : ℝ)) * Gold + Bgrid / (n : ℝ) := by
        congr 1
        field_simp [ne_of_gt hnpos]
        <;> ring
  let sd : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (cov p 0 0 * cov p 1 1 - (cov p 0 1) ^ 2)
  let tr : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (cov p 0 0 + cov p 1 1 + 2 * sd p)
  let whitening : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
    ![![(cov p 1 1 + sd p) / (sd p * tr p), -(cov p 0 1) / (sd p * tr p)],
      ![-(cov p 0 1) / (sd p * tr p), (cov p 0 0 + sd p) / (sd p * tr p)]]
  let Q : Kcells → (ℝ × ℝ) → ℝ := fun k z =>
    (cov (pOf (y k)) 1 1 * z.1 ^ 2 - 2 * cov (pOf (y k)) 0 1 * z.1 * z.2 +
      cov (pOf (y k)) 0 0 * z.2 ^ 2) / (cov (pOf (y k))).det
  let JG : Kcells → ℝ := fun k =>
    ((n : ℝ) / (2 * Real.pi * Real.sqrt (cov (pOf (y k))).det)) *
      ∫ w : ℝ × ℝ in cell k, Real.exp (-(n : ℝ) *
        ((pOf (y k) : ℝ × ℝ).1 * (w - y k).1 +
          (pOf (y k) : ℝ × ℝ).2 * (w - y k).2) - ((n : ℝ) / 2) * Q k (w - y k))
  have hIdent (k : Kcells) : JGold k = JG k := by
    let p : Theta := pOf (y k)
    have ha : 0 < cov p 0 0 := lt_of_lt_of_le hlo (by
      simpa only [one_pow, zero_pow (by decide : 2 ≠ 0), add_zero, one_mul,
        mul_zero, zero_mul, zero_add, mul_one] using (hbounds p p.property 1 0).1)
    have hSym : cov p 1 0 = cov p 0 1 := by
      simp [cov, parabolaCovariance]
    have hCovDet : (cov p).det = cov p 0 0 * cov p 1 1 - (cov p 0 1) ^ 2 := by
      rw [Matrix.det_fin_two, hSym]
      ring
    have hPositive : 0 < cov p 0 0 * cov p 1 1 - (cov p 0 1) ^ 2 := by
      rw [← hCovDet]
      exact (hThetaPoints p p.property).2.2
    have hCanon := canonical_pair_whitening_determinant_quadratic
      (cov p 0 0) (cov p 0 1) (cov p 1 1) ha hPositive (E p)
      (by simpa [whitening, sd, tr] using (hE p).1)
    have hDetE : |(E p : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).toLinearMap.det| =
        1 / Real.sqrt (cov p).det := by
      simpa only [hCovDet] using hCanon.2.1
    have hQuad (v : ℝ × ℝ) : (E p v).1 ^ 2 + (E p v).2 ^ 2 = Q k v := by
      change (E p v).1 ^ 2 + (E p v).2 ^ 2 =
        (cov p 1 1 * v.1 ^ 2 - 2 * cov p 0 1 * v.1 * v.2 + cov p 0 0 * v.2 ^ 2) /
          (cov p).det
      rw [hCovDet]
      exact hCanon.2.2 v
    have hMean : means (pOf (y k)) = (y k : ℝ × ℝ) :=
      (hVPoints (y k) (y k).property).2.2.2.2.2.1
    have hCell : MeasurableSet (cell k) :=
      (measurableSet_Ioc.prod measurableSet_Ioc).inter hVCompact.measurableSet
    have hPull := standardized_exponential_gaussian_cell_pullback n hn1
      (E p) (y k) p (cell k) hCell
    have hFold : JGold k =
        ((n : ℝ) * |(E p : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).toLinearMap.det| /
          (2 * Real.pi)) *
          ∫ w : ℝ × ℝ in cell k,
            Real.exp (-(n : ℝ) * ((p : ℝ × ℝ).1 * (w - y k).1 +
              (p : ℝ × ℝ).2 * (w - y k).2) - ((n : ℝ) / 2) *
                ((E p (w - y k)).1 ^ 2 + (E p (w - y k)).2 ^ 2)) := by
      simpa only [JGold, F, g, phi, p, hMean] using hPull.2
    have hCoef : (n : ℝ) * (1 / Real.sqrt (cov p).det) / (2 * Real.pi) =
        (n : ℝ) / (2 * Real.pi * Real.sqrt (cov p).det) := by
      simp only [div_eq_mul_inv, _root_.mul_inv_rev]
      ring
    rw [hFold, hDetE, hCoef]
    change _ * _ = _ * _
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun w => by dsimp only; rw [hQuad])
  let A : (ℝ × ℝ) → ℝ := fun w => (Real.sqrt (parabolaCovariance (nu (e.symm w))).det)⁻¹
  let T : (ℝ × ℝ) → ℝ := fun w => A w * Real.exp (-(n : ℝ) * (J w - J0))
  let Ln : ℝ := ((n : ℝ) / (2 * Real.pi)) * ∫ w : ℝ × ℝ in V, T w
  let gRate : Kcells → (ℝ × ℝ) → ℝ := fun k w =>
    A (y k) * Real.exp (-(n : ℝ) * (J (y k) +
      ((e.symm (y k)).1 * (w - y k).1 + (e.symm (y k)).2 * (w - y k).2) +
        Q k (w - y k) / 2 - J0))
  let Gnew : ℝ := ((n : ℝ) / (2 * Real.pi)) *
    ∑ k : Kcells, ∫ w : ℝ × ℝ in cell k, gRate k w
  have hInt := hIntegral n hnV Kcells hK y (fun k => (hy k).2.1) J0
  change IntegrableOn T V ∧ (∀ k : Kcells, IntegrableOn (gRate k) (cell k)) ∧
    0 ≤ Ln ∧ |Gnew - Ln| ≤ (CV / (n : ℝ)) * Ln at hInt
  have hNorm (k : Kcells) : W k * JG k =
      ((n : ℝ) / (2 * Real.pi)) * ∫ w : ℝ × ℝ in cell k, gRate k w := by
    let f : (ℝ × ℝ) → ℝ := fun w =>
      Real.exp (-(n : ℝ) * ((e.symm (y k)).1 * (w - y k).1 +
        (e.symm (y k)).2 * (w - y k).2) - ((n : ℝ) / 2) * Q k (w - y k))
    have hFun : gRate k = fun w => (W k * A (y k)) * f w := by
      funext w
      dsimp only [gRate, W, f]
      rw [show -(n : ℝ) * (J (y k) +
          ((e.symm (y k)).1 * (w - y k).1 + (e.symm (y k)).2 * (w - y k).2) +
            Q k (w - y k) / 2 - J0) =
          (n : ℝ) * (J0 - J (y k)) +
            (-(n : ℝ) * ((e.symm (y k)).1 * (w - y k).1 +
              (e.symm (y k)).2 * (w - y k).2) - ((n : ℝ) / 2) * Q k (w - y k)) by ring,
        Real.exp_add]
      ring
    have hCoef : (n : ℝ) / (2 * Real.pi * Real.sqrt (cov (e.symm (y k))).det) =
        ((n : ℝ) / (2 * Real.pi)) * A (y k) := by
      simp only [A, cov, div_eq_mul_inv, _root_.mul_inv_rev]
      ring
    change W k * (((n : ℝ) / (2 * Real.pi * Real.sqrt (cov (e.symm (y k))).det)) *
      ∫ w : ℝ × ℝ in cell k, f w) = _
    rw [hCoef, hFun, integral_const_mul]
    ring
  have hGold : Gold = Gnew := by
    dsimp only [Gold, Gnew]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hIdent k]
    exact hNorm k
  have hError : |Gold - Ln| ≤ (CV / (n : ℝ)) * Ln := by
    rw [hGold]
    exact hInt.2.2.2
  have hLn : 0 ≤ Ln := hInt.2.2.1
  have hGoldUpper : Gold ≤ (1 + CV) * Ln := by
    have hSub : Gold - Ln ≤ (CV / (n : ℝ)) * Ln := (le_abs_self _).trans hError
    have hRatio : CV / (n : ℝ) ≤ CV := div_le_self hCV.le (by exact_mod_cast hn1)
    have hBound := mul_le_mul_of_nonneg_right hRatio hLn
    nlinarith
  have hProb : |Z - Ln| ≤ (CP / (n : ℝ)) * Ln + Bgrid / (n : ℝ) := by
    calc
      |Z - Ln| ≤ |Z - Gold| + |Gold - Ln| := abs_sub_le _ _ _
      _ ≤ ((CE / (n : ℝ)) * Gold + Bgrid / (n : ℝ)) +
            (CV / (n : ℝ)) * Ln := add_le_add hProbOld hError
      _ ≤ ((CE / (n : ℝ)) * ((1 + CV) * Ln) + Bgrid / (n : ℝ)) +
            (CV / (n : ℝ)) * Ln := add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hGoldUpper (div_nonneg hCE.le hnpos.le)) le_rfl) le_rfl
      _ = (CP / (n : ℝ)) * Ln + Bgrid / (n : ℝ) := by dsimp only [CP]; ring
  obtain ⟨_, _, _, hMain, hLapError⟩ := hLaplace n hn1
  have hMainPos : 0 < main := hMain
  have hLapError' : |Ln / main - 1| ≤ CL / Real.sqrt (n : ℝ) := hLapError
  let s : ℝ := Real.sqrt (n : ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr hnpos
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr (by exact_mod_cast hn1)
  have hsq : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hsLe : s ≤ (n : ℝ) := by nlinarith
  have hmain : main = 1 / (s * kDen) := by
    dsimp only [main, s, kDen]
    rw [Real.sqrt_mul (show 0 ≤ 2 * Real.pi by positivity)]
    congr 1
    ring
  have hLnRatio : Ln / main ≤ 1 + CL := by
    have hSub : Ln / main - 1 ≤ CL / s := (le_abs_self _).trans hLapError'
    have hBound : CL / s ≤ CL := div_le_self hCL.le hs1
    linarith
  have hPdiv : |Z - Ln| / main ≤ (CP / (n : ℝ)) * (Ln / main) +
      Bgrid / ((n : ℝ) * main) := by
    calc
      _ ≤ ((CP / (n : ℝ)) * Ln + Bgrid / (n : ℝ)) / main :=
        div_le_div_of_nonneg_right hProb hMainPos.le
      _ = _ := by ring
  have hConst : Bgrid / ((n : ℝ) * main) = Bgrid * kDen / s := by
    rw [hmain, ← hsq]
    field_simp [hs.ne', hkDen.ne']
    <;> ring
  have hNinv : CP / (n : ℝ) ≤ CP / s :=
    (div_le_div_iff₀ hnpos hs).mpr (mul_le_mul_of_nonneg_left hsLe hCP.le)
  have hFirst : (CP / (n : ℝ)) * (Ln / main) ≤ CP * (1 + CL) / s := by
    calc
      _ ≤ (CP / (n : ℝ)) * (1 + CL) :=
        mul_le_mul_of_nonneg_left hLnRatio (div_nonneg hCP.le hnpos.le)
      _ ≤ (CP / s) * (1 + CL) := mul_le_mul_of_nonneg_right hNinv (by positivity)
      _ = _ := by ring
  refine ⟨hMainPos, ?_⟩
  change |Z / main - 1| ≤ Cfinal / s
  calc
    |Z / main - 1| ≤ |Z / main - Ln / main| + |Ln / main - 1| := abs_sub_le _ _ _
    _ = |Z - Ln| / main + |Ln / main - 1| := by
      rw [← sub_div, abs_div, abs_of_pos hMainPos]
    _ ≤ ((CP / (n : ℝ)) * (Ln / main) + Bgrid / ((n : ℝ) * main)) + CL / s :=
      add_le_add hPdiv hLapError'
    _ ≤ (CP * (1 + CL) / s + Bgrid * kDen / s) + CL / s := by
      rw [hConst]
      exact add_le_add (add_le_add hFirst le_rfl) le_rfl
    _ = Cfinal / s := by dsimp only [Cfinal]; ring

end
end Shao.OQ3
