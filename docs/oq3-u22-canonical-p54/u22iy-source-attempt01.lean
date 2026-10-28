import Shao.OQ3.ActualSelfNormalizedTailUniqueMinimum
import Shao.OQ3.CovarianceRowInverseQuadratic
import Shao.OQ3.ActualMeanChartCompactLaplaceTiltWindows

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators Matrix Topology
noncomputable section

set_option maxHeartbeats 1000000 in
theorem canonical_actual_self_normalized_tail_laplace
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
    (Theta0 : Set (ℝ × ℝ)) (hTheta0 : IsCompact Theta0)
    (htheta0 : theta ∈ interior Theta0)
    (beta c R : ℝ) (hbeta : 0 < beta) (hbetaUpper : beta < (2 : ℝ) / 5)
    (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ p ∈ Theta0, ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic
        (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) xi eta‖ ≤
          1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    let nu : Measure ℝ := mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance nu
    let v : Fin 2 → ℝ := ![1, 2 * a0 / level ^ 2]
    let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 + dotProduct v (D⁻¹ *ᵥ v)
    let J0 : ℝ := theta.1 * a0 + theta.2 * (a0 ^ 2 / level ^ 2) -
      Real.log (∫ x : ℝ, Real.exp (theta.1 * x + theta.2 * x ^ 2) ∂mu)
    let Tail : Set (ℝ × ℝ) := {w | 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
    0 < Lambda1 →
      (∀ w ∈ Tail,
        Shao.Probability.bivariateLegendreRate mu
            (fun x : ℝ => (x, x ^ 2)) (a0, a0 ^ 2 / level ^ 2) ≤
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w ∧
        (Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w =
            Shao.Probability.bivariateLegendreRate mu
              (fun x : ℝ => (x, x ^ 2)) (a0, a0 ^ 2 / level ^ 2) ↔
          w = (a0, a0 ^ 2 / level ^ 2))) →
      ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
        let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
        let T : Set (Shao.Path n) := {z |
          level * Real.sqrt (n : ℝ) ≤
            (if Shao.energy z = 0 then 0 else
              (∑ i : Fin n, z i) / Real.sqrt (Shao.energy z))}
        let main : ℝ := 1 /
          (Real.sqrt (2 * Real.pi * (n : ℝ)) * (-theta.2) * Real.sqrt D.det *
            Real.sqrt Lambda1)
        0 < main ∧
          |(Real.exp ((n : ℝ) * J0) * P.real T) / main - 1| ≤
            C / Real.sqrt (n : ℝ) := by
  classical
  intro nu D v Lambda1 J0 Tail hcurvature hUnique
  obtain ⟨L, f, hL, hf, htf, _htarget, hsourcef, _hsmooth, _hderiv⟩ :=
    open_domain_quadratic_tilt_local_mean_inverse mu theta htheta hdet.ne'
  let e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
    f.restrOpen (interior Theta0) isOpen_interior
  have he : (e : (ℝ × ℝ) → (ℝ × ℝ)) = fun p =>
      (∫ x : ℝ, x ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2),
        ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) := hf
  have hte : theta ∈ e.source := ⟨htf, htheta0⟩
  have hsource : e.source ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) :=
    fun _ hp => hsourcef hp.1
  have h10 : D 1 0 = D 0 1 := rfl
  have hRows : ∀ w : ℝ × ℝ, L w =
      (D 0 0 * w.1 + D 0 1 * w.2, D 1 0 * w.1 + D 1 1 * w.2) := by
    intro w
    have h := congrArg (fun A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) => A w) hL
    change L w = (D 0 0 * w.1 + D 0 1 * w.2,
      D 0 1 * w.1 + D 1 1 * w.2) at h
    simpa only [h10] using h
  let lam : ℝ := 2 * theta.2 / level ^ 2 +
    (L.symm (1, 2 * a0 / level ^ 2)).1 +
      (2 * a0 / level ^ 2) * (L.symm (1, 2 * a0 / level ^ 2)).2
  have hlam : lam = Lambda1 := by
    have hq := (covariance_row_equivalence_inverse_quadratic D hdet.ne' L hRows
      (1, 2 * a0 / level ^ 2)).2
    dsimp only [lam, Lambda1, v]
    simpa only [Prod.fst, Prod.snd, one_mul, add_assoc] using
      congrArg (fun x : ℝ => 2 * theta.2 / level ^ 2 + x) hq
  have hlampos : 0 < lam := by rw [hlam]; exact hcurvature
  have hecenter : e.symm (a0, a0 ^ 2 / level ^ 2) = theta := by
    have hem : e theta = (a0, a0 ^ 2 / level ^ 2) := by rw [he]; exact hmean
    rw [← hem]
    exact e.left_inv hte
  let j0 : ℝ := (e.symm (a0, a0 ^ 2 / level ^ 2)).1 * a0 +
    (e.symm (a0, a0 ^ 2 / level ^ 2)).2 * (a0 ^ 2 / level ^ 2) -
      Real.log (∫ x : ℝ, Real.exp
        ((e.symm (a0, a0 ^ 2 / level ^ 2)).1 * x +
          (e.symm (a0, a0 ^ 2 / level ^ 2)).2 * x ^ 2) ∂mu)
  have hj0 : j0 = J0 := by dsimp only [j0]; rw [hecenter]; rfl
  have hGeometry := actual_mean_chart_compact_laplace_tilt_windows
    mu theta htheta hdet level a0 hlevel ha0 hnegative hmean hsaddle
      e he hte hsource 1 (by norm_num) L hL
  have hFull := actual_self_normalized_tail_laplace_of_unique_minimum
    mu theta htheta hdet level a0 hlevel ha0 hnegative hmean hsaddle
      e he hte hsource 1 (by norm_num) beta c R hbeta hbetaUpper hc hR L hL
  obtain ⟨capG, hcapG, _hcapGMax, _hC0, hGeom⟩ := hGeometry.2 hlampos
  obtain ⟨capT, hcapT, _hcapTMax, hTail⟩ := hFull.2 hlampos
  let rho : ℝ := min capG capT
  have hrho : 0 < rho := lt_min hcapG hcapT
  have hrhoG : rho ≤ capG := min_le_left _ _
  have hrhoT : rho ≤ capT := min_le_right _ _
  have hG := hGeom rho hrho hrhoG
  have hThisWC : ∀ p ∈ e.symm ''
      {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
        0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho},
      ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
        ‖jointCharacteristic
          (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) xi eta‖ ≤
            1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta) := by
    intro p hp xi eta hfreq
    have hpe : p ∈ e.source := (hG.2.2.2.1 p hp).1
    have hp0 : p ∈ interior Theta0 := hpe.2
    exact hWC p (interior_subset hp0) xi eta hfreq
  have hResult := (hTail rho hrho hrhoT hThisWC).2 hUnique
  change ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    let T : Set (Shao.Path n) := {z | level * Real.sqrt (n : ℝ) ≤
      (if Shao.energy z = 0 then 0 else
        (∑ i : Fin n, z i) / Real.sqrt (Shao.energy z))}
    let main : ℝ := 1 / (Real.sqrt (2 * Real.pi * (n : ℝ)) *
      (-theta.2) * Real.sqrt D.det * Real.sqrt lam)
    0 < main ∧ |(Real.exp ((n : ℝ) * j0) * P.real T) / main - 1| ≤
      C / Real.sqrt (n : ℝ) at hResult
  simpa only [hlam, hj0] using hResult

end
end Shao.OQ3
