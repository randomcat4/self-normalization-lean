import Shao.OQ3.CanonicalActualSelfNormalizedTail

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators Matrix Topology
noncomputable section

theorem canonical_actual_self_normalized_tail_scaled_expansion
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
    let vCorr : ℝ := (-theta.2) * Real.sqrt D.det * Real.sqrt Lambda1
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
      0 < vCorr ∧ ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
          let T : Set (Shao.Path n) := {z |
            level * Real.sqrt (n : ℝ) ≤
              (if Shao.energy z = 0 then 0 else
                (∑ i : Fin n, z i) / Real.sqrt (Shao.energy z))}
          |Real.sqrt (2 * Real.pi * (n : ℝ)) *
              Real.exp ((n : ℝ) * J0) * P.real T - vCorr⁻¹| ≤
            C / Real.sqrt (n : ℝ) := by
  classical
  intro nu D v Lambda1 J0 vCorr Tail hcurvature hUnique
  obtain ⟨C, hC, N, hN, hBound⟩ :=
    canonical_actual_self_normalized_tail_laplace
      mu theta htheta hdet level a0 hlevel ha0 hnegative hmean hsaddle
        Theta0 hTheta0 htheta0 beta c R hbeta hbetaUpper hc hR hWC hcurvature hUnique
  have hvCorr : 0 < vCorr :=
    mul_pos (mul_pos (neg_pos.mpr hnegative) (Real.sqrt_pos.mpr hdet))
      (Real.sqrt_pos.mpr hcurvature)
  refine ⟨hvCorr, C / vCorr, div_pos hC hvCorr, N, hN, ?_⟩
  intro n hn P T
  have hrel := (hBound n hn).2
  let A : ℝ := Real.sqrt (2 * Real.pi * (n : ℝ))
  have hnNat : 0 < n := by omega
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnNat
  have hA : 0 < A := Real.sqrt_pos.mpr
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) hnReal)
  have hmain : 1 / (Real.sqrt (2 * Real.pi * (n : ℝ)) * (-theta.2) *
      Real.sqrt D.det * Real.sqrt Lambda1) = 1 / (A * vCorr) := by
    simp only [A, vCorr, mul_assoc]
  change |(Real.exp ((n : ℝ) * J0) * P.real T) /
    (1 / (Real.sqrt (2 * Real.pi * (n : ℝ)) * (-theta.2) *
      Real.sqrt D.det * Real.sqrt Lambda1)) - 1| ≤ C / Real.sqrt (n : ℝ) at hrel
  rw [hmain] at hrel
  have hscale : (Real.exp ((n : ℝ) * J0) * P.real T) / (1 / (A * vCorr)) - 1 =
      vCorr * (A * Real.exp ((n : ℝ) * J0) * P.real T - vCorr⁻¹) := by
    field_simp [hvCorr.ne', hA.ne'] <;> ring
  rw [hscale, abs_mul, abs_of_pos hvCorr] at hrel
  calc
    |Real.sqrt (2 * Real.pi * (n : ℝ)) *
        Real.exp ((n : ℝ) * J0) * P.real T - vCorr⁻¹| ≤
        (C / Real.sqrt (n : ℝ)) / vCorr :=
      (le_div_iff₀ hvCorr).mpr (by simpa only [mul_comm] using hrel)
    _ = (C / vCorr) / Real.sqrt (n : ℝ) := by ring

end
end Shao.OQ3
