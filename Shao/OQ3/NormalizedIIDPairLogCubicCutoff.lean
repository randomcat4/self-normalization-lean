import Shao.OQ3.NormalizedIIDPairSuperpolynomialDecay

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators
noncomputable section

theorem normalized_iid_pair_weak_cramer_real_cutoff_bound
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law]
    (n : ℕ) (hn : 1 ≤ n) (beta c R d : ℝ)
    (hbeta : 0 ≤ beta) (hbudget : 0 < 1 + beta / 2 - d * beta)
    (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤
          1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta))
    (xi eta : ℝ)
    (hfreq : Real.sqrt (n : ℝ) * R < Real.sqrt (xi ^ 2 + eta ^ 2))
    (hcutoff : Real.sqrt (xi ^ 2 + eta ^ 2) ≤ Real.rpow (n : ℝ) d) :
    let Q : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
    let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun z =>
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, z i
    let rho : Measure (ℝ × ℝ) := Q.map S
    0 < 1 + beta / 2 - d * beta ∧
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ ≤
          Real.exp (-c * Real.rpow (n : ℝ) (1 + beta / 2 - d * beta)) := by
  dsimp only
  have hN : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn)
  have hpositive : 0 < Real.sqrt (xi ^ 2 + eta ^ 2) :=
    lt_of_le_of_lt (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hR) hfreq
  have hdecay := Real.rpow_le_rpow_of_nonpos hpositive hcutoff (neg_nonpos.mpr hbeta)
  have hpower : Real.rpow (n : ℝ) (1 + beta / 2 - d * beta) =
      Real.rpow (n : ℝ) (1 + beta / 2) * Real.rpow (Real.rpow (n : ℝ) d) (-beta) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul hN.le d (-beta), ← Real.rpow_add hN]
    congr 1
    ring
  have hcoefficient : Real.rpow (n : ℝ) (1 + beta / 2 - d * beta) ≤
      Real.rpow (n : ℝ) (1 + beta / 2) *
        Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta) := by
    rw [hpower]
    exact mul_le_mul_of_nonneg_left hdecay (Real.rpow_nonneg hN.le _)
  have hnegative : -c * Real.rpow (n : ℝ) (1 + beta / 2) *
        Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta) ≤
      -c * Real.rpow (n : ℝ) (1 + beta / 2 - d * beta) := by
    have h := mul_le_mul_of_nonpos_left hcoefficient (neg_nonpos.mpr hc.le)
    simpa only [mul_assoc] using h
  have h := normalized_iid_pair_weak_cramer_power_bound
    law n hn beta c R hbeta hc hR hWC xi eta hfreq
  exact ⟨hbudget, h.trans (Real.exp_le_exp.mpr hnegative)⟩


theorem normalized_iid_pair_uniform_real_cutoff_far_frequency_decay
    (beta c R d p epsilon : ℝ)
    (hbeta : 0 ≤ beta) (hbudget : 0 < 1 + beta / 2 - d * beta)
    (hc : 0 < c) (hR : 0 ≤ R) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ law : Measure (ℝ × ℝ), IsProbabilityMeasure law →
        (∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
          ‖(∫ w : ℝ × ℝ,
            Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤
              1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta)) →
        ∀ xi eta : ℝ,
          Real.sqrt (n : ℝ) * R < Real.sqrt (xi ^ 2 + eta ^ 2) →
          Real.sqrt (xi ^ 2 + eta ^ 2) ≤ Real.rpow (n : ℝ) d →
          let Q : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
          let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun z =>
            (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, z i
          let rho : Measure (ℝ × ℝ) := Q.map S
          Real.rpow (n : ℝ) p *
            ‖(∫ w : ℝ × ℝ,
              Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ <
                epsilon := by
  have halpha : 0 < 1 + beta / 2 - d * beta := hbudget
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_real_power_mul_stretched_exponential_lt
      (1 + beta / 2 - d * beta) c p epsilon halpha hc hepsilon)
  refine ⟨max 1 N, le_max_left 1 N, ?_⟩
  intro n hn law hlaw hWC xi eta hfreq hcutoff
  letI : IsProbabilityMeasure law := hlaw
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 N) hn
  have hCF := (normalized_iid_pair_weak_cramer_real_cutoff_bound
    law n hn1 beta c R d hbeta hbudget hc hR hWC xi eta hfreq hcutoff).2
  have hbound := mul_le_mul_of_nonneg_left hCF
    (Real.rpow_nonneg (Nat.cast_nonneg n) p)
  exact lt_of_le_of_lt hbound (hN n (le_trans (le_max_right 1 N) hn))


theorem exists_weak_cramer_real_cutoff_above_cubic_log
    (beta : ℝ) (hbeta : 0 ≤ beta) (hbetaUpper : beta < (2 : ℝ) / 5) :
    ∃ d : ℝ, 3 < d ∧ 0 < 1 + beta / 2 - d * beta ∧
      ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
        (n : ℝ) ^ 3 * Real.log (n : ℝ) ≤ Real.rpow (n : ℝ) d := by
  let eps : ℝ := (1 - (5 / 2 : ℝ) * beta) / 2
  have heps : 0 < eps := by dsimp [eps]; linarith
  have hsmall : eps * beta ≤ eps :=
    mul_le_of_le_one_right heps.le (by linarith)
  have hbudget : 0 < 1 + beta / 2 - (3 + eps) * beta := by
    dsimp [eps] at *
    nlinarith
  have htR : Tendsto (fun x : ℝ => Real.log x / Real.rpow x eps) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop heps).tendsto_div_nhds_zero
  have ht := htR.comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds zero_lt_one))
  refine ⟨3 + eps, by linarith, hbudget, max 1 N, le_max_left 1 N, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left 1 N).trans hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hlog : Real.log (n : ℝ) ≤ Real.rpow (n : ℝ) eps := by
    have h := hN n ((le_max_right 1 N).trans hn)
    have hp : 0 < Real.rpow (n : ℝ) eps := Real.rpow_pos_of_pos hnR eps
    exact ((div_lt_one hp).mp h).le
  calc
    (n : ℝ) ^ 3 * Real.log (n : ℝ) ≤ (n : ℝ) ^ 3 * Real.rpow (n : ℝ) eps :=
      mul_le_mul_of_nonneg_left hlog (pow_nonneg hnR.le 3)
    _ = Real.rpow (n : ℝ) (3 + eps) := by
      exact (congrArg (fun b : ℝ => b * Real.rpow (n : ℝ) eps)
        (Real.rpow_natCast (n : ℝ) 3).symm).trans
          (Real.rpow_add hnR 3 eps).symm


theorem normalized_iid_pair_uniform_log_cubic_far_frequency_decay
    (beta c R p epsilon : ℝ)
    (hbeta : 0 ≤ beta) (hbetaUpper : beta < (2 : ℝ) / 5)
    (hc : 0 < c) (hR : 0 ≤ R) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ law : Measure (ℝ × ℝ), IsProbabilityMeasure law →
        (∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
          ‖(∫ w : ℝ × ℝ,
            Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤
              1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta)) →
        ∀ xi eta : ℝ,
          Real.sqrt (n : ℝ) * R < Real.sqrt (xi ^ 2 + eta ^ 2) →
          Real.sqrt (xi ^ 2 + eta ^ 2) ≤ (n : ℝ) ^ 3 * Real.log (n : ℝ) →
          let Q : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
          let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun z =>
            (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, z i
          let rho : Measure (ℝ × ℝ) := Q.map S
          Real.rpow (n : ℝ) p *
            ‖(∫ w : ℝ × ℝ,
              Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ <
                epsilon := by
  obtain ⟨d, hd, hbudget, N0, hN0, hcut⟩ :=
    exists_weak_cramer_real_cutoff_above_cubic_log beta hbeta hbetaUpper
  obtain ⟨N1, hN1, hFn⟩ := normalized_iid_pair_uniform_real_cutoff_far_frequency_decay
    beta c R d p epsilon hbeta hbudget hc hR hepsilon
  refine ⟨max N0 N1, hN0.trans (le_max_left _ _), ?_⟩
  intro n hn law hlaw hWC xi eta hfreq hcutoff
  exact hFn n ((le_max_right N0 N1).trans hn) law hlaw hWC xi eta hfreq
    (hcutoff.trans (hcut n ((le_max_left N0 N1).trans hn)))

end
end Shao.OQ3
