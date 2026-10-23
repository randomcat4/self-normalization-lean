import Shao.OQ3.NormalizedIIDPairCharacteristic

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
noncomputable section

theorem scaled_iid_pair_frequency_length
    (n : ℕ) (hn : 1 ≤ n) (xi eta R : ℝ) :
    Real.sqrt ((xi / Real.sqrt (n : ℝ)) ^ 2 + (eta / Real.sqrt (n : ℝ)) ^ 2) =
      Real.sqrt (xi ^ 2 + eta ^ 2) / Real.sqrt (n : ℝ) ∧
    (R < Real.sqrt ((xi / Real.sqrt (n : ℝ)) ^ 2 + (eta / Real.sqrt (n : ℝ)) ^ 2) ↔
      Real.sqrt (n : ℝ) * R < Real.sqrt (xi ^ 2 + eta ^ 2)) := by
  have hN : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hN
  have hlength : Real.sqrt
      ((xi / Real.sqrt (n : ℝ)) ^ 2 + (eta / Real.sqrt (n : ℝ)) ^ 2) =
      Real.sqrt (xi ^ 2 + eta ^ 2) / Real.sqrt (n : ℝ) := by
    rw [div_pow, div_pow, ← add_div,
      Real.sqrt_div (add_nonneg (sq_nonneg xi) (sq_nonneg eta)),
      Real.sqrt_sq (Real.sqrt_nonneg (n : ℝ))]
  refine ⟨hlength, ?_⟩
  rw [hlength, lt_div_iff₀ hs, mul_comm R (Real.sqrt (n : ℝ))]

theorem normalized_iid_pair_weak_cramer_power_bound
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law]
    (n : ℕ) (hn : 1 ≤ n) (beta c R : ℝ)
    (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤
          1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta))
    (xi eta : ℝ)
    (hfreq : Real.sqrt (n : ℝ) * R < Real.sqrt (xi ^ 2 + eta ^ 2)) :
    let Q : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
    let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun z =>
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, z i
    let rho : Measure (ℝ × ℝ) := Q.map S
    ‖(∫ w : ℝ × ℝ,
      Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ ≤
        Real.exp (-c * Real.rpow (n : ℝ) (1 + beta / 2) *
          Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) := by
  dsimp only
  have hN : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn)
  obtain ⟨hlength, hthreshold⟩ := scaled_iid_pair_frequency_length n hn xi eta R
  have hscaled := hthreshold.mpr hfreq
  have hsquare : (Real.sqrt (n : ℝ)) ^ (2 : ℝ) = (n : ℝ) := by
    calc
      Real.rpow (Real.sqrt (n : ℝ)) (2 : ℝ) = (Real.sqrt (n : ℝ)) ^ 2 :=
        Real.rpow_natCast _ 2
      _ = (n : ℝ) := Real.sq_sqrt hN.le
  have hrootpower : Real.rpow (Real.sqrt (n : ℝ)) (-beta) =
      Real.rpow (n : ℝ) (-(beta / 2)) := by
    have h := Real.rpow_mul (Real.sqrt_nonneg (n : ℝ)) (2 : ℝ) (-(beta / 2))
    rw [hsquare] at h
    simpa only [Real.rpow_eq_pow, show (2 : ℝ) * (-(beta / 2)) = -beta by ring] using h
  have hcoefficient : (n : ℝ) * Real.rpow (Real.sqrt
      ((xi / Real.sqrt (n : ℝ)) ^ 2 + (eta / Real.sqrt (n : ℝ)) ^ 2)) (-beta) =
      Real.rpow (n : ℝ) (1 + beta / 2) *
        Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta) := by
    simp only [Real.rpow_eq_pow] at hrootpower ⊢
    rw [hlength, Real.div_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (-beta),
      hrootpower, Real.rpow_neg hN.le (beta / 2), div_inv_eq_mul,
      Real.rpow_add hN 1 (beta / 2), Real.rpow_one]
    ring
  have h := normalized_iid_pair_weak_cramer_exponential_bound
    law n hn beta c R hbeta hc hR hWC xi eta hscaled
  refine h.trans_eq ?_
  congr 1
  calc
    -(n : ℝ) * c * Real.rpow (Real.sqrt
        ((xi / Real.sqrt (n : ℝ)) ^ 2 + (eta / Real.sqrt (n : ℝ)) ^ 2)) (-beta) =
        -c * ((n : ℝ) * Real.rpow (Real.sqrt
          ((xi / Real.sqrt (n : ℝ)) ^ 2 + (eta / Real.sqrt (n : ℝ)) ^ 2)) (-beta)) := by ring
    _ = -c * (Real.rpow (n : ℝ) (1 + beta / 2) *
        Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) := by rw [hcoefficient]
    _ = -c * Real.rpow (n : ℝ) (1 + beta / 2) *
        Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta) := by ring

theorem normalized_iid_pair_weak_cramer_cubic_cutoff_bound
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law]
    (n : ℕ) (hn : 1 ≤ n) (beta c R : ℝ)
    (hbeta : 0 ≤ beta) (hbetaUpper : beta < (2 : ℝ) / 5)
    (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤
          1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta))
    (xi eta : ℝ)
    (hfreq : Real.sqrt (n : ℝ) * R < Real.sqrt (xi ^ 2 + eta ^ 2))
    (hcutoff : Real.sqrt (xi ^ 2 + eta ^ 2) ≤ (n : ℝ) ^ 3) :
    let Q : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
    let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun z =>
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, z i
    let rho : Measure (ℝ × ℝ) := Q.map S
    0 < 1 - (5 / 2 : ℝ) * beta ∧
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ ≤
          Real.exp (-c * Real.rpow (n : ℝ) (1 - (5 / 2 : ℝ) * beta)) := by
  dsimp only
  have hN : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn)
  have hpositive : 0 < Real.sqrt (xi ^ 2 + eta ^ 2) :=
    lt_of_le_of_lt (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hR) hfreq
  have hdecay := Real.rpow_le_rpow_of_nonpos hpositive hcutoff (neg_nonpos.mpr hbeta)
  have hpower : Real.rpow (n : ℝ) (1 - (5 / 2 : ℝ) * beta) =
      Real.rpow (n : ℝ) (1 + beta / 2) * Real.rpow ((n : ℝ) ^ 3) (-beta) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast_mul hN.le 3 (-beta), ← Real.rpow_add hN]
    congr 1
    ring
  have hcoefficient : Real.rpow (n : ℝ) (1 - (5 / 2 : ℝ) * beta) ≤
      Real.rpow (n : ℝ) (1 + beta / 2) *
        Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta) := by
    rw [hpower]
    exact mul_le_mul_of_nonneg_left hdecay (Real.rpow_nonneg hN.le _)
  have hnegative : -c * Real.rpow (n : ℝ) (1 + beta / 2) *
        Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta) ≤
      -c * Real.rpow (n : ℝ) (1 - (5 / 2 : ℝ) * beta) := by
    have h := mul_le_mul_of_nonpos_left hcoefficient (neg_nonpos.mpr hc.le)
    simpa only [mul_assoc] using h
  have h := normalized_iid_pair_weak_cramer_power_bound
    law n hn beta c R hbeta hc hR hWC xi eta hfreq
  exact ⟨by linarith, h.trans (Real.exp_le_exp.mpr hnegative)⟩

end
end Shao.OQ3
