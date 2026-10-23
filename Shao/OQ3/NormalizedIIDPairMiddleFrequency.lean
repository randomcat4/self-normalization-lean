import Shao.OQ3.WeakCramerPairCompactGap
import Shao.OQ3.NormalizedIIDPairCharacteristic
import Shao.OQ3.NormalizedIIDPairSuperpolynomialDecay

namespace Shao.OQ3
open MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section

theorem normalized_iid_pair_compact_middle_frequency_bound
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law]
    (beta c R : ℝ) (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤
          1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta))
    (K : Set (ℝ × ℝ)) (hcompact : IsCompact K)
    (hzero : ∀ a ∈ K, a.1 ≠ 0 ∨ a.2 ≠ 0) :
    ∃ gamma : ℝ, 0 < gamma ∧ gamma < 1 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ xi eta : ℝ,
        (xi / Real.sqrt (n : ℝ), eta / Real.sqrt (n : ℝ)) ∈ K →
          let Q : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
          let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun z =>
            (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, z i
          let rho : Measure (ℝ × ℝ) := Q.map S
          ‖(∫ w : ℝ × ℝ,
            Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ ≤
              gamma ^ n := by
  obtain ⟨gamma, hgamma, hgammaUpper, hgap⟩ :=
    weak_cramer_pair_compact_frequency_gap law beta c R hbeta hc hR hWC K hcompact hzero
  refine ⟨gamma, hgamma, hgammaUpper, ?_⟩
  intro n hn xi eta hfreq
  have hfactor := normalized_iid_pair_characteristic_factor law n hn xi eta
  dsimp only at hfactor ⊢
  rw [hfactor, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hgap _ hfreq) n

theorem normalized_iid_pair_compact_middle_frequency_decay
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law]
    (beta c R : ℝ) (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤
          1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta))
    (K : Set (ℝ × ℝ)) (hcompact : IsCompact K)
    (hzero : ∀ a ∈ K, a.1 ≠ 0 ∨ a.2 ≠ 0)
    (p epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ xi eta : ℝ,
        (xi / Real.sqrt (n : ℝ), eta / Real.sqrt (n : ℝ)) ∈ K →
          let Q : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
          let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun z =>
            (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, z i
          let rho : Measure (ℝ × ℝ) := Q.map S
          Real.rpow (n : ℝ) p *
            ‖(∫ w : ℝ × ℝ,
              Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ <
                epsilon := by
  obtain ⟨gamma, hgamma, hgammaUpper, hbound⟩ :=
    normalized_iid_pair_compact_middle_frequency_bound
      law beta c R hbeta hc hR hWC K hcompact hzero
  have hc0 : 0 < 1 - gamma := sub_pos.mpr hgammaUpper
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_real_power_mul_stretched_exponential_lt
      1 (1 - gamma) p epsilon (by norm_num) hc0 hepsilon)
  refine ⟨max 1 N, le_max_left 1 N, ?_⟩
  intro n hn xi eta hfreq
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 N) hn
  have hCF := hbound n hn1 xi eta hfreq
  have hgammaExp : gamma ≤ Real.exp (-(1 - gamma)) := by
    have h := Real.add_one_le_exp (-(1 - gamma))
    linarith
  have hexp : gamma ^ n ≤ Real.exp (-(1 - gamma) * (n : ℝ)) := by
    calc
      gamma ^ n ≤ (Real.exp (-(1 - gamma))) ^ n :=
        pow_le_pow_left₀ hgamma.le hgammaExp n
      _ = Real.exp (-(1 - gamma) * (n : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hscaled := mul_le_mul_of_nonneg_left (hCF.trans hexp)
    (Real.rpow_nonneg (Nat.cast_nonneg n) p)
  have hfinal : Real.rpow (n : ℝ) p *
      Real.exp (-(1 - gamma) * (n : ℝ)) < epsilon := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using hN n (le_trans (le_max_right 1 N) hn)
  exact lt_of_le_of_lt hscaled hfinal

end
end Shao.OQ3
