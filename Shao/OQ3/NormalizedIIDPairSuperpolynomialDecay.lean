import Shao.OQ3.NormalizedIIDPairFrequencyDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators
noncomputable section

theorem tendsto_real_power_mul_stretched_exponential
    (alpha c p : ℝ) (halpha : 0 < alpha) (hc : 0 < c) :
    Filter.Tendsto (fun n : ℕ =>
      Real.rpow (n : ℝ) p * Real.exp (-c * Real.rpow (n : ℝ) alpha))
      Filter.atTop (𝓝 (0 : ℝ)) := by
  have ht : Tendsto (fun n : ℕ => Real.rpow (n : ℝ) alpha) atTop atTop :=
    (tendsto_rpow_atTop halpha).comp tendsto_natCast_atTop_atTop
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (p / alpha) c hc).comp ht
  refine h.congr (fun n => ?_)
  have hpower : Real.rpow (Real.rpow (n : ℝ) alpha) (p / alpha) =
      Real.rpow (n : ℝ) p := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    field_simp [halpha.ne']
  dsimp only [Function.comp_apply]
  simp only [Real.rpow_eq_pow] at hpower ⊢
  rw [hpower]

theorem eventually_real_power_mul_stretched_exponential_lt
    (alpha c p epsilon : ℝ) (halpha : 0 < alpha) (hc : 0 < c)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.rpow (n : ℝ) p * Real.exp (-c * Real.rpow (n : ℝ) alpha) < epsilon := by
  exact (tendsto_real_power_mul_stretched_exponential alpha c p halpha hc).eventually
    (gt_mem_nhds hepsilon)

theorem normalized_iid_pair_uniform_far_frequency_decay
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
          Real.sqrt (xi ^ 2 + eta ^ 2) ≤ (n : ℝ) ^ 3 →
          let Q : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
          let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun z =>
            (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, z i
          let rho : Measure (ℝ × ℝ) := Q.map S
          Real.rpow (n : ℝ) p *
            ‖(∫ w : ℝ × ℝ,
              Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ <
                epsilon := by
  have halpha : 0 < 1 - (5 / 2 : ℝ) * beta := by linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_real_power_mul_stretched_exponential_lt
      (1 - (5 / 2 : ℝ) * beta) c p epsilon halpha hc hepsilon)
  refine ⟨max 1 N, le_max_left 1 N, ?_⟩
  intro n hn law hlaw hWC xi eta hfreq hcutoff
  letI : IsProbabilityMeasure law := hlaw
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 N) hn
  have hCF := (normalized_iid_pair_weak_cramer_cubic_cutoff_bound
    law n hn1 beta c R hbeta hbetaUpper hc hR hWC xi eta hfreq hcutoff).2
  have hbound := mul_le_mul_of_nonneg_left hCF
    (Real.rpow_nonneg (Nat.cast_nonneg n) p)
  exact lt_of_le_of_lt hbound (hN n (le_trans (le_max_right 1 N) hn))

end
end Shao.OQ3
