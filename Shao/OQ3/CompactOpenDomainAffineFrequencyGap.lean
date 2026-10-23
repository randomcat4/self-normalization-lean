import Shao.OQ3.CompactOpenDomainTiltedFrequencyGap
import Shao.OQ3.AffineWeakCramer

namespace Shao.OQ3
open MeasureTheory
open scoped Topology Matrix
noncomputable section

theorem isCompact_euclidean_pair_annulus (delta H : ℝ) :
    IsCompact {a : ℝ × ℝ |
      delta ≤ Real.sqrt (a.1 ^ 2 + a.2 ^ 2) ∧
        Real.sqrt (a.1 ^ 2 + a.2 ^ 2) ≤ H} := by
  have hf : Continuous (fun a : ℝ × ℝ => Real.sqrt (a.1 ^ 2 + a.2 ^ 2)) := by
    fun_prop
  have hclosed : IsClosed {a : ℝ × ℝ |
      delta ≤ Real.sqrt (a.1 ^ 2 + a.2 ^ 2) ∧
        Real.sqrt (a.1 ^ 2 + a.2 ^ 2) ≤ H} :=
    (isClosed_le continuous_const hf).inter (isClosed_le hf continuous_const)
  refine (isCompact_closedBall (0 : ℝ × ℝ) H).of_isClosed_subset hclosed ?_
  intro a ha
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  change max |a.1| |a.2| ≤ H
  have h1 : |a.1| ≤ Real.sqrt (a.1 ^ 2 + a.2 ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg a.2])
  have h2 : |a.2| ≤ Real.sqrt (a.1 ^ 2 + a.2 ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg a.1])
  exact max_le (h1.trans ha.2) (h2.trans ha.2)

theorem compact_open_domain_affine_frequency_gap
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (beta c R : ℝ) (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ theta ∈ Theta, ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ x : ℝ,
        Complex.exp (((u * x + v * x ^ 2 : ℝ) : ℂ) * Complex.I)
          ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))‖ ≤
            1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta))
    (A : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ)
    (b : (ℝ × ℝ) → (Fin 2 → ℝ))
    (L U : ℝ) (hL : 0 < L) (hU : 0 < U)
    (hfreq : ∀ theta ∈ Theta, ∀ xi eta : ℝ,
      L * Real.sqrt (xi ^ 2 + eta ^ 2) ≤
          Real.sqrt ((xi * A theta 0 0 + eta * A theta 1 0) ^ 2 +
            (xi * A theta 0 1 + eta * A theta 1 1) ^ 2) ∧
        Real.sqrt ((xi * A theta 0 0 + eta * A theta 1 0) ^ 2 +
          (xi * A theta 0 1 + eta * A theta 1 1) ^ 2) ≤
            U * Real.sqrt (xi ^ 2 + eta ^ 2))
    (delta H : ℝ) (hdelta : 0 < delta) :
    let nu : (ℝ × ℝ) → Measure ℝ := fun theta =>
      mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)
    let Y : (ℝ × ℝ) → ℝ → (Fin 2 → ℝ) := fun theta x =>
      A theta *ᵥ (![x, x ^ 2] - b theta)
    let laws : (ℝ × ℝ) → Measure (Fin 2 → ℝ) := fun theta =>
      (nu theta).map (Y theta)
    let Phi : (ℝ × ℝ) → ℝ → ℝ → ℂ := fun theta xi eta =>
      ∫ y : Fin 2 → ℝ,
        Complex.exp (((xi * y 0 + eta * y 1 : ℝ) : ℂ) * Complex.I) ∂laws theta
    (∀ theta ∈ Theta, IsProbabilityMeasure (laws theta)) ∧
      ∃ gamma : ℝ, 0 < gamma ∧ gamma < 1 ∧
        ∀ theta ∈ Theta, ∀ xi eta : ℝ,
          delta ≤ Real.sqrt (xi ^ 2 + eta ^ 2) →
            Real.sqrt (xi ^ 2 + eta ^ 2) ≤ H → ‖Phi theta xi eta‖ ≤ gamma := by
  dsimp only
  let nu : (ℝ × ℝ) → Measure ℝ := fun theta =>
    mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)
  let Y : (ℝ × ℝ) → ℝ → (Fin 2 → ℝ) := fun theta x =>
    A theta *ᵥ (![x, x ^ 2] - b theta)
  let laws : (ℝ × ℝ) → Measure (Fin 2 → ℝ) := fun theta =>
    (nu theta).map (Y theta)
  have hprob : ∀ theta ∈ Theta, IsProbabilityMeasure (nu theta) := by
    intro theta htheta
    have hf : Integrable (fun x : ℝ =>
        Real.exp (theta.1 * x + theta.2 * x ^ 2)) mu :=
      interior_subset (hTheta htheta)
    exact isProbabilityMeasure_tilted hf
  have hWC' : ∀ theta ∈ Theta, ∀ u v : ℝ,
      R < Real.sqrt (u ^ 2 + v ^ 2) →
        ‖jointCharacteristic (nu theta) u v‖ ≤
          1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta) := by
    simpa only [nu, jointCharacteristic, jointPhase] using hWC
  have hfamily := uniform_weakCramer_of_affine_frequency_bounds
    Theta nu hprob A b L U beta c R hL hU hbeta hc hR hfreq hWC'
  refine ⟨fun theta htheta => (hfamily.2.2 theta htheta).1, ?_⟩
  let K : Set (ℝ × ℝ) := {a |
    L * delta ≤ Real.sqrt (a.1 ^ 2 + a.2 ^ 2) ∧
      Real.sqrt (a.1 ^ 2 + a.2 ^ 2) ≤ U * H}
  have hzero : ∀ a ∈ K, a.1 ≠ 0 ∨ a.2 ≠ 0 := by
    intro a ha
    by_contra h
    push_neg at h
    have hpos : 0 < L * delta := mul_pos hL hdelta
    have hlow := ha.1
    simp only [h.1, h.2, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      Real.sqrt_zero, zero_add] at hlow
    linarith
  obtain ⟨gamma, hgamma0, hgamma1, hgap⟩ :=
    compact_open_domain_tilted_frequency_gap mu Theta hcompact hTheta
      beta c R hbeta hc hR hWC K (isCompact_euclidean_pair_annulus (L * delta) (U * H))
        hzero
  refine ⟨gamma, hgamma0, hgamma1, ?_⟩
  intro theta htheta xi eta hlow hhigh
  have ht := hfreq theta htheta xi eta
  have hmem : (xi * A theta 0 0 + eta * A theta 1 0,
      xi * A theta 0 1 + eta * A theta 1 1) ∈ K :=
    ⟨(mul_le_mul_of_nonneg_left hlow hL.le).trans ht.1,
      ht.2.trans (mul_le_mul_of_nonneg_left hhigh hU.le)⟩
  have hnorm := (affine_parabola_characteristic_factor
    (nu theta) (A theta) (b theta) xi eta).2
  change ‖(∫ y : Fin 2 → ℝ,
    Complex.exp (((xi * y 0 + eta * y 1 : ℝ) : ℂ) * Complex.I) ∂laws theta)‖ ≤ gamma
  rw [hnorm]
  simpa only [nu, jointCharacteristic, jointPhase] using hgap theta htheta
    (xi * A theta 0 0 + eta * A theta 1 0,
      xi * A theta 0 1 + eta * A theta 1 1) hmem

end
end Shao.OQ3
