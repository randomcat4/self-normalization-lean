import Shao.OQ3.OpenDomainTiltedFourierContinuity
import Shao.OQ3.WeakCramerPairNonlattice
import Mathlib.Topology.Order.Compact

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem open_domain_tilted_weak_cramer_nonlattice
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (beta c R : ℝ) (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ x : ℝ,
        Complex.exp (((u * x + v * x ^ 2 : ℝ) : ℂ) * Complex.I)
          ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))‖ ≤
            1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta)) :
    let nu : Measure ℝ := mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)
    IsProbabilityMeasure nu ∧ ∀ u v : ℝ, u ≠ 0 ∨ v ≠ 0 →
      ‖(∫ x : ℝ,
        Complex.exp (((u * x + v * x ^ 2 : ℝ) : ℂ) * Complex.I) ∂nu)‖ < 1 := by
  dsimp only
  let nu : Measure ℝ := mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)
  have hf : Integrable (fun x : ℝ =>
      Real.exp (theta.1 * x + theta.2 * x ^ 2)) mu := interior_subset htheta
  letI : IsProbabilityMeasure nu := isProbabilityMeasure_tilted hf
  let W : ℝ → (ℝ × ℝ) := fun x => (x, x ^ 2)
  have hW : Continuous W := by dsimp [W]; fun_prop
  let law : Measure (ℝ × ℝ) := nu.map W
  have hlaw : IsProbabilityMeasure law :=
    (Measure.isProbabilityMeasure_map_iff hW.measurable.aemeasurable).mpr inferInstance
  letI : IsProbabilityMeasure law := hlaw
  have hint : ∀ u v : ℝ,
      (∫ w : ℝ × ℝ,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law) =
      ∫ x : ℝ, Complex.exp (((u * x + v * x ^ 2 : ℝ) : ℂ) * Complex.I) ∂nu := by
    intro u v
    exact MeasureTheory.integral_map hW.measurable.aemeasurable
      (show Continuous (fun w : ℝ × ℝ =>
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I)) by
          fun_prop).aestronglyMeasurable
  have hWClaw : ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤
        1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta) := by
    intro u v huv
    rw [hint]
    exact hWC u v huv
  refine ⟨inferInstance, ?_⟩
  intro u v hne
  rw [← hint]
  exact weak_cramer_pair_characteristic_norm_lt_one
    law beta c R hbeta hc hR hWClaw u v hne

theorem compact_open_domain_tilted_frequency_gap
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
    (K : Set (ℝ × ℝ)) (hKcompact : IsCompact K)
    (hzero : ∀ a ∈ K, a.1 ≠ 0 ∨ a.2 ≠ 0) :
    ∃ gamma : ℝ, 0 < gamma ∧ gamma < 1 ∧
      ∀ theta ∈ Theta, ∀ a ∈ K,
        ‖(∫ x : ℝ,
          Complex.exp (((a.1 * x + a.2 * x ^ 2 : ℝ) : ℂ) * Complex.I)
            ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))‖ ≤ gamma := by
  let F : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ := fun z =>
    ‖(∫ x : ℝ,
      Complex.exp (((z.2.1 * x + z.2.2 * x ^ 2 : ℝ) : ℂ) * Complex.I)
        ∂mu.tilted (fun x => z.1.1 * x + z.1.2 * x ^ 2))‖
  have hF : ContinuousOn F (Set.prod Theta K) := by
    intro z hz
    exact (open_domain_tilted_fourier_continuousAt
      mu z.1 z.2 (hTheta hz.1)).2.2.norm.continuousWithinAt
  by_cases hne : (Set.prod Theta K).Nonempty
  · obtain ⟨z, hz, hmax⟩ := (hcompact.prod hKcompact).exists_isMaxOn hne hF
    have hlt : F z < 1 :=
      (open_domain_tilted_weak_cramer_nonlattice
        mu z.1 (hTheta hz.1) beta c R hbeta hc hR (hWC z.1 hz.1)).2
          z.2.1 z.2.2 (hzero z.2 hz.2)
    have hnonneg : 0 ≤ F z := norm_nonneg _
    refine ⟨(F z + 1) / 2, by linarith, by linarith, ?_⟩
    intro theta htheta a ha
    have hle : F (theta, a) ≤ F z := hmax ⟨htheta, ha⟩
    exact hle.trans (by linarith)
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    intro theta htheta a ha
    exact (hne ⟨(theta, a), htheta, ha⟩).elim

end
end Shao.OQ3
