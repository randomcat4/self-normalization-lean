import Shao.OQ3.GaussianNoiseTailBounds
import Shao.OQ3.GaussianSmoothingScale
import Shao.OQ3.IndependentSumThickeningBounds

namespace Shao.OQ3
open MeasureTheory
open scoped NNReal
noncomputable section

theorem cubic_pair_gaussian_noise_tail_bound
    (n : ℕ) (hn : 1 ≤ n) :
    let b : ℝ := 1 / (2 * (n : ℝ) ^ 6)
    let eps : ℝ := Real.log (n : ℝ) / (n : ℝ) ^ 3
    let v : ℝ≥0 := Real.toNNReal (2 * b)
    let gamma : Measure (ℝ × ℝ) :=
      (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
    gamma.real {y : ℝ × ℝ | eps < ‖y‖} ≤
      4 * Real.exp (-(Real.log (n : ℝ)) ^ 2 / 2) := by
  intro b eps v gamma
  obtain ⟨hb, heps, hid⟩ := cubic_gaussian_smoothing_scale_identity n hn
  change Real.exp (-eps ^ 2 / (4 * b)) =
    Real.exp (-(Real.log (n : ℝ)) ^ 2 / 2) at hid
  calc
    _ ≤ 4 * Real.exp (-eps ^ 2 / (4 * b)) :=
      pair_gaussian_noise_tail_le b hb eps heps
    _ = _ := by rw [hid]

theorem eventually_cubic_pair_gaussian_noise_tail
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let b : ℝ := 1 / (2 * (n : ℝ) ^ 6)
      let eps : ℝ := Real.log (n : ℝ) / (n : ℝ) ^ 3
      let v : ℝ≥0 := Real.toNNReal (2 * b)
      let gamma : Measure (ℝ × ℝ) :=
        (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
      gamma.real {y : ℝ × ℝ | eps < ‖y‖} ≤ Real.rpow (n : ℝ) (-a) := by
  obtain ⟨N, hN, H⟩ := cubic_gaussian_smoothing_scale_superpolynomial a ha
  refine ⟨N, hN, ?_⟩
  intro n hn b eps v gamma
  obtain ⟨hb, heps, hdecay⟩ := H n hn
  exact (pair_gaussian_noise_tail_le b hb eps heps).trans hdecay

theorem eventually_cubic_gaussian_smoothed_set_sandwich
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (nu : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu]
        (s : Set (ℝ × ℝ)), MeasurableSet s →
      let b : ℝ := 1 / (2 * (n : ℝ) ^ 6)
      let eps : ℝ := Real.log (n : ℝ) / (n : ℝ) ^ 3
      let v : ℝ≥0 := Real.toNNReal (2 * b)
      let gamma : Measure (ℝ × ℝ) :=
        (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
      let rho : Measure (ℝ × ℝ) := (nu.prod gamma).map (fun q => q.1 + q.2)
      rho.real ((Metric.cthickening eps sᶜ)ᶜ) - Real.rpow (n : ℝ) (-a) ≤ nu.real s ∧
        nu.real s ≤ rho.real (Metric.cthickening eps s) + Real.rpow (n : ℝ) (-a) := by
  obtain ⟨N, hN, H⟩ := eventually_cubic_pair_gaussian_noise_tail a ha
  refine ⟨N, hN, ?_⟩
  intro n hn nu hnu s hs b eps v gamma rho
  letI : IsProbabilityMeasure nu := hnu
  letI : IsProbabilityMeasure gamma := by dsimp only [gamma]; infer_instance
  have ht := H n hn
  change gamma.real {y : ℝ × ℝ | eps < ‖y‖} ≤ Real.rpow (n : ℝ) (-a) at ht
  have hset := independent_sum_cthickening_real_sandwich nu gamma s hs eps
  exact ⟨(sub_le_sub_left ht _).trans hset.1,
    hset.2.trans (add_le_add_left ht _)⟩

end
end Shao.OQ3
