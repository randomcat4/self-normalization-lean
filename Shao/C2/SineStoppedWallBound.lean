import Shao.C2.BrownianSineStoppedMesh
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
namespace Shao.C2.SineStoppedWallBound
open MeasureTheory Set Filter
open scoped NNReal Topology BigOperators
open Shao.C2.IntervalSineTerms Shao.C2.IntervalSineSeries Shao.C2.IntervalSpectralGaussian

private theorem low_sineSeries_strip_bound (j : ℕ) (hj : j ≤ 1) (a z H : ℝ)
    (ha : 0 < a) (hH : 0 < H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : ℝ, H ≤ U → ∀ x : ℝ, ‖mixedSineSeries j 0 a z U x‖ ≤ C := by
  let A : ℝ := (1 / a) * (Real.pi / (2 * a)) ^ j
  let W : ℕ → ℝ := weightedGaussian (Real.pi ^ 2 / 8) j (H / a ^ 2)
  let C : ℝ := A * ∑' n : ℕ, W n
  have hW : Summable W := weightedGaussian_summable (Real.pi ^ 2 / 8) (H / a ^ 2) j
    (by positivity) (by positivity)
  have hb (U : ℝ) (hHU : H ≤ U) (x : ℝ) : ‖mixedSineSeries j 0 a z U x‖ ≤ C := by
    have hs := mixedSineTerm_summable j 0 a z U x ha (hH.trans_le hHU)
    have ht (n : ℕ) : ‖mixedSineTerm j 0 a z U x n‖ ≤ A * W n := by
      simpa only [mul_zero, add_zero, pow_zero, mul_one] using
        mixedSineTerm_strip_bound j 0 a z H U x n ha hHU
    exact hs.hasSum.norm_le_of_bounded (hW.hasSum.mul_left A) ht
  exact ⟨C, (norm_nonneg _).trans (hb H le_rfl 0), hb⟩

theorem sineSeries_zero_walls (a z U : ℝ) (ha : 0 < a) :
    mixedSineSeries 0 0 a z U (-a) = 0 ∧ mixedSineSeries 0 0 a z U a = 0 := by
  change (∑' n : ℕ, mixedSineTerm 0 0 a z U (-a) n) = 0 ∧
    (∑' n : ℕ, mixedSineTerm 0 0 a z U a n) = 0
  simp only [mixedSineTerm, iteratedDeriv_zero]
  constructor
  · calc
      _ = ∑' _n : ℕ, (0 : ℝ) := tsum_congr fun n => by simp [sineTerm]
      _ = 0 := tsum_zero
  · have hz (n : ℕ) : sineTerm a z U a n = 0 := by
      have he : frequency a n * (a + a) = ((n + 1 : ℕ) : ℝ) * Real.pi := by
        dsimp only [frequency]
        push_cast
        field_simp [ha.ne'] <;> ring
      simp only [sineTerm, he, Real.sin_nat_mul_pi, mul_zero, zero_mul]
    calc
      _ = ∑' _n : ℕ, (0 : ℝ) := tsum_congr hz
      _ = 0 := tsum_zero

theorem sineSeries_uniform_bounded_lipschitz (a z H : ℝ) (ha : 0 < a) (hH : 0 < H) :
    ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧ ∀ U : ℝ, H ≤ U →
      (∀ x : ℝ, |mixedSineSeries 0 0 a z U x| ≤ M) ∧
      ∀ x y : ℝ, |mixedSineSeries 0 0 a z U x - mixedSineSeries 0 0 a z U y| ≤ L * |x - y| := by
  obtain ⟨M, hM0, hM⟩ := low_sineSeries_strip_bound 0 (by norm_num) a z H ha hH
  obtain ⟨L, hL0, hL⟩ := low_sineSeries_strip_bound 1 (by norm_num) a z H ha hH
  refine ⟨M, L, hM0, hL0, fun U hHU => ⟨?_, ?_⟩⟩
  · intro x
    simpa only [Real.norm_eq_abs] using hM U hHU x
  · intro x y
    have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := mixedSineSeries 0 0 a z U) (f' := mixedSineSeries 1 0 a z U)
      (s := (univ : Set ℝ)) (x := y) (y := x)
      (fun w _ => (mixedSineSeries_spatial_hasDerivAt 0 0 a z U w ha (hH.trans_le hHU)).hasDerivWithinAt)
      (fun w _ => hL U hHU w) convex_univ (mem_univ y) (mem_univ x)
    simpa only [Real.norm_eq_abs] using hh

theorem sineSeries_uniform_wall_bound (a z H : ℝ) (ha : 0 < a) (hH : 0 < H) :
    ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧ ∀ U : ℝ, H ≤ U → ∀ x : ℝ,
      |mixedSineSeries 0 0 a z U x| ≤ M ∧
      |mixedSineSeries 0 0 a z U x| ≤ L * abs (abs x - a) := by
  obtain ⟨M, L, hM0, hL0, hb⟩ := sineSeries_uniform_bounded_lipschitz a z H ha hH
  refine ⟨M, L, hM0, hL0, fun U hHU x => ⟨(hb U hHU).1 x, ?_⟩⟩
  by_cases hx : 0 ≤ x
  · have hh := (hb U hHU).2 x a
    rw [(sineSeries_zero_walls a z U ha).2, sub_zero] at hh
    simpa only [abs_of_nonneg hx] using hh
  · have hh := (hb U hHU).2 x (-a)
    rw [(sineSeries_zero_walls a z U ha).1, sub_zero] at hh
    have he : |x - (-a)| = abs (abs x - a) := by
      rw [abs_of_neg (lt_of_not_ge hx), show -x - a = -(x - (-a)) by ring, abs_neg]
    rw [he] at hh
    exact hh

end Shao.C2.SineStoppedWallBound
