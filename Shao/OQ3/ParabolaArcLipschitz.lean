import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

namespace Shao.OQ3
open scoped Topology
noncomputable section

theorem affine_segment_lipschitz
    (a b dx dq : ℝ) :
    LipschitzWith (Real.toNNReal (max |dx| |dq|))
      (fun t : ℝ => (a + t * dx, b + t * dq)) := by
  apply LipschitzWith.of_dist_le'
  intro t u
  have hx : a + t * dx - (a + u * dx) = dx * (t - u) := by ring
  have hq : b + t * dq - (b + u * dq) = dq * (t - u) := by ring
  simp only [dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
  rw [hx, hq, abs_mul, abs_mul]
  exact max_le
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))

theorem parabola_segment_lipschitz
    (a dx level shift M : ℝ) (hM : 0 ≤ M)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, |a + t * dx| ≤ M) :
    LipschitzOnWith (Real.toNNReal (|dx| * max 1 (2 * M / level ^ 2)))
      (fun t : ℝ => (a + t * dx, (a + t * dx) ^ 2 / level ^ 2 - shift))
      (Set.Icc (0 : ℝ) 1) := by
  apply LipschitzOnWith.of_dist_le'
  intro t ht u hu
  let x : ℝ := a + t * dx
  let z : ℝ := a + u * dx
  have hd : x - z = dx * (t - u) := by dsimp only [x, z]; ring
  have hs : |x + z| ≤ 2 * M := by
    calc
      |x + z| ≤ |x| + |z| := abs_add_le _ _
      _ ≤ M + M := add_le_add (hpos t ht) (hpos u hu)
      _ = 2 * M := by ring
  have hfirst : |x - z| ≤ (|dx| * max 1 (2 * M / level ^ 2)) * |t - u| := by
    calc
      |x - z| = (|dx| * 1) * |t - u| := by rw [hd, abs_mul]; ring
      _ ≤ (|dx| * max 1 (2 * M / level ^ 2)) * |t - u| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (abs_nonneg _)) (abs_nonneg _)
  have hsecond : |(x ^ 2 / level ^ 2 - shift) - (z ^ 2 / level ^ 2 - shift)| ≤
      (|dx| * max 1 (2 * M / level ^ 2)) * |t - u| := by
    have hpoly : x ^ 2 - z ^ 2 = (x + z) * (x - z) := by ring
    have hdiv : (x ^ 2 / level ^ 2 - shift) - (z ^ 2 / level ^ 2 - shift) =
        (x ^ 2 - z ^ 2) / level ^ 2 := by ring
    calc
      _ = |x + z| * |x - z| / level ^ 2 := by
        rw [hdiv, hpoly, abs_div, abs_mul, abs_of_nonneg (sq_nonneg level)]
      _ ≤ (2 * M) * (|dx| * |t - u|) / level ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg level)
        exact mul_le_mul hs (by rw [hd, abs_mul]) (abs_nonneg _) (by linarith [hM])
      _ = (|dx| * (2 * M / level ^ 2)) * |t - u| := by ring
      _ ≤ (|dx| * max 1 (2 * M / level ^ 2)) * |t - u| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (abs_nonneg _)) (abs_nonneg _)
  simpa only [dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub,
    Real.norm_eq_abs] using max_le hfirst hsecond

theorem standardized_lipschitz_arc
    (n : ℕ) (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (y : ℝ × ℝ)
    (f : ℝ → ℝ × ℝ) (K : NNReal)
    (hf : LipschitzOnWith K f (Set.Icc (0 : ℝ) 1)) :
    LipschitzOnWith (Real.toNNReal (Real.sqrt (n : ℝ) * ‖E‖ * (K : ℝ)))
      (fun t : ℝ => Real.sqrt (n : ℝ) • E (f t - y))
      (Set.Icc (0 : ℝ) 1) := by
  apply LipschitzOnWith.of_dist_le'
  intro t ht u hu
  have heq : (f t - y) - (f u - y) = f t - f u := by abel
  have hd : ‖f t - f u‖ ≤ (K : ℝ) * |t - u| := by
    simpa only [dist_eq_norm, Real.norm_eq_abs] using hf.dist_le_mul t ht u hu
  calc
    _ = Real.sqrt (n : ℝ) * ‖E (f t - f u)‖ := by
      rw [dist_eq_norm, ← smul_sub, ← map_sub, heq, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ Real.sqrt (n : ℝ) * (‖E‖ * ((K : ℝ) * |t - u|)) :=
      mul_le_mul_of_nonneg_left
        ((E.le_opNorm _).trans (mul_le_mul_of_nonneg_left hd (norm_nonneg _)))
        (Real.sqrt_nonneg _)
    _ = (Real.sqrt (n : ℝ) * ‖E‖ * (K : ℝ)) * dist t u := by
      rw [Real.dist_eq]
      ring

end
end Shao.OQ3

