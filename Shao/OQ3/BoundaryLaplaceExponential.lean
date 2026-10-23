import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Shao.OQ3
open scoped Topology
noncomputable section

theorem abs_exp_neg_sub_exp_neg_le
    (a b d : ℝ) (ha : d ≤ a) (hb : d ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ Real.exp (-d) * |a - b| := by
  have hd (t : ℝ) : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-t)) t := by
    convert! (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg using 1
    simp
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (min a b) (max a b)) :
      ‖-Real.exp (-t)‖ ≤ Real.exp (-d) := by
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (neg_le_neg ((le_min ha hb).trans ht.1))
  have hm := (convex_Icc (min a b) (max a b)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hd t).hasDerivWithinAt) hbound
    (show b ∈ Set.Icc (min a b) (max a b) from ⟨min_le_right _ _, le_max_right _ _⟩)
    (show a ∈ Set.Icc (min a b) (max a b) from ⟨min_le_left _ _, le_max_left _ _⟩)
  simpa only [Real.norm_eq_abs] using hm

theorem abs_weighted_exp_neg_sub_le
    (a b w w0 d E Q : ℝ) (ha : d ≤ a) (hb : d ≤ b)
    (hexponent : |a - b| ≤ E) (hamplitude : |w - w0| ≤ Q) :
    |w * Real.exp (-a) - w0 * Real.exp (-b)| ≤
      (Q + |w0| * E) * Real.exp (-d) := by
  have hQ : 0 ≤ Q := (abs_nonneg _).trans hamplitude
  have hfirst : |w - w0| * Real.exp (-a) ≤ Q * Real.exp (-d) :=
    mul_le_mul hamplitude (Real.exp_le_exp.mpr (neg_le_neg ha))
      (Real.exp_pos _).le hQ
  have hsecond : |w0| * |Real.exp (-a) - Real.exp (-b)| ≤
      |w0| * (Real.exp (-d) * E) :=
    mul_le_mul_of_nonneg_left ((abs_exp_neg_sub_exp_neg_le a b d ha hb).trans
      (mul_le_mul_of_nonneg_left hexponent (Real.exp_pos _).le)) (abs_nonneg _)
  have heq : w * Real.exp (-a) - w0 * Real.exp (-b) =
      (w - w0) * Real.exp (-a) + w0 * (Real.exp (-a) - Real.exp (-b)) := by ring
  rw [heq]
  calc
    _ ≤ |(w - w0) * Real.exp (-a)| + |w0 * (Real.exp (-a) - Real.exp (-b))| :=
      abs_add_le _ _
    _ = |w - w0| * Real.exp (-a) + |w0| * |Real.exp (-a) - Real.exp (-b)| := by
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ Q * Real.exp (-d) + |w0| * (Real.exp (-d) * E) := add_le_add hfirst hsecond
    _ = (Q + |w0| * E) * Real.exp (-d) := by ring

end
end Shao.OQ3
