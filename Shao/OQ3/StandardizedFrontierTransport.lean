import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.Homeomorph.Defs

namespace Shao.OQ3
open scoped Topology
noncomputable section

theorem standardized_frontier_image
    (n : ℕ) (hn : 1 ≤ n) (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (y : ℝ × ℝ) (A : Set (ℝ × ℝ)) :
    frontier ((fun w : ℝ × ℝ => Real.sqrt (n : ℝ) • E (w - y)) '' A) =
      (fun w : ℝ × ℝ => Real.sqrt (n : ℝ) • E (w - y)) '' frontier A := by
  have hN : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn)
  let s : ℝ := Real.sqrt (n : ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr hN
  let H : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
    { toFun := fun w => s • E (w - y)
      invFun := fun v => E.symm (s⁻¹ • v) + y
      left_inv := by
        intro w
        simp [smul_smul, hs.ne']
      right_inv := by
        intro v
        simp [smul_smul, hs.ne']
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact (H.image_frontier A).symm

end
end Shao.OQ3

