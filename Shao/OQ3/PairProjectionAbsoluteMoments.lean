import Shao.OQ3.PairCharacteristicQuadraticRemainder

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem pair_projection_absolute_moment_bound
    (law : Measure (Fin 2 → ℝ)) (m : ℕ)
    (hM : Integrable (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m) law)
    (u v : ℝ) :
    let f : (Fin 2 → ℝ) → ℝ := fun y => |u * y 0 + v * y 1| ^ m
    Integrable f law ∧ 0 ≤ (∫ y, f y ∂law) ∧
      (∫ y, f y ∂law) ≤
        Real.sqrt (u ^ 2 + v ^ 2) ^ m *
          (∫ y : Fin 2 → ℝ, Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m ∂law) := by
  intro f
  let C : ℝ := Real.sqrt (u ^ 2 + v ^ 2) ^ m
  have hbound (y : Fin 2 → ℝ) :
      f y ≤ C * Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m := by
    change |u * y 0 + v * y 1| ^ m ≤
      Real.sqrt (u ^ 2 + v ^ 2) ^ m * Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m
    calc
      _ ≤ (Real.sqrt (u ^ 2 + v ^ 2) * Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ m :=
        pow_le_pow_left₀ (abs_nonneg _) (pair_linear_projection_abs_le_euclidean u v (y 0) (y 1)) m
      _ = _ := mul_pow _ _ _
  have hmajor : Integrable (fun y : Fin 2 → ℝ =>
      C * Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m) law := hM.const_mul C
  have hc : Continuous f := by
    dsimp [f]
    fun_prop
  have hf : Integrable f law := by
    apply hmajor.mono' hc.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun y => by
      change ‖|u * y 0 + v * y 1| ^ m‖ ≤
        C * Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m
      simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using hbound y)
  refine ⟨hf, integral_nonneg (fun y => pow_nonneg (abs_nonneg _) m), ?_⟩
  calc
    _ ≤ ∫ y : Fin 2 → ℝ, C * Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m ∂law :=
      integral_mono hf hmajor hbound
    _ = Real.sqrt (u ^ 2 + v ^ 2) ^ m *
          (∫ y : Fin 2 → ℝ, Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m ∂law) := by
      rw [integral_const_mul]

end
end Shao.OQ3

