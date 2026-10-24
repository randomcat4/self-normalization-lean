import Shao.OQ3.PairProjectionAbsoluteMoments
import Mathlib.Analysis.Real.Sqrt

namespace Shao.OQ3

open MeasureTheory
open scoped BigOperators
noncomputable section

theorem pair_projection_moment_homogeneity
    (law : Measure (Fin 2 → ℝ)) (m : ℕ)
    (hI : Integrable
      (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m) law)
    (u v s : ℝ) :
    let L : (Fin 2 → ℝ) → ℝ := fun y => u * y 0 + v * y 1
    Integrable (fun y => L y ^ m) law ∧
      Integrable (fun y : Fin 2 → ℝ => ((s * u) * y 0 + (s * v) * y 1) ^ m) law ∧
      (∫ y : Fin 2 → ℝ, ((s * u) * y 0 + (s * v) * y 1) ^ m ∂law) =
        s ^ m * (∫ y, L y ^ m ∂law) := by
  intro L
  have hcont : Continuous L := by
    dsimp only [L]
    fun_prop
  have hbase : Integrable (fun y => L y ^ m) law := by
    apply (integrable_norm_iff (hcont.pow m).aestronglyMeasurable).mp
    change Integrable (fun y : Fin 2 → ℝ => ‖L y ^ m‖) law
    simpa only [Real.norm_eq_abs, abs_pow, L] using
      (pair_projection_absolute_moment_bound law m hI u v).1
  have hscale (y : Fin 2 → ℝ) :
      ((s * u) * y 0 + (s * v) * y 1) ^ m = s ^ m * L y ^ m := by
    dsimp only [L]
    rw [show s * u * y 0 + s * v * y 1 =
      s * (u * y 0 + v * y 1) by ring, mul_pow]
  have hscaled : Integrable
      (fun y : Fin 2 → ℝ => ((s * u) * y 0 + (s * v) * y 1) ^ m) law :=
    (hbase.const_mul (s ^ m)).congr (Filter.Eventually.of_forall fun y => (hscale y).symm)
  refine ⟨hbase, hscaled, ?_⟩
  calc
    (∫ y : Fin 2 → ℝ, ((s * u) * y 0 + (s * v) * y 1) ^ m ∂law) =
        ∫ y, s ^ m * L y ^ m ∂law :=
      integral_congr_ae (Filter.Eventually.of_forall hscale)
    _ = s ^ m * (∫ y, L y ^ m ∂law) := by rw [integral_const_mul]

theorem euclidean_frequency_radius_scalar_mul (s u v : ℝ) :
    Real.sqrt ((s * u) ^ 2 + (s * v) ^ 2) =
      |s| * Real.sqrt (u ^ 2 + v ^ 2) := by
  rw [show (s * u) ^ 2 + (s * v) ^ 2 = s ^ 2 * (u ^ 2 + v ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs]

end
end Shao.OQ3
