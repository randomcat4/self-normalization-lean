import Shao.OQ3.OpenDomainMeanInverse
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace Shao.OQ3
open scoped Matrix
noncomputable section

theorem covariance_row_equivalence_inverse_quadratic
    (D : Matrix (Fin 2) (Fin 2) ℝ) (hdet : D.det ≠ 0)
    (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (hL : ∀ w : ℝ × ℝ, L w =
      (D 0 0 * w.1 + D 0 1 * w.2, D 1 0 * w.1 + D 1 1 * w.2)) :
    ∀ w : ℝ × ℝ,
      D⁻¹ *ᵥ ![w.1, w.2] = ![(L.symm w).1, (L.symm w).2] ∧
        w.1 * (L.symm w).1 + w.2 * (L.symm w).2 =
          dotProduct ![w.1, w.2] (D⁻¹ *ᵥ ![w.1, w.2]) := by
  intro w
  let x : Fin 2 → ℝ := ![(L.symm w).1, (L.symm w).2]
  have hrow :
      (D 0 0 * (L.symm w).1 + D 0 1 * (L.symm w).2,
        D 1 0 * (L.symm w).1 + D 1 1 * (L.symm w).2) = w :=
    (hL (L.symm w)).symm.trans (L.apply_symm_apply w)
  have hDx : D *ᵥ x = ![w.1, w.2] := by
    ext i
    fin_cases i
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, x] using
        congrArg Prod.fst hrow
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, x] using
        congrArg Prod.snd hrow
  have hinv : D⁻¹ *ᵥ ![w.1, w.2] = x := by
    rw [← hDx, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul D (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  refine ⟨hinv, ?_⟩
  rw [hinv]
  simp [dotProduct, Fin.sum_univ_two, x]

end
end Shao.OQ3
