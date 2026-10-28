import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem ae_coordinate_square_affine_preimage (m : ℕ) (b c : ℝ) (hc : c ≠ 0)
    (P : (Fin m → ℝ) → Prop) (hP : ∀ᵐ y ∂(volume : Measure (Fin m → ℝ)), P y) :
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), (∀ j, 0 < x j) →
      P (fun j => (x j ^ 2 - b) / c) := by
  classical
  let G : (Fin m → ℝ) → (Fin m → ℝ) := fun y j => Real.sqrt (c * y j + b)
  let S : Set (Fin m → ℝ) := {y | ¬P y ∧ ∀ j, 0 < c * y j + b}
  have hbad : volume {y | ¬P y} = 0 := ae_iff.mp hP
  have hS : volume S = 0 := measure_mono_null (fun _ hy => hy.1) hbad
  have hG : DifferentiableOn ℝ G S := by
    intro y hy
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_pi.mpr
    intro j
    exact (((differentiableAt_apply j y).const_mul c).add_const b).sqrt
      (ne_of_gt (hy.2 j))
  have himage : volume (G '' S) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hG hS
  have halg (x : ℝ) : c * ((x ^ 2 - b) / c) + b = x ^ 2 := by
    field_simp <;> ring
  apply ae_iff.mpr
  apply measure_mono_null ?_ himage
  intro x hx
  have hx' : (∀ j, 0 < x j) ∧ ¬P (fun j => (x j ^ 2 - b) / c) := not_imp.mp hx
  refine ⟨fun j => (x j ^ 2 - b) / c, ⟨hx'.2, ?_⟩, ?_⟩
  · intro j
    rw [halg]
    exact sq_pos_of_pos (hx'.1 j)
  · funext j
    change Real.sqrt (c * ((x j ^ 2 - b) / c) + b) = x j
    rw [halg, Real.sqrt_sq (hx'.1 j).le]

end
end Shao.OQ3
