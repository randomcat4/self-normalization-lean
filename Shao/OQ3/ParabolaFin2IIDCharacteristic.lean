import Shao.OQ3.NormalizedIIDPairCharacteristic
import Mathlib.Data.Matrix.Mul

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Matrix Topology BigOperators
noncomputable section

theorem iid_parabola_fin2_characteristic_factor
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 1 ≤ n)
    (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ)
    (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (hpoint : ∀ x : ℝ, E ((x, x ^ 2) - (b 0, b 1)) =
      ((A *ᵥ (![x, x ^ 2] - b)) 0, (A *ᵥ (![x, x ^ 2] - b)) 1))
    (xi eta : ℝ) :
    let Y : ℝ → (Fin 2 → ℝ) := fun x => A *ᵥ (![x, x ^ 2] - b)
    let law : Measure (Fin 2 → ℝ) := nu.map Y
    let Phi : ℝ → ℝ → ℂ := fun u v =>
      ∫ y : Fin 2 → ℝ,
        Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂law
    let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    let T : Shao.Path n → (ℝ × ℝ) := fun z =>
      Real.sqrt (n : ℝ) • E (M z - (b 0, b 1))
    let rho : Measure (ℝ × ℝ) := Q.map T
    IsProbabilityMeasure law ∧ IsProbabilityMeasure rho ∧
      (∫ w : ℝ × ℝ,
        Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho) =
          (Phi (xi / Real.sqrt (n : ℝ)) (eta / Real.sqrt (n : ℝ))) ^ n := by
  dsimp only
  let Y : ℝ → (Fin 2 → ℝ) := fun x => A *ᵥ (![x, x ^ 2] - b)
  let law : Measure (Fin 2 → ℝ) := nu.map Y
  let Phi : ℝ → ℝ → ℂ := fun u v =>
    ∫ y : Fin 2 → ℝ,
      Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂law
  let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let M : Shao.Path n → (ℝ × ℝ) := fun z =>
    ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
  let T : Shao.Path n → (ℝ × ℝ) := fun z =>
    Real.sqrt (n : ℝ) • E (M z - (b 0, b 1))
  let rho : Measure (ℝ × ℝ) := Q.map T
  have hY : Continuous Y := by
    apply continuous_pi
    intro i
    change Continuous (fun x : ℝ => ∑ j : Fin 2, A i j * (![x, x ^ 2] - b) j)
    apply continuous_finsetSum
    intro j hj
    fin_cases j <;> simp <;> fun_prop
  have hlaw : IsProbabilityMeasure law :=
    (Measure.isProbabilityMeasure_map_iff hY.measurable.aemeasurable).mpr inferInstance
  refine ⟨hlaw, (iid_parabola_affine_standardized_law nu n hn (b 0, b 1) E).2.1, ?_⟩
  have hPhi : ∀ u v : ℝ,
      (∫ x : ℝ,
        Complex.exp (((u * (E ((x, x ^ 2) - (b 0, b 1))).1 +
          v * (E ((x, x ^ 2) - (b 0, b 1))).2 : ℝ) : ℂ) * Complex.I) ∂nu) =
            Phi u v := by
    intro u v
    have hmap := MeasureTheory.integral_map (μ := nu) hY.measurable.aemeasurable
      (show Continuous (fun y : Fin 2 → ℝ =>
        Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I)) by
          fun_prop).aestronglyMeasurable
    change _ = ∫ y : Fin 2 → ℝ,
      Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂nu.map Y
    rw [hmap]
    apply integral_congr_ae
    filter_upwards [] with x
    have hx := hpoint x
    change E ((x, x ^ 2) - (b 0, b 1)) = (Y x 0, Y x 1) at hx
    rw [hx]
  have hf := iid_parabola_standardized_characteristic_factor nu n hn (b 0, b 1) E xi eta
  dsimp only at hf
  rw [hPhi] at hf
  exact hf

end
end Shao.OQ3
