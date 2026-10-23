import Shao.OQ3.QuadraticSampleChangeOfMeasure
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem iid_quadratic_standardized_cell_change_of_measure
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    (n : ℕ) (hn : 1 ≤ n) (y : ℝ × ℝ)
    (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) :
    let f : ℝ → ℝ := fun x => theta.1 * x + theta.2 * x ^ 2
    let K : ℝ := Real.log (∫ x : ℝ, Real.exp (f x) ∂mu)
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu.tilted f)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    let F : (ℝ × ℝ) → (ℝ × ℝ) := fun w => Real.sqrt (n : ℝ) • E (w - y)
    let T : Shao.Path n → (ℝ × ℝ) := fun z => F (M z)
    let rho : Measure (ℝ × ℝ) := Measure.map T Q
    let B : Set (ℝ × ℝ) := {v | y + (Real.sqrt (n : ℝ))⁻¹ • E.symm v ∈ A}
    let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-Real.sqrt (n : ℝ) *
      (theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2))
    MeasurableSet B ∧ B = F '' A ∧ Integrable g rho ∧
      P.real (M ⁻¹' A) = Real.exp (-(n : ℝ) * (theta.1 * y.1 + theta.2 * y.2 - K)) *
        ∫ v : ℝ × ℝ in B, g v ∂rho := by
  let f : ℝ → ℝ := fun x => theta.1 * x + theta.2 * x ^ 2
  let K : ℝ := Real.log (∫ x : ℝ, Real.exp (f x) ∂mu)
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
  let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu.tilted f)
  let M : Shao.Path n → (ℝ × ℝ) := fun z =>
    ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
  let F : (ℝ × ℝ) → (ℝ × ℝ) := fun w => Real.sqrt (n : ℝ) • E (w - y)
  let T : Shao.Path n → (ℝ × ℝ) := fun z => F (M z)
  let rho : Measure (ℝ × ℝ) := Measure.map T Q
  let B : Set (ℝ × ℝ) := {v | y + (Real.sqrt (n : ℝ))⁻¹ • E.symm v ∈ A}
  let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-Real.sqrt (n : ℝ) *
    (theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2))
  let G : Shao.Path n → ℝ := fun z => Real.exp (-(theta.1 *
    ((∑ i : Fin n, z i) - (n : ℝ) * y.1) +
    theta.2 * (Shao.energy z - (n : ℝ) * y.2)))
  have hN : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hN
  have hinv (w : ℝ × ℝ) :
      y + (Real.sqrt (n : ℝ))⁻¹ • E.symm (F w) = w := by
    dsimp only [F]
    rw [map_smul, E.symm_apply_apply, ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ hs.ne', one_smul]
    abel
  have hforward (v : ℝ × ℝ) :
      F (y + (Real.sqrt (n : ℝ))⁻¹ • E.symm v) = v := by
    dsimp only [F]
    rw [show y + (Real.sqrt (n : ℝ))⁻¹ • E.symm v - y =
      (Real.sqrt (n : ℝ))⁻¹ • E.symm v from by abel,
      map_smul, E.apply_symm_apply, ← smul_assoc, smul_eq_mul, mul_inv_cancel₀ hs.ne', one_smul]
  have hM : Continuous M := by dsimp [M, Shao.energy]; fun_prop
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hT : Continuous T := hF.comp hM
  have hInv : Continuous (fun v : ℝ × ℝ => y + (Real.sqrt (n : ℝ))⁻¹ • E.symm v) := by
    fun_prop
  have hB : MeasurableSet B := hInv.measurable hA
  have himage : B = F '' A := by
    ext v
    constructor
    · intro hv
      exact ⟨y + (Real.sqrt (n : ℝ))⁻¹ • E.symm v, hv, hforward v⟩
    · rintro ⟨w, hw, rfl⟩
      change y + (Real.sqrt (n : ℝ))⁻¹ • E.symm (F w) ∈ A
      rw [hinv]
      exact hw
  have hpre : T ⁻¹' B = M ⁻¹' A := by
    ext z
    change (y + (Real.sqrt (n : ℝ))⁻¹ • E.symm (F (M z)) ∈ A) ↔ M z ∈ A
    rw [hinv]
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hcoord (x b : ℝ) : Real.sqrt (n : ℝ) *
      (Real.sqrt (n : ℝ) * (x / (n : ℝ) - b)) = x - (n : ℝ) * b := by
    calc
      _ = (Real.sqrt (n : ℝ)) ^ 2 * (x / (n : ℝ) - b) := by ring
      _ = _ := by rw [Real.sq_sqrt hN.le]; field_simp
  have hET (z : Shao.Path n) : E.symm (T z) =
      Real.sqrt (n : ℝ) • (M z - y) := by
    dsimp only [T, F]
    rw [map_smul, E.symm_apply_apply]
  have hpull (z : Shao.Path n) : g (T z) = G z := by
    dsimp only [g, G]
    rw [hET]
    congr 1
    change -Real.sqrt (n : ℝ) *
      (theta.1 * (Real.sqrt (n : ℝ) * ((∑ i : Fin n, z i) / (n : ℝ) - y.1)) +
      theta.2 * (Real.sqrt (n : ℝ) * (Shao.energy z / (n : ℝ) - y.2))) = _
    calc
      _ = -(theta.1 * (Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ) *
          ((∑ i : Fin n, z i) / (n : ℝ) - y.1))) +
          theta.2 * (Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ) *
          (Shao.energy z / (n : ℝ) - y.2)))) := by ring
      _ = _ := by rw [hcoord, hcoord]
  obtain ⟨hG, hcell⟩ := iid_quadratic_cell_change_of_measure mu theta htheta n y A hA
  have hG0 : Integrable G Q := hG
  have hgRho : Integrable g rho := by
    apply (integrable_map_measure hg.aestronglyMeasurable hT.measurable.aemeasurable).mpr
    simpa only [Function.comp_def, hpull] using hG0
  have hIntegral : (∫ v : ℝ × ℝ in B, g v ∂rho) =
      ∫ z : Shao.Path n in M ⁻¹' A, G z ∂Q := by
    rw [setIntegral_map hB hg.aestronglyMeasurable hT.measurable.aemeasurable, hpre]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hpull
  refine ⟨hB, himage, hgRho, ?_⟩
  rw [hIntegral]
  exact hcell

end
end Shao.OQ3
