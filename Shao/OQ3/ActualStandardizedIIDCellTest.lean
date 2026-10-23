import Shao.OQ3.ParabolaIIDStandardizedLaw
import Shao.OQ3.StandardizedCellBoundedBorelTest
import Shao.OQ3.StandardizedCellChangeOfMeasure

namespace Shao.OQ3
open MeasureTheory
open scoped Topology BigOperators
noncomputable section

theorem iid_quadratic_standardized_rectangular_bounded_test
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    (n : ℕ) (hn : 1 ≤ n) (y : ℝ × ℝ)
    (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (aL aR qL qR M0 R0 S0 : ℝ)
    (hM0 : 0 ≤ M0) (hR0 : 0 ≤ R0) (hS0 : 0 ≤ S0)
    (hboundTheta : ‖theta‖ ≤ M0)
    (hE : ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ R0)
    (hEinv : ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ S0)
    (hy : y ∈ Set.Icc aL aR ×ˢ Set.Icc qL qR)
    (hawidth : aR - aL ≤ 1 / (n : ℝ))
    (hqwidth : qR - qL ≤ 1 / (n : ℝ))
    (A : Set (ℝ × ℝ)) (hA : MeasurableSet A)
    (hrect : A ⊆ Set.Ioc aL aR ×ˢ Set.Ioc qL qR) :
    let f : ℝ → ℝ := fun x => theta.1 * x + theta.2 * x ^ 2
    let K : ℝ := Real.log (∫ x : ℝ, Real.exp (f x) ∂mu)
    let nu : Measure ℝ := mu.tilted f
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    let F : (ℝ × ℝ) → (ℝ × ℝ) := fun w => Real.sqrt (n : ℝ) • E (w - y)
    let T : Shao.Path n → (ℝ × ℝ) := fun z => F (M z)
    let rho : Measure (ℝ × ℝ) := Q.map T
    let B : Set (ℝ × ℝ) := {v | y + (Real.sqrt (n : ℝ))⁻¹ • E.symm v ∈ A}
    let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-Real.sqrt (n : ℝ) *
      (theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2))
    let C0 : ℝ := Real.exp ((2 * M0) * S0 * R0)
    let Y : ℝ → (ℝ × ℝ) := fun x => E ((x, x ^ 2) - y)
    let law : Measure (ℝ × ℝ) := nu.map Y
    let QY : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
    let SN : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun v =>
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, v i
    IsProbabilityMeasure nu ∧ IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
      IsProbabilityMeasure law ∧ IsProbabilityMeasure rho ∧ rho = QY.map SN ∧
      0 < C0 ∧ MeasurableSet B ∧ B = F '' A ∧
      Measurable (B.indicator g) ∧
      (∀ v : ℝ × ℝ, |B.indicator g v| ≤ C0) ∧
      Integrable (B.indicator g) rho ∧
      P.real (M ⁻¹' A) =
        Real.exp (-(n : ℝ) * (theta.1 * y.1 + theta.2 * y.2 - K)) *
          ∫ v : ℝ × ℝ, B.indicator g v ∂rho := by
  dsimp only
  let f : ℝ → ℝ := fun x => theta.1 * x + theta.2 * x ^ 2
  have hf : Integrable (fun x : ℝ => Real.exp (f x)) mu := htheta
  let nu : Measure ℝ := mu.tilted f
  letI : IsProbabilityMeasure nu := isProbabilityMeasure_tilted hf
  let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let M : Shao.Path n → (ℝ × ℝ) := fun z =>
    ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
  let T : Shao.Path n → (ℝ × ℝ) := fun z =>
    Real.sqrt (n : ℝ) • E (M z - y)
  let rho : Measure (ℝ × ℝ) := Q.map T
  obtain ⟨hlaw, hrho, _, hnormalized⟩ :=
    iid_parabola_affine_standardized_law nu n hn y E
  letI : IsProbabilityMeasure rho := hrho
  obtain ⟨hC0, hB, hBeq, hmeas, hbound, hint⟩ :=
    standardized_rectangular_cell_uniform_bounded_borel_test n hn theta E y
      aL aR qL qR M0 R0 S0 hM0 hR0 hS0 hboundTheta hE hEinv
      hy hawidth hqwidth A hA hrect rho
  have hchange := iid_quadratic_standardized_cell_change_of_measure
    mu theta htheta n hn y E A hA
  refine ⟨inferInstance, inferInstance, inferInstance, hlaw, hrho, hnormalized,
    hC0, hB, hBeq, hmeas, hbound, hint, ?_⟩
  rw [integral_indicator hB]
  exact hchange.2.2.2

end
end Shao.OQ3
