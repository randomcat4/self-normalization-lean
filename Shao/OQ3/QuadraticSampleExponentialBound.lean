import Shao.OQ3.QuadraticSampleChangeOfMeasure

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem iid_quadratic_exponential_separator_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    (n : ℕ) (hn : 1 ≤ n) (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) (c : ℝ)
    (hsep : ∀ w ∈ A, c ≤ theta.1 * w.1 + theta.2 * w.2 -
      Real.log (∫ x : ℝ, Real.exp (theta.1 * x + theta.2 * x ^ 2) ∂mu)) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    P.real (M ⁻¹' A) ≤ Real.exp (-(n : ℝ) * c) := by
  let f : ℝ → ℝ := fun x => theta.1 * x + theta.2 * x ^ 2
  let K : ℝ := Real.log (∫ x : ℝ, Real.exp (f x) ∂mu)
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
  let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu.tilted f)
  let M : Shao.Path n → (ℝ × ℝ) := fun z =>
    ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
  let E : Set (Shao.Path n) := M ⁻¹' A
  let G : Shao.Path n → ℝ := fun z => Real.exp (-(theta.1 * (∑ i : Fin n, z i) +
    theta.2 * Shao.energy z))
  have hf : Integrable (fun x : ℝ => Real.exp (f x)) mu := htheta
  let : IsProbabilityMeasure (mu.tilted f) := isProbabilityMeasure_tilted hf
  have hM : Continuous M := by dsimp [M, Shao.energy]; fun_prop
  have hE : MeasurableSet E := hM.measurable hA
  have hN : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn)
  obtain ⟨hG, hcell⟩ := iid_quadratic_cell_change_of_measure mu theta htheta n (0, 0) A hA
  have hG0 : Integrable G Q := by
    simpa only [mul_zero, sub_zero, Prod.fst_zero, Prod.snd_zero] using hG
  have hidentity : P.real E = Real.exp ((n : ℝ) * K) *
      ∫ z : Shao.Path n in E, G z ∂Q := by
    simpa only [Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero, sub_zero,
      zero_sub, neg_mul_neg] using hcell
  have hpoint (z : Shao.Path n) (hz : z ∈ E) :
      G z ≤ Real.exp (-(n : ℝ) * (c + K)) := by
    have htest : c ≤ theta.1 * ((∑ i : Fin n, z i) / (n : ℝ)) +
        theta.2 * (Shao.energy z / (n : ℝ)) - K := hsep (M z) hz
    have hfrac : theta.1 * ((∑ i : Fin n, z i) / (n : ℝ)) +
        theta.2 * (Shao.energy z / (n : ℝ)) =
        (theta.1 * (∑ i : Fin n, z i) + theta.2 * Shao.energy z) / (n : ℝ) := by ring
    rw [hfrac] at htest
    have hraw : (c + K) * (n : ℝ) ≤
        theta.1 * (∑ i : Fin n, z i) + theta.2 * Shao.energy z :=
      (le_div_iff₀ hN).mp (by linarith)
    apply Real.exp_le_exp.mpr
    change -(theta.1 * (∑ i : Fin n, z i) + theta.2 * Shao.energy z) ≤
      -(n : ℝ) * (c + K)
    nlinarith
  have hint : (∫ z : Shao.Path n in E, G z ∂Q) ≤
      Real.exp (-(n : ℝ) * (c + K)) * Q.real E := by
    calc
      _ ≤ ∫ _ : Shao.Path n in E, Real.exp (-(n : ℝ) * (c + K)) ∂Q := by
        apply integral_mono_ae hG0.integrableOn (integrable_const _)
        filter_upwards [ae_restrict_mem hE] with z hz
        exact hpoint z hz
      _ = _ := by simp [measureReal_def, mul_comm]
  have hmass : Q.real E ≤ 1 := measureReal_le_one
  calc
    _ = Real.exp ((n : ℝ) * K) * ∫ z : Shao.Path n in E, G z ∂Q := hidentity
    _ ≤ Real.exp ((n : ℝ) * K) *
        (Real.exp (-(n : ℝ) * (c + K)) * Q.real E) :=
      mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le
    _ ≤ Real.exp ((n : ℝ) * K) * (Real.exp (-(n : ℝ) * (c + K)) * 1) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = Real.exp (-(n : ℝ) * c) := by
      rw [mul_one, ← Real.exp_add]
      congr 1
      ring

end
end Shao.OQ3
