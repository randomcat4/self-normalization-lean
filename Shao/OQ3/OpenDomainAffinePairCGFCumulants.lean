import Shao.OQ3.QuadraticTiltCumulants
import Shao.OQ3.ScalarCGFThirdFourthDerivatives

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Topology
noncomputable section

theorem open_domain_affine_pair_cgf_third_fourth_derivatives
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    let nu : Measure ℝ := mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)
    let means : Fin 2 → ℝ := ![∫ x : ℝ, x ∂nu, ∫ x : ℝ, x ^ 2 ∂nu]
    let Y : ℝ → (Fin 2 → ℝ) := fun x => A *ᵥ (![x, x ^ 2] - means)
    let law : Measure (Fin 2 → ℝ) := nu.map Y
    IsProbabilityMeasure law ∧ ∀ u v : ℝ,
      let X : (Fin 2 → ℝ) → ℝ := fun y => u * y 0 + v * y 1
      0 ∈ interior (ProbabilityTheory.integrableExpSet X law) ∧
        (∫ y : Fin 2 → ℝ, X y ∂law) = 0 ∧
        iteratedDeriv 3 (ProbabilityTheory.cgf X law) 0 =
          (∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 3 ∂law) ∧
        iteratedDeriv 4 (ProbabilityTheory.cgf X law) 0 =
          (∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 4 ∂law) -
            3 * (∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 2 ∂law) ^ 2 := by
  intro nu means Y law
  obtain ⟨hnu, hxL2, hx2L2, hdir⟩ :=
    open_domain_quadratic_tilt_directional_cumulants mu theta htheta
  letI : IsProbabilityMeasure nu := hnu
  have hY : Continuous Y := by
    apply continuous_pi
    intro j
    change Continuous (fun x : ℝ =>
      ∑ k : Fin 2, A j k * ((![x, x ^ 2] : Fin 2 → ℝ) k - means k))
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    fun_prop
  have hlaw : IsProbabilityMeasure law :=
    (Measure.isProbabilityMeasure_map_iff hY.measurable.aemeasurable).mpr inferInstance
  letI : IsProbabilityMeasure law := hlaw
  refine ⟨hlaw, ?_⟩
  intro u v X
  let d : ℝ × ℝ := (u * A 0 0 + v * A 1 0, u * A 0 1 + v * A 1 1)
  let F : ℝ → ℝ := fun x => d.1 * x + d.2 * x ^ 2
  let center : ℝ := d.1 * means 0 + d.2 * means 1
  have hX : Continuous X := by dsimp [X]; fun_prop
  have hid (x : ℝ) : X (Y x) = F x - center := by
    simp only [X, Y, F, center, d, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  obtain ⟨hF0, hFL2, _, _, _⟩ := hdir d
  have hFI : Integrable F nu := hFL2.integrable (by norm_num)
  have hFmean : (∫ x : ℝ, F x ∂nu) = center := by
    dsimp only [F, center]
    rw [integral_add ((hxL2.integrable (by norm_num)).const_mul d.1)
      ((hx2L2.integrable (by norm_num)).const_mul d.2), integral_const_mul, integral_const_mul]
    simp only [means, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rfl
  have hmeanX : (∫ y : Fin 2 → ℝ, X y ∂law) = 0 := by
    change (∫ y : Fin 2 → ℝ, X y ∂nu.map Y) = 0
    rw [integral_map hY.measurable.aemeasurable hX.aestronglyMeasurable]
    calc
      _ = ∫ x : ℝ, F x - center ∂nu := integral_congr_ae (Filter.Eventually.of_forall hid)
      _ = (∫ x : ℝ, F x ∂nu) - center := by
        rw [integral_sub hFI (integrable_const center)]
        simp
      _ = 0 := by rw [hFmean]; ring
  have hsubset : ProbabilityTheory.integrableExpSet F nu ⊆
      ProbabilityTheory.integrableExpSet X law := by
    intro q hq
    have hshift : Integrable (fun x : ℝ => Real.exp (q * (F x - center))) nu := by
      have hi : Integrable (fun x : ℝ => Real.exp (q * F x)) nu := hq
      convert hi.const_mul (Real.exp (-q * center)) using 1
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    have hg : Continuous (fun y : Fin 2 → ℝ => Real.exp (q * X y)) := by fun_prop
    change Integrable (fun y : Fin 2 → ℝ => Real.exp (q * X y)) (nu.map Y)
    apply (integrable_map_measure hg.aestronglyMeasurable hY.measurable.aemeasurable).mpr
    change Integrable (fun x : ℝ => Real.exp (q * X (Y x))) nu
    simpa only [hid] using hshift
  have h0 : 0 ∈ interior (ProbabilityTheory.integrableExpSet X law) :=
    (interior_mono hsubset) hF0
  obtain ⟨hthird, hfourth⟩ := centered_cgf_third_fourth_derivatives law X h0 hmeanX
  exact ⟨h0, hmeanX, hthird, hfourth⟩

end
end Shao.OQ3
