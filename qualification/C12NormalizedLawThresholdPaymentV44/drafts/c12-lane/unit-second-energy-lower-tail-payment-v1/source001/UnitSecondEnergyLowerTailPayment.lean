import Shao.C2.ActualEnergyLowerTailPayment
import Shao.C2.ActualCenteredProductTransport

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace Shao.C2.UnitSecondEnergyLowerTailPayment
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

theorem iid_unit_second_energy_lower_tail_gaussian_payment
    (rho : Measure ℝ) [IsProbabilityMeasure rho] (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) rho)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) rho)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂rho) = 1)
    (x : ℝ) (hx : 0 ≤ x) :
    let delta : ℝ := (∫ z : ℝ, |z| ^ 3 ∂rho) / Real.sqrt (n : ℝ)
    delta * (1 + x) ^ 3 ≤ 1 / 16 →
      0 < delta ∧
        (Measure.pi (fun _ : Fin n => rho)).real
          {v : Shao.Path n | Shao.energy v ≤ (n : ℝ) / 2} ≤
          32 * delta * (1 + x) ^ 3 * Shao.standardNormalTail x := by
  intro delta hsmall
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnReal
  let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
  let eta : Measure ℝ := Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) rho
  have hScale : Measurable (fun z : ℝ => z / Real.sqrt (n : ℝ)) :=
    measurable_id.div_const _
  letI : IsProbabilityMeasure eta := by
    dsimp only [eta]
    exact (Measure.isProbabilityMeasure_map_iff hScale.aemeasurable).mpr inferInstance
  have hEta2 : Integrable (fun z : ℝ => z ^ 2) eta := by
    dsimp only [eta]
    apply (integrable_map_measure (by fun_prop) hScale.aemeasurable).mpr
    simpa only [Function.comp_apply, div_pow] using
      (h2.div_const (Real.sqrt (n : ℝ) ^ 2))
  have hEta3 : Integrable (fun z : ℝ => |z| ^ 3) eta := by
    dsimp only [eta]
    apply (integrable_map_measure (by fun_prop) hScale.aemeasurable).mpr
    simpa only [Function.comp_apply, abs_div, abs_of_pos hsn, div_pow] using
      (h3.div_const (Real.sqrt (n : ℝ) ^ 3))
  have hEtaSecond : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) = 1 := by
    dsimp only [eta]
    rw [integral_map (μ := rho) (φ := fun z : ℝ => z / Real.sqrt (n : ℝ))
      (f := fun z : ℝ => z ^ 2) hScale.aemeasurable (by fun_prop)]
    simp only [div_pow]
    rw [integral_div, hsecond, Real.sq_sqrt hnReal.le]
    exact mul_one_div_cancel hnReal.ne'
  have hEtaThird : (n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂eta) = delta := by
    dsimp only [eta]
    rw [integral_map (μ := rho) (φ := fun z : ℝ => z / Real.sqrt (n : ℝ))
      (f := fun z : ℝ => |z| ^ 3) hScale.aemeasurable (by fun_prop)]
    simp only [abs_div, abs_of_pos hsn, div_pow]
    rw [integral_div]
    change (n : ℝ) * (beta / Real.sqrt (n : ℝ) ^ 3) = beta / Real.sqrt (n : ℝ)
    rw [show Real.sqrt (n : ℝ) ^ 3 = (n : ℝ) * Real.sqrt (n : ℝ) by
      rw [pow_succ, Real.sq_sqrt hnReal.le]]
    field_simp [hnReal.ne', hsn.ne'] <;> ring
  have hEtaSmall : ((n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂eta)) * (1 + x) ^ 3 ≤ 1 / 16 := by
    rw [hEtaThird]
    exact hsmall
  have hPaid :=
    Shao.C2.ActualEnergyLowerTailPayment.iid_actual_energy_lower_tail_gaussian_payment
      eta n hn hEta2 hEta3 hEtaSecond x hx hEtaSmall
  change 0 < (n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂eta) ∧
    (Measure.pi (fun _ : Fin n => eta)).real {v : Shao.Path n | Shao.energy v ≤ 1 / 2} ≤
      32 * ((n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂eta)) *
        (1 + x) ^ 3 * Shao.standardNormalTail x at hPaid
  rw [hEtaThird] at hPaid
  have hTransport :=
    (Shao.C2.ActualCenteredProductTransport.iid_centered_scaled_product_transport
      rho n hn 0 (Real.sqrt (n : ℝ)) hsn).2.2.2 ((n : ℝ) / 2)
  have hProduct :
      (Measure.pi (fun _ : Fin n => rho)).real
          {v : Shao.Path n | Shao.energy v ≤ (n : ℝ) / 2} =
        (Measure.pi (fun _ : Fin n => eta)).real
          {w : Shao.Path n | (n : ℝ) * Shao.energy w ≤ (n : ℝ) / 2} := by
    simpa only [sub_zero, Real.sq_sqrt hnReal.le] using hTransport
  have hHalf : {w : Shao.Path n | (n : ℝ) * Shao.energy w ≤ (n : ℝ) / 2} =
      {w : Shao.Path n | Shao.energy w ≤ 1 / 2} := by
    ext w
    change (n : ℝ) * Shao.energy w ≤ (n : ℝ) / 2 ↔ Shao.energy w ≤ 1 / 2
    rw [show (n : ℝ) / 2 = (n : ℝ) * (1 / 2 : ℝ) by ring]
    exact mul_le_mul_iff_right₀ hnReal
  rw [hHalf] at hProduct
  exact ⟨hPaid.1, by rw [hProduct]; exact hPaid.2⟩

end Shao.C2.UnitSecondEnergyLowerTailPayment
