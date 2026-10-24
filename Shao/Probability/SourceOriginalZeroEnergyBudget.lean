/- Separate next mathematical candidate. No production or Lean authority. -/
import Shao.Probability.FiniteIID
import Shao.Probability.TruncationIntegrals
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.Probability.SourceOriginalZeroEnergyBudget
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

theorem original_iid_zero_energy_budget
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (rho : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure rho]
    (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ)
    (hX : ∀ i, AEMeasurable (X i) mu)
    (hIndep : iIndepFun X mu)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) mu rho)
    (h2 : Integrable (fun z : ℝ => z ^ 2) rho)
    (hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂rho) :
    let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
    let scale : ℝ := Real.sqrt ((n : ℝ) * sigmaSq)
    let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) rho
    let R : ℝ := Shao.truncationBudget normalizedLaw n 0
    let rawEnergy : Ω → ℝ := fun omega => ∑ i : Fin n, (X i omega) ^ 2
    mu.real {omega : Ω | rawEnergy omega = 0} ≤ 16 * R
 := by
  classical
  intro sigmaSq scale normalizedLaw R rawEnergy
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < scale := Real.sqrt_pos.2 (mul_pos hN hsecond)
  have hs2 : scale ^ 2 = (n : ℝ) * sigmaSq := Real.sq_sqrt (by positivity)
  have h2s : Integrable (fun z : ℝ => (z / scale) ^ 2) rho := by
    simpa only [div_pow] using h2.div_const (scale ^ 2)
  have hNorm : (n : ℝ) * (∫ z : ℝ, (z / scale) ^ 2 ∂rho) = 1 := by
    simp_rw [div_pow]
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const]
    rw [← div_eq_mul_inv]
    change (n : ℝ) * (sigmaSq / scale ^ 2) = 1
    rw [hs2]
    field_simp [show sigmaSq ≠ 0 from ne_of_gt hsecond]
  have hF : Integrable (fun z : ℝ => Shao.truncationF (z / scale)) rho := by
    refine h2s.mono' (Shao.continuous_truncationF.measurable.comp (by fun_prop)).aestronglyMeasurable (ae_of_all rho (fun z => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (Shao.truncationF_nonneg _)]
    exact Shao.truncationF_le_sq _
  have hR : R = (n : ℝ) * ∫ z : ℝ, Shao.truncationF (z / scale) ∂rho := by
    change (n : ℝ) * (∫ z : ℝ, Shao.truncationF ((1 + 0) * z)
      ∂Measure.map (fun z : ℝ => z / scale) rho) = _
    simp only [add_zero, one_mul]
    rw [integral_map (by fun_prop) Shao.continuous_truncationF.aestronglyMeasurable]
  have hR0 : 0 ≤ R := by
    rw [hR]
    exact mul_nonneg hN.le (integral_nonneg fun z => Shao.truncationF_nonneg _)
  let u : ℝ → ℝ := fun z => if |z| ≤ 1 then z ^ 2 else 0
  have hu (z : ℝ) : 0 ≤ u z ∧ u z ≤ 1 := by
    dsimp only [u]
    split_ifs with hz
    · exact ⟨sq_nonneg z, by nlinarith [sq_abs z, abs_nonneg z]⟩
    · exact ⟨le_rfl, zero_le_one⟩
  have hum : Measurable u :=
    Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
      (measurable_id.pow_const 2) measurable_const
  have hMeanPoint (z : ℝ) : z ^ 2 ≤ u z + Shao.truncationF z := by
    by_cases hz : |z| ≤ 1
    · simp only [u, if_pos hz]
      linarith [Shao.truncationF_nonneg z]
    · rw [show u z = 0 by simp only [u, if_neg hz],
        Shao.truncationF_of_one_le_abs z (le_of_not_ge hz)]
      simp
  have hSquarePoint (z : ℝ) : (u z) ^ 2 ≤ Shao.truncationF z := by
    by_cases hz : |z| ≤ 1
    · rw [show u z = z ^ 2 by simp only [u, if_pos hz],
        Shao.truncationF_of_abs_le_one z hz]
      calc
        (z ^ 2) ^ 2 = |z| ^ 3 * |z| := by rw [← sq_abs z]; ring
        _ ≤ |z| ^ 3 * 1 := mul_le_mul_of_nonneg_left hz (pow_nonneg (abs_nonneg z) 3)
        _ = _ := mul_one _
    · rw [show u z = 0 by simp only [u, if_neg hz]]
      simpa using Shao.truncationF_nonneg z
  let g : ℝ → ℝ := fun z => u (z / scale)
  let Ui : Fin n → Ω → ℝ := fun i omega => g (X i omega)
  let U : Ω → ℝ := fun omega => ∑ i : Fin n, Ui i omega
  let m : ℝ := ∫ omega : Ω, U omega ∂mu
  have hgm : Measurable g := hum.comp (by fun_prop)
  have hg2 : MemLp g 2 rho :=
    MemLp.of_bound hgm.aestronglyMeasurable 1 (ae_of_all rho fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hu (z / scale)).1]
      exact (hu (z / scale)).2)
  have hUiLaw (i : Fin n) : IdentDistrib (Ui i) g mu rho := (hLaw i).comp hgm
  have hUi2 (i : Fin n) : MemLp (Ui i) 2 mu := (hUiLaw i).memLp_iff.mpr hg2
  have hUi1 (i : Fin n) : Integrable (Ui i) mu := (hUi2 i).integrable (by norm_num)
  have hU2 : MemLp U 2 mu := by
    simpa only [U, Finset.sum_apply] using
      memLp_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ => hUi2 i)
  have hm : m = (n : ℝ) * ∫ z : ℝ, g z ∂rho := by
    change (∫ omega : Ω, ∑ i : Fin n, Ui i omega ∂mu) = _
    rw [integral_finsetSum _ (fun i _ => hUi1 i)]
    simp only [fun i => (hUiLaw i).integral_eq, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmLower : 1 - R ≤ m := by
    have hi := integral_mono h2s ((hg2.integrable (by norm_num)).add hF)
      (fun z => hMeanPoint (z / scale))
    change (∫ z : ℝ, (z / scale) ^ 2 ∂rho) ≤
      ∫ z : ℝ, g z + Shao.truncationF (z / scale) ∂rho at hi
    rw [integral_add (hg2.integrable (by norm_num)) hF] at hi
    have hiN := mul_le_mul_of_nonneg_left hi hN.le
    rw [hNorm, mul_add, ← hm, ← hR] at hiN
    linarith
  have hVarG : variance g rho ≤ ∫ z : ℝ, Shao.truncationF (z / scale) ∂rho := by
    have hi := integral_mono hg2.integrable_sq hF (fun z => hSquarePoint (z / scale))
    rw [variance_eq_sub hg2]
    simp only [Pi.pow_apply]
    nlinarith [sq_nonneg (∫ z : ℝ, g z ∂rho)]
  have hIndepUi : iIndepFun Ui mu := hIndep.comp (fun _ => g) (fun _ => hgm)
  have hVar : variance U mu ≤ R := by
    have hv := IndepFun.variance_sum (s := (Finset.univ : Finset (Fin n)))
      (fun i _ => hUi2 i) (fun i _ j _ hij => hIndepUi.indepFun hij)
    have he : (∑ i : Fin n, Ui i) = U := by
      funext omega
      simp only [U, Finset.sum_apply]
    rw [he] at hv
    rw [hv]
    calc
      _ ≤ ∑ _ : Fin n, ∫ z : ℝ, Shao.truncationF (z / scale) ∂rho :=
        Finset.sum_le_sum (fun i _ => (hUiLaw i).variance_eq.le.trans hVarG)
      _ = R := by
        rw [hR]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  by_cases hLarge : (1 / 4 : ℝ) ≤ R
  · exact (measureReal_le_one).trans (by linarith)
  · have hmPos : 0 < m := by linarith
    have hSub : {omega : Ω | rawEnergy omega = 0} ⊆
        {omega : Ω | (1 / 4 : ℝ) ≤ |U omega - ∫ omega : Ω, U omega ∂mu|} := by
      intro omega homega
      have hCoords : ∀ i : Fin n, X i omega = 0 :=
        (Shao.energy_eq_zero_iff (samplePath X omega)).mp homega
      have hZero : U omega = 0 := by
        simp only [U, Ui, g, hCoords, zero_div, u, abs_zero, zero_le_one, if_true,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero]
      change (1 / 4 : ℝ) ≤ |U omega - m|
      rw [hZero, zero_sub, abs_neg, abs_of_pos hmPos]
      linarith
    have hCheb := meas_ge_le_variance_div_sq hU2 (by norm_num : (0 : ℝ) < 1 / 4)
    have hReal := ENNReal.toReal_mono (by finiteness) hCheb
    rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg U mu) (sq_nonneg _))] at hReal
    calc
      _ ≤ mu.real {omega : Ω | (1 / 4 : ℝ) ≤ |U omega - ∫ omega : Ω, U omega ∂mu|} :=
        measureReal_mono hSub
      _ ≤ variance U mu / (1 / 4 : ℝ) ^ 2 := hReal
      _ ≤ 16 * R := by norm_num; linarith

end Shao.Probability.SourceOriginalZeroEnergyBudget
