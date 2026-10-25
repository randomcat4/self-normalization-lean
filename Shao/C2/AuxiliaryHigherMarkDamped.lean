import Shao.Probability.SourceSuffixMomentBudgets
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryHigherMarkDamped
open MeasureTheory ProbabilityTheory

theorem auxiliary_actual_higher_mark_damped :
    ∀ p : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
        Integrable (fun z : ℝ => z ^ 2) nu →
        Integrable (fun z : ℝ => |z| ^ 3) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ s : ℝ, 0 < s →
          Integrable (fun z : ℝ => |z| ^ (3 + p) * Real.exp (-s * z ^ 2)) nu ∧
            (∫ z : ℝ, |z| ^ (3 + p) * Real.exp (-s * z ^ 2) ∂nu) ≤
              C * Real.rpow s (-(p : ℝ) / 2) * (∫ z : ℝ, |z| ^ 3 ∂nu) := by
  intro p
  obtain ⟨C, hC, hMarked⟩ := Shao.Probability.iid_marked_gaussian_damped_moments p
  refine ⟨C, hC, ?_⟩
  intro nu _ h2 h3 hMean hNorm s hs
  let P : Measure (Shao.Path 1) := Measure.pi (fun _ : Fin 1 => nu)
  let f : ℝ → ℝ := fun z => |z| ^ (3 + p) * Real.exp (-s * z ^ 2)
  let fp : Shao.Path 1 → ℝ := fun v =>
    |v 0| ^ 3 * |Shao.prefixSum v 1| ^ p * Real.exp (-s * Shao.energy v)
  let a3 : ℝ → ℝ := fun z => |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2)
  have hb : 0 < (1 : ℝ) / s := one_div_pos.mpr hs
  have hsb : s ≤ 2 / ((1 : ℝ) / s) := by
    rw [one_div, div_inv_eq_mul]
    linarith
  have hOld := hMarked nu h2 hMean hNorm 0 (1 / s) s hb hs hsb
  have hPath : Integrable fp P ∧ (∫ v : Shao.Path 1, fp v ∂P) ≤
      C * Real.rpow s (-(p : ℝ) / 2) * (∫ z : ℝ, a3 z ∂nu) := by
    simpa only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one] using hOld
  let e : Shao.Path 1 ≃ᵐ ℝ := MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)
  have hMP : MeasurePreserving e P nu := measurePreserving_piUnique (fun _ : Fin 1 => nu)
  have he (v : Shao.Path 1) : e v = v 0 := rfl
  have hSum (v : Shao.Path 1) : Shao.prefixSum v 1 = v 0 := by
    rw [Shao.prefixSum_length, Fin.sum_univ_one]
  have hEnergy (v : Shao.Path 1) : Shao.energy v = (v 0) ^ 2 := by
    simp only [Shao.energy, Fin.sum_univ_one]
  have hPull (v : Shao.Path 1) : f (e v) = fp v := by
    dsimp only [f, fp]
    rw [he, hSum, hEnergy, pow_add]
  have hPullInt : Integrable (f ∘ e) P :=
    hPath.1.congr (ae_of_all _ fun v => (hPull v).symm)
  have hf : Integrable f nu := (hMP.integrable_comp_emb e.measurableEmbedding).mp hPullInt
  have hIntegral : (∫ z : ℝ, f z ∂nu) = ∫ v : Shao.Path 1, fp v ∂P :=
    (hMP.integral_comp' f).symm.trans (integral_congr_ae (ae_of_all _ hPull))
  have ha30 (z : ℝ) : 0 ≤ a3 z :=
    mul_nonneg (pow_nonneg (abs_nonneg z) 3) (Real.exp_pos _).le
  have ha3Bound (z : ℝ) : a3 z ≤ |z| ^ 3 := by
    have hExp : Real.exp (-(s / 2) * z ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg z))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hExp (pow_nonneg (abs_nonneg z) 3)
  have ha3 : Integrable a3 nu := by
    refine h3.mono' (by dsimp only [a3]; fun_prop) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (ha30 z)]
    exact ha3Bound z
  have ha3Integral : (∫ z : ℝ, a3 z ∂nu) ≤ ∫ z : ℝ, |z| ^ 3 ∂nu :=
    integral_mono ha3 h3 ha3Bound
  refine ⟨hf, ?_⟩
  calc
    (∫ z : ℝ, f z ∂nu) = ∫ v : Shao.Path 1, fp v ∂P := hIntegral
    _ ≤ C * Real.rpow s (-(p : ℝ) / 2) * (∫ z : ℝ, a3 z ∂nu) := hPath.2
    _ ≤ C * Real.rpow s (-(p : ℝ) / 2) * (∫ z : ℝ, |z| ^ 3 ∂nu) :=
      mul_le_mul_of_nonneg_left ha3Integral (mul_nonneg hC.le (Real.rpow_nonneg hs.le _))

end Shao.C2.AuxiliaryHigherMarkDamped
