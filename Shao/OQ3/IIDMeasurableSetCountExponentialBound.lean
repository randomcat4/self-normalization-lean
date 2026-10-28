import Shao.Basic.FinitePath
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace Shao.OQ3
open Classical MeasureTheory
open scoped BigOperators
noncomputable section

theorem iid_measurable_set_count_exponential_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (H : Set ℝ) (hH : MeasurableSet H) (t alpha : ℝ) (ht : 0 < t) (n : ℕ) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    let Count : Shao.Path n → ℕ := fun z =>
      (Finset.univ.filter (fun i : Fin n => z i ∈ H)).card
    P.real {z | alpha * (n : ℝ) ≤ (Count z : ℝ)} ≤
      Real.exp (-(t * alpha) * (n : ℝ)) *
        (1 + (Real.exp t - 1) * mu.real H) ^ n := by
  classical
  intro P Count
  let f : ℝ → ℝ := fun x => if x ∈ H then Real.exp t else 1
  have hfNN (x : ℝ) : 0 ≤ f x := by
    dsimp only [f]
    split_ifs <;> positivity
  have hfEq : f = fun x => 1 + (Real.exp t - 1) * H.indicator (fun _ => (1 : ℝ)) x := by
    funext x
    by_cases hx : x ∈ H <;> simp [f, hx]
  have hfInt : Integrable f mu := by
    rw [hfEq]
    exact (integrable_const (1 : ℝ)).add
      (((integrable_const (1 : ℝ)).indicator hH).const_mul (Real.exp t - 1))
  have hfValue : (∫ x : ℝ, f x ∂mu) = 1 + (Real.exp t - 1) * mu.real H := by
    rw [hfEq, integral_add (integrable_const 1)
      (((integrable_const (1 : ℝ)).indicator hH).const_mul (Real.exp t - 1)),
      integral_const_mul, integral_indicator hH, setIntegral_const]
    simp
  let F : Shao.Path n → ℝ := fun z => ∏ i : Fin n, f (z i)
  have hFInt : Integrable F P := Integrable.fintype_prod (fun _ : Fin n => hfInt)
  have hFNN (z : Shao.Path n) : 0 ≤ F z := Finset.prod_nonneg (fun i _ => hfNN (z i))
  have hFValue : (∫ z : Shao.Path n, F z ∂P) = (∫ x : ℝ, f x ∂mu) ^ n := by
    simpa only [F, P, Fintype.card_fin] using
      (integral_fintype_prod_eq_pow (ι := Fin n) (μ := mu) f)
  have hFFormula (z : Shao.Path n) : F z = Real.exp t ^ Count z := by
    dsimp only [F, f, Count]
    rw [Finset.prod_ite]
    simp
  let E : Set (Shao.Path n) := {z | alpha * (n : ℝ) ≤ (Count z : ℝ)}
  have hOnE (z : Shao.Path n) (hz : z ∈ E) : Real.exp (t * alpha * (n : ℝ)) ≤ F z := by
    rw [hFFormula, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hz ht.le
    nlinarith only [hh]
  have hsub : E ⊆ {z | Real.exp (t * alpha * (n : ℝ)) ≤ F z} := fun z hz => hOnE z hz
  have hm : P.real E ≤ P.real {z | Real.exp (t * alpha * (n : ℝ)) ≤ F z} :=
    measureReal_mono hsub (measure_ne_top P _)
  have hMark := mul_meas_ge_le_integral_of_nonneg (ae_of_all P hFNN) hFInt
    (Real.exp (t * alpha * (n : ℝ)))
  have hb : P.real E * Real.exp (t * alpha * (n : ℝ)) ≤ ∫ z : Shao.Path n, F z ∂P :=
    (mul_le_mul_of_nonneg_right hm (Real.exp_nonneg _)).trans
      (by simpa only [mul_comm] using hMark)
  change P.real E ≤ _
  calc
    P.real E ≤ (∫ z : Shao.Path n, F z ∂P) / Real.exp (t * alpha * (n : ℝ)) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr hb
    _ = Real.exp (-(t * alpha) * (n : ℝ)) * (∫ x : ℝ, f x ∂mu) ^ n := by
      rw [hFValue, show -(t * alpha) * (n : ℝ) = -(t * alpha * (n : ℝ)) by ring,
        Real.exp_neg]
      ring
    _ = Real.exp (-(t * alpha) * (n : ℝ)) *
        (1 + (Real.exp t - 1) * mu.real H) ^ n := by rw [hfValue]

end
end Shao.OQ3
