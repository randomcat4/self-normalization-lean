import Shao.OQ3.BoundaryLaplaceExponential
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

namespace Shao.OQ3
open scoped Topology
noncomputable section

theorem normalizing_dual_linear_bound
    (theta : ℝ × ℝ) (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (v : ℝ × ℝ) :
    |theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2| ≤
      ((|theta.1| + |theta.2|) * ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖) * ‖v‖ := by
  have h1 : |(E.symm v).1| ≤ ‖E.symm v‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact le_max_left _ _
  have h2 : |(E.symm v).2| ≤ ‖E.symm v‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact le_max_right _ _
  calc
    _ ≤ |theta.1| * |(E.symm v).1| + |theta.2| * |(E.symm v).2| := by
      simpa only [abs_mul] using abs_add_le (theta.1 * (E.symm v).1) (theta.2 * (E.symm v).2)
    _ ≤ |theta.1| * ‖E.symm v‖ + |theta.2| * ‖E.symm v‖ :=
      add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ = (|theta.1| + |theta.2|) * ‖E.symm v‖ := by ring
    _ ≤ (|theta.1| + |theta.2|) * (‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left
        ((E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).le_opNorm v)
        (add_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

theorem standardized_cell_support_bound
    (n : ℕ) (hn : 1 ≤ n) (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (y : ℝ × ℝ) (d : ℝ) (hd : 0 ≤ d) (A : Set (ℝ × ℝ))
    (hcell : ∀ w ∈ A, ‖w - y‖ ≤ d / (n : ℝ)) :
    ∀ v ∈ (fun w : ℝ × ℝ => Real.sqrt (n : ℝ) • E (w - y)) '' A,
      ‖v‖ ≤ d * ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ / Real.sqrt (n : ℝ) := by
  have hN : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hN
  have hdN : 0 ≤ d / (n : ℝ) := div_nonneg hd hN.le
  rintro v ⟨w, hw, rfl⟩
  have hscale : Real.sqrt (n : ℝ) * (‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ * (d / (n : ℝ))) =
      d * ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ / Real.sqrt (n : ℝ) := by
    calc
      _ = (d * ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖) * Real.sqrt (n : ℝ) / (n : ℝ) := by ring
      _ = (d * ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖) * Real.sqrt (n : ℝ) / (Real.sqrt (n : ℝ)) ^ 2 := by
        rw [Real.sq_sqrt hN.le]
      _ = _ := by field_simp [hs.ne'] <;> ring
  calc
    _ = Real.sqrt (n : ℝ) * ‖E (w - y)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    _ ≤ Real.sqrt (n : ℝ) * (‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ * (d / (n : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (((E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).le_opNorm (w - y)).trans
          (mul_le_mul (le_refl _) (hcell w hw) (norm_nonneg _) (norm_nonneg _))) hs.le
    _ = _ := hscale

theorem standardized_cell_exponential_bounds
    (n : ℕ) (hn : 1 ≤ n) (theta : ℝ × ℝ)
    (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (R : ℝ) (hR : 0 ≤ R) :
    let B : ℝ := (|theta.1| + |theta.2|) * ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
    let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-Real.sqrt (n : ℝ) *
      (theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2))
    (∀ v : ℝ × ℝ, ‖v‖ ≤ R / Real.sqrt (n : ℝ) →
      0 < g v ∧ |g v| ≤ Real.exp (B * R)) ∧
    (∀ v w : ℝ × ℝ, ‖v‖ ≤ R / Real.sqrt (n : ℝ) →
      ‖w‖ ≤ R / Real.sqrt (n : ℝ) →
      |g v - g w| ≤ Real.sqrt (n : ℝ) * B * Real.exp (B * R) * ‖v - w‖) := by
  let B : ℝ := (|theta.1| + |theta.2|) * ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
  let ell : (ℝ × ℝ) → ℝ := fun v => theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2
  let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-Real.sqrt (n : ℝ) * ell v)
  have hN : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hN
  have hB : 0 ≤ B := mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (norm_nonneg _)
  have hBR : 0 ≤ B * R := mul_nonneg hB hR
  have hlinear (v : ℝ × ℝ) : |ell v| ≤ B * ‖v‖ :=
    normalizing_dual_linear_bound theta E v
  have hdifference (v w : ℝ × ℝ) : |ell v - ell w| ≤ B * ‖v - w‖ := by
    have heq : ell v - ell w = ell (v - w) := by
      dsimp only [ell]
      rw [map_sub]
      change _ = theta.1 * ((E.symm v).1 - (E.symm w).1) +
        theta.2 * ((E.symm v).2 - (E.symm w).2)
      ring
    rw [heq]
    exact hlinear (v - w)
  have hscaled (v : ℝ × ℝ) (hv : ‖v‖ ≤ R / Real.sqrt (n : ℝ)) :
      |Real.sqrt (n : ℝ) * ell v| ≤ B * R := by
    calc
      _ = Real.sqrt (n : ℝ) * |ell v| := by rw [abs_mul, abs_of_pos hs]
      _ ≤ Real.sqrt (n : ℝ) * (B * ‖v‖) :=
        mul_le_mul_of_nonneg_left (hlinear v) hs.le
      _ = B * (‖v‖ * Real.sqrt (n : ℝ)) := by ring
      _ ≤ B * R := mul_le_mul_of_nonneg_left ((le_div_iff₀ hs).mp hv) hB
  refine ⟨?_, ?_⟩
  · intro v hv
    refine ⟨Real.exp_pos _, ?_⟩
    change |Real.exp (-Real.sqrt (n : ℝ) * ell v)| ≤ Real.exp (B * R)
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hb := (abs_le.mp (hscaled v hv)).1
    linarith
  · intro v w hv hw
    have ha : -(B * R) ≤ Real.sqrt (n : ℝ) * ell v := (abs_le.mp (hscaled v hv)).1
    have hb : -(B * R) ≤ Real.sqrt (n : ℝ) * ell w := (abs_le.mp (hscaled w hw)).1
    have hdelta : |Real.sqrt (n : ℝ) * ell v - Real.sqrt (n : ℝ) * ell w| ≤
        Real.sqrt (n : ℝ) * (B * ‖v - w‖) := by
      rw [← mul_sub, abs_mul, abs_of_pos hs]
      exact mul_le_mul_of_nonneg_left (hdifference v w) hs.le
    have hcomp := abs_exp_neg_sub_exp_neg_le
      (Real.sqrt (n : ℝ) * ell v) (Real.sqrt (n : ℝ) * ell w) (-(B * R)) ha hb
    change |Real.exp (-Real.sqrt (n : ℝ) * ell v) -
      Real.exp (-Real.sqrt (n : ℝ) * ell w)| ≤ _
    rw [neg_mul, neg_mul]
    calc
      _ ≤ Real.exp (B * R) *
          |Real.sqrt (n : ℝ) * ell v - Real.sqrt (n : ℝ) * ell w| := by
        simpa only [neg_neg] using hcomp
      _ ≤ Real.exp (B * R) * (Real.sqrt (n : ℝ) * (B * ‖v - w‖)) :=
        mul_le_mul_of_nonneg_left hdelta (Real.exp_pos _).le
      _ = _ := by ring

end
end Shao.OQ3
