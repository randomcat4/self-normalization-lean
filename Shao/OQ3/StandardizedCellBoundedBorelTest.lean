import Shao.OQ3.StandardizedCellBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem standardized_rectangular_cell_uniform_bounded_borel_test
    (n : ℕ) (hn : 1 ≤ n) (theta : ℝ × ℝ)
    (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (y : ℝ × ℝ)
    (aL aR qL qR M R S : ℝ)
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (htheta : ‖theta‖ ≤ M)
    (hE : ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ R)
    (hEinv : ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ S)
    (hy : y ∈ Set.Icc aL aR ×ˢ Set.Icc qL qR)
    (hawidth : aR - aL ≤ 1 / (n : ℝ))
    (hqwidth : qR - qL ≤ 1 / (n : ℝ))
    (A : Set (ℝ × ℝ)) (hA : MeasurableSet A)
    (hrect : A ⊆ Set.Ioc aL aR ×ˢ Set.Ioc qL qR)
    (nu : Measure (ℝ × ℝ)) [IsFiniteMeasure nu] :
    let F : (ℝ × ℝ) → (ℝ × ℝ) := fun w => Real.sqrt (n : ℝ) • E (w - y)
    let B : Set (ℝ × ℝ) := {v | y + (Real.sqrt (n : ℝ))⁻¹ • E.symm v ∈ A}
    let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-Real.sqrt (n : ℝ) *
      (theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2))
    let C0 : ℝ := Real.exp ((2 * M) * S * R)
    0 < C0 ∧ MeasurableSet B ∧ B = F '' A ∧
      Measurable (B.indicator g) ∧
      (∀ v : ℝ × ℝ, |B.indicator g v| ≤ C0) ∧
      Integrable (B.indicator g) nu := by
  dsimp only
  let s : ℝ := Real.sqrt (n : ℝ)
  have hN : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn)
  have hs : 0 < s := Real.sqrt_pos.mpr hN
  let F : (ℝ × ℝ) → (ℝ × ℝ) := fun w => s • E (w - y)
  let B : Set (ℝ × ℝ) := {v | y + s⁻¹ • E.symm v ∈ A}
  let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-s *
    (theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2))
  let C0 : ℝ := Real.exp ((2 * M) * S * R)
  let kappa : ℝ := (|theta.1| + |theta.2|) *
    ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
  have hInv : Continuous (fun v : ℝ × ℝ => y + s⁻¹ • E.symm v) := by
    fun_prop
  have hB : MeasurableSet B := hInv.measurable hA
  have hBeq : B = F '' A := by
    ext v
    constructor
    · intro hv
      refine ⟨y + s⁻¹ • E.symm v, hv, ?_⟩
      change s • E ((y + s⁻¹ • E.symm v) - y) = v
      simp [map_smul, smul_smul, hs.ne']
    · rintro ⟨w, hw, rfl⟩
      change y + s⁻¹ • E.symm (s • E (w - y)) ∈ A
      have hi : y + s⁻¹ • E.symm (s • E (w - y)) = w := by
        simp [map_smul, smul_smul, hs.ne', add_comm]
      rw [hi]
      exact hw
  have hcell : ∀ w ∈ A, ‖w - y‖ ≤ (1 : ℝ) / (n : ℝ) := by
    intro w hw
    have hwrect := hrect hw
    have ha : |w.1 - y.1| ≤ 1 / (n : ℝ) := by
      apply abs_le.mpr
      constructor <;> linarith [hwrect.1.1, hwrect.1.2, hy.1.1, hy.1.2]
    have hq : |w.2 - y.2| ≤ 1 / (n : ℝ) := by
      apply abs_le.mpr
      constructor <;> linarith [hwrect.2.1, hwrect.2.2, hy.2.1, hy.2.2]
    simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
      using max_le ha hq
  have hsupport : ∀ v ∈ B, ‖v‖ ≤ R / s := by
    intro v hv
    have hv' : v ∈ F '' A := hBeq ▸ hv
    have h := standardized_cell_support_bound n hn E y 1 (by norm_num) A hcell v hv'
    have h' : ‖v‖ ≤ ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ / s := by
      simpa only [one_mul] using h
    exact h'.trans (div_le_div_of_nonneg_right hE hs.le)
  have hcoords : |theta.1| ≤ M ∧ |theta.2| ≤ M := by
    simpa only [Prod.norm_def, Real.norm_eq_abs, max_le_iff] using htheta
  have hsum : |theta.1| + |theta.2| ≤ 2 * M := by linarith [hcoords.1, hcoords.2]
  have hkappa : kappa ≤ (2 * M) * S :=
    mul_le_mul hsum hEinv (norm_nonneg _) (mul_nonneg (by norm_num) hM)
  have hC : Real.exp (kappa * R) ≤ C0 :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hkappa hR)
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have htest : Measurable (B.indicator g) := hg.measurable.indicator hB
  have hbound : ∀ v : ℝ × ℝ, |B.indicator g v| ≤ C0 := by
    intro v
    by_cases hv : v ∈ B
    · rw [Set.indicator_of_mem hv]
      have h := (standardized_cell_exponential_bounds n hn theta E R hR).1 v
        (hsupport v hv)
      exact h.2.trans hC
    · rw [Set.indicator_of_notMem hv, abs_zero]
      exact (Real.exp_pos _).le
  refine ⟨Real.exp_pos _, hB, hBeq, htest, hbound, ?_⟩
  exact (integrable_const C0).mono' htest.aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => by
      simpa only [Real.norm_eq_abs] using hbound v)

end
end Shao.OQ3
