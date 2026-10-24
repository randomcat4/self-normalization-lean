import Shao.C2.AuxiliaryMarkedRareRealSplit
import Shao.C2.AuxiliaryUnmarkedBlockRealCauchy
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryMarkedRareFubini
open MeasureTheory ProbabilityTheory

theorem auxiliary_actual_marked_rare_fubini
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (n : ℕ) (s x a : ℝ) (hs : 0 ≤ s) (hx : 1 ≤ x) (ha : 0 ≤ a)
    (hHigherMark : Integrable (fun z : ℝ =>
      Real.rpow |z| (3 + a) * Real.exp (-s * z ^ 2)) nu)
    (hDamped : Integrable (fun w : Shao.Path n =>
      Real.rpow |Shao.prefixSum w n| (2 * a) * Real.exp (-s * Shao.energy w))
      (Measure.pi (fun _ : Fin n => nu))) :
    let P : Measure (Shao.Path (n + 1)) := Measure.pi (fun _ : Fin (n + 1) => nu)
    let Ptail : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let B : Set (Shao.Path (n + 1)) := {v |
      ((3 / 2) * x) * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v (n + 1)|}
    let A : Set (Shao.Path n) := {w | 0 < Shao.energy w ∧
      Real.sqrt ((9 / 4) * x ^ 2 - 1) * Real.sqrt (Shao.energy w) ≤
        |Shao.prefixSum w n|}
    let W : Shao.Path n → ℝ := fun w => Real.exp (-s * Shao.energy w)
    let F : Shao.Path (n + 1) → ℝ := fun v =>
      |v 0| ^ 3 * Real.rpow |Shao.prefixSum v (n + 1)| a *
        Real.exp (-s * Shao.energy v)
    Integrable (B.indicator F) P ∧
      (∫ v : Shao.Path (n + 1), B.indicator F v ∂P) ≤
        Real.rpow 2 a *
          ((∫ z : ℝ, Real.rpow |z| (3 + a) * Real.exp (-s * z ^ 2) ∂nu) *
              (∫ w : Shao.Path n, A.indicator W w ∂Ptail) +
            (∫ z : ℝ, |z| ^ 3 ∂nu) *
              Real.sqrt (∫ w : Shao.Path n,
                Real.rpow |Shao.prefixSum w n| (2 * a) * W w ∂Ptail) *
              Real.sqrt (∫ w : Shao.Path n, A.indicator W w ∂Ptail)) := by
  classical
  intro P Ptail B A W F
  let C : ℝ := Real.rpow 2 a
  let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
  let fHigh : ℝ → ℝ := fun z => Real.rpow |z| (3 + a) * Real.exp (-s * z ^ 2)
  let f3 : ℝ → ℝ := fun z => |z| ^ 3 * Real.exp (-s * z ^ 2)
  let g0 : Shao.Path n → ℝ := A.indicator W
  let gp : Shao.Path n → ℝ := A.indicator
    (fun w => Real.rpow |Shao.prefixSum w n| a * W w)
  have hC0 : 0 ≤ C := Real.rpow_nonneg (by norm_num) a
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const Shao.measurable_energy).inter
      (measurableSet_le (measurable_const.mul Shao.measurable_sqrt_energy)
        (Shao.continuous_prefixSum n).abs.measurable)
  have hW : Continuous W :=
    Real.continuous_exp.comp (continuous_const.mul Shao.continuous_energy)
  have hWInt : Integrable W Ptail := by
    refine (integrable_const (1 : ℝ)).mono' hW.aestronglyMeasurable
      (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (Shao.energy_nonneg w))
  have hg0 : Integrable g0 Ptail := hWInt.indicator hA
  have hCauchy :=
    Shao.C2.AuxiliaryUnmarkedBlockRealCauchy.auxiliary_actual_unmarked_block_real_cauchy
      nu n a s ha hs A hA hDamped
  change Integrable gp Ptail ∧
    (∫ w : Shao.Path n, gp w ∂Ptail) ≤
      Real.sqrt (∫ w : Shao.Path n,
        Real.rpow |Shao.prefixSum w n| (2 * a) * W w ∂Ptail) *
      Real.sqrt (∫ w : Shao.Path n, g0 w ∂Ptail) at hCauchy
  have hfHigh : Integrable fHigh nu := hHigherMark
  have hf30 (z : ℝ) : 0 ≤ f3 z :=
    mul_nonneg (pow_nonneg (abs_nonneg z) 3) (Real.exp_pos _).le
  have hf3Bound (z : ℝ) : f3 z ≤ |z| ^ 3 := by
    have hExp : Real.exp (-s * z ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (sq_nonneg z))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hExp
      (pow_nonneg (abs_nonneg z) 3)
  have hf3 : Integrable f3 nu := by
    refine h3.mono' (by dsimp [f3]; fun_prop) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf30 z)]
    exact hf3Bound z
  have hf3Integral : (∫ z : ℝ, f3 z ∂nu) ≤ beta :=
    integral_mono hf3 h3 hf3Bound
  have hBeta0 : 0 ≤ beta := integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  have hgp0 (w : Shao.Path n) : 0 ≤ gp w := by
    by_cases hw : w ∈ A
    · rw [show gp w = A.indicator
        (fun u => Real.rpow |Shao.prefixSum u n| a * W u) w from rfl,
        Set.indicator_of_mem hw]
      exact mul_nonneg (Real.rpow_nonneg (abs_nonneg _) a) (Real.exp_pos _).le
    · simp only [gp, Set.indicator_of_notMem hw, le_refl]
  let e : Shao.Path (n + 1) ≃ᵐ (ℝ × Shao.Path n) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hMP : MeasurePreserving e P (nu.prod Ptail) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => nu) 0
  let Q : Shao.Path (n + 1) → ℝ := fun v =>
    C * (fHigh (e v).1 * g0 (e v).2 + f3 (e v).1 * gp (e v).2)
  have hSep : Integrable (fun y : ℝ × Shao.Path n =>
      C * (fHigh y.1 * g0 y.2 + f3 y.1 * gp y.2)) (nu.prod Ptail) :=
    ((hfHigh.mul_prod hg0).add (hf3.mul_prod hCauchy.1)).const_mul C
  have hQ : Integrable Q P := hMP.integrable_comp_of_integrable hSep
  have hQIntegral : (∫ v : Shao.Path (n + 1), Q v ∂P) =
      C * ((∫ z : ℝ, fHigh z ∂nu) * (∫ w : Shao.Path n, g0 w ∂Ptail) +
        (∫ z : ℝ, f3 z ∂nu) * (∫ w : Shao.Path n, gp w ∂Ptail)) := by
    calc
      _ = ∫ y : ℝ × Shao.Path n,
          C * (fHigh y.1 * g0 y.2 + f3 y.1 * gp y.2) ∂(nu.prod Ptail) :=
        hMP.integral_comp' _
      _ = C * ((∫ y : ℝ × Shao.Path n, fHigh y.1 * g0 y.2 ∂(nu.prod Ptail)) +
          ∫ y : ℝ × Shao.Path n, f3 y.1 * gp y.2 ∂(nu.prod Ptail)) := by
        rw [integral_const_mul, integral_add (hfHigh.mul_prod hg0) (hf3.mul_prod hCauchy.1)]
      _ = _ := by rw [integral_prod_mul, integral_prod_mul]
  have hConsPoint (z : ℝ) (w : Shao.Path n) :
      B.indicator F (Fin.cons z w) ≤ C * (fHigh z * g0 w + f3 z * gp w) := by
    have hSplit :=
      Shao.C2.AuxiliaryMarkedRareRealSplit.auxiliary_actual_marked_rare_real_split
        w z x s a ha hx
    change B.indicator F (Fin.cons z w) ≤
      C * (Real.rpow |z| (3 + a) + |z| ^ 3 * Real.rpow |Shao.prefixSum w n| a) *
        Real.exp (-s * z ^ 2) * g0 w at hSplit
    refine hSplit.trans (le_of_eq ?_)
    by_cases hw : w ∈ A
    · simp only [fHigh, f3, g0, gp, Set.indicator_of_mem hw]
      ring
    · simp only [g0, gp, Set.indicator_of_notMem hw, mul_zero, add_zero]
  have hConsInverse (y : ℝ × Shao.Path n) : e.symm y = Fin.cons y.1 y.2 := by
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero]
    rfl
  have hPoint (v : Shao.Path (n + 1)) : B.indicator F v ≤ Q v := by
    have hv : Fin.cons (e v).1 (e v).2 = v := by
      rw [← hConsInverse]
      exact e.symm_apply_apply v
    simpa only [hv] using hConsPoint (e v).1 (e v).2
  have hB : MeasurableSet B :=
    measurableSet_le (measurable_const.mul Shao.measurable_sqrt_energy)
      (Shao.continuous_prefixSum (n + 1)).abs.measurable
  have hF : Continuous F :=
    (((continuous_apply 0).abs.pow 3).mul
      ((Shao.continuous_prefixSum (n + 1)).abs.rpow_const (fun _ => Or.inr ha))).mul
        (Real.continuous_exp.comp (continuous_const.mul Shao.continuous_energy))
  have hTarget0 (v : Shao.Path (n + 1)) : 0 ≤ B.indicator F v := by
    by_cases hv : v ∈ B
    · rw [Set.indicator_of_mem hv]
      exact mul_nonneg
        (mul_nonneg (pow_nonneg (abs_nonneg _) 3) (Real.rpow_nonneg (abs_nonneg _) a))
        (Real.exp_pos _).le
    · simp only [Set.indicator_of_notMem hv, le_refl]
  have hTarget : Integrable (B.indicator F) P := by
    refine hQ.mono' (hF.aestronglyMeasurable.indicator hB) (ae_of_all _ fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hTarget0 v)]
    exact hPoint v
  have hUnmarkedProduct :
      (∫ z : ℝ, f3 z ∂nu) * (∫ w : Shao.Path n, gp w ∂Ptail) ≤
        beta * (Real.sqrt (∫ w : Shao.Path n,
          Real.rpow |Shao.prefixSum w n| (2 * a) * W w ∂Ptail) *
          Real.sqrt (∫ w : Shao.Path n, g0 w ∂Ptail)) :=
    mul_le_mul hf3Integral hCauchy.2 (integral_nonneg hgp0) hBeta0
  refine ⟨hTarget, ?_⟩
  calc
    (∫ v : Shao.Path (n + 1), B.indicator F v ∂P) ≤
        ∫ v : Shao.Path (n + 1), Q v ∂P := integral_mono hTarget hQ hPoint
    _ = C * ((∫ z : ℝ, fHigh z ∂nu) * (∫ w : Shao.Path n, g0 w ∂Ptail) +
        (∫ z : ℝ, f3 z ∂nu) * (∫ w : Shao.Path n, gp w ∂Ptail)) := hQIntegral
    _ ≤ C * ((∫ z : ℝ, fHigh z ∂nu) * (∫ w : Shao.Path n, g0 w ∂Ptail) +
        beta * (Real.sqrt (∫ w : Shao.Path n,
          Real.rpow |Shao.prefixSum w n| (2 * a) * W w ∂Ptail) *
          Real.sqrt (∫ w : Shao.Path n, g0 w ∂Ptail))) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hUnmarkedProduct) hC0
    _ = _ := by dsimp only [C, fHigh, g0, beta]; ring

end Shao.C2.AuxiliaryMarkedRareFubini
