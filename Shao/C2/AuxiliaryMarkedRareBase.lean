import Shao.C2.AuxiliaryRareLaplace
import Shao.C2.AuxiliaryMarkedDeletion
import Shao.OQ4.KilledPathLaw
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryMarkedRareBase
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem auxiliary_original_cutoff_marked_rare_base :
    ∃ C : ℝ, 0 < C ∧
      ∀ rhoStar : ℝ, 0 < rhoStar → rhoStar ≤ 1 / 16 →
        ∀ L : ℝ, 0 ≤ L →
          ∀ K : ℝ, 8000000 * (1 + L) ^ 2 ≤ K →
            2 * (768 / rhoStar) ^ 2 ≤ K →
            ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
              Integrable (fun z : ℝ => z ^ 2) nu →
              Integrable (fun z : ℝ => |z| ^ 3) nu →
              (∫ z : ℝ, z ∂nu) = 0 →
              (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
              ∀ s : ℝ, 0 ≤ s →
                ∀ x : ℝ, 1 ≤ x →
                  ∀ n : ℕ,
                    Nat.ceil (K * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 * (1 + x) ^ 6) ≤ n + 1 →
                    s * ((n + 1 : ℕ) : ℝ) ≤ L * x ^ 2 →
                    let P : Measure (Shao.Path (n + 1)) :=
                      Measure.pi (fun _ : Fin (n + 1) => nu)
                    let B : Set (Shao.Path (n + 1)) := {v |
                      ((3 / 2) * x) * Real.sqrt (Shao.energy v) ≤
                        |Shao.prefixSum v (n + 1)|}
                    let F : Shao.Path (n + 1) → ℝ := fun v =>
                      |v 0| ^ 3 * Real.exp (-s * Shao.energy v)
                    Integrable (B.indicator F) P ∧
                      (∫ v : Shao.Path (n + 1), B.indicator F v ∂P) ≤
                        C * (∫ z : ℝ, |z| ^ 3 ∂nu) *
                          Real.exp (-(7 / 8) * s * (n : ℝ)) *
                            Shao.standardNormalTail ((3 / 2) * x) := by
  classical
  obtain ⟨C, hC, hLaplace⟩ :=
    Shao.C2.AuxiliaryRareLaplace.auxiliary_original_cutoff_rare_laplace
  refine ⟨C, hC, ?_⟩
  intro rhoStar hRho0 hRho16 L hL K hKDrift hKBudget nu _ h2 h3 hMean hNorm s hs x hx n hCutoff hTime P B F
  let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
  let Ptail : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let a : ℝ := Real.sqrt ((9 / 4) * x ^ 2 - 1)
  let A : Set (Shao.Path n) := {w | 0 < Shao.energy w ∧
    a * Real.sqrt (Shao.energy w) ≤ |Shao.prefixSum w n|}
  let W : Shao.Path n → ℝ := fun w => Real.exp (-s * Shao.energy w)
  let g : Shao.Path n → ℝ := A.indicator W
  let f : ℝ → ℝ := fun z => |z| ^ 3 * Real.exp (-s * z ^ 2)
  have hLap := hLaplace rhoStar hRho0 hRho16 L hL K hKDrift hKBudget
    nu h2 h3 hMean hNorm s hs x hx (n + 1) n hCutoff (Or.inr (by omega)) hTime
  change Integrable g Ptail ∧
    (∫ w : Shao.Path n, g w ∂Ptail) ≤
      C * Real.exp (-(7 / 8) * s * (n : ℝ)) * Shao.standardNormalTail ((3 / 2) * x) at hLap
  have hf0 (z : ℝ) : 0 ≤ f z :=
    mul_nonneg (pow_nonneg (abs_nonneg z) 3) (Real.exp_pos _).le
  have hfBound (z : ℝ) : f z ≤ |z| ^ 3 := by
    have hExp : Real.exp (-s * z ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (sq_nonneg z))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hExp (pow_nonneg (abs_nonneg z) 3)
  have hf : Integrable f nu := by
    refine h3.mono' (by dsimp [f]; fun_prop) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 z)]
    exact hfBound z
  have hfIntegral : (∫ z : ℝ, f z ∂nu) ≤ beta := integral_mono hf h3 hfBound
  have hBeta0 : 0 ≤ beta := integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  have hg0 (w : Shao.Path n) : 0 ≤ g w := by
    by_cases hw : w ∈ A
    · simpa only [g, Set.indicator_of_mem hw] using (Real.exp_pos (-s * Shao.energy w)).le
    · simp only [g, Set.indicator_of_notMem hw, le_refl]
  let e : Shao.Path (n + 1) ≃ᵐ (ℝ × Shao.Path n) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hMP : MeasurePreserving e P (nu.prod Ptail) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => nu) 0
  let Q : Shao.Path (n + 1) → ℝ := fun v => f (e v).1 * g (e v).2
  have hQ : Integrable Q P := hMP.integrable_comp_of_integrable (hf.mul_prod hLap.1)
  have hQIntegral : (∫ v : Shao.Path (n + 1), Q v ∂P) =
      (∫ z : ℝ, f z ∂nu) * (∫ w : Shao.Path n, g w ∂Ptail) :=
    (hMP.integral_comp' (fun z : ℝ × Shao.Path n => f z.1 * g z.2)).trans
      (integral_prod_mul f g)
  have hConsEnergy (z : ℝ) (w : Shao.Path n) :
      Shao.energy (Fin.cons z w) = z ^ 2 + Shao.energy w := by
    simp only [Shao.energy, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  have hConsPoint (z : ℝ) (w : Shao.Path n) :
      B.indicator F (Fin.cons z w) ≤ f z * g w := by
    by_cases hb : Fin.cons z w ∈ B
    · by_cases hE0 : Shao.energy (Fin.cons z w) = 0
      · have hz : z = 0 := by
          simpa only [Fin.cons_zero] using
            (Shao.energy_eq_zero_iff (Fin.cons z w)).mp hE0 0
        rw [Set.indicator_of_mem hb]
        simp [F, f, hz]
      · have hPositive : 0 < Shao.energy (Fin.cons z w) :=
          lt_of_le_of_ne (Shao.energy_nonneg _) (Ne.symm hE0)
        have hCross := hb
        change (3 / 2 : ℝ) * x * Real.sqrt (Shao.energy (Fin.cons z w)) ≤
          |Shao.prefixSum (Fin.cons z w) (n + 1)| at hCross
        rw [hConsEnergy, Shao.OQ4.prefixSum_cons] at hCross
        have hRemaining : w ∈ A :=
          Shao.C2.AuxiliaryMarkedDeletion.auxiliary_marked_terminal_deletion w z x hx
            (by simpa only [hConsEnergy] using hPositive) hCross
        rw [Set.indicator_of_mem hb]
        change F (Fin.cons z w) ≤ f z * A.indicator W w
        rw [Set.indicator_of_mem hRemaining]
        change |z| ^ 3 * Real.exp (-s * Shao.energy (Fin.cons z w)) ≤
          (|z| ^ 3 * Real.exp (-s * z ^ 2)) * Real.exp (-s * Shao.energy w)
        rw [hConsEnergy, mul_add, Real.exp_add]
        exact le_of_eq (by ring)
    · rw [Set.indicator_of_notMem hb]
      exact mul_nonneg (hf0 z) (hg0 w)
  have hConsInverse (z : ℝ × Shao.Path n) : e.symm z = Fin.cons z.1 z.2 := by
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
    ((continuous_apply 0).abs.pow 3).mul
      (Real.continuous_exp.comp (continuous_const.mul Shao.continuous_energy))
  have hTarget0 (v : Shao.Path (n + 1)) : 0 ≤ B.indicator F v := by
    by_cases hv : v ∈ B
    · rw [Set.indicator_of_mem hv]
      exact mul_nonneg (pow_nonneg (abs_nonneg _) 3) (Real.exp_pos _).le
    · simp only [Set.indicator_of_notMem hv, le_refl]
  have hTarget : Integrable (B.indicator F) P := by
    refine hQ.mono' (hF.aestronglyMeasurable.indicator hB) (ae_of_all _ fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hTarget0 v)]
    exact hPoint v
  refine ⟨hTarget, ?_⟩
  calc
    (∫ v : Shao.Path (n + 1), B.indicator F v ∂P) ≤ ∫ v : Shao.Path (n + 1), Q v ∂P :=
      integral_mono hTarget hQ hPoint
    _ = (∫ z : ℝ, f z ∂nu) * (∫ w : Shao.Path n, g w ∂Ptail) := hQIntegral
    _ ≤ beta * (C * Real.exp (-(7 / 8) * s * (n : ℝ)) *
        Shao.standardNormalTail ((3 / 2) * x)) :=
      mul_le_mul hfIntegral hLap.2 (integral_nonneg hg0) hBeta0
    _ = C * beta * Real.exp (-(7 / 8) * s * (n : ℝ)) *
        Shao.standardNormalTail ((3 / 2) * x) := by ring

end Shao.C2.AuxiliaryMarkedRareBase
