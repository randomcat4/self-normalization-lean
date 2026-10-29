import Shao.OQ6.OriginalLogarithmicConditionalCenteredPhysicalTail

open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory Filter Finset

namespace Shao.OQ6.OriginalLogarithmicConditionalFullWindowUncenteredPhysicalTail

noncomputable section
universe u
set_option autoImplicit false
open Shao.OQ5.P51
private theorem finite_physical_centered_projection_bridge
    (n : ℕ) (hn : 4 ≤ n)
    {Ω : Type u} (h : Ω → Ω → ℝ) (g : Ω → ℝ)
    (hhsymm : ∀ a b : Ω, h a b = h b a) :
    let r : Ω → Ω → ℝ := fun a b => h a b - g a - g b
    let U : (Fin n → Ω) → ℝ := fun ζ =>
      Shao.OQ6.FiniteRows.uStatistic (fun i j => h (ζ i) (ζ j))
    let R2 : (Fin n → Ω) → ℝ := fun ζ =>
      Shao.OQ6.FiniteRows.jackknifeSq (fun i j => h (ζ i) (ζ j))
    let s : (Fin n → Ω) → ℝ := fun ζ => Real.sqrt (centeredSq n g r ζ)
    ∀ ζ : Fin n → Ω,
      (if 0 < R2 ζ then Real.sqrt (n : ℝ) * U ζ / Real.sqrt (R2 ζ) else 0) =
        (if s ζ = 0 then 0 else
          (projectionW n g ζ + residualStatisticD n r ζ) / s ζ)
:= by
  -- FINITE_ONLY_SCRATCH_NOT_CHECKED_NOT_MAIN276
  classical
  let r : Ω → Ω → ℝ := fun a b => h a b - g a - g b
  let U : (Fin n → Ω) → ℝ := fun ζ =>
    Shao.OQ6.FiniteRows.uStatistic (fun i j => h (ζ i) (ζ j))
  let R2 : (Fin n → Ω) → ℝ := fun ζ =>
    Shao.OQ6.FiniteRows.jackknifeSq (fun i j => h (ζ i) (ζ j))
  let s : (Fin n → Ω) → ℝ := fun ζ => Real.sqrt (centeredSq n g r ζ)
  change ∀ ζ : Fin n → Ω,
    (if 0 < R2 ζ then Real.sqrt (n : ℝ) * U ζ / Real.sqrt (R2 ζ) else 0) =
      (if s ζ = 0 then 0 else
        (projectionW n g ζ + residualStatisticD n r ζ) / s ζ)
  intro ζ
  have hrsymm : ∀ a b : Ω, r a b = r b a := by
    intro a b
    dsimp only [r]
    rw [hhsymm a b]
    ring
  have hsample : Shao.OQ5.P51.sampledKernel n g r ζ =
      (fun i j : Fin n => h (ζ i) (ζ j)) := by
    funext i j
    dsimp only [Shao.OQ5.P51.sampledKernel, r]
    ring
  have hN4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNpos : (0 : ℝ) < (n : ℝ) := by linarith only [hN4]
  have hNne : (n : ℝ) ≠ 0 := ne_of_gt hNpos
  have hN1ne : (n : ℝ) - 1 ≠ 0 := by linarith only [hN4]
  have hrootNne : Real.sqrt (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hNpos)
  have hrootN2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hNpos.le
  have hformula :=
    Shao.OQ5.P51.sampled_uStatistic_formula n g r ζ hrsymm hn
  rw [hsample] at hformula
  change U ζ = _ at hformula
  have hnum : projectionW n g ζ + residualStatisticD n r ζ =
      Real.sqrt (n : ℝ) * U ζ / 2 := by
    rw [hformula]
    unfold projectionW residualStatisticD
    field_simp [hNne, hN1ne, hrootNne]
    <;> ring_nf <;> simp only [hrootN2] <;> ring
  have hRnonneg : 0 ≤ R2 ζ :=
    Shao.OQ6.FiniteRows.jackknifeSq_nonneg
      (fun i j : Fin n => h (ζ i) (ζ j)) (by omega)
  have hcenterSq : centeredSq n g r ζ = R2 ζ / 4 := by
    unfold centeredSq
    rw [hsample]
  have hsnonneg : 0 ≤ s ζ := Real.sqrt_nonneg _
  have hs2 : (s ζ) ^ 2 = R2 ζ / 4 := by
    change (Real.sqrt (centeredSq n g r ζ)) ^ 2 = _
    rw [hcenterSq]
    exact Real.sq_sqrt (div_nonneg hRnonneg (by norm_num))
  have hscaleSq : (Real.sqrt (R2 ζ)) ^ 2 = (2 * s ζ) ^ 2 := by
    rw [mul_pow, hs2, Real.sq_sqrt hRnonneg]
    ring
  have hscale : Real.sqrt (R2 ζ) = 2 * s ζ :=
    (sq_eq_sq₀ (Real.sqrt_nonneg (R2 ζ))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hsnonneg)).mp hscaleSq
  by_cases hs0 : s ζ = 0
  · have hRzero : R2 ζ = 0 := by
      rw [hs0] at hs2
      linarith only [hs2]
    have hRnotpos : ¬ 0 < R2 ζ := by
      rw [hRzero]
      exact lt_irrefl (0 : ℝ)
    rw [if_neg hRnotpos, if_pos hs0]
  · have hsp : 0 < s ζ := by
      by_contra hnot
      exact hs0 (le_antisymm (le_of_not_gt hnot) hsnonneg)
    have hsSqPos : 0 < (s ζ) ^ 2 := sq_pos_of_pos hsp
    have hRpos : 0 < R2 ζ := by linarith only [hs2, hsSqPos]
    rw [if_pos hRpos, if_neg hs0, hnum, hscale]
    field_simp [hs0]
    <;> ring
end
end Shao.OQ6.OriginalLogarithmicConditionalFullWindowUncenteredPhysicalTail
