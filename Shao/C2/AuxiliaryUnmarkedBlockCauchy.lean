import Shao.Probability.MeasurablePath
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryUnmarkedBlockCauchy
open MeasureTheory ProbabilityTheory

theorem auxiliary_actual_unmarked_block_cauchy
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n p : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (A : Set (Shao.Path n)) (hA : MeasurableSet A)
    (hDamped : Integrable
      (fun v : Shao.Path n => |Shao.prefixSum v n| ^ (2 * p) *
        Real.exp (-s * Shao.energy v)) (Measure.pi (fun _ : Fin n => nu))) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let W : Shao.Path n → ℝ := fun v => Real.exp (-s * Shao.energy v)
    let D : Shao.Path n → ℝ := fun v => |Shao.prefixSum v n| ^ p * W v
    Integrable (A.indicator D) P ∧
      (∫ v : Shao.Path n, A.indicator D v ∂P) ≤
        Real.sqrt (∫ v : Shao.Path n,
          |Shao.prefixSum v n| ^ (2 * p) * W v ∂P) *
        Real.sqrt (∫ v : Shao.Path n, A.indicator W v ∂P) := by
  classical
  intro P W D
  let H : Shao.Path n → ℝ := fun v => Real.exp (-s * Shao.energy v / 2)
  let f : Shao.Path n → ℝ := fun v => |Shao.prefixSum v n| ^ p * H v
  let g : Shao.Path n → ℝ := A.indicator H
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hH : Continuous H :=
    Real.continuous_exp.comp ((continuous_const.mul Shao.continuous_energy).div_const 2)
  have hf : Continuous f := ((Shao.continuous_prefixSum n).abs.pow p).mul hH
  have hW : Continuous W :=
    Real.continuous_exp.comp (continuous_const.mul Shao.continuous_energy)
  have hWInt : Integrable W P := by
    refine (integrable_const (1 : ℝ)).mono' hW.aestronglyMeasurable (ae_of_all _ fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (Shao.energy_nonneg v))
  have hHSq (v : Shao.Path n) : (H v) ^ 2 = W v := by
    change (Real.exp (-s * Shao.energy v / 2)) ^ 2 = Real.exp (-s * Shao.energy v)
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hFSq (v : Shao.Path n) : (f v) ^ 2 = |Shao.prefixSum v n| ^ (2 * p) * W v := by
    change (|Shao.prefixSum v n| ^ p * H v) ^ 2 = _
    rw [mul_pow, hHSq, ← pow_mul, Nat.mul_comm p 2]
  have hGSq (v : Shao.Path n) : (g v) ^ 2 = A.indicator W v := by
    by_cases hv : v ∈ A
    · simp only [g, Set.indicator_of_mem hv, hHSq]
    · simp only [g, Set.indicator_of_notMem hv, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hFSqFun : (fun v : Shao.Path n => (f v) ^ 2) =
      (fun v => |Shao.prefixSum v n| ^ (2 * p) * W v) := funext hFSq
  have hGSqFun : (fun v : Shao.Path n => (g v) ^ 2) = A.indicator W := funext hGSq
  have hfMem : MemLp f 2 P := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 (by
    rw [hFSqFun]
    exact hDamped)
  have hgMem : MemLp g 2 P :=
    (memLp_two_iff_integrable_sq (hH.aestronglyMeasurable.indicator hA)).2 (by
      rw [hGSqFun]
      exact hWInt.indicator hA)
  have hProduct : Integrable (fun v : Shao.Path n => f v * g v) P := hfMem.integrable_mul hgMem
  have hFG (v : Shao.Path n) : f v * g v = A.indicator D v := by
    by_cases hv : v ∈ A
    · simp only [f, g, Set.indicator_of_mem hv]
      change (|Shao.prefixSum v n| ^ p * H v) * H v = |Shao.prefixSum v n| ^ p * W v
      rw [mul_assoc, ← sq, hHSq]
    · simp only [g, Set.indicator_of_notMem hv, mul_zero]
  have hFGFun : (fun v : Shao.Path n => f v * g v) = A.indicator D := funext hFG
  have hTarget : Integrable (A.indicator D) P := by
    rw [← hFGFun]
    exact hProduct
  have hf0 (v : Shao.Path n) : 0 ≤ f v :=
    mul_nonneg (pow_nonneg (abs_nonneg _) p) (Real.exp_pos _).le
  have hg0 (v : Shao.Path n) : 0 ≤ g v := by
    by_cases hv : v ∈ A
    · simpa only [g, Set.indicator_of_mem hv] using (Real.exp_pos (-s * Shao.energy v / 2)).le
    · simp only [g, Set.indicator_of_notMem hv, le_refl]
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ hf0) (ae_of_all _ hg0)
    (by simpa using hfMem) (by simpa using hgMem)
  have hfRpow (v : Shao.Path n) : (f v) ^ (2 : ℝ) = (f v) ^ (2 : ℕ) :=
    Real.rpow_natCast (f v) 2
  have hgRpow (v : Shao.Path n) : (g v) ^ (2 : ℝ) = (g v) ^ (2 : ℕ) :=
    Real.rpow_natCast (g v) 2
  simp_rw [hfRpow, hgRpow, hFSq, hGSq] at hHolder
  rw [hFGFun] at hHolder
  exact ⟨hTarget, by simpa only [Real.sqrt_eq_rpow] using hHolder⟩

end Shao.C2.AuxiliaryUnmarkedBlockCauchy
