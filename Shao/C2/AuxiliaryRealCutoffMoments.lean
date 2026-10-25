import Shao.Probability.SourceSuffixMomentBudgets
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryRealCutoffMoments
open MeasureTheory ProbabilityTheory

theorem auxiliary_actual_real_marked_cutoff_inverse_moments :
    let c : ℝ := (1 - Real.exp (-2)) / 8
    ∀ a : ℝ, 0 ≤ a → ∀ q : ℕ, (q = 1 ∨ q = 3) → ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ (m : ℕ) (b : ℝ), 0 < b →
          let P : Measure (Shao.Path (m + 1)) := Measure.pi (fun _ : Fin (m + 1) => nu)
          let T : Shao.Path (m + 1) → ℝ := Shao.energy
          let d : Shao.Path (m + 1) → ℝ := fun v => Shao.prefixSum v (m + 1)
          let M : Shao.Path (m + 1) → ℝ := fun v => |v 0| ^ 3
          let a3 : ℝ → ℝ := fun u => ∫ z : ℝ, |z| ^ 3 * Real.exp (-u * z ^ 2) ∂nu
          let retained : ℝ := ∫ z : ℝ, if z ^ 2 ≤ b then z ^ 2 else 0 ∂nu
          let gamma : ℝ := if (1 / 2 : ℝ) ≤ retained then -c else 1
          let selected : Shao.Path (m + 1) → ℝ := fun v =>
            if 0 < T v ∧ b ≤ T v then
              M v / (Real.sqrt (T v)) ^ q * Real.rpow (1 + |d v| / Real.sqrt (T v)) a
            else 0
          let kernel : ℝ → ℝ := fun s =>
            Real.rpow s ((q : ℝ) / 2 - 1) * a3 (s / 2) *
              Real.exp (gamma * s * (m : ℝ))
          Integrable selected P ∧ IntegrableOn kernel (Set.Ioo 0 (1 / b)) ∧
            (∫ v, selected v ∂P) ≤ C * ∫ s : ℝ in Set.Ioo 0 (1 / b), kernel s := by
  intro c a ha q hq
  let k : ℕ := Nat.ceil a
  have hka : a ≤ (k : ℝ) := Nat.le_ceil a
  obtain ⟨C, hC, hMoment⟩ := Shao.Probability.iid_marked_cutoff_inverse_moments k q hq
  refine ⟨C, hC, ?_⟩
  intro nu _ h2 hMean hNorm m b hb P T d M a3 retained gamma selected kernel
  let oldSelected : Shao.Path (m + 1) → ℝ := fun v =>
    if 0 < T v ∧ b ≤ T v then
      M v / (Real.sqrt (T v)) ^ q * (1 + |d v| / Real.sqrt (T v)) ^ k
    else 0
  have hold : Integrable oldSelected P ∧ IntegrableOn kernel (Set.Ioo 0 (1 / b)) ∧
      (∫ v, oldSelected v ∂P) ≤ C * ∫ s : ℝ in Set.Ioo 0 (1 / b), kernel s :=
    hMoment nu h2 hMean hNorm m b hb
  have hTMeas : Measurable T := Shao.continuous_energy.measurable
  have hdMeas : Measurable d := (Shao.continuous_prefixSum (m + 1)).measurable
  have hCoord : Continuous (fun v : Shao.Path (m + 1) => v 0) := continuous_apply 0
  have hMMeas : Measurable M := (hCoord.abs.pow 3).measurable
  have hDMeas : Measurable (fun v : Shao.Path (m + 1) => 1 + |d v| / Real.sqrt (T v)) :=
    measurable_const.add ((continuous_abs.measurable.comp hdMeas).div (Real.continuous_sqrt.measurable.comp hTMeas))
  have hPowCont : Continuous (fun x : ℝ => Real.rpow x a) :=
    continuous_id.rpow_const (fun _ => Or.inr ha)
  have hMeas : Measurable selected := by
    dsimp only [selected]
    exact Measurable.ite
      ((measurableSet_lt measurable_const hTMeas).inter (measurableSet_le measurable_const hTMeas))
      ((hMMeas.div ((Real.continuous_sqrt.measurable.comp hTMeas).pow_const q)).mul (hPowCont.measurable.comp hDMeas))
      measurable_const
  have hCoeff (v : Shao.Path (m + 1)) : 0 ≤ M v / (Real.sqrt (T v)) ^ q :=
    div_nonneg (pow_nonneg (abs_nonneg _) 3) (pow_nonneg (Real.sqrt_nonneg _) q)
  have hD (v : Shao.Path (m + 1)) : 1 ≤ 1 + |d v| / Real.sqrt (T v) :=
    le_add_of_nonneg_right (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
  have hNonneg (v : Shao.Path (m + 1)) : 0 ≤ selected v := by
    by_cases hv : 0 < T v ∧ b ≤ T v
    · simp only [selected, if_pos hv]
      change 0 ≤ M v / (Real.sqrt (T v)) ^ q * (1 + |d v| / Real.sqrt (T v)) ^ a
      exact mul_nonneg (hCoeff v) (Real.rpow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (hD v)) a)
    · simp only [selected, if_neg hv, le_refl]
  have hPoint (v : Shao.Path (m + 1)) : selected v ≤ oldSelected v := by
    by_cases hv : 0 < T v ∧ b ≤ T v
    · simp only [selected, oldSelected, if_pos hv]
      exact mul_le_mul_of_nonneg_left
        ((Real.rpow_le_rpow_of_exponent_le (hD v) hka).trans_eq (Real.rpow_natCast _ k)) (hCoeff v)
    · simp only [selected, oldSelected, if_neg hv, le_refl]
  have hInt : Integrable selected P := by
    refine hold.1.mono' hMeas.aestronglyMeasurable (ae_of_all _ fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hNonneg v)]
    exact hPoint v
  exact ⟨hInt, hold.2.1, (integral_mono hInt hold.1 hPoint).trans hold.2.2⟩

end Shao.C2.AuxiliaryRealCutoffMoments
