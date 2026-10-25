import Shao.C2.AuxiliaryRealMarkedFiniteCutoffInverse
import Shao.Probability.SourceSuffixMomentBudgets

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Shao.C2.AuxiliaryRealMarkedFiniteCutoffExtendedBudget
open MeasureTheory ProbabilityTheory

theorem auxiliary_actual_real_marked_finite_cutoff_extended_budget :
    let c : ℝ := (1 - Real.exp (-2)) / 8
    ∀ a q : ℝ, 0 ≤ a → 0 < q → ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ (m : ℕ) (b H : ℝ), 0 < b → b ≤ H →
          let P : Measure (Shao.Path (m + 1)) := Measure.pi (fun _ : Fin (m + 1) => nu)
          let T : Shao.Path (m + 1) → ℝ := Shao.energy
          let d : Shao.Path (m + 1) → ℝ := fun v => Shao.prefixSum v (m + 1)
          let M : Shao.Path (m + 1) → ℝ := fun v => |v 0| ^ 3
          let a3 : ℝ → ℝ := fun u => ∫ z : ℝ, |z| ^ 3 * Real.exp (-u * z ^ 2) ∂nu
          let retained : ℝ := ∫ z : ℝ, if z ^ 2 ≤ b then z ^ 2 else 0 ∂nu
          let gamma : ℝ := if (1 / 2 : ℝ) ≤ retained then -c else 1
          let selected : Shao.Path (m + 1) → ℝ := fun v =>
            if 0 < T v ∧ b ≤ T v ∧ T v < H then
              M v * Real.rpow (T v) (-q / 2) *
                Real.rpow (1 + |d v| / Real.sqrt (T v)) a else 0
          let kernel : ℝ → ℝ := fun s =>
            Real.rpow s (q / 2 - 1) * a3 (s / 2) *
              Real.exp (gamma * (s + 1 / H) * (m : ℝ))
          Integrable selected P ∧
            (∫⁻ v, ENNReal.ofReal (selected v) ∂P) ≤
              ENNReal.ofReal C *
                ∫⁻ s : ℝ in Set.Ioo 0 (1 / b), ENNReal.ofReal (kernel s) := by
  intro c a q ha hq
  obtain ⟨C, hC, hStrong⟩ :=
    Shao.C2.AuxiliaryRealMarkedFiniteCutoffInverse.auxiliary_actual_real_marked_finite_cutoff_inverse_moments
      a q ha hq
  refine ⟨C, hC, ?_⟩
  intro nu hnu h2 hmean hnorm m b H hb hbH P T d M a3 retained gamma selected kernel
  letI : IsProbabilityMeasure nu := hnu
  have hH : 0 < H := lt_of_lt_of_le hb hbH
  have hdelta : 0 < 1 / H := one_div_pos.mpr hH
  have hdeltab : 1 / H ≤ 1 / b := one_div_le_one_div_of_le hb hbH
  let S : Set ℝ := Set.Ioo 0 (1 / b)
  let K : ℝ → ℝ := fun s => Real.rpow s (q / 2 - 1) * a3 ((s + 1 / H) / 2) *
    Real.exp (gamma * (s + 1 / H) * (m : ℝ))
  have hActual := hStrong nu h2 hmean hnorm m b H hb hbH
  have hK : IntegrableOn K S := hActual.2.1
  have hRaw (u : ℝ) (hu : 0 < u) (hub : u ≤ 2 / b) :
      Integrable (fun z : ℝ => |z| ^ 3 * Real.exp (-(u / 2) * z ^ 2)) nu :=
    (Shao.Probability.raw_gaussian_damped_coordinate_factors.2.2
      nu h2 hmean hnorm b u hb hu hub).1
  have hCmp : K ≤ᵐ[volume.restrict S] kernel := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hsLegal : s ≤ 2 / b := by
      calc
        s ≤ 1 / b := hs.2.le
        _ ≤ 1 / b + 1 / b := le_add_of_nonneg_right (one_div_pos.mpr hb).le
        _ = _ := by ring
    have huLegal : s + 1 / H ≤ 2 / b := by
      calc
        s + 1 / H ≤ 1 / b + 1 / b := add_le_add hs.2.le hdeltab
        _ = _ := by ring
    have hA3 : a3 ((s + 1 / H) / 2) ≤ a3 (s / 2) := by
      apply integral_mono (hRaw (s + 1 / H) (add_pos hs.1 hdelta) huLegal) (hRaw s hs.1 hsLegal)
      intro z
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg _) 3)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hdelta.le (sq_nonneg z)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hA3 (Real.rpow_nonneg hs.1.le _)) (Real.exp_pos _).le
  have hSelectedNN : 0 ≤ᵐ[P] selected := by
    apply Filter.Eventually.of_forall
    intro v
    dsimp only [selected, M]
    split_ifs with hv
    · exact mul_nonneg
        (mul_nonneg (pow_nonneg (abs_nonneg _) 3) (Real.rpow_nonneg hv.1.le _))
        (Real.rpow_nonneg (by positivity) _)
    · exact le_rfl
  have hKNN : 0 ≤ᵐ[volume.restrict S] K := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hA3 : 0 ≤ a3 ((s + 1 / H) / 2) := by
      apply integral_nonneg
      intro z
      positivity
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.1.le _) hA3)
      (Real.exp_pos _).le
  refine ⟨hActual.1, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hActual.1 hSelectedNN]
  calc
    ENNReal.ofReal (∫ v, selected v ∂P) ≤
        ENNReal.ofReal (C * ∫ s : ℝ in S, K s) :=
      ENNReal.ofReal_le_ofReal hActual.2.2
    _ = ENNReal.ofReal C * ∫⁻ s : ℝ in S, ENNReal.ofReal (K s) := by
      rw [ENNReal.ofReal_mul hC.le, ofReal_integral_eq_lintegral_ofReal hK hKNN]
    _ ≤ ENNReal.ofReal C * ∫⁻ s : ℝ in S, ENNReal.ofReal (kernel s) :=
      mul_le_mul_of_nonneg_left
        (lintegral_mono_ae (hCmp.mono fun _ h => ENNReal.ofReal_le_ofReal h)) (by positivity)

end Shao.C2.AuxiliaryRealMarkedFiniteCutoffExtendedBudget
