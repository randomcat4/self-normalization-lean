import Shao.C2.AuxiliaryRealDampedMoments
import Shao.Probability.SourceSuffixMomentBudgets
import Lean

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Shao.C2.AuxiliaryRealMarkedMoments
open MeasureTheory ProbabilityTheory

theorem scaled_nonnegative_real_power_le
    (x a s : ℝ) (k : ℕ) (hx : 0 ≤ x) (ha : 0 ≤ a) (hs : 0 < s) (hk : a ≤ (k : ℝ)) :
    Real.rpow x a ≤ Real.rpow s (-a / 2) *
      (1 + Real.rpow s ((k : ℝ) / 2) * x ^ k) := by
  run_tac
    let n := Lean.mkPrivateNameCore ("Shao.C2.AuxiliaryRealDampedMoments".toName)
      ("Shao.C2.AuxiliaryRealDampedMoments.scaled_real_power_le".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
      $(Lean.mkIdent ("x".toName)) $(Lean.mkIdent ("a".toName)) $(Lean.mkIdent ("s".toName))
      $(Lean.mkIdent ("k".toName)) $(Lean.mkIdent ("hx".toName)) $(Lean.mkIdent ("ha".toName))
      $(Lean.mkIdent ("hs".toName)) $(Lean.mkIdent ("hk".toName))))

theorem auxiliary_actual_real_marked_gaussian_damped_moments :
    let c : ℝ := (1 - Real.exp (-2)) / 8
    ∀ a : ℝ, 0 ≤ a → ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ (m : ℕ) (b s : ℝ), 0 < b → 0 < s → s ≤ 2 / b →
          let P : Measure (Shao.Path (m + 1)) := Measure.pi (fun _ : Fin (m + 1) => nu)
          let M : Shao.Path (m + 1) → ℝ := fun v => |v 0| ^ 3
          let a3 : ℝ → ℝ := fun u => ∫ z : ℝ, |z| ^ 3 * Real.exp (-u * z ^ 2) ∂nu
          let retained : ℝ := ∫ z : ℝ, if z ^ 2 ≤ b then z ^ 2 else 0 ∂nu
          let gamma : ℝ := if (1 / 2 : ℝ) ≤ retained then -c else 1
          Integrable (fun v : Shao.Path (m + 1) =>
            M v * Real.rpow |Shao.prefixSum v (m + 1)| a * Real.exp (-s * Shao.energy v)) P ∧
            (∫ v : Shao.Path (m + 1),
              M v * Real.rpow |Shao.prefixSum v (m + 1)| a * Real.exp (-s * Shao.energy v) ∂P) ≤
              C * Real.rpow s (-a / 2) * a3 (s / 2) *
                Real.exp (gamma * s * (m : ℝ)) := by
  intro c a ha
  let k : ℕ := Nat.ceil a
  have hka : a ≤ (k : ℝ) := Nat.le_ceil a
  obtain ⟨C0, hC0, hMoment0⟩ := Shao.Probability.iid_marked_gaussian_damped_moments 0
  obtain ⟨Ck, hCk, hMomentk⟩ := Shao.Probability.iid_marked_gaussian_damped_moments k
  refine ⟨C0 + Ck, add_pos hC0 hCk, ?_⟩
  intro nu _ h2 hMean hNorm m b s hb hs hsb P M a3 retained gamma
  let W : Shao.Path (m + 1) → ℝ := fun v => Real.exp (-s * Shao.energy v)
  let F0 : Shao.Path (m + 1) → ℝ := fun v => M v * W v
  let Fk : Shao.Path (m + 1) → ℝ := fun v => M v * |Shao.prefixSum v (m + 1)| ^ k * W v
  let A : ℝ := Real.rpow s (-a / 2)
  let B : ℝ := Real.rpow s ((k : ℝ) / 2)
  let G : ℝ := a3 (s / 2)
  let E : ℝ := Real.exp (gamma * s * (m : ℝ))
  let U : Shao.Path (m + 1) → ℝ := fun v => A * (F0 v + B * Fk v)
  have hRpowZero : Real.rpow s 0 = 1 := Real.rpow_zero s
  have h0 : Integrable F0 P ∧ (∫ v : Shao.Path (m + 1), F0 v ∂P) ≤ C0 * G * E := by
    simpa only [pow_zero, mul_one, Nat.cast_zero, neg_zero, zero_div, hRpowZero] using
      hMoment0 nu h2 hMean hNorm m b s hb hs hsb
  have hkMoment := hMomentk nu h2 hMean hNorm m b s hb hs hsb
  have hU : Integrable U P := (h0.1.add (hkMoment.1.const_mul B)).const_mul A
  have hMNonneg (v : Shao.Path (m + 1)) : 0 ≤ M v := pow_nonneg (abs_nonneg _) 3
  have hPoint (v : Shao.Path (m + 1)) :
      M v * Real.rpow |Shao.prefixSum v (m + 1)| a * W v ≤ U v := by
    calc
      _ = Real.rpow |Shao.prefixSum v (m + 1)| a * (M v * W v) := by ring
      _ ≤ (A * (1 + B * |Shao.prefixSum v (m + 1)| ^ k)) * (M v * W v) :=
        mul_le_mul_of_nonneg_right
          (scaled_nonnegative_real_power_le |Shao.prefixSum v (m + 1)| a s k
            (abs_nonneg _) ha hs hka) (mul_nonneg (hMNonneg v) (Real.exp_pos _).le)
      _ = _ := by dsimp only [U, F0, Fk]; ring
  have hCoord : Continuous (fun v : Shao.Path (m + 1) => v 0) := continuous_apply 0
  have hMCont : Continuous M := hCoord.abs.pow 3
  have hMeas : Continuous (fun v : Shao.Path (m + 1) =>
      M v * Real.rpow |Shao.prefixSum v (m + 1)| a * W v) :=
    (hMCont.mul ((Shao.continuous_prefixSum (m + 1)).abs.rpow_const (fun _ => Or.inr ha))).mul
      (Real.continuous_exp.comp (continuous_const.mul Shao.continuous_energy))
  have hInt : Integrable (fun v : Shao.Path (m + 1) =>
      M v * Real.rpow |Shao.prefixSum v (m + 1)| a * W v) P := by
    refine hU.mono' hMeas.aestronglyMeasurable (ae_of_all _ fun v => ?_)
    have hNonneg : 0 ≤ M v * Real.rpow |Shao.prefixSum v (m + 1)| a * W v :=
      mul_nonneg (mul_nonneg (hMNonneg v) (Real.rpow_nonneg (abs_nonneg _) a)) (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
    exact hPoint v
  have hCancel : B * Real.rpow s (-(k : ℝ) / 2) = 1 := by
    change s ^ ((k : ℝ) / 2) * s ^ (-(k : ℝ) / 2) = 1
    rw [← Real.rpow_add hs, show (k : ℝ) / 2 + -(k : ℝ) / 2 = 0 by ring, Real.rpow_zero]
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ v : Shao.Path (m + 1), U v ∂P := integral_mono hInt hU hPoint
    _ = A * ((∫ v : Shao.Path (m + 1), F0 v ∂P) +
        B * ∫ v : Shao.Path (m + 1), Fk v ∂P) := by
      dsimp only [U]
      rw [integral_const_mul, integral_add h0.1 (hkMoment.1.const_mul B), integral_const_mul]
    _ ≤ A * (C0 * G * E + B * (Ck * Real.rpow s (-(k : ℝ) / 2) * G * E)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add h0.2 (mul_le_mul_of_nonneg_left hkMoment.2 (Real.rpow_nonneg hs.le _)))
        (Real.rpow_nonneg hs.le _)
    _ = (C0 + Ck * (B * Real.rpow s (-(k : ℝ) / 2))) * A * G * E := by ring
    _ = _ := by rw [hCancel]; ring

end Shao.C2.AuxiliaryRealMarkedMoments
