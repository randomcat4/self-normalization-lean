import Shao.OQ3.ParabolaCellAveragedOscillation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
noncomputable section

theorem log_cubic_gaussian_radius_admissible
    (n : ℕ) (hn : 2 ≤ n) :
    0 < Real.log (n : ℝ) / (n : ℝ) ^ 3 ∧
      Real.log (n : ℝ) / (n : ℝ) ^ 3 ≤ 1 / Real.sqrt (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnp : (0 : ℝ) < (n : ℝ) := by linarith
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnp
  have hl : Real.log (n : ℝ) ≤ (n : ℝ) :=
    (Real.log_le_sub_one_of_pos hnp).trans (by linarith)
  have hsq : Real.sqrt (n : ℝ) ≤ (n : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr hn1)
  have hmul : Real.log (n : ℝ) * Real.sqrt (n : ℝ) ≤ (n : ℝ) * (n : ℝ) :=
    mul_le_mul hl hsq (Real.sqrt_nonneg _) (by positivity)
  have hcube : (n : ℝ) * (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.mpr hn1)]
  refine ⟨div_pos (Real.log_pos (by linarith)) (pow_pos hnp 3), ?_⟩
  apply (div_le_div_iff₀ (pow_pos hnp 3) hs).mpr
  simpa only [one_mul] using hmul.trans hcube

theorem actual_parabola_cell_log_cubic_gaussian_oscillation_bound
    (n : ℕ) (hn : 2 ≤ n) (theta : ℝ × ℝ)
    (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (y : ℝ × ℝ)
    (aL aR qL qR level a0 rho : ℝ) (hrho : 0 ≤ rho)
    (hy : y ∈ Set.Icc aL aR ×ˢ Set.Icc qL qR)
    (hawidth : aR - aL ≤ 1 / (n : ℝ)) (hqwidth : qR - qL ≤ 1 / (n : ℝ))
    :
    let h : ℝ := Real.log (n : ℝ) / (n : ℝ) ^ 3
    let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩
      {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
        0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    let B : Set (ℝ × ℝ) :=
      (fun w : ℝ × ℝ => Real.sqrt (n : ℝ) • E (w - y)) '' A
    let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-Real.sqrt (n : ℝ) *
      (theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2))
    let kappa : ℝ := (|theta.1| + |theta.2|) *
      ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
    let R : ℝ := ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
    let C : ℝ := Real.exp (kappa * R)
    let G : ℝ := R * (1 + 2 * (|a0| + rho) / level ^ 2)
    let Φ : MeasureTheory.Measure (ℝ × ℝ) :=
      (ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1)
    MeasureTheory.Integrable (openBallOscillation (B.indicator g) h) Φ ∧
      (∫ z, openBallOscillation (B.indicator g) h z ∂Φ) ≤
        C * (8 * kappa * (R + 1) ^ 2 + 768 * (G + 1)) * Real.log (n : ℝ) /
          ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hh, hsmall⟩ := log_cubic_gaussian_radius_admissible n hn
  have hi := actual_parabola_cell_thin_gaussian_oscillation_bound n hn1 theta E y
    aL aR qL qR level a0 rho hrho hy hawidth hqwidth
    (Real.log (n : ℝ) / (n : ℝ) ^ 3) hh hsmall
  simpa only [mul_div_assoc, div_div] using hi

theorem log_cubic_gaussian_oscillation_normalized_tendsto_zero :
    Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 *
        (Real.log (n : ℝ) / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ))))
      Filter.atTop (nhds 0) := by
  have ht : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ))
      atTop (𝓝 0) :=
    (_root_.isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hnat : Tendsto (fun n : ℕ => Real.log (n : ℝ) / Real.sqrt (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using
      ht.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  apply hnat.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnp : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  field_simp [hnp.ne', (Real.sqrt_pos.mpr hnp).ne']

end
end Shao.OQ3
