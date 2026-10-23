import Shao.OQ3.ParabolaCellAveragedOscillation

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

theorem actual_parabola_cell_ncube_gaussian_oscillation_bound
    (n : ℕ) (hn : 1 ≤ n) (theta : ℝ × ℝ)
    (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (y : ℝ × ℝ)
    (aL aR qL qR level a0 rho : ℝ) (hrho : 0 ≤ rho)
    (hy : y ∈ Set.Icc aL aR ×ˢ Set.Icc qL qR)
    (hawidth : aR - aL ≤ 1 / (n : ℝ)) (hqwidth : qR - qL ≤ 1 / (n : ℝ))
    :
    let h : ℝ := 1 / (n : ℝ) ^ 3
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
        C * (8 * kappa * (R + 1) ^ 2 + 768 * (G + 1)) /
          ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) := by
  have hN1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hN
  have hN2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hN3 : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    calc
      (n : ℝ) = (n : ℝ) * 1 := by ring
      _ ≤ (n : ℝ) * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hN2 hN.le
      _ = (n : ℝ) ^ 3 := by ring
  let h : ℝ := 1 / (n : ℝ) ^ 3
  have hh : 0 < h := div_pos zero_lt_one (pow_pos hN 3)
  have hsmall : h ≤ 1 / Real.sqrt (n : ℝ) := by
    change 1 / (n : ℝ) ^ 3 ≤ 1 / Real.sqrt (n : ℝ)
    apply (div_le_div_iff₀ (pow_pos hN 3) hs).mpr
    simpa only [one_mul] using
      (Real.sqrt_le_self_iff.mpr (Or.inr hN1)).trans hN3
  have hi := actual_parabola_cell_thin_gaussian_oscillation_bound n hn theta E y
    aL aR qL qR level a0 rho hrho hy hawidth hqwidth h hh hsmall
  simpa only [h, mul_one_div, div_div] using hi

end
end Shao.OQ3

