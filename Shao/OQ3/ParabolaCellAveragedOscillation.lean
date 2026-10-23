import Shao.OQ3.StandardizedGaussianCellOscillation
import Shao.OQ3.ParabolaCellGaussianTube

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

theorem actual_parabola_cell_thin_gaussian_oscillation_bound
    (n : ℕ) (hn : 1 ≤ n) (theta : ℝ × ℝ)
    (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (y : ℝ × ℝ)
    (aL aR qL qR level a0 rho : ℝ) (hrho : 0 ≤ rho)
    (hy : y ∈ Set.Icc aL aR ×ˢ Set.Icc qL qR)
    (hawidth : aR - aL ≤ 1 / (n : ℝ)) (hqwidth : qR - qL ≤ 1 / (n : ℝ))
    (h : ℝ) (hh : 0 < h) (hsmall : h ≤ 1 / Real.sqrt (n : ℝ)) :
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
        C * (8 * kappa * (R + 1) ^ 2 + 768 * (G + 1)) * h / Real.sqrt (n : ℝ) := by
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
  let Φ : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)
  change Integrable (openBallOscillation (B.indicator g) h) Φ ∧
    (∫ z, openBallOscillation (B.indicator g) h z ∂Φ) ≤
      C * (8 * kappa * (R + 1) ^ 2 + 768 * (G + 1)) * h / Real.sqrt (n : ℝ)
  have hN : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hN
  have hR : 0 ≤ R := norm_nonneg _
  have hkappa : 0 ≤ kappa :=
    mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (norm_nonneg _)
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hcell : ∀ w ∈ A, ‖w - y‖ ≤ (1 : ℝ) / (n : ℝ) := by
    intro w hw
    have ha : w.1 ∈ Set.Ioc aL aR := hw.1.1
    have hq : w.2 ∈ Set.Ioc qL qR := hw.1.2
    have hx : |w.1 - y.1| ≤ 1 / (n : ℝ) :=
      abs_le.mpr ⟨by linarith [ha.1, hy.1.2], by linarith [ha.2, hy.1.1]⟩
    have hz : |w.2 - y.2| ≤ 1 / (n : ℝ) :=
      abs_le.mpr ⟨by linarith [hq.1, hy.2.2], by linarith [hq.2, hy.2.1]⟩
    simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs] using max_le hx hz
  have hAX : Integrable (openBallOscillation (B.indicator g) h) Φ ∧
      (∫ z, openBallOscillation (B.indicator g) h z ∂Φ) ≤
        8 * Real.sqrt (n : ℝ) * kappa * C * h *
          (R / Real.sqrt (n : ℝ) + h) ^ 2 +
        2 * C * Φ.real (Metric.cthickening h (frontier B)) := by
    simpa only [one_mul] using
      standardized_gaussian_cell_averaged_oscillation_bound n hn theta E y 1
        (by norm_num) A hcell h hh.le
  have htube : Φ.real (Metric.cthickening h (frontier B)) ≤
      384 * (G * h / Real.sqrt (n : ℝ) + h ^ 2) :=
    actual_standardized_parabola_cell_frontier_tube_bound n hn E y
      aL aR qL qR level a0 rho hrho hawidth hqwidth h hh
  have hnear0 : 0 ≤ R / Real.sqrt (n : ℝ) + h :=
    add_nonneg (div_nonneg hR hs.le) hh.le
  have hbig0 : 0 ≤ (R + 1) / Real.sqrt (n : ℝ) :=
    div_nonneg (add_nonneg hR zero_le_one) hs.le
  have hnearle : R / Real.sqrt (n : ℝ) + h ≤ (R + 1) / Real.sqrt (n : ℝ) := by
    calc
      _ ≤ R / Real.sqrt (n : ℝ) + 1 / Real.sqrt (n : ℝ) := add_le_add le_rfl hsmall
      _ = _ := by ring
  have hnearSq : (R / Real.sqrt (n : ℝ) + h) ^ 2 ≤
      ((R + 1) / Real.sqrt (n : ℝ)) ^ 2 := by
    nlinarith [mul_le_mul hnearle hnearle hnear0 hbig0]
  have hnear : 8 * Real.sqrt (n : ℝ) * kappa * C * h *
      (R / Real.sqrt (n : ℝ) + h) ^ 2 ≤
      8 * kappa * C * (R + 1) ^ 2 * h / Real.sqrt (n : ℝ) := by
    calc
      _ ≤ 8 * Real.sqrt (n : ℝ) * kappa * C * h *
          ((R + 1) / Real.sqrt (n : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hnearSq (by positivity)
      _ = _ := by field_simp [hs.ne'] <;> ring
  have hhsq : h ^ 2 ≤ h / Real.sqrt (n : ℝ) := by
    calc
      h ^ 2 = h * h := by ring
      _ ≤ h * (1 / Real.sqrt (n : ℝ)) := mul_le_mul_of_nonneg_left hsmall hh.le
      _ = _ := by ring
  have hboundary : G * h / Real.sqrt (n : ℝ) + h ^ 2 ≤
      (G + 1) * h / Real.sqrt (n : ℝ) := by
    calc
      _ ≤ G * h / Real.sqrt (n : ℝ) + h / Real.sqrt (n : ℝ) := add_le_add le_rfl hhsq
      _ = _ := by ring
  have hprob : 2 * C * Φ.real (Metric.cthickening h (frontier B)) ≤
      768 * C * (G * h / Real.sqrt (n : ℝ) + h ^ 2) := by
    calc
      _ ≤ 2 * C * (384 * (G * h / Real.sqrt (n : ℝ) + h ^ 2)) :=
        mul_le_mul_of_nonneg_left htube (mul_nonneg (by norm_num) hC)
      _ = _ := by ring
  refine ⟨hAX.1, hAX.2.trans ?_⟩
  calc
    _ ≤ 8 * kappa * C * (R + 1) ^ 2 * h / Real.sqrt (n : ℝ) +
        768 * C * ((G + 1) * h / Real.sqrt (n : ℝ)) :=
      add_le_add hnear (hprob.trans
        (mul_le_mul_of_nonneg_left hboundary (mul_nonneg (by norm_num) hC)))
    _ = C * (8 * kappa * (R + 1) ^ 2 + 768 * (G + 1)) * h / Real.sqrt (n : ℝ) := by ring

end
end Shao.OQ3

