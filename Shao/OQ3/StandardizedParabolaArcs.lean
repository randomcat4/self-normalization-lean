import Shao.OQ3.ParabolaArcLipschitz
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace Shao.OQ3
open scoped Topology
noncomputable section

theorem actual_six_standardized_arcs_lipschitz
    (n : ℕ) (hn : 1 ≤ n) (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (y : ℝ × ℝ)
    (aL aR qL qR level a0 rho : ℝ) (hrho : 0 ≤ rho)
    (hclip : max aL (a0 - rho) ≤ min aR (a0 + rho)) (hqorder : qL ≤ qR)
    (hawidth : aR - aL ≤ 1 / (n : ℝ)) (hqwidth : qR - qL ≤ 1 / (n : ℝ)) :
    let L : ℝ := max aL (a0 - rho)
    let R : ℝ := min aR (a0 + rho)
    let M : ℝ := |a0| + rho
    let C : ℝ := 1 + 2 * M / level ^ 2
    let curve : Fin 6 → ℝ → ℝ × ℝ := ![
      (fun t => (L + t * (R - L), qL)),
      (fun t => (L + t * (R - L), qR)),
      (fun t => (L, qL + t * (qR - qL))),
      (fun t => (R, qL + t * (qR - qL))),
      (fun t => (L + t * (R - L), (L + t * (R - L)) ^ 2 / level ^ 2)),
      (fun t => (L + t * (R - L), (L + t * (R - L)) ^ 2 / level ^ 2 - rho))]
    ∀ i : Fin 6,
      LipschitzOnWith (Real.toNNReal (‖E‖ * C / Real.sqrt (n : ℝ)))
        (fun t : ℝ => Real.sqrt (n : ℝ) • E (curve i t - y))
        (Set.Icc (0 : ℝ) 1) := by
  classical
  let L : ℝ := max aL (a0 - rho)
  let R : ℝ := min aR (a0 + rho)
  let M : ℝ := |a0| + rho
  let C : ℝ := 1 + 2 * M / level ^ 2
  let curve : Fin 6 → ℝ → ℝ × ℝ := ![
    (fun t => (L + t * (R - L), qL)),
    (fun t => (L + t * (R - L), qR)),
    (fun t => (L, qL + t * (qR - qL))),
    (fun t => (R, qL + t * (qR - qL))),
    (fun t => (L + t * (R - L), (L + t * (R - L)) ^ 2 / level ^ 2)),
    (fun t => (L + t * (R - L), (L + t * (R - L)) ^ 2 / level ^ 2 - rho))]
  have hN : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hN
  have hM : 0 ≤ M := add_nonneg (abs_nonneg _) hrho
  have hratio : 0 ≤ 2 * M / level ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) hM) (sq_nonneg _)
  have hC1 : 1 ≤ C := by dsimp only [C]; linarith
  have hCr : 2 * M / level ^ 2 ≤ C := by dsimp only [C]; linarith
  have hC : 0 ≤ C := zero_le_one.trans hC1
  have hCN : 0 ≤ C / (n : ℝ) := div_nonneg hC hN.le
  have hwidth : 1 / (n : ℝ) ≤ C / (n : ℝ) :=
    div_le_div_of_nonneg_right hC1 hN.le
  have hdx0 : 0 ≤ R - L := sub_nonneg.mpr hclip
  have hdx : R - L ≤ 1 / (n : ℝ) := by
    have hl : aL ≤ L := le_max_left _ _
    have hr : R ≤ aR := min_le_left _ _
    linarith
  have hdxabs : |R - L| ≤ 1 / (n : ℝ) := by rw [abs_of_nonneg hdx0]; exact hdx
  have hdq0 : 0 ≤ qR - qL := sub_nonneg.mpr hqorder
  have hdqabs : |qR - qL| ≤ 1 / (n : ℝ) := by
    rw [abs_of_nonneg hdq0]
    exact hqwidth
  have hzero : |(0 : ℝ)| ≤ 1 / (n : ℝ) := by
    simpa only [abs_zero] using (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hN.le)
  have hposition : ∀ t ∈ Set.Icc (0 : ℝ) 1, |L + t * (R - L)| ≤ M := by
    intro t ht
    have hl : a0 - rho ≤ L := le_max_right _ _
    have hr : R ≤ a0 + rho := min_le_right _ _
    have ht0 : 0 ≤ t * (R - L) := mul_nonneg ht.1 hdx0
    have ht1 : t * (R - L) ≤ R - L := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 hdx0
    have hcenter : |L + t * (R - L) - a0| ≤ rho := abs_le.mpr ⟨by linarith, by linarith⟩
    calc
      |L + t * (R - L)| =
          |(L + t * (R - L) - a0) + a0| := by congr 1; ring
      _ ≤ |L + t * (R - L) - a0| + |a0| := abs_add_le _ _
      _ ≤ rho + |a0| := add_le_add hcenter le_rfl
      _ = M := by dsimp only [M]; ring
  have hstraight (a b dx dq : ℝ) (hx : |dx| ≤ 1 / (n : ℝ))
      (hq : |dq| ≤ 1 / (n : ℝ)) :
      LipschitzOnWith (Real.toNNReal (C / (n : ℝ)))
        (fun t : ℝ => (a + t * dx, b + t * dq)) (Set.Icc (0 : ℝ) 1) := by
    exact (affine_segment_lipschitz a b dx dq).lipschitzOnWith.weaken
      (Real.toNNReal_mono ((max_le hx hq).trans hwidth))
  have hparabola (shift : ℝ) :
      LipschitzOnWith (Real.toNNReal (C / (n : ℝ)))
        (fun t : ℝ => (L + t * (R - L), (L + t * (R - L)) ^ 2 / level ^ 2 - shift))
        (Set.Icc (0 : ℝ) 1) := by
    have hk : |R - L| * max 1 (2 * M / level ^ 2) ≤ C / (n : ℝ) := by
      calc
        _ ≤ (1 / (n : ℝ)) * C :=
          mul_le_mul hdxabs (max_le hC1 hCr)
            (zero_le_one.trans (le_max_left _ _)) (div_nonneg (by norm_num) hN.le)
        _ = C / (n : ℝ) := by ring
    exact (parabola_segment_lipschitz L (R - L) level shift M hM hposition).weaken
      (Real.toNNReal_mono hk)
  have hraw (i : Fin 6) : LipschitzOnWith (Real.toNNReal (C / (n : ℝ)))
      (curve i) (Set.Icc (0 : ℝ) 1) := by
    fin_cases i <;> simp only [curve, Matrix.cons_val_zero', Matrix.cons_val_succ']
    · simpa only [mul_zero, add_zero] using hstraight L qL (R - L) 0 hdxabs hzero
    · simpa only [mul_zero, add_zero] using hstraight L qR (R - L) 0 hdxabs hzero
    · simpa only [mul_zero, add_zero] using hstraight L qL 0 (qR - qL) hzero hdqabs
    · simpa only [mul_zero, add_zero] using hstraight R qL 0 (qR - qL) hzero hdqabs
    · simpa only [sub_zero] using hparabola 0
    · exact hparabola rho
  have hscale : Real.sqrt (n : ℝ) * ‖E‖ * (Real.toNNReal (C / (n : ℝ)) : ℝ) =
      ‖E‖ * C / Real.sqrt (n : ℝ) := by
    rw [Real.coe_toNNReal _ hCN]
    calc
      _ = (‖E‖ * C) * Real.sqrt (n : ℝ) / (n : ℝ) := by ring
      _ = (‖E‖ * C) * Real.sqrt (n : ℝ) / (Real.sqrt (n : ℝ)) ^ 2 := by
        rw [Real.sq_sqrt hN.le]
      _ = ‖E‖ * C / Real.sqrt (n : ℝ) := by field_simp [hs.ne'] <;> ring
  change ∀ i : Fin 6,
    LipschitzOnWith (Real.toNNReal (‖E‖ * C / Real.sqrt (n : ℝ)))
      (fun t : ℝ => Real.sqrt (n : ℝ) • E (curve i t - y)) (Set.Icc (0 : ℝ) 1)
  intro i
  have hi := standardized_lipschitz_arc n E y (curve i) (Real.toNNReal (C / (n : ℝ))) (hraw i)
  simpa only [hscale] using hi

end
end Shao.OQ3

