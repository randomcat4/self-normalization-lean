import Shao.OQ3.GaussianNoiseTailBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Shao.OQ3
open MeasureTheory Filter
open scoped NNReal
noncomputable section

theorem log_square_gaussian_half_four_le_rpow
    (a x : ℝ) (ha : 0 ≤ a) (hx : 0 < x)
    (hlogone : 1 ≤ Real.log x) (hloglarge : 8 * (a + Real.log 4) ≤ Real.log x) :
    4 * Real.exp (-(Real.log x) ^ 2 / 8) ≤ Real.rpow x (-a) := by
  have hlognonneg : 0 ≤ Real.log x := le_trans zero_le_one hlogone
  have hfourlog : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hp := mul_nonneg (sub_nonneg.mpr hloglarge) hlognonneg
  have hq := mul_nonneg hfourlog (sub_nonneg.mpr hlogone)
  calc
    _ = Real.exp (Real.log 4) * Real.exp (-(Real.log x) ^ 2 / 8) := by
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    _ = Real.exp (Real.log 4 - (Real.log x) ^ 2 / 8) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (Real.log x * (-a)) := Real.exp_le_exp.2 (by nlinarith)
    _ = _ := (Real.rpow_def_of_pos hx (-a)).symm

theorem cubic_gaussian_half_oscillation_noise_superpolynomial
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let b : ℝ := 1 / (2 * (n : ℝ) ^ 6)
      let h : ℝ := Real.log (n : ℝ) / (n : ℝ) ^ 3
      let v : ℝ≥0 := Real.toNNReal (2 * b)
      let gamma : Measure (ℝ × ℝ) :=
        (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
      0 < b ∧ 0 < h ∧
        gamma.real {d : ℝ × ℝ | h / 2 < ‖d‖} ≤
          4 * Real.exp (-(Real.log (n : ℝ)) ^ 2 / 8) ∧
        gamma.real {d : ℝ × ℝ | h / 2 < ‖d‖} ≤ Real.rpow (n : ℝ) (-a) := by
  have ht : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ 1 ≤ Real.log (n : ℝ) ∧ 8 * (a + Real.log 4) ≤ Real.log (n : ℝ) :=
    (eventually_ge_atTop 2).and
      ((ht.eventually (eventually_ge_atTop 1)).and
        (ht.eventually (eventually_ge_atTop (8 * (a + Real.log 4)))))
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  refine ⟨N, (hN N le_rfl).1, ?_⟩
  intro n hn b h v gamma
  have hh := hN n hn
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hb : 0 < b := by dsimp [b]; positivity
  have hlog : 0 < Real.log (n : ℝ) := lt_of_lt_of_le zero_lt_one hh.2.1
  have hpos : 0 < h := by dsimp [h]; positivity
  have htail := pair_gaussian_noise_tail_le b hb (h / 2) (by positivity)
  have hi : -(h / 2) ^ 2 / (4 * b) = -(Real.log (n : ℝ)) ^ 2 / 8 := by
    dsimp only [h, b]
    field_simp [hnp.ne']
    ring
  have hfirst : gamma.real {d : ℝ × ℝ | h / 2 < ‖d‖} ≤
      4 * Real.exp (-(Real.log (n : ℝ)) ^ 2 / 8) := by
    change gamma.real {d : ℝ × ℝ | h / 2 < ‖d‖} ≤
      4 * Real.exp (-(h / 2) ^ 2 / (4 * b)) at htail
    simpa only [hi] using htail
  refine ⟨hb, hpos, hfirst, ?_⟩
  exact hfirst.trans (log_square_gaussian_half_four_le_rpow a (n : ℝ) ha hnp hh.2.1 hh.2.2)

end
end Shao.OQ3
