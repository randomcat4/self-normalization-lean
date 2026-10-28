import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Shao.OQ3
open Filter
noncomputable section

theorem log_square_gaussian_four_le_rpow
    (a x : ℝ) (ha : 0 ≤ a) (hx : 0 < x)
    (hlogone : 1 ≤ Real.log x) (hloglarge : 2 * (a + Real.log 4) ≤ Real.log x) :
    4 * Real.exp (-(Real.log x) ^ 2 / 2) ≤ Real.rpow x (-a) := by
  have hlognonneg : 0 ≤ Real.log x := le_trans zero_le_one hlogone
  have hfourlog : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hp := mul_nonneg (sub_nonneg.mpr hloglarge) hlognonneg
  have hq := mul_nonneg hfourlog (sub_nonneg.mpr hlogone)
  calc
    _ = Real.exp (Real.log 4) * Real.exp (-(Real.log x) ^ 2 / 2) := by
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    _ = Real.exp (Real.log 4 - (Real.log x) ^ 2 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (Real.log x * (-a)) := Real.exp_le_exp.2 (by nlinarith)
    _ = _ := (Real.rpow_def_of_pos hx (-a)).symm

theorem cubic_gaussian_smoothing_scale_identity
    (n : ℕ) (hn : 1 ≤ n) :
    let b : ℝ := 1 / (2 * (n : ℝ) ^ 6)
    let eps : ℝ := Real.log (n : ℝ) / (n : ℝ) ^ 3
    0 < b ∧ 0 ≤ eps ∧
      Real.exp (-eps ^ 2 / (4 * b)) = Real.exp (-(Real.log (n : ℝ)) ^ 2 / 2) := by
  intro b eps
  have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnr
  refine ⟨by dsimp only [b]; positivity, ?_, ?_⟩
  · dsimp only [eps]
    exact div_nonneg (Real.log_nonneg hnr) (by positivity)
  · congr 1
    dsimp only [b, eps]
    field_simp [hnp.ne']
    ring

theorem cubic_gaussian_smoothing_scale_superpolynomial
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let b : ℝ := 1 / (2 * (n : ℝ) ^ 6)
      let eps : ℝ := Real.log (n : ℝ) / (n : ℝ) ^ 3
      0 < b ∧ 0 ≤ eps ∧
        4 * Real.exp (-eps ^ 2 / (4 * b)) ≤ Real.rpow (n : ℝ) (-a) := by
  have ht : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ n : ℕ in atTop,
      1 ≤ n ∧ 1 ≤ Real.log (n : ℝ) ∧ 2 * (a + Real.log 4) ≤ Real.log (n : ℝ) :=
    (eventually_ge_atTop 1).and
      ((ht.eventually (eventually_ge_atTop 1)).and
        (ht.eventually (eventually_ge_atTop (2 * (a + Real.log 4)))))
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  refine ⟨N, (hN N le_rfl).1, fun n hn => ?_⟩
  intro b eps
  have hh := hN n hn
  have hscale := cubic_gaussian_smoothing_scale_identity n hh.1
  change 0 < b ∧ 0 ≤ eps ∧
    Real.exp (-eps ^ 2 / (4 * b)) = Real.exp (-(Real.log (n : ℝ)) ^ 2 / 2) at hscale
  obtain ⟨hb, heps, hi⟩ := hscale
  refine ⟨hb, heps, ?_⟩
  rw [hi]
  have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hh.1
  exact log_square_gaussian_four_le_rpow a (n : ℝ) ha
    (lt_of_lt_of_le zero_lt_one hnr) hh.2.1 hh.2.2

end
end Shao.OQ3
