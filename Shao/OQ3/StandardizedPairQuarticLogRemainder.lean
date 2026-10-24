import Shao.OQ3.StandardizedPairLogMomentApproximation
import Shao.OQ3.PairCharacteristicLowMomentPolynomial
import Shao.OQ3.ComplexLogTaylorQuarticCorrection

namespace Shao.OQ3

open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

theorem uniform_standardized_pair_quartic_log_remainder
    {ι : Type*} (law : ι → Measure (Fin 2 → ℝ))
    (hprob : ∀ i, IsProbabilityMeasure (law i))
    (hL2 : ∀ i, ∀ j : Fin 2, MemLp (fun y : Fin 2 → ℝ => y j) 2 (law i))
    (hmean : ∀ i, ∀ j : Fin 2, (∫ y : Fin 2 → ℝ, y j ∂law i) = 0)
    (hcov : ∀ i, ∀ j k : Fin 2, ProbabilityTheory.covariance
      (fun y : Fin 2 → ℝ => y j) (fun y : Fin 2 → ℝ => y k) (law i) =
        if j = k then 1 else 0)
    (M3 M4 M5 : ℝ)
    (hI3 : ∀ i, Integrable
      (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3) (law i))
    (hM3 : ∀ i, (∫ y : Fin 2 → ℝ,
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3 ∂law i) ≤ M3)
    (hI4 : ∀ i, Integrable
      (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 4) (law i))
    (hM4 : ∀ i, (∫ y : Fin 2 → ℝ,
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 4 ∂law i) ≤ M4)
    (hI5 : ∀ i, Integrable
      (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 5) (law i))
    (hM5 : ∀ i, (∫ y : Fin 2 → ℝ,
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 5 ∂law i) ≤ M5) :
    let Phi : ι → ℝ → ℝ → ℂ := fun i u v =>
      ∫ y : Fin 2 → ℝ,
        Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂law i
    let Q : ι → ℝ → ℝ → ℂ := fun i u v =>
      -((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2 -
        Complex.I * ((∫ y : Fin 2 → ℝ,
          (u * y 0 + v * y 1) ^ 3 ∂law i : ℝ) : ℂ) / 6 +
        (((∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 4 ∂law i : ℝ) -
          3 * (u ^ 2 + v ^ 2) ^ 2 : ℝ) : ℂ) / 24
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
      ∀ i, ∀ u v : ℝ, Real.sqrt (u ^ 2 + v ^ 2) ≤ delta →
        ‖Complex.log (Phi i u v) - Q i u v‖ ≤
          C * Real.sqrt (u ^ 2 + v ^ 2) ^ 5 := by
  intro Phi Q
  let K2 : ℝ := 2 + (Real.exp 1 + 4) * |M3|
  let K5 : ℝ := 1 + (Real.exp 1 + (5 : ℝ) + 1) * |M5|
  let B : ℝ := 1 + |M3|
  let T : ℝ := 1 + |M4|
  let H : ℝ := (1 / 2 : ℝ) * (B + T) + (B + T) ^ 2
  obtain ⟨hK2, hK5, delta, hdpos, hdle, hlog⟩ :=
    uniform_standardized_pair_log_moment_approximation
      law hprob hL2 hmean hcov 5 (by norm_num) M3 M5 hI3 hM3 hI5 hM5
  change 0 < K2 at hK2
  change 0 < K5 at hK5
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hH : 0 ≤ H := by
    dsimp only [H]
    exact add_nonneg (mul_nonneg (by norm_num) (add_nonneg hB hT)) (sq_nonneg _)
  let Ctot : ℝ := 2 * K2 ^ 3 + 3 * K5 + H + 1
  have hCtot : 0 < Ctot := by
    dsimp only [Ctot]
    positivity
  refine ⟨Ctot, delta, hCtot, hdpos, hdle, ?_⟩
  intro i u v hrad
  letI : IsProbabilityMeasure (law i) := hprob i
  let r : ℝ := Real.sqrt (u ^ 2 + v ^ 2)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r ≤ 1 := hrad.trans hdle
  have hr2 : r ^ 2 = u ^ 2 + v ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg u) (sq_nonneg v))
  have hr65 : r ^ 6 ≤ r ^ 5 := by
    calc
      r ^ 6 = r ^ 5 * r := by ring
      _ ≤ r ^ 5 * 1 := mul_le_mul_of_nonneg_left hr1 (pow_nonneg hr0 5)
      _ = r ^ 5 := by ring
  let L : (Fin 2 → ℝ) → ℝ := fun y => u * y 0 + v * y 1
  let m3 : ℝ := ∫ y, L y ^ 3 ∂law i
  let m4 : ℝ := ∫ y, L y ^ 4 ∂law i
  let a : ℂ := -((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2
  let b : ℂ := -Complex.I * (m3 : ℂ) / 6
  let c : ℂ := (m4 : ℂ) / 24
  obtain ⟨hs3, hs4, hpoly⟩ :=
    pair_probability_degree_four_moment_polynomial
      (law i) (hL2 i) (hmean i) (hcov i) (hI3 i) (hI4 i) u v
  have hpolyL :
      (∑ j ∈ Finset.range 5, (Complex.I ^ j / (j.factorial : ℂ)) *
        ((∫ y, L y ^ j ∂law i : ℝ) : ℂ)) =
      1 - ((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2 -
        Complex.I * (m3 : ℂ) / 6 + (m4 : ℂ) / 24 := hpoly
  have hP :
      (∑ j ∈ Finset.range 5, (Complex.I ^ j / (j.factorial : ℂ)) *
        ((∫ y, L y ^ j ∂law i : ℝ) : ℂ)) - 1 = a + b + c := by
    rw [hpolyL]
    dsimp only [a, b, c]
    ring
  have hm3abs : |m3| ≤ r ^ 3 * |M3| := by
    calc
      |m3| ≤ ∫ y, |L y| ^ 3 ∂law i := by
        have hn := norm_integral_le_integral_norm (μ := law i)
          (fun y : Fin 2 → ℝ => L y ^ 3)
        change ‖m3‖ ≤ ∫ y, ‖L y ^ 3‖ ∂law i at hn
        have heq : (fun y : Fin 2 → ℝ => ‖L y ^ 3‖) =
            (fun y => |L y| ^ 3) := by
          funext y
          rw [Real.norm_eq_abs, abs_pow]
        rw [heq] at hn
        simpa only [Real.norm_eq_abs] using hn
      _ ≤ r ^ 3 * (∫ y : Fin 2 → ℝ,
          Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3 ∂law i) :=
        (pair_projection_absolute_moment_bound (law i) 3 (hI3 i) u v).2.2
      _ ≤ r ^ 3 * |M3| :=
        mul_le_mul_of_nonneg_left ((hM3 i).trans (le_abs_self M3)) (pow_nonneg hr0 3)
  have hm4abs : |m4| ≤ r ^ 4 * |M4| := by
    calc
      |m4| ≤ ∫ y, |L y| ^ 4 ∂law i := by
        have hn := norm_integral_le_integral_norm (μ := law i)
          (fun y : Fin 2 → ℝ => L y ^ 4)
        change ‖m4‖ ≤ ∫ y, ‖L y ^ 4‖ ∂law i at hn
        have heq : (fun y : Fin 2 → ℝ => ‖L y ^ 4‖) =
            (fun y => |L y| ^ 4) := by
          funext y
          rw [Real.norm_eq_abs, abs_pow]
        rw [heq] at hn
        simpa only [Real.norm_eq_abs] using hn
      _ ≤ r ^ 4 * (∫ y : Fin 2 → ℝ,
          Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 4 ∂law i) :=
        (pair_projection_absolute_moment_bound (law i) 4 (hI4 i) u v).2.2
      _ ≤ r ^ 4 * |M4| :=
        mul_le_mul_of_nonneg_left ((hM4 i).trans (le_abs_self M4)) (pow_nonneg hr0 4)
  have ha : ‖a‖ ≤ (1 / 2 : ℝ) * r ^ 2 := by
    calc
      ‖a‖ = (u ^ 2 + v ^ 2) / 2 := by
        dsimp only [a]
        rw [Complex.norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (add_nonneg (sq_nonneg u) (sq_nonneg v))]
        norm_num
      _ ≤ (1 / 2 : ℝ) * r ^ 2 := by nlinarith [hr2]
  have hb : ‖b‖ ≤ B * r ^ 3 := by
    calc
      ‖b‖ = |m3| / 6 := by
        dsimp only [b]
        rw [Complex.norm_div, Complex.norm_mul, norm_neg, Complex.norm_I,
          Complex.norm_real, Real.norm_eq_abs]
        norm_num
      _ ≤ |m3| := div_le_self (abs_nonneg _) (by norm_num)
      _ ≤ r ^ 3 * |M3| := hm3abs
      _ ≤ B * r ^ 3 := by dsimp only [B]; nlinarith [pow_nonneg hr0 3]
  have hc : ‖c‖ ≤ T * r ^ 4 := by
    calc
      ‖c‖ = |m4| / 24 := by
        dsimp only [c]
        rw [Complex.norm_div, Complex.norm_real, Real.norm_eq_abs]
        norm_num
      _ ≤ |m4| := div_le_self (abs_nonneg _) (by norm_num)
      _ ≤ r ^ 4 * |M4| := hm4abs
      _ ≤ T * r ^ 4 := by dsimp only [T]; nlinarith [pow_nonneg hr0 4]
  have hQ : Q i u v = a + b + c - a ^ 2 / 2 := by
    dsimp only [Q, a, b, c, m3, m4, L]
    push_cast
    ring
  have hfinite : ‖Complex.logTaylor 3 (a + b + c) - Q i u v‖ ≤ H * r ^ 5 := by
    rw [hQ]
    exact complex_log_taylor_quartic_correction_bound
      a b c r (1 / 2) B T hr0 hr1 (by norm_num) hB hT ha hb hc
  have hlog0 :
      ‖Complex.log (Phi i u v) -
        Complex.logTaylor 3 ((∑ j ∈ Finset.range 5,
          (Complex.I ^ j / (j.factorial : ℂ)) *
            ((∫ y, L y ^ j ∂law i : ℝ) : ℂ)) - 1)‖ ≤
        2 * (K2 * (u ^ 2 + v ^ 2)) ^ 3 / 3 + 3 * K5 * r ^ 5 := by
    simpa only [Nat.reduceAdd, Nat.cast_ofNat] using ((hlog i u v hrad).2.2 2)
  rw [hP] at hlog0
  have hbig : 2 * (K2 * (u ^ 2 + v ^ 2)) ^ 3 / 3 ≤ 2 * K2 ^ 3 * r ^ 5 := by
    calc
      _ ≤ 2 * (K2 * (u ^ 2 + v ^ 2)) ^ 3 :=
        div_le_self (by positivity) (by norm_num)
      _ = 2 * K2 ^ 3 * r ^ 6 := by rw [← hr2]; ring
      _ ≤ 2 * K2 ^ 3 * r ^ 5 :=
        mul_le_mul_of_nonneg_left hr65 (by positivity)
  have hlogSmall : ‖Complex.log (Phi i u v) - Complex.logTaylor 3 (a + b + c)‖ ≤
      (2 * K2 ^ 3 + 3 * K5) * r ^ 5 := by
    calc
      _ ≤ 2 * (K2 * (u ^ 2 + v ^ 2)) ^ 3 / 3 + 3 * K5 * r ^ 5 := hlog0
      _ ≤ 2 * K2 ^ 3 * r ^ 5 + 3 * K5 * r ^ 5 :=
        add_le_add hbig (le_refl _)
      _ = (2 * K2 ^ 3 + 3 * K5) * r ^ 5 := by ring
  have hsplit : Complex.log (Phi i u v) - Q i u v =
      (Complex.log (Phi i u v) - Complex.logTaylor 3 (a + b + c)) +
        (Complex.logTaylor 3 (a + b + c) - Q i u v) := by ring
  calc
    ‖Complex.log (Phi i u v) - Q i u v‖ ≤
        ‖Complex.log (Phi i u v) - Complex.logTaylor 3 (a + b + c)‖ +
          ‖Complex.logTaylor 3 (a + b + c) - Q i u v‖ := by
      rw [hsplit]
      exact norm_add_le _ _
    _ ≤ (2 * K2 ^ 3 + 3 * K5) * r ^ 5 + H * r ^ 5 :=
      add_le_add hlogSmall hfinite
    _ ≤ Ctot * r ^ 5 := by
      dsimp only [Ctot]
      nlinarith [pow_nonneg hr0 5]

end
end Shao.OQ3
