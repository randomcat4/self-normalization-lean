import Shao.OQ3.StandardizedPairQuarticExponentialError
import Shao.OQ3.PairMomentEdgeworthExponentialError

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem uniform_standardized_pair_edgeworth_polynomial_error
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
    let m3 : ι → ℝ → ℝ → ℝ := fun i u v =>
      ∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 3 ∂law i
    let m4 : ι → ℝ → ℝ → ℝ := fun i u v =>
      ∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 4 ∂law i
    let Pn : ι → ℕ → ℝ → ℝ → ℂ := fun i n u v =>
      Complex.exp (-((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2) *
        (1 - Complex.I * (m3 i u v : ℂ) / (6 * (Real.sqrt (n : ℝ) : ℂ)) +
          ((((m4 i u v - 3 * (u ^ 2 + v ^ 2) ^ 2) / 24 -
            (m3 i u v) ^ 2 / 72 : ℝ) : ℂ) / (n : ℂ)))
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ i, ∀ u v : ℝ,
        Real.sqrt (u ^ 2 + v ^ 2) ≤ delta * Real.sqrt (n : ℝ) →
        ‖Phi i (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ n‖ ≤
            Real.exp (-(u ^ 2 + v ^ 2) / 4) ∧
          ‖Phi i (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ n - Pn i n u v‖ ≤
            C * (Real.sqrt (u ^ 2 + v ^ 2) ^ 5 + Real.sqrt (u ^ 2 + v ^ 2) ^ 7 +
              Real.sqrt (u ^ 2 + v ^ 2) ^ 8 + Real.sqrt (u ^ 2 + v ^ 2) ^ 9) /
              ((n : ℝ) * Real.sqrt (n : ℝ)) * Real.exp (-(u ^ 2 + v ^ 2) / 8) := by
  intro Phi m3 m4 Pn
  obtain ⟨CD, dD, hCD, hdD, hdD1, hD⟩ :=
    uniform_standardized_pair_quartic_exponential_error law hprob hL2 hmean hcov
      M3 M4 M5 hI3 hM3 hI4 hM4 hI5 hM5
  obtain ⟨CE, dE, hCE, hdE, hdE1, hE⟩ :=
    uniform_pair_moment_edgeworth_exponential_error law M3 M4 hI3 hM3 hI4 hM4
  refine ⟨CD + CE, min dD dE, add_pos hCD hCE, lt_min hdD hdE,
    (min_le_left _ _).trans hdD1, ?_⟩
  intro n hn i u v huv
  have hDuv := hD n hn i u v (huv.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)))
  have hEuv := hE n hn i u v (huv.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)))
  refine ⟨hDuv.1, ?_⟩
  let r : ℝ := Real.sqrt (u ^ 2 + v ^ 2)
  let s : ℝ := Real.sqrt (n : ℝ)
  let G : ℝ := Real.exp (-(u ^ 2 + v ^ 2) / 8)
  let Qn : ℂ := -((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2 -
    Complex.I * (m3 i u v : ℂ) / (6 * (s : ℂ)) +
      ((m4 i u v - 3 * (u ^ 2 + v ^ 2) ^ 2 : ℝ) : ℂ) / (24 * (n : ℂ))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hs : 0 < s := Real.sqrt_pos.2 hn0
  have hden : 0 < (n : ℝ) * s := mul_pos hn0 hs
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hpoly : CD * r ^ 5 + CE * (r ^ 7 + r ^ 8 + r ^ 9) ≤
      (CD + CE) * (r ^ 5 + r ^ 7 + r ^ 8 + r ^ 9) := by
    nlinarith only [mul_nonneg hCD.le (by positivity : 0 ≤ r ^ 7 + r ^ 8 + r ^ 9),
      mul_nonneg hCE.le (pow_nonneg hr 5)]
  calc
    _ = ‖(Phi i (u / s) (v / s) ^ n - Complex.exp Qn) +
        (Complex.exp Qn - Pn i n u v)‖ := by congr 1; ring
    _ ≤ ‖Phi i (u / s) (v / s) ^ n - Complex.exp Qn‖ +
        ‖Complex.exp Qn - Pn i n u v‖ := norm_add_le _ _
    _ ≤ CD * r ^ 5 / ((n : ℝ) * s) * G +
        CE * (r ^ 7 + r ^ 8 + r ^ 9) / ((n : ℝ) * s) * G :=
      add_le_add hDuv.2 hEuv
    _ = (CD * r ^ 5 + CE * (r ^ 7 + r ^ 8 + r ^ 9)) / ((n : ℝ) * s) * G := by ring
    _ ≤ (CD + CE) * (r ^ 5 + r ^ 7 + r ^ 8 + r ^ 9) / ((n : ℝ) * s) * G :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpoly hden.le) (Real.exp_pos _).le
    _ = _ := rfl

end
end Shao.OQ3
