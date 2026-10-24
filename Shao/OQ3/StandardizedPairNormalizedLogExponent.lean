import Shao.OQ3.StandardizedPairQuarticLogRemainder
import Shao.OQ3.StandardizedPairLogMomentApproximation
import Shao.OQ3.PairDirectionalMomentScaling

namespace Shao.OQ3

open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

theorem uniform_standardized_pair_normalized_log_exponent
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
    let Qn : ι → ℕ → ℝ → ℝ → ℂ := fun i n u v =>
      -((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2 -
        Complex.I * ((∫ y : Fin 2 → ℝ,
          (u * y 0 + v * y 1) ^ 3 ∂law i : ℝ) : ℂ) /
          (6 * (Real.sqrt (n : ℝ) : ℂ)) +
        (((∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 4 ∂law i : ℝ) -
          3 * (u ^ 2 + v ^ 2) ^ 2 : ℝ) : ℂ) / (24 * (n : ℂ))
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ i, ∀ u v : ℝ,
        Real.sqrt (u ^ 2 + v ^ 2) ≤ delta * Real.sqrt (n : ℝ) →
        Phi i (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ≠ 0 ∧
        ‖(n : ℂ) *
            Complex.log (Phi i (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ))) -
          Qn i n u v‖ ≤
          C * Real.sqrt (u ^ 2 + v ^ 2) ^ 5 / ((n : ℝ) * Real.sqrt (n : ℝ)) ∧
        Complex.exp ((n : ℂ) *
          Complex.log (Phi i (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)))) =
          Phi i (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ n := by
  intro Phi Qn
  let Q : ι → ℝ → ℝ → ℂ := fun i u v =>
    -((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2 -
      Complex.I * ((∫ y : Fin 2 → ℝ,
        (u * y 0 + v * y 1) ^ 3 ∂law i : ℝ) : ℂ) / 6 +
      (((∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 4 ∂law i : ℝ) -
        3 * (u ^ 2 + v ^ 2) ^ 2 : ℝ) : ℂ) / 24
  obtain ⟨C, d1, hC, hd1, hd1le, hrem⟩ :=
    uniform_standardized_pair_quartic_log_remainder
      law hprob hL2 hmean hcov M3 M4 M5 hI3 hM3 hI4 hM4 hI5 hM5
  obtain ⟨hK2, hK5, d0, hd0, hd0le, hsmall⟩ :=
    uniform_standardized_pair_log_moment_approximation
      law hprob hL2 hmean hcov 5 (by norm_num) M3 M5 hI3 hM3 hI5 hM5
  let delta : ℝ := min d1 d0
  have hdpos : 0 < delta := lt_min hd1 hd0
  have hdle : delta ≤ 1 := (min_le_left d1 d0).trans hd1le
  refine ⟨C, delta, hC, hdpos, hdle, ?_⟩
  intro n hn i u v hrad
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  let s : ℝ := Real.sqrt (n : ℝ)
  have hspos : 0 < s := Real.sqrt_pos.2 hnpos
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hsq : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsne
  have hnC : (n : ℂ) = (s : ℂ) ^ 2 := by exact_mod_cast hsq.symm
  let r : ℝ := Real.sqrt (u ^ 2 + v ^ 2)
  have hrscaled : Real.sqrt ((u / s) ^ 2 + (v / s) ^ 2) = r / s := by
    simpa only [r, div_eq_mul_inv, mul_comm, abs_of_pos (inv_pos.mpr hspos)] using
      euclidean_frequency_radius_scalar_mul s⁻¹ u v
  have hrdelta : r / s ≤ delta := (div_le_iff₀ hspos).2 hrad
  have hscaled1 : Real.sqrt ((u / s) ^ 2 + (v / s) ^ 2) ≤ d1 := by
    rw [hrscaled]
    exact hrdelta.trans (min_le_left d1 d0)
  have hscaled0 : Real.sqrt ((u / s) ^ 2 + (v / s) ^ 2) ≤ d0 := by
    rw [hrscaled]
    exact hrdelta.trans (min_le_right d1 d0)
  have hne : Phi i (u / s) (v / s) ≠ 0 := by
    intro hz
    have hball := (hsmall i (u / s) (v / s) hscaled0).1
    change ‖Phi i (u / s) (v / s) - 1‖ ≤ 1 / 2 at hball
    rw [hz] at hball
    norm_num at hball
  refine ⟨hne, ?_, ?_⟩
  · have hm3 :
        (∫ y : Fin 2 → ℝ, ((u / s) * y 0 + (v / s) * y 1) ^ 3 ∂law i) =
        s⁻¹ ^ 3 * (∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 3 ∂law i) := by
      simpa only [div_eq_mul_inv, mul_comm] using
        (pair_projection_moment_homogeneity (law i) 3 (hI3 i) u v s⁻¹).2.2
    have hm4 :
        (∫ y : Fin 2 → ℝ, ((u / s) * y 0 + (v / s) * y 1) ^ 4 ∂law i) =
        s⁻¹ ^ 4 * (∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 4 ∂law i) := by
      simpa only [div_eq_mul_inv, mul_comm] using
        (pair_projection_moment_homogeneity (law i) 4 (hI4 i) u v s⁻¹).2.2
    have hfreq : (u / s) ^ 2 + (v / s) ^ 2 = (u ^ 2 + v ^ 2) / s ^ 2 := by
      field_simp
      <;> ring
    have hQscale : (n : ℂ) * Q i (u / s) (v / s) = Qn i n u v := by
      change (n : ℂ) * Q i (u / s) (v / s) =
        -((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2 -
          Complex.I * ((∫ y : Fin 2 → ℝ,
            (u * y 0 + v * y 1) ^ 3 ∂law i : ℝ) : ℂ) / (6 * (s : ℂ)) +
          (((∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 4 ∂law i : ℝ) -
            3 * (u ^ 2 + v ^ 2) ^ 2 : ℝ) : ℂ) / (24 * (n : ℂ))
      dsimp only [Q]
      rw [hm3, hm4, hfreq]
      generalize h3value : (∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 3 ∂law i) = m3
      generalize h4value : (∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 4 ∂law i) = m4
      push_cast
      rw [hnC]
      field_simp [hsC]
      <;> ring
    have hlocal :
        ‖Complex.log (Phi i (u / s) (v / s)) - Q i (u / s) (v / s)‖ ≤
          C * Real.sqrt ((u / s) ^ 2 + (v / s) ^ 2) ^ 5 :=
      hrem i (u / s) (v / s) hscaled1
    have hfactor : (n : ℂ) * Complex.log (Phi i (u / s) (v / s)) - Qn i n u v =
        (n : ℂ) * (Complex.log (Phi i (u / s) (v / s)) - Q i (u / s) (v / s)) := by
      rw [← hQscale]
      ring
    change ‖(n : ℂ) * Complex.log (Phi i (u / s) (v / s)) - Qn i n u v‖ ≤
      C * r ^ 5 / ((n : ℝ) * s)
    calc
      ‖(n : ℂ) * Complex.log (Phi i (u / s) (v / s)) - Qn i n u v‖ =
          (n : ℝ) * ‖Complex.log (Phi i (u / s) (v / s)) - Q i (u / s) (v / s)‖ := by
        rw [hfactor, Complex.norm_mul, Complex.norm_natCast]
      _ ≤ (n : ℝ) * (C * Real.sqrt ((u / s) ^ 2 + (v / s) ^ 2) ^ 5) :=
        mul_le_mul_of_nonneg_left hlocal hnpos.le
      _ = C * r ^ 5 / ((n : ℝ) * s) := by
        rw [hrscaled, ← hsq]
        field_simp [hsne]
        <;> ring
  · rw [Complex.exp_nat_mul, Complex.exp_log hne]

end
end Shao.OQ3
