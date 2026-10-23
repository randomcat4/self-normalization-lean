import Shao.OQ3.UniformPairCharacteristicLocalGaussian
import Shao.OQ3.PairCharacteristicGaussianRemainder

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
noncomputable section

theorem complex_power_difference_norm_bound (a b : ℂ) (d : ℝ)
    (hd : 0 ≤ d) (ha : ‖a‖ ≤ d) (hb : ‖b‖ ≤ d) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ (n : ℝ) * d ^ (n - 1) * ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ k =>
      have hidentity : a ^ (k + 1 + 1) - b ^ (k + 1 + 1) =
          (a - b) * a ^ (k + 1) + b * (a ^ (k + 1) - b ^ (k + 1)) := by
        ring
      rw [hidentity]
      calc
        ‖(a - b) * a ^ (k + 1) + b * (a ^ (k + 1) - b ^ (k + 1))‖ ≤
            ‖a - b‖ * ‖a‖ ^ (k + 1) + ‖b‖ * ‖a ^ (k + 1) - b ^ (k + 1)‖ := by
          simpa only [norm_mul, norm_pow] using
            norm_add_le ((a - b) * a ^ (k + 1))
              (b * (a ^ (k + 1) - b ^ (k + 1)))
        _ ≤ ‖a - b‖ * d ^ (k + 1) +
            d * (((k + 1 : ℕ) : ℝ) * d ^ k * ‖a - b‖) :=
          add_le_add
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (norm_nonneg _) ha (k + 1)) (norm_nonneg _))
            (mul_le_mul hb (by simpa using ih) (norm_nonneg _) hd)
        _ = ((k + 1 + 1 : ℕ) : ℝ) * d ^ (k + 1 + 1 - 1) * ‖a - b‖ := by
          simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
          ring

theorem uniform_isotropic_pair_characteristic_power_gaussian_error_bound
    {ι : Type*} (K : Set ι) (laws : ι → Measure (Fin 2 → ℝ))
    (hprob : ∀ p ∈ K, IsProbabilityMeasure (laws p))
    (hL2 : ∀ p ∈ K, ∀ i : Fin 2, MemLp (fun y : Fin 2 → ℝ => y i) 2 (laws p))
    (hmean : ∀ p ∈ K, ∀ i : Fin 2, (∫ y : Fin 2 → ℝ, y i ∂laws p) = 0)
    (hcov : ∀ p ∈ K, ∀ i j : Fin 2, ProbabilityTheory.covariance
      (fun y : Fin 2 → ℝ => y i) (fun y : Fin 2 → ℝ => y j) (laws p) =
        if i = j then 1 else 0)
    (hthird : ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K,
      Integrable (fun y : Fin 2 → ℝ =>
        (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 3) (laws p) ∧
      (∫ y : Fin 2 → ℝ,
        (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 3 ∂laws p) ≤ C) :
    ∃ delta B : ℝ, 0 < delta ∧ delta ≤ 1 ∧ 0 < B ∧
      ∀ n : ℕ, 2 ≤ n → ∀ p ∈ K, ∀ u v : ℝ,
        Real.sqrt ((u / Real.sqrt (n : ℝ)) ^ 2 +
          (v / Real.sqrt (n : ℝ)) ^ 2) ≤ delta →
        ‖(∫ y : Fin 2 → ℝ,
          Complex.exp ((((u / Real.sqrt (n : ℝ)) * y 0 +
            (v / Real.sqrt (n : ℝ)) * y 1 : ℝ) : ℂ) * Complex.I) ∂laws p) ^ n -
              ((Real.exp (-(u ^ 2 + v ^ 2) / 2) : ℝ) : ℂ)‖ ≤
          B * (n : ℝ) *
            (Real.sqrt ((u / Real.sqrt (n : ℝ)) ^ 2 +
              (v / Real.sqrt (n : ℝ)) ^ 2)) ^ 3 *
                Real.exp (-(u ^ 2 + v ^ 2) / 8) := by
  obtain ⟨delta, hdelta0, hdelta1, hlocal⟩ :=
    uniform_isotropic_pair_characteristic_local_gaussian_bound
      K laws hprob hL2 hmean hcov hthird
  obtain ⟨C, hC, hthird⟩ := hthird
  let B : ℝ := (Real.exp 1 + 4) * C + Real.exp 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨delta, B, hdelta0, hdelta1, hB, ?_⟩
  intro n hn p hp u v hsmall
  letI : IsProbabilityMeasure (laws p) := hprob p hp
  let q : ℝ := (u / Real.sqrt (n : ℝ)) ^ 2 + (v / Real.sqrt (n : ℝ)) ^ 2
  let r : ℝ := Real.sqrt q
  let a : ℂ := ∫ y : Fin 2 → ℝ,
    Complex.exp ((((u / Real.sqrt (n : ℝ)) * y 0 +
      (v / Real.sqrt (n : ℝ)) * y 1 : ℝ) : ℂ) * Complex.I) ∂laws p
  let b : ℂ := ((Real.exp (-q / 2) : ℝ) : ℂ)
  let d : ℝ := Real.exp (-q / 4)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hd : 0 ≤ d := (Real.exp_pos _).le
  have ha : ‖a‖ ≤ d :=
    hlocal p hp (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) hsmall
  have hb : ‖b‖ ≤ d := by
    dsimp [b, d]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by linarith)
  have herror : ‖a - b‖ ≤ B * r ^ 3 := by
    have hraw := pair_probability_characteristic_gaussian_remainder_bound
      (laws p) (hL2 p hp) (hmean p hp) (hcov p hp) (hthird p hp).1
        (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ))
          (hsmall.trans hdelta1)
    have hcoef : (Real.exp 1 + 4) *
        (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 3 ∂laws p) +
          Real.exp 1 ≤ B :=
      add_le_add (mul_le_mul_of_nonneg_left (hthird p hp).2
        (show 0 ≤ Real.exp 1 + 4 by positivity)) le_rfl
    exact hraw.trans (mul_le_mul_of_nonneg_right hcoef (pow_nonneg hr0 3))
  have hnR : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hn1 : 1 ≤ n := by omega
  have hsqrt : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hnpos.le
  have hscale : (n : ℝ) * q = u ^ 2 + v ^ 2 := by
    dsimp [q]
    rw [div_pow, div_pow, hsqrt]
    field_simp [ne_of_gt hnpos]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1]
    norm_num
  have hdamp : d ^ (n - 1) ≤ Real.exp (-(u ^ 2 + v ^ 2) / 8) := by
    dsimp [d]
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rw [hcast]
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) hq0, hscale]
  have hbpow : b ^ n = ((Real.exp (-(u ^ 2 + v ^ 2) / 2) : ℝ) : ℂ) := by
    dsimp [b]
    norm_cast
    rw [← Real.exp_nat_mul]
    congr 1
    nlinarith [hscale]
  change ‖a ^ n - ((Real.exp (-(u ^ 2 + v ^ 2) / 2) : ℝ) : ℂ)‖ ≤
    B * (n : ℝ) * r ^ 3 * Real.exp (-(u ^ 2 + v ^ 2) / 8)
  rw [← hbpow]
  calc
    ‖a ^ n - b ^ n‖ ≤ (n : ℝ) * d ^ (n - 1) * ‖a - b‖ :=
      complex_power_difference_norm_bound a b d hd ha hb n
    _ ≤ (n : ℝ) * Real.exp (-(u ^ 2 + v ^ 2) / 8) * (B * r ^ 3) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hdamp (Nat.cast_nonneg n))
        herror (norm_nonneg _) (by positivity)
    _ = B * (n : ℝ) * r ^ 3 * Real.exp (-(u ^ 2 + v ^ 2) / 8) := by ring

end
end Shao.OQ3
