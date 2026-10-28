import Shao.OQ3.SixOrderHigherWeightGrowth
import Shao.OQ3.DirectionalCGFCumulantContinuity
import Shao.OQ3.GaussianRadialPowerIntegrability
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

set_option maxHeartbeats 2000000 in
theorem uniform_actual_cgf_higher_weight_gaussian_integral_bound
    {ι : Type*} (law : ι → Measure (Fin 2 → ℝ))
    (hprob : ∀ i : ι, IsProbabilityMeasure (law i))
    (h0 : ∀ i : ι, ∀ u v : ℝ, 0 ∈ interior (ProbabilityTheory.integrableExpSet
      (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) (law i)))
    (hM : ∀ i : ι, ∀ k : ℕ, Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ k) (law i))
    (B : Fin 6 → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hbound : ∀ j : Fin 6, ∀ i : ι, ∀ u v : ℝ,
      |iteratedDeriv (j.val + 3) (ProbabilityTheory.cgf
        (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) (law i)) 0| ≤
          B j * Real.sqrt (u ^ 2 + v ^ 2) ^ (j.val + 3)) :
    let X : ι → (ℝ × ℝ) → (Fin 2 → ℝ) → ℝ :=
      fun i z y => z.1 * y 0 + z.2 * y 1
    let kappa : ι → ℕ → (ℝ × ℝ) → ℝ :=
      fun i j z => iteratedDeriv j (ProbabilityTheory.cgf (X i z) (law i)) 0
    let a : ι → ℕ → (ℝ × ℝ) → Fin 6 → ℂ := fun i n z j =>
      (Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
        (kappa i (j.val + 3) z : ℂ) / (Real.sqrt (n : ℝ) : ℂ) ^ (j.val + 1)
    let Rn : ι → ℕ → (ℝ × ℝ) → ℂ := fun i n z =>
      Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2) *
        ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
          ∑ sigma : Fin q.val → Fin 6,
            if 2 ≤ (∑ l, ((sigma l).val + 1)) ∧
              (∑ l, ((sigma l).val + 1)) ≤ 6 then ∏ l, a i n z (sigma l) else 0
    let kernel : (ℝ × ℝ) → (ℝ × ℝ) → ℂ := fun x z =>
      Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ))
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ i : ι,
      Continuous (Rn i n) ∧ Integrable (Rn i n) ∧
        Integrable (fun z : ℝ × ℝ => ‖Rn i n z‖) ∧
        (∫ z : ℝ × ℝ, ‖Rn i n z‖) ≤ C / (n : ℝ) ∧
        ∀ x : ℝ × ℝ,
          Integrable (fun z : ℝ × ℝ => kernel x z * Rn i n z) ∧
            ‖∫ z : ℝ × ℝ, kernel x z * Rn i n z‖ ≤ C / (n : ℝ) := by
  classical
  intro X kappa a Rn kernel
  obtain ⟨K, hK, hGrowth⟩ := complex_six_order_higher_weight_growth_bound B hB
  let envelope : (ℝ × ℝ) → ℝ := fun z =>
    (1 + Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 18) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)
  have hpoint (n : ℕ) (hn : 1 ≤ n) (i : ι) (z : ℝ × ℝ) :
      ‖Rn i n z‖ ≤ (K / (n : ℝ)) * envelope z := by
    let sn : ℝ := Real.sqrt (n : ℝ)
    let tau : ℝ := 1 / sn
    let r : ℝ := Real.sqrt (z.1 ^ 2 + z.2 ^ 2)
    have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnp : 0 < (n : ℝ) := by linarith
    have hsn : 0 < sn := Real.sqrt_pos.mpr hnp
    have hsn1 : 1 ≤ sn := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hnR1
    have ht0 : 0 ≤ tau := one_div_nonneg.mpr hsn.le
    have ht1 : tau ≤ 1 := (div_le_one hsn).mpr hsn1
    have hr : 0 ≤ r := Real.sqrt_nonneg _
    have hcoeff (j : Fin 6) :
        ‖(Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
          (kappa i (j.val + 3) z : ℂ)‖ ≤ B j * r ^ (j.val + 3) := by
      have hfac : (1 : ℝ) ≤ ((j.val + 3).factorial : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (j.val + 3))
      calc
        _ = |kappa i (j.val + 3) z| / ((j.val + 3).factorial : ℝ) := by
          norm_num [norm_mul, norm_div, norm_pow] <;> ring
        _ ≤ |kappa i (j.val + 3) z| := div_le_self (abs_nonneg _) hfac
        _ ≤ _ := hbound j i z.1 z.2
    have ha (j : Fin 6) :
        ‖a i n z j‖ ≤ B j * tau ^ (j.val + 1) * r ^ (j.val + 3) := by
      calc
        _ = ‖(Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
            (kappa i (j.val + 3) z : ℂ)‖ / sn ^ (j.val + 1) := by
          dsimp only [a]
          rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        _ ≤ (B j * r ^ (j.val + 3)) / sn ^ (j.val + 1) :=
          div_le_div_of_nonneg_right (hcoeff j) (pow_nonneg hsn.le _)
        _ = _ := by dsimp only [tau]; rw [_root_.one_div_pow]; ring
    have hTail : ‖∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
        ∑ sigma : Fin q.val → Fin 6,
          if 2 ≤ (∑ l, ((sigma l).val + 1)) ∧ (∑ l, ((sigma l).val + 1)) ≤ 6
            then ∏ l, a i n z (sigma l) else 0‖ ≤ K * tau ^ 2 * (1 + r ^ 18) :=
      hGrowth tau r ht0 ht1 hr (a i n z) ha
    have htau2 : tau ^ 2 = 1 / (n : ℝ) := by
      dsimp only [tau, sn]
      rw [_root_.one_div_pow, Real.sq_sqrt hnp.le]
    have hg : ‖Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)‖ =
        Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) := by
      rw [Complex.norm_exp]
      congr 1
      norm_num [Complex.div_re, pow_two, Complex.mul_re] <;> ring
    calc
      ‖Rn i n z‖ = Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) *
          ‖∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
            ∑ sigma : Fin q.val → Fin 6,
              if 2 ≤ (∑ l, ((sigma l).val + 1)) ∧ (∑ l, ((sigma l).val + 1)) ≤ 6
                then ∏ l, a i n z (sigma l) else 0‖ := by
        dsimp only [Rn]
        rw [norm_mul, hg]
      _ ≤ Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) * (K * tau ^ 2 * (1 + r ^ 18)) :=
        mul_le_mul_of_nonneg_left hTail (Real.exp_pos _).le
      _ = (K / (n : ℝ)) * envelope z := by
        rw [htau2]
        dsimp only [envelope, r]
        ring
  have hcont (i : ι) (n : ℕ) : Continuous (Rn i n) := by
    letI : IsProbabilityMeasure (law i) := hprob i
    have hk (j : ℕ) : Continuous (kappa i j) :=
      continuous_directional_actual_cgf_cumulants (law i) (h0 i) (hM i) j
    have ha (j : Fin 6) : Continuous (fun z : ℝ × ℝ => a i n z j) := by
      dsimp only [a]
      exact (continuous_const.mul (Complex.continuous_ofReal.comp (hk (j.val + 3)))).div_const _
    dsimp only [Rn]
    apply Continuous.mul (by fun_prop)
    apply continuous_finsetSum
    intro q hq
    apply continuous_const.mul
    apply continuous_finsetSum
    intro sigma hsigma
    by_cases h : 2 ≤ (∑ l, ((sigma l).val + 1)) ∧ (∑ l, ((sigma l).val + 1)) ≤ 6
    · simp only [if_pos h]
      exact continuous_finsetProd _ (fun l hl => ha (sigma l))
    · simp only [if_neg h]
      exact continuous_const
  have hEnv : Integrable envelope := by
    have h0G := integrable_euclidean_radius_power_gaussian 0 (1 / 2) (by norm_num)
    have h18 := integrable_euclidean_radius_power_gaussian 18 (1 / 2) (by norm_num)
    apply (h0G.add h18).congr
    exact Filter.Eventually.of_forall (fun z => by
      change Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 0 *
        Real.exp (-(1 / 2) * (z.1 ^ 2 + z.2 ^ 2)) +
          Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 18 *
            Real.exp (-(1 / 2) * (z.1 ^ 2 + z.2 ^ 2)) = envelope z
      dsimp only [envelope]
      rw [show -(1 / 2 : ℝ) * (z.1 ^ 2 + z.2 ^ 2) =
        -(z.1 ^ 2 + z.2 ^ 2) / 2 by ring]
      ring)
  let L : ℝ := ∫ z : ℝ × ℝ, envelope z
  have hL : 0 ≤ L := integral_nonneg (fun z => by dsimp only [envelope]; positivity)
  refine ⟨K * (L + 1), by positivity, ?_⟩
  intro n hn i
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn)
  have hKn : 0 ≤ K / (n : ℝ) := div_nonneg hK.le hnp.le
  have hi : Integrable (Rn i n) := by
    apply (hEnv.const_mul (K / (n : ℝ))).mono' (hcont i n).aestronglyMeasurable
    exact Filter.Eventually.of_forall (hpoint n hn i)
  have hIntegral : (∫ z : ℝ × ℝ, ‖Rn i n z‖) ≤ (K * (L + 1)) / (n : ℝ) := by
    calc
      _ ≤ ∫ z : ℝ × ℝ, (K / (n : ℝ)) * envelope z :=
        integral_mono hi.norm (hEnv.const_mul (K / (n : ℝ))) (hpoint n hn i)
      _ = (K / (n : ℝ)) * L := integral_const_mul _ _
      _ ≤ (K / (n : ℝ)) * (L + 1) := mul_le_mul_of_nonneg_left (by linarith) hKn
      _ = _ := by ring
  refine ⟨hcont i n, hi, hi.norm, hIntegral, ?_⟩
  intro x
  have hkernel : Continuous (kernel x) := by dsimp only [kernel]; fun_prop
  have hknorm (z : ℝ × ℝ) : ‖kernel x z‖ = 1 := by
    simp [kernel, Complex.norm_exp, Complex.mul_re]
  have hnorm (z : ℝ × ℝ) : ‖kernel x z * Rn i n z‖ = ‖Rn i n z‖ := by
    rw [norm_mul, hknorm, one_mul]
  have hki : Integrable (fun z : ℝ × ℝ => kernel x z * Rn i n z) := by
    apply hi.norm.mono' (hkernel.mul (hcont i n)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => (hnorm z).le)
  refine ⟨hki, ?_⟩
  calc
    _ ≤ ∫ z : ℝ × ℝ, ‖kernel x z * Rn i n z‖ := norm_integral_le_integral_norm _
    _ = ∫ z : ℝ × ℝ, ‖Rn i n z‖ := integral_congr_ae (Filter.Eventually.of_forall hnorm)
    _ ≤ _ := hIntegral

end
end Shao.OQ3
