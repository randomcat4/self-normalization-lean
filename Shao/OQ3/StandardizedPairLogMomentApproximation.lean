import Shao.OQ3.PairCharacteristicQuadraticRemainder
import Shao.OQ3.PairCharacteristicMomentRemainder
import Shao.OQ3.ComplexLogTaylorPerturbation

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem uniform_standardized_pair_log_moment_approximation
    {ι : Type*} (law : ι → Measure (Fin 2 → ℝ))
    (hprob : ∀ i, IsProbabilityMeasure (law i))
    (hL2 : ∀ i, ∀ j : Fin 2, MemLp (fun y : Fin 2 → ℝ => y j) 2 (law i))
    (hmean : ∀ i, ∀ j : Fin 2, (∫ y : Fin 2 → ℝ, y j ∂(law i)) = 0)
    (hcov : ∀ i, ∀ j k : Fin 2, ProbabilityTheory.covariance
      (fun y : Fin 2 → ℝ => y j) (fun y : Fin 2 → ℝ => y k) (law i) =
        if j = k then 1 else 0)
    (m : ℕ) (hm : 1 ≤ m) (M3 Mm : ℝ)
    (hI3 : ∀ i, Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3) (law i))
    (hM3 : ∀ i, (∫ y : Fin 2 → ℝ,
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3 ∂(law i)) ≤ M3)
    (hIm : ∀ i, Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m) (law i))
    (hMm : ∀ i, (∫ y : Fin 2 → ℝ,
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m ∂(law i)) ≤ Mm) :
    let Phi : ι → ℝ → ℝ → ℂ := fun i u v =>
      ∫ y : Fin 2 → ℝ, Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂(law i)
    let P : ι → ℝ → ℝ → ℂ := fun i u v =>
      ∑ j ∈ Finset.range m, (Complex.I ^ j / (j.factorial : ℂ)) *
        ((∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ j ∂(law i) : ℝ) : ℂ)
    let K2 : ℝ := 2 + (Real.exp 1 + 4) * |M3|
    let Km : ℝ := 1 + (Real.exp 1 + (m : ℝ) + 1) * |Mm|
    0 < K2 ∧ 0 < Km ∧ ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ (i : ι) (u v : ℝ), Real.sqrt (u ^ 2 + v ^ 2) ≤ delta →
        ‖Phi i u v - 1‖ ≤ 1 / 2 ∧ ‖P i u v - 1‖ ≤ 1 ∧
          ∀ q : ℕ, ‖Complex.log (Phi i u v) -
              Complex.logTaylor (q + 1) (P i u v - 1)‖ ≤
            2 * (K2 * (u ^ 2 + v ^ 2)) ^ (q + 1) / ((q + 1 : ℕ) : ℝ) +
              ((q + 1 : ℕ) : ℝ) * Km * Real.sqrt (u ^ 2 + v ^ 2) ^ m := by
  intro Phi P K2 Km
  have hK2 : 0 < K2 := by dsimp [K2]; positivity
  have hKm : 0 < Km := by dsimp [Km]; positivity
  have hc3 : 0 ≤ Real.exp 1 + 4 := by positivity
  have hcm : 0 ≤ Real.exp 1 + (m : ℝ) + 1 := by positivity
  refine ⟨hK2, hKm, ?_⟩
  let delta : ℝ := min 1 (min (1 / (4 * K2)) (1 / (4 * Km)))
  have hdpos : 0 < delta := by
    dsimp [delta]
    exact lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  refine ⟨delta, hdpos, min_le_left _ _, ?_⟩
  intro i u v hr
  letI : IsProbabilityMeasure (law i) := hprob i
  let r : ℝ := Real.sqrt (u ^ 2 + v ^ 2)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r ≤ 1 := hr.trans (min_le_left _ _)
  have hrK2 : r ≤ 1 / (4 * K2) :=
    hr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrKm : r ≤ 1 / (4 * Km) :=
    hr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hK2r : K2 * r ≤ 1 / 4 := by
    have hx := (le_div_iff₀ (by positivity : 0 < 4 * K2)).1 hrK2
    nlinarith
  have hKmr : Km * r ≤ 1 / 4 := by
    have hx := (le_div_iff₀ (by positivity : 0 < 4 * Km)).1 hrKm
    nlinarith
  have hr2 : r ^ 2 = u ^ 2 + v ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg u) (sq_nonneg v))
  have hrsq : r ^ 2 ≤ r := by nlinarith
  have hr3 : r ^ 3 ≤ r ^ 2 := by
    calc
      _ = r ^ 2 * r := by ring
      _ ≤ r ^ 2 * 1 := mul_le_mul_of_nonneg_left hr1 (sq_nonneg r)
      _ = r ^ 2 := mul_one _
  have hrm : r ^ m ≤ r := by
    have hmne : m ≠ 0 := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmne
    rw [hk, pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hr0 hr1) hr0).trans_eq (one_mul r)
  let G : ℂ := 1 - ((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2
  have hq := pair_probability_characteristic_quadratic_remainder_bound
    (law i) (hL2 i) (hmean i) (hcov i) (hI3 i) u v
  have h3bound : ‖Phi i u v - G‖ ≤ (Real.exp 1 + 4) * |M3| * r ^ 3 := by
    calc
      _ ≤ (Real.exp 1 + 4) * r ^ 3 *
          (∫ y : Fin 2 → ℝ, Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3 ∂(law i)) := by
        simpa only [Phi, G, r] using hq
      _ ≤ (Real.exp 1 + 4) * r ^ 3 * |M3| :=
        mul_le_mul_of_nonneg_left ((hM3 i).trans (le_abs_self M3))
          (mul_nonneg hc3 (pow_nonneg hr0 3))
      _ = (Real.exp 1 + 4) * |M3| * r ^ 3 := by ring
  have hGnorm : ‖G - 1‖ = r ^ 2 / 2 := by
    have heq : G - 1 = -((r ^ 2 / 2 : ℝ) : ℂ) := by
      dsimp [G]
      rw [hr2]
      push_cast
      ring
    rw [heq, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (sq_nonneg r) (by norm_num))]
  have hphibound : ‖Phi i u v - 1‖ ≤ K2 * r ^ 2 := by
    calc
      _ = ‖(Phi i u v - G) + (G - 1)‖ := by congr 1; ring
      _ ≤ ‖Phi i u v - G‖ + ‖G - 1‖ := norm_add_le _ _
      _ = ‖Phi i u v - G‖ + r ^ 2 / 2 := by rw [hGnorm]
      _ ≤ (Real.exp 1 + 4) * |M3| * r ^ 3 + r ^ 2 / 2 :=
        add_le_add h3bound (le_refl (r ^ 2 / 2))
      _ ≤ (Real.exp 1 + 4) * |M3| * r ^ 2 + r ^ 2 / 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hr3 (mul_nonneg hc3 (abs_nonneg M3)))
          (le_refl (r ^ 2 / 2))
      _ ≤ K2 * r ^ 2 := by dsimp [K2]; nlinarith [sq_nonneg r]
  have hphismall : ‖Phi i u v - 1‖ ≤ 1 / 2 := by
    have hx := mul_le_mul_of_nonneg_left hrsq hK2.le
    linarith
  have hco : (Real.exp 1 + (m : ℝ) + 1) * Mm ≤ Km := by
    have hx := mul_le_mul_of_nonneg_left (le_abs_self Mm) hcm
    dsimp [Km]
    linarith
  have herr0 := uniform_pair_characteristic_moment_remainder_bound
    law hprob m Mm hIm hMm i u v
  have herr : ‖Phi i u v - P i u v‖ ≤ Km * r ^ m := by
    calc
      _ ≤ (Real.exp 1 + (m : ℝ) + 1) * Mm * r ^ m := by
        simpa only [Phi, P, r] using herr0
      _ ≤ Km * r ^ m := mul_le_mul_of_nonneg_right hco (pow_nonneg hr0 m)
  have hPsmall : ‖P i u v - 1‖ ≤ 1 := by
    calc
      _ = ‖(Phi i u v - 1) - (Phi i u v - P i u v)‖ := by congr 1; ring
      _ ≤ ‖Phi i u v - 1‖ + ‖Phi i u v - P i u v‖ := norm_sub_le _ _
      _ ≤ 1 / 2 + Km * r ^ m := add_le_add hphismall herr
      _ ≤ 1 / 2 + Km * r := add_le_add (le_refl ((1 : ℝ) / 2))
          (mul_le_mul_of_nonneg_left hrm hKm.le)
      _ ≤ 1 := by linarith
  refine ⟨hphismall, hPsmall, ?_⟩
  intro q
  have he := complex_log_taylor_perturbation_bound q
    (Phi i u v - 1) (P i u v - 1) hphismall hPsmall
  have hsum : (1 : ℂ) + (Phi i u v - 1) = Phi i u v := by ring
  have hdiff : (Phi i u v - 1) - (P i u v - 1) = Phi i u v - P i u v := by ring
  rw [hsum, hdiff] at he
  have hpow : ‖Phi i u v - 1‖ ^ (q + 1) ≤
      (K2 * (u ^ 2 + v ^ 2)) ^ (q + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) (by simpa only [hr2] using hphibound) (q + 1)
  apply he.trans
  apply add_le_add
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by norm_num)) (by positivity)
  · simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg (α := ℝ) (q + 1))

end
end Shao.OQ3

