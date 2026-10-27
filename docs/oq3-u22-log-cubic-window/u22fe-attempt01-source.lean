import Shao.OQ3.ComplexSixOrderPolynomialGrowth
import Shao.OQ3.DirectionalCGFCumulantContinuity
import Shao.OQ3.EuclideanGaussianWeightedTail

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

set_option maxHeartbeats 1000000 in
theorem uniform_actual_cgf_six_order_gaussian_polynomial_bound
    {ι : Type*} (law : ι → Measure (Fin 2 → ℝ))
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
    let Pn : ι → ℕ → (ℝ × ℝ) → ℂ := fun i n z =>
      Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2) *
        ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
          ∑ sigma : Fin q.val → Fin 6,
            if (∑ l, ((sigma l).val + 1)) ≤ 6 then ∏ l, a i n z (sigma l) else 0
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ i : ι, ∀ u v : ℝ,
      ‖Pn i n (u, v)‖ ≤ C * (1 + Real.sqrt (u ^ 2 + v ^ 2) ^ 18) *
        Real.exp (-(u ^ 2 + v ^ 2) / 2) := by
  intro X kappa a Pn
  obtain ⟨C, hC, hP⟩ := complex_six_order_filtered_polynomial_growth_bound B hB
  refine ⟨C, hC, ?_⟩
  intro n hn i u v
  let sn : ℝ := Real.sqrt (n : ℝ)
  let tau : ℝ := 1 / sn
  let r : ℝ := Real.sqrt (u ^ 2 + v ^ 2)
  let P0 : (Fin 6 → ℂ) → ℂ := fun b =>
    ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
      ∑ sigma : Fin q.val → Fin 6,
        if (∑ l, ((sigma l).val + 1)) ≤ 6 then ∏ l, b (sigma l) else 0
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsn : 0 < sn := Real.sqrt_pos.mpr (by linarith)
  have hsn1 : 1 ≤ sn := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hnR1
  have ht0 : 0 ≤ tau := one_div_nonneg.mpr hsn.le
  have ht1 : tau ≤ 1 := (div_le_one hsn).mpr hsn1
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hcoeff (j : Fin 6) :
      ‖(Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
        (kappa i (j.val + 3) (u, v) : ℂ)‖ ≤ B j * r ^ (j.val + 3) := by
    have hfac : (1 : ℝ) ≤ ((j.val + 3).factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (j.val + 3))
    calc
      _ = |kappa i (j.val + 3) (u, v)| / ((j.val + 3).factorial : ℝ) := by
        norm_num [norm_mul, norm_div, norm_pow] <;> ring
      _ ≤ |kappa i (j.val + 3) (u, v)| := div_le_self (abs_nonneg _) hfac
      _ ≤ _ := hbound j i u v
  have ha (j : Fin 6) :
      ‖a i n (u, v) j‖ ≤ B j * tau ^ (j.val + 1) * r ^ (j.val + 3) := by
    calc
      _ = ‖(Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
          (kappa i (j.val + 3) (u, v) : ℂ)‖ / sn ^ (j.val + 1) := by
        dsimp only [a]
        rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ (B j * r ^ (j.val + 3)) / sn ^ (j.val + 1) :=
        div_le_div_of_nonneg_right (hcoeff j) (pow_nonneg hsn.le _)
      _ = _ := by dsimp only [tau]; rw [_root_.one_div_pow]; ring
  have hp : ‖P0 (a i n (u, v))‖ ≤ C * (1 + r ^ 18) :=
    hP tau r ht0 ht1 hr (a i n (u, v)) ha
  have hg : ‖Complex.exp (-((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2)‖ =
      Real.exp (-(u ^ 2 + v ^ 2) / 2) := by
    rw [Complex.norm_exp]
    congr 1
    norm_num [Complex.div_re] <;> ring
  calc
    ‖Pn i n (u, v)‖ = Real.exp (-(u ^ 2 + v ^ 2) / 2) * ‖P0 (a i n (u, v))‖ := by
      change ‖Complex.exp (-((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2) * P0 (a i n (u, v))‖ = _
      rw [norm_mul, hg]
    _ ≤ Real.exp (-(u ^ 2 + v ^ 2) / 2) * (C * (1 + r ^ 18)) :=
      mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ = C * (1 + Real.sqrt (u ^ 2 + v ^ 2) ^ 18) *
        Real.exp (-(u ^ 2 + v ^ 2) / 2) := by ring

set_option maxHeartbeats 1000000 in
theorem uniform_actual_cgf_six_order_gaussian_polynomial_tail
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
    let Pn : ι → ℕ → (ℝ × ℝ) → ℂ := fun i n z =>
      Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2) *
        ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
          ∑ sigma : Fin q.val → Fin 6,
            if (∑ l, ((sigma l).val + 1)) ≤ 6 then ∏ l, a i n z (sigma l) else 0
    ∀ delta : ℝ, 0 < delta → ∀ k : ℕ, ∀ q epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ i : ι,
        let tail : Set (ℝ × ℝ) := {z |
          delta * Real.sqrt (n : ℝ) ≤ Real.sqrt (z.1 ^ 2 + z.2 ^ 2)}
        let f : (ℝ × ℝ) → ℝ := fun z =>
          Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ k * ‖Pn i n z‖
        IntegrableOn f tail ∧ 0 ≤ (∫ z in tail, f z) ∧
          Real.rpow (n : ℝ) q * (∫ z in tail, f z) < epsilon := by
  intro X kappa a Pn
  obtain ⟨C, hC, hP⟩ := uniform_actual_cgf_six_order_gaussian_polynomial_bound law B hB hbound
  have hcont (i : ι) (n : ℕ) : Continuous (Pn i n) := by
    letI : IsProbabilityMeasure (law i) := hprob i
    exact continuous_actual_cgf_six_order_edgeworth_polynomial (law i) (h0 i) (hM i) n
  let g : ℕ → (ℝ × ℝ) → ℝ := fun j z =>
    Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ j * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)
  intro delta hdelta k q epsilon hepsilon
  let eps : ℝ := epsilon / (2 * C)
  have heps : 0 < eps := div_pos hepsilon (mul_pos (by norm_num) hC)
  obtain ⟨N1, hN1, hT1⟩ := eventually_scaled_euclidean_gaussian_weighted_tail
    k delta q eps hdelta heps
  obtain ⟨N2, hN2, hT2⟩ := eventually_scaled_euclidean_gaussian_weighted_tail
    (k + 18) delta q eps hdelta heps
  refine ⟨max N1 N2, hN1.trans (le_max_left _ _), ?_⟩
  intro n hn i tail f
  have hn1 : N1 ≤ n := (le_max_left N1 N2).trans hn
  have hn2 : N2 ≤ n := (le_max_right N1 N2).trans hn
  have hnpos : 1 ≤ n := hN1.trans hn1
  have ht1 := hT1 n hn1
  have ht2 := hT2 n hn2
  have hg1 : IntegrableOn (g k) tail := ht1.1
  have hg2 : IntegrableOn (g (k + 18)) tail := ht2.1
  have hG : IntegrableOn (fun z => C * (g k z + g (k + 18) z)) tail := by
    apply ((hg1.add hg2).const_mul C).congr
    filter_upwards [] with z
    rfl
  have hnonneg (z : ℝ × ℝ) : 0 ≤ f z :=
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) k) (norm_nonneg _)
  have hfc : Continuous f :=
    (show Continuous (fun z : ℝ × ℝ => Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ k) by
      fun_prop).mul (hcont i n).norm
  have hGF (z : ℝ × ℝ) : f z ≤ C * (g k z + g (k + 18) z) := by
    have h := mul_le_mul_of_nonneg_left (hP n hnpos i z.1 z.2)
      (pow_nonneg (Real.sqrt_nonneg (z.1 ^ 2 + z.2 ^ 2)) k)
    calc
      f z ≤ Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ k *
          (C * (1 + Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 18) *
            Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)) := h
      _ = C * (g k z + g (k + 18) z) := by
        dsimp [g]
        rw [pow_add]
        ring
  have hfi : IntegrableOn f tail := by
    apply hG.mono' hfc.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg z)]
      exact hGF z)
  have htail : MeasurableSet tail :=
    (isClosed_le continuous_const (by fun_prop)).measurableSet
  have hI : (∫ z in tail, f z) ≤
      C * ((∫ z in tail, g k z) + (∫ z in tail, g (k + 18) z)) := by
    calc
      _ ≤ ∫ z in tail, C * (g k z + g (k + 18) z) :=
        setIntegral_mono_on hfi hG htail (fun z hz => hGF z)
      _ = _ := by rw [integral_const_mul, integral_add hg1 hg2]
  refine ⟨hfi, integral_nonneg hnonneg, ?_⟩
  calc
    Real.rpow (n : ℝ) q * (∫ z in tail, f z) ≤
        Real.rpow (n : ℝ) q *
          (C * ((∫ z in tail, g k z) + (∫ z in tail, g (k + 18) z))) :=
      mul_le_mul_of_nonneg_left hI (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = C * (Real.rpow (n : ℝ) q * (∫ z in tail, g k z) +
        Real.rpow (n : ℝ) q * (∫ z in tail, g (k + 18) z)) := by ring
    _ < C * (eps + eps) := mul_lt_mul_of_pos_left (add_lt_add ht1.2.2 ht2.2.2) hC
    _ = epsilon := by dsimp [eps]; field_simp [hC.ne']; ring

end
end Shao.OQ3
