import Shao.Probability.RetainedMoments
import Mathlib.Analysis.Real.Sqrt

/-!
# Genuine retained third moment and raw retained-row bounds

The cutoff law and mass are the existing actual conditional measure and its
normalizer. The source input remains `n * integral F(xz) ≤ 1`. The second
moments below are raw second moments, not centered variances.
-/

set_option autoImplicit false

namespace Shao

open MeasureTheory

private theorem retained_abs_cube_integrable_restrict (ν : Measure ℝ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (x : ℝ) (hx : 0 < x) :
    Integrable (fun z : ℝ => |z| ^ 3) (ν.restrict (retainedCutoffSet x)) := by
  apply (integrable_truncation_small_three ν h2 x hx).restrict.congr
  filter_upwards [ae_restrict_mem (measurableSet_retainedCutoffSet x)] with z hz
  have hz' : |z| ≤ 1 / x := hz
  exact ite_eq_left hz'

private theorem integral_retained_abs_cube (ν : Measure ℝ) (x : ℝ) :
    (∫ z : ℝ in retainedCutoffSet x, |z| ^ 3 ∂ν) =
      ∫ z : ℝ, if |z| ≤ 1 / x then |z| ^ 3 else 0 ∂ν := by
  rw [← integral_indicator (measurableSet_retainedCutoffSet x)]
  rfl

theorem integrable_retainedCutoffLaw_abs_cube
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (x : ℝ) (hx : 0 < x) (hq : 0 < retainedCutoffMass ν x)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    Integrable (fun z : ℝ => |z| ^ 3) (retainedCutoffLaw ν x) :=
  integrable_retainedCutoffLaw ν x hq _ (retained_abs_cube_integrable_restrict ν h2 x hx)

theorem retainedCutoffLaw_third_moment_bound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 < x)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hcut : (n : ℝ) * (∫ z : ℝ, truncationF (x * z) ∂ν) ≤ 1) :
    (n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂retainedCutoffLaw ν x) ≤ 2 / x ^ 3 := by
  obtain ⟨_, hqhalf, _⟩ := retainedCutoffMass_bounds ν n hn x hx h2 hcut
  have hq : 0 < retainedCutoffMass ν x := by linarith
  have hrestricted := retained_abs_cube_integrable_restrict ν h2 x hx
  have hraw := mul_le_mul_of_nonneg_left (integral_truncation_small_three_le ν h2 x hx)
    (Nat.cast_nonneg n)
  rw [← integral_retained_abs_cube ν x] at hraw
  have hnum : (n : ℝ) * (∫ z : ℝ in retainedCutoffSet x, |z| ^ 3 ∂ν) ≤ 1 / x ^ 3 :=
    (le_div_iff₀ (pow_pos hx 3)).mpr (by nlinarith only [hraw, hcut])
  calc
    _ = ((n : ℝ) * (∫ z : ℝ in retainedCutoffSet x, |z| ^ 3 ∂ν)) /
        retainedCutoffMass ν x := by
      rw [integral_retainedCutoffLaw ν x hq _ hrestricted]
      ring
    _ ≤ (1 / x ^ 3) / retainedCutoffMass ν x :=
      div_le_div_of_nonneg_right hnum hq.le
    _ ≤ 2 / x ^ 3 := by
      apply (div_le_iff₀ hq).mpr
      have hq2 : 1 ≤ 2 * retainedCutoffMass ν x := by linarith only [hqhalf]
      have h := mul_le_mul_of_nonneg_left hq2 (div_nonneg zero_le_one (pow_nonneg hx.le 3))
      simpa only [div_eq_mul_inv, one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using h

theorem retainedSample_size_bounds (n j : ℕ) (x : ℝ)
    (hx : 2 ≤ x) (hsize : x ^ 6 ≤ (n : ℝ))
    (hj : (j : ℝ) ≤ x ^ 2 / 2) :
    64 ≤ n ∧ j < n ∧ 1 ≤ n - j ∧
      1 - 1 / (2 * x ^ 4) ≤ ((n - j : ℕ) : ℝ) / (n : ℝ) ∧
      (31 / 32 : ℝ) ≤ 1 - 1 / (2 * x ^ 4) := by
  have hx0 : 0 ≤ x := by linarith
  have hx4 : (16 : ℝ) ≤ x ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 4
    norm_num at h
    exact h
  have hx6 : (64 : ℝ) ≤ x ^ 6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 6
    norm_num at h
    exact h
  have hN64 : (64 : ℝ) ≤ n := hx6.trans hsize
  have hn64 : 64 ≤ n := by exact_mod_cast hN64
  have hNpos : (0 : ℝ) < n := by linarith
  have hden : 0 < 2 * x ^ 4 := by positivity
  have hcross : (2 * x ^ 4) * (j : ℝ) ≤ n := by
    have h := mul_le_mul_of_nonneg_right hj (pow_nonneg hx0 4)
    nlinarith only [h, hsize]
  have hjratio : (j : ℝ) / n ≤ 1 / (2 * x ^ 4) := by
    apply (div_le_div_iff₀ hNpos hden).mpr
    nlinarith only [hcross]
  have hinv : 1 / (2 * x ^ 4) ≤ (1 / 32 : ℝ) := by
    apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 32)).mpr
    nlinarith only [hx4]
  have hjdiv : (j : ℝ) / n < 1 :=
    (hjratio.trans hinv).trans_lt (by norm_num)
  have hjN : (j : ℝ) < n := by
    simpa only [one_mul] using (div_lt_iff₀ hNpos).mp hjdiv
  have hjn : j < n := by exact_mod_cast hjN
  have hm : 1 ≤ n - j := by omega
  have hcast : ((n - j : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := Nat.cast_sub hjn.le
  have hfrac : ((n - j : ℕ) : ℝ) / (n : ℝ) = 1 - (j : ℝ) / n := by
    rw [hcast, sub_div, div_self hNpos.ne']
  refine ⟨hn64, hjn, hm, ?_, ?_⟩
  · rw [hfrac]
    linarith only [hjratio]
  · linarith only [hinv]

theorem retainedSample_threshold_bounds (j : ℕ) (x : ℝ)
    (hx : 2 ≤ x) (hj : (j : ℝ) ≤ x ^ 2 / 2) :
    x / Real.sqrt 2 ≤ Real.sqrt (x ^ 2 - (j : ℝ)) ∧
      Real.sqrt (x ^ 2 - (j : ℝ)) ≤ x ∧
      1 ≤ Real.sqrt (x ^ 2 - (j : ℝ)) := by
  have hx0 : 0 ≤ x := by linarith
  have hx2 : (4 : ℝ) ≤ x ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 2
    norm_num at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · apply Real.le_sqrt_of_sq_le
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith only [hj]
  · calc
      Real.sqrt (x ^ 2 - (j : ℝ)) ≤ Real.sqrt (x ^ 2) :=
        Real.sqrt_le_sqrt (sub_le_self _ (Nat.cast_nonneg j))
      _ = x := Real.sqrt_sq hx0
  · apply Real.le_sqrt_of_sq_le
    nlinarith only [hx2, hj]

theorem retainedSample_raw_moment_bounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n j : ℕ) (x : ℝ)
    (hx : 2 ≤ x) (hsize : x ^ 6 ≤ (n : ℝ))
    (hj : (j : ℝ) ≤ x ^ 2 / 2)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (hcut : (n : ℝ) * (∫ z : ℝ, truncationF (x * z) ∂ν) ≤ 1) :
    (∀ᵐ z : ℝ ∂retainedCutoffLaw ν x,
      |z| ≤ 1 / Real.sqrt (x ^ 2 - (j : ℝ))) ∧
    ((1 / 2 : ℝ) ≤ ((n - j : ℕ) : ℝ) *
        (∫ z : ℝ, z ^ 2 ∂retainedCutoffLaw ν x) ∧
      ((n - j : ℕ) : ℝ) *
        (∫ z : ℝ, z ^ 2 ∂retainedCutoffLaw ν x) ≤ 2) ∧
    ((n - j : ℕ) : ℝ) * |∫ z : ℝ, z ∂retainedCutoffLaw ν x| ≤
      2 / Real.sqrt (x ^ 2 - (j : ℝ)) ∧
    ((n - j : ℕ) : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂retainedCutoffLaw ν x) ≤
      2 / (Real.sqrt (x ^ 2 - (j : ℝ))) ^ 3 := by
  obtain ⟨hn64, _, _, hfrac, h31⟩ := retainedSample_size_bounds n j x hx hsize hj
  obtain ⟨_, hyx, hy1⟩ := retainedSample_threshold_bounds j x hx hj
  have hn2 : 2 ≤ n := by omega
  have hxpos : 0 < x := by linarith
  let N : ℝ := n
  let M : ℝ := (n - j : ℕ)
  let y : ℝ := Real.sqrt (x ^ 2 - (j : ℝ))
  let E2 : ℝ := ∫ z : ℝ, z ^ 2 ∂retainedCutoffLaw ν x
  have hN2 : (2 : ℝ) ≤ N := by dsimp only [N]; exact_mod_cast hn2
  have hNpos : 0 < N := by linarith
  have hM0 : 0 ≤ M := Nat.cast_nonneg (n - j)
  have hMN : M ≤ N := by dsimp only [M, N]; exact_mod_cast (Nat.sub_le n j)
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hy1
  have hinv : 1 / x ≤ 1 / y := by
    apply (div_le_div_iff₀ hxpos hypos).mpr
    simpa only [one_mul] using hyx
  obtain ⟨_, hqhalf, _⟩ := retainedCutoffMass_bounds ν n hn2 x hxpos h2 hcut
  have hq : 0 < retainedCutoffMass ν x := by linarith
  have hsecond := retainedCutoffLaw_second_moment_bounds ν n hn2 x hxpos h2 hnorm hcut
  have hE20 : 0 ≤ E2 := integral_nonneg (fun z => sq_nonneg z)
  have hx2 : (4 : ℝ) ≤ x ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 2
    norm_num at h
    exact h
  have hxinv : 1 / x ^ 2 ≤ (1 / 4 : ℝ) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hxpos) (by norm_num : (0 : ℝ) < 4)).mpr
    nlinarith only [hx2]
  have hNlo : (3 / 4 : ℝ) ≤ N * E2 := by
    have hlo : (3 / 4 : ℝ) ≤ 1 - 1 / x ^ 2 := by linarith only [hxinv]
    exact hlo.trans hsecond.1
  have hratio : (31 / 32 : ℝ) ≤ M / N := h31.trans hfrac
  have hprod := mul_le_mul hratio hNlo (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (div_nonneg hM0 hNpos.le)
  have hcancel : (M / N) * (N * E2) = M * E2 := by field_simp [hNpos.ne']
  rw [hcancel] at hprod
  norm_num at hprod
  have hlo : (1 / 2 : ℝ) ≤ M * E2 := by linarith only [hprod]
  have hNinv : 2 / N ≤ 1 := (div_le_iff₀ hNpos).mpr (by linarith only [hN2])
  have hupp : M * E2 ≤ 2 := by
    have h := (mul_le_mul_of_nonneg_right hMN hE20).trans hsecond.2
    linarith only [h, hNinv]
  have hmeanN := retainedCutoffLaw_mean_bound ν n hn2 x hxpos h2 hmean hcut
  have hthirdN := retainedCutoffLaw_third_moment_bound ν n hn2 x hxpos h2 hcut
  have hE30 : 0 ≤ ∫ z : ℝ, |z| ^ 3 ∂retainedCutoffLaw ν x :=
    integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  refine ⟨?_, ⟨hlo, hupp⟩, ?_, ?_⟩
  · filter_upwards [ae_abs_le_retainedCutoffLaw ν x hq] with z hz
    exact hz.trans hinv
  · apply (mul_le_mul_of_nonneg_right hMN (abs_nonneg _)).trans hmeanN |>.trans
    apply (div_le_div_iff₀ hxpos hypos).mpr
    linarith only [hyx]
  · apply (mul_le_mul_of_nonneg_right hMN hE30).trans hthirdN |>.trans
    apply (div_le_div_iff₀ (pow_pos hxpos 3) (pow_pos hypos 3)).mpr
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hypos.le hyx 3) (by norm_num)

end Shao
