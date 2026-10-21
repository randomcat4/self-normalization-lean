import Shao.Basic.TruncationBudget
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrating the genuine truncated-moment budget

The measure `ν` is the true law of the normalized observation in the source.
The results below need only an arbitrary measure on the real line and an
integrable square. In particular, no global third moment is required for the
truncated third-moment kernel. Every integral comparison explicitly proves the
integrability of its two sides.

The original budget is defined for every real parameter; its source range is
nonnegative. Continuity, strict increase, normalization, the limit at infinity,
and the sample-size lower bound are separate results.
-/

set_option autoImplicit false

namespace Shao

open MeasureTheory

/-- The actual source budget for the law of the normalized observation. -/
noncomputable def truncationBudget (ν : Measure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (n : ℝ) * ∫ z : ℝ, truncationF ((1 + t) * z) ∂ν

theorem integrable_truncationF_mul (ν : Measure ℝ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (a : ℝ) :
    Integrable (fun z : ℝ => truncationF (a * z)) ν := by
  apply (h2.const_mul (a ^ 2)).mono'
    ((continuous_truncationF.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
  exact ae_of_all ν (fun z => by
    change ‖truncationF (a * z)‖ ≤ a ^ 2 * z ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (truncationF_nonneg _)]
    calc
      truncationF (a * z) ≤ (a * z) ^ 2 := truncationF_le_sq _
      _ = a ^ 2 * z ^ 2 := mul_pow _ _ _)

theorem integrable_truncation_tail_one (ν : Measure ℝ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (a : ℝ) (ha : 0 < a) :
    Integrable (fun z : ℝ => if 1 / a < |z| then |z| else 0) ν := by
  have hm : Measurable (fun z : ℝ => if 1 / a < |z| then |z| else 0) :=
    Measurable.ite (measurableSet_lt measurable_const continuous_abs.measurable)
      continuous_abs.measurable measurable_const
  apply (h2.const_mul a).mono' hm.aestronglyMeasurable
  exact ae_of_all ν (fun z => by
    split_ifs with hl
    · rw [Real.norm_eq_abs, abs_abs]
      have hlarge : 1 ≤ |z| * a := ((div_lt_iff₀ ha).mp hl).le
      calc
        |z| = 1 * |z| := (one_mul _).symm
        _ ≤ (|z| * a) * |z| := mul_le_mul_of_nonneg_right hlarge (abs_nonneg z)
        _ = a * z ^ 2 := by rw [← sq_abs z]; ring
    · simpa only [norm_zero] using mul_nonneg ha.le (sq_nonneg z))

theorem integrable_truncation_tail_two (ν : Measure ℝ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (a : ℝ) (ha : 0 < a) :
    Integrable (fun z : ℝ => if 1 / a < |z| then z ^ 2 else 0) ν := by
  have hm : Measurable (fun z : ℝ => if 1 / a < |z| then z ^ 2 else 0) :=
    Measurable.ite (measurableSet_lt measurable_const continuous_abs.measurable)
      (continuous_id.pow 2).measurable measurable_const
  apply h2.mono' hm.aestronglyMeasurable
  exact ae_of_all ν (fun z => by
    split_ifs
    · simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z)] using
        (le_rfl : z ^ 2 ≤ z ^ 2)
    · simpa only [norm_zero] using sq_nonneg z)

theorem integrable_truncation_small_three (ν : Measure ℝ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (a : ℝ) (ha : 0 < a) :
    Integrable (fun z : ℝ => if |z| ≤ 1 / a then |z| ^ 3 else 0) ν := by
  have hm : Measurable (fun z : ℝ => if |z| ≤ 1 / a then |z| ^ 3 else 0) :=
    Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
      (continuous_abs.pow 3).measurable measurable_const
  apply (h2.const_mul (1 / a)).mono' hm.aestronglyMeasurable
  exact ae_of_all ν (fun z => by
    split_ifs with hs
    · rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) 3)]
      calc
        |z| ^ 3 = |z| * |z| ^ 2 := by ring
        _ ≤ (1 / a) * |z| ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
        _ = (1 / a) * z ^ 2 := by rw [sq_abs]
    · simpa only [norm_zero] using
        mul_nonneg (div_nonneg zero_le_one ha.le) (sq_nonneg z))

theorem integral_truncation_tail_one_le (ν : Measure ℝ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (a : ℝ) (ha : 0 < a) :
    a * (∫ z : ℝ, if 1 / a < |z| then |z| else 0 ∂ν) ≤
      ∫ z : ℝ, truncationF (a * z) ∂ν := by
  have h := integral_mono
    ((integrable_truncation_tail_one ν h2 a ha).const_mul a)
    (integrable_truncationF_mul ν h2 a) (fun z => truncationF_tail_one a z ha)
  simpa only [integral_const_mul] using h

theorem integral_truncation_tail_two_le (ν : Measure ℝ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (a : ℝ) (ha : 0 < a) :
    a ^ 2 * (∫ z : ℝ, if 1 / a < |z| then z ^ 2 else 0 ∂ν) ≤
      ∫ z : ℝ, truncationF (a * z) ∂ν := by
  have h := integral_mono
    ((integrable_truncation_tail_two ν h2 a ha).const_mul (a ^ 2))
    (integrable_truncationF_mul ν h2 a) (fun z => truncationF_tail_two a z ha)
  simpa only [integral_const_mul] using h

theorem integral_truncation_small_three_le (ν : Measure ℝ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (a : ℝ) (ha : 0 < a) :
    a ^ 3 * (∫ z : ℝ, if |z| ≤ 1 / a then |z| ^ 3 else 0 ∂ν) ≤
      ∫ z : ℝ, truncationF (a * z) ∂ν := by
  have h := integral_mono
    ((integrable_truncation_small_three ν h2 a ha).const_mul (a ^ 3))
    (integrable_truncationF_mul ν h2 a) (fun z => truncationF_truncated_three a z ha)
  simpa only [integral_const_mul] using h

theorem truncationBudget_nonneg (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (t : ℝ) :
    0 ≤ truncationBudget ν n t := by
  have hF := integrable_truncationF_mul ν h2 (1 + t)
  have hzero : Integrable (fun _z : ℝ => (0 : ℝ)) ν := by
    simpa only [zero_mul] using hF.const_mul 0
  have hnonneg := integral_mono hzero hF (fun z => truncationF_nonneg ((1 + t) * z))
  have hI : 0 ≤ ∫ z : ℝ, truncationF ((1 + t) * z) ∂ν := by simpa using hnonneg
  exact mul_nonneg (Nat.cast_nonneg n) hI

theorem truncationBudget_mono (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (s t : ℝ)
    (hs : -1 ≤ s) (hst : s ≤ t) :
    truncationBudget ν n s ≤ truncationBudget ν n t := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  exact integral_mono (integrable_truncationF_mul ν h2 (1 + s))
    (integrable_truncationF_mul ν h2 (1 + t))
    (fun z => truncationF_mono_scale (1 + s) (1 + t) z (by linarith) (by linarith))

theorem truncationBudget_scale_le_one (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (t c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    c ^ 3 * truncationBudget ν n t ≤
        truncationBudget ν n (c * (1 + t) - 1) ∧
      truncationBudget ν n (c * (1 + t) - 1) ≤
        c ^ 2 * truncationBudget ν n t := by
  have harg : 1 + (c * (1 + t) - 1) = c * (1 + t) := by ring
  have hlow := integral_mono
    ((integrable_truncationF_mul ν h2 (1 + t)).const_mul (c ^ 3))
    (integrable_truncationF_mul ν h2 (c * (1 + t)))
    (fun z => by simpa only [mul_assoc] using (truncationF_scale_le_one c ((1 + t) * z) hc0 hc1).1)
  have hupp := integral_mono
    (integrable_truncationF_mul ν h2 (c * (1 + t)))
    ((integrable_truncationF_mul ν h2 (1 + t)).const_mul (c ^ 2))
    (fun z => by simpa only [mul_assoc] using (truncationF_scale_le_one c ((1 + t) * z) hc0 hc1).2)
  rw [integral_const_mul] at hlow hupp
  constructor
  · have h := mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg n)
    simpa only [truncationBudget, harg, mul_assoc, mul_comm, mul_left_comm] using h
  · have h := mul_le_mul_of_nonneg_left hupp (Nat.cast_nonneg n)
    simpa only [truncationBudget, harg, mul_assoc, mul_comm, mul_left_comm] using h

theorem truncationBudget_scale_one_le (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (t c : ℝ) (hc : 1 ≤ c) :
    c ^ 2 * truncationBudget ν n t ≤
        truncationBudget ν n (c * (1 + t) - 1) ∧
      truncationBudget ν n (c * (1 + t) - 1) ≤
        c ^ 3 * truncationBudget ν n t := by
  have harg : 1 + (c * (1 + t) - 1) = c * (1 + t) := by ring
  have hlow := integral_mono
    ((integrable_truncationF_mul ν h2 (1 + t)).const_mul (c ^ 2))
    (integrable_truncationF_mul ν h2 (c * (1 + t)))
    (fun z => by simpa only [mul_assoc] using (truncationF_scale_one_le c ((1 + t) * z) hc).1)
  have hupp := integral_mono
    (integrable_truncationF_mul ν h2 (c * (1 + t)))
    ((integrable_truncationF_mul ν h2 (1 + t)).const_mul (c ^ 3))
    (fun z => by simpa only [mul_assoc] using (truncationF_scale_one_le c ((1 + t) * z) hc).2)
  rw [integral_const_mul] at hlow hupp
  constructor
  · have h := mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg n)
    simpa only [truncationBudget, harg, mul_assoc, mul_comm, mul_left_comm] using h
  · have h := mul_le_mul_of_nonneg_left hupp (Nat.cast_nonneg n)
    simpa only [truncationBudget, harg, mul_assoc, mul_comm, mul_left_comm] using h

theorem truncationBudget_local_comparison (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (x t : ℝ)
    (hx : 0 ≤ x) (ht : 0 ≤ t) (hxt : |t - x| ≤ (1 + x)⁻¹) :
    (1 / 8 : ℝ) * truncationBudget ν n x ≤ truncationBudget ν n t ∧
      truncationBudget ν n t ≤ 8 * truncationBudget ν n x := by
  have hx1 : 0 < 1 + x := by linarith
  have hinv : (1 + x)⁻¹ ≤ (1 : ℝ) := by
    rw [← one_div]
    apply (div_le_iff₀ hx1).mpr
    linarith
  obtain ⟨hdifflo, hdiffhi⟩ := abs_le.mp (hxt.trans hinv)
  let c : ℝ := (1 + t) / (1 + x)
  have hc0 : 0 ≤ c := div_nonneg (by linarith) hx1.le
  have hclo : (1 / 2 : ℝ) ≤ c := by
    apply (le_div_iff₀ hx1).mpr
    linarith
  have hchi : c ≤ 2 := by
    apply (div_le_iff₀ hx1).mpr
    linarith
  have htime : c * (1 + x) - 1 = t := by
    dsimp [c]
    rw [div_mul_cancel₀ _ hx1.ne']
    ring
  have hR := truncationBudget_nonneg ν n h2 x
  by_cases hc1 : c ≤ 1
  · have hbound := truncationBudget_scale_le_one ν n h2 x c hc0 hc1
    rw [htime] at hbound
    have hc3 : (1 / 8 : ℝ) ≤ c ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hclo 3
      norm_num at h
      exact h
    have hc2 : c ^ 2 ≤ 1 := by
      simpa using pow_le_pow_left₀ hc0 hc1 2
    constructor
    · exact (mul_le_mul_of_nonneg_right hc3 hR).trans hbound.1
    · calc
        truncationBudget ν n t ≤ c ^ 2 * truncationBudget ν n x := hbound.2
        _ ≤ 1 * truncationBudget ν n x := mul_le_mul_of_nonneg_right hc2 hR
        _ ≤ 8 * truncationBudget ν n x := by linarith
  · have hc1' : 1 ≤ c := (lt_of_not_ge hc1).le
    have hbound := truncationBudget_scale_one_le ν n h2 x c hc1'
    rw [htime] at hbound
    have hc2 : 1 ≤ c ^ 2 := by
      simpa using pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hc1' 2
    have hc3 : c ^ 3 ≤ 8 := by
      have h := pow_le_pow_left₀ hc0 hchi 3
      norm_num at h
      exact h
    constructor
    · calc
        (1 / 8 : ℝ) * truncationBudget ν n x ≤ 1 * truncationBudget ν n x := by linarith
        _ ≤ c ^ 2 * truncationBudget ν n x := mul_le_mul_of_nonneg_right hc2 hR
        _ ≤ truncationBudget ν n t := hbound.1
    · exact hbound.2.trans (mul_le_mul_of_nonneg_right hc3 hR)

theorem truncationBudget_decomposition (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (t : ℝ) (ht : -1 < t) :
    truncationBudget ν n t =
      (1 + t) ^ 3 * ((n : ℝ) *
        ∫ z : ℝ, if |z| ≤ 1 / (1 + t) then |z| ^ 3 else 0 ∂ν) +
      (1 + t) ^ 2 * ((n : ℝ) *
        ∫ z : ℝ, if 1 / (1 + t) < |z| then z ^ 2 else 0 ∂ν) := by
  have ha : 0 < 1 + t := by linarith
  have hsmall := integrable_truncation_small_three ν h2 (1 + t) ha
  have hlarge := integrable_truncation_tail_two ν h2 (1 + t) ha
  have hI : (∫ z : ℝ, truncationF ((1 + t) * z) ∂ν) =
      (1 + t) ^ 3 * (∫ z : ℝ, if |z| ≤ 1 / (1 + t) then |z| ^ 3 else 0 ∂ν) +
      (1 + t) ^ 2 * (∫ z : ℝ, if 1 / (1 + t) < |z| then z ^ 2 else 0 ∂ν) := by
    calc
      _ = ∫ z : ℝ, (1 + t) ^ 3 * (if |z| ≤ 1 / (1 + t) then |z| ^ 3 else 0) +
            (1 + t) ^ 2 * (if 1 / (1 + t) < |z| then z ^ 2 else 0) ∂ν :=
        integral_congr_ae (ae_of_all ν (fun z => truncationF_scaled_decomposition (1 + t) z ha))
      _ = _ := by
        rw [integral_add (hsmall.const_mul _) (hlarge.const_mul _),
          integral_const_mul, integral_const_mul]
  unfold truncationBudget
  rw [hI]
  ring

theorem truncationBudget_le_rpow_moment (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (t p : ℝ)
    (ht : 0 ≤ t) (hp2 : 2 ≤ p) (hp3 : p ≤ 3)
    (hp : Integrable (fun z : ℝ => Real.rpow |z| p) ν) :
    truncationBudget ν n t ≤
      Real.rpow (1 + t) p * ((n : ℝ) * ∫ z : ℝ, Real.rpow |z| p ∂ν) := by
  have ha : 0 ≤ 1 + t := by linarith
  have hpoint (z : ℝ) : Real.rpow |(1 + t) * z| p =
      Real.rpow (1 + t) p * Real.rpow |z| p := by
    rw [abs_mul, abs_of_nonneg ha]
    exact Real.mul_rpow (z := p) ha (abs_nonneg z)
  have hpmul : Integrable (fun z : ℝ => Real.rpow |(1 + t) * z| p) ν :=
    (hp.const_mul (Real.rpow (1 + t) p)).congr (ae_of_all ν (fun z => (hpoint z).symm))
  have hbound := integral_mono (integrable_truncationF_mul ν h2 (1 + t)) hpmul
    (fun z => truncationF_le_rpow ((1 + t) * z) p hp2 hp3)
  have hI : (∫ z : ℝ, Real.rpow |(1 + t) * z| p ∂ν) =
      Real.rpow (1 + t) p * ∫ z : ℝ, Real.rpow |z| p ∂ν := by
    calc
      _ = ∫ z : ℝ, Real.rpow (1 + t) p * Real.rpow |z| p ∂ν :=
        integral_congr_ae (ae_of_all ν hpoint)
      _ = _ := integral_const_mul _ _
  rw [hI] at hbound
  have h := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg n)
  simpa only [truncationBudget, mul_assoc, mul_comm, mul_left_comm] using h

theorem truncationBudget_cutoff_tail_one (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (x : ℝ) (hx : 0 < x) :
    x * ((n : ℝ) * ∫ z : ℝ, if 1 / x < |z| then |z| else 0 ∂ν) ≤
      truncationBudget ν n x := by
  have hscale := integral_mono (integrable_truncationF_mul ν h2 x)
    (integrable_truncationF_mul ν h2 (1 + x))
    (fun z => truncationF_mono_scale x (1 + x) z hx.le (by linarith))
  have h := mul_le_mul_of_nonneg_left
    ((integral_truncation_tail_one_le ν h2 x hx).trans hscale) (Nat.cast_nonneg n)
  simpa only [truncationBudget, mul_assoc, mul_comm, mul_left_comm] using h

theorem truncationBudget_cutoff_tail_two (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (x : ℝ) (hx : 0 < x) :
    x ^ 2 * ((n : ℝ) * ∫ z : ℝ, if 1 / x < |z| then z ^ 2 else 0 ∂ν) ≤
      truncationBudget ν n x := by
  have hscale := integral_mono (integrable_truncationF_mul ν h2 x)
    (integrable_truncationF_mul ν h2 (1 + x))
    (fun z => truncationF_mono_scale x (1 + x) z hx.le (by linarith))
  have h := mul_le_mul_of_nonneg_left
    ((integral_truncation_tail_two_le ν h2 x hx).trans hscale) (Nat.cast_nonneg n)
  simpa only [truncationBudget, mul_assoc, mul_comm, mul_left_comm] using h

theorem truncationBudget_cutoff_small_three (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (x : ℝ) (hx : 0 < x) :
    x ^ 3 * ((n : ℝ) * ∫ z : ℝ, if |z| ≤ 1 / x then |z| ^ 3 else 0 ∂ν) ≤
      truncationBudget ν n x := by
  have hscale := integral_mono (integrable_truncationF_mul ν h2 x)
    (integrable_truncationF_mul ν h2 (1 + x))
    (fun z => truncationF_mono_scale x (1 + x) z hx.le (by linarith))
  have h := mul_le_mul_of_nonneg_left
    ((integral_truncation_small_three_le ν h2 x hx).trans hscale) (Nat.cast_nonneg n)
  simpa only [truncationBudget, mul_assoc, mul_comm, mul_left_comm] using h

end Shao
