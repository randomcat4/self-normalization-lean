import Shao.Basic.FinitePath
import Shao.OQ4.CosineCoefficients
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr

/-!
# Genuine Gaussian limits for varying-row finite blocks

Source: b01/proof01.md 233–237. A common third absolute moment bound
controls the complete complex characteristic function. The comparison is a
finite unit-disk telescoping estimate; it does not invoke a fixed-law CLT.
This one-block identification does not close the path-space or OQ4 roots.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal

namespace Shao.OQ4.RowBlockGaussianLimit

noncomputable section

def scaledBlockSum (n : ℕ) (h : ℝ) (a : Shao.Path n) : ℝ :=
  Shao.prefixSum a n / h

private theorem scaledBlockSum_continuous (n : ℕ) (h : ℝ) :
    Continuous (scaledBlockSum n h) := by
  unfold scaledBlockSum
  simp only [Shao.prefixSum_length]
  fun_prop

private theorem integrable_lower_moments_of_third
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν) :
    Integrable (fun x : ℝ => x) ν ∧
      Integrable (fun x : ℝ => x ^ 2) ν := by
  have hdom (x : ℝ) : |x| ≤ 1 + |x| ^ 3 ∧ x ^ 2 ≤ 1 + |x| ^ 3 := by
    have hp := abs_nonneg x
    by_cases hx : |x| ≤ 1
    · constructor
      · nlinarith [pow_nonneg hp 3]
      · nlinarith [mul_nonneg (sub_nonneg.mpr hx) hp, sq_abs x,
          pow_nonneg hp 3]
    · have h1 : 1 ≤ |x| := le_of_not_ge hx
      have h2 : |x| ≤ |x| ^ 2 := by
        nlinarith [mul_nonneg hp (sub_nonneg.mpr h1)]
      have h3' : |x| ^ 2 ≤ |x| ^ 3 := by
        nlinarith [mul_nonneg (sq_nonneg |x|) (sub_nonneg.mpr h1)]
      constructor <;> nlinarith [sq_abs x]
  have hi : Integrable (fun x : ℝ => 1 + |x| ^ 3) ν := (integrable_const 1).add h3
  constructor
  · exact hi.mono' (by fun_prop) (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using (hdom x).1)
  · exact hi.mono' (by fun_prop) (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)] using (hdom x).2)

private theorem charFun_third_moment_remainder_bound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (u : ℝ) :
    ‖charFun ν u - ((1 - u ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      (∫ x : ℝ, |x| ^ 3 ∂ν) * |u| ^ 3 / 3 := by
  obtain ⟨h1, h2⟩ := integrable_lower_moments_of_third ν h3
  have hb := Shao.OQ4.cosine_coefficients_third_moment_bound ν
    (fun x : ℝ => x) u h1 h2 h3 hmean hsecond
  dsimp only at hb
  have hi : Integrable (fun x : ℝ => Complex.exp ((u * x : ℝ) * Complex.I)) ν := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Eventually.of_forall fun x => by simp [Complex.norm_exp]
  have hre : (charFun ν u).re = ∫ x : ℝ, Real.cos (u * x) ∂ν := by
    rw [charFun_apply_real]
    simpa [Complex.exp_re] using (integral_re hi).symm
  have him : (charFun ν u).im = ∫ x : ℝ, Real.sin (u * x) ∂ν := by
    rw [charFun_apply_real]
    simpa [Complex.exp_im] using (integral_im hi).symm
  calc
    _ ≤ |(charFun ν u - ((1 - u ^ 2 / 2 : ℝ) : ℂ)).re| +
        |(charFun ν u - ((1 - u ^ 2 / 2 : ℝ) : ℂ)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |(∫ x : ℝ, Real.cos (u * x) ∂ν) - (1 - u ^ 2 / 2)| +
        |∫ x : ℝ, Real.sin (u * x) ∂ν| := by
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, hre, him, sub_zero]
    _ ≤ |u| ^ 3 * (∫ x : ℝ, |x| ^ 3 ∂ν) / 6 +
        |u| ^ 3 * (∫ x : ℝ, |x| ^ 3 ∂ν) / 6 := add_le_add hb.1 hb.2
    _ = _ := by ring

private theorem norm_pow_sub_pow_unitDisk_le
    (z w : ℂ) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖z ^ n - w ^ n‖ ≤ (n : ℝ) * ‖z - w‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hzn : ‖z ^ n‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg z) hz
    have hid : z ^ (n + 1) - w ^ (n + 1) =
        z ^ n * (z - w) + (z ^ n - w ^ n) * w := by ring
    calc
      _ ≤ ‖z ^ n‖ * ‖z - w‖ + ‖z ^ n - w ^ n‖ * ‖w‖ := by
        rw [hid]
        simpa only [norm_mul] using norm_add_le (z ^ n * (z - w)) ((z ^ n - w ^ n) * w)
      _ ≤ 1 * ‖z - w‖ + ((n : ℝ) * ‖z - w‖) * 1 :=
        add_le_add (mul_le_mul_of_nonneg_right hzn (norm_nonneg _))
          (mul_le_mul ih hw (norm_nonneg _) (by positivity))
      _ = _ := by push_cast; ring

private theorem charFun_pow_gaussian_error_bound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (u : ℝ) (hu : u ^ 2 / 2 ≤ 1) (n : ℕ) :
    ‖(charFun ν u) ^ n -
      Complex.exp ((-((n : ℝ) * u ^ 2) / 2 : ℝ) : ℂ)‖ ≤
      (n : ℝ) *
        ((∫ x : ℝ, |x| ^ 3 ∂ν) * |u| ^ 3 / 3 + u ^ 4 / 4) := by
  let c : ℂ := ((-(u ^ 2 / 2) : ℝ) : ℂ)
  have hc : ‖c‖ ≤ 1 := by
    simpa [c, abs_of_nonneg (show 0 ≤ u ^ 2 / 2 by positivity)] using hu
  have hw : ‖Complex.exp c‖ ≤ 1 := by
    rw [show c = ((-(u ^ 2 / 2) : ℝ) : ℂ) from rfl, Complex.norm_exp_ofReal]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (sq_nonneg u) (by norm_num)))
  have he : ‖Complex.exp c - ((1 - u ^ 2 / 2 : ℝ) : ℂ)‖ ≤ u ^ 4 / 4 := by
    have hr := Complex.norm_exp_sub_one_sub_id_le hc
    have hleft : Complex.exp c - ((1 - u ^ 2 / 2 : ℝ) : ℂ) = Complex.exp c - 1 - c := by
      dsimp only [c]
      push_cast
      ring
    rw [hleft]
    convert hr using 1
    simp only [c, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ u ^ 2 / 2 by positivity)]
    ring
  have hstep : ‖charFun ν u - Complex.exp c‖ ≤
      (∫ x : ℝ, |x| ^ 3 ∂ν) * |u| ^ 3 / 3 + u ^ 4 / 4 := by
    calc
      _ = ‖(charFun ν u - ((1 - u ^ 2 / 2 : ℝ) : ℂ)) +
          (((1 - u ^ 2 / 2 : ℝ) : ℂ) - Complex.exp c)‖ := by congr 1; ring
      _ ≤ ‖charFun ν u - ((1 - u ^ 2 / 2 : ℝ) : ℂ)‖ +
          ‖((1 - u ^ 2 / 2 : ℝ) : ℂ) - Complex.exp c‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (charFun_third_moment_remainder_bound ν h3 hmean hsecond u)
        (by simpa only [norm_sub_rev] using he)
  have hp : Complex.exp c ^ n = Complex.exp ((-((n : ℝ) * u ^ 2) / 2 : ℝ) : ℂ) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    dsimp only [c]
    push_cast
    ring
  rw [← hp]
  exact (norm_pow_sub_pow_unitDisk_le _ _ (norm_charFun_le_one u) hw n).trans
    (mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg n))

theorem charFun_scaledBlockSum
    (n : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] (h t : ℝ) :
    charFun ((Measure.pi (fun _ : Fin n => ν)).map (scaledBlockSum n h)) t =
      (charFun ν (t / h)) ^ n := by
  have heq : scaledBlockSum n h = (fun a : Shao.Path n => h⁻¹ * ∑ i, a i) := by
    funext a
    simp [scaledBlockSum, Shao.prefixSum_length, div_eq_mul_inv, mul_comm]
  rw [heq, charFun_map_mul_comp (by fun_prop), charFun_map_sum_pi_eq_prod]
  simp [div_eq_mul_inv, mul_comm]

theorem row_block_charFun_tendsto
    (νSeq : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (νSeq j)]
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hbound : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (hh : Tendsto hSeq atTop atTop)
    (nSeq : ℕ → ℕ) (T : ℝ≥0)
    (hratio : Tendsto (fun j => (nSeq j : ℝ) / (hSeq j) ^ 2)
      atTop (𝓝 (T : ℝ))) (t : ℝ) :
    Tendsto (fun j => charFun
      ((Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).map
        (scaledBlockSum (nSeq j) (hSeq j))) t)
      atTop (𝓝 (Complex.exp ((-((T : ℝ) * t ^ 2) / 2 : ℝ) : ℂ))) := by
  have hi : Tendsto (fun j => (hSeq j)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hh
  have hu : Tendsto (fun j => t / hSeq j) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul t
  have hu2 : Tendsto (fun j => (t / hSeq j) ^ 2 / 2) atTop (𝓝 (0 : ℝ)) := by
    simpa using (hu.pow 2).div_const 2
  have hsmall : ∀ᶠ j in atTop, (t / hSeq j) ^ 2 / 2 ≤ 1 :=
    (hu2.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).mono fun _ hj => hj.le
  let E : ℕ → ℝ := fun j =>
    (M * |t| ^ 3 / 3) * ((nSeq j : ℝ) / (hSeq j) ^ 2) * (hSeq j)⁻¹ +
      (t ^ 4 / 4) * ((nSeq j : ℝ) / (hSeq j) ^ 2) * ((hSeq j)⁻¹) ^ 2
  have hE : Tendsto E atTop (𝓝 (0 : ℝ)) := by
    have hA := (hratio.mul hi).const_mul (M * |t| ^ 3 / 3)
    have hB := (hratio.mul (hi.pow 2)).const_mul (t ^ 4 / 4)
    simpa [E, mul_assoc] using hA.add hB
  have hbound' : ∀ᶠ j in atTop,
      ‖(charFun (νSeq j) (t / hSeq j)) ^ nSeq j -
        Complex.exp ((-((nSeq j : ℝ) * (t / hSeq j) ^ 2) / 2 : ℝ) : ℂ)‖ ≤ E j := by
    filter_upwards [hsmall, hh.eventually_ge_atTop 1] with j hj hhj
    have hpos : 0 < hSeq j := lt_of_lt_of_le (by norm_num) hhj
    calc
      _ ≤ (nSeq j : ℝ) *
          ((∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) * |t / hSeq j| ^ 3 / 3 +
            (t / hSeq j) ^ 4 / 4) :=
        charFun_pow_gaussian_error_bound (νSeq j) (h3 j) (hmean j) (hsecond j) _ hj _
      _ ≤ (nSeq j : ℝ) * (M * |t / hSeq j| ^ 3 / 3 + (t / hSeq j) ^ 4 / 4) := by
        gcongr
        exact hbound j
      _ = E j := by
        dsimp only [E]
        rw [abs_div, abs_of_pos hpos]
        simp only [div_eq_mul_inv, inv_pow]
        ring
  have hd : Tendsto (fun j => (charFun (νSeq j) (t / hSeq j)) ^ nSeq j -
      Complex.exp ((-((nSeq j : ℝ) * (t / hSeq j) ^ 2) / 2 : ℝ) : ℂ))
      atTop (𝓝 (0 : ℂ)) := by
    apply (tendsto_zero_iff_norm_tendsto_zero).2
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound' hE
  have hexponent : Tendsto (fun j => -((nSeq j : ℝ) * (t / hSeq j) ^ 2) / 2)
      atTop (𝓝 (-((T : ℝ) * t ^ 2) / 2)) := by
    convert (hratio.mul_const (t ^ 2)).neg.div_const 2 using 1
    funext j
    rw [div_pow]
    ring
  have hcexponent := Complex.continuous_ofReal.continuousAt.tendsto.comp hexponent
  have hy := Complex.continuous_exp.continuousAt.tendsto.comp hcexponent
  simp_rw [charFun_scaledBlockSum]
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using hd.add hy

theorem row_block_tendsto_gaussian
    (νSeq : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (νSeq j)]
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hbound : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (hh : Tendsto hSeq atTop atTop)
    (nSeq : ℕ → ℕ) (T : ℝ≥0)
    (hratio : Tendsto (fun j => (nSeq j : ℝ) / (hSeq j) ^ 2)
      atTop (𝓝 (T : ℝ))) :
    TendstoInDistribution (fun j => scaledBlockSum (nSeq j) (hSeq j)) atTop
      (id : ℝ → ℝ) (fun j => Measure.pi (fun _ : Fin (nSeq j) => νSeq j))
      (ProbabilityTheory.gaussianReal 0 T) := by
  apply TendstoInDistribution.of_tendsto_charFun
    (fun j => (scaledBlockSum_continuous (nSeq j) (hSeq j)).measurable.aemeasurable)
    measurable_id.aemeasurable
  intro t
  have hgauss : charFun ((gaussianReal 0 T).map (id : ℝ → ℝ)) t =
      Complex.exp ((-((T : ℝ) * t ^ 2) / 2 : ℝ) : ℂ) := by
    rw [Measure.map_id, charFun_gaussianReal]
    congr 1
    push_cast
    ring
  rw [hgauss]
  exact row_block_charFun_tendsto νSeq h3 hmean hsecond M hbound hSeq hh nSeq T hratio t

theorem floor_time_block_tendsto_gaussian
    (νSeq : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (νSeq j)]
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hbound : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (hh : Tendsto hSeq atTop atTop)
    (T : ℝ≥0) :
    TendstoInDistribution
      (fun j => scaledBlockSum (Nat.floor ((T : ℝ) * (hSeq j) ^ 2)) (hSeq j))
      atTop (id : ℝ → ℝ)
      (fun j => Measure.pi
        (fun _ : Fin (Nat.floor ((T : ℝ) * (hSeq j) ^ 2)) => νSeq j))
      (ProbabilityTheory.gaussianReal 0 T) := by
  apply row_block_tendsto_gaussian νSeq h3 hmean hsecond M hbound hSeq hh
    (fun j => Nat.floor ((T : ℝ) * (hSeq j) ^ 2)) T
  exact (tendsto_nat_floor_mul_div_atTop T.2).comp
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hh)

end

end Shao.OQ4.RowBlockGaussianLimit
