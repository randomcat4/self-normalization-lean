import Shao.Probability.SourceNonresidualBrownian
import Shao.Probability.GaussianTail

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace Shao.C2.ActualBrownianThresholdPayment
open MeasureTheory ProbabilityTheory Set
open Shao.C2.BridgeDomination
open scoped NNReal Topology Classical

theorem standard_normal_tail_local_difference
    (x t : ℝ) (hx : 0 ≤ x) (ht : 0 ≤ t)
    (hneigh : |t - x| ≤ 1 / (1 + x)) :
    |Shao.standardNormalTail t - Shao.standardNormalTail x| ≤
      (2 * Real.exp 2) * (1 + x) * |t - x| * Shao.standardNormalTail x := by
  let delta : ℝ := |t - x|
  let K : ℝ := (2 * Real.exp 2) * (1 + x) * Shao.standardNormalTail x
  have ha : 0 < 1 + x := by linarith only [hx]
  have hd : 0 ≤ delta := abs_nonneg _
  have hBudget : delta * (1 + x) ≤ 1 := (le_div_iff₀ ha).mp hneigh
  have hdOne : delta ≤ 1 := by nlinarith only [hBudget, mul_nonneg hd hx]
  have hBetween (s : ℝ) (hs : s ∈ Icc (min x t) (max x t)) :
      0 ≤ s ∧ |s - x| ≤ delta := by
    refine ⟨(le_min hx ht).trans hs.1, ?_⟩
    change |s - x| ≤ |t - x|
    by_cases hxt : x ≤ t
    · rw [min_eq_left hxt, max_eq_right hxt] at hs
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1), abs_of_nonneg (sub_nonneg.mpr hxt)]
      linarith only [hs.2]
    · have htx : t ≤ x := (lt_of_not_ge hxt).le
      rw [min_eq_right htx, max_eq_left htx] at hs
      rw [abs_of_nonpos (sub_nonpos.mpr hs.2), abs_of_nonpos (sub_nonpos.mpr htx)]
      linarith only [hs.1]
  have hDeriv (s : ℝ) (hs : s ∈ Icc (min x t) (max x t)) :
      ‖deriv Shao.standardNormalTail s‖ ≤ K := by
    have hs0 := (hBetween s hs).1
    have hsDistance := (hBetween s hs).2
    have hsUpper : s ≤ x + delta := by
      have hh := (abs_le.mp hsDistance).2
      linarith only [hh]
    have hLinear : 1 + s ≤ 2 * (1 + x) := by linarith only [hsUpper, hdOne, hx]
    have hTail :=
      (Shao.standardNormalTail_local_comparison x s hx hs0 (hsDistance.trans hneigh)).2
    have hTail0 : 0 ≤ Shao.standardNormalTail s :=
      ((Shao.standardNormalTail_basic.2.2.1 s).1).le
    have hDensity : Shao.standardNormalDensity s ≤
        (1 + s) * Shao.standardNormalTail s := by
      simpa only [mul_comm] using
        (div_le_iff₀ (show 0 < 1 + s by linarith only [hs0])).mp
          (Shao.standardNormal_mills_bounds s hs0).1
    have hDensityPos : 0 < Shao.standardNormalDensity s :=
      ProbabilityTheory.gaussianPDFReal_pos 0 1 s (by norm_num)
    rw [(Shao.standardNormal_derivatives s).2.deriv, norm_neg,
      Real.norm_eq_abs, abs_of_pos hDensityPos]
    calc
      Shao.standardNormalDensity s ≤ (1 + s) * Shao.standardNormalTail s := hDensity
      _ ≤ (2 * (1 + x)) * (Real.exp 2 * Shao.standardNormalTail x) :=
        mul_le_mul hLinear hTail hTail0 (by linarith only [ha])
      _ = K := by dsimp only [K]; ring
  have hMean := Convex.norm_image_sub_le_of_norm_deriv_le (C := K)
    (fun s (_hs : s ∈ Icc (min x t) (max x t)) =>
      (Shao.standardNormal_derivatives s).2.differentiableAt)
    hDeriv (convex_Icc (min x t) (max x t))
    (show x ∈ Icc (min x t) (max x t) from ⟨min_le_left _ _, le_max_left _ _⟩)
    (show t ∈ Icc (min x t) (max x t) from ⟨min_le_right _ _, le_max_right _ _⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hMean
  calc
    |Shao.standardNormalTail t - Shao.standardNormalTail x| ≤ K * |t - x| := hMean
    _ = (2 * Real.exp 2) * (1 + x) * |t - x| * Shao.standardNormalTail x := by
      dsimp only [K]
      ring

theorem brownian_double_threshold_difference
    {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hB : IsBrownianReal B PB) (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    let D : ℝ → Set ΩB := fun z => {omega |
      (∃ r : BridgeTime, z ≤ B ⟨(r : ℝ), r.property.1⟩ omega) ∧
      ∃ r : BridgeTime, B ⟨(r : ℝ), r.property.1⟩ omega ≤ -z}
    0 ≤ PB.real (D s) - PB.real (D t) ∧
      PB.real (D s) - PB.real (D t) ≤
        4 * (Shao.standardNormalTail s - Shao.standardNormalTail t) := by
  intro D
  let H : ℝ → Set ΩB := fun z =>
    {omega | ∃ r : BridgeTime, z ≤ |B ⟨(r : ℝ), r.property.1⟩ omega|}
  have ht : 0 < t := hs.trans_le hst
  have hS :=
    (Shao.Probability.SourceNonresidualBrownian.actual_brownian_weak_double_crossing
      B PB hB s hs).2.2.2.2.1
  have hT :=
    (Shao.Probability.SourceNonresidualBrownian.actual_brownian_weak_double_crossing
      B PB hB t ht).2.2.2.2.1
  change PB.real (D s) = 4 * Shao.standardNormalTail s - PB.real (H s) at hS
  change PB.real (D t) = 4 * Shao.standardNormalTail t - PB.real (H t) at hT
  have hDsub : D t ⊆ D s := by
    intro omega homega
    rcases homega with ⟨⟨r, hr⟩, ⟨q, hq⟩⟩
    refine ⟨⟨r, hst.trans hr⟩, ⟨q, ?_⟩⟩
    linarith only [hq, hst]
  have hHsub : H t ⊆ H s := by
    intro omega homega
    rcases homega with ⟨r, hr⟩
    exact ⟨r, hst.trans hr⟩
  have hDmono : PB.real (D t) ≤ PB.real (D s) := measureReal_mono hDsub
  have hHmono : PB.real (H t) ≤ PB.real (H s) := measureReal_mono hHsub
  exact ⟨sub_nonneg.mpr hDmono, by linarith only [hS, hT, hHmono]⟩

theorem brownian_double_local_threshold_payment
    {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hB : IsBrownianReal B PB) (x t : ℝ) (hx : 0 < x) (ht : 0 < t)
    (hneigh : |t - x| ≤ 1 / (1 + x)) :
    let D : ℝ → Set ΩB := fun z => {omega |
      (∃ r : BridgeTime, z ≤ B ⟨(r : ℝ), r.property.1⟩ omega) ∧
      ∃ r : BridgeTime, B ⟨(r : ℝ), r.property.1⟩ omega ≤ -z}
    Shao.standardNormalTail t ≤ Real.exp 2 * Shao.standardNormalTail x ∧
      |PB.real (D t) - PB.real (D x)| ≤
        (8 * Real.exp 2) * (1 + x) * |t - x| * Shao.standardNormalTail x := by
  intro D
  have hTail := (Shao.standardNormalTail_local_comparison x t hx.le ht.le hneigh).2
  have hGaussian := standard_normal_tail_local_difference x t hx.le ht.le hneigh
  have hDifference : |PB.real (D t) - PB.real (D x)| ≤
      4 * |Shao.standardNormalTail t - Shao.standardNormalTail x| := by
    rcases le_total x t with hxt | htx
    · have hh := brownian_double_threshold_difference B PB hB x t hx hxt
      change 0 ≤ PB.real (D x) - PB.real (D t) ∧
        PB.real (D x) - PB.real (D t) ≤
          4 * (Shao.standardNormalTail x - Shao.standardNormalTail t) at hh
      rw [abs_of_nonpos (by linarith only [hh.1] : PB.real (D t) - PB.real (D x) ≤ 0)]
      have hAbs := neg_le_abs (Shao.standardNormalTail t - Shao.standardNormalTail x)
      linarith only [hh.2, hAbs]
    · have hh := brownian_double_threshold_difference B PB hB t x ht htx
      change 0 ≤ PB.real (D t) - PB.real (D x) ∧
        PB.real (D t) - PB.real (D x) ≤
          4 * (Shao.standardNormalTail t - Shao.standardNormalTail x) at hh
      rw [abs_of_nonneg hh.1]
      have hAbs := le_abs_self (Shao.standardNormalTail t - Shao.standardNormalTail x)
      linarith only [hh.2, hAbs]
  refine ⟨hTail, ?_⟩
  calc
    |PB.real (D t) - PB.real (D x)| ≤
        4 * |Shao.standardNormalTail t - Shao.standardNormalTail x| := hDifference
    _ ≤ 4 * ((2 * Real.exp 2) * (1 + x) * |t - x| * Shao.standardNormalTail x) :=
      mul_le_mul_of_nonneg_left hGaussian (by norm_num)
    _ = (8 * Real.exp 2) * (1 + x) * |t - x| * Shao.standardNormalTail x := by ring

end Shao.C2.ActualBrownianThresholdPayment
