import Shao.C2.IntervalImageTaylorSegment

noncomputable section
namespace Shao.C2.IntervalSpectralGaussian
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.HalfLineTimeProfiles Shao.C2.IntervalImageSpatialConvergence

def weightedGaussian (c : ℝ) (r : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ r * Real.exp (-c * ((n : ℝ) + 1) ^ 2 * x)

def spectralConstant (c : ℝ) (r : ℕ) : ℝ :=
  (1 / (c / 2)) ^ (r + 1) * (2 : ℝ) ^ (r + 1) * (Nat.factorial (r + 1) : ℝ) *
    (∑' n : ℕ, weightedGaussian (c / 2) r 1 n)

theorem weightedGaussian_nonneg (c x : ℝ) (r n : ℕ) :
    0 ≤ weightedGaussian c r x n := by
  dsimp only [weightedGaussian]
  positivity

theorem weightedGaussian_summable (c x : ℝ) (r : ℕ) (hc : 0 < c) (hx : 0 < x) :
    Summable (weightedGaussian c r x) := by
  let C : ℝ := c * x
  let K : ℝ := (1 / C) ^ r * (2 : ℝ) ^ r * (Nat.factorial r : ℝ)
  have hC : 0 < C := mul_pos hc hx
  have hg := summable_exp_neg_nat_sq (C / 2) (by positivity)
  have hshift : Summable (fun n : ℕ => Real.exp (-(C / 2) * ((n : ℝ) + 1) ^ 2)) := by
    have hs := hg.comp_injective (show Function.Injective (fun n : ℕ => n + 1) from
      fun _ _ h => Nat.add_right_cancel h)
    change Summable (fun n : ℕ => Real.exp (-(C / 2) * (((n + 1 : ℕ) : ℝ)) ^ 2)) at hs
    simpa only [Nat.cast_add, Nat.cast_one] using hs
  have hb (n : ℕ) : ‖weightedGaussian c r x n‖ ≤
      K * Real.exp (-(C / 2) * ((n : ℝ) + 1) ^ 2) := by
    let N : ℝ := (n : ℝ) + 1
    have hN : 1 ≤ N := by dsimp only [N]; linarith only [Nat.cast_nonneg (α := ℝ) n]
    have hNsq : N ≤ N ^ 2 := by nlinarith only [hN]
    have hpow := pow_le_pow_left₀ (by linarith only [hN] : 0 ≤ N) hNsq r
    have hm := nonneg_exp_monomial_profile (C * N ^ 2) (by positivity) r
    have hscale : (1 / C) ^ r * (C * N ^ 2) ^ r = (N ^ 2) ^ r := by
      rw [← mul_pow]
      congr 1
      field_simp [ne_of_gt hC]
    have he : -c * N ^ 2 * x = -(C * N ^ 2) := by dsimp only [C]; ring
    rw [Real.norm_eq_abs, abs_of_nonneg (weightedGaussian_nonneg c x r n)]
    change N ^ r * Real.exp (-c * N ^ 2 * x) ≤ K * Real.exp (-(C / 2) * N ^ 2)
    rw [he]
    calc
      _ ≤ (N ^ 2) ^ r * Real.exp (-(C * N ^ 2)) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
      _ = (1 / C) ^ r * ((C * N ^ 2) ^ r * Real.exp (-(C * N ^ 2))) := by
        rw [← mul_assoc, hscale]
      _ ≤ (1 / C) ^ r * ((2 : ℝ) ^ r * (Nat.factorial r : ℝ) *
          Real.exp (-(C * N ^ 2) / 2)) := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = _ := by
        rw [show -(C * N ^ 2) / 2 = -(C / 2) * N ^ 2 by ring]
        dsimp only [K]
        ring
  exact (hshift.mul_left K).of_norm_bounded hb

theorem weightedGaussian_split_bound (c x : ℝ) (r n : ℕ) (hc : 0 < c) (hx : 1 ≤ x) :
    weightedGaussian c r x n ≤ Real.exp (-(c / 2) * x) * weightedGaussian (c / 2) r 1 n := by
  let N : ℝ := (n : ℝ) + 1
  have hN : 1 ≤ N := by dsimp only [N]; linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hN2 : 1 ≤ N ^ 2 := by nlinarith only [hN]
  have hx0 : 0 ≤ x := by linarith only [hx]
  have h1 : N ^ 2 ≤ N ^ 2 * x := by
    nlinarith only [mul_nonneg (sq_nonneg N) (sub_nonneg.mpr hx)]
  have h2 : x ≤ N ^ 2 * x := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hN2) hx0]
  have he : -c * N ^ 2 * x ≤ -(c / 2) * x + -(c / 2) * N ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hc.le
    nlinarith only [hh]
  change N ^ r * Real.exp (-c * N ^ 2 * x) ≤
    Real.exp (-(c / 2) * x) * (N ^ r * Real.exp (-(c / 2) * N ^ 2 * 1))
  calc
    _ ≤ N ^ r * Real.exp (-(c / 2) * x + -(c / 2) * N ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
    _ = _ := by rw [Real.exp_add, mul_one]; ring

theorem weightedGaussian_tsum_split (c x : ℝ) (r : ℕ) (hc : 0 < c) (hx : 1 ≤ x) :
    (∑' n : ℕ, weightedGaussian c r x n) ≤
      Real.exp (-(c / 2) * x) * (∑' n : ℕ, weightedGaussian (c / 2) r 1 n) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hs := weightedGaussian_summable c x r hc hx0
  have hg := weightedGaussian_summable (c / 2) 1 r (by positivity) (by norm_num)
  have hb : ∀ n : ℕ, ‖weightedGaussian c r x n‖ ≤
      Real.exp (-(c / 2) * x) * weightedGaussian (c / 2) r 1 n := by
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (weightedGaussian_nonneg c x r n)]
    exact weightedGaussian_split_bound c x r n hc hx
  have hsum := hs.hasSum.norm_le_of_bounded (hg.hasSum.mul_left (Real.exp (-(c / 2) * x))) hb
  simpa only [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (weightedGaussian_nonneg c x r))] using hsum

theorem sqrt_power_exp_bound (c x : ℝ) (p : ℕ) (hc : 0 < c) (hx : 1 ≤ x) :
    (Real.sqrt x) ^ p * Real.exp (-c * x) ≤
      (1 / c) ^ p * (2 : ℝ) ^ p * (Nat.factorial p : ℝ) := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hxsq : x ≤ x ^ 2 := by
    nlinarith only [mul_nonneg hx0 (sub_nonneg.mpr hx)]
  have hsqrt : Real.sqrt x ≤ x := by
    nlinarith only [Real.sq_sqrt hx0, Real.sqrt_nonneg x, hxsq, hx]
  have hm := nonneg_exp_monomial_profile (c * x) (mul_nonneg hc.le hx0) p
  have hscale : (1 / c) ^ p * (c * x) ^ p = x ^ p := by
    rw [← mul_pow]
    congr 1
    field_simp [ne_of_gt hc]
  have he : Real.exp (-(c * x) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hc.le hx0])
  calc
    _ ≤ x ^ p * Real.exp (-c * x) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.sqrt_nonneg x) hsqrt p) (Real.exp_nonneg _)
    _ = (1 / c) ^ p * ((c * x) ^ p * Real.exp (-(c * x))) := by
      rw [← mul_assoc, hscale, neg_mul]
    _ ≤ (1 / c) ^ p * ((2 : ℝ) ^ p * (Nat.factorial p : ℝ) * Real.exp (-(c * x) / 2)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ (1 / c) ^ p * ((2 : ℝ) ^ p * (Nat.factorial p : ℝ) * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity)
    _ = _ := by ring

theorem spectralConstant_nonneg (c : ℝ) (r : ℕ) (hc : 0 < c) :
    0 ≤ spectralConstant c r := by
  dsimp only [spectralConstant]
  exact mul_nonneg (by positivity) (tsum_nonneg (weightedGaussian_nonneg (c / 2) 1 r))

theorem weightedGaussian_scaled_bound (c x : ℝ) (r : ℕ) (hc : 0 < c) (hx : 1 ≤ x) :
    (Real.sqrt x) ^ (r + 1) * (∑' n : ℕ, weightedGaussian c r x n) ≤ spectralConstant c r := by
  have hs := weightedGaussian_tsum_split c x r hc hx
  have hm := sqrt_power_exp_bound (c / 2) x (r + 1) (by positivity) hx
  have hsum0 : 0 ≤ ∑' n : ℕ, weightedGaussian (c / 2) r 1 n :=
    tsum_nonneg (weightedGaussian_nonneg (c / 2) 1 r)
  calc
    _ ≤ (Real.sqrt x) ^ (r + 1) *
        (Real.exp (-(c / 2) * x) * (∑' n : ℕ, weightedGaussian (c / 2) r 1 n)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = ((Real.sqrt x) ^ (r + 1) * Real.exp (-(c / 2) * x)) *
        (∑' n : ℕ, weightedGaussian (c / 2) r 1 n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hm hsum0
    _ = _ := rfl

end Shao.C2.IntervalSpectralGaussian

