/- Mathematical candidate only: supplement.tex 4810--4856.
   One actual raw-population retained local bill. No production body/check. -/
import Shao.Probability.SourceActualIntervalProfileBudget
import Shao.Probability.SourceActualRegularPhysicalRatio
import Shao.C2.BridgeIntervalImageResolved
import Shao.C2.BridgeLowerIdentification
import Shao.C2.IntervalImageMixedIntSeries
import Shao.C2.IntervalImageRevealDerivatives
import Shao.C2.IntervalImageWallLimit
import Shao.C2.HalfLineTaylorRemainder

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.Probability.SourceActualRegularLocal
open MeasureTheory ProbabilityTheory
open SourcePermutationReveal SourceSeparatedOvershoot
open SourceActualLocalProfileBudget SourceActualIntervalProfileBudget
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open scoped BigOperators Classical
open scoped NNReal

/- Requested private analytic leaves; no bodies written before Root freeze.
   Same complete imports/options/namespace/open context as public frozen source. -/

private theorem arl_quarter_reflection_monomial
    (u v T : ℝ) (hu : 0 < u) (hv : 0 < v) (hT : 0 < T)
    (j m : ℕ) (hj : j ≤ 3) :
    let r : ℝ := 2 * u * v / T
    let h : ℝ := 2 * v / T
    let D : ℝ := 1 + |u - v| / Real.sqrt T
    h ^ j * r ^ m * Real.exp (-r) ≤
      (96 / Real.sqrt T * D) ^ j *
        ((8 : ℝ) ^ m * (Nat.factorial m : ℝ)) * Real.exp (-3 * r / 4) := by
  intro r h D
  have hr : 0 < r := by dsimp only [r]; positivity
  have hfac : 0 ≤ (Nat.factorial m : ℝ) := Nat.cast_nonneg _
  have hpow (p : ℝ) (k : ℕ) : (2 : ℝ) ^ k * (p / 2) ^ k = p ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  have he : Real.exp (-r / 2) * Real.exp (-r / 2) = Real.exp (-r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he3 : Real.exp (-r / 4) * Real.exp (-r / 2) = Real.exp (-3 * r / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  by_cases hj0 : j = 0
  · subst j
    simp only [pow_zero, one_mul]
    have hmono := Shao.C2.HalfLineTimeProfiles.nonneg_exp_monomial_profile
      (r / 2) (by positivity) m
    have hexp : Real.exp (-(r / 2) / 2) = Real.exp (-r / 4) := by
      congr 1
      ring
    rw [hexp] at hmono
    calc
      r ^ m * Real.exp (-r) =
          (2 : ℝ) ^ m * ((r / 2) ^ m * Real.exp (-r / 2)) * Real.exp (-r / 2) := by
        rw [← he, ← hpow r m]
        ring
      _ ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ m * (Nat.factorial m : ℝ) *
          Real.exp (-r / 4)) * Real.exp (-r / 2) := by
        simpa only [neg_div] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ (2 : ℝ) ^ m))
          (Real.exp_pos (-r / 2)).le
      _ = (4 : ℝ) ^ m * (Nat.factorial m : ℝ) * Real.exp (-3 * r / 4) := by
        rw [← he3, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
        ring
      _ ≤ (8 : ℝ) ^ m * (Nat.factorial m : ℝ) * Real.exp (-3 * r / 4) := by
        gcongr <;> norm_num
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    let D2 : ℝ := 1 + |u - v| / Real.sqrt (2 * T)
    let base : ℝ := 16 * (j : ℝ) / Real.sqrt (2 * T) * D2
    have hs := Shao.C2.HalfLineMixedProfiles.positive_reflection_power_monomial_profile
      u v (2 * T) hu hv (by positivity) j hjpos m
    have hh : 2 * v / (2 * T) = h / 2 := by
      dsimp only [h]
      field_simp
      <;> ring
    have hrr : 2 * u * v / (2 * T) = r / 2 := by
      dsimp only [r]
      field_simp
      <;> ring
    have harg : -2 * u * v / (2 * T) = -r / 2 := by
      dsimp only [r]
      field_simp
      <;> ring
    have harg' : -u * v / (2 * T) = -r / 4 := by
      dsimp only [r]
      field_simp
      <;> ring
    rw [hh, hrr, harg, harg'] at hs
    change (h / 2) ^ j * (r / 2) ^ m * Real.exp (-r / 2) ≤
      base ^ j * ((4 : ℝ) ^ m * (Nat.factorial m : ℝ)) * Real.exp (-r / 4) at hs
    have hscale : h ^ j * r ^ m * Real.exp (-r) ≤
        (2 * base) ^ j * ((8 : ℝ) ^ m * (Nat.factorial m : ℝ)) *
          Real.exp (-3 * r / 4) := by
      calc
        _ = (2 : ℝ) ^ (j + m) *
            ((h / 2) ^ j * (r / 2) ^ m * Real.exp (-r / 2)) * Real.exp (-r / 2) := by
          calc
            _ = ((2 : ℝ) ^ j * (h / 2) ^ j) * ((2 : ℝ) ^ m * (r / 2) ^ m) *
                (Real.exp (-r / 2) * Real.exp (-r / 2)) := by rw [hpow, hpow, he]
            _ = _ := by rw [pow_add]; ring
        _ ≤ (2 : ℝ) ^ (j + m) *
            (base ^ j * ((4 : ℝ) ^ m * (Nat.factorial m : ℝ)) * Real.exp (-r / 4)) *
              Real.exp (-r / 2) := by gcongr
        _ = _ := by
          have h8 : (8 : ℝ) ^ m = (2 : ℝ) ^ m * (4 : ℝ) ^ m := by
            rw [← mul_pow]
            norm_num
          dsimp only [base]
          rw [pow_add, mul_pow, h8, ← he3]
          have h32 : (32 : ℝ) ^ j = (2 : ℝ) ^ j * (16 : ℝ) ^ j := by
            rw [← mul_pow]
            norm_num
          ring_nf
          rw [h32]
          ring
    have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
    have hs2 : Real.sqrt T ≤ Real.sqrt (2 * T) :=
      Real.sqrt_le_sqrt (by linarith only [hT])
    have hD : D2 ≤ D := by
      dsimp only [D2, D]
      exact add_le_add le_rfl (div_le_div_of_nonneg_left (abs_nonneg _) hsT hs2)
    have hD2 : 0 ≤ D2 := by dsimp only [D2]; positivity
    have hjR : (j : ℝ) ≤ 3 := by exact_mod_cast hj
    have hco : 32 * (j : ℝ) / Real.sqrt (2 * T) ≤ 96 / Real.sqrt T := by
      calc
        _ ≤ 96 / Real.sqrt (2 * T) := by gcongr; linarith only [hjR]
        _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hsT hs2
    have hbase : 2 * base ≤ 96 / Real.sqrt T * D := by
      have hh := mul_le_mul hco hD hD2 (by positivity : 0 ≤ 96 / Real.sqrt T)
      dsimp only [base]
      convert hh using 1 <;> ring
    exact hscale.trans (by gcongr)

private theorem arl_far_mixed_clock_sum
    (j l : ℕ) (a y z T b theta : ℝ) (hl : l ≤ 3)
    (hT : 0 < T) (ha : 16 * Real.sqrt T ≤ a)
    (hy : |y| < a) (hz : |z| ≤ a)
    (hd : |z - y| ≤ (3 / 2 : ℝ) * a)
    (hb : b ^ 2 ≤ T / 2) (hnew : |y + b| ≤ a)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    let S : ℝ := T - theta * b ^ 2
    let Y : ℝ := y + theta * b
    let E : ℕ → ℝ := fun k =>
      |Shao.C2.IntervalImageMixedIntSeries.mixedImageA j l a z S Y ((k : ℤ) + 1)| +
      |Shao.C2.IntervalImageMixedIntSeries.mixedImageA j l a z S Y (-((k : ℤ) + 1))| +
      |Shao.C2.IntervalImageMixedIntSeries.mixedImageB j l a z S Y ((k : ℤ) + 1)| +
      |Shao.C2.IntervalImageMixedIntSeries.mixedImageB j l a z S Y (-((k : ℤ) + 2))|
    Summable E ∧ (∑' k : ℕ, E k) ≤
      (4 * Real.exp 2 + 4) * (12 * Real.sqrt 2) ^ j * (2 : ℝ) ^ l *
        Shao.C2.IntervalImageMixedTerms.mixedTimeConstant j l *
          (1 / Real.sqrt T) ^ (j + 2 * l) *
            (1 + |z - y| / Real.sqrt T) ^ j * Real.exp (-(a ^ 2) / T) := by
  intro S Y E
  have hSall := Shao.C2.HalfLineTaylorSegment.segment_energy_bounds
    T b theta hT hb htheta0 htheta1
  have hS : 0 < S := hSall.1
  have hhalf : T / 2 ≤ S := hSall.2.1
  have hST : S ≤ T := hSall.2.2
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hsS : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
  have ha0 : 0 < a := (mul_pos (by norm_num) hsT).trans_le ha
  have hY : |Y| ≤ a := Shao.C2.IntervalImageTaylorSegment.segment_space_closed
    a y b theta hy hnew htheta0 htheta1
  have htime : 4 * T ≤ a ^ 2 := by
    nlinarith only [ha, Real.sq_sqrt hT.le, Real.sqrt_nonneg T]
  have hdrift : |z - Y| ≤ (3 / 2 : ℝ) * a + theta * |b| := by
    have hh : |(z - y) - theta * b| ≤ |z - y| + theta * |b| := by
      simpa only [sub_eq_add_neg, abs_neg, abs_mul, abs_of_nonneg htheta0] using
        abs_add_le (z - y) (-(theta * b))
    have he : z - Y = (z - y) - theta * b := by dsimp only [Y]; ring
    rw [he]
    linarith only [hh, hd]
  let M : ℝ := Shao.C2.IntervalImageMixedTerms.mixedTimeConstant j l
  let PS : ℝ := (4 / Real.sqrt S * (1 + |z - Y| / Real.sqrt S)) ^ j * M / S ^ l
  let PT : ℝ := (12 * Real.sqrt 2) ^ j * (2 : ℝ) ^ l * M *
    (1 / Real.sqrt T) ^ (j + 2 * l) * (1 + |z - y| / Real.sqrt T) ^ j
  have hM : 0 ≤ M := Shao.C2.IntervalImageMixedTerms.mixedTimeConstant_nonneg j l
  have hPS : 0 ≤ PS := by dsimp only [PS]; positivity
  have hPT : 0 ≤ PT := by dsimp only [PT]; positivity
  have hInv : 1 / Real.sqrt S ≤ Real.sqrt 2 / Real.sqrt T := by
    have hq : (Real.sqrt 2 * Real.sqrt S) ^ 2 = 2 * S := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hS.le]
    have hh : Real.sqrt T ≤ Real.sqrt 2 * Real.sqrt S := by
      nlinarith only [hq, Real.sq_sqrt hT.le, hhalf, Real.sqrt_nonneg T,
        mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg S)]
    exact (div_le_div_iff₀ hsS hsT).2 (by simpa only [one_mul] using hh)
  have hD := Shao.C2.HalfLineTaylorSegment.segment_displacement_bound
    (z - y) T b theta hT hb htheta0 htheta1
  change 1 + |(z - y) - theta * b| / Real.sqrt S ≤ _ at hD
  have hDY : 1 + |z - Y| / Real.sqrt S ≤ 3 * (1 + |z - y| / Real.sqrt T) := by
    convert hD using 1 <;> dsimp only [Y] <;> ring
  have hspace : 4 / Real.sqrt S * (1 + |z - Y| / Real.sqrt S) ≤
      (12 * Real.sqrt 2) * (1 / Real.sqrt T) * (1 + |z - y| / Real.sqrt T) := by
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hInv (by norm_num : (0 : ℝ) ≤ 4))
      hDY (by positivity : 0 ≤ 1 + |z - Y| / Real.sqrt S) (by positivity)
    convert hh using 1 <;> ring
  have hInvTime : 1 / S ≤ 2 / T :=
    (div_le_div_iff₀ hS hT).2 (by linarith only [hhalf])
  have hscale : PS ≤ PT := by
    have hp := mul_le_mul
      (pow_le_pow_left₀ (by positivity) hspace j)
      (pow_le_pow_left₀ (by positivity) hInvTime l) (by positivity) (by positivity)
    have hpM := mul_le_mul_of_nonneg_left hp hM
    have hsq : (1 / Real.sqrt T) ^ 2 = 1 / T := by
      rw [one_div_pow, Real.sq_sqrt hT.le]
    dsimp only [PS, PT]
    calc
      _ = M * ((4 / Real.sqrt S * (1 + |z - Y| / Real.sqrt S)) ^ j * (1 / S) ^ l) := by
        rw [one_div_pow]
        ring
      _ ≤ M * (((12 * Real.sqrt 2) * (1 / Real.sqrt T) *
          (1 + |z - y| / Real.sqrt T)) ^ j * (2 / T) ^ l) := hpM
      _ = _ := by
        rw [pow_add, pow_mul, hsq, mul_pow, mul_pow, div_pow, one_div_pow]
        ring
  have hAlog (m : ℤ) (k : ℝ) (hk : 1 ≤ k) (hm : |(m : ℝ)| = k) :
      k ^ 2 * a ^ 2 / T - 2 ≤
        Shao.C2.IntervalImageExponents.imageA a Y z (m : ℝ) / (2 * S) := by
    have hk0 : 0 ≤ k := by linarith only [hk]
    have hk1 : 0 ≤ k - 1 := sub_nonneg.2 hk
    have hm2 : (m : ℝ) ^ 2 = k ^ 2 := by rw [← sq_abs (m : ℝ), hm]
    have hn := neg_abs_le ((m : ℝ) * (z - Y))
    rw [abs_mul, hm] at hn
    have hdM := mul_le_mul_of_nonneg_left hdrift hk0
    have hlow : (8 * k ^ 2 - 6 * k) * a ^ 2 - 4 * k * a * theta * |b| ≤
        Shao.C2.IntervalImageExponents.imageA a Y z (m : ℝ) := by
      have hsum : -(k * ((3 / 2 : ℝ) * a + theta * |b|)) ≤ (m : ℝ) * (z - Y) := by
        linarith only [hn, hdM]
      have hmA := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 4 * a)
      dsimp only [Shao.C2.IntervalImageExponents.imageA]
      rw [hm2]
      nlinarith only [hmA]
    have hpos1 : 0 ≤ 6 * k * (k - 1) * a ^ 2 * T := by positivity
    have hpos2 : 0 ≤ 2 * theta * (k * a * |b| - T) ^ 2 := by positivity
    have htT : theta * T ≤ T := by simpa only [one_mul] using mul_le_mul_of_nonneg_right htheta1 hT.le
    have hpos3 : 0 ≤ (4 * S - 2 * theta * T) * T := by
      exact mul_nonneg (by linarith only [hhalf, htT]) hT.le
    have hid : ((8 * k ^ 2 - 6 * k) * a ^ 2 - 4 * k * a * theta * |b|) * T -
        2 * S * (k ^ 2 * a ^ 2 - 2 * T) =
          6 * k * (k - 1) * a ^ 2 * T +
            2 * theta * (k * a * |b| - T) ^ 2 + (4 * S - 2 * theta * T) * T := by
      dsimp only [S]
      rw [← sq_abs b]
      ring
    have hcross : 2 * S * (k ^ 2 * a ^ 2 - 2 * T) ≤
        Shao.C2.IntervalImageExponents.imageA a Y z (m : ℝ) * T := by
      have hh := mul_le_mul_of_nonneg_right hlow hT.le
      nlinarith only [hid, hpos1, hpos2, hpos3, hh]
    have hh : (k ^ 2 * a ^ 2 - 2 * T) / T ≤
        Shao.C2.IntervalImageExponents.imageA a Y z (m : ℝ) / (2 * S) :=
      (div_le_div_iff₀ hT (by positivity : 0 < 2 * S)).2 (by nlinarith only [hcross])
    convert hh using 1 <;> field_simp <;> ring
  have hNat (k : ℕ) :
      a ^ 2 / T + 4 * (k : ℝ) ≤ ((k : ℝ) + 1) ^ 2 * a ^ 2 / T := by
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hquad : (k : ℝ) ≤ ((k : ℝ) + 1) ^ 2 - 1 := by nlinarith only [sq_nonneg (k : ℝ)]
    have hh1 := mul_le_mul_of_nonneg_left htime hk
    have hh2 := mul_le_mul_of_nonneg_right hquad (sq_nonneg a)
    apply (le_div_iff₀ hT).2
    have he : (a ^ 2 / T + 4 * (k : ℝ)) * T = a ^ 2 + 4 * (k : ℝ) * T := by
      field_simp
    rw [he]
    nlinarith only [hh1, hh2]
  have hExp (C0 : ℝ) (k : ℕ)
      (hlog : a ^ 2 / T + 4 * (k : ℝ) - 2 ≤ C0 / (2 * S)) :
      Real.exp (-C0 / (2 * S)) ≤
        Real.exp 2 * Real.exp (-(a ^ 2) / T) * Real.exp (-4) ^ k := by
    have hh := Real.exp_le_exp.2 (neg_le_neg hlog)
    have he : Real.exp (-(a ^ 2 / T + 4 * (k : ℝ) - 2)) =
        Real.exp 2 * Real.exp (-(a ^ 2) / T) * Real.exp (-4) ^ k := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    simpa only [neg_div, he] using hh
  have hBExp (m : ℤ) (k : ℕ)
      (hC : 8 * ((k : ℝ) + 1) ^ 2 * a ^ 2 ≤ Shao.C2.IntervalImageExponents.imageB a Y z (m : ℝ)) :
      Real.exp (-Shao.C2.IntervalImageExponents.imageB a Y z (m : ℝ) / (2 * S)) ≤
        Real.exp (-(a ^ 2) / T) * Real.exp (-4) ^ k := by
    have hC0 : 0 ≤ Shao.C2.IntervalImageExponents.imageB a Y z (m : ℝ) :=
      le_trans (by positivity : 0 ≤ 8 * ((k : ℝ) + 1) ^ 2 * a ^ 2) hC
    have hratio : 4 * ((k : ℝ) + 1) ^ 2 * a ^ 2 / T ≤
        Shao.C2.IntervalImageExponents.imageB a Y z (m : ℝ) / (2 * S) := by
      calc
        _ = (8 * ((k : ℝ) + 1) ^ 2 * a ^ 2) / (2 * T) := by ring
        _ ≤ Shao.C2.IntervalImageExponents.imageB a Y z (m : ℝ) / (2 * T) := by gcongr
        _ ≤ _ := div_le_div_of_nonneg_left hC0 (by positivity) (by linarith only [hST])
    have hknon : 0 ≤ ((k : ℝ) + 1) ^ 2 * a ^ 2 / T := by positivity
    have hlog : a ^ 2 / T + 4 * (k : ℝ) ≤
        Shao.C2.IntervalImageExponents.imageB a Y z (m : ℝ) / (2 * S) := by
      have he4 : 4 * (((k : ℝ) + 1) ^ 2 * a ^ 2 / T) ≤
          Shao.C2.IntervalImageExponents.imageB a Y z (m : ℝ) / (2 * S) := by
        convert hratio using 1 <;> ring
      linarith only [hNat k, he4, hknon]
    have hh := Real.exp_le_exp.2 (neg_le_neg hlog)
    have he : Real.exp (-(a ^ 2 / T + 4 * (k : ℝ))) =
        Real.exp (-(a ^ 2) / T) * Real.exp (-4) ^ k := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    simpa only [neg_div, he] using hh
  let B0 : ℝ := (2 * Real.exp 2 + 2) * PS * Real.exp (-(a ^ 2) / T)
  have hB0 : 0 ≤ B0 := by dsimp only [B0]; positivity
  have hpoint (k : ℕ) : E k ≤ B0 * Real.exp (-4) ^ k := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith only [hk0]
    have hmp : |(((k : ℤ) + 1 : ℤ) : ℝ)| = (k : ℝ) + 1 := by
      push_cast
      exact abs_of_nonneg (by positivity)
    have hmn : |((-((k : ℤ) + 1) : ℤ) : ℝ)| = (k : ℝ) + 1 := by
      push_cast
      rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ (k : ℝ) + 1)]
    have hAp := hExp _ k (by linarith only [hAlog ((k : ℤ) + 1) _ hk hmp, hNat k])
    have hAn := hExp _ k (by linarith only [hAlog (-((k : ℤ) + 1)) _ hk hmn, hNat k])
    have hBpCore := Shao.C2.IntervalImageExponents.imageB_positive_tail
      a Y z ((k : ℝ) + 1) ha0 hY hz (by positivity)
    have hBnCore := Shao.C2.IntervalImageExponents.imageB_negative_tail
      a Y z ((k : ℝ) + 1) ha0 hY hz (by positivity)
    have hBp := hBExp ((k : ℤ) + 1) k (by
      push_cast
      have hn := Shao.C2.IntervalImageExponents.imageB_nonneg a Y z 0 ha0 hY hz
      norm_num at hn
      linarith only [hBpCore, hn])
    have hBn := hBExp (-((k : ℤ) + 2)) k (by
      push_cast
      have he : -((k : ℝ) + 2) = -((k : ℝ) + 1) - 1 := by ring
      rw [he]
      have hn := Shao.C2.IntervalImageExponents.imageB_nonneg a Y z (-1) ha0 hY hz
      norm_num at hn
      linarith only [hBnCore, hn])
    have h1 := (Shao.C2.IntervalImageMixedTerms.spatialImageA_mixed_profile
      j l a z S Y ((k : ℤ) + 1) hl ha0 hz hS hY).trans (mul_le_mul_of_nonneg_left hAp hPS)
    have h2 := (Shao.C2.IntervalImageMixedTerms.spatialImageA_mixed_profile
      j l a z S Y (-((k : ℤ) + 1)) hl ha0 hz hS hY).trans (mul_le_mul_of_nonneg_left hAn hPS)
    have h3 := (Shao.C2.IntervalImageMixedTerms.spatialImageB_mixed_profile
      j l a z S Y ((k : ℤ) + 1) hl ha0 hz hS hY).trans (mul_le_mul_of_nonneg_left hBp hPS)
    have h4 := (Shao.C2.IntervalImageMixedTerms.spatialImageB_mixed_profile
      j l a z S Y (-((k : ℤ) + 2)) hl ha0 hz hS hY).trans (mul_le_mul_of_nonneg_left hBn hPS)
    change _ ≤ _ at h1 h2 h3 h4
    dsimp only [E, B0, Shao.C2.IntervalImageMixedIntSeries.mixedImageA,
      Shao.C2.IntervalImageMixedIntSeries.mixedImageB]
    nlinarith only [h1, h2, h3, h4]
  have hg := Shao.C2.IntervalImageSmallTimeTails.geometric_four_sum_bound
  have hsum : Summable E := (hg.1.mul_left B0).of_nonneg_of_le
    (fun k => by dsimp only [E]; positivity) hpoint
  refine ⟨hsum, ?_⟩
  have hh := hsum.tsum_le_tsum hpoint (hg.1.mul_left B0)
  rw [hg.1.tsum_mul_left] at hh
  have hbound := mul_le_mul_of_nonneg_left hg.2 hB0
  have hscaled := mul_le_mul_of_nonneg_left hscale
    (by positivity : 0 ≤ (4 * Real.exp 2 + 4) * Real.exp (-(a ^ 2) / T))
  change (∑' k : ℕ, E k) ≤ _
  dsimp only [B0] at hh hbound
  dsimp only [PT, M] at hscaled
  nlinarith only [hh, hbound, hscaled]

private theorem arl_far_cancelled_value
    (a Y z S T : ℝ) (hT : 0 < T) (ha : 16 * Real.sqrt T ≤ a)
    (hS : 0 < S) (hST : S ≤ T) (hY : |Y| ≤ a) (hz : |z| ≤ a)
    (hd : |z - Y| ≤ (25 / 16 : ℝ) * a) :
    let Z : ℝ := 1 + Shao.C2.IntervalImageCandidateSpatial.intervalImageCandidate a z S Y -
      Shao.C2.HalfLineReflectionFormula.upperReflection a Y S z -
      Shao.C2.HalfLineReflectionFormula.lowerReflection a Y S z
    |Z| ≤ 8 * Real.exp (-(a ^ 2) / T) := by
  intro Z
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have ha0 : 0 < a := (mul_pos (by norm_num) hsT).trans_le ha
  have htime : 4 * T ≤ a ^ 2 := by
    nlinarith only [ha, Real.sq_sqrt hT.le, Real.sqrt_nonneg T]
  let e0 : ℝ := Real.exp (-(a ^ 2) / T)
  let g : ℝ := Real.exp (-4)
  have he0 : 0 < e0 := Real.exp_pos _
  have hg0 : 0 < g := Real.exp_pos _
  have hghalf : g ≤ (1 / 2 : ℝ) := by
    have hh : (2 : ℝ) ≤ Real.exp 4 := by linarith only [Real.add_one_le_exp (4 : ℝ)]
    dsimp only [g]
    rw [Real.exp_neg, inv_eq_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hh
  have hA (m : ℤ) (k : ℝ) (hk : 1 ≤ k) (hm : |(m : ℝ)| = k) :
      k ^ 2 * a ^ 2 ≤ Shao.C2.IntervalImageExponents.imageA a Y z (m : ℝ) := by
    have hk0 : 0 ≤ k := by linarith only [hk]
    have hk7 : 0 ≤ 7 * k - (25 / 4 : ℝ) := by linarith only [hk]
    have hm2 : (m : ℝ) ^ 2 = k ^ 2 := by rw [← sq_abs (m : ℝ), hm]
    have hn := neg_abs_le ((m : ℝ) * (z - Y))
    rw [abs_mul, hm] at hn
    have hh := mul_le_mul_of_nonneg_left hd hk0
    have hh' : -((25 / 16 : ℝ) * k * a) ≤ (m : ℝ) * (z - Y) := by
      nlinarith only [hn, hh]
    have hmul := mul_le_mul_of_nonneg_left hh' (by positivity : 0 ≤ 4 * a)
    have hpos : 0 ≤ k * (7 * k - (25 / 4 : ℝ)) * a ^ 2 := by positivity
    dsimp only [Shao.C2.IntervalImageExponents.imageA]
    rw [hm2]
    nlinarith only [hmul, hpos]
  have hNat (k : ℕ) :
      a ^ 2 / T + 4 * (k : ℝ) ≤ ((k : ℝ) + 1) ^ 2 * a ^ 2 / T := by
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hquad : (k : ℝ) ≤ ((k : ℝ) + 1) ^ 2 - 1 := by nlinarith only [sq_nonneg (k : ℝ)]
    have hh1 := mul_le_mul_of_nonneg_left htime hk
    have hh2 := mul_le_mul_of_nonneg_right hquad (sq_nonneg a)
    apply (le_div_iff₀ hT).2
    have he : (a ^ 2 / T + 4 * (k : ℝ)) * T = a ^ 2 + 4 * (k : ℝ) * T := by field_simp
    rw [he]
    nlinarith only [hh1, hh2]
  have hExp (C0 : ℝ) (k : ℕ) (hC : ((k : ℝ) + 1) ^ 2 * a ^ 2 ≤ C0) :
      Real.exp (-C0 / S) ≤ e0 * g ^ k := by
    have hC0 : 0 ≤ C0 := le_trans (by positivity) hC
    have hh : ((k : ℝ) + 1) ^ 2 * a ^ 2 / T ≤ C0 / S := by
      calc
        _ ≤ C0 / T := (div_le_div_iff_of_pos_right hT).2 hC
        _ ≤ _ := div_le_div_of_nonneg_left hC0 hS hST
    have hlog := (hNat k).trans hh
    have he : Real.exp (-(a ^ 2 / T + 4 * (k : ℝ))) = e0 * g ^ k := by
      dsimp only [e0, g]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    simpa only [neg_div, he] using Real.exp_le_exp.2 (neg_le_neg hlog)
  have hApositive (k : ℕ) :
      Real.exp (-Shao.C2.IntervalImageExponents.imageA a Y z ((k : ℤ) + 1 : ℤ) / S) ≤ e0 * g ^ k := by
    apply hExp _ k
    apply hA _ ((k : ℝ) + 1)
    · have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith only [hk]
    · push_cast
      exact abs_of_nonneg (by positivity)
  have hAnegative (k : ℕ) :
      Real.exp (-Shao.C2.IntervalImageExponents.imageA a Y z (-((k : ℤ) + 1) : ℤ) / S) ≤ e0 * g ^ k := by
    apply hExp _ k
    apply hA _ ((k : ℝ) + 1)
    · have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith only [hk]
    · push_cast
      rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ (k : ℝ) + 1)]
  have hBpositive (k : ℕ) :
      Real.exp (-Shao.C2.IntervalImageExponents.imageB a Y z ((k : ℤ) + 1 : ℤ) / S) ≤ e0 * g ^ k := by
    apply hExp _ k
    have ht := Shao.C2.IntervalImageExponents.imageB_positive_tail
      a Y z ((k : ℝ) + 1) ha0 hY hz (by positivity)
    have hn := Shao.C2.IntervalImageExponents.imageB_nonneg a Y z 0 ha0 hY hz
    norm_num at hn
    push_cast
    nlinarith only [ht, hn, sq_nonneg (((k : ℝ) + 1) * a)]
  have hBnegative (k : ℕ) :
      Real.exp (-Shao.C2.IntervalImageExponents.imageB a Y z (-((k : ℤ) + 2) : ℤ) / S) ≤ e0 * g ^ k := by
    apply hExp _ k
    have ht := Shao.C2.IntervalImageExponents.imageB_negative_tail
      a Y z ((k : ℝ) + 1) ha0 hY hz (by positivity)
    have hn := Shao.C2.IntervalImageExponents.imageB_nonneg a Y z (-1) ha0 hY hz
    norm_num at hn
    push_cast
    have he : -((k : ℝ) + 2) = -((k : ℝ) + 1) - 1 := by ring
    rw [he]
    nlinarith only [ht, hn, sq_nonneg (((k : ℝ) + 1) * a)]
  let tail : ℕ → ℝ := Shao.C2.IntervalImageMixedConvergence.mixedTailBlock 0 0 a z S Y
  have hb (k : ℕ) : ‖tail k‖ ≤ (3 * e0) * g ^ k := by
    have hAp : Real.exp (-Shao.C2.IntervalImageExponents.imageA a Y z ((k : ℤ) + 2 : ℤ) / S) ≤
        (1 / 2 : ℝ) * e0 * g ^ k := by
      have hh : Real.exp (-Shao.C2.IntervalImageExponents.imageA a Y z ((k : ℤ) + 2 : ℤ) / S) ≤
          e0 * g ^ (k + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hApositive (k + 1)
      rw [pow_succ] at hh
      have hmul := mul_le_mul_of_nonneg_left hghalf (by positivity : 0 ≤ e0 * g ^ k)
      nlinarith only [hh, hmul]
    have hAn : Real.exp (-Shao.C2.IntervalImageExponents.imageA a Y z (-((k : ℤ) + 2) : ℤ) / S) ≤
        (1 / 2 : ℝ) * e0 * g ^ k := by
      have hh : Real.exp (-Shao.C2.IntervalImageExponents.imageA a Y z (-((k : ℤ) + 2) : ℤ) / S) ≤
          e0 * g ^ (k + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hAnegative (k + 1)
      rw [pow_succ] at hh
      have hmul := mul_le_mul_of_nonneg_left hghalf (by positivity : 0 ≤ e0 * g ^ k)
      nlinarith only [hh, hmul]
    have hBp := hBpositive k
    have hBn := hBnegative k
    simp only [tail, Shao.C2.IntervalImageMixedConvergence.mixedTailBlock,
      iteratedDeriv_zero, Shao.C2.IntervalImageIntSeries.spatialImageA,
      Shao.C2.IntervalImageIntSeries.spatialImageB]
    rw [Real.norm_eq_abs]
    have h1 := Real.exp_pos (-Shao.C2.IntervalImageExponents.imageA a Y z ((k : ℤ) + 2 : ℤ) / S)
    have h2 := Real.exp_pos (-Shao.C2.IntervalImageExponents.imageA a Y z (-((k : ℤ) + 2) : ℤ) / S)
    have h3 := Real.exp_pos (-Shao.C2.IntervalImageExponents.imageB a Y z ((k : ℤ) + 1 : ℤ) / S)
    have h4 := Real.exp_pos (-Shao.C2.IntervalImageExponents.imageB a Y z (-((k : ℤ) + 2) : ℤ) / S)
    apply abs_le.2
    constructor <;> nlinarith only [hAp, hAn, hBp, hBn, h1, h2, h3, h4]
  have hg := Shao.C2.IntervalImageSmallTimeTails.geometric_four_sum_bound
  have hbound : |Shao.C2.IntervalImageMixedConvergence.mixedTailSum 0 0 a z S Y| ≤ 6 * e0 := by
    have hh : ‖∑' k : ℕ, tail k‖ ≤ (3 * e0) * (∑' k : ℕ, g ^ k) :=
      ((hg.1.mul_left (3 * e0)).of_norm_bounded hb).hasSum.norm_le_of_bounded
        (hg.1.hasSum.mul_left (3 * e0)) hb
    have hn := mul_le_mul_of_nonneg_left hg.2 (by positivity : 0 ≤ 3 * e0)
    change |∑' k : ℕ, tail k| ≤ _
    rw [Real.norm_eq_abs] at hh
    change (3 * e0) * (∑' k : ℕ, g ^ k) ≤ (3 * e0) * 2 at hn
    nlinarith only [hh, hn]
  have hm := Shao.C2.IntervalImageMixedCandidate.mixedImageCandidate_zero 0 a z S Y
  simp only [Shao.C2.IntervalImageMixedCandidate.mixedImageCandidate,
    Shao.C2.IntervalImageMixedCandidate.mixedFiniteImages, iteratedDeriv_zero,
    Shao.C2.IntervalImageIntSeries.spatialImageA, Shao.C2.IntervalImageIntSeries.spatialImageB,
    Int.cast_zero, Int.cast_one, Int.cast_neg, Shao.C2.IntervalImageExponents.imageA_zero,
    neg_zero, zero_div, Real.exp_zero] at hm
  have hBzero : Real.exp (-Shao.C2.IntervalImageExponents.imageB a Y z 0 / S) =
      Real.exp (-2 * (a + Y) * (a + z) / S) := by
    congr 1
    dsimp only [Shao.C2.IntervalImageExponents.imageB]
    ring
  have hBminus : Real.exp (-Shao.C2.IntervalImageExponents.imageB a Y z (-1) / S) =
      Real.exp (-2 * (a - Y) * (a - z) / S) := by
    congr 1
    dsimp only [Shao.C2.IntervalImageExponents.imageB]
    ring
  have hZ : Z = Real.exp (-Shao.C2.IntervalImageExponents.imageA a Y z 1 / S) +
      Real.exp (-Shao.C2.IntervalImageExponents.imageA a Y z (-1) / S) +
        Shao.C2.IntervalImageMixedConvergence.mixedTailSum 0 0 a z S Y := by
    dsimp only [Z, Shao.C2.IntervalImageCandidateSpatial.intervalImageCandidate,
      Shao.C2.HalfLineReflectionFormula.upperReflection, Shao.C2.HalfLineReflectionFormula.lowerReflection]
    rw [← hm, hBzero, hBminus]
    ring
  have hAp := hApositive 0
  have hAn := hAnegative 0
  norm_num at hAp hAn
  rw [hZ]
  have hsum := abs_add_le
    (Real.exp (-Shao.C2.IntervalImageExponents.imageA a Y z 1 / S) +
      Real.exp (-Shao.C2.IntervalImageExponents.imageA a Y z (-1) / S))
    (Shao.C2.IntervalImageMixedConvergence.mixedTailSum 0 0 a z S Y)
  have hpos : 0 ≤ Real.exp (-Shao.C2.IntervalImageExponents.imageA a Y z 1 / S) +
      Real.exp (-Shao.C2.IntervalImageExponents.imageA a Y z (-1) / S) := by positivity
  rw [abs_of_nonneg hpos] at hsum
  change _ ≤ 8 * e0
  linarith only [hAp, hAn, hsum, hbound]

theorem actual_regular_retained_local_cubic_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : ℝ≥0 → ΩB → ℝ), IsBrownianReal B PB →
        let Q : Measure BridgeNoise := bridgeLaw B PB
        ∀ {n : ℕ} (pop : Shao.Path n) (x : ℝ)
          (σ : LabelPerm n) (r : Fin n),
          let a : ℝ := actualWall pop x
          let y : ℝ := Shao.prefixSum (Spitzer.reorder pop σ) r.val
          let T : ℝ := remainingEnergy pop r.val σ
          let z : ℝ := Shao.prefixSum pop n
          let b : ℝ := pop (σ r)
          16 ≤ x →
          (∀ k : ℕ, k ≤ r.val →
            |Shao.prefixSum (Spitzer.reorder pop σ) k| < a) →
          0 < T → |z - y| ≤ (3 / 2 : ℝ) * x * Real.sqrt T →
          let F : MonitoredDomain → BridgeKernel := fun J => eventCompletionKernel J Q
          let FY : MonitoredDomain → BridgeKernel := fun J => match J with
            | .upper => halflineDerivative .upper
            | .lower => halflineDerivative .lower
            | .interval => intervalDerivative Q
          let L : ℝ :=
            sourceRetainedRemainder .interval (F .interval) (FY .interval)
              pop x (fun _ => n) r.val σ -
            sourceRetainedRemainder .upper (F .upper) (FY .upper)
              pop x (fun _ => n) r.val σ -
            sourceRetainedRemainder .lower (F .lower) (FY .lower)
              pop x (fun _ => n) r.val σ
          let D : ℝ := 1 + |z - y| / Real.sqrt T
          |L| ≤ C * (|b| / Real.sqrt T) ^ 3 * D ^ 3 * Real.exp (-(a ^ 2) / T) := by
  classical
  let W : ℝ := 4 * Real.exp 2 + 4
  let K : ℕ → ℕ → ℝ := fun j l =>
    W * (12 * Real.sqrt 2) ^ j * (2 : ℝ) ^ l *
      Shao.C2.IntervalImageMixedTerms.mixedTimeConstant j l
  let P : ℕ → ℕ → ℝ := fun j m =>
    (96 : ℝ) ^ j * (8 : ℝ) ^ m * (Nat.factorial m : ℝ)
  let N : ℕ → ℕ → ℝ := fun j l => match j, l with
    | 1, 0 => P 1 0
    | 3, 0 => P 3 0
    | 2, 1 => 2 * P 2 0 + P 2 1
    | 1, 2 => 2 * P 1 0 + 4 * P 1 1 + P 1 2
    | 0, 3 => 6 * P 0 1 + 6 * P 0 2 + P 0 3
    | 1, 1 => P 1 0 + P 1 1
    | 0, 2 => 2 * P 0 1 + P 0 2
    | _, _ => 0
  let H : ℕ → ℕ → ℝ := fun j l =>
    (3 * Real.sqrt 2) ^ j * (2 : ℝ) ^ l * N j l
  let Bill : (ℕ → ℕ → ℝ) → ℝ := fun J =>
    (J 3 0 + 3 * J 2 1 + 3 * J 1 2 + J 0 3) / 6 + J 1 1 + J 0 2 / 2
  let G : ℝ := K 1 0 + H 1 0
  let C : ℝ := 1 + Bill K + 2 * Bill H + 32 * Real.sqrt 2 + 2 * G
  have hC : 0 < C := by
    dsimp only [C, G, Bill, K, H, N, P, W]
    norm_num [Shao.C2.IntervalImageMixedTerms.mixedTimeConstant,
      Shao.C2.IntervalImageTimeProfiles.mixedFirstConstant,
      Shao.C2.IntervalImageHigherTime.mixedSecondConstant,
      Shao.C2.IntervalImageHigherTime.mixedThirdConstant]
    positivity
  refine ⟨C, hC, ?_⟩
  intro ΩB _ PB _ B hB Q n pop x sigma r a y T z b hx hbefore hT hd F FY L D
  have hgeom := remaining_population_geometry pop r.val r.is_lt.le sigma
  have hb2 : b ^ 2 ≤ T := hgeom.2.2.1 r le_rfl
  have hTtotal : T ≤ Shao.energy pop := by
    dsimp only [T, remainingEnergy]
    apply sub_le_self
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (Spitzer.reorder pop sigma i))
  have henergy : 0 < Shao.energy pop := hT.trans_le hTtotal
  have hx0 : 0 < x := by linarith only [hx]
  have hax : x * Real.sqrt T ≤ a := by
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hTtotal) hx0.le
  have ha16 : 16 * Real.sqrt T ≤ a :=
    (mul_le_mul_of_nonneg_right hx (Real.sqrt_nonneg T)).trans hax
  have ha : 0 < a := (mul_pos (by norm_num) (Real.sqrt_pos.2 hT)).trans_le ha16
  have hy : |y| < a := hbefore r.val le_rfl
  have hda : |z - y| ≤ (3 / 2 : ℝ) * a :=
    hd.trans (by nlinarith only [hax])
  have hbabs : |b| ≤ Real.sqrt T := by
    nlinarith only [hb2, sq_abs b, Real.sq_sqrt hT.le,
      abs_nonneg b, Real.sqrt_nonneg T]
  have hba : |b| ≤ a / 16 := by linarith only [hbabs, ha16]
  have hnewT : 0 ≤ T - b ^ 2 := sub_nonneg.2 hb2
  have hzero : T - b ^ 2 = 0 → y + b = z :=
    actual_reveal_zero_future_reachable pop r sigma
  have hpre (J : MonitoredDomain) :
      ∀ k : ℕ, k ≤ r.val → Interior J a (Shao.prefixSum (Spitzer.reorder pop sigma) k) := by
    intro k hk
    have hh := abs_lt.mp (hbefore k hk)
    cases J with
    | upper => exact hh.2
    | lower => exact hh.1
    | interval => exact hh
  have halive (J : MonitoredDomain) :
      sourceAlive J pop x r.val sigma ↔ Interior J a z := by
    constructor
    · intro h
      exact h.2.1
    · intro h
      exact ⟨henergy, h, hpre J⟩
  let M : ℕ → ℕ → ℝ → ℝ → ℝ := fun j l Y S =>
    Shao.C2.IntervalImageMixedCandidate.mixedImageCandidate j l a z S Y -
      (if j = 0 ∧ l = 0 then 1 else 0) +
        Shao.C2.IntervalImageMixedIntSeries.mixedImageB j l a z S Y 0 +
          Shao.C2.IntervalImageMixedIntSeries.mixedImageB j l a z S Y (-1)
  have hMbound (j l : ℕ) (q theta : ℝ) (hl : l ≤ 3)
      (hz : |z| ≤ a) (hq : q ^ 2 ≤ T / 2) (hnew : |y + q| ≤ a)
      (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
      |M j l (y + theta * q) (T - theta * q ^ 2)| ≤
        K j l * (1 / Real.sqrt T) ^ (j + 2 * l) * D ^ j * Real.exp (-(a ^ 2) / T) := by
    let S : ℝ := T - theta * q ^ 2
    let Y : ℝ := y + theta * q
    let A1 : ℕ → ℝ := fun k =>
      Shao.C2.IntervalImageMixedIntSeries.mixedImageA j l a z S Y ((k : ℤ) + 1)
    let A2 : ℕ → ℝ := fun k =>
      Shao.C2.IntervalImageMixedIntSeries.mixedImageA j l a z S Y (-((k : ℤ) + 1))
    let B1 : ℕ → ℝ := fun k =>
      Shao.C2.IntervalImageMixedIntSeries.mixedImageB j l a z S Y ((k : ℤ) + 1)
    let B2 : ℕ → ℝ := fun k =>
      Shao.C2.IntervalImageMixedIntSeries.mixedImageB j l a z S Y (-((k : ℤ) + 2))
    let E : ℕ → ℝ := fun k => |A1 k| + |A2 k| + |B1 k| + |B2 k|
    obtain ⟨hE, hEbound⟩ := arl_far_mixed_clock_sum j l a y z T q theta hl hT ha16
      hy hz hda hq hnew htheta0 htheta1
    change Summable E at hE
    have hA1 : Summable A1 := hE.of_norm_bounded (fun k => by
      rw [Real.norm_eq_abs];dsimp only [E];linarith only [abs_nonneg (A2 k), abs_nonneg (B1 k), abs_nonneg (B2 k)])
    have hA2 : Summable A2 := hE.of_norm_bounded (fun k => by
      rw [Real.norm_eq_abs];dsimp only [E];linarith only [abs_nonneg (A1 k), abs_nonneg (B1 k), abs_nonneg (B2 k)])
    have hB1 : Summable B1 := hE.of_norm_bounded (fun k => by
      rw [Real.norm_eq_abs];dsimp only [E];linarith only [abs_nonneg (A1 k), abs_nonneg (A2 k), abs_nonneg (B2 k)])
    have hB2 : Summable B2 := hE.of_norm_bounded (fun k => by
      rw [Real.norm_eq_abs];dsimp only [E];linarith only [abs_nonneg (A1 k), abs_nonneg (A2 k), abs_nonneg (B1 k)])
    let F : ℕ → ℝ := fun k => A1 k + A2 k - B1 k - B2 k
    have hF : Summable F := ((hA1.add hA2).sub hB1).sub hB2
    have hpoint (k : ℕ) : ‖F k‖ ≤ E k := by
      have h1 := norm_add_le (A1 k) (A2 k)
      have h2 := norm_sub_le (A1 k + A2 k) (B1 k)
      have h3 := norm_sub_le (A1 k + A2 k - B1 k) (B2 k)
      simp only [Real.norm_eq_abs] at h1 h2 h3 ⊢
      dsimp only [F, E]
      linarith only [h1, h2, h3]
    have hnorm : |∑' k : ℕ, F k| ≤ ∑' k : ℕ, E k := by
      simpa only [Real.norm_eq_abs] using hF.hasSum.norm_le_of_bounded hE.hasSum hpoint
    have hS : 0 < S := (Shao.C2.HalfLineTaylorSegment.segment_energy_bounds
      T q theta hT hq htheta0 htheta1).1
    have hY : |Y| ≤ a := Shao.C2.IntervalImageTaylorSegment.segment_space_closed
      a y q theta hy hnew htheta0 htheta1
    obtain ⟨hsA1, hsA2, hsB1, hsB2⟩ :=
      Shao.C2.IntervalImageMixedIntSeries.mixed_image_tails_summable j l a z S Y hl ha hz hS hY
    have htail : Shao.C2.IntervalImageMixedConvergence.mixedTailSum j l a z S Y =
        (∑' k : ℕ, Shao.C2.IntervalImageMixedIntSeries.mixedImageA j l a z S Y ((k : ℤ) + 2)) +
          (∑' k : ℕ, Shao.C2.IntervalImageMixedIntSeries.mixedImageA j l a z S Y (-((k : ℤ) + 2))) -
            (∑' k : ℕ, B1 k) - (∑' k : ℕ, B2 k) := by
      change (∑' k : ℕ, (Shao.C2.IntervalImageMixedIntSeries.mixedImageA j l a z S Y ((k : ℤ) + 2) +
        Shao.C2.IntervalImageMixedIntSeries.mixedImageA j l a z S Y (-((k : ℤ) + 2)) - B1 k - B2 k)) = _
      rw [((hsA1.add hsA2).sub hsB1).tsum_sub hsB2, (hsA1.add hsA2).tsum_sub hsB1,
        hsA1.tsum_add hsA2]
    have hs1 := hA1.tsum_eq_zero_add
    have hs2 := hA2.tsum_eq_zero_add
    simp only [A1, A2, Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one,
      add_assoc, one_add_one_eq_two] at hs1 hs2
    have hsum : (∑' k : ℕ, F k) = M j l Y S := by
      dsimp only [F]
      rw [((hA1.add hA2).sub hB1).tsum_sub hB2, (hA1.add hA2).tsum_sub hB1,
        hA1.tsum_add hA2, hs1, hs2]
      dsimp only [M, Shao.C2.IntervalImageMixedCandidate.mixedImageCandidate,
        Shao.C2.IntervalImageMixedCandidate.mixedFiniteImages]
      rw [htail]
      change _ =
        (Shao.C2.IntervalImageMixedIntSeries.mixedImageA j l a z S Y 0 +
          Shao.C2.IntervalImageMixedIntSeries.mixedImageA j l a z S Y 1 +
            Shao.C2.IntervalImageMixedIntSeries.mixedImageA j l a z S Y (-1) -
              Shao.C2.IntervalImageMixedIntSeries.mixedImageB j l a z S Y 0 -
                Shao.C2.IntervalImageMixedIntSeries.mixedImageB j l a z S Y (-1) + _) -
                  (if j = 0 ∧ l = 0 then 1 else 0) +
                    Shao.C2.IntervalImageMixedIntSeries.mixedImageB j l a z S Y 0 +
                      Shao.C2.IntervalImageMixedIntSeries.mixedImageB j l a z S Y (-1)
      rw [Shao.C2.IntervalImageSmallTimeTails.mixedImageA_zero]
      ring
    rw [hsum] at hnorm
    exact hnorm.trans (by simpa only [K, W, D] using hEbound)
  have hBcont (j l : ℕ) (m : ℤ) (Y S : ℝ) (hl : l ≤ 3)
      (hS : 0 < S) (hY : |Y| < a) :
      ContinuousAt (fun p : ℝ × ℝ =>
        Shao.C2.IntervalImageMixedIntSeries.mixedImageB j l a z p.2 p.1 m) (Y, S) := by
    have hc : ContinuousOn (fun p : ℝ × ℝ =>
        Shao.C2.IntervalImageMixedIntSeries.mixedImageB j l a z p.2 p.1 m)
        {p : ℝ × ℝ | |p.1| ≤ a ∧ S / 2 ≤ p.2 ∧ p.2 ≤ 2 * S} :=
      continuousOn_iff_continuous_restrict.2
        (Shao.C2.IntervalImageJointContinuity.mixedImageB_strip_continuous
          j l a z (S / 2) (2 * S) m hl (by positivity))
    have heq : {p : ℝ × ℝ | |p.1| ≤ a ∧ S / 2 ≤ p.2 ∧ p.2 ≤ 2 * S} =
        Set.Icc (-a) a ×ˢ Set.Icc (S / 2) (2 * S) := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc, abs_le]
    rw [heq] at hc
    have hYN : Set.Icc (-a) a ∈ nhds Y := Icc_mem_nhds (abs_lt.mp hY).1 (abs_lt.mp hY).2
    have hSN : Set.Icc (S / 2) (2 * S) ∈ nhds S := Icc_mem_nhds (by linarith) (by linarith)
    have hN : Set.Icc (-a) a ×ˢ Set.Icc (S / 2) (2 * S) ∈ nhds (Y, S) := by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod hYN hSN
    exact (hc (Y, S) ⟨abs_le.mp hY.le, by linarith, by linarith⟩).continuousAt hN
  have hBjoint (j l : ℕ) (m : ℤ) (Y S : ℝ) (hl : l ≤ 2)
      (hS : 0 < S) (hY : |Y| < a) :
      HasStrictFDerivAt (fun p : ℝ × ℝ =>
        Shao.C2.IntervalImageMixedIntSeries.mixedImageB j l a z p.2 p.1 m)
        (((1 : ℝ →L[ℝ] ℝ).smulRight
          (Shao.C2.IntervalImageMixedIntSeries.mixedImageB (j + 1) l a z S Y m)).coprod
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (Shao.C2.IntervalImageMixedIntSeries.mixedImageB j (l + 1) a z S Y m))) (Y, S) := by
    have hl3 : l ≤ 3 := by omega
    have hlp3 : l + 1 ≤ 3 := by omega
    let f : ℝ → ℝ → ℝ := fun w V => Shao.C2.IntervalImageMixedIntSeries.mixedImageB j l a z V w m
    let f1 : ℝ → ℝ → (ℝ →L[ℝ] ℝ) := fun w V =>
      (1 : ℝ →L[ℝ] ℝ).smulRight
        (Shao.C2.IntervalImageMixedIntSeries.mixedImageB (j + 1) l a z V w m)
    let f2 : ℝ → ℝ → (ℝ →L[ℝ] ℝ) := fun w V =>
      (1 : ℝ →L[ℝ] ℝ).smulRight
        (Shao.C2.IntervalImageMixedIntSeries.mixedImageB j (l + 1) a z V w m)
    have hN : Set.Ioo (-a) a ×ˢ Set.Ioi 0 ∈ nhds (Y, S) := by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod (isOpen_Ioo.mem_nhds (abs_lt.mp hY)) (isOpen_Ioi.mem_nhds hS)
    have df1 : ∀ᶠ p : ℝ × ℝ in nhds (Y, S), HasFDerivAt (fun w => f w p.2) (f1 p.1 p.2) p.1 := by
      filter_upwards [hN] with p hp
      exact (Shao.C2.IntervalImageMixedSpatialDerivatives.mixedImageB_spatial_hasDerivAt
        j l a z p.2 p.1 m hl3 hp.2).hasFDerivAt
    have df2 : ∀ᶠ p : ℝ × ℝ in nhds (Y, S), HasFDerivAt (f p.1) (f2 p.1 p.2) p.2 := by
      filter_upwards [hN] with p hp
      exact (Shao.C2.IntervalImageMixedTerms.spatialImageB_time_iterated_hasDerivAt
        j l a z p.2 p.1 m hl hp.2).hasFDerivAt
    have cf1 : ContinuousAt (fun p : ℝ × ℝ => f1 p.1 p.2) (Y, S) :=
      (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.comp
        (hBcont (j + 1) l m Y S hl3 hS hY)
    have cf2 : ContinuousAt (fun p : ℝ × ℝ => f2 p.1 p.2) (Y, S) :=
      (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.comp
        (hBcont j (l + 1) m Y S hlp3 hS hY)
    exact hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := (Y, S)) (f := f)
      (f₁ := f1) (f₂ := f2) df1 df2 cf1 cf2
  have hBpath (j l : ℕ) (m : ℤ) (q theta : ℝ) (hl : l ≤ 2)
      (hS : 0 < T - theta * q ^ 2) (hY : |y + theta * q| < a) :
      HasDerivAt (fun t : ℝ =>
        Shao.C2.IntervalImageMixedIntSeries.mixedImageB j l a z (T - t * q ^ 2) (y + t * q) m)
        (q * Shao.C2.IntervalImageMixedIntSeries.mixedImageB (j + 1) l a z
            (T - theta * q ^ 2) (y + theta * q) m -
          q ^ 2 * Shao.C2.IntervalImageMixedIntSeries.mixedImageB j (l + 1) a z
            (T - theta * q ^ 2) (y + theta * q) m) theta := by
    have hYd : HasDerivAt (fun t : ℝ => y + t * q) q theta := by
      simpa using (hasDerivAt_mul_const q (x := theta)).const_add y
    have hSd : HasDerivAt (fun t : ℝ => T - t * q ^ 2) (-q ^ 2) theta := by
      simpa using (hasDerivAt_mul_const (q ^ 2) (x := theta)).const_sub T
    have hd := (hBjoint j l m (y + theta * q) (T - theta * q ^ 2) hl hS hY).hasFDerivAt.comp
      theta (hYd.hasFDerivAt.prodMk hSd.hasFDerivAt)
    convert hd.hasDerivAt using 1 <;>
      simp only [Function.comp_def, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply_one, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.coprod_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.one_apply, smul_eq_mul] <;> ring
  have hMpath (j l : ℕ) (q theta : ℝ) (hl : l ≤ 2) (hz : |z| ≤ a)
      (hS : 0 < T - theta * q ^ 2) (hY : |y + theta * q| < a) :
      HasDerivAt (fun t : ℝ => M j l (y + t * q) (T - t * q ^ 2))
        (q * M (j + 1) l (y + theta * q) (T - theta * q ^ 2) -
          q ^ 2 * M j (l + 1) (y + theta * q) (T - theta * q ^ 2)) theta := by
    have hd := (((Shao.C2.IntervalImageJointDerivatives.mixedImageCandidate_path_hasDerivAt
      j l a z T y q theta hl ha hz hS hY).sub_const
        (if j = 0 ∧ l = 0 then 1 else 0)).add
          (hBpath j l 0 q theta hl hS hY)).add (hBpath j l (-1) q theta hl hS hY)
    convert hd using 1 <;> (try funext t) <;>
      simp only [M, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, false_and, if_false] <;> ring
  have hMspace (j l : ℕ) (Y S : ℝ) (hl : l ≤ 3) (hz : |z| ≤ a)
      (hS : 0 < S) (hY : |Y| < a) :
      HasDerivAt (fun w : ℝ => M j l w S) (M (j + 1) l Y S) Y := by
    have hd := (((Shao.C2.IntervalImageMixedSpatialDerivatives.mixedImageCandidate_spatial_hasDerivAt
      j l a z S Y hl ha hz hS hY).sub_const
        (if j = 0 ∧ l = 0 then 1 else 0)).add
          (Shao.C2.IntervalImageMixedSpatialDerivatives.mixedImageB_spatial_hasDerivAt
            j l a z S Y 0 hl hS)).add
              (Shao.C2.IntervalImageMixedSpatialDerivatives.mixedImageB_spatial_hasDerivAt
                j l a z S Y (-1) hl hS)
    convert hd using 1 <;> (try funext w) <;>
      simp only [M, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, false_and, if_false] <;> ring
  have hMPDE (hz : |z| ≤ a) :
      M 0 1 y T = (1 / 2 : ℝ) * M 2 0 y T + (z - y) / T * M 1 0 y T := by
    have hPI := Shao.C2.IntervalImageRevealRegularity.mixedImageCandidate_base_PDE a z T y ha hz hT hy
    have hPB (m : ℤ) :
        Shao.C2.IntervalImageMixedIntSeries.mixedImageB 0 1 a z T y m =
          (1 / 2 : ℝ) * Shao.C2.IntervalImageMixedIntSeries.mixedImageB 2 0 a z T y m +
            (z - y) / T * Shao.C2.IntervalImageMixedIntSeries.mixedImageB 1 0 a z T y m := by
      simpa only [Shao.C2.IntervalImageMixedIntSeries.mixedImageB, iteratedDeriv_succ,
        iteratedDeriv_zero, Nat.zero_add, Nat.cast_zero, zero_div, zero_mul, sub_zero] using
        (Shao.C2.IntervalImageTimeDerivatives.spatialImageB_time_hasDerivAt 0 a z T y m hT).deriv
    dsimp only [M]
    norm_num only [true_and, false_and, and_false, if_false, sub_zero]
    nlinarith only [hPI, hPB 0, hPB (-1)]
  have hMC (q theta : ℝ) (hz : |z| ≤ a)
      (hS : 0 < T - theta * q ^ 2) (hY : |y + theta * q| < a) :
      ContDiffAt ℝ (3 : ℕ) (fun t : ℝ => M 0 0 (y + t * q) (T - t * q ^ 2)) theta := by
    have hI : ContDiffAt ℝ (3 : ℕ) (fun t : ℝ =>
        Shao.C2.IntervalImageMixedCandidate.mixedImageCandidate 0 0 a z
          (T - t * q ^ 2) (y + t * q)) theta := by
      simpa only [Shao.C2.IntervalImageMixedCandidate.mixedImageCandidate_zero,
        Shao.C2.IntervalImageCandidateSpatial.intervalImageCandidate] using
        Shao.C2.IntervalImageRevealRegularity.intervalImageCandidate_path_contDiffAt_three
          a z T y q theta ha hz hS hY
    have hC (m : ℤ) : ContDiffAt ℝ (3 : ℕ) (fun t : ℝ =>
        Shao.C2.IntervalImageMixedIntSeries.mixedImageB 0 0 a z
          (T - t * q ^ 2) (y + t * q) m) theta := by
      simp only [Shao.C2.IntervalImageMixedIntSeries.mixedImageB,
        Shao.C2.IntervalImageIntSeries.spatialImageB, iteratedDeriv_zero]
      unfold Shao.C2.IntervalImageExponents.imageB
      fun_prop (disch := exact ne_of_gt hS)
    have hc1 : ContDiffAt ℝ (3 : ℕ) (fun _ : ℝ => (1 : ℝ)) theta := contDiffAt_const
    convert ((hI.sub hc1).add (hC 0)).add (hC (-1)) using 1 <;>
      (try funext t) <;> simp only [M, and_self, if_true]
  have hMlagrange (q : ℝ) (hz : |z| ≤ a) (hq : q ^ 2 ≤ T / 2)
      (hnew : |y + q| < a) :
      ∃ theta ∈ Set.Ioo (0 : ℝ) 1,
        M 0 0 (y + q) (T - q ^ 2) - M 0 0 y T -
            (q - q ^ 2 * (z - y) / T) * M 1 0 y T =
          (1 / 6 : ℝ) *
            (q ^ 3 * M 3 0 (y + theta * q) (T - theta * q ^ 2) -
              3 * q ^ 4 * M 2 1 (y + theta * q) (T - theta * q ^ 2) +
              3 * q ^ 5 * M 1 2 (y + theta * q) (T - theta * q ^ 2) -
              q ^ 6 * M 0 3 (y + theta * q) (T - theta * q ^ 2)) -
            q ^ 3 * M 1 1 y T + (1 / 2 : ℝ) * q ^ 4 * M 0 2 y T := by
    let g : ℝ → ℝ := fun t => M 0 0 (y + t * q) (T - t * q ^ 2)
    let p1 : ℝ → ℝ := fun t =>
      q * M 1 0 (y + t * q) (T - t * q ^ 2) -
        q ^ 2 * M 0 1 (y + t * q) (T - t * q ^ 2)
    let p2 : ℝ → ℝ := fun t =>
      q ^ 2 * M 2 0 (y + t * q) (T - t * q ^ 2) -
        2 * q ^ 3 * M 1 1 (y + t * q) (T - t * q ^ 2) +
          q ^ 4 * M 0 2 (y + t * q) (T - t * q ^ 2)
    let p3 : ℝ → ℝ := fun t =>
      q ^ 3 * M 3 0 (y + t * q) (T - t * q ^ 2) -
        3 * q ^ 4 * M 2 1 (y + t * q) (T - t * q ^ 2) +
          3 * q ^ 5 * M 1 2 (y + t * q) (T - t * q ^ 2) -
            q ^ 6 * M 0 3 (y + t * q) (T - t * q ^ 2)
    have hd0 (t : ℝ) (hS : 0 < T - t * q ^ 2) (hY : |y + t * q| < a) :
        HasDerivAt g (p1 t) t := hMpath 0 0 q t (by norm_num) hz hS hY
    have hd1 (t : ℝ) (hS : 0 < T - t * q ^ 2) (hY : |y + t * q| < a) :
        HasDerivAt p1 (p2 t) t := by
      have hh := ((hMpath 1 0 q t (by norm_num) hz hS hY).const_mul q).sub
        ((hMpath 0 1 q t (by norm_num) hz hS hY).const_mul (q ^ 2))
      convert hh using 1 <;> (try funext w) <;>
        simp only [p1, p2, Pi.sub_apply, Pi.mul_apply] <;> ring
    have hd2 (t : ℝ) (hS : 0 < T - t * q ^ 2) (hY : |y + t * q| < a) :
        HasDerivAt p2 (p3 t) t := by
      have hh := (((hMpath 2 0 q t (by norm_num) hz hS hY).const_mul (q ^ 2)).sub
        ((hMpath 1 1 q t (by norm_num) hz hS hY).const_mul (2 * q ^ 3))).add
          ((hMpath 0 2 q t (by norm_num) hz hS hY).const_mul (q ^ 4))
      convert hh using 1 <;> (try funext w) <;>
        simp only [p2, p3, Pi.add_apply, Pi.sub_apply, Pi.mul_apply] <;> ring
    have hnear (t : ℝ) (hS : 0 < T - t * q ^ 2) (hY : |y + t * q| < a) :
        {w : ℝ | 0 < T - w * q ^ 2 ∧ |y + w * q| < a} ∈ nhds t := by
      have hcS : Continuous (fun w : ℝ => T - w * q ^ 2) := by fun_prop
      have hcY : Continuous (fun w : ℝ => |y + w * q|) := by fun_prop
      exact ((isOpen_lt continuous_const hcS).inter
        (isOpen_lt hcY continuous_const)).mem_nhds ⟨hS, hY⟩
    have hiter2 (t : ℝ) (hS : 0 < T - t * q ^ 2) (hY : |y + t * q| < a) :
        iteratedDeriv 2 g t = p2 t := by
      have heq : deriv g =ᶠ[nhds t] p1 := by
        filter_upwards [hnear t hS hY] with w hw
        exact (hd0 w hw.1 hw.2).deriv
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
        heq.deriv_eq.trans (hd1 t hS hY).deriv
    have hiter3 (t : ℝ) (hS : 0 < T - t * q ^ 2) (hY : |y + t * q| < a) :
        iteratedDeriv 3 g t = p3 t := by
      have heq : iteratedDeriv 2 g =ᶠ[nhds t] p2 := by
        filter_upwards [hnear t hS hY] with w hw
        exact hiter2 w hw.1 hw.2
      simpa only [iteratedDeriv_succ] using
        heq.deriv_eq.trans (hd2 t hS hY).deriv
    have hzero : (0 : ℝ) ≠ 1 := by norm_num
    have hle : (0 : ℝ) ≤ 1 := by norm_num
    have hC0 : ContDiffAt ℝ (3 : ℕ) g 0 := by
      exact hMC q 0 hz (by simpa using hT) (by simpa using hy)
    have hf : ContDiffOn ℝ (3 : ℕ) g (Set.uIcc (0 : ℝ) 1) := by
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa only [Set.uIcc_of_le hle] using ht
      exact (hMC q t hz
        (Shao.C2.HalfLineTaylorSegment.segment_energy_bounds T q t hT hq ht'.1 ht'.2).1
        (Shao.C2.IntervalImageLagrangeRemainder.segment_space_strict a y q t hy hnew ht'.1 ht'.2)).contDiffWithinAt
    have hu : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) 1) := uniqueDiffOn_uIcc hzero
    have hz0 : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by simp
    have hit (k : ℕ) (hk : k ≤ 3) :
        iteratedDerivWithin k g (Set.uIcc (0 : ℝ) 1) 0 = iteratedDeriv k g 0 :=
      iteratedDerivWithin_eq_iteratedDeriv hu (hC0.of_le (by exact_mod_cast hk)) hz0
    have hpoly : taylorWithinEval g 2 (Set.uIcc (0 : ℝ) 1) 0 1 =
        g 0 + deriv g 0 + (1 / 2 : ℝ) * deriv (deriv g) 0 := by
      simp only [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_zero]
      rw [hit 0 (by norm_num), hit 1 (by norm_num), hit 2 (by norm_num)]
      norm_num [iteratedDeriv_succ, iteratedDeriv_zero, smul_eq_mul]
      <;> ring
    obtain ⟨theta, htheta, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hzero hf
    have htheta' : theta ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [Set.uIoo_of_lt (by norm_num : (0 : ℝ) < 1)] using htheta
    have hS := (Shao.C2.HalfLineTaylorSegment.segment_energy_bounds
      T q theta hT hq htheta'.1.le htheta'.2.le).1
    have hY := Shao.C2.IntervalImageLagrangeRemainder.segment_space_strict
      a y q theta hy hnew htheta'.1.le htheta'.2.le
    rw [hpoly, hiter3 theta hS hY] at hrem
    norm_num at hrem
    have h1 : deriv g 0 = p1 0 := (hd0 0 (by simpa using hT) (by simpa using hy)).deriv
    have h2 : deriv (deriv g) 0 = p2 0 := by
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
        hiter2 0 (by simpa using hT) (by simpa using hy)
    have hc : p1 0 + (1 / 2 : ℝ) * p2 0 -
        (q - q ^ 2 * (z - y) / T) * M 1 0 y T =
          -q ^ 3 * M 1 1 y T + (1 / 2 : ℝ) * q ^ 4 * M 0 2 y T := by
      dsimp only [p1, p2]
      simp only [zero_mul, sub_zero, add_zero]
      rw [hMPDE hz]
      ring
    rw [h1, h2] at hrem
    refine ⟨theta, htheta', ?_⟩
    have hh : g 1 - g 0 - (q - q ^ 2 * (z - y) / T) * M 1 0 y T =
        (1 / 6 : ℝ) * p3 theta - q ^ 3 * M 1 1 y T +
          (1 / 2 : ℝ) * q ^ 4 * M 0 2 y T := by
      linarith only [hrem, hc]
    simpa only [g, p3, one_mul, zero_mul, sub_zero, add_zero] using hh
  have hKnonneg (j l : ℕ) : 0 ≤ K j l := by
    dsimp only [K, W]
    exact mul_nonneg (by positivity)
      (Shao.C2.IntervalImageMixedTerms.mixedTimeConstant_nonneg j l)
  have hMweighted (j l : ℕ) (q theta : ℝ) (hl : l ≤ 3) (hj : j ≤ 3)
      (ho : 3 ≤ j + 2 * l) (hz : |z| ≤ a)
      (hq : q ^ 2 ≤ T / 2) (hnew : |y + q| ≤ a)
      (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) :
      |q ^ (j + 2 * l) * M j l (y + theta * q) (T - theta * q ^ 2)| ≤
        K j l * (|q| / Real.sqrt T) ^ 3 * D ^ 3 * Real.exp (-a ^ 2 / T) := by
    have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
    have hqa : |q| ≤ Real.sqrt T := by
      nlinarith only [hq, sq_abs q, Real.sq_sqrt hT.le, abs_nonneg q, Real.sqrt_nonneg T]
    have hD : 1 ≤ D := by
      dsimp only [D]
      linarith only [div_nonneg (abs_nonneg (z - y)) hs.le]
    have hn := Shao.C2.HalfLineSmallTaylor.normalized_power_domination
      (|q| / Real.sqrt T) D (by positivity) ((div_le_one hs).2 hqa) hD
      (j + 2 * l - 3) j hj
    have he : 3 + (j + 2 * l - 3) = j + 2 * l := by omega
    rw [he] at hn
    calc
      _ = |q| ^ (j + 2 * l) * |M j l (y + theta * q) (T - theta * q ^ 2)| := by
        rw [abs_mul, abs_pow]
      _ ≤ |q| ^ (j + 2 * l) *
          (K j l * (1 / Real.sqrt T) ^ (j + 2 * l) * D ^ j * Real.exp (-a ^ 2 / T)) :=
        mul_le_mul_of_nonneg_left (hMbound j l q theta hl hz hq hnew ht0 ht1) (by positivity)
      _ = K j l * ((|q| / Real.sqrt T) ^ (j + 2 * l) * D ^ j) *
          Real.exp (-a ^ 2 / T) := by rw [div_pow]; ring
      _ ≤ K j l * ((|q| / Real.sqrt T) ^ 3 * D ^ 3) *
          Real.exp (-a ^ 2 / T) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (hKnonneg j l))
          (Real.exp_pos _).le
      _ = _ := by ring
  have hMtaylor_strict (q : ℝ) (hz : |z| ≤ a)
      (hq : q ^ 2 ≤ T / 2) (hnew : |y + q| < a) :
      |M 0 0 (y + q) (T - q ^ 2) - M 0 0 y T -
        (q - q ^ 2 * (z - y) / T) * M 1 0 y T| ≤
          Bill K * (|q| / Real.sqrt T) ^ 3 * D ^ 3 * Real.exp (-a ^ 2 / T) := by
    obtain ⟨theta, htheta, heq⟩ := hMlagrange q hz hq hnew
    have h30 := hMweighted 3 0 q theta (by norm_num) (by norm_num) (by norm_num)
      hz hq hnew.le htheta.1.le htheta.2.le
    have h21 := hMweighted 2 1 q theta (by norm_num) (by norm_num) (by norm_num)
      hz hq hnew.le htheta.1.le htheta.2.le
    have h12 := hMweighted 1 2 q theta (by norm_num) (by norm_num) (by norm_num)
      hz hq hnew.le htheta.1.le htheta.2.le
    have h03 := hMweighted 0 3 q theta (by norm_num) (by norm_num) (by norm_num)
      hz hq hnew.le htheta.1.le htheta.2.le
    have h11 := hMweighted 1 1 q 0 (by norm_num) (by norm_num) (by norm_num)
      hz hq hnew.le (by norm_num) (by norm_num)
    have h02 := hMweighted 0 2 q 0 (by norm_num) (by norm_num) (by norm_num)
      hz hq hnew.le (by norm_num) (by norm_num)
    norm_num only [zero_mul, sub_zero, add_zero, Nat.mul_zero, Nat.mul_one,
      Nat.zero_add, Nat.add_zero, Nat.mul_succ] at h30 h21 h12 h03 h11 h02
    rw [heq]
    apply abs_le.mpr
    constructor <;> dsimp only [Bill] <;>
      nlinarith only [(abs_le.mp h30).1, (abs_le.mp h30).2,
        (abs_le.mp h21).1, (abs_le.mp h21).2, (abs_le.mp h12).1, (abs_le.mp h12).2,
        (abs_le.mp h03).1, (abs_le.mp h03).2, (abs_le.mp h11).1, (abs_le.mp h11).2,
        (abs_le.mp h02).1, (abs_le.mp h02).2]
  have hMtaylor (q : ℝ) (hz : |z| ≤ a)
      (hq : q ^ 2 ≤ T / 2) (hnew : |y + q| ≤ a) :
      |M 0 0 (y + q) (T - q ^ 2) - M 0 0 y T -
        (q - q ^ 2 * (z - y) / T) * M 1 0 y T| ≤
          Bill K * (|q| / Real.sqrt T) ^ 3 * D ^ 3 * Real.exp (-a ^ 2 / T) := by
    let LL : ℝ → ℝ := fun theta =>
      |M 0 0 (y + theta * q) (T - (theta * q) ^ 2) - M 0 0 y T -
        (theta * q - (theta * q) ^ 2 * (z - y) / T) * M 1 0 y T|
    let RR : ℝ → ℝ := fun theta =>
      Bill K * (|theta * q| / Real.sqrt T) ^ 3 * D ^ 3 * Real.exp (-a ^ 2 / T)
    have hCF : ContinuousOn (fun theta : ℝ =>
        Shao.C2.IntervalImageCandidateSpatial.intervalImageCandidate a z
          (T - (theta * q) ^ 2) (y + theta * q)) (Set.Icc (0 : ℝ) 1) :=
      Shao.C2.IntervalImageWallLimit.intervalImageCandidate_scaled_step_continuousOn
        a y z T q ha hy hz hT hq hnew
    have hCB (m : ℤ) : ContinuousOn (fun theta : ℝ =>
        Shao.C2.IntervalImageMixedIntSeries.mixedImageB 0 0 a z
          (T - (theta * q) ^ 2) (y + theta * q) m) (Set.Icc (0 : ℝ) 1) := by
      intro theta htheta
      have htheta2 : theta ^ 2 ≤ 1 := by nlinarith only [htheta.1, htheta.2]
      have hqtheta : (theta * q) ^ 2 ≤ q ^ 2 := by
        rw [mul_pow]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right htheta2 (sq_nonneg q)
      have hS : 0 < T - (theta * q) ^ 2 := by linarith only [hT, hq, hqtheta]
      apply ContinuousAt.continuousWithinAt
      simp only [Shao.C2.IntervalImageMixedIntSeries.mixedImageB,
        Shao.C2.IntervalImageIntSeries.spatialImageB, iteratedDeriv_zero]
      unfold Shao.C2.IntervalImageExponents.imageB
      fun_prop (disch := exact ne_of_gt hS)
    have hCM : ContinuousOn (fun theta : ℝ =>
        M 0 0 (y + theta * q) (T - (theta * q) ^ 2)) (Set.Icc (0 : ℝ) 1) := by
      have hc1 : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (0 : ℝ) 1) := continuousOn_const
      have hh := ((hCF.sub hc1).add (hCB 0)).add (hCB (-1))
      convert hh using 1 <;> (try funext theta) <;>
        simp only [M, Shao.C2.IntervalImageMixedCandidate.mixedImageCandidate_zero,
          Shao.C2.IntervalImageCandidateSpatial.intervalImageCandidate, and_self, if_true,
          Pi.add_apply, Pi.sub_apply]
    have hCL : ContinuousOn LL (Set.Icc (0 : ℝ) 1) := by
      have hc : ContinuousOn (fun theta : ℝ =>
          (theta * q - (theta * q) ^ 2 * (z - y) / T) * M 1 0 y T)
          (Set.Icc (0 : ℝ) 1) := by fun_prop
      exact ((hCM.sub continuousOn_const).sub hc).abs
    have hCR : Continuous RR := by dsimp only [RR]; fun_prop
    have hm : ∀ᶠ theta : ℝ in nhdsWithin (1 : ℝ) (Set.Iio 1),
        theta ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with theta htheta
      exact ⟨htheta.1.le, htheta.2.le⟩
    have ht : Filter.Tendsto (fun theta : ℝ => theta)
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhdsWithin (1 : ℝ) (Set.Icc 0 1)) :=
      tendsto_nhdsWithin_iff.2 ⟨Filter.tendsto_id.mono_left nhdsWithin_le_nhds, hm⟩
    have hCL0 : Filter.Tendsto LL (nhdsWithin (1 : ℝ) (Set.Icc 0 1)) (nhds (LL 1)) :=
      hCL 1 ⟨by norm_num, by norm_num⟩
    have hCR0 : Filter.Tendsto RR (nhds (1 : ℝ)) (nhds (RR 1)) := hCR.continuousAt
    have hineq : LL ≤ᶠ[nhdsWithin (1 : ℝ) (Set.Iio 1)] RR := by
      filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with theta htheta
      have htheta2 : theta ^ 2 ≤ 1 := by nlinarith only [htheta.1.le, htheta.2.le]
      have hqtheta : (theta * q) ^ 2 ≤ q ^ 2 := by
        rw [mul_pow]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right htheta2 (sq_nonneg q)
      exact hMtaylor_strict (theta * q) hz (hqtheta.trans hq)
        (Shao.C2.IntervalImageTaylorSegment.segment_space_interior
          a y q theta hy hnew htheta.1.le htheta.2)
    have hh := le_of_tendsto_of_tendsto (hCL0.comp ht)
      (hCR0.mono_left nhdsWithin_le_nhds) hineq
    simpa only [LL, RR, one_mul] using hh
  have hNnonneg (j l : ℕ) : 0 ≤ N j l := by
    dsimp only [N]
    split <;> (try dsimp only [P]) <;> positivity
  have hHalfProfiles (u v S : ℝ) (hu : 0 < u) (hv : 0 < v) (hS : 0 < S) :
      let DU := 1 + |u - v| / Real.sqrt S
      let E := Real.exp (-3 * (2 * u * v / S) / 4)
      |Shao.C2.HalfLineMixedProfiles.slopeTime u v S| ≤
        N 1 0 * (1 / Real.sqrt S) * DU * E ∧
      |(2 * v / S) ^ 3 * Real.exp (-2 * u * v / S)| ≤
        N 3 0 * (1 / Real.sqrt S) ^ 3 * DU ^ 3 * E ∧
      |deriv (Shao.C2.HalfLineMixedProfiles.curvatureTime u v) S| ≤
        N 2 1 * (1 / Real.sqrt S) ^ 4 * DU ^ 2 * E ∧
      |deriv (deriv (Shao.C2.HalfLineMixedProfiles.slopeTime u v)) S| ≤
        N 1 2 * (1 / Real.sqrt S) ^ 5 * DU * E ∧
      |deriv (deriv (deriv (Shao.C2.HalfLineTimeProfiles.timeCompletion (2 * u * v)))) S| ≤
        N 0 3 * (1 / Real.sqrt S) ^ 6 * E ∧
      |deriv (Shao.C2.HalfLineMixedProfiles.slopeTime u v) S| ≤
        N 1 1 * (1 / Real.sqrt S) ^ 3 * DU * E ∧
      |deriv (deriv (Shao.C2.HalfLineTimeProfiles.timeCompletion (2 * u * v))) S| ≤
        N 0 2 * (1 / Real.sqrt S) ^ 4 * E := by
    intro DU E
    let rr : ℝ := 2 * u * v / S
    let cc : ℝ := 2 * v / S
    let ee : ℝ := Real.exp (-rr)
    have hs : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
    have hs2 : (Real.sqrt S) ^ 2 = S := Real.sq_sqrt hS.le
    have hInvS : 1 / S = (1 / Real.sqrt S) ^ 2 := by
      rw [one_div_pow, Real.sq_sqrt hS.le]
    have hr : 0 ≤ rr := by dsimp only [rr]; positivity
    have hc : 0 ≤ cc := by dsimp only [cc]; positivity
    have he : 0 ≤ ee := (Real.exp_pos _).le
    have hExp : Real.exp (-2 * u * v / S) = ee := by
      dsimp only [ee, rr]; congr 1; ring
    have hm (j m : ℕ) (hj : j ≤ 3) :
        cc ^ j * rr ^ m * ee ≤
          P j m * (1 / Real.sqrt S) ^ j * DU ^ j * E := by
      convert arl_quarter_reflection_monomial u v S hu hv hS j m hj using 1 <;>
        dsimp only [cc, rr, ee, P, DU, E] <;>
        simp only [mul_pow, div_pow] <;> ring
    have h10 := hm 1 0 (by norm_num)
    have h11 := hm 1 1 (by norm_num)
    have h12 := hm 1 2 (by norm_num)
    have h20 := hm 2 0 (by norm_num)
    have h21 := hm 2 1 (by norm_num)
    have h30 := hm 3 0 (by norm_num)
    have h01 := hm 0 1 (by norm_num)
    have h02 := hm 0 2 (by norm_num)
    have h03 := hm 0 3 (by norm_num)
    norm_num [P] at h10 h11 h12 h20 h21 h30 h01 h02 h03
    have hL11 : |cc * rr * ee - cc * ee| ≤
        N 1 1 * (1 / Real.sqrt S) * DU * E := by
      apply abs_le.mpr
      constructor <;> norm_num [N, P] <;>
        nlinarith only [h10, h11, mul_nonneg hc he, mul_nonneg (mul_nonneg hc hr) he]
    have hL21 : |2 * (cc ^ 2 * ee) - cc ^ 2 * rr * ee| ≤
        N 2 1 * (1 / Real.sqrt S) ^ 2 * DU ^ 2 * E := by
      apply abs_le.mpr
      constructor <;> norm_num [N, P] <;>
        nlinarith only [h20, h21, mul_nonneg (sq_nonneg cc) he,
          mul_nonneg (mul_nonneg (sq_nonneg cc) hr) he]
    have hL12 : |2 * (cc * ee) - 4 * (cc * rr * ee) + cc * rr ^ 2 * ee| ≤
        N 1 2 * (1 / Real.sqrt S) * DU * E := by
      apply abs_le.mpr
      constructor <;> norm_num [N, P] <;>
        nlinarith only [h10, h11, h12, mul_nonneg hc he,
          mul_nonneg (mul_nonneg hc hr) he, mul_nonneg (mul_nonneg hc (sq_nonneg rr)) he]
    have hL03 : |-6 * (rr * ee) + 6 * (rr ^ 2 * ee) - rr ^ 3 * ee| ≤
        N 0 3 * E := by
      apply abs_le.mpr
      constructor <;> norm_num [N, P] <;>
        nlinarith only [h01, h02, h03, mul_nonneg hr he,
          mul_nonneg (sq_nonneg rr) he, mul_nonneg (pow_nonneg hr 3) he]
    have hL02 : |2 * (rr * ee) - rr ^ 2 * ee| ≤ N 0 2 * E := by
      apply abs_le.mpr
      constructor <;> norm_num [N, P] <;>
        nlinarith only [h01, h02, mul_nonneg hr he, mul_nonneg (sq_nonneg rr) he]
    have hf11 : deriv (Shao.C2.HalfLineMixedProfiles.slopeTime u v) S =
        (cc * rr * ee - cc * ee) / S := by
      rw [(Shao.C2.HalfLineMixedProfiles.slopeTime_hasDerivAt u v S hS).deriv, hExp]
      dsimp only [cc, rr]
      field_simp [ne_of_gt hS] <;> ring
    have hf21 : deriv (Shao.C2.HalfLineMixedProfiles.curvatureTime u v) S =
        (2 * (cc ^ 2 * ee) - cc ^ 2 * rr * ee) / S := by
      rw [(Shao.C2.HalfLineMixedProfiles.curvatureTime_hasDerivAt u v S hS).deriv, hExp]
      dsimp only [cc, rr]
      field_simp [ne_of_gt hS] <;> ring
    have hf12 : deriv (deriv (Shao.C2.HalfLineMixedProfiles.slopeTime u v)) S =
        (2 * (cc * ee) - 4 * (cc * rr * ee) + cc * rr ^ 2 * ee) / S ^ 2 := by
      rw [(Shao.C2.HalfLineMixedProfiles.slopeTime_second_hasDerivAt u v S hS).deriv, hExp]
      dsimp only [cc, rr]
      field_simp [ne_of_gt hS] <;> ring
    have hf03 : deriv (deriv (deriv (Shao.C2.HalfLineTimeProfiles.timeCompletion (2 * u * v)))) S =
        (-6 * (rr * ee) + 6 * (rr ^ 2 * ee) - rr ^ 3 * ee) / S ^ 3 := by
      rw [(Shao.C2.HalfLineTimeProfiles.timeCompletion_third_hasDerivAt (2 * u * v) S hS).deriv]
      have hExp' : Real.exp (-(2 * u * v) / S) = ee := by
        dsimp only [ee, rr]
        congr 1
        ring
      rw [hExp']
      dsimp only [rr]
      field_simp [ne_of_gt hS] <;> ring
    have hf02 : deriv (deriv (Shao.C2.HalfLineTimeProfiles.timeCompletion (2 * u * v))) S =
        (2 * (rr * ee) - rr ^ 2 * ee) / S ^ 2 := by
      rw [(Shao.C2.HalfLineTimeProfiles.timeCompletion_second_hasDerivAt (2 * u * v) S hS).deriv]
      have hExp' : Real.exp (-(2 * u * v) / S) = ee := by
        dsimp only [ee, rr]
        congr 1
        ring
      rw [hExp']
      dsimp only [rr]
      field_simp [ne_of_gt hS] <;> ring
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold Shao.C2.HalfLineMixedProfiles.slopeTime
      rw [hExp, abs_of_nonneg (mul_nonneg hc he)]
      simpa [N, P, cc] using h10
    · rw [hExp, abs_of_nonneg (mul_nonneg (pow_nonneg hc 3) he)]
      norm_num [N, P, cc] at ⊢
      simpa only [cc] using h30
    · rw [hf21, abs_div, abs_of_pos hS]
      calc
        _ ≤ (N 2 1 * (1 / Real.sqrt S) ^ 2 * DU ^ 2 * E) / S :=
          div_le_div_of_nonneg_right hL21 hS.le
        _ = _ := by
          rw [div_eq_mul_one_div]
          try rw [← one_div_pow]
          rw [hInvS]
          ring
    · rw [hf12, abs_div, abs_of_pos (pow_pos hS 2)]
      calc
        _ ≤ (N 1 2 * (1 / Real.sqrt S) * DU * E) / S ^ 2 :=
          div_le_div_of_nonneg_right hL12 (pow_nonneg hS.le 2)
        _ = _ := by
          rw [div_eq_mul_one_div]
          try rw [← one_div_pow]
          rw [hInvS]
          ring
    · rw [hf03, abs_div, abs_of_pos (pow_pos hS 3)]
      calc
        _ ≤ (N 0 3 * E) / S ^ 3 :=
          div_le_div_of_nonneg_right hL03 (pow_nonneg hS.le 3)
        _ = _ := by
          rw [div_eq_mul_one_div]
          try rw [← one_div_pow]
          rw [hInvS]
          ring
    · rw [hf11, abs_div, abs_of_pos hS]
      calc
        _ ≤ (N 1 1 * (1 / Real.sqrt S) * DU * E) / S :=
          div_le_div_of_nonneg_right hL11 hS.le
        _ = _ := by
          rw [div_eq_mul_one_div]
          try rw [← one_div_pow]
          rw [hInvS]
          ring
    · rw [hf02, abs_div, abs_of_pos (pow_pos hS 2)]
      calc
        _ ≤ (N 0 2 * E) / S ^ 2 :=
          div_le_div_of_nonneg_right hL02 (pow_nonneg hS.le 2)
        _ = _ := by
          rw [div_eq_mul_one_div]
          try rw [← one_div_pow]
          rw [hInvS]
          ring
  have hHtransport (j l : ℕ) (S DU E : ℝ) (hS : 0 < S) (hhalf : T / 2 ≤ S)
      (hDU0 : 0 ≤ DU) (hDU : DU ≤ 3 * D) (hE0 : 0 ≤ E)
      (hE : E ≤ Real.exp (-a ^ 2 / T)) :
      N j l * (1 / Real.sqrt S) ^ (j + 2 * l) * DU ^ j * E ≤
        H j l * (1 / Real.sqrt T) ^ (j + 2 * l) * D ^ j * Real.exp (-a ^ 2 / T) := by
    have hn := hNnonneg j l
    have hsS : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
    have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
    have hD0 : 0 ≤ D := by dsimp only [D]; positivity
    have hInv : 1 / Real.sqrt S ≤ Real.sqrt 2 / Real.sqrt T := by
      have hsq : (Real.sqrt 2 * Real.sqrt S) ^ 2 = 2 * S := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hS.le]
      have hh : Real.sqrt T ≤ Real.sqrt 2 * Real.sqrt S := by
        nlinarith only [hsq, Real.sq_sqrt hT.le, hhalf, Real.sqrt_nonneg T,
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg S)]
      exact (div_le_div_iff₀ hsS hsT).2 (by simpa only [one_mul] using hh)
    have hspace : (1 / Real.sqrt S) * DU ≤
        (3 * Real.sqrt 2) * (1 / Real.sqrt T) * D := by
      have hh := mul_le_mul hInv hDU hDU0 (by positivity)
      convert hh using 1 <;> ring
    have hInvTime : 1 / S ≤ 2 / T :=
      (div_le_div_iff₀ hS hT).2 (by linarith only [hhalf])
    have hsqS : (1 / Real.sqrt S) ^ 2 = 1 / S := by
      rw [one_div_pow, Real.sq_sqrt hS.le]
    have hsqT : (1 / Real.sqrt T) ^ 2 = 1 / T := by
      rw [one_div_pow, Real.sq_sqrt hT.le]
    have hscale : N j l * (1 / Real.sqrt S) ^ (j + 2 * l) * DU ^ j ≤
        H j l * (1 / Real.sqrt T) ^ (j + 2 * l) * D ^ j := by
      have hh := mul_le_mul
        (pow_le_pow_left₀ (by positivity) hspace j)
        (pow_le_pow_left₀ (by positivity) hInvTime l) (by positivity) (by positivity)
      have hhN := mul_le_mul_of_nonneg_left hh (hNnonneg j l)
      calc
        _ = N j l * (((1 / Real.sqrt S) * DU) ^ j * (1 / S) ^ l) := by
          rw [pow_add, pow_mul, hsqS, mul_pow]
          ring
        _ ≤ N j l * (((3 * Real.sqrt 2) * (1 / Real.sqrt T) * D) ^ j *
            (2 / T) ^ l) := hhN
        _ = _ := by
          dsimp only [H]
          rw [pow_add, pow_mul, hsqT, mul_pow, mul_pow, div_pow, one_div_pow]
          ring
    exact mul_le_mul hscale hE hE0 (by
      exact mul_nonneg (mul_nonneg (by dsimp only [H]; positivity)
        (pow_nonneg (by positivity) (j + 2 * l))) (pow_nonneg hD0 j))
  have hHalfProfilesAt (u v q theta : ℝ) (hv : 0 < v)
      (hdisp : |u - v| = |z - y|) (hq : q ^ 2 ≤ T / 2)
      (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
      (hfar : (2 / 3 : ℝ) * a ^ 2 ≤ (u - theta * q) * v) :
      let U := u - theta * q
      let S := T - theta * q ^ 2
      |Shao.C2.HalfLineMixedProfiles.slopeTime U v S| ≤
        H 1 0 * (1 / Real.sqrt T) * D * Real.exp (-a ^ 2 / T) ∧
      |(2 * v / S) ^ 3 * Real.exp (-2 * U * v / S)| ≤
        H 3 0 * (1 / Real.sqrt T) ^ 3 * D ^ 3 * Real.exp (-a ^ 2 / T) ∧
      |deriv (Shao.C2.HalfLineMixedProfiles.curvatureTime U v) S| ≤
        H 2 1 * (1 / Real.sqrt T) ^ 4 * D ^ 2 * Real.exp (-a ^ 2 / T) ∧
      |deriv (deriv (Shao.C2.HalfLineMixedProfiles.slopeTime U v)) S| ≤
        H 1 2 * (1 / Real.sqrt T) ^ 5 * D * Real.exp (-a ^ 2 / T) ∧
      |deriv (deriv (deriv (Shao.C2.HalfLineTimeProfiles.timeCompletion (2 * U * v)))) S| ≤
        H 0 3 * (1 / Real.sqrt T) ^ 6 * Real.exp (-a ^ 2 / T) ∧
      |deriv (Shao.C2.HalfLineMixedProfiles.slopeTime U v) S| ≤
        H 1 1 * (1 / Real.sqrt T) ^ 3 * D * Real.exp (-a ^ 2 / T) ∧
      |deriv (deriv (Shao.C2.HalfLineTimeProfiles.timeCompletion (2 * U * v))) S| ≤
        H 0 2 * (1 / Real.sqrt T) ^ 4 * Real.exp (-a ^ 2 / T) := by
    intro U S
    have hEb := Shao.C2.HalfLineTaylorSegment.segment_energy_bounds T q theta hT hq ht0 ht1
    have hS : 0 < S := hEb.1
    have hhalf : T / 2 ≤ S := hEb.2.1
    have hST : S ≤ T := hEb.2.2
    have hU : 0 < U := by
      have hp : 0 < U * v := (by positivity : (0 : ℝ) < (2 / 3 : ℝ) * a ^ 2).trans_le hfar
      by_contra hnot
      have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) hv.le
      linarith only [hp, hh]
    let DU := 1 + |U - v| / Real.sqrt S
    let E := Real.exp (-3 * (2 * U * v / S) / 4)
    have hDU0 : 0 ≤ DU := by dsimp only [DU]; positivity
    have hDU : DU ≤ 3 * D := by
      have hh := Shao.C2.HalfLineTaylorSegment.segment_displacement_bound (u - v) T q theta
        hT hq ht0 ht1
      have heq : U - v = (u - v) - theta * q := by dsimp only [U]; ring
      dsimp only [DU]
      rw [heq]
      simpa only [Shao.C2.HalfLineTaylorSegment.segmentEnergy, hdisp, D] using hh
    have hE : E ≤ Real.exp (-a ^ 2 / T) := by
      have hn : a ^ 2 ≤ (3 / 2 : ℝ) * U * v := by linarith only [hfar]
      have hn0 : 0 ≤ (3 / 2 : ℝ) * U * v := by positivity
      have hh := ((div_le_div_iff_of_pos_right hT).2 hn).trans
        (div_le_div_of_nonneg_left hn0 hS hST)
      apply Real.exp_le_exp.2
      convert neg_le_neg hh using 1 <;> (try dsimp only [E]) <;> ring
    have ht (j l : ℕ) :
        N j l * (1 / Real.sqrt S) ^ (j + 2 * l) * DU ^ j * E ≤
          H j l * (1 / Real.sqrt T) ^ (j + 2 * l) * D ^ j * Real.exp (-a ^ 2 / T) :=
      hHtransport j l S DU E hS hhalf hDU0 hDU (Real.exp_pos _).le hE
    have hp := hHalfProfiles U v S hU hv hS
    change
      |Shao.C2.HalfLineMixedProfiles.slopeTime U v S| ≤ _ ∧ _ at hp
    refine ⟨hp.1.trans ?_, hp.2.1.trans ?_, hp.2.2.1.trans ?_, hp.2.2.2.1.trans ?_,
      hp.2.2.2.2.1.trans ?_, hp.2.2.2.2.2.1.trans ?_, hp.2.2.2.2.2.2.trans ?_⟩
    · simpa only [Nat.mul_zero, Nat.add_zero, pow_one] using ht 1 0
    · simpa only [Nat.mul_zero, Nat.add_zero] using ht 3 0
    · simpa only [Nat.mul_one] using ht 2 1
    · simpa only [Nat.mul_succ, Nat.mul_one, pow_one] using ht 1 2
    · simpa only [Nat.zero_add, pow_zero, mul_one] using ht 0 3
    · simpa only [Nat.mul_one, pow_one] using ht 1 1
    · simpa only [Nat.zero_add, pow_zero, mul_one] using ht 0 2
  have hHnonneg (j l : ℕ) : 0 ≤ H j l := by
    have hn := hNnonneg j l
    dsimp only [H]
    positivity
  have hCubicWeight (A V q : ℝ) (j l : ℕ) (hA : 0 ≤ A) (hj : j ≤ 3)
      (ho : 3 ≤ j + 2 * l) (hq : q ^ 2 ≤ T / 2)
      (hV : |V| ≤ A * (1 / Real.sqrt T) ^ (j + 2 * l) * D ^ j *
        Real.exp (-a ^ 2 / T)) :
      |q ^ (j + 2 * l) * V| ≤
        A * (|q| / Real.sqrt T) ^ 3 * D ^ 3 * Real.exp (-a ^ 2 / T) := by
    have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
    have hqa : |q| ≤ Real.sqrt T := by
      nlinarith only [hq, sq_abs q, Real.sq_sqrt hT.le, abs_nonneg q, Real.sqrt_nonneg T]
    have hD : 1 ≤ D := by
      dsimp only [D]
      linarith only [div_nonneg (abs_nonneg (z - y)) hs.le]
    have hn := Shao.C2.HalfLineSmallTaylor.normalized_power_domination
      (|q| / Real.sqrt T) D (by positivity) ((div_le_one hs).2 hqa) hD
      (j + 2 * l - 3) j hj
    have he : 3 + (j + 2 * l - 3) = j + 2 * l := by omega
    rw [he] at hn
    calc
      _ = |q| ^ (j + 2 * l) * |V| := by rw [abs_mul, abs_pow]
      _ ≤ |q| ^ (j + 2 * l) *
          (A * (1 / Real.sqrt T) ^ (j + 2 * l) * D ^ j * Real.exp (-a ^ 2 / T)) :=
        mul_le_mul_of_nonneg_left hV (by positivity)
      _ = A * ((|q| / Real.sqrt T) ^ (j + 2 * l) * D ^ j) * Real.exp (-a ^ 2 / T) := by
        rw [div_pow]; ring
      _ ≤ A * ((|q| / Real.sqrt T) ^ 3 * D ^ 3) * Real.exp (-a ^ 2 / T) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hA) (Real.exp_pos _).le
      _ = _ := by ring
  have hHalfTaylorFar (u v q : ℝ) (hv : 0 < v)
      (hdisp : |u - v| = |z - y|) (hq : q ^ 2 ≤ T / 2)
      (hfar : ∀ theta : ℝ, 0 ≤ theta → theta ≤ 1 →
        (2 / 3 : ℝ) * a ^ 2 ≤ (u - theta * q) * v) :
      |Shao.C2.HalfLineTaylorPath.completionAlongSegment u v T q 1 -
        Shao.C2.HalfLineTaylorPath.completionAlongSegment u v T q 0 -
        (q - q ^ 2 * (u - v) / T) * (-Shao.C2.HalfLineMixedProfiles.slopeTime u v T)| ≤
          Bill H * (|q| / Real.sqrt T) ^ 3 * D ^ 3 * Real.exp (-a ^ 2 / T) := by
    obtain ⟨theta, htheta, heq⟩ :=
      Shao.C2.HalfLineTaylorRemainder.compensated_lagrange_remainder u v T q hT hq
    have hp := hHalfProfilesAt u v q theta hv hdisp hq htheta.1.le htheta.2.le
      (hfar theta htheta.1.le htheta.2.le)
    have hp0 := hHalfProfilesAt u v q 0 hv hdisp hq (by norm_num) (by norm_num)
      (hfar 0 (by norm_num) (by norm_num))
    have h30 := hCubicWeight (H 3 0)
      ((2 * v / (T - theta * q ^ 2)) ^ 3 *
        Real.exp (-2 * (u - theta * q) * v / (T - theta * q ^ 2)))
      q 3 0 (hHnonneg 3 0) (by norm_num) (by norm_num) hq (by simpa using hp.2.1)
    have h21 := hCubicWeight (H 2 1)
      (deriv (Shao.C2.HalfLineMixedProfiles.curvatureTime (u - theta * q) v)
        (T - theta * q ^ 2)) q 2 1 (hHnonneg 2 1) (by norm_num) (by norm_num) hq
          (by simpa using hp.2.2.1)
    have h12 := hCubicWeight (H 1 2)
      (deriv (deriv (Shao.C2.HalfLineMixedProfiles.slopeTime (u - theta * q) v))
        (T - theta * q ^ 2)) q 1 2 (hHnonneg 1 2) (by norm_num) (by norm_num) hq
          (by simpa using hp.2.2.2.1)
    have h03 := hCubicWeight (H 0 3)
      (deriv (deriv (deriv (Shao.C2.HalfLineTimeProfiles.timeCompletion
        (2 * (u - theta * q) * v)))) (T - theta * q ^ 2))
      q 0 3 (hHnonneg 0 3) (by norm_num) (by norm_num) hq
        (by simpa using hp.2.2.2.2.1)
    have h11 := hCubicWeight (H 1 1)
      (deriv (Shao.C2.HalfLineMixedProfiles.slopeTime u v) T)
      q 1 1 (hHnonneg 1 1) (by norm_num) (by norm_num) hq
        (by simpa using hp0.2.2.2.2.2.1)
    have h02 := hCubicWeight (H 0 2)
      (deriv (deriv (Shao.C2.HalfLineTimeProfiles.timeCompletion (2 * u * v))) T)
      q 0 2 (hHnonneg 0 2) (by norm_num) (by norm_num) hq
        (by simpa using hp0.2.2.2.2.2.2)
    have hE := (Shao.C2.HalfLineTaylorSegment.segment_energy_bounds
      T q theta hT hq htheta.1.le htheta.2.le).1
    rw [Shao.C2.HalfLineTaylorRemainder.third_path_derivative_decomposition u v T q theta hE] at heq
    dsimp only [Shao.C2.HalfLineTaylorSegment.segmentEnergy,
      Shao.C2.HalfLineTaylorSegment.segmentDistance] at heq
    norm_num only [Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero, Nat.mul_succ]
      at h30 h21 h12 h03 h11 h02
    rw [heq]
    apply abs_le.mpr
    constructor <;> dsimp only [Bill] <;>
      nlinarith only [(abs_le.mp h30).1, (abs_le.mp h30).2,
        (abs_le.mp h21).1, (abs_le.mp h21).2, (abs_le.mp h12).1, (abs_le.mp h12).2,
        (abs_le.mp h03).1, (abs_le.mp h03).2, (abs_le.mp h11).1, (abs_le.mp h11).2,
        (abs_le.mp h02).1, (abs_le.mp h02).2]
  let Z : ℝ → ℝ → ℝ := fun Y S =>
    1 + completionExt .interval (F .interval) a Y S z -
      completionExt .upper (F .upper) a Y S z -
      completionExt .lower (F .lower) a Y S z
  let ZY : ℝ := FY .interval (a, y, T, z) -
    (if z < a then FY .upper (a, y, T, z) else 0) -
    (if -a < z then FY .lower (a, y, T, z) else 0)
  have hExtI (Y S : ℝ) :
      completionExt .interval (F .interval) a Y S z =
        Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q a Y S z := by
    by_cases hY : |Y| < a
    · by_cases hz : |z| < a
      · simp [completionExt, Interior, F, eventCompletionKernel,
          Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion, ha, hY,
          (abs_lt.mp hY).1, (abs_lt.mp hY).2, (abs_lt.mp hz).1, (abs_lt.mp hz).2]
      · rw [Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion_exterior Q a Y S z
          (fun hh => hz hh.2)]
        unfold completionExt
        exact if_neg (by
          intro hh
          exact hz (abs_lt.mpr hh.2.2))
    · rw [Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion_exterior Q a Y S z
        (fun hh => hY hh.1)]
      unfold completionExt
      exact if_neg (by
        intro hh
        exact hY (abs_lt.mpr hh.2.1))
  have hExtU (Y S : ℝ) :
      completionExt .upper (F .upper) a Y S z =
        Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion Q a Y S z := by
    by_cases hY : Y < a
    · by_cases hz : z < a
      · simp [completionExt, Interior, F, eventCompletionKernel,
          Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion, ha, hY, hz]
      · rw [Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion_exterior Q a Y S z (fun hh => hz hh.2)]
        unfold completionExt
        exact if_neg (by intro hh; exact hz hh.2.2)
    · rw [Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion_exterior Q a Y S z (fun hh => hY hh.1)]
      unfold completionExt
      exact if_neg (by intro hh; exact hY hh.2.1)
  have hExtL (Y S : ℝ) :
      completionExt .lower (F .lower) a Y S z =
        Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion Q a Y S z := by
    by_cases hY : -a < Y
    · by_cases hz : -a < z
      · simp [completionExt, Interior, F, eventCompletionKernel,
          Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion, ha, hY, hz]
      · rw [Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion_exterior Q a Y S z (fun hh => hz hh.2)]
        unfold completionExt
        exact if_neg (by intro hh; exact hz hh.2.2)
    · rw [Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion_exterior Q a Y S z (fun hh => hY hh.1)]
      unfold completionExt
      exact if_neg (by intro hh; exact hY hh.2.1)
  have hExtU_scalar (hz : z < a) (Y S : ℝ) :
      completionExt .upper (F .upper) a Y S z =
        Shao.C2.HalfLinePhysicalGaussian.upperCompletion a Y S z := by
    rw [hExtU]
    exact congrFun (congrFun
      (Shao.C2.BridgeUpperAffineIdentification.source_upper_eq_scalar B PB hB a z ha hz) Y) S
  have hExtL_scalar (hz : -a < z) (Y S : ℝ) :
      completionExt .lower (F .lower) a Y S z =
        Shao.C2.HalfLinePhysicalGaussian.lowerCompletion a Y S z := by
    rw [hExtL]
    exact congrFun (congrFun
      (Shao.C2.BridgeLowerIdentification.source_lower_eq_scalar B PB hB a z ha hz) Y) S
  have hFIimage (hz : |z| < a) (Y S : ℝ) (hY : |Y| ≤ a) (hS : 0 < S) :
      completionExt .interval (F .interval) a Y S z =
        Shao.C2.IntervalImageCandidateSpatial.intervalImageCandidate a z S Y := by
    rw [hExtI]
    exact Shao.C2.BridgeIntervalImageResolved.sourceIntervalCompletion_eq_image B PB hB
      a z S Y ha hz hS hY
  have hFYI (hz : |z| < a) :
      FY .interval (a, y, T, z) =
        deriv (Shao.C2.IntervalImageCandidateSpatial.intervalImageCandidate a z T) y := by
    have heq : (fun w : ℝ => eventCompletionKernel .interval Q (a, w, T, z)) =
        (fun w : ℝ => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q a w T z) := by
      funext w
      rw [Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion_pos Q a w T z hT]
      rfl
    change intervalDerivative Q (a, y, T, z) = _
    rw [intervalDerivative, if_pos ⟨ha, hT, hy, hz⟩, heq]
    exact (Shao.C2.BridgeIntervalImageResolved.sourceIntervalCompletion_spatial_hasDerivAt
      B PB hB a y T z ha hy hz hT).deriv
  have hFYU : FY .upper (a, y, T, z) = -Shao.C2.HalfLineMixedProfiles.slopeTime (a - y) (a - z) T := rfl
  have hFYL : FY .lower (a, y, T, z) = Shao.C2.HalfLineMixedProfiles.slopeTime (a + y) (a + z) T := rfl
  have hMzero (Y S : ℝ) :
      M 0 0 Y S = 1 + Shao.C2.IntervalImageCandidateSpatial.intervalImageCandidate a z S Y -
        Shao.C2.HalfLineReflectionFormula.upperReflection a Y S z -
        Shao.C2.HalfLineReflectionFormula.lowerReflection a Y S z := by
    have hB0 : Shao.C2.IntervalImageMixedIntSeries.mixedImageB 0 0 a z S Y 0 =
        Real.exp (-2 * (a + Y) * (a + z) / S) := by
      simp only [Shao.C2.IntervalImageMixedIntSeries.mixedImageB,
        Shao.C2.IntervalImageIntSeries.spatialImageB, iteratedDeriv_zero]
      congr 1
      dsimp only [Shao.C2.IntervalImageExponents.imageB]
      norm_num
      ring
    have hBn : Shao.C2.IntervalImageMixedIntSeries.mixedImageB 0 0 a z S Y (-1) =
        Real.exp (-2 * (a - Y) * (a - z) / S) := by
      simp only [Shao.C2.IntervalImageMixedIntSeries.mixedImageB,
        Shao.C2.IntervalImageIntSeries.spatialImageB, iteratedDeriv_zero]
      congr 1
      dsimp only [Shao.C2.IntervalImageExponents.imageB]
      norm_num
      ring
    dsimp only [M]
    simp only [and_self, if_true, Shao.C2.IntervalImageMixedCandidate.mixedImageCandidate_zero, hB0, hBn]
    dsimp only [Shao.C2.IntervalImageCandidateSpatial.intervalImageCandidate,
      Shao.C2.HalfLineReflectionFormula.upperReflection, Shao.C2.HalfLineReflectionFormula.lowerReflection]
    ring
  have hMone (hz : |z| < a) :
      M 1 0 y T = FY .interval (a, y, T, z) -
        FY .upper (a, y, T, z) - FY .lower (a, y, T, z) := by
    have hI := Shao.C2.IntervalImageCandidateSpatial.imageCandidateSpatial_hasDerivAt
      0 a z T y ha hz.le hT hy
    change HasDerivAt (Shao.C2.IntervalImageCandidateSpatial.intervalImageCandidate a z T)
      (Shao.C2.IntervalImageCandidateSpatial.imageCandidateSpatial 1 a z T y) y at hI
    have hU : HasDerivAt (fun w : ℝ => Shao.C2.HalfLineReflectionFormula.upperReflection a w T z)
        (-Shao.C2.HalfLineMixedProfiles.slopeTime (a - y) (a - z) T) y := by
      convert Shao.C2.HalfLineReflectionFormula.upperReflection_hasDerivAt a y T z using 1
      dsimp only [Shao.C2.HalfLineMixedProfiles.slopeTime]
      ring
    have hD := (((hasDerivAt_const y (1 : ℝ)).add hI).sub hU).sub
      (Shao.C2.HalfLineReflectionFormula.lowerReflection_hasDerivAt a y T z)
    have hDE : HasDerivAt (fun w : ℝ => M 0 0 w T)
        (Shao.C2.IntervalImageCandidateSpatial.imageCandidateSpatial 1 a z T y -
          (-Shao.C2.HalfLineMixedProfiles.slopeTime (a - y) (a - z) T) -
            Shao.C2.HalfLineMixedProfiles.slopeTime (a + y) (a + z) T) y := by
      convert hD using 1 <;> (try funext w)
      · exact hMzero w T
      · dsimp only [Shao.C2.HalfLineMixedProfiles.slopeTime]; ring
    rw [hFYI hz, hFYU, hFYL, hI.deriv]
    exact (hMspace 0 0 y T (by norm_num) hz.le hT hy).unique hDE
  have hSourceRetained (J : MonitoredDomain) :
      sourceRetainedRemainder J (F J) (FY J) pop x (fun _ => n) r.val sigma =
        if Interior J a z then localRetainedRemainder J (F J) (FY J) a y T z b else 0 := by
    unfold sourceRetainedRemainder
    rw [dif_pos r.is_lt]
    change (if r.val < n ∧ sourceAlive J pop x r.val sigma ∧ 0 < T then
      localRetainedRemainder J (F J) (FY J) a y T z b else 0) = _
    simp only [r.is_lt, true_and, hT, and_true, halive]
  have hBase (J : MonitoredDomain) (hzJ : Interior J a z) :
      F J (a, y, T, z) = completionExt J (F J) a y T z := by
    have hyJ : Interior J a y := hpre J r.val le_rfl
    rw [completionExt, if_pos
      (show 0 < a ∧ Interior J a y ∧ Interior J a z from ⟨ha, hyJ, hzJ⟩), if_pos hT]
  have hExtDead (J : MonitoredDomain) (hzJ : ¬Interior J a z) (Y S : ℝ) :
      completionExt J (F J) a Y S z = 0 := by
    unfold completionExt
    exact if_neg (fun hh => hzJ hh.2.2)
  have hEUclosed (hz : z < a) (Y S : ℝ) (hY : Y ≤ a) (hS : 0 < S) :
      completionExt .upper (F .upper) a Y S z =
        Shao.C2.HalfLineReflectionFormula.upperReflection a Y S z := by
    rw [hExtU_scalar hz]
    exact Shao.C2.HalfLineGaussianStep.completion_positive_time
      (a - Y) (a - z) S (sub_nonneg.mpr hY) (sub_pos.mpr hz) hS
  have hELclosed (hz : -a < z) (Y S : ℝ) (hY : -a ≤ Y) (hS : 0 < S) :
      completionExt .lower (F .lower) a Y S z =
        Shao.C2.HalfLineReflectionFormula.lowerReflection a Y S z := by
    rw [hExtL_scalar hz]
    exact Shao.C2.HalfLineGaussianStep.completion_positive_time
      (a + Y) (a + z) S (by linarith only [hY]) (by linarith only [hz]) hS
  have hZinner (hz : |z| < a) (Y S : ℝ) (hY : |Y| ≤ a) (hS : 0 < S) :
      Z Y S = M 0 0 Y S := by
    dsimp only [Z]
    rw [hFIimage hz Y S hY hS,
      hEUclosed (abs_lt.mp hz).2 Y S (abs_le.mp hY).2 hS,
      hELclosed (abs_lt.mp hz).1 Y S (abs_le.mp hY).1 hS,
      hMzero]
  have hZYinner (hz : |z| < a) : ZY = M 1 0 y T := by
    dsimp only [ZY]
    rw [if_pos (abs_lt.mp hz).2, if_pos (abs_lt.mp hz).1, hMone hz]
  have hFYI_dead (hz : ¬|z| < a) : FY .interval (a, y, T, z) = 0 := by
    change intervalDerivative Q (a, y, T, z) = 0
    exact if_neg (fun hh => hz hh.2.2.2)
  have hZterminal : Z z 0 = 0 := by
    by_cases hu : z < a <;> by_cases hl : -a < z
    · simp [Z, completionExt, Interior, ha, hu, hl]
    · simp [Z, completionExt, Interior, ha, hu, hl]
    · simp [Z, completionExt, Interior, ha, hu, hl]
    · exfalso
      linarith only [ha, le_of_not_gt hu, le_of_not_gt hl]
  have hSingleLarge (J : MonitoredDomain) (hbig : ¬b ^ 2 ≤ T / 2) :
      sourceRetainedRemainder J (F J) (FY J) pop x (fun _ => n) r.val sigma =
        completionExt J (F J) a (y + b) (T - b ^ 2) z -
          completionExt J (F J) a y T z -
            compensationCoefficient b (z - y) T *
              (if Interior J a z then FY J (a, y, T, z) else 0) := by
    rw [hSourceRetained]
    by_cases hzJ : Interior J a z
    · rw [if_pos hzJ, localRetainedRemainder, if_neg (show ¬(0 < T ∧ b ^ 2 ≤ T / 2) from fun hh => hbig hh.2), localRemainder,
        if_pos hzJ, hBase J hzJ]
    · rw [if_neg hzJ, if_neg hzJ, hExtDead J hzJ, hExtDead J hzJ]
      ring
  have hLlarge (hbig : ¬b ^ 2 ≤ T / 2) :
      L = Z (y + b) (T - b ^ 2) - Z y T - compensationCoefficient b (z - y) T * ZY := by
    have hi : (if Interior .interval a z then FY .interval (a, y, T, z) else 0) =
        FY .interval (a, y, T, z) := by
      by_cases hz : |z| < a
      · exact if_pos (show Interior .interval a z from abs_lt.mp hz)
      · rw [hFYI_dead hz]
        split_ifs <;> rfl
    dsimp only [L]
    rw [hSingleLarge .interval hbig, hSingleLarge .upper hbig, hSingleLarge .lower hbig, hi]
    dsimp only [Z, ZY, Interior, compensationCoefficient]
    ring_nf <;> rfl
  have hRZidentity (q : ℝ) (hz : |z| < a) (hq : q ^ 2 ≤ T / 2) (hnew : |y + q| ≤ a) :
      localRemainder .interval (F .interval) (FY .interval) a y T z q -
        localRemainder .upper (F .upper) (FY .upper) a y T z q -
        localRemainder .lower (F .lower) (FY .lower) a y T z q =
      M 0 0 (y + q) (T - q ^ 2) - M 0 0 y T -
        compensationCoefficient q (z - y) T * M 1 0 y T := by
    have hS : 0 < T - q ^ 2 := by linarith only [hT, hq]
    have hn := hZinner hz (y + q) (T - q ^ 2) hnew hS
    have ho := hZinner hz y T hy.le hT
    rw [← hn, ← ho, hMone hz]
    dsimp only [localRemainder]
    rw [hBase .interval (abs_lt.mp hz), hBase .upper (abs_lt.mp hz).2,
      hBase .lower (abs_lt.mp hz).1]
    dsimp only [Z]
    ring
  have hRUfar (q : ℝ) (hz : z < a) (hq : q ^ 2 ≤ T / 2)
      (hfar : ∀ theta : ℝ, 0 ≤ theta → theta ≤ 1 →
        (2 / 3 : ℝ) * a ^ 2 ≤ (a - y - theta * q) * (a - z)) :
      |localRemainder .upper (F .upper) (FY .upper) a y T z q| ≤
        Bill H * (|q| / Real.sqrt T) ^ 3 * D ^ 3 * Real.exp (-a ^ 2 / T) := by
    have hv : 0 < a - z := sub_pos.mpr hz
    have hu : 0 < a - y := sub_pos.mpr (abs_lt.mp hy).2
    have hn : 0 < a - y - q := by
      have hp : 0 < (a - y - q) * (a - z) := by
        simpa only [one_mul] using
          (show (0 : ℝ) < (2 / 3 : ℝ) * a ^ 2 by positivity).trans_le
            (hfar 1 (by norm_num) (by norm_num))
      by_contra hh
      have hc := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hh) hv.le
      linarith only [hp, hc]
    have hS : 0 < T - q ^ 2 := by linarith only [hT, hq]
    have heq : localRemainder .upper (F .upper) (FY .upper) a y T z q =
        Shao.C2.HalfLineTaylorPath.completionAlongSegment (a - y) (a - z) T q 1 -
          Shao.C2.HalfLineTaylorPath.completionAlongSegment (a - y) (a - z) T q 0 -
          (q - q ^ 2 * ((a - y) - (a - z)) / T) *
            (-Shao.C2.HalfLineMixedProfiles.slopeTime (a - y) (a - z) T) := by
      dsimp only [localRemainder]
      rw [hBase .upper hz, hExtU_scalar hz (y + q) (T - q ^ 2),
        hExtU_scalar hz y T, hFYU]
      dsimp only [Shao.C2.HalfLinePhysicalGaussian.upperCompletion]
      rw [Shao.C2.HalfLineGaussianStep.completion_positive_time
          (a - (y + q)) (a - z) (T - q ^ 2) (by linarith only [hn]) hv hS,
        Shao.C2.HalfLineGaussianStep.completion_positive_time (a - y) (a - z) T hu.le hv hT]
      dsimp only [Shao.C2.HalfLineTaylorPath.completionAlongSegment,
        Shao.C2.HalfLineTaylorSegment.segmentEnergy,
        Shao.C2.HalfLineTaylorSegment.segmentDistance, compensationCoefficient]
      simp only [one_mul, zero_mul, sub_zero]
      rw [show a - (y + q) = a - y - q by ring]
      ring
    rw [heq]
    exact hHalfTaylorFar (a - y) (a - z) q hv
      (by congr 1; ring) hq hfar
  have hRLfar (q : ℝ) (hz : -a < z) (hq : q ^ 2 ≤ T / 2)
      (hfar : ∀ theta : ℝ, 0 ≤ theta → theta ≤ 1 →
        (2 / 3 : ℝ) * a ^ 2 ≤ (a + y + theta * q) * (a + z)) :
      |localRemainder .lower (F .lower) (FY .lower) a y T z q| ≤
        Bill H * (|q| / Real.sqrt T) ^ 3 * D ^ 3 * Real.exp (-a ^ 2 / T) := by
    have hv : 0 < a + z := by linarith only [hz]
    have hu : 0 < a + y := by linarith only [(abs_lt.mp hy).1]
    have hn : 0 < a + y + q := by
      have hp : 0 < (a + y + q) * (a + z) := by
        simpa only [one_mul] using
          (show (0 : ℝ) < (2 / 3 : ℝ) * a ^ 2 by positivity).trans_le
            (hfar 1 (by norm_num) (by norm_num))
      by_contra hh
      have hc := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hh) hv.le
      linarith only [hp, hc]
    have hS : 0 < T - q ^ 2 := by linarith only [hT, hq]
    have heq : localRemainder .lower (F .lower) (FY .lower) a y T z q =
        Shao.C2.HalfLineTaylorPath.completionAlongSegment (a + y) (a + z) T (-q) 1 -
          Shao.C2.HalfLineTaylorPath.completionAlongSegment (a + y) (a + z) T (-q) 0 -
          (-q - (-q) ^ 2 * ((a + y) - (a + z)) / T) *
            (-Shao.C2.HalfLineMixedProfiles.slopeTime (a + y) (a + z) T) := by
      dsimp only [localRemainder]
      rw [hBase .lower hz, hExtL_scalar hz (y + q) (T - q ^ 2),
        hExtL_scalar hz y T, hFYL]
      dsimp only [Shao.C2.HalfLinePhysicalGaussian.lowerCompletion]
      rw [Shao.C2.HalfLineGaussianStep.completion_positive_time
          (a + (y + q)) (a + z) (T - q ^ 2) (by linarith only [hn]) hv hS,
        Shao.C2.HalfLineGaussianStep.completion_positive_time (a + y) (a + z) T hu.le hv hT]
      dsimp only [Shao.C2.HalfLineTaylorPath.completionAlongSegment,
        Shao.C2.HalfLineTaylorSegment.segmentEnergy,
        Shao.C2.HalfLineTaylorSegment.segmentDistance, compensationCoefficient]
      simp only [one_mul, zero_mul, sub_zero, neg_sq, sub_neg_eq_add]
      rw [show a + (y + q) = a + y + q by ring]
      ring
    rw [heq]
    have hh := hHalfTaylorFar (a + y) (a + z) (-q) hv
      (by rw [show (a + y) - (a + z) = y - z by ring, abs_sub_comm])
      (by simpa only [neg_sq] using hq) (by
        intro theta ht0 ht1
        simpa only [mul_neg, sub_neg_eq_add] using hfar theta ht0 ht1)
    simpa only [abs_neg] using hh
  have hExtStartDead (J : MonitoredDomain) (Y S : ℝ) (hY : ¬Interior J a Y) :
      completionExt J (F J) a Y S z = 0 := by
    unfold completionExt
    exact if_neg (fun hh => hY hh.2.1)
  have hFarExp (u v S : ℝ) (hS : 0 < S) (hST : S ≤ T)
      (huv : a ^ 2 / 2 ≤ u * v) :
      Real.exp (-2 * u * v / S) ≤ Real.exp (-a ^ 2 / T) := by
    have hn : a ^ 2 ≤ 2 * u * v := by linarith only [huv]
    have hn0 : 0 ≤ 2 * u * v := (sq_nonneg a).trans hn
    have hh := ((div_le_div_iff_of_pos_right hT).2 hn).trans
      (div_le_div_of_nonneg_left hn0 hS hST)
    apply Real.exp_le_exp.2
    convert neg_le_neg hh using 1 <;> ring
  have hFarUValue (Y S : ℝ) (hz : z < a) (hY : Y ≤ a) (hS : 0 < S) (hST : S ≤ T)
      (huv : a ^ 2 / 2 ≤ (a - Y) * (a - z)) :
      |1 - completionExt .upper (F .upper) a Y S z| ≤ Real.exp (-a ^ 2 / T) := by
    rw [hEUclosed hz Y S hY hS]
    unfold Shao.C2.HalfLineReflectionFormula.upperReflection
    rw [show (1 : ℝ) - (1 - Real.exp (-2 * (a - Y) * (a - z) / S)) =
        Real.exp (-2 * (a - Y) * (a - z) / S) by ring,
      abs_of_pos (Real.exp_pos _)]
    exact hFarExp (a - Y) (a - z) S hS hST huv
  have hFarLValue (Y S : ℝ) (hz : -a < z) (hY : -a ≤ Y) (hS : 0 < S) (hST : S ≤ T)
      (huv : a ^ 2 / 2 ≤ (a + Y) * (a + z)) :
      |1 - completionExt .lower (F .lower) a Y S z| ≤ Real.exp (-a ^ 2 / T) := by
    rw [hELclosed hz Y S hY hS]
    unfold Shao.C2.HalfLineReflectionFormula.lowerReflection
    rw [show (1 : ℝ) - (1 - Real.exp (-2 * (a + Y) * (a + z) / S)) =
        Real.exp (-2 * (a + Y) * (a + z) / S) by ring,
      abs_of_pos (Real.exp_pos _)]
    exact hFarExp (a + Y) (a + z) S hS hST huv
  have hZvalue (Y S : ℝ) (hS : 0 < S) (hST : S ≤ T)
      (hnear : |z - Y| ≤ (25 / 16 : ℝ) * a) :
      |Z Y S| ≤ 8 * Real.exp (-a ^ 2 / T) := by
    have hE0 : 0 ≤ Real.exp (-a ^ 2 / T) := (Real.exp_pos _).le
    have he8 : Real.exp (-a ^ 2 / T) ≤ 8 * Real.exp (-a ^ 2 / T) := by linarith only [hE0]
    by_cases hz : |z| < a
    · by_cases hY : |Y| ≤ a
      · rw [hZinner hz Y S hY hS, hMzero]
        exact arl_far_cancelled_value a Y z S T hT ha16 hS hST hY hz.le hnear
      · rcases lt_or_ge Y 0 with hYneg | hYpos
        · have hYwall : Y ≤ -a := by
            rw [abs_of_neg hYneg] at hY
            linarith only [hY]
          have hzU : z < a := (abs_lt.mp hz).2
          have h1 : 2 * a ≤ a - Y := by linarith only [hYwall]
          have h2 : (7 / 16 : ℝ) * a ≤ a - z := by
            linarith only [(abs_le.mp hnear).2, hYwall]
          have hp := mul_le_mul h1 h2 (by positivity : (0 : ℝ) ≤ 7 / 16 * a)
            (by linarith only [ha, h1] : (0 : ℝ) ≤ a - Y)
          have hv := hFarUValue Y S hzU (by linarith only [hYwall, ha]) hS hST
            (by nlinarith only [hp, sq_nonneg a])
          have hI : ¬Interior .interval a Y := by
            intro hh
            exact not_lt_of_ge hYwall hh.1
          have hD : ¬Interior .lower a Y := not_lt_of_ge hYwall
          have hh : |Z Y S| ≤ Real.exp (-a ^ 2 / T) := by
            simpa only [Z, hExtStartDead .interval Y S hI, hExtStartDead .lower Y S hD,
              add_zero, sub_zero] using hv
          exact hh.trans he8
        · have hYwall : a ≤ Y := by
            rw [abs_of_nonneg hYpos] at hY
            exact le_of_lt (lt_of_not_ge hY)
          have hzD : -a < z := (abs_lt.mp hz).1
          have h1 : 2 * a ≤ a + Y := by linarith only [hYwall]
          have h2 : (7 / 16 : ℝ) * a ≤ a + z := by
            linarith only [(abs_le.mp hnear).1, hYwall]
          have hp := mul_le_mul h1 h2 (by positivity : (0 : ℝ) ≤ 7 / 16 * a)
            (by linarith only [ha, h1] : (0 : ℝ) ≤ a + Y)
          have hv := hFarLValue Y S hzD (by linarith only [hYwall, ha]) hS hST
            (by nlinarith only [hp, sq_nonneg a])
          have hI : ¬Interior .interval a Y := by
            intro hh
            exact not_lt_of_ge hYwall hh.2
          have hU : ¬Interior .upper a Y := not_lt_of_ge hYwall
          have hh : |Z Y S| ≤ Real.exp (-a ^ 2 / T) := by
            simpa only [Z, hExtStartDead .interval Y S hI, hExtStartDead .upper Y S hU,
              add_zero, sub_zero] using hv
          exact hh.trans he8
    · rcases lt_or_ge z 0 with hzneg | hzpos
      · have hzwall : z ≤ -a := by
          rw [abs_of_neg hzneg] at hz
          linarith only [hz]
        have hzU : z < a := by linarith only [hzwall, ha]
        have h1 : (7 / 16 : ℝ) * a ≤ a - Y := by
          linarith only [(abs_le.mp hnear).1, hzwall]
        have h2 : 2 * a ≤ a - z := by linarith only [hzwall]
        have hp := mul_le_mul h1 h2 (by positivity : (0 : ℝ) ≤ 2 * a)
          (by linarith only [ha, h1] : (0 : ℝ) ≤ a - Y)
        have hv := hFarUValue Y S hzU (by linarith only [h1, ha]) hS hST
          (by nlinarith only [hp, sq_nonneg a])
        have hI : ¬Interior .interval a z := by intro hh; exact hz (abs_lt.mpr hh)
        have hD : ¬Interior .lower a z := not_lt_of_ge hzwall
        have hh : |Z Y S| ≤ Real.exp (-a ^ 2 / T) := by
          simpa only [Z, hExtDead .interval hI Y S, hExtDead .lower hD Y S,
            add_zero, sub_zero] using hv
        exact hh.trans he8
      · have hzwall : a ≤ z := by
          rw [abs_of_nonneg hzpos] at hz
          exact le_of_not_gt hz
        have hzD : -a < z := by linarith only [hzwall, ha]
        have h1 : (7 / 16 : ℝ) * a ≤ a + Y := by
          linarith only [(abs_le.mp hnear).2, hzwall]
        have h2 : 2 * a ≤ a + z := by linarith only [hzwall]
        have hp := mul_le_mul h1 h2 (by positivity : (0 : ℝ) ≤ 2 * a)
          (by linarith only [ha, h1] : (0 : ℝ) ≤ a + Y)
        have hv := hFarLValue Y S hzD (by linarith only [h1, ha]) hS hST
          (by nlinarith only [hp, sq_nonneg a])
        have hI : ¬Interior .interval a z := by intro hh; exact hz (abs_lt.mpr hh)
        have hU : ¬Interior .upper a z := not_lt_of_ge hzwall
        have hh : |Z Y S| ≤ Real.exp (-a ^ 2 / T) := by
          simpa only [Z, hExtDead .interval hI Y S, hExtDead .upper hU Y S,
            add_zero, sub_zero] using hv
        exact hh.trans he8
  have hGnonneg : 0 ≤ G := add_nonneg (hKnonneg 1 0) (hHnonneg 1 0)
  have hZgradient :
      |ZY| ≤ G * (1 / Real.sqrt T) * D * Real.exp (-a ^ 2 / T) := by
    have hKG : K 1 0 ≤ G := by dsimp only [G]; linarith only [hHnonneg 1 0]
    have hHG : H 1 0 ≤ G := by dsimp only [G]; linarith only [hKnonneg 1 0]
    have hD0 : 0 ≤ D := by dsimp only [D]; positivity
    by_cases hz : |z| < a
    · rw [hZYinner hz]
      have hm := hMbound 1 0 0 0 (by norm_num) hz.le
        (by linarith only [hT]) (by simpa using hy.le) (by norm_num) (by norm_num)
      simp only [zero_mul, sub_zero, add_zero, Nat.mul_zero, Nat.add_zero, pow_one] at hm
      calc
        _ ≤ K 1 0 * (1 / Real.sqrt T) * D * Real.exp (-a ^ 2 / T) := hm
        _ ≤ _ := by gcongr <;> assumption
    · rcases lt_or_ge z 0 with hzneg | hzpos
      · have hzw : z ≤ -a := by rw [abs_of_neg hzneg] at hz; linarith only [hz]
        have hzu : z < a := by linarith only [hzw, ha]
        have hyhi : y ≤ a / 2 := by linarith only [(abs_le.mp hda).1, hzw]
        have h1 : a / 2 ≤ a - y := by linarith only [hyhi]
        have h2 : 2 * a ≤ a - z := by linarith only [hzw]
        have hp := mul_le_mul h1 h2 (by positivity : (0 : ℝ) ≤ 2 * a)
          (by linarith only [ha, h1] : (0 : ℝ) ≤ a - y)
        have hh := (hHalfProfilesAt (a - y) (a - z) 0 0 (sub_pos.mpr hzu)
          (by congr 1; ring) (by linarith only [hT]) (by norm_num) (by norm_num)
          (by nlinarith only [hp, sq_nonneg a])).1
        have heq : ZY = Shao.C2.HalfLineMixedProfiles.slopeTime (a - y) (a - z) T := by
          dsimp only [ZY]
          rw [hFYI_dead hz, if_pos hzu, if_neg (not_lt_of_ge hzw), hFYU]
          ring
        rw [heq]
        calc
          _ ≤ H 1 0 * (1 / Real.sqrt T) * D * Real.exp (-a ^ 2 / T) := by
            simpa only [zero_mul, sub_zero] using hh
          _ ≤ _ := by gcongr <;> assumption
      · have hzw : a ≤ z := by rw [abs_of_nonneg hzpos] at hz; exact le_of_not_gt hz
        have hzd : -a < z := by linarith only [hzw, ha]
        have hylo : -a / 2 ≤ y := by linarith only [(abs_le.mp hda).2, hzw]
        have h1 : a / 2 ≤ a + y := by linarith only [hylo]
        have h2 : 2 * a ≤ a + z := by linarith only [hzw]
        have hp := mul_le_mul h1 h2 (by positivity : (0 : ℝ) ≤ 2 * a)
          (by linarith only [ha, h1] : (0 : ℝ) ≤ a + y)
        have hh := (hHalfProfilesAt (a + y) (a + z) 0 0 (by linarith only [hzd])
          (by rw [show (a + y) - (a + z) = y - z by ring, abs_sub_comm])
          (by linarith only [hT]) (by norm_num) (by norm_num)
          (by nlinarith only [hp, sq_nonneg a])).1
        have heq : ZY = -Shao.C2.HalfLineMixedProfiles.slopeTime (a + y) (a + z) T := by
          dsimp only [ZY]
          rw [hFYI_dead hz, if_neg (not_lt_of_ge hzw), if_pos hzd, hFYL]
          ring
        rw [heq, abs_neg]
        calc
          _ ≤ H 1 0 * (1 / Real.sqrt T) * D * Real.exp (-a ^ 2 / T) := by
            simpa only [zero_mul, sub_zero] using hh
          _ ≤ _ := by gcongr <;> assumption
  have hBillNonneg (J : ℕ → ℕ → ℝ) (hJ : ∀ j l, 0 ≤ J j l) : 0 ≤ Bill J := by
    have h30 := hJ 3 0
    have h21 := hJ 2 1
    have h12 := hJ 1 2
    have h03 := hJ 0 3
    have h11 := hJ 1 1
    have h02 := hJ 0 2
    dsimp only [Bill]
    positivity
  have hBK : 0 ≤ Bill K := hBillNonneg K hKnonneg
  have hBH : 0 ≤ Bill H := hBillNonneg H hHnonneg
  have hCoef : |compensationCoefficient b (z - y) T| ≤ |b| * D := by
    have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
    have hq0 : 0 ≤ |b| / Real.sqrt T := by positivity
    have hq1 : |b| / Real.sqrt T ≤ 1 := (div_le_one hs).2 hbabs
    have heq : b ^ 2 / T = (|b| / Real.sqrt T) ^ 2 := by
      rw [div_pow, sq_abs, Real.sq_sqrt hT.le]
    have hr : b ^ 2 / T ≤ |b| / Real.sqrt T := by
      rw [heq]
      nlinarith only [hq0, hq1]
    have hm : b ^ 2 * |z - y| / T ≤ |b| * (|z - y| / Real.sqrt T) := by
      convert mul_le_mul_of_nonneg_right hr (abs_nonneg (z - y)) using 1 <;> ring
    calc
      _ ≤ |b| + |b ^ 2 * (z - y) / T| := by
        simpa only [compensationCoefficient, sub_zero, zero_sub, abs_neg] using
          abs_sub_le b 0 (b ^ 2 * (z - y) / T)
      _ = |b| + b ^ 2 * |z - y| / T := by
        rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg b), abs_of_pos hT]
      _ ≤ |b| + |b| * (|z - y| / Real.sqrt T) := add_le_add le_rfl hm
      _ = _ := by dsimp only [D]; ring
  have hLarge (hbig : ¬b ^ 2 ≤ T / 2) :
      |L| ≤ C * (|b| / Real.sqrt T) ^ 3 * D ^ 3 * Real.exp (-a ^ 2 / T) := by
    let qq : ℝ := |b| / Real.sqrt T
    let EE : ℝ := Real.exp (-a ^ 2 / T)
    have hEE : 0 ≤ EE := (Real.exp_pos _).le
    have hD : 1 ≤ D := by
      dsimp only [D]
      linarith only [div_nonneg (abs_nonneg (z - y)) (Real.sqrt_nonneg T)]
    have hD0 : 0 ≤ D := zero_le_one.trans hD
    have hq0 : 0 ≤ qq := by dsimp only [qq]; positivity
    have hq2 : (1 / 2 : ℝ) ≤ qq ^ 2 := by
      have heq : qq ^ 2 = b ^ 2 / T := by
        dsimp only [qq]
        rw [div_pow, sq_abs, Real.sq_sqrt hT.le]
      rw [heq]
      apply (le_div_iff₀ hT).2
      linarith only [lt_of_not_ge hbig]
    have hq2' : (1 : ℝ) ≤ 2 * qq ^ 2 := by linarith only [hq2]
    have hqS : (1 : ℝ) ≤ Real.sqrt 2 * qq := by
      have hs : (Real.sqrt 2 * qq) ^ 2 = 2 * qq ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith only [hs, hq2', mul_nonneg (Real.sqrt_nonneg 2) hq0]
    have hq3 : (1 : ℝ) ≤ 2 * Real.sqrt 2 * qq ^ 3 := by
      have hh := mul_le_mul hqS hq2' (by norm_num : (0 : ℝ) ≤ 1)
        (mul_nonneg (Real.sqrt_nonneg 2) hq0)
      nlinarith only [hh]
    have hqD : qq * D ^ 2 ≤ 2 * qq ^ 3 * D ^ 3 := by
      have hq' : qq ≤ 2 * qq ^ 3 := by
        convert mul_le_mul_of_nonneg_left hq2' hq0 using 1 <;> ring
      calc
        _ ≤ 2 * qq ^ 3 * D ^ 2 := mul_le_mul_of_nonneg_right hq' (sq_nonneg D)
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hD (by norm_num : (2 : ℕ) ≤ 3)) (by positivity)
    have hconst : (16 : ℝ) ≤ 32 * Real.sqrt 2 * qq ^ 3 * D ^ 3 := by
      have hD3 : (1 : ℝ) ≤ D ^ 3 := one_le_pow₀ hD
      have hh := mul_le_mul hq3 hD3 (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
      nlinarith only [hh]
    have hNearOld : |z - y| ≤ (25 / 16 : ℝ) * a := by linarith only [hda, ha]
    have hNearNew : |z - (y + b)| ≤ (25 / 16 : ℝ) * a := by
      have hh : |z - (y + b)| ≤ |z - y| + |b| := by
        calc
          _ = |(z - y) + (-b)| := by congr 1; ring
          _ ≤ |z - y| + |-b| := abs_add_le _ _
          _ = _ := by rw [abs_neg]
      linarith only [hh, hda, hba]
    have hOld : |Z y T| ≤ 8 * EE := hZvalue y T hT le_rfl hNearOld
    have hNew : |Z (y + b) (T - b ^ 2)| ≤ 8 * EE := by
      by_cases hzT : T - b ^ 2 = 0
      · rw [hzero hzT, hzT, hZterminal]
        simpa only [abs_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hEE
      · exact hZvalue (y + b) (T - b ^ 2)
          (lt_of_le_of_ne hnewT (Ne.symm hzT)) (by linarith only [sq_nonneg b]) hNearNew
    have hGrad : |compensationCoefficient b (z - y) T * ZY| ≤ G * qq * D ^ 2 * EE := by
      rw [abs_mul]
      calc
        _ ≤ (|b| * D) * (G * (1 / Real.sqrt T) * D * EE) :=
          mul_le_mul hCoef hZgradient (abs_nonneg ZY) (mul_nonneg (abs_nonneg b) hD0)
        _ = _ := by dsimp only [qq]; ring
    have hCoarse : |L| ≤ 16 * EE + G * qq * D ^ 2 * EE := by
      rw [hLlarge hbig]
      apply abs_le.mpr
      constructor <;>
        nlinarith only [(abs_le.mp hOld).1, (abs_le.mp hOld).2,
          (abs_le.mp hNew).1, (abs_le.mp hNew).2,
          (abs_le.mp hGrad).1, (abs_le.mp hGrad).2]
    have hConstE := mul_le_mul_of_nonneg_right hconst hEE
    have hGradE := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hqD hGnonneg) hEE
    have hPaid : |L| ≤ (32 * Real.sqrt 2 + 2 * G) * qq ^ 3 * D ^ 3 * EE := by
      nlinarith only [hCoarse, hConstE, hGradE]
    have hDom : 32 * Real.sqrt 2 + 2 * G ≤ C := by
      dsimp only [C]
      linarith only [hBK, hBH]
    exact hPaid.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDom (pow_nonneg hq0 3))
        (pow_nonneg hD0 3)) hEE)
  have hScaleCubic (A q : ℝ) (hA : 0 ≤ A) (hq : |q| ≤ |b|) :
      A * (|q| / Real.sqrt T) ^ 3 * D ^ 3 * Real.exp (-a ^ 2 / T) ≤
        A * (|b| / Real.sqrt T) ^ 3 * D ^ 3 * Real.exp (-a ^ 2 / T) := by
    have hD0 : 0 ≤ D := by dsimp only [D]; positivity
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ |q| / Real.sqrt T)
      ((div_le_div_iff_of_pos_right (Real.sqrt_pos.2 hT)).2 hq) 3
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hh hA) (pow_nonneg hD0 3)) (Real.exp_pos _).le
  have hSmallDom : Bill K + 2 * Bill H ≤ C := by
    dsimp only [C]
    have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    linarith only [hGnonneg, hs]
  have hKDom : Bill K ≤ C := (by linarith only [hBH] : Bill K ≤ Bill K + 2 * Bill H).trans hSmallDom
  have hHDom : Bill H ≤ C := (by linarith only [hBK, hBH] : Bill H ≤ Bill K + 2 * Bill H).trans hSmallDom
  have hPay (A : ℝ) (hA : A ≤ C) (hh :
      |L| ≤ A * (|b| / Real.sqrt T) ^ 3 * D ^ 3 * Real.exp (-a ^ 2 / T)) :
      |L| ≤ C * (|b| / Real.sqrt T) ^ 3 * D ^ 3 * Real.exp (-a ^ 2 / T) := by
    have hD0 : 0 ≤ D := by dsimp only [D]; positivity
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hA (by positivity)) (pow_nonneg hD0 3)) (Real.exp_pos _).le)
  by_cases hsmall : b ^ 2 ≤ T / 2
  · by_cases hz : |z| < a
    · have hzI : Interior .interval a z := abs_lt.mp hz
      have hzU : Interior .upper a z := (abs_lt.mp hz).2
      have hzD : Interior .lower a z := (abs_lt.mp hz).1
      by_cases hcrossU : a ≤ y + b
      · let p : ℝ := a - y
        have hp : 0 < p := sub_pos.mpr (abs_lt.mp hy).2
        have hpb : p ≤ b := by dsimp only [p]; linarith only [hcrossU]
        have hbpos : 0 < b := hp.trans_le hpb
        have hpabs : |p| ≤ |b| := by rw [abs_of_pos hp, abs_of_pos hbpos]; exact hpb
        have hp2 : p ^ 2 ≤ b ^ 2 := by
          have hh := mul_nonneg (sub_nonneg.mpr hpb) (add_nonneg hp.le hbpos.le)
          nlinarith only [hh]
        have hpsmall : p ^ 2 ≤ T / 2 := hp2.trans hsmall
        have hpnew : |y + p| ≤ a := by
          have heq : y + p = a := by dsimp only [p]; ring
          rw [heq, abs_of_pos ha]
        have hnotD : ¬y + b ≤ -a := by linarith only [hcrossU, ha]
        have hLeq : L =
            localRemainder .interval (F .interval) (FY .interval) a y T z p -
              localRemainder .upper (F .upper) (FY .upper) a y T z p -
              localRemainder .lower (F .lower) (FY .lower) a y T z b := by
          simp only [L, hSourceRetained, if_pos hzI, if_pos hzU, if_pos hzD,
            localRetainedRemainder, if_pos (show 0 < T ∧ b ^ 2 ≤ T / 2 from ⟨hT, hsmall⟩), projectionIncrement,
            if_pos hcrossU, if_neg hnotD, p]
        have hyhi : (15 / 16 : ℝ) * a ≤ y := by
          linarith only [hcrossU, hba, le_abs_self b]
        have hzlo : -(9 / 16 : ℝ) * a ≤ z := by
          linarith only [(abs_le.mp hda).1, hyhi]
        have hFar (q : ℝ) (hq0 : 0 ≤ q) (theta : ℝ) (ht0 : 0 ≤ theta) (_ : theta ≤ 1) :
            (2 / 3 : ℝ) * a ^ 2 ≤ (a + y + theta * q) * (a + z) := by
          have h1 : (31 / 16 : ℝ) * a ≤ a + y + theta * q := by
            linarith only [hyhi, mul_nonneg ht0 hq0]
          have h2 : (7 / 16 : ℝ) * a ≤ a + z := by linarith only [hzlo]
          have hh := mul_le_mul h1 h2 (by positivity : (0 : ℝ) ≤ 7 / 16 * a)
            (by linarith only [h1, ha] : (0 : ℝ) ≤ a + y + theta * q)
          nlinarith only [hh, sq_nonneg a]
        have hMp := (hMtaylor p hz.le hpsmall hpnew).trans (hScaleCubic (Bill K) p hBK hpabs)
        have hLp := (hRLfar p hzD hpsmall (hFar p hp.le)).trans (hScaleCubic (Bill H) p hBH hpabs)
        have hLb := hRLfar b hzD hsmall (hFar b hbpos.le)
        have hRID := hRZidentity p hz hpsmall hpnew
        have hRewrite : L =
            (M 0 0 (y + p) (T - p ^ 2) - M 0 0 y T -
              compensationCoefficient p (z - y) T * M 1 0 y T) +
            localRemainder .lower (F .lower) (FY .lower) a y T z p -
            localRemainder .lower (F .lower) (FY .lower) a y T z b := by
          linarith only [hLeq, hRID]
        apply hPay (Bill K + 2 * Bill H) hSmallDom
        rw [hRewrite]
        dsimp only [compensationCoefficient]
        apply abs_le.mpr
        constructor <;>
          nlinarith only [(abs_le.mp hMp).1, (abs_le.mp hMp).2,
            (abs_le.mp hLp).1, (abs_le.mp hLp).2, (abs_le.mp hLb).1, (abs_le.mp hLb).2]
      · by_cases hcrossD : y + b ≤ -a
        · let p : ℝ := -a - y
          have hp : p < 0 := by dsimp only [p]; linarith only [(abs_lt.mp hy).1]
          have hbp : b ≤ p := by dsimp only [p]; linarith only [hcrossD]
          have hbneg : b < 0 := hbp.trans_lt hp
          have hpabs : |p| ≤ |b| := by rw [abs_of_neg hp, abs_of_neg hbneg]; linarith only [hbp]
          have hp2 : p ^ 2 ≤ b ^ 2 := by
            have hh := mul_nonneg (sub_nonneg.mpr hbp) (neg_nonneg.mpr (add_nonpos hp.le hbneg.le))
            nlinarith only [hh]
          have hpsmall : p ^ 2 ≤ T / 2 := hp2.trans hsmall
          have hpnew : |y + p| ≤ a := by
            have heq : y + p = -a := by dsimp only [p]; ring
            rw [heq, abs_neg, abs_of_pos ha]
          have hLeq : L =
              localRemainder .interval (F .interval) (FY .interval) a y T z p -
                localRemainder .upper (F .upper) (FY .upper) a y T z b -
                localRemainder .lower (F .lower) (FY .lower) a y T z p := by
            simp only [L, hSourceRetained, if_pos hzI, if_pos hzU, if_pos hzD,
              localRetainedRemainder, if_pos (show 0 < T ∧ b ^ 2 ≤ T / 2 from ⟨hT, hsmall⟩), projectionIncrement,
              if_neg hcrossU, if_pos hcrossD, p]
          have hylo : y ≤ -(15 / 16 : ℝ) * a := by
            linarith only [hcrossD, hba, neg_abs_le b]
          have hzhi : z ≤ (9 / 16 : ℝ) * a := by
            linarith only [(abs_le.mp hda).2, hylo]
          have hFar (q : ℝ) (hq0 : q ≤ 0) (theta : ℝ) (ht0 : 0 ≤ theta) (_ : theta ≤ 1) :
              (2 / 3 : ℝ) * a ^ 2 ≤ (a - y - theta * q) * (a - z) := by
            have h1 : (31 / 16 : ℝ) * a ≤ a - y - theta * q := by
              linarith only [hylo, mul_nonpos_of_nonneg_of_nonpos ht0 hq0]
            have h2 : (7 / 16 : ℝ) * a ≤ a - z := by linarith only [hzhi]
            have hh := mul_le_mul h1 h2 (by positivity : (0 : ℝ) ≤ 7 / 16 * a)
              (by linarith only [h1, ha] : (0 : ℝ) ≤ a - y - theta * q)
            nlinarith only [hh, sq_nonneg a]
          have hMp := (hMtaylor p hz.le hpsmall hpnew).trans (hScaleCubic (Bill K) p hBK hpabs)
          have hUp := (hRUfar p hzU hpsmall (hFar p hp.le)).trans (hScaleCubic (Bill H) p hBH hpabs)
          have hUb := hRUfar b hzU hsmall (hFar b hbneg.le)
          have hRID := hRZidentity p hz hpsmall hpnew
          have hRewrite : L =
              (M 0 0 (y + p) (T - p ^ 2) - M 0 0 y T -
                compensationCoefficient p (z - y) T * M 1 0 y T) +
              localRemainder .upper (F .upper) (FY .upper) a y T z p -
              localRemainder .upper (F .upper) (FY .upper) a y T z b := by
            linarith only [hLeq, hRID]
          apply hPay (Bill K + 2 * Bill H) hSmallDom
          rw [hRewrite]
          dsimp only [compensationCoefficient]
          apply abs_le.mpr
          constructor <;>
            nlinarith only [(abs_le.mp hMp).1, (abs_le.mp hMp).2,
              (abs_le.mp hUp).1, (abs_le.mp hUp).2, (abs_le.mp hUb).1, (abs_le.mp hUb).2]
        · have hnew : |y + b| < a := abs_lt.mpr ⟨lt_of_not_ge hcrossD, lt_of_not_ge hcrossU⟩
          have hLeq : L =
              localRemainder .interval (F .interval) (FY .interval) a y T z b -
                localRemainder .upper (F .upper) (FY .upper) a y T z b -
                localRemainder .lower (F .lower) (FY .lower) a y T z b := by
            simp only [L, hSourceRetained, if_pos hzI, if_pos hzU, if_pos hzD,
              localRetainedRemainder, if_pos (show 0 < T ∧ b ^ 2 ≤ T / 2 from ⟨hT, hsmall⟩), projectionIncrement,
              if_neg hcrossU, if_neg hcrossD]
          apply hPay (Bill K) hKDom
          rw [hLeq, hRZidentity b hz hsmall hnew.le]
          exact hMtaylor b hz.le hsmall hnew.le
    · rcases lt_or_ge z 0 with hzneg | hzpos
      · have hzw : z ≤ -a := by rw [abs_of_neg hzneg] at hz; linarith only [hz]
        have hzu : z < a := by linarith only [hzw, ha]
        have hyhi : y ≤ a / 2 := by linarith only [(abs_le.mp hda).1, hzw]
        have hcrossU : ¬a ≤ y + b := by
          intro hh
          linarith only [hh, hyhi, hba, le_abs_self b, ha]
        have hI : ¬Interior .interval a z := by intro hh; exact hz (abs_lt.mpr hh)
        have hD : ¬Interior .lower a z := not_lt_of_ge hzw
        have hLeq : L = -localRemainder .upper (F .upper) (FY .upper) a y T z b := by
          simp only [L, hSourceRetained, if_neg hI, if_neg hD, if_pos (show Interior .upper a z from hzu),
            localRetainedRemainder, if_pos (show 0 < T ∧ b ^ 2 ≤ T / 2 from ⟨hT, hsmall⟩), projectionIncrement,
            if_neg hcrossU, zero_sub, sub_zero]
        have hFar (theta : ℝ) (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) :
            (2 / 3 : ℝ) * a ^ 2 ≤ (a - y - theta * b) * (a - z) := by
          have htB : theta * b ≤ |b| := by
            exact (mul_le_mul_of_nonneg_left (le_abs_self b) ht0).trans
              (by simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1 (abs_nonneg b))
          have h1 : (7 / 16 : ℝ) * a ≤ a - y - theta * b := by
            linarith only [hyhi, htB, hba]
          have h2 : 2 * a ≤ a - z := by linarith only [hzw]
          have hh := mul_le_mul h1 h2 (by positivity : (0 : ℝ) ≤ 2 * a)
            (by linarith only [h1, ha] : (0 : ℝ) ≤ a - y - theta * b)
          nlinarith only [hh, sq_nonneg a]
        apply hPay (Bill H) hHDom
        rw [hLeq, abs_neg]
        exact hRUfar b hzu hsmall hFar
      · have hzw : a ≤ z := by rw [abs_of_nonneg hzpos] at hz; exact le_of_not_gt hz
        have hzd : -a < z := by linarith only [hzw, ha]
        have hylo : -a / 2 ≤ y := by linarith only [(abs_le.mp hda).2, hzw]
        have hcrossD : ¬y + b ≤ -a := by
          intro hh
          linarith only [hh, hylo, hba, neg_abs_le b, ha]
        have hI : ¬Interior .interval a z := by intro hh; exact hz (abs_lt.mpr hh)
        have hU : ¬Interior .upper a z := not_lt_of_ge hzw
        have hLeq : L = -localRemainder .lower (F .lower) (FY .lower) a y T z b := by
          simp only [L, hSourceRetained, if_neg hI, if_neg hU, if_pos (show Interior .lower a z from hzd),
            localRetainedRemainder, if_pos (show 0 < T ∧ b ^ 2 ≤ T / 2 from ⟨hT, hsmall⟩), projectionIncrement,
            if_neg hcrossD, sub_zero, zero_sub]
        have hFar (theta : ℝ) (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) :
            (2 / 3 : ℝ) * a ^ 2 ≤ (a + y + theta * b) * (a + z) := by
          have htB : -|b| ≤ theta * b := by
            have h1 := mul_le_mul_of_nonneg_left (neg_abs_le b) ht0
            have h2 := mul_le_mul_of_nonneg_right ht1 (abs_nonneg b)
            nlinarith only [h1, h2]
          have h1 : (7 / 16 : ℝ) * a ≤ a + y + theta * b := by
            linarith only [hylo, htB, hba]
          have h2 : 2 * a ≤ a + z := by linarith only [hzw]
          have hh := mul_le_mul h1 h2 (by positivity : (0 : ℝ) ≤ 2 * a)
            (by linarith only [h1, ha] : (0 : ℝ) ≤ a + y + theta * b)
          nlinarith only [hh, sq_nonneg a]
        apply hPay (Bill H) hHDom
        rw [hLeq, abs_neg]
        exact hRLfar b hzd hsmall hFar
  · exact hLarge hsmall

end Shao.Probability.SourceActualRegularLocal
