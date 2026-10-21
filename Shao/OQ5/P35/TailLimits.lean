import Shao.OQ5.P35.RareTailLowerBound
import Shao.OQ5.P35.GaussianTail

/-!
# Actual tail limits for the p35 counterexample

Source: original p35 §7. The limits concern the actual sample statistic and
actual standard Gaussian upper tail. All estimates are discharged by the
accepted rare-event lower bound and complete deterministic threshold scales.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

def p35TailProbability (n : ℕ) : ℝ :=
  sampleLaw.real {ω | counterexampleThreshold n ≤ sampleStatistic n ω}

def counterexampleWindow (n : ℕ) : ℝ := 2 * counterexampleThreshold n

theorem p35TailProbability_nonneg (n : ℕ) : 0 ≤ p35TailProbability n :=
  ENNReal.toReal_nonneg

theorem p35TailProbability_le_one (n : ℕ) : p35TailProbability n ≤ 1 := by
  simpa only [p35TailProbability, probReal_univ] using
    (measureReal_mono (μ := sampleLaw)
      (Set.subset_univ {ω | counterexampleThreshold n ≤ sampleStatistic n ω}))

theorem p35TailProbability_eventually_pos :
    ∀ᶠ j : ℕ in atTop, 0 < p35TailProbability (rareSampleSize j) :=
  rare_tail_probability_eventually_pos

private theorem threshold_half_pos (j : ℕ) :
    0 < counterexampleThreshold (rareSampleSize j)^2/2 := by
  rw [counterexampleThreshold_sq_half_rareSampleSize]
  exact div_pos (Real.rpow_pos_of_pos (by linarith [categoryScale_one_le j]) _) (by norm_num)

private theorem threshold_half_tendsto :
    Tendsto (fun j : ℕ => counterexampleThreshold (rareSampleSize j)^2/2) atTop atTop := by
  have hk : Tendsto categoryScale atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 4)
  have h := Tendsto.atTop_div_const (by norm_num : (0:ℝ) < 512)
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 6/5)).comp hk)
  exact h.congr (fun j => (counterexampleThreshold_sq_half_rareSampleSize j).symm)

/-- Positivity is established before logarithms; negating the log reverses its bound. -/
private theorem log_ratio_bounds :
    ∀ᶠ j : ℕ in atTop,
      0 ≤ Real.log (p35TailProbability (rareSampleSize j)) /
          (-(counterexampleThreshold (rareSampleSize j)^2)/2) ∧
      Real.log (p35TailProbability (rareSampleSize j)) /
          (-(counterexampleThreshold (rareSampleSize j)^2)/2) ≤
        (5*categoryScale j*Real.log (categoryScale j)+Real.log 2) /
          (counterexampleThreshold (rareSampleSize j)^2/2) := by
  filter_upwards [p35TailProbability_eventually_pos, rare_tail_probability_half_lower]
    with j hp hhalf
  have hb := threshold_half_pos j
  have hlower : -(5*categoryScale j*Real.log (categoryScale j))-Real.log 2 ≤
      Real.log (p35TailProbability (rareSampleSize j)) := by
    have hlog := Real.log_le_log (mul_pos (by norm_num : (0:ℝ) < 1/2) (Real.exp_pos _)) hhalf
    rw [Real.log_mul (by norm_num : (1/2:ℝ) ≠ 0) (Real.exp_ne_zero _),
      Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
      Real.log_one, Real.log_exp] at hlog
    change _ ≤ Real.log (p35TailProbability (rareSampleSize j)) at hlog
    linarith
  have hupper : Real.log (p35TailProbability (rareSampleSize j)) ≤ 0 :=
    Real.log_nonpos hp.le (p35TailProbability_le_one _)
  have he : Real.log (p35TailProbability (rareSampleSize j)) /
      (-(counterexampleThreshold (rareSampleSize j)^2)/2) =
      -Real.log (p35TailProbability (rareSampleSize j)) /
        (counterexampleThreshold (rareSampleSize j)^2/2) := by ring
  rw [he]
  constructor
  · exact div_nonneg (neg_nonneg.mpr hupper) hb.le
  · apply (div_le_div_iff_of_pos_right hb).mpr
    linarith

theorem p35LogTailRatio_tendsto_zero :
    Tendsto (fun j : ℕ => Real.log (p35TailProbability (rareSampleSize j)) /
      (-(counterexampleThreshold (rareSampleSize j)^2)/2)) atTop (nhds 0) := by
  have hconst := threshold_half_tendsto.const_div_atTop (Real.log 2)
  have hbound : Tendsto (fun j : ℕ =>
      (5*categoryScale j*Real.log (categoryScale j)+Real.log 2) /
        (counterexampleThreshold (rareSampleSize j)^2/2)) atTop (nhds 0) := by
    have h := rareLogCost_div_threshold_sq_tendsto_zero.add hconst
    have hlim : Tendsto (fun j : ℕ =>
        (5*categoryScale j*Real.log (categoryScale j))/(counterexampleThreshold (rareSampleSize j)^2/2) +
        Real.log 2/(counterexampleThreshold (rareSampleSize j)^2/2)) atTop (nhds 0) := by
      simpa only [zero_add] using h
    exact hlim.congr (fun j => (add_div _ _ _).symm)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
  · exact log_ratio_bounds.mono (fun _ h => h.1)
  · exact log_ratio_bounds.mono (fun _ h => h.2)

private theorem tail_exponent_tendsto :
    Tendsto (fun j : ℕ => counterexampleThreshold (rareSampleSize j)^2/2 -
      5*categoryScale j*Real.log (categoryScale j)) atTop atTop := by
  have hcost : ∀ᶠ j : ℕ in atTop,
      (5*categoryScale j*Real.log (categoryScale j)) /
        (counterexampleThreshold (rareSampleSize j)^2/2) ≤ (1/2:ℝ) :=
    rareLogCost_div_threshold_sq_tendsto_zero.eventually
      (eventually_le_nhds (by norm_num : (0:ℝ) < 1/2))
  apply tendsto_atTop_mono' atTop _ (threshold_half_tendsto.atTop_div_const (by norm_num : (0:ℝ)<2))
  filter_upwards [hcost] with j hj
  have h := (div_le_iff₀ (threshold_half_pos j)).mp hj
  linarith

/-- Comparison uses the genuine positive Gaussian tail and the actual half-exponential lower bound. -/
private theorem relative_ratio_lower :
    ∀ᶠ j : ℕ in atTop,
      (1/2:ℝ)*Real.exp (counterexampleThreshold (rareSampleSize j)^2/2 -
        5*categoryScale j*Real.log (categoryScale j)) ≤
      p35TailProbability (rareSampleSize j) /
        standardNormalUpperTail (counterexampleThreshold (rareSampleSize j)) := by
  filter_upwards [rare_tail_probability_half_lower] with j hp
  have hn : 1 ≤ rareSampleSize j := by
    have hpos : 0 < rareSampleSize j := by
      unfold rareSampleSize targetCategoryCount
      positivity
    omega
  have hx := (counterexampleThreshold_pos _ hn).le
  have hψ := standardNormalUpperTail_pos (counterexampleThreshold (rareSampleSize j))
  apply (le_div_iff₀ hψ).mpr
  calc
    _ ≤ ((1/2:ℝ)*Real.exp (counterexampleThreshold (rareSampleSize j)^2/2 -
        5*categoryScale j*Real.log (categoryScale j)))*
        Real.exp (-(counterexampleThreshold (rareSampleSize j)^2)/2) :=
      mul_le_mul_of_nonneg_left (standardNormalUpperTail_le_exp _ hx) (by positivity)
    _ = (1/2:ℝ)*Real.exp (-5*categoryScale j*Real.log (categoryScale j)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ p35TailProbability (rareSampleSize j) := hp

theorem p35RelativeTailRatio_tendsto_atTop :
    Tendsto (fun j : ℕ => p35TailProbability (rareSampleSize j) /
      standardNormalUpperTail (counterexampleThreshold (rareSampleSize j))) atTop atTop := by
  have hExp := Real.tendsto_exp_atTop.comp tail_exponent_tendsto
  have hLower : Tendsto (fun j : ℕ => (1/2:ℝ)*Real.exp
      (counterexampleThreshold (rareSampleSize j)^2/2 -
        5*categoryScale j*Real.log (categoryScale j))) atTop atTop := by
    have h := hExp.atTop_div_const (by norm_num : (0:ℝ) < 2)
    exact h.congr (fun j => by dsimp only [Function.comp_def]; ring)
  exact tendsto_atTop_mono' atTop relative_ratio_lower hLower

theorem p35LogTailRatio_not_tendsto_one :
    ¬ Tendsto (fun n : ℕ => Real.log (p35TailProbability n) /
      (-(counterexampleThreshold n^2)/2)) atTop (nhds 1) := by
  intro h
  have hsub := h.comp rareSampleSize_tendsto
  have h01 := tendsto_nhds_unique p35LogTailRatio_tendsto_zero hsub
  norm_num at h01

theorem p35RelativeTailRatio_not_tendsto_one :
    ¬ Tendsto (fun n : ℕ => p35TailProbability n /
      standardNormalUpperTail (counterexampleThreshold n)) atTop (nhds 1) := by
  intro h
  have hb : ∀ᶠ j : ℕ in atTop,
      p35TailProbability (rareSampleSize j) /
        standardNormalUpperTail (counterexampleThreshold (rareSampleSize j)) ≤ 2 :=
    (h.comp rareSampleSize_tendsto).eventually (eventually_le_nhds (by norm_num : (1:ℝ)<2))
  have hg : ∀ᶠ j : ℕ in atTop, 3 ≤
      p35TailProbability (rareSampleSize j) /
        standardNormalUpperTail (counterexampleThreshold (rareSampleSize j)) :=
    p35RelativeTailRatio_tendsto_atTop.eventually (eventually_ge_atTop 3)
  obtain ⟨j,hj,hj'⟩ := (hb.and hg).exists
  linarith

theorem counterexampleWindow_div_sixth_tendsto_zero :
    Tendsto (fun n : ℕ => counterexampleWindow n/(n:ℝ)^(1/6:ℝ)) atTop (nhds 0) := by
  have h := counterexampleThreshold_div_sixth_tendsto_zero.const_mul (2:ℝ)
  have hlim : Tendsto (fun n : ℕ => 2*(counterexampleThreshold n/(n:ℝ)^(1/6:ℝ)))
      atTop (nhds 0) := by simpa only [mul_zero] using h
  exact hlim.congr (fun n => by unfold counterexampleWindow; ring)

theorem counterexampleThreshold_mem_window (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ counterexampleThreshold n ∧ counterexampleThreshold n < counterexampleWindow n :=
  counterexampleThreshold_window n hn

theorem p35WindowUniformApproximation_false :
    ¬ (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ t : ℝ, 0 ≤ t → t < counterexampleWindow n →
        |sampleLaw.real {ω | t ≤ sampleStatistic n ω}/standardNormalUpperTail t-1| ≤ ε) := by
  intro h
  have hb := rareSampleSize_tendsto.eventually (h 1 (by norm_num))
  have hn := rareSampleSize_tendsto.eventually (eventually_ge_atTop 1)
  have hg : ∀ᶠ j : ℕ in atTop, 3 ≤
      p35TailProbability (rareSampleSize j) /
        standardNormalUpperTail (counterexampleThreshold (rareSampleSize j)) :=
    p35RelativeTailRatio_tendsto_atTop.eventually (eventually_ge_atTop 3)
  have hf : ∀ᶠ j : ℕ in atTop, False := by
    filter_upwards [hb,hn,hg] with j hj hn' hg'
    have hw := counterexampleThreshold_mem_window (rareSampleSize j) hn'
    have hle := hj (counterexampleThreshold (rareSampleSize j)) hw.1 hw.2
    have habs := (abs_le.mp hle).2
    change p35TailProbability (rareSampleSize j) /
      standardNormalUpperTail (counterexampleThreshold (rareSampleSize j))-1 ≤ 1 at habs
    linarith
  obtain ⟨j,hj⟩ := hf.exists
  exact hj

end

end Shao.OQ5.P35
