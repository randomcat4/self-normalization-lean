import Shao.OQ4.RandomDenominatorAsymptotic
import Shao.OQ4.PositiveBoundaryStudentized
import Shao.Probability.BrownianFirstTerm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

noncomputable section
namespace Shao.OQ4.OriginalWindowProduct
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
set_option autoImplicit false
variable {ΩB : Type*} [MeasurableSpace ΩB]

-- A01 PUBLIC full value. Fixed law, genuine random energy, all finite lengths.
def productProbability (ν : Measure ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (Measure.pi (fun _ : Fin n => ν)).real
    (RandomDenominatorFarTail.randomDenominatorEvent n (x * Real.sqrt (n : ℝ)))

-- A02 PUBLIC full value. The reference CDF is the actual supplied Brownian law.
def relativeError
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (ν : Measure ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  |productProbability ν n x / Shao.Probability.BrownianSup.probability B P hB x - 1|

-- A03 PUBLIC full value. Exact open source window, including early indices.
def windowValues
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (ν : Measure ℝ) (a : ℕ → ℝ) (n : ℕ) : Set ℝ :=
  (fun x : ℝ => relativeError B P hB ν n x) '' Ioo (a n) 1

-- A04 PUBLIC full value. Real conditional supremum, without early-index patching.
def windowError
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (ν : Measure ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  sSup (windowValues B P hB ν a n)

-- A05 PRIVATE head. All fractional exponents are real.
private theorem scale_identities (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 < x) :
    x * Real.sqrt (n : ℝ) =
        (x * (n : ℝ) ^ ((1 : ℝ) / 6)) * (n : ℝ) ^ ((1 : ℝ) / 3) ∧
    (n : ℝ) / (x * Real.sqrt (n : ℝ)) ^ 2 = 1 / x ^ 2 ∧
    (n : ℝ) / (x * Real.sqrt (n : ℝ)) ^ 3 =
        1 / (x * (n : ℝ) ^ ((1 : ℝ) / 6)) ^ 3 := by
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hs : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hN.le
  have hp : 0 < (n : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hN _
  have hp3 : ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 3 = Real.sqrt (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num
    exact (Real.sqrt_eq_rpow _).symm
  have hh2 : (x * Real.sqrt (n : ℝ)) ^ 2 = x ^ 2 * (n : ℝ) := by
    rw [mul_pow, hs]
  have hf3 : (x * (n : ℝ) ^ ((1 : ℝ) / 6)) ^ 3 =
      x ^ 3 * Real.sqrt (n : ℝ) := by rw [mul_pow, hp3]
  have hh3 : (x * Real.sqrt (n : ℝ)) ^ 3 =
      (n : ℝ) * (x * (n : ℝ) ^ ((1 : ℝ) / 6)) ^ 3 := by
    calc
      _ = x ^ 3 * (Real.sqrt (n : ℝ) ^ 2) * Real.sqrt (n : ℝ) := by ring
      _ = _ := by rw [hs, hf3]; ring
  refine ⟨?_, ?_, ?_⟩
  · calc
      x * Real.sqrt (n : ℝ) = x * (n : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow]
      _ = x * ((n : ℝ) ^ ((1 : ℝ) / 6) * (n : ℝ) ^ ((1 : ℝ) / 3)) := by
        rw [← Real.rpow_add hN]
        norm_num
      _ = _ := by ring
  · rw [hh2]
    field_simp [ne_of_gt hN, ne_of_gt hx] <;> ring
  · rw [hh3]
    field_simp [ne_of_gt hN, ne_of_gt hx, ne_of_gt hp] <;> ring


-- A06 PRIVATE head. No all-index positivity is added to a limit target.
private theorem small_boundary_scales
    (nSeq : ℕ → ℕ) (hn : Tendsto nSeq atTop atTop)
    (xSeq : ℕ → ℝ) (hxpos : ∀ᶠ j in atTop, 0 < xSeq j)
    (hx : Tendsto xSeq atTop (𝓝 (0 : ℝ)))
    (hslow : Tendsto (fun j => xSeq j * (nSeq j : ℝ) ^ ((1 : ℝ) / 6))
      atTop atTop) :
    Tendsto (fun j => xSeq j * Real.sqrt (nSeq j : ℝ)) atTop atTop ∧
    Tendsto (fun j => (nSeq j : ℝ) /
      (xSeq j * Real.sqrt (nSeq j : ℝ)) ^ 2) atTop atTop ∧
    Tendsto (fun j => (nSeq j : ℝ) /
      (xSeq j * Real.sqrt (nSeq j : ℝ)) ^ 3) atTop (𝓝 (0 : ℝ)) := by
  have hnt : ∀ᶠ j in atTop, 0 < nSeq j := by
    filter_upwards [hn.eventually_ge_atTop 1] with j hj
    omega
  have hid : ∀ᶠ j in atTop,
      xSeq j * Real.sqrt (nSeq j : ℝ) =
        (xSeq j * (nSeq j : ℝ) ^ ((1 : ℝ) / 6)) *
          (nSeq j : ℝ) ^ ((1 : ℝ) / 3) ∧
      (nSeq j : ℝ) / (xSeq j * Real.sqrt (nSeq j : ℝ)) ^ 2 = 1 / xSeq j ^ 2 ∧
      (nSeq j : ℝ) / (xSeq j * Real.sqrt (nSeq j : ℝ)) ^ 3 =
        1 / (xSeq j * (nSeq j : ℝ) ^ ((1 : ℝ) / 6)) ^ 3 := by
    filter_upwards [hnt, hxpos] with j hj hxj
    exact scale_identities (nSeq j) hj (xSeq j) hxj
  have hh : Tendsto (fun j => xSeq j * Real.sqrt (nSeq j : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hslow
    filter_upwards [hid, hn.eventually_ge_atTop 1, hxpos] with j hj hnj hxj
    rw [hj.1]
    have hN : (1 : ℝ) ≤ (nSeq j : ℝ) := by exact_mod_cast hnj
    have hp := Real.one_le_rpow hN (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3)
    have hf : 0 ≤ xSeq j * (nSeq j : ℝ) ^ ((1 : ℝ) / 6) :=
      mul_nonneg hxj.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    nlinarith
  have hxright : Tendsto xSeq atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx, hxpos⟩
  have hinv : Tendsto (fun j => (xSeq j)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp hxright
  have hlong0 : Tendsto (fun j => 1 / xSeq j ^ 2) atTop atTop := by
    simpa only [one_div, inv_pow, Function.comp_def] using
      (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp hinv
  have hshort0 : Tendsto
      (fun j => 1 / (xSeq j * (nSeq j : ℝ) ^ ((1 : ℝ) / 6)) ^ 3)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, Pi.inv_apply, inv_pow, Function.comp_def,
      (show (0 : ℝ) ^ 3 = 0 by norm_num)] using
      hslow.inv_tendsto_atTop.pow 3
  refine ⟨hh, hlong0.congr' ?_, hshort0.congr' ?_⟩
  · exact hid.mono fun j hj => hj.2.1.symm
  · exact hid.mono fun j hj => hj.2.2.symm


-- A07 PRIVATE head. Literal equality, not an asymptotic logarithmic comparison.
private theorem farMainTerm_eq_firstTerm (n : ℕ) (hn : 0 < n)
    (x : ℝ) (hx : 0 < x) :
    RandomDenominatorFarTail.farMainTerm n (x * Real.sqrt (n : ℝ)) =
      Shao.Probability.BrownianSup.firstTerm x := by
  rw [RandomDenominatorFarTail.farMainTerm,
    (scale_identities n hn x hx).2.1, Shao.Probability.BrownianSup.firstTerm]
  congr 2
  ring


-- A08 PRIVATE head. Derived from the qualified epsilon-delta actual first term.
private theorem actual_firstTerm_ratio_tendsto
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (xSeq : ℕ → ℝ) (hxpos : ∀ᶠ j in atTop, 0 < xSeq j)
    (hx : Tendsto xSeq atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j => Shao.Probability.BrownianSup.probability B P hB (xSeq j) /
      Shao.Probability.BrownianSup.firstTerm (xSeq j)) atTop (𝓝 (1 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := Shao.Probability.BrownianSup.actual_brownian_firstTerm
    B P hB ε hε
  filter_upwards [hxpos, hx.eventually (eventually_lt_nhds hδ)] with j hj hjδ
  simpa only [Real.dist_eq] using hbound (xSeq j) hj hjδ


-- A09 PUBLIC head. Calls E5 internally; E5 is never a hypothesis of this theorem.
theorem small_boundary_ratio_tendsto
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (nSeq : ℕ → ℕ) (hn : Tendsto nSeq atTop atTop)
    (xSeq : ℕ → ℝ) (hxpos : ∀ᶠ j in atTop, 0 < xSeq j)
    (hx : Tendsto xSeq atTop (𝓝 (0 : ℝ)))
    (hslow : Tendsto (fun j => xSeq j * (nSeq j : ℝ) ^ ((1 : ℝ) / 6))
      atTop atTop) :
    Tendsto (fun j => productProbability ν (nSeq j) (xSeq j) /
      Shao.Probability.BrownianSup.probability B P hB (xSeq j))
      atTop (𝓝 (1 : ℝ)) := by
  have hs := small_boundary_scales nSeq hn xSeq hxpos hx hslow
  have hmain := RandomDenominatorAsymptotic.randomDenominator_relative_main_tendsto
    ν h3 hmean hsecond (fun j => xSeq j * Real.sqrt (nSeq j : ℝ)) nSeq
      hs.1 hs.2.1 hs.2.2
  have hden := actual_firstTerm_ratio_tendsto B P hB xSeq hxpos hx
  have hmain' : Tendsto (fun j => productProbability ν (nSeq j) (xSeq j) /
      Shao.Probability.BrownianSup.firstTerm (xSeq j)) atTop (𝓝 (1 : ℝ)) := by
    apply hmain.congr'
    filter_upwards [hn.eventually_ge_atTop 1, hxpos] with j hnj hxj
    rw [farMainTerm_eq_firstTerm (nSeq j) (by omega) (xSeq j) hxj]
    rfl
  have hq : Tendsto (fun j =>
      (productProbability ν (nSeq j) (xSeq j) /
        Shao.Probability.BrownianSup.firstTerm (xSeq j)) /
      (Shao.Probability.BrownianSup.probability B P hB (xSeq j) /
        Shao.Probability.BrownianSup.firstTerm (xSeq j))) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Pi.div_def, div_self (by norm_num : (1 : ℝ) ≠ 0)] using
      hmain'.div hden (by norm_num : (1 : ℝ) ≠ 0)
  apply hq.congr'
  filter_upwards [hxpos] with j hxj
  have hm : 0 < Shao.Probability.BrownianSup.firstTerm (xSeq j) := by
    unfold Shao.Probability.BrownianSup.firstTerm
    exact mul_pos (div_pos (by norm_num) Real.pi_pos) (Real.exp_pos _)
  have hF := BrownianPositiveCDF.probability_pos B P hB (xSeq j) hxj
  field_simp [ne_of_gt hm, ne_of_gt hF] <;> ring


-- A10 PRIVATE head. Positivity is paid, not assumed at every index.
private theorem eventually_window_positive
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 (0 : ℝ)))
    (hslow : Tendsto (fun n => a n * (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop) :
    ∀ᶠ n in atTop, 0 < a n ∧ a n < 1 := by
  filter_upwards [hslow.eventually_gt_atTop 0,
    ha.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with n hn hn1
  refine ⟨?_, hn1⟩
  by_contra h
  have hp : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hnp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hp
  exact (not_lt_of_ge hnp) hn


-- A11 PRIVATE head. Genuine frequently-bad extraction and compact subsequence.
private theorem bad_window_subsequence
    (e : ℕ → ℝ → ℝ) (a : ℕ → ℝ) (ε : ℝ)
    (ha : ∀ᶠ n in atTop, 0 < a n)
    (hbad : ∃ᶠ n in atTop, ∃ x ∈ Ioo (a n) 1, ε ≤ e n x) :
    ∃ nSeq : ℕ → ℕ, ∃ xSeq : ℕ → ℝ, ∃ x : ℝ,
      StrictMono nSeq ∧ x ∈ Icc 0 1 ∧ Tendsto xSeq atTop (𝓝 x) ∧
      (∀ j, 0 < xSeq j ∧ xSeq j ∈ Ioo (a (nSeq j)) 1 ∧ ε ≤ e (nSeq j) (xSeq j)) := by
  classical
  have hb : ∃ᶠ n in atTop, (∃ x ∈ Ioo (a n) 1, ε ≤ e n x) ∧ 0 < a n :=
    hbad.and_eventually ha
  obtain ⟨m, hm, hmb⟩ := extraction_of_frequently_atTop hb
  choose y hy hybad using fun j => (hmb j).1
  have hy01 : ∀ j, y j ∈ Icc (0 : ℝ) 1 := fun j =>
    ⟨((hmb j).2.trans (hy j).1).le, (hy j).2.le⟩
  obtain ⟨x, hx, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hy01
  refine ⟨m ∘ φ, y ∘ φ, x, hm.comp hφ, hx, hlim, ?_⟩
  intro j
  exact ⟨(hmb (φ j)).2.trans (hy (φ j)).1, hy (φ j), hybad (φ j)⟩


-- A12 PUBLIC head. Original decreasing-window hypotheses are retained.
theorem product_window_eventually
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (a : ℕ → ℝ) (haAnti : Antitone a)
    (ha : Tendsto a atTop (𝓝 (0 : ℝ)))
    (hslow : Tendsto (fun n => a n * (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x ∈ Ioo (a n) 1, relativeError B P hB ν n x < ε := by
  classical
  intro ε hε
  by_contra hgood
  have hbad : ∃ᶠ n in atTop,
      ∃ x ∈ Ioo (a n) 1, ε ≤ relativeError B P hB ν n x := by
    simpa only [Filter.Frequently, not_exists, not_and, not_le] using hgood
  have hap := eventually_window_positive a ha hslow
  obtain ⟨nSeq, xSeq, x, hnmono, hx01, hxlim, hbadSeq⟩ :=
    bad_window_subsequence (relativeError B P hB ν) a ε
      (hap.mono fun _ h => h.1) hbad
  have hn : Tendsto nSeq atTop atTop := hnmono.tendsto_atTop
  have hr : Tendsto (fun j => productProbability ν (nSeq j) (xSeq j) /
      Shao.Probability.BrownianSup.probability B P hB (xSeq j))
      atTop (𝓝 (1 : ℝ)) := by
    by_cases hx0 : x = 0
    · have hxs : Tendsto (fun j => xSeq j * (nSeq j : ℝ) ^ ((1 : ℝ) / 6))
          atTop atTop := by
        apply tendsto_atTop_mono' atTop _ (hslow.comp hn)
        exact Eventually.of_forall fun j =>
          mul_le_mul_of_nonneg_right (hbadSeq j).2.1.1.le
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      exact small_boundary_ratio_tendsto B P hB ν h3 hmean hsecond nSeq hn
        xSeq (Eventually.of_forall fun j => (hbadSeq j).1) (hx0 ▸ hxlim) hxs
    · have hxpos : 0 < x := by
        by_contra h
        exact hx0 (le_antisymm (le_of_not_gt h) hx01.1)
      exact PositiveBoundaryStudentized.studentized_positive_boundary_ratio_tendsto
        B P hB ν h3 hmean hsecond nSeq hn xSeq x hxpos hxlim
  have he := (Metric.tendsto_nhds.mp hr) ε hε
  obtain ⟨j, hj⟩ := he.exists
  have hjlt : relativeError B P hB ν (nSeq j) (xSeq j) < ε := by
    simpa only [relativeError, Real.dist_eq] using hj
  exact (not_le_of_gt hjlt) (hbadSeq j).2.2


-- A13 PRIVATE head. Applies to the actual measurable product-law event.
private theorem productProbability_bounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) (x : ℝ) :
    0 ≤ productProbability ν n x ∧ productProbability ν n x ≤ 1 := by
  refine ⟨measureReal_nonneg, ?_⟩
  have h := measureReal_mono (μ := Measure.pi (fun _ : Fin n => ν))
    (Set.subset_univ (RandomDenominatorFarTail.randomDenominatorEvent n
      (x * Real.sqrt (n : ℝ))))
  simpa only [productProbability, Measure.real, measure_univ, ENNReal.toReal_one] using h


-- A14 PRIVATE head. A midpoint witnesses nonemptiness.
private theorem windowValues_nonempty
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (ν : Measure ℝ) (a : ℕ → ℝ) (n : ℕ)
    (ha : a n < 1) : (windowValues B P hB ν a n).Nonempty := by
  refine ⟨relativeError B P hB ν n ((a n + 1) / 2), ?_⟩
  exact ⟨(a n + 1) / 2, ⟨by linarith, by linarith⟩, rfl⟩


-- A15 PRIVATE head. The bound depends on n through the positive F(a n).
private theorem windowValues_bound
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (a : ℕ → ℝ) (n : ℕ) (ha : 0 < a n) :
    ∀ y ∈ windowValues B P hB ν a n,
      y ≤ 1 + 1 / Shao.Probability.BrownianSup.probability B P hB (a n) := by
  rintro y ⟨x, hx, rfl⟩
  have hc := BrownianPositiveCDF.probability_pos B P hB (a n) ha
  have hFx := BrownianPositiveCDF.probability_pos B P hB x (ha.trans hx.1)
  have hmono := BrownianPositiveCDF.probability_mono B P hB hx.1.le
  have hp := productProbability_bounds ν n x
  have hr : 0 ≤ productProbability ν n x /
      Shao.Probability.BrownianSup.probability B P hB x := div_nonneg hp.1 hFx.le
  have hrb : productProbability ν n x /
      Shao.Probability.BrownianSup.probability B P hB x ≤
      1 / Shao.Probability.BrownianSup.probability B P hB (a n) :=
    (div_le_div_of_nonneg_right hp.2 hFx.le).trans
      (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hc hmono)
  unfold relativeError
  calc
    _ ≤ |productProbability ν n x /
        Shao.Probability.BrownianSup.probability B P hB x| + |(1 : ℝ)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (productProbability ν n x /
          Shao.Probability.BrownianSup.probability B P hB x) (0 : ℝ) 1)
    _ = productProbability ν n x /
        Shao.Probability.BrownianSup.probability B P hB x + 1 := by
      rw [abs_of_nonneg hr, abs_one]
    _ ≤ _ := by linarith


-- A16 PUBLIC head. This pays a genuine finite supremum at each good index.
theorem windowError_spec
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (a : ℕ → ℝ) (n : ℕ) (ha0 : 0 < a n) (ha1 : a n < 1) :
    (windowValues B P hB ν a n).Nonempty ∧
      BddAbove (windowValues B P hB ν a n) ∧
      IsLUB (windowValues B P hB ν a n) (windowError B P hB ν a n) ∧
      0 ≤ windowError B P hB ν a n := by
  have hne := windowValues_nonempty B P hB ν a n ha1
  have hb : BddAbove (windowValues B P hB ν a n) :=
    ⟨_, windowValues_bound B P hB ν a n ha0⟩
  have hlub : IsLUB (windowValues B P hB ν a n) (windowError B P hB ν a n) :=
    isLUB_csSup hne hb
  obtain ⟨y, hy⟩ := hne
  have hy0 : 0 ≤ y := by
    obtain ⟨x, hx, rfl⟩ := hy
    exact abs_nonneg _
  exact ⟨⟨y, hy⟩, hb, hlub, hy0.trans (hlub.1 hy)⟩


-- A17 PUBLIC head. Exact requested real supremum for one fixed standardized law.
theorem product_window_tendsto
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (a : ℕ → ℝ) (haAnti : Antitone a)
    (ha : Tendsto a atTop (𝓝 (0 : ℝ)))
    (hslow : Tendsto (fun n => a n * (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop) :
    Tendsto (windowError B P hB ν a) atTop (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := product_window_eventually B P hB ν h3 hmean hsecond a haAnti ha hslow
    (ε / 2) (by linarith)
  filter_upwards [eventually_window_positive a ha hslow, he] with n hn hne
  have hs := windowError_spec B P hB ν a n hn.1 hn.2
  have hb : windowError B P hB ν a n ≤ ε / 2 := by
    apply csSup_le hs.1
    rintro y ⟨x, hx, rfl⟩
    exact (hne x hx).le
  have hlt : windowError B P hB ν a n < ε := by linarith
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hs.2.2.2] using hlt


end Shao.OQ4.OriginalWindowProduct
end
