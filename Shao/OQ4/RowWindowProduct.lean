import Shao.OQ4.RowRandomDenominatorAsymptotic
import Shao.OQ4.RowPositiveBoundaryStudentized
import Shao.OQ4.UnconditionalKernelAsymptotic
import Shao.Probability.BrownianFirstTerm
import Shao.OQ4.BrownianPositiveCDF
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.OQ4.RowWindowProduct

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal Topology

universe uB
variable {ΩB : Type uB} [MeasurableSpace ΩB]

-- NEW NON-THEOREM VALUE 1: complete exact value; actual ν/n/a finite arguments.
-- Closed interval includes BOTH endpoints. There is no limit/boundedness premise.
def actualWindowErrors
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (ν : Measure ℝ) (n : ℕ) (a : ℝ) : Set ℝ :=
  (fun x : ℝ =>
    |(Measure.pi (fun _ : Fin n => ν)).real
        {v : Shao.Path n |
          v ∈ Shao.closedStrip (x * Real.sqrt (Shao.energy v))} /
      Shao.Probability.BrownianSup.probability B P hB x - 1|) '' Icc a 1

-- PRIVATE 1. Exact real-rpow identities only after N>0 and x>0.
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

-- PRIVATE 2. No all-index sign or monotonicity assumption is introduced.
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

-- PRIVATE 3. Literal equality of actual weak events, with no Q division.
private theorem actual_event_eq_randomDenominatorEvent
    (n : ℕ) (hn : 0 < n) (x : ℝ) :
    {v : Shao.Path n |
      v ∈ Shao.closedStrip (x * Real.sqrt (Shao.energy v))} =
    RandomDenominatorFarTail.randomDenominatorEvent n (x * Real.sqrt (n : ℝ)) := by
  have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have hcancel : x * Real.sqrt (n : ℝ) / Real.sqrt (n : ℝ) = x := by
    field_simp [hs]
  simp only [RandomDenominatorFarTail.randomDenominatorEvent, hcancel]

-- PRIVATE 4. Qualified changing-row K, with a body-local positive-prefix patch.
private theorem varying_row_closedStrip_relative_main_tendsto
    (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun z : ℝ => |z| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ z : ℝ, z ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ z : ℝ, z ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ z : ℝ, |z| ^ 3 ∂(νSeq j)) ≤ M)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j =>
      (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (@Shao.closedStrip (n j) (h j)) /
        RandomDenominatorFarTail.farMainTerm (n j) (h j))
      atTop (𝓝 (1 : ℝ)) := by
  let ht : ℕ → ℝ := fun j => if 0 < h j then h j else 1
  have hpos : ∀ j, 0 < ht j := by
    intro j
    dsimp only [ht]
    split_ifs with hj
    · exact hj
    · norm_num
  have heq : ht =ᶠ[atTop] h := by
    filter_upwards [hinfty.eventually_gt_atTop 0] with j hj
    dsimp only [ht]
    rw [if_pos hj]
  have hi : Tendsto ht atTop atTop := hinfty.congr' heq.symm
  have hl : Tendsto (fun j => (n j : ℝ) / ht j ^ 2) atTop atTop :=
    hlong.congr' (heq.mono fun j hj => congrArg (fun t : ℝ => (n j : ℝ) / t ^ 2) hj.symm)
  have hs : Tendsto (fun j => (n j : ℝ) / ht j ^ 3) atTop (𝓝 (0 : ℝ)) :=
    hshort.congr' (heq.mono fun j hj => congrArg (fun t : ℝ => (n j : ℝ) / t ^ 3) hj.symm)
  have hK := UnconditionalKernelAsymptotic.varying_row_closedStrip_relative_asymptotic
    νSeq hprob h3 hmean hsecond M hM ht n hpos hi hl hs
  have hK' : Tendsto (fun j =>
      (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (@Shao.closedStrip (n j) (ht j)) /
        RandomDenominatorFarTail.farMainTerm (n j) (ht j))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [RandomDenominatorFarTail.farMainTerm,
      RademacherScalarBounds.lambda, mul_div_assoc] using hK
  apply hK'.congr'
  filter_upwards [heq] with j hj
  rw [hj]

-- PRIVATE 5. The actual supplied Brownian CDF and actual firstTerm producer.
private theorem actual_firstTerm_ratio_tendsto
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (xSeq : ℕ → ℝ) (hxpos : ∀ᶠ j in atTop, 0 < xSeq j)
    (hx : Tendsto xSeq atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j =>
      Shao.Probability.BrownianSup.probability B P hB (xSeq j) /
        Shao.Probability.BrownianSup.firstTerm (xSeq j))
      atTop (𝓝 (1 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := Shao.Probability.BrownianSup.actual_brownian_firstTerm
    B P hB ε hε
  filter_upwards [hxpos, hx.eventually (eventually_lt_nhds hδ)] with j hj hjδ
  simpa only [Real.dist_eq] using hbound (xSeq j) hj hjδ

-- PUBLIC 1. Full actual changing-row small-boundary relative probability.
theorem varying_row_studentized_small_boundary_ratio_tendsto
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun z : ℝ => |z| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ z : ℝ, z ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ z : ℝ, z ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ z : ℝ, |z| ^ 3 ∂(νSeq j)) ≤ M)
    (nSeq : ℕ → ℕ) (hn : Tendsto nSeq atTop atTop)
    (xSeq : ℕ → ℝ) (hxpos : ∀ᶠ j in atTop, 0 < xSeq j)
    (hx : Tendsto xSeq atTop (𝓝 (0 : ℝ)))
    (hslow : Tendsto (fun j => xSeq j * (nSeq j : ℝ) ^ ((1 : ℝ) / 6))
      atTop atTop) :
    Tendsto (fun j =>
      (Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).real
        {v : Shao.Path (nSeq j) |
          v ∈ Shao.closedStrip (xSeq j * Real.sqrt (Shao.energy v))} /
        Shao.Probability.BrownianSup.probability B P hB (xSeq j))
      atTop (𝓝 (1 : ℝ)) := by
  let H : ℕ → ℝ := fun j => xSeq j * Real.sqrt (nSeq j : ℝ)
  let R : ℕ → ℝ := fun j => (Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).real
    (RandomDenominatorFarTail.randomDenominatorEvent (nSeq j) (H j))
  let G : ℕ → ℝ := fun j => (Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).real
    (@Shao.closedStrip (nSeq j) (H j))
  let m : ℕ → ℝ := fun j => RandomDenominatorFarTail.farMainTerm (nSeq j) (H j)
  let p : ℕ → ℝ := fun j => (Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).real
    {v : Shao.Path (nSeq j) |
      v ∈ Shao.closedStrip (xSeq j * Real.sqrt (Shao.energy v))}
  let g : ℕ → ℝ := fun j => Shao.Probability.BrownianSup.firstTerm (xSeq j)
  let F : ℕ → ℝ := fun j => Shao.Probability.BrownianSup.probability B P hB (xSeq j)
  have hsc := small_boundary_scales nSeq hn xSeq hxpos hx hslow
  have hD : Tendsto (fun j => R j / G j) atTop (𝓝 (1 : ℝ)) :=
    RowRandomDenominatorAsymptotic.varying_row_randomDenominator_relative_closedStrip_tendsto
      νSeq hprob h3 hmean hsecond M hM H nSeq hsc.1 hsc.2.1 hsc.2.2
  have hK : Tendsto (fun j => G j / m j) atTop (𝓝 (1 : ℝ)) :=
    varying_row_closedStrip_relative_main_tendsto νSeq hprob h3 hmean hsecond M hM
      H nSeq hsc.1 hsc.2.1 hsc.2.2
  have hGpos : ∀ᶠ j in atTop, 0 < G j := by
    filter_upwards [hK.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))] with j hj
    have hm : 0 < m j := RandomDenominatorFarTail.farMainTerm_pos (nSeq j) (H j)
    exact (div_pos_iff_of_pos_right hm).mp hj
  have hprod : Tendsto (fun j => R j / G j * (G j / m j)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_one] using hD.mul hK
  have hmain : Tendsto (fun j => R j / m j) atTop (𝓝 (1 : ℝ)) := by
    apply hprod.congr'
    filter_upwards [hGpos] with j hj
    have hm : m j ≠ 0 := (RandomDenominatorFarTail.farMainTerm_pos (nSeq j) (H j)).ne'
    field_simp [hj.ne', hm] <;> ring
  have hmain' : Tendsto (fun j => p j / g j) atTop (𝓝 (1 : ℝ)) := by
    apply hmain.congr'
    filter_upwards [hn.eventually_ge_atTop 1, hxpos] with j hnj hxj
    have hn0 : 0 < nSeq j := by omega
    have hm : RandomDenominatorFarTail.farMainTerm (nSeq j)
        (xSeq j * Real.sqrt (nSeq j : ℝ)) =
        Shao.Probability.BrownianSup.firstTerm (xSeq j) := by
      rw [RandomDenominatorFarTail.farMainTerm,
        (scale_identities (nSeq j) hn0 (xSeq j) hxj).2.1,
        Shao.Probability.BrownianSup.firstTerm]
      congr 2
      ring
    dsimp only [R, m, p, g, H]
    rw [← actual_event_eq_randomDenominatorEvent (nSeq j) hn0 (xSeq j), hm]
  have hden : Tendsto (fun j => F j / g j) atTop (𝓝 (1 : ℝ)) :=
    actual_firstTerm_ratio_tendsto B P hB xSeq hxpos hx
  have hq : Tendsto (fun j => (p j / g j) / (F j / g j))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [Pi.div_def, div_self (by norm_num : (1 : ℝ) ≠ 0)] using
      hmain'.div hden (by norm_num : (1 : ℝ) ≠ 0)
  apply hq.congr'
  filter_upwards [hxpos] with j hxj
  have hm : 0 < g j := by
    dsimp only [g, Shao.Probability.BrownianSup.firstTerm]
    exact mul_pos (div_pos (by norm_num) Real.pi_pos) (Real.exp_pos _)
  have hF : 0 < F j := BrownianPositiveCDF.probability_pos B P hB (xSeq j) hxj
  change (p j / g j) / (F j / g j) = p j / F j
  field_simp [ne_of_gt hm, ne_of_gt hF] <;> ring

-- PRIVATE 6. A cofinal bad-index sequence, followed by compact-radius extraction.
private theorem bad_closed_window_subsequence
    (e : ℕ → ℝ → ℝ) (aSeq : ℕ → ℝ) (ε : ℝ)
    (hapos : ∀ᶠ j in atTop, 0 < aSeq j)
    (hbad : ∃ᶠ j in atTop, ∃ x ∈ Icc (aSeq j) 1, ε ≤ e j x) :
    ∃ κ : ℕ → ℕ, ∃ xSeq : ℕ → ℝ, ∃ c : ℝ,
      StrictMono κ ∧ c ∈ Icc 0 1 ∧ Tendsto xSeq atTop (𝓝 c) ∧
      (∀ k, 0 < xSeq k ∧ xSeq k ∈ Icc (aSeq (κ k)) 1 ∧
        ε ≤ e (κ k) (xSeq k)) := by
  classical
  have hb : ∃ᶠ j in atTop, (∃ x ∈ Icc (aSeq j) 1, ε ≤ e j x) ∧ 0 < aSeq j :=
    hbad.and_eventually hapos
  obtain ⟨m, hm, hmb⟩ := extraction_of_frequently_atTop hb
  choose y hy hybad using fun k => (hmb k).1
  have hy01 : ∀ k, y k ∈ Icc (0 : ℝ) 1 := fun k =>
    ⟨((hmb k).2.trans_le (hy k).1).le, (hy k).2⟩
  obtain ⟨c, hc, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hy01
  refine ⟨m ∘ φ, y ∘ φ, c, hm.comp hφ, hc, hlim, ?_⟩
  intro k
  exact ⟨(hmb (φ k)).2.trans_le (hy (φ k)).1, hy (φ k), hybad (φ k)⟩

-- PUBLIC 2. New CLOSED window: includes x=aSeq j and x=1, no Antitone.
theorem varying_row_closed_window_eventually
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun z : ℝ => |z| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ z : ℝ, z ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ z : ℝ, z ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ z : ℝ, |z| ^ 3 ∂(νSeq j)) ≤ M)
    (nSeq : ℕ → ℕ) (hn : Tendsto nSeq atTop atTop)
    (aSeq : ℕ → ℝ) (hapos : ∀ᶠ j in atTop, 0 < aSeq j)
    (ha : Tendsto aSeq atTop (𝓝 (0 : ℝ)))
    (hslow : Tendsto (fun j => aSeq j * (nSeq j : ℝ) ^ ((1 : ℝ) / 6))
      atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x ∈ Icc (aSeq j) 1,
      |(Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).real
          {v : Shao.Path (nSeq j) |
            v ∈ Shao.closedStrip (x * Real.sqrt (Shao.energy v))} /
        Shao.Probability.BrownianSup.probability B P hB x - 1| < ε := by
  classical
  intro ε hε
  let e : ℕ → ℝ → ℝ := fun j x =>
    |(Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).real
        {v : Shao.Path (nSeq j) |
          v ∈ Shao.closedStrip (x * Real.sqrt (Shao.energy v))} /
      Shao.Probability.BrownianSup.probability B P hB x - 1|
  by_contra hgood
  have hbad : ∃ᶠ j in atTop, ∃ x ∈ Icc (aSeq j) 1, ε ≤ e j x := by
    simpa only [e, Filter.Frequently, not_exists, not_and, not_le] using hgood
  obtain ⟨κ, xSeq, c, hκmono, hc01, hxlim, hbadSeq⟩ :=
    bad_closed_window_subsequence e aSeq ε hapos hbad
  have hκ : Tendsto κ atTop atTop := hκmono.tendsto_atTop
  have hn' : Tendsto (fun k => nSeq (κ k)) atTop atTop := hn.comp hκ
  have hr : Tendsto (fun k =>
      (Measure.pi (fun _ : Fin (nSeq (κ k)) => νSeq (κ k))).real
        {v : Shao.Path (nSeq (κ k)) |
          v ∈ Shao.closedStrip (xSeq k * Real.sqrt (Shao.energy v))} /
      Shao.Probability.BrownianSup.probability B P hB (xSeq k))
      atTop (𝓝 (1 : ℝ)) := by
    by_cases hc0 : c = 0
    · have hxs : Tendsto
          (fun k => xSeq k * (nSeq (κ k) : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop := by
        apply tendsto_atTop_mono' atTop _ (hslow.comp hκ)
        exact Eventually.of_forall fun k =>
          mul_le_mul_of_nonneg_right (hbadSeq k).2.1.1
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      exact varying_row_studentized_small_boundary_ratio_tendsto B P hB
        (fun k => νSeq (κ k)) (fun k => hprob (κ k)) (fun k => h3 (κ k))
        (fun k => hmean (κ k)) (fun k => hsecond (κ k)) M (fun k => hM (κ k))
        (fun k => nSeq (κ k)) hn' xSeq
        (Eventually.of_forall fun k => (hbadSeq k).1) (hc0 ▸ hxlim) hxs
    · have hcpos : 0 < c := by
        by_contra h
        exact hc0 (le_antisymm (le_of_not_gt h) hc01.1)
      exact RowPositiveBoundaryStudentized.varying_row_studentized_positive_boundary_ratio_tendsto
        B P hB (fun k => νSeq (κ k)) (fun k => hprob (κ k)) (fun k => h3 (κ k))
        (fun k => hmean (κ k)) (fun k => hsecond (κ k)) M (fun k => hM (κ k))
        (fun k => nSeq (κ k)) hn' xSeq c hcpos hxlim
  have he := (Metric.tendsto_nhds.mp hr) ε hε
  obtain ⟨k, hk⟩ := he.exists
  have hklt : e (κ k) (xSeq k) < ε := by
    simpa only [e, Real.dist_eq] using hk
  exact (not_le_of_gt hklt) (hbadSeq k).2.2

-- PRIVATE 7. A real, nonempty, bounded actual errors image at a finite good row.
-- n=0 is permitted; ν probability and 0<a≤1 pay every order prerequisite.
private theorem actualWindowErrors_spec
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    (actualWindowErrors B P hB ν n a).Nonempty ∧
      BddAbove (actualWindowErrors B P hB ν n a) ∧
      IsLUB (actualWindowErrors B P hB ν n a)
        (sSup (actualWindowErrors B P hB ν n a)) ∧
      0 ≤ sSup (actualWindowErrors B P hB ν n a) := by
  let p : ℝ → ℝ := fun x => (Measure.pi (fun _ : Fin n => ν)).real
    {v : Shao.Path n | v ∈ Shao.closedStrip (x * Real.sqrt (Shao.energy v))}
  let F : ℝ → ℝ := Shao.Probability.BrownianSup.probability B P hB
  have hne : (actualWindowErrors B P hB ν n a).Nonempty :=
    ⟨|p a / F a - 1|, a, ⟨le_rfl, ha1⟩, rfl⟩
  have hb : BddAbove (actualWindowErrors B P hB ν n a) := by
    refine ⟨1 + 1 / F a, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    change |p x / F x - 1| ≤ 1 + 1 / F a
    have hc : 0 < F a := BrownianPositiveCDF.probability_pos B P hB a ha0
    have hFx : 0 < F x := BrownianPositiveCDF.probability_pos B P hB x (ha0.trans_le hx.1)
    have hmono : F a ≤ F x := BrownianPositiveCDF.probability_mono B P hB hx.1
    have hp0 : 0 ≤ p x := measureReal_nonneg
    have hp1 : p x ≤ 1 := by
      have h := measureReal_mono (μ := Measure.pi (fun _ : Fin n => ν))
        (Set.subset_univ {v : Shao.Path n |
          v ∈ Shao.closedStrip (x * Real.sqrt (Shao.energy v))})
      simpa only [p, Measure.real, measure_univ, ENNReal.toReal_one] using h
    have hr : 0 ≤ p x / F x := div_nonneg hp0 hFx.le
    have hrb : p x / F x ≤ 1 / F a :=
      (div_le_div_of_nonneg_right hp1 hFx.le).trans
        (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hc hmono)
    calc
      _ ≤ |p x / F x| + |(1 : ℝ)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le (p x / F x) (0 : ℝ) 1)
      _ = p x / F x + 1 := by rw [abs_of_nonneg hr, abs_one]
      _ ≤ _ := by linarith
  have hlub : IsLUB (actualWindowErrors B P hB ν n a)
      (sSup (actualWindowErrors B P hB ν n a)) := isLUB_csSup hne hb
  obtain ⟨y, hy⟩ := hne
  have hy0 : 0 ≤ y := by
    obtain ⟨x, hx, rfl⟩ := hy
    exact abs_nonneg _
  exact ⟨⟨y, hy⟩, hb, hlub, hy0.trans (hlub.1 hy)⟩

-- PUBLIC 3. Exact real sSup of the new actual CLOSED-window absolute errors.
theorem varying_row_closed_window_sSup_tendsto
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun z : ℝ => |z| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ z : ℝ, z ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ z : ℝ, z ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ z : ℝ, |z| ^ 3 ∂(νSeq j)) ≤ M)
    (nSeq : ℕ → ℕ) (hn : Tendsto nSeq atTop atTop)
    (aSeq : ℕ → ℝ) (hapos : ∀ᶠ j in atTop, 0 < aSeq j)
    (ha : Tendsto aSeq atTop (𝓝 (0 : ℝ)))
    (hslow : Tendsto (fun j => aSeq j * (nSeq j : ℝ) ^ ((1 : ℝ) / 6))
      atTop atTop) :
    Tendsto (fun j => sSup
      (actualWindowErrors B P hB (νSeq j) (nSeq j) (aSeq j)))
      atTop (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := varying_row_closed_window_eventually B P hB νSeq hprob h3 hmean hsecond
    M hM nSeq hn aSeq hapos ha hslow (ε / 2) (by linarith)
  have hgeom : ∀ᶠ j in atTop, 0 < aSeq j ∧ aSeq j ≤ 1 := by
    filter_upwards [hapos,
      ha.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with j hj hj1
    exact ⟨hj, hj1.le⟩
  filter_upwards [hgeom, he] with j hj hje
  letI := hprob j
  have hs := actualWindowErrors_spec B P hB (νSeq j) (nSeq j) (aSeq j) hj.1 hj.2
  have hb : sSup (actualWindowErrors B P hB (νSeq j) (nSeq j) (aSeq j)) ≤ ε / 2 := by
    apply csSup_le hs.1
    rintro y ⟨x, hx, rfl⟩
    exact (hje x hx).le
  have hlt : sSup (actualWindowErrors B P hB (νSeq j) (nSeq j) (aSeq j)) < ε := by linarith
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hs.2.2.2] using hlt

end Shao.OQ4.RowWindowProduct
end
