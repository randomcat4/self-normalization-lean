/-
Actual varying-row joint finite-dimensional limits and fractional endpoints.
Declaration heads and literal mathematical definition values were frozen by
the OQ4 lead at SHA0241f9136a91b297472f00863a1f56ca060d0c19da0feef74895c2379eb035fd.

Mathematical target SHA256:
820ac3b21dadc27a6a7f8e135a5f012c37c919b358e770639faf933334110e96
See math-proof.md and api-notes.md for complete mathematical proofs and actual
pinned APIs. Existing source bytes and old receipts are not modified.

Proposed implementation module: Shao.OQ4.RowPolygonalFDD
All public vectors are ordinary Fin m → ℝ with product Borel/topology and sup
norm. EuclideanSpace is only a private characteristic-function bridge.
-/

import Shao.OQ4.RowBlockGaussianLimit
import Shao.OQ4.PolygonalThirdMomentB3
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Positivity

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false

namespace Shao.OQ4.RowPolygonalFDD

noncomputable section

/- PUBLIC DEFINITIONS: literal values, with m inferred only where shown. -/

def durationPrefix {m : ℕ} (D : Fin m → ℝ≥0) (q : ℕ) : ℝ≥0 :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin m => k.val < q), D k

def observationTime {m : ℕ} (D : Fin m → ℝ≥0) (k : Fin m) : ℝ≥0 :=
  durationPrefix D (k.val + 1)

def totalDuration {m : ℕ} (D : Fin m → ℝ≥0) : ℝ≥0 :=
  ∑ k : Fin m, D k

def floorGridIndex {m : ℕ} (D : Fin m → ℝ≥0) (h : ℝ) (q : ℕ) : ℕ :=
  Nat.floor ((durationPrefix D q : ℝ) * h ^ 2)

def floorBlockLength {m : ℕ} (D : Fin m → ℝ≥0) (h : ℝ) (k : Fin m) : ℕ :=
  floorGridIndex D h (k.val + 1) - floorGridIndex D h k.val

def floorBlockVector {m : ℕ} (N : ℕ) (h : ℝ) (D : Fin m → ℝ≥0)
    (a : Shao.Path N) : Fin m → ℝ :=
  fun k => (Shao.prefixSum a (floorGridIndex D h (k.val + 1)) -
    Shao.prefixSum a (floorGridIndex D h k.val)) / h

def cumulativeMap (m : ℕ) (v : Fin m → ℝ) : Fin m → ℝ :=
  fun k => Shao.prefixSum v (k.val + 1)

def floorPrefixVector {m : ℕ} (N : ℕ) (h : ℝ) (D : Fin m → ℝ≥0)
    (a : Shao.Path N) : Fin m → ℝ :=
  fun k => Shao.prefixSum a (floorGridIndex D h (k.val + 1)) / h

def polygonalVector {m : ℕ} (N : ℕ) (h : ℝ) (D : Fin m → ℝ≥0)
    (a : Shao.Path N) : Fin m → ℝ :=
  fun k => Shao.OQ4.PolygonalThirdMoment.polygonalPath N h a
    (observationTime D k : ℝ)

def gaussianIncrementLaw {m : ℕ} (D : Fin m → ℝ≥0) : Measure (Fin m → ℝ) :=
  Measure.pi (fun k : Fin m => ProbabilityTheory.gaussianReal 0 (D k))

def cumulativeGaussianLaw {m : ℕ} (D : Fin m → ℝ≥0) : Measure (Fin m → ℝ) :=
  (gaussianIncrementLaw D).map (cumulativeMap m)

instance gaussianIncrementLaw_isProbabilityMeasure {m : ℕ} (D : Fin m → ℝ≥0) :
  IsProbabilityMeasure (gaussianIncrementLaw D) := by
  unfold gaussianIncrementLaw
  infer_instance

instance cumulativeGaussianLaw_isProbabilityMeasure {m : ℕ} (D : Fin m → ℝ≥0) :
  IsProbabilityMeasure (cumulativeGaussianLaw D) := by
  unfold cumulativeGaussianLaw
  infer_instance

/- PRIVATE FINITE ALGEBRA / CONTINUITY: no new mathematical premises. -/

private theorem durationPrefix_zero {m : ℕ} (D : Fin m → ℝ≥0) :
    durationPrefix D 0 = 0 := by
  simp [durationPrefix]

private theorem durationPrefix_length {m : ℕ} (D : Fin m → ℝ≥0) :
    durationPrefix D m = totalDuration D := by
  unfold durationPrefix totalDuration
  rw [Finset.filter_eq_self.mpr (fun k _ => k.is_lt)]

private theorem durationPrefix_monotone {m : ℕ} (D : Fin m → ℝ≥0) :
    Monotone (durationPrefix D) := by
  intro q r hqr
  unfold durationPrefix
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by intro k hk; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *; omega)
    (fun _ _ _ => bot_le)

private theorem durationPrefix_succ {m : ℕ} (D : Fin m → ℝ≥0) (k : Fin m) :
    durationPrefix D (k.val + 1) = durationPrefix D k.val + D k := by
  classical
  have heq : Finset.univ.filter (fun i : Fin m => i.val < k.val + 1) =
      insert k (Finset.univ.filter (fun i : Fin m => i.val < k.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hi
      by_cases hik : i.val = k.val
      · exact Or.inl (Fin.ext hik)
      · exact Or.inr (by omega)
    · rintro (rfl | hi) <;> omega
  unfold durationPrefix
  rw [heq, Finset.sum_insert (by simp), add_comm]

private theorem observationTime_le_total {m : ℕ} (D : Fin m → ℝ≥0) (k : Fin m) :
    observationTime D k ≤ totalDuration D := by
  rw [observationTime, ← durationPrefix_length D]
  exact durationPrefix_monotone D (by omega)

private theorem floorGridIndex_monotone {m : ℕ} (D : Fin m → ℝ≥0) (h : ℝ) :
    Monotone (floorGridIndex D h) := by
  intro q r hqr
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast durationPrefix_monotone D hqr)
    (sq_nonneg h)

private theorem floorGridIndex_le_length {m : ℕ} (N : ℕ) (h : ℝ)
    (D : Fin m → ℝ≥0) (hN : (totalDuration D : ℝ) * h ^ 2 ≤ (N : ℝ))
    (q : ℕ) (hq : q ≤ m) :
    floorGridIndex D h q ≤ N := by
  have hqT : (durationPrefix D q : ℝ) ≤ (totalDuration D : ℝ) := by
    exact_mod_cast (durationPrefix_monotone D hq).trans_eq (durationPrefix_length D)
  apply Nat.floor_le_of_le
  exact (mul_le_mul_of_nonneg_right hqT (sq_nonneg h)).trans hN

private theorem cumulativeMap_continuous (m : ℕ) : Continuous (cumulativeMap m) := by
  unfold cumulativeMap Shao.prefixSum
  fun_prop

private theorem floorBlockVector_continuous {m : ℕ} (N : ℕ) (h : ℝ)
    (D : Fin m → ℝ≥0) : Continuous (floorBlockVector N h D) := by
  unfold floorBlockVector Shao.prefixSum
  fun_prop

private theorem floorPrefixVector_continuous {m : ℕ} (N : ℕ) (h : ℝ)
    (D : Fin m → ℝ≥0) : Continuous (floorPrefixVector N h D) := by
  unfold floorPrefixVector Shao.prefixSum
  fun_prop

private theorem polygonalVector_continuous {m : ℕ} (N : ℕ) (h : ℝ)
    (D : Fin m → ℝ≥0) : Continuous (polygonalVector N h D) := by
  unfold polygonalVector Shao.OQ4.PolygonalThirdMoment.polygonalPath
  fun_prop

private theorem cumulative_floorBlockVector {m : ℕ} (N : ℕ) (h : ℝ)
    (D : Fin m → ℝ≥0) (a : Shao.Path N) :
    cumulativeMap m (floorBlockVector N h D a) = floorPrefixVector N h D a := by
  classical
  have htel (q : ℕ) (hq : q ≤ m) :
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < q),
        (Shao.prefixSum a (floorGridIndex D h (i.val + 1)) -
          Shao.prefixSum a (floorGridIndex D h i.val))) =
        Shao.prefixSum a (floorGridIndex D h q) := by
    induction q with
    | zero => simp [floorGridIndex, durationPrefix_zero]
    | succ q ih =>
      let k : Fin m := ⟨q, by omega⟩
      have heq : Finset.univ.filter (fun i : Fin m => i.val < q + 1) =
          insert k (Finset.univ.filter (fun i : Fin m => i.val < q)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hi
          by_cases hik : i.val = q
          · exact Or.inl (Fin.ext hik)
          · exact Or.inr (by omega)
        · rintro (rfl | hi)
          · simp [k]
          · exact Nat.lt_succ_of_lt hi
      rw [heq, Finset.sum_insert (by simp [k]), ih (by omega)]
      simp only [k]
      ring
  funext k
  simpa [cumulativeMap, floorBlockVector, floorPrefixVector, Shao.prefixSum,
    ← Finset.sum_div] using congrArg (fun x : ℝ => x / h) (htel (k.val + 1) (by omega))

/- PRIVATE DISJOINT CUT BLOCKS: the b_0 cut need not be zero. -/

private def cutBlockVector (m N : ℕ) (b : Fin (m + 1) → ℕ) (h : ℝ)
    (a : Shao.Path N) : Fin m → ℝ :=
  fun k => (Shao.prefixSum a (b k.succ) - Shao.prefixSum a (b k.castSucc)) / h

private def cutCoeff (m N : ℕ) (b : Fin (m + 1) → ℕ) (h : ℝ)
    (t : EuclideanSpace ℝ (Fin m)) (i : Fin N) : ℝ :=
  ∑ k : Fin m, if b k.castSucc ≤ i.val ∧ i.val < b k.succ then t k / h else 0

private theorem prefix_difference_eq_window (N l r : ℕ) (hlr : l ≤ r)
    (a : Shao.Path N) :
    Shao.prefixSum a r - Shao.prefixSum a l =
      ∑ i : Fin N, if l ≤ i.val ∧ i.val < r then a i else 0 := by
  classical
  simp only [Shao.prefixSum, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hil : i.val < l
  · have hir : i.val < r := hil.trans_le hlr
    simp [hil, hir, show ¬l ≤ i.val by omega]
  · by_cases hir : i.val < r
    · simp [hil, hir, show l ≤ i.val by omega]
    · simp [hil, hir]

private theorem coordinate_window_card (N l r : ℕ) (hlr : l ≤ r) (hrN : r ≤ N) :
    (Finset.univ.filter (fun i : Fin N => l ≤ i.val ∧ i.val < r)).card = r - l := by
  classical
  have hc : (Finset.univ.filter (fun i : Fin N => l ≤ i.val ∧ i.val < r)).card =
      (Finset.range (r - l)).card := by
    refine Finset.card_bij (fun i _ => i.val - l) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_range]
      omega
    · intro i hi j hj heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      apply Fin.ext
      omega
    · intro q hq
      simp only [Finset.mem_range] at hq
      let i : Fin N := ⟨l + q, by omega⟩
      refine ⟨i, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, i]
        omega
      · simp [i]
  simpa using hc

private theorem cutBlockVector_continuous (m N : ℕ) (b : Fin (m + 1) → ℕ)
    (h : ℝ) : Continuous (cutBlockVector m N b h) := by
  unfold cutBlockVector Shao.prefixSum
  fun_prop

private theorem cutBlockVector_inner (m N : ℕ) (b : Fin (m + 1) → ℕ)
    (hb : Monotone b) (h : ℝ) (a : Shao.Path N)
    (t : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (WithLp.toLp 2 (cutBlockVector m N b h a)) t =
      ∑ i : Fin N, cutCoeff m N b h t i * a i := by
  classical
  have hd (k : Fin m) :
      Shao.prefixSum a (b k.succ) - Shao.prefixSum a (b k.castSucc) =
        ∑ i : Fin N, if b k.castSucc ≤ i.val ∧ i.val < b k.succ then a i else 0 :=
    prefix_difference_eq_window N _ _ (hb (by change k.val ≤ k.val + 1; omega)) a
  calc
    _ = ∑ k : Fin m, ∑ i : Fin N,
        (if b k.castSucc ≤ i.val ∧ i.val < b k.succ then t k / h else 0) * a i := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, cutBlockVector]
      apply Finset.sum_congr rfl
      intro k _
      rw [hd, Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hw : b k.castSucc ≤ i.val ∧ i.val < b k.succ
      · simp only [if_pos hw]
        ring
      · simp only [if_neg hw, zero_div, mul_zero, zero_mul]
    _ = ∑ i : Fin N, ∑ k : Fin m,
        (if b k.castSucc ≤ i.val ∧ i.val < b k.succ then t k / h else 0) * a i :=
      Finset.sum_comm
    _ = _ := by simp only [cutCoeff, Finset.sum_mul]

private theorem prod_charFun_cutCoeff (m N : ℕ) (b : Fin (m + 1) → ℕ)
    (hb : Monotone b) (hN : b (Fin.last m) ≤ N)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (h : ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    (∏ i : Fin N, charFun ν (cutCoeff m N b h t i)) =
      ∏ k : Fin m, (charFun ν (t k / h)) ^ (b k.succ - b k.castSucc) := by
  classical
  have huniq (i : Fin N) (k l : Fin m)
      (hk : b k.castSucc ≤ i.val ∧ i.val < b k.succ)
      (hl : b l.castSucc ≤ i.val ∧ i.val < b l.succ) : k = l := by
    apply Fin.ext
    rcases lt_trichotomy k.val l.val with hkl | hkl | hkl
    · have horder := hb (show k.succ ≤ l.castSucc by change k.val + 1 ≤ l.val; omega)
      omega
    · exact hkl
    · have horder := hb (show l.succ ≤ k.castSucc by change l.val + 1 ≤ k.val; omega)
      omega
  have hpoint (i : Fin N) : charFun ν (cutCoeff m N b h t i) =
      ∏ k : Fin m, if b k.castSucc ≤ i.val ∧ i.val < b k.succ
        then charFun ν (t k / h) else 1 := by
    by_cases hex : ∃ k : Fin m, b k.castSucc ≤ i.val ∧ i.val < b k.succ
    · obtain ⟨k, hk⟩ := hex
      have hothers (l : Fin m) (hlk : l ≠ k) :
          ¬ (b l.castSucc ≤ i.val ∧ i.val < b l.succ) :=
        fun hl => hlk (huniq i l k hl hk)
      have hsum : cutCoeff m N b h t i = t k / h := by
        unfold cutCoeff
        rw [Finset.sum_eq_single k]
        · simp [hk]
        · intro l _ hlk
          simp [hothers l hlk]
        · simp
      rw [hsum, Finset.prod_eq_single k]
      · simp [hk]
      · intro l _ hlk
        simp [hothers l hlk]
      · simp
    · have hnone (k : Fin m) : ¬ (b k.castSucc ≤ i.val ∧ i.val < b k.succ) :=
        fun hk => hex ⟨k, hk⟩
      simp [cutCoeff, hnone]
  simp_rw [hpoint]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro k _
  rw [← Finset.prod_filter, Finset.prod_const,
    coordinate_window_card N (b k.castSucc) (b k.succ)
      (hb (by change k.val ≤ k.val + 1; omega))
      ((hb (Fin.le_last _)).trans hN)]

private theorem cutBlockVector_charFun (m N : ℕ) (b : Fin (m + 1) → ℕ)
    (hb : Monotone b) (hN : b (Fin.last m) ≤ N)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (h : ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    charFun ((Measure.pi (fun _ : Fin N => ν)).map
      (fun a => WithLp.toLp 2 (cutBlockVector m N b h a))) t =
      ∏ k : Fin m, (charFun ν (t k / h)) ^ (b k.succ - b k.castSucc) := by
  classical
  have hc : AEMeasurable (fun a : Shao.Path N => WithLp.toLp 2
      (cutBlockVector m N b h a)) (Measure.pi (fun _ : Fin N => ν)) := by
    exact ((PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).comp
      (cutBlockVector_continuous m N b h)).measurable.aemeasurable
  rw [charFun_map_eq_charFun_map_inner_one hc]
  simp_rw [cutBlockVector_inner m N b hb h]
  have hi : iIndepFun (fun i : Fin N => fun a : Shao.Path N =>
      cutCoeff m N b h t i * a i) (Measure.pi (fun _ : Fin N => ν)) :=
    (iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)).comp
      (fun i y => cutCoeff m N b h t i * y) (by fun_prop)
  rw [hi.charFun_map_fun_sum_eq_prod (fun i =>
    ((measurable_pi_apply i).const_mul (cutCoeff m N b h t i)).aemeasurable)]
  simp only [Finset.prod_apply]
  have heval (i : Fin N) :
      (Measure.pi (fun _ : Fin N => ν)).map (fun a : Shao.Path N => a i) = ν :=
    (measurePreserving_eval (fun _ : Fin N => ν) i).map_eq
  have hfactor (i : Fin N) :
      charFun ((Measure.pi (fun _ : Fin N => ν)).map
        (fun a : Shao.Path N => cutCoeff m N b h t i * a i)) (1 : ℝ) =
          charFun ν (cutCoeff m N b h t i) := by
    rw [charFun_map_mul_comp (measurable_pi_apply i).aemeasurable, heval, mul_one]
  simp_rw [hfactor]
  exact prod_charFun_cutCoeff m N b hb hN ν h t

private theorem cutBlockVector_map_eq_pi (m N : ℕ) (b : Fin (m + 1) → ℕ)
    (hb : Monotone b) (hN : b (Fin.last m) ≤ N)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (h : ℝ) :
    (Measure.pi (fun _ : Fin N => ν)).map (cutBlockVector m N b h) =
      Measure.pi (fun k : Fin m =>
        (Measure.pi (fun _ : Fin (b k.succ - b k.castSucc) => ν)).map
          (Shao.OQ4.RowBlockGaussianLimit.scaledBlockSum
            (b k.succ - b k.castSucc) h)) := by
  apply charFun_eq_pi_iff.mp
  intro t
  rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop)
    (cutBlockVector_continuous m N b h).measurable.aemeasurable]
  simp only [Function.comp_def]
  rw [cutBlockVector_charFun m N b hb hN ν h t]
  apply Finset.prod_congr rfl
  intro k _
  exact (Shao.OQ4.RowBlockGaussianLimit.charFun_scaledBlockSum _ ν h (t k)).symm

/- PUBLIC: exact joint law of the actual disjoint floor blocks. -/

theorem floor_block_vector_map_eq_pi
    (m N : ℕ) (D : Fin m → ℝ≥0) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hN : (totalDuration D : ℝ) * h ^ 2 ≤ (N : ℝ)) :
    (Measure.pi (fun _ : Fin N => ν)).map (floorBlockVector N h D) =
      Measure.pi (fun k : Fin m =>
        (Measure.pi (fun _ : Fin (floorBlockLength D h k) => ν)).map
          (Shao.OQ4.RowBlockGaussianLimit.scaledBlockSum (floorBlockLength D h k) h))
    := by
  let b : Fin (m + 1) → ℕ := fun k => floorGridIndex D h k.val
  have hb : Monotone b := fun _ _ hkl => floorGridIndex_monotone D h hkl
  have hbN : b (Fin.last m) ≤ N :=
    floorGridIndex_le_length N h D hN m le_rfl
  exact cutBlockVector_map_eq_pi m N b hb hbN ν h

/- PRIVATE: ratio is DERIVED here; no ratio premise in either public FDD head. -/

private theorem floorBlockLength_ratio_tendsto
    (m : ℕ) (D : Fin m → ℝ≥0) (hSeq : ℕ → ℝ)
    (hh : Tendsto hSeq atTop atTop) (k : Fin m) :
    Tendsto (fun j => (floorBlockLength D (hSeq j) k : ℝ) / (hSeq j) ^ 2)
      atTop (𝓝 (D k : ℝ)) := by
  have hp : Tendsto (fun j => (hSeq j) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hh
  have hq (q : ℕ) : Tendsto (fun j =>
      (floorGridIndex D (hSeq j) q : ℝ) / (hSeq j) ^ 2)
      atTop (𝓝 (durationPrefix D q : ℝ)) :=
    (tendsto_nat_floor_mul_div_atTop (durationPrefix D q).2).comp hp
  have hs := (hq (k.val + 1)).sub (hq k.val)
  have heq (j : ℕ) : (floorBlockLength D (hSeq j) k : ℝ) / (hSeq j) ^ 2 =
      (floorGridIndex D (hSeq j) (k.val + 1) : ℝ) / (hSeq j) ^ 2 -
        (floorGridIndex D (hSeq j) k.val : ℝ) / (hSeq j) ^ 2 := by
    rw [floorBlockLength, Nat.cast_sub
      (floorGridIndex_monotone D (hSeq j) (Nat.le_succ k.val)), sub_div]
  simpa only [← heq, durationPrefix_succ, NNReal.coe_add, add_sub_cancel_left] using hs

private theorem floorBlockVector_tendsto_gaussian_product
    (m : ℕ) (D : Fin m → ℝ≥0)
    (νSeq : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (νSeq j)]
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hbound : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (hh : Tendsto hSeq atTop atTop)
    (NSeq : ℕ → ℕ)
    (hN : ∀ j, (totalDuration D : ℝ) * (hSeq j) ^ 2 ≤ (NSeq j : ℝ)) :
    TendstoInDistribution (fun j => floorBlockVector (NSeq j) (hSeq j) D) atTop
      (id : (Fin m → ℝ) → (Fin m → ℝ))
      (fun j => Measure.pi (fun _ : Fin (NSeq j) => νSeq j))
      (gaussianIncrementLaw D) := by
  have hE : TendstoInDistribution
      (fun j a => WithLp.toLp 2 (floorBlockVector (NSeq j) (hSeq j) D a)) atTop
      (fun g : Fin m → ℝ => WithLp.toLp 2 g)
      (fun j => Measure.pi (fun _ : Fin (NSeq j) => νSeq j))
      (gaussianIncrementLaw D) := by
    apply TendstoInDistribution.of_tendsto_charFun
      (fun j => ((PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).comp
        (floorBlockVector_continuous (NSeq j) (hSeq j) D)).measurable.aemeasurable)
      (by fun_prop)
    intro t
    have hchar (j : ℕ) : charFun
        ((Measure.pi (fun _ : Fin (NSeq j) => νSeq j)).map
          (fun a => WithLp.toLp 2 (floorBlockVector (NSeq j) (hSeq j) D a))) t =
        ∏ k : Fin m, (charFun (νSeq j) (t k / hSeq j)) ^
          floorBlockLength D (hSeq j) k := by
      have hmap :
          (((Measure.pi (fun _ : Fin (NSeq j) => νSeq j)).map
            (floorBlockVector (NSeq j) (hSeq j) D)).map
            (fun g : Fin m → ℝ => WithLp.toLp 2 g)) =
          (Measure.pi (fun _ : Fin (NSeq j) => νSeq j)).map
            (fun a => WithLp.toLp 2 (floorBlockVector (NSeq j) (hSeq j) D a)) := by
        simpa only [Function.comp_def] using Measure.map_map
          (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).measurable
          (floorBlockVector_continuous (NSeq j) (hSeq j) D).measurable
      rw [← hmap,
        floor_block_vector_map_eq_pi m (NSeq j) D (νSeq j) (hSeq j) (hN j), charFun_pi]
      simp_rw [Shao.OQ4.RowBlockGaussianLimit.charFun_scaledBlockSum]
    have htarget : charFun ((gaussianIncrementLaw D).map
        (fun g : Fin m → ℝ => WithLp.toLp 2 g)) t =
        ∏ k : Fin m, Complex.exp ((-((D k : ℝ) * (t k) ^ 2) / 2 : ℝ) : ℂ) := by
      rw [gaussianIncrementLaw, charFun_pi]
      apply Finset.prod_congr rfl
      intro k _
      rw [charFun_gaussianReal]
      congr 1
      push_cast
      ring
    simp only [Function.comp_def, hchar, htarget]
    apply tendsto_finsetProd
    intro k _
    simpa only [Shao.OQ4.RowBlockGaussianLimit.charFun_scaledBlockSum] using
      Shao.OQ4.RowBlockGaussianLimit.row_block_charFun_tendsto νSeq h3 hmean hsecond
        M hbound hSeq hh (fun j => floorBlockLength D (hSeq j) k) (D k)
        (floorBlockLength_ratio_tendsto m D hSeq hh k) (t k)
  have hc := hE.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : Fin m => ℝ))
  apply hc.congr
  · intro j
    exact Eventually.of_forall fun a => rfl
  · exact Eventually.of_forall fun g => rfl

/- PUBLIC TARGET 1: actual floor prefixes, actual independent Gaussian target. -/

theorem row_floor_prefix_tendsto_cumulative_gaussian
    (m : ℕ) (D : Fin m → ℝ≥0)
    (νSeq : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (νSeq j)]
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hbound : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (hh : Tendsto hSeq atTop atTop)
    (NSeq : ℕ → ℕ)
    (hN : ∀ j, (totalDuration D : ℝ) * (hSeq j) ^ 2 ≤ (NSeq j : ℝ)) :
    TendstoInDistribution (fun j => floorPrefixVector (NSeq j) (hSeq j) D) atTop
      (id : (Fin m → ℝ) → (Fin m → ℝ))
      (fun j => Measure.pi (fun _ : Fin (NSeq j) => νSeq j))
      (cumulativeGaussianLaw D) := by
  have hc := (floorBlockVector_tendsto_gaussian_product m D νSeq h3 hmean hsecond
    M hbound hSeq hh NSeq hN).continuous_comp (cumulativeMap_continuous m)
  refine ⟨fun j => (floorPrefixVector_continuous (NSeq j) (hSeq j) D).measurable.aemeasurable,
    measurable_id.aemeasurable, ?_⟩
  simpa only [Function.comp_def, cumulative_floorBlockVector, cumulativeGaussianLaw,
    id_eq, Measure.map_id] using hc.tendsto

/- PRIVATE: explicit actual residual coefficient, valid for ANY real h,t. -/

private def endpointResidualCoeff (N : ℕ) (h t : ℝ) (i : Fin N) : ℝ :=
  (max 0 (min 1 (t * h ^ 2 - (i.val : ℝ))) -
    (if i.val < Nat.floor (t * h ^ 2) then 1 else 0)) / h

private theorem polygonal_floor_error_eq_weighted_sum
    (N : ℕ) (h t : ℝ) (a : Shao.Path N) :
    Shao.OQ4.PolygonalThirdMoment.polygonalPath N h a t -
        Shao.prefixSum a (Nat.floor (t * h ^ 2)) / h =
      ∑ i : Fin N, endpointResidualCoeff N h t i * a i
    := by
  classical
  unfold Shao.OQ4.PolygonalThirdMoment.polygonalPath Shao.prefixSum
  simp only [Finset.sum_filter]
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [endpointResidualCoeff]
  split_ifs <;> simp_all <;> ring

/- PUBLIC: integrability all rows, including arbitrary finite bad-h prefixes. -/

theorem polygonal_floor_error_abs_cube_integrable
    (N : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν) (h t : ℝ) :
    Integrable (fun a : Shao.Path N =>
      |Shao.OQ4.PolygonalThirdMoment.polygonalPath N h a t -
        Shao.prefixSum a (Nat.floor (t * h ^ 2)) / h| ^ 3)
      (Measure.pi (fun _ : Fin N => ν)) := by
  simpa only [polygonal_floor_error_eq_weighted_sum] using
    Shao.OQ4.WeightedThirdMoment.weighted_sum_abs_cube_integrable N ν h3
      (endpointResidualCoeff N h t)

/- PUBLIC: actual B3 fixed-time floor residual bound. -/

theorem polygonal_floor_error_abs_cube_le
    (N : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (h t : ℝ) (hh : 0 < h) (ht0 : 0 ≤ t) (htN : t * h ^ 2 ≤ (N : ℝ)) :
    (∫ a : Shao.Path N,
      |Shao.OQ4.PolygonalThirdMoment.polygonalPath N h a t -
        Shao.prefixSum a (Nat.floor (t * h ^ 2)) / h| ^ 3
      ∂(Measure.pi (fun _ : Fin N => ν))) ≤
      24 * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3 := by
  let q := Nat.floor (t * h ^ 2)
  let s := (q : ℝ) / h ^ 2
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
  have ht2 : 0 ≤ t * h ^ 2 := mul_nonneg ht0 hh2.le
  have hq : (q : ℝ) ≤ t * h ^ 2 := Nat.floor_le ht2
  have hqN : q ≤ N := Nat.floor_le_of_le htN
  have hs : 0 ≤ s := div_nonneg (Nat.cast_nonneg q) hh2.le
  have hst : s ≤ t := (div_le_iff₀ hh2).2 hq
  have hgap : t - s ≤ (1 / h) ^ 2 := by
    have hfloor : t * h ^ 2 < (q : ℝ) + 1 := Nat.lt_floor_add_one (t * h ^ 2)
    dsimp only [s]
    rw [one_div_pow]
    apply (le_div_iff₀ hh2).2
    have hdiv : ((q : ℝ) / h ^ 2) * h ^ 2 = q := div_mul_cancel₀ _ hh2.ne'
    nlinarith
  have hroot : Real.sqrt (t - s) ≤ 1 / h := by
    exact (Real.sqrt_le_iff).2 ⟨by positivity, hgap⟩
  have hβ : 0 ≤ ∫ x : ℝ, |x| ^ 3 ∂ν := integral_nonneg (fun x => by positivity)
  have hpow : (Real.sqrt (t - s)) ^ 3 ≤ (1 / h) ^ 3 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 3
  have hgrid (a : Shao.Path N) :
      Shao.OQ4.PolygonalThirdMoment.polygonalPath N h a ((q : ℝ) / h ^ 2) =
        Shao.prefixSum a q / h :=
    Shao.OQ4.PolygonalThirdMoment.polygonalPath_at_grid N h hh a q hqN
  have hb := Shao.OQ4.PolygonalThirdMoment.polygonal_increment_abs_cube_le
    N ν h3 hmean h s t hh hs hst htN
  have hsame : (fun a : Shao.Path N =>
      |Shao.OQ4.PolygonalThirdMoment.polygonalPath N h a t -
        Shao.OQ4.PolygonalThirdMoment.polygonalPath N h a s| ^ 3) =
      (fun a : Shao.Path N =>
        |Shao.OQ4.PolygonalThirdMoment.polygonalPath N h a t -
          Shao.prefixSum a (Nat.floor (t * h ^ 2)) / h| ^ 3) := by
    funext a
    rw [show s = (q : ℝ) / h ^ 2 from rfl, hgrid a]
  rw [hsame] at hb
  calc
    _ ≤ 24 * (∫ x : ℝ, |x| ^ 3 ∂ν) * (Real.sqrt (t - s)) ^ 3 := hb
    _ ≤ 24 * (∫ x : ℝ, |x| ^ 3 ∂ν) * (1 / h) ^ 3 :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num) hβ)
    _ = _ := by rw [one_div_pow, mul_one_div]

/- PUBLIC: each actual coordinate residual disappears in L3. -/

theorem row_polygonal_error_abs_cube_tendsto_zero
    (m : ℕ) (D : Fin m → ℝ≥0)
    (νSeq : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (νSeq j)]
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (M : ℝ) (hbound : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (hh : Tendsto hSeq atTop atTop)
    (NSeq : ℕ → ℕ)
    (hN : ∀ j, (totalDuration D : ℝ) * (hSeq j) ^ 2 ≤ (NSeq j : ℝ))
    (k : Fin m) :
    Tendsto (fun j => ∫ a : Shao.Path (NSeq j),
      |polygonalVector (NSeq j) (hSeq j) D a k -
        floorPrefixVector (NSeq j) (hSeq j) D a k| ^ 3
      ∂(Measure.pi (fun _ : Fin (NSeq j) => νSeq j))) atTop (𝓝 (0 : ℝ)) := by
  have hlim : Tendsto (fun j => 24 * M / (hSeq j) ^ 3) atTop (𝓝 (0 : ℝ)) := by
    simpa [div_eq_mul_inv, inv_pow] using
      ((tendsto_inv_atTop_zero.comp hh).pow 3).const_mul (24 * M)
  apply squeeze_zero' (Eventually.of_forall fun j => integral_nonneg (fun a => by positivity))
    ?_ hlim
  filter_upwards [hh.eventually_ge_atTop 1] with j hj
  have hhj : 0 < hSeq j := lt_of_lt_of_le (by norm_num) hj
  have htk : (observationTime D k : ℝ) * (hSeq j) ^ 2 ≤ (NSeq j : ℝ) :=
    (mul_le_mul_of_nonneg_right
      (show (observationTime D k : ℝ) ≤ (totalDuration D : ℝ) by
        exact_mod_cast observationTime_le_total D k) (sq_nonneg _)).trans (hN j)
  calc
    _ ≤ 24 * (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) / (hSeq j) ^ 3 := by
      exact polygonal_floor_error_abs_cube_le (NSeq j) (νSeq j) (h3 j) (hmean j)
        (hSeq j) (observationTime D k : ℝ) hhj (observationTime D k).2 htk
    _ ≤ _ := by gcongr; exact hbound j

/- PUBLIC: actual finite-vector probability bound, no limit premise. -/

theorem polygonal_vector_error_probability_le
    (m N : ℕ) (D : Fin m → ℝ≥0) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (h : ℝ) (hh : 0 < h) (hN : (totalDuration D : ℝ) * h ^ 2 ≤ (N : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin N => ν)).real
      {a : Shao.Path N | ε < ‖polygonalVector N h D a - floorPrefixVector N h D a‖} ≤
        (m : ℝ) * 24 * (∫ x : ℝ, |x| ^ 3 ∂ν) / (ε ^ 3 * h ^ 3) := by
  classical
  let μ := Measure.pi (fun _ : Fin N => ν)
  let R : Shao.Path N → Fin m → ℝ := fun a =>
    polygonalVector N h D a - floorPrefixVector N h D a
  have hε3 : 0 < ε ^ 3 := pow_pos hε 3
  have hcoord (k : Fin m) :
      μ.real {a | ε < |R a k|} ≤
        (24 * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3) / ε ^ 3 := by
    have htk : (observationTime D k : ℝ) * h ^ 2 ≤ (N : ℝ) :=
      (mul_le_mul_of_nonneg_right
        (show (observationTime D k : ℝ) ≤ (totalDuration D : ℝ) by
          exact_mod_cast observationTime_le_total D k) (sq_nonneg h)).trans hN
    have hi : Integrable (fun a => |R a k| ^ 3) μ :=
      polygonal_floor_error_abs_cube_integrable N ν h3 h (observationTime D k : ℝ)
    have hb : (∫ a, |R a k| ^ 3 ∂μ) ≤
        24 * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3 :=
      polygonal_floor_error_abs_cube_le N ν h3 hmean h (observationTime D k : ℝ)
        hh (observationTime D k).2 htk
    have hm := mul_meas_ge_le_integral_of_nonneg
      (μ := μ) (f := fun a => |R a k| ^ 3)
      (Eventually.of_forall fun a => by positivity) hi (ε ^ 3)
    calc
      _ ≤ μ.real {a | ε ^ 3 ≤ |R a k| ^ 3} := measureReal_mono (by
        intro a ha
        exact pow_le_pow_left₀ hε.le (le_of_lt ha) 3)
      _ ≤ (∫ a, |R a k| ^ 3 ∂μ) / ε ^ 3 := by
        apply (le_div_iff₀ hε3).2
        simpa [mul_comm] using hm
      _ ≤ _ := div_le_div_of_nonneg_right hb hε3.le
  have hsubset : {a : Shao.Path N | ε < ‖R a‖} ⊆
      ⋃ k : Fin m, {a | ε < |R a k|} := by
    intro a ha
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    by_contra hex
    push Not at hex
    have hn : ‖R a‖ ≤ ε := (pi_norm_le_iff_of_nonneg hε.le).2
      (fun k => by simpa only [Real.norm_eq_abs] using hex k)
    exact (not_lt_of_ge hn) ha
  calc
    _ ≤ μ.real (⋃ k : Fin m, {a | ε < |R a k|}) := measureReal_mono hsubset
    _ ≤ ∑ k : Fin m, μ.real {a | ε < |R a k|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : Fin m,
        (24 * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3) / ε ^ 3 :=
      Finset.sum_le_sum (fun k _ => hcoord k)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem row_polygonal_vector_error_probability_tendsto_zero
    (m : ℕ) (D : Fin m → ℝ≥0)
    (νSeq : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (νSeq j)]
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (M : ℝ) (hbound : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (hh : Tendsto hSeq atTop atTop)
    (NSeq : ℕ → ℕ)
    (hN : ∀ j, (totalDuration D : ℝ) * (hSeq j) ^ 2 ≤ (NSeq j : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun j => (Measure.pi (fun _ : Fin (NSeq j) => νSeq j)).real
      {a : Shao.Path (NSeq j) | ε <
        ‖polygonalVector (NSeq j) (hSeq j) D a -
          floorPrefixVector (NSeq j) (hSeq j) D a‖}) atTop (𝓝 (0 : ℝ)) := by
  let A : ℝ := (m : ℝ) * 24 * M / ε ^ 3
  have hlim : Tendsto (fun j => A * ((hSeq j)⁻¹) ^ 3) atTop (𝓝 (0 : ℝ)) := by
    simpa using ((tendsto_inv_atTop_zero.comp hh).pow 3).const_mul A
  apply squeeze_zero' (Eventually.of_forall fun j => measureReal_nonneg) ?_ hlim
  filter_upwards [hh.eventually_ge_atTop 1] with j hj
  have hhj : 0 < hSeq j := lt_of_lt_of_le (by norm_num) hj
  calc
    _ ≤ (m : ℝ) * 24 * (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) /
        (ε ^ 3 * (hSeq j) ^ 3) :=
      polygonal_vector_error_probability_le m (NSeq j) D (νSeq j)
        (h3 j) (hmean j) (hSeq j) hhj (hN j) ε hε
    _ ≤ (m : ℝ) * 24 * M / (ε ^ 3 * (hSeq j) ^ 3) := by
      gcongr
      exact hbound j
    _ = _ := by simp only [A, div_eq_mul_inv, mul_inv_rev, inv_pow]; ring

/- PRIVATE: general cubic-to-L1 and varying-row transfer, PROVED in math-proof.
These are tools with independently verified elementary proofs, not hypotheses
added to either final theorem. No common source measure/domain is required.
-/

private theorem abs_integrable_of_cube
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : AEMeasurable f μ)
    (h3 : Integrable (fun a => |f a| ^ 3) μ) :
    Integrable (fun a => |f a|) μ := by
  have hdom (a : Ω) : |f a| ≤ 1 + |f a| ^ 3 := by
    have hx := abs_nonneg (f a)
    by_cases h1 : |f a| ≤ 1
    · nlinarith [pow_nonneg hx 3]
    · have h1' : 1 ≤ |f a| := le_of_not_ge h1
      have h2 : |f a| ≤ |f a| ^ 2 := by
        nlinarith [mul_nonneg hx (sub_nonneg.mpr h1')]
      have h3' : |f a| ^ 2 ≤ |f a| ^ 3 := by
        nlinarith [mul_nonneg (sq_nonneg |f a|) (sub_nonneg.mpr h1')]
      nlinarith
  have hAbs : AEStronglyMeasurable (fun a => |f a|) μ :=
    (continuous_abs.measurable.comp_aemeasurable hf).aestronglyMeasurable
  exact ((integrable_const 1).add h3).mono' hAbs
    (Eventually.of_forall fun a => by
      simpa only [Real.norm_eq_abs, abs_abs, Pi.add_apply] using hdom a)

private theorem integral_abs_le_split
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : AEMeasurable f μ)
    (h3 : Integrable (fun a => |f a| ^ 3) μ) (δ : ℝ) (hδ : 0 < δ) :
    (∫ a, |f a| ∂μ) ≤ δ + (∫ a, |f a| ^ 3 ∂μ) / δ ^ 2 := by
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hpoint (a : Ω) : |f a| ≤ δ + |f a| ^ 3 / δ ^ 2 := by
    by_cases hsmall : |f a| ≤ δ
    · exact hsmall.trans (le_add_of_nonneg_right (by positivity))
    · have hlarge : δ ≤ |f a| := le_of_not_ge hsmall
      have hsquare : δ ^ 2 ≤ |f a| ^ 2 := pow_le_pow_left₀ hδ.le hlarge 2
      have hm := mul_le_mul_of_nonneg_right hsquare (abs_nonneg (f a))
      have hmain : |f a| ≤ |f a| ^ 3 / δ ^ 2 := by
        apply (le_div_iff₀ hδ2).2
        nlinarith [hm]
      exact hmain.trans (le_add_of_nonneg_left hδ.le)
  have hb := integral_mono (abs_integrable_of_cube μ f hf h3)
    ((integrable_const δ).add (h3.div_const (δ ^ 2))) hpoint
  simpa [integral_add (integrable_const δ) (h3.div_const (δ ^ 2)), integral_div] using hb

private theorem integral_abs_tendsto_of_cube_tendsto
    {Ω : ℕ → Type*} [∀ j, MeasurableSpace (Ω j)]
    (μ : (j : ℕ) → Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (f : (j : ℕ) → Ω j → ℝ) (hf : ∀ j, AEMeasurable (f j) (μ j))
    (h3 : ∀ j, Integrable (fun a => |f j a| ^ 3) (μ j))
    (hlim : Tendsto (fun j => ∫ a, |f j a| ^ 3 ∂(μ j)) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j => ∫ a, |f j a| ∂(μ j)) atTop (𝓝 (0 : ℝ)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun j => ha.trans_le (integral_nonneg (fun _ => abs_nonneg _))
  · intro b hb
    have hδ : 0 < b / 2 := half_pos hb
    have hδ2 : 0 < (b / 2) ^ 2 := sq_pos_of_pos hδ
    have ht : 0 < (b / 2) * (b / 2) ^ 2 := mul_pos hδ hδ2
    filter_upwards [hlim.eventually (gt_mem_nhds ht)] with j hj
    have hs := integral_abs_le_split (μ j) (f j) (hf j) (h3 j) (b / 2) hδ
    have hq : (∫ a, |f j a| ^ 3 ∂(μ j)) / (b / 2) ^ 2 < b / 2 :=
      (div_lt_iff₀ hδ2).2 hj
    linarith

private theorem charFun_vector_difference_le
    (m : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → (Fin m → ℝ))
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (habs : ∀ k : Fin m, Integrable (fun a => |Y a k - X a k|) μ)
    (t : EuclideanSpace ℝ (Fin m)) :
    ‖charFun (μ.map (fun a => WithLp.toLp 2 (Y a))) t -
        charFun (μ.map (fun a => WithLp.toLp 2 (X a))) t‖ ≤
      ∑ k : Fin m, |t k| * (∫ a, |Y a k - X a k| ∂μ) := by
  classical
  have hJX : AEMeasurable (fun a => WithLp.toLp 2 (X a)) μ :=
    (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurable.comp_aemeasurable hX
  have hJY : AEMeasurable (fun a => WithLp.toLp 2 (Y a)) μ :=
    (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurable.comp_aemeasurable hY
  have hXI : Integrable (fun a => Complex.exp
      ((inner ℝ (WithLp.toLp 2 (X a)) t : ℝ) * Complex.I)) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Eventually.of_forall fun a => by simp only [Complex.norm_exp_ofReal_mul_I, le_refl]
  have hYI : Integrable (fun a => Complex.exp
      ((inner ℝ (WithLp.toLp 2 (Y a)) t : ℝ) * Complex.I)) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Eventually.of_forall fun a => by simp only [Complex.norm_exp_ofReal_mul_I, le_refl]
  have hphase (x y : ℝ) :
      ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ ≤ |x - y| := by
    have harg : (y : ℂ) * Complex.I + Complex.I * ((x - y : ℝ) : ℂ) =
        (x : ℂ) * Complex.I := by push_cast; ring
    have heq : Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I) =
        Complex.exp ((y : ℂ) * Complex.I) *
          (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add, harg]
    rw [heq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    simpa only [Real.norm_eq_abs] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y))
  have hinner (a : Ω) : inner ℝ (WithLp.toLp 2 (Y a)) t -
      inner ℝ (WithLp.toLp 2 (X a)) t =
        ∑ k : Fin m, t k * (Y a k - X a k) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hpoint (a : Ω) :
      ‖Complex.exp ((inner ℝ (WithLp.toLp 2 (Y a)) t : ℝ) * Complex.I) -
        Complex.exp ((inner ℝ (WithLp.toLp 2 (X a)) t : ℝ) * Complex.I)‖ ≤
          ∑ k : Fin m, |t k| * |Y a k - X a k| := by
    calc
      _ ≤ |inner ℝ (WithLp.toLp 2 (Y a)) t -
          inner ℝ (WithLp.toLp 2 (X a)) t| := hphase _ _
      _ = ‖∑ k : Fin m, t k * (Y a k - X a k)‖ := by
        rw [hinner, Real.norm_eq_abs]
      _ ≤ ∑ k : Fin m, ‖t k * (Y a k - X a k)‖ := norm_sum_le _ _
      _ = _ := by simp only [Real.norm_eq_abs, abs_mul]
  have hright : Integrable (fun a => ∑ k : Fin m, |t k| * |Y a k - X a k|) μ :=
    integrable_finsetSum Finset.univ (fun k _ => (habs k).const_mul |t k|)
  rw [charFun_apply, charFun_apply, integral_map hJY (by fun_prop),
    integral_map hJX (by fun_prop), ← integral_sub hYI hXI]
  calc
    _ ≤ ∫ a, ‖Complex.exp ((inner ℝ (WithLp.toLp 2 (Y a)) t : ℝ) * Complex.I) -
        Complex.exp ((inner ℝ (WithLp.toLp 2 (X a)) t : ℝ) * Complex.I)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ a, ∑ k : Fin m, |t k| * |Y a k - X a k| ∂μ :=
      integral_mono (hYI.sub hXI).norm hright hpoint
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun k _ => (habs k).const_mul |t k|)]
      simp only [integral_const_mul]

private theorem varying_row_vector_transfer_of_cubic_errors
    (m : ℕ) {Ω : ℕ → Type*} [∀ j, MeasurableSpace (Ω j)]
    (μ : (j : ℕ) → Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (X Y : (j : ℕ) → Ω j → (Fin m → ℝ))
    (ρ : Measure (Fin m → ℝ)) [IsProbabilityMeasure ρ]
    (hX : TendstoInDistribution X atTop
      (id : (Fin m → ℝ) → (Fin m → ℝ)) μ ρ)
    (hY : ∀ j, AEMeasurable (Y j) (μ j))
    (h3 : ∀ j (k : Fin m), Integrable (fun a => |Y j a k - X j a k| ^ 3) (μ j))
    (hlim : ∀ k : Fin m,
      Tendsto (fun j => ∫ a, |Y j a k - X j a k| ^ 3 ∂(μ j)) atTop (𝓝 (0 : ℝ))) :
    TendstoInDistribution Y atTop (id : (Fin m → ℝ) → (Fin m → ℝ)) μ ρ := by
  classical
  have hmeas (j : ℕ) (k : Fin m) : AEMeasurable (fun a => Y j a k - X j a k) (μ j) :=
    ((measurable_pi_apply k).comp_aemeasurable (hY j)).sub
      ((measurable_pi_apply k).comp_aemeasurable (hX.forall_aemeasurable j))
  have habs (j : ℕ) (k : Fin m) : Integrable (fun a => |Y j a k - X j a k|) (μ j) :=
    abs_integrable_of_cube (μ j) _ (hmeas j k) (h3 j k)
  have hL1 (k : Fin m) : Tendsto (fun j => ∫ a, |Y j a k - X j a k| ∂(μ j))
      atTop (𝓝 (0 : ℝ)) :=
    integral_abs_tendsto_of_cube_tendsto μ (fun j a => Y j a k - X j a k)
      (fun j => hmeas j k) (fun j => h3 j k) (hlim k)
  have hXE := hX.continuous_comp (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ))
  have hE : TendstoInDistribution
      (fun j a => WithLp.toLp 2 (Y j a)) atTop
      (fun g : Fin m → ℝ => WithLp.toLp 2 g) μ ρ := by
    apply TendstoInDistribution.of_tendsto_charFun
      (fun j => (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurable.comp_aemeasurable (hY j))
      (by fun_prop)
    intro t
    have hsum : Tendsto (fun j => ∑ k : Fin m,
        |t k| * (∫ a, |Y j a k - X j a k| ∂(μ j))) atTop (𝓝 (0 : ℝ)) := by
      simpa using tendsto_finsetSum Finset.univ (fun k _ => (hL1 k).const_mul |t k|)
    have hd : Tendsto (fun j =>
        charFun ((μ j).map (fun a => WithLp.toLp 2 (Y j a))) t -
          charFun ((μ j).map (fun a => WithLp.toLp 2 (X j a))) t)
        atTop (𝓝 (0 : ℂ)) := by
      apply (tendsto_zero_iff_norm_tendsto_zero).2
      exact squeeze_zero' (Eventually.of_forall fun j => norm_nonneg _)
        (Eventually.of_forall fun j => charFun_vector_difference_le m (μ j) (X j) (Y j)
          (hX.forall_aemeasurable j) (hY j) (habs j) t) hsum
    simpa only [Function.comp_def, id_eq, MeasurableEquiv.coe_toLp,
      sub_add_cancel, zero_add] using
      hd.add (hXE.tendsto_charFun t)
  have hc := hE.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : Fin m => ℝ))
  apply hc.congr
  · intro j
    exact Eventually.of_forall fun a => rfl
  · exact Eventually.of_forall fun g => rfl

/- PUBLIC TARGET 2: actual B3 polygonal values, same actual joint limit law. -/

theorem row_polygonal_tendsto_cumulative_gaussian
    (m : ℕ) (D : Fin m → ℝ≥0)
    (νSeq : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (νSeq j)]
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hbound : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (hh : Tendsto hSeq atTop atTop)
    (NSeq : ℕ → ℕ)
    (hN : ∀ j, (totalDuration D : ℝ) * (hSeq j) ^ 2 ≤ (NSeq j : ℝ)) :
    TendstoInDistribution (fun j => polygonalVector (NSeq j) (hSeq j) D) atTop
      (id : (Fin m → ℝ) → (Fin m → ℝ))
      (fun j => Measure.pi (fun _ : Fin (NSeq j) => νSeq j))
      (cumulativeGaussianLaw D) := by
  apply varying_row_vector_transfer_of_cubic_errors m
    (fun j => Measure.pi (fun _ : Fin (NSeq j) => νSeq j))
    (fun j => floorPrefixVector (NSeq j) (hSeq j) D)
    (fun j => polygonalVector (NSeq j) (hSeq j) D) (cumulativeGaussianLaw D)
    (row_floor_prefix_tendsto_cumulative_gaussian m D νSeq h3 hmean hsecond
      M hbound hSeq hh NSeq hN)
    (fun j => (polygonalVector_continuous (NSeq j) (hSeq j) D).measurable.aemeasurable)
  · intro j k
    exact polygonal_floor_error_abs_cube_integrable (NSeq j) (νSeq j) (h3 j)
      (hSeq j) (observationTime D k : ℝ)
  · intro k
    exact row_polygonal_error_abs_cube_tendsto_zero m D νSeq h3 hmean M hbound hSeq hh NSeq hN k

end

end Shao.OQ4.RowPolygonalFDD
