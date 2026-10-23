import Shao.Probability.MeasurablePath
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.SpecialFunctions.Exp
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.List.Rotate
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite, labelled Spitzer combinatorics

The intended all-real finite cut identity is the deterministic producer behind
Spitzer's maximum-transform identity. The marked-word construction follows the
3214 transformation of Abramson and Pitman, Section 8, Theorem 26 (2011).
Generic subset means are internal deterministic proof devices; probability
laws, moment assumptions, and sample-dependent iid invariance are not inputs.

This file is an in-progress implementation of the frozen finite declarations.
Only declarations whose proofs are present below have been implemented.
-/

noncomputable section

namespace Shao.Probability.Spitzer

open Finset Set
open scoped BigOperators Topology

def reorder {n : ℕ} (a : Shao.Path n) (σ : Equiv.Perm (Fin n)) :
    Shao.Path n := fun i => a (σ i)

def head {n : ℕ} (a : Shao.Path n) (k : ℕ) (hk : k ≤ n) :
    Shao.Path k :=
  fun i => a ⟨i.val, Nat.lt_of_lt_of_le i.is_lt hk⟩

def tail {n : ℕ} (a : Shao.Path n) (k : ℕ) (hk : k ≤ n) :
    Shao.Path (n - k) :=
  fun i => a ⟨k + i.val, by omega⟩

def subsetMean {n : ℕ} (a : Shao.Path n) (u : Finset (Fin n)) : ℝ :=
  (∑ i ∈ u, a i) / (u.card : ℝ)

def DistinctDisjointMeans {n : ℕ} (a : Shao.Path n) : Prop :=
  ∀ u v : Finset (Fin n), u.Nonempty → v.Nonempty →
    Disjoint u v → subsetMean a u ≠ subsetMean a v

def wordSum {n : ℕ} (a : Shao.Path n) (w : List (Fin n)) : ℝ :=
  (w.map a).sum

def wordMean {n : ℕ} (a : Shao.Path n) (w : List (Fin n)) : ℝ :=
  wordSum a w / (w.length : ℝ)

def rotateWord {α : Type*} (w : List α) (r : ℕ) : List α :=
  w.drop r ++ w.take r

def StrictBelowChord {n : ℕ} (a : Shao.Path n) (w : List (Fin n)) : Prop :=
  w ≠ [] ∧ ∀ j : ℕ, 0 < j → j < w.length →
    wordSum a (w.take j) < (j : ℝ) * wordMean a w

def FaceDecomposition {n : ℕ} (a : Shao.Path n)
    (σ : Equiv.Perm (Fin n)) (B : List (List (Fin n))) : Prop :=
  B.flatten = List.ofFn (fun i : Fin n => σ i) ∧
    (∀ w ∈ B, StrictBelowChord a w) ∧
    B.Pairwise (fun u v => wordMean a v < wordMean a u)

theorem head_prefixSum {n : ℕ} (a : Shao.Path n) (k : ℕ) (hk : k ≤ n)
    (j : ℕ) (hj : j ≤ k) :
    Shao.prefixSum (head a k hk) j = Shao.prefixSum a j := by
  classical
  unfold Shao.prefixSum
  apply Finset.sum_bij (fun i _ => (⟨i.val, Nat.lt_of_lt_of_le i.is_lt hk⟩ : Fin n))
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i hi i' hi' heq
    exact Fin.ext (congrArg (fun x : Fin n => x.val) heq)
  · intro i hi
    have hij : i.val < j := (mem_filter.mp hi).2
    let q : Fin k := ⟨i.val, Nat.lt_of_lt_of_le hij hj⟩
    exact ⟨q, by simpa [q] using hij, Fin.ext rfl⟩
  · intro i hi
    rfl

private theorem continuous_subsetMean {n : ℕ} (u : Finset (Fin n)) :
    Continuous (fun a : Shao.Path n => subsetMean a u) := by
  exact (continuous_finsetSum _ (fun i _ => continuous_apply i)).div_const _

private theorem dense_subsetMean_ne {n : ℕ} (u v : Finset (Fin n))
    (hu : u.Nonempty) (hv : v.Nonempty) (huv : Disjoint u v) :
    Dense {a : Shao.Path n | subsetMean a u ≠ subsetMean a v} := by
  classical
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨a, ha⟩ := hUne
  by_cases hneq : subsetMean a u ≠ subsetMean a v
  · exact ⟨a, ha, hneq⟩
  obtain ⟨i, hi⟩ := hu
  have hiv : i ∉ v := fun h => Finset.disjoint_left.mp huv hi h
  have hcard : (u.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨i, hi⟩).ne'
  let g : ℝ → Shao.Path n := fun t j => a j + if j = i then t else 0
  have hg : Continuous g := by
    apply continuous_pi
    intro j
    dsimp [g]
    split_ifs <;> fun_prop
  have hgu (t : ℝ) : subsetMean (g t) u = subsetMean a u + t / (u.card : ℝ) := by
    simp [subsetMean, g, sum_add_distrib, hi, add_div]
  have hgv (t : ℝ) : subsetMean (g t) v = subsetMean a v := by
    simp [subsetMean, g, sum_add_distrib, hiv]
  have hO : IsOpen (g ⁻¹' U) := hg.isOpen_preimage _ hU
  have hN : (g ⁻¹' U).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [g] using ha
  obtain ⟨t, ht, htU⟩ := (dense_compl_singleton (0 : ℝ)).exists_mem_open hO hN
  have ht0 : t ≠ 0 := by simpa using ht
  refine ⟨g t, htU, ?_⟩
  change subsetMean (g t) u ≠ subsetMean (g t) v
  rw [hgu, hgv]
  have heq : subsetMean a u = subsetMean a v := not_ne_iff.mp hneq
  rw [heq]
  exact fun h => (div_ne_zero ht0 hcard) (by linarith)

private theorem dense_finset_all {E ι : Type*} [TopologicalSpace E]
    (U : ι → Set E) (hopen : ∀ i, IsOpen (U i)) (hdense : ∀ i, Dense (U i))
    (s : Finset ι) : Dense {x : E | ∀ i ∈ s, x ∈ U i} := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (dense_univ : Dense (Set.univ : Set E))
  | @insert i s hi ih =>
    have h := (hdense i).inter_of_isOpen_left ih (hopen i)
    convert h using 1
    ext x
    simp only [Set.mem_ofPred_eq, Finset.mem_insert, Set.mem_inter_iff]
    constructor
    · intro hx
      exact ⟨hx i (Or.inl rfl), fun j hj => hx j (Or.inr hj)⟩
    · rintro ⟨hxi, hxs⟩ j (rfl | hj)
      · exact hxi
      · exact hxs j hj

private theorem dense_distinctDisjointMeans_aux (n : ℕ) :
    Dense {a : Shao.Path n | DistinctDisjointMeans a} := by
  classical
  let I := {p : Finset (Fin n) × Finset (Fin n) //
    p.1.Nonempty ∧ p.2.Nonempty ∧ Disjoint p.1 p.2}
  let U : I → Set (Shao.Path n) := fun p =>
    {a | subsetMean a p.1.1 ≠ subsetMean a p.1.2}
  have ho (p : I) : IsOpen (U p) := by
    exact isOpen_ne_fun (continuous_subsetMean p.1.1) (continuous_subsetMean p.1.2)
  have hd (p : I) : Dense (U p) :=
    dense_subsetMean_ne p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2
  have hall := dense_finset_all U ho hd Finset.univ
  convert hall using 1
  ext a
  simp only [Set.mem_ofPred_eq, Finset.mem_univ, forall_true_left]
  constructor
  · intro ha p
    exact ha p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2
  · intro ha u v hu hv huv
    exact ha ⟨(u, v), hu, hv, huv⟩

theorem exists_distinctDisjointMeans_direction (n : ℕ) :
    ∃ v : Shao.Path n, DistinctDisjointMeans v := by
  exact (dense_distinctDisjointMeans_aux n).nonempty

theorem dense_distinctDisjointMeans (n : ℕ) :
    Dense {a : Shao.Path n | DistinctDisjointMeans a} :=
  dense_distinctDisjointMeans_aux n

private theorem wordSum_eq_finsetSum {n : ℕ} (a : Shao.Path n)
    (w : List (Fin n)) (hw : w.Nodup) :
    wordSum a w = ∑ i ∈ w.toFinset, a i := by
  classical
  induction w with
  | nil => simp [wordSum]
  | cons i w ih =>
    obtain ⟨hi, hw⟩ := List.nodup_cons.mp hw
    simpa [wordSum, hi] using congrArg (fun z : ℝ => a i + z) (ih hw)

private theorem wordMean_eq_subsetMean {n : ℕ} (a : Shao.Path n)
    (w : List (Fin n)) (hw : w.Nodup) :
    wordMean a w = subsetMean a w.toFinset := by
  rw [wordMean, subsetMean, wordSum_eq_finsetSum a w hw,
    List.toFinset_card_of_nodup hw]

private theorem wordMean_ne_of_disjoint {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) (u v : List (Fin n))
    (hu : u.Nodup) (hv : v.Nodup) (hd : u.Disjoint v)
    (hne_u : u ≠ []) (hne_v : v ≠ []) : wordMean a u ≠ wordMean a v := by
  classical
  rw [wordMean_eq_subsetMean a u hu, wordMean_eq_subsetMean a v hv]
  apply ha u.toFinset v.toFinset
  · cases u with
    | nil => exact False.elim (hne_u rfl)
    | cons i u => exact ⟨i, by simp⟩
  · cases v with
    | nil => exact False.elim (hne_v rfl)
    | cons i v => exact ⟨i, by simp⟩
  · exact List.disjoint_toFinset_iff_disjoint.mpr hd

private theorem wordSum_eq_length_mul_mean {n : ℕ} (a : Shao.Path n)
    (w : List (Fin n)) (hne : w ≠ []) :
    wordSum a w = (w.length : ℝ) * wordMean a w := by
  have hc : (w.length : ℝ) ≠ 0 := by
    cases w with
    | nil => exact False.elim (hne rfl)
    | cons i w =>
      have hp : (0 : ℝ) < (w.length : ℝ) + 1 := by positivity
      simpa only [List.length_cons, Nat.cast_add, Nat.cast_one] using hp.ne'
  unfold wordMean
  rw [mul_div_cancel₀ _ hc]

private theorem wordMean_ne_full_of_partition {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) (A B C : List (Fin n))
    (hw : (A ++ B ++ C).Nodup) (hB : B ≠ []) (hAC : A ++ C ≠ []) :
    wordMean a B ≠ wordMean a (A ++ B ++ C) := by
  have hp : (A ++ B ++ C).Perm (B ++ A ++ C) := by
    simpa only [List.append_assoc] using
      ((List.perm_append_comm : (A ++ B).Perm (B ++ A)).append_right C)
  have hn : (B ++ (A ++ C)).Nodup := by
    simpa only [List.append_assoc] using hp.nodup_iff.mp hw
  have hparts := List.nodup_append'.mp hn
  have hne := wordMean_ne_of_disjoint a ha B (A ++ C)
    hparts.1 hparts.2.1 hparts.2.2 hB hAC
  intro heq
  apply hne
  have hfull : A ++ B ++ C ≠ [] := by
    intro h
    exact hB (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).2
  have hb := wordSum_eq_length_mul_mean a B hB
  have hc := wordSum_eq_length_mul_mean a (A ++ C) hAC
  have hf := wordSum_eq_length_mul_mean a (A ++ B ++ C) hfull
  have hs : wordSum a (A ++ B ++ C) = wordSum a B + wordSum a (A ++ C) := by
    simp only [wordSum, List.map_append, List.sum_append]
    ring
  have hl : ((A ++ B ++ C).length : ℝ) =
      (B.length : ℝ) + ((A ++ C).length : ℝ) := by
    simp only [List.length_append, Nat.cast_add]
    ring
  have hcp : 0 < ((A ++ C).length : ℝ) := by
    have : 0 < (A ++ C).length := by
      cases h : A ++ C with
      | nil => exact False.elim (hAC h)
      | cons i w => simp
    exact_mod_cast this
  rw [← heq, hl, hs] at hf
  nlinarith

private def centeredPrefix {n : ℕ} (a : Shao.Path n) (w : List (Fin n)) (j : ℕ) : ℝ :=
  wordSum a (w.take j) - (j : ℝ) * wordMean a w

private theorem centeredPrefix_ne {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) (w : List (Fin n)) (hw : w.Nodup)
    (i j : ℕ) (hij : i < j) (hj : j < w.length) :
    centeredPrefix a w i ≠ centeredPrefix a w j := by
  let A := w.take i
  let B := (w.drop i).take (j - i)
  let C := w.drop j
  have hsum : i + (j - i) = j := by omega
  have hmid : B ++ C = w.drop i := by
    simpa only [hsum] using List.drop_take_append_drop w i (j - i)
  have hfull : A ++ B ++ C = w := by
    rw [List.append_assoc, hmid]
    exact List.take_append_drop i w
  have hpre : A ++ B = w.take j := by
    have ht : w.take (i + (j - i)) = w.take i ++ (w.drop i).take (j - i) :=
      List.take_add
    simpa only [hsum] using ht.symm
  have hBlength : B.length = j - i := by
    simp only [B, List.length_take, List.length_drop]
    omega
  have hB : B ≠ [] := by
    intro h
    have : B.length = 0 := by rw [h]; rfl
    omega
  have hAC : A ++ C ≠ [] := by
    intro h
    have hC : C = [] := (List.append_eq_nil_iff.mp h).2
    have : C.length = 0 := by rw [hC]; rfl
    simp only [C, List.length_drop] at this
    omega
  have hneq := wordMean_ne_full_of_partition a ha A B C (hfull.symm ▸ hw) hB hAC
  rw [hfull] at hneq
  intro heq
  apply hneq
  have hsumAB : wordSum a (A ++ B) = wordSum a A + wordSum a B := by
    simp [wordSum]
  have hb := wordSum_eq_length_mul_mean a B hB
  have hbp : 0 < (B.length : ℝ) := by
    rw [hBlength]
    exact_mod_cast (Nat.sub_pos_of_lt hij)
  have hcast : (j : ℝ) = (i : ℝ) + (B.length : ℝ) := by
    rw [hBlength, Nat.cast_sub hij.le]
    ring
  change wordSum a A - (i : ℝ) * wordMean a w =
    wordSum a (w.take j) - (j : ℝ) * wordMean a w at heq
  rw [← hpre, hsumAB, hcast] at heq
  nlinarith

private theorem centeredPrefix_injective {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) (w : List (Fin n)) (hw : w.Nodup) :
    Function.Injective (fun j : Fin w.length => centeredPrefix a w j.val) := by
  intro i j heq
  by_contra hne
  have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hij | hji
  · exact centeredPrefix_ne a ha w hw i.val j.val hij j.is_lt heq
  · exact centeredPrefix_ne a ha w hw j.val i.val hji i.is_lt heq.symm

private theorem wordSum_take_drop {n : ℕ} (a : Shao.Path n)
    (w : List (Fin n)) (r j : ℕ) :
    wordSum a ((w.drop r).take j) =
      wordSum a (w.take (r + j)) - wordSum a (w.take r) := by
  have ht : w.take (r + j) = w.take r ++ (w.drop r).take j := List.take_add
  have hs := congrArg (wordSum a) ht
  simp only [wordSum, List.map_append, List.sum_append] at hs ⊢
  linarith

private theorem rotateWord_length {α : Type*} (w : List α) (r : ℕ)
    (hr : r ≤ w.length) : (rotateWord w r).length = w.length := by
  simp only [rotateWord, List.length_append, List.length_drop, List.length_take,
    Nat.min_eq_left hr]
  omega

private theorem wordMean_rotateWord {n : ℕ} (a : Shao.Path n)
    (w : List (Fin n)) (r : ℕ) (hr : r ≤ w.length) :
    wordMean a (rotateWord w r) = wordMean a w := by
  have hs := congrArg (wordSum a) (List.take_append_drop r w)
  have hsum : wordSum a (rotateWord w r) = wordSum a w := by
    simp only [wordSum, rotateWord, List.map_append, List.sum_append] at hs ⊢
    linarith
  rw [wordMean, hsum, rotateWord_length w r hr]
  rfl

private theorem centeredPrefix_rotateWord {n : ℕ} (a : Shao.Path n)
    (w : List (Fin n)) (r j : ℕ) (hr : r < w.length) (hj : j < w.length) :
    centeredPrefix a (rotateWord w r) j =
      if r + j < w.length then
        centeredPrefix a w (r + j) - centeredPrefix a w r
      else centeredPrefix a w (r + j - w.length) - centeredPrefix a w r := by
  have hm := wordMean_rotateWord a w r hr.le
  by_cases hcase : r + j < w.length
  · rw [ite_eq_left hcase]
    have hsub : j - (w.length - r) = 0 := by omega
    have ht : (rotateWord w r).take j = (w.drop r).take j := by
      simp only [rotateWord, List.take_append, List.length_drop, hsub,
        List.take_zero, List.append_nil]
    unfold centeredPrefix
    rw [ht, wordSum_take_drop, hm]
    simp only [Nat.cast_add]
    ring
  · rw [ite_eq_right hcase]
    have hdrop : (w.drop r).length ≤ j := by simp only [List.length_drop]; omega
    have hrem : j - (w.length - r) = r + j - w.length := by omega
    have hremle : r + j - w.length ≤ r := by omega
    have ht : (rotateWord w r).take j =
        w.drop r ++ w.take (r + j - w.length) := by
      simp only [rotateWord, List.take_append, List.take_of_length_le hdrop,
        List.length_drop, List.take_take, hrem, Nat.min_eq_left hremle]
    have htotal : wordSum a w = (w.length : ℝ) * wordMean a w :=
      wordSum_eq_length_mul_mean a w (by intro h; simp [h] at hr)
    have hsplit := congrArg (wordSum a) (List.take_append_drop r w)
    simp only [wordSum, List.map_append, List.sum_append] at hsplit
    have hcast : (r : ℝ) + (j : ℝ) =
        (w.length : ℝ) + ((r + j - w.length : ℕ) : ℝ) := by
      have hnat : r + j = w.length + (r + j - w.length) := by omega
      exact_mod_cast hnat
    have hcastMul := congrArg (fun t : ℝ => t * wordMean a w) hcast
    unfold centeredPrefix
    rw [ht, hm]
    simp only [wordSum, List.map_append, List.sum_append] at htotal ⊢
    nlinarith only [htotal, hsplit, hcastMul]

theorem exists_unique_rotation_strictBelowChord {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) (w : List (Fin n))
    (hw : w.Nodup) (hne : w ≠ []) :
    ∃! r : Fin w.length, StrictBelowChord a (rotateWord w r.val) := by
  classical
  have hk : 0 < w.length := by
    cases w with
    | nil => exact False.elim (hne rfl)
    | cons i w => simp
  obtain ⟨r, _, hr⟩ := Finset.exists_max_image Finset.univ
    (fun q : Fin w.length => centeredPrefix a w q.val)
    (show (Finset.univ : Finset (Fin w.length)).Nonempty from ⟨⟨0, hk⟩, by simp⟩)
  have hmax (q : Fin w.length) : centeredPrefix a w q.val ≤ centeredPrefix a w r.val :=
    hr q (Finset.mem_univ _)
  have hinj := centeredPrefix_injective a ha w hw
  have hstrict (q : Fin w.length) (hqr : q ≠ r) :
      centeredPrefix a w q.val < centeredPrefix a w r.val :=
    lt_of_le_of_ne (hmax q) (fun h => hqr (hinj h))
  refine ⟨r, ?_, ?_⟩
  · constructor
    · intro he
      have hl := rotateWord_length w r.val r.is_lt.le
      rw [he] at hl
      simp only [List.length_nil] at hl
      omega
    · intro j hj0 hj
      rw [rotateWord_length w r.val r.is_lt.le] at hj
      have hc : centeredPrefix a (rotateWord w r.val) j < 0 := by
        rw [centeredPrefix_rotateWord a w r.val j r.is_lt hj]
        split_ifs with hcase
        · let q : Fin w.length := ⟨r.val + j, hcase⟩
          have hqr : q ≠ r := by intro h; have := congrArg Fin.val h; dsimp [q] at this; omega
          exact sub_neg.mpr (hstrict q hqr)
        · let q : Fin w.length := ⟨r.val + j - w.length, by omega⟩
          have hqr : q ≠ r := by intro h; have := congrArg Fin.val h; dsimp [q] at this; omega
          exact sub_neg.mpr (hstrict q hqr)
      exact sub_neg.mp hc
  · intro q hq
    by_contra hqr
    have hv : q.val ≠ r.val := fun h => hqr (Fin.ext h)
    rcases lt_or_gt_of_ne hv with hlt | hgt
    · let j := r.val - q.val
      have hj0 : 0 < j := by dsimp [j]; omega
      have hj : j < w.length := by dsimp [j]; omega
      have hjrot : j < (rotateWord w q.val).length := by
        rw [rotateWord_length w q.val q.is_lt.le]; exact hj
      have hc : centeredPrefix a (rotateWord w q.val) j < 0 :=
        sub_neg.mpr (hq.2 j hj0 hjrot)
      rw [centeredPrefix_rotateWord a w q.val j q.is_lt hj,
        ite_eq_left (by dsimp [j]; omega), show q.val + j = r.val by dsimp [j]; omega] at hc
      linarith [hmax q]
    · let j := w.length + r.val - q.val
      have hj0 : 0 < j := by dsimp [j]; omega
      have hj : j < w.length := by dsimp [j]; omega
      have hjrot : j < (rotateWord w q.val).length := by
        rw [rotateWord_length w q.val q.is_lt.le]; exact hj
      have hc : centeredPrefix a (rotateWord w q.val) j < 0 :=
        sub_neg.mpr (hq.2 j hj0 hjrot)
      rw [centeredPrefix_rotateWord a w q.val j q.is_lt hj,
        ite_eq_right (by dsimp [j]; omega),
        show q.val + j - w.length = r.val by dsimp [j]; omega] at hc
      linarith [hmax q]

private theorem properPrefixMean_ne {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) (w : List (Fin n)) (hw : w.Nodup)
    (k : ℕ) (hk0 : 0 < k) (hk : k < w.length) :
    wordMean a (w.take k) ≠ wordMean a w := by
  have htake : w.take k ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp only [List.length_take, Nat.min_eq_left hk.le, List.length_nil] at hlen
    omega
  have hdrop : w.drop k ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp only [List.length_drop, List.length_nil] at hlen
    omega
  have hfull : [] ++ w.take k ++ w.drop k = w := by
    simp only [List.nil_append, List.take_append_drop]
  have hnd : ([] ++ w.take k ++ w.drop k).Nodup := hfull.symm ▸ hw
  have hneq := wordMean_ne_full_of_partition a ha [] (w.take k) (w.drop k)
    hnd htake (by simpa only [List.nil_append] using hdrop)
  simpa only [hfull] using hneq

private theorem prefixMeans_ne {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) (w : List (Fin n)) (hw : w.Nodup)
    (i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ w.length) :
    wordMean a (w.take i) ≠ wordMean a (w.take j) := by
  have hlen : (w.take j).length = j := by simp [List.length_take, Nat.min_eq_left hj]
  have hneq := properPrefixMean_ne a ha (w.take j)
    (show (w.take j).Nodup from hw.take) i hi
    (by rw [hlen]; exact hij)
  simpa only [List.take_take, Nat.min_eq_left hij.le] using hneq

private theorem exists_greedy_first_face {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) (w : List (Fin n))
    (hw : w.Nodup) (hne : w ≠ []) :
    ∃ k : ℕ, 0 < k ∧ k ≤ w.length ∧ StrictBelowChord a (w.take k) ∧
      (∀ j : ℕ, 0 < j → j ≤ w.length → j ≠ k →
        wordMean a (w.take j) < wordMean a (w.take k)) ∧
      (∀ j : ℕ, 0 < j → j ≤ (w.drop k).length →
        wordMean a ((w.drop k).take j) < wordMean a (w.take k)) := by
  classical
  have hwpos : 0 < w.length := by
    cases w with
    | nil => exact False.elim (hne rfl)
    | cons i w => simp
  obtain ⟨r, _, hr⟩ := Finset.exists_max_image Finset.univ
    (fun q : Fin w.length => wordMean a (w.take (q.val + 1)))
    (show (Finset.univ : Finset (Fin w.length)).Nonempty from ⟨⟨0, hwpos⟩, by simp⟩)
  let k := r.val + 1
  have hk0 : 0 < k := by dsimp [k]; omega
  have hk : k ≤ w.length := by dsimp [k]; omega
  have hlenk : (w.take k).length = k := by simp [List.length_take, Nat.min_eq_left hk]
  have htake : w.take k ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    rw [hlenk] at hlen
    simp only [List.length_nil] at hlen
    omega
  have hmax (j : ℕ) (hj0 : 0 < j) (hj : j ≤ w.length) :
      wordMean a (w.take j) ≤ wordMean a (w.take k) := by
    let q : Fin w.length := ⟨j - 1, by omega⟩
    have hq : q.val + 1 = j := by dsimp [q]; omega
    have hh := hr q (Finset.mem_univ _)
    simpa only [hq] using hh
  have hbest (j : ℕ) (hj0 : 0 < j) (hj : j ≤ w.length) (hjk : j ≠ k) :
      wordMean a (w.take j) < wordMean a (w.take k) := by
    have hneq : wordMean a (w.take j) ≠ wordMean a (w.take k) := by
      rcases lt_or_gt_of_ne hjk with hjk | hkj
      · exact prefixMeans_ne a ha w hw j k hj0 hjk hk
      · exact (prefixMeans_ne a ha w hw k j hk0 hkj hj).symm
    exact lt_of_le_of_ne (hmax j hj0 hj) hneq
  refine ⟨k, hk0, hk, ⟨htake, ?_⟩, hbest, ?_⟩
  · intro j hj0 hjk
    rw [hlenk] at hjk
    have hj : j ≤ w.length := hjk.le.trans hk
    have hlenj : (w.take j).length = j := by simp [List.length_take, Nat.min_eq_left hj]
    have htakej : w.take j ≠ [] := by
      intro h
      have hh := congrArg List.length h
      rw [hlenj] at hh
      simp only [List.length_nil] at hh
      omega
    have hs := wordSum_eq_length_mul_mean a (w.take j) htakej
    rw [hlenj] at hs
    rw [List.take_take, Nat.min_eq_left hjk.le, hs]
    exact mul_lt_mul_of_pos_left (hbest j hj0 hj (by omega)) (by exact_mod_cast hj0)
  · intro j hj0 hj
    have hjlen : j ≤ w.length - k := by simpa only [List.length_drop] using hj
    have hkj : k + j ≤ w.length := by omega
    have hmean := hbest (k + j) (by omega) hkj (by omega)
    have hlenj : ((w.drop k).take j).length = j := by
      simp only [List.length_take, List.length_drop, Nat.min_eq_left hjlen]
    have hneqj : (w.drop k).take j ≠ [] := by
      intro h
      have hh := congrArg List.length h
      rw [hlenj] at hh
      simp only [List.length_nil] at hh
      omega
    have hneqkj : w.take (k + j) ≠ [] := by
      intro h
      have hh := congrArg List.length h
      simp only [List.length_take, Nat.min_eq_left hkj, List.length_nil] at hh
      omega
    have hsu := wordSum_eq_length_mul_mean a (w.take k) htake
    rw [hlenk] at hsu
    have hsv := wordSum_eq_length_mul_mean a ((w.drop k).take j) hneqj
    rw [hlenj] at hsv
    have hsw := wordSum_eq_length_mul_mean a (w.take (k + j)) hneqkj
    simp only [List.length_take, Nat.min_eq_left hkj, Nat.cast_add] at hsw
    have ht : w.take (k + j) = w.take k ++ (w.drop k).take j := List.take_add
    have hsum := congrArg (wordSum a) ht
    simp only [wordSum, List.map_append, List.sum_append] at hsum
    have hmul := mul_lt_mul_of_pos_left hmean
      (show (0 : ℝ) < (k : ℝ) + (j : ℝ) by positivity)
    have hjpos : (0 : ℝ) < j := by exact_mod_cast hj0
    simp only [wordSum] at hsu hsv hsw
    have hjl : (j : ℝ) * wordMean a ((w.drop k).take j) <
        (j : ℝ) * wordMean a (w.take k) := by
      nlinarith only [hsu, hsv, hsw, hsum, hmul]
    exact lt_of_not_ge (fun h => (not_le_of_gt hjl)
      (mul_le_mul_of_nonneg_left h hjpos.le))

private def WordFaces {n : ℕ} (a : Shao.Path n) (w : List (Fin n))
    (B : List (List (Fin n))) : Prop :=
  B.flatten = w ∧ (∀ b ∈ B, StrictBelowChord a b) ∧
    B.Pairwise (fun u v => wordMean a v < wordMean a u)

private theorem wordFaces_first_prefix {n : ℕ} (a : Shao.Path n)
    (w b : List (Fin n)) (B : List (List (Fin n))) (h : WordFaces a w (b :: B)) :
    w.take b.length = b ∧ b.length ≤ w.length := by
  have hf : b ++ B.flatten = w := h.1
  rw [← hf]
  constructor
  · simp
  · simp only [List.length_append]; omega

private theorem exists_wordFaces {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) (w : List (Fin n)) (hw : w.Nodup) :
    ∃ B : List (List (Fin n)), WordFaces a w B := by
  classical
  have main : ∀ m : ℕ, ∀ w : List (Fin n), w.length = m → w.Nodup →
      ∃ B : List (List (Fin n)), WordFaces a w B := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro w hlen hw
      by_cases hnil : w = []
      · subst w
        exact ⟨[], by simp [WordFaces]⟩
      obtain ⟨k, hk0, hk, hhead, _, htail⟩ := exists_greedy_first_face a ha w hw hnil
      have hdropLt : (w.drop k).length < m := by
        simp only [List.length_drop]
        omega
      obtain ⟨B, hB⟩ := ih (w.drop k).length hdropLt (w.drop k) rfl
        (show (w.drop k).Nodup from hw.drop)
      have hrel : ∀ b ∈ B, wordMean a b < wordMean a (w.take k) := by
        cases hbc : B with
        | nil => simp [hbc]
        | cons b bs =>
          have hB' : WordFaces a (w.drop k) (b :: bs) := hbc ▸ hB
          have hnonempty := (hB'.2.1 b (by simp)).1
          have hpos : 0 < b.length := by
            cases b with
            | nil => exact False.elim (hnonempty rfl)
            | cons i b => simp
          have hpref := wordFaces_first_prefix a (w.drop k) b bs hB'
          have hfirst := htail b.length hpos hpref.2
          rw [hpref.1] at hfirst
          intro c hc
          simp only [hbc, List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact hfirst
          · exact ((List.pairwise_cons.mp hB'.2.2).1 c hc).trans hfirst
      refine ⟨w.take k :: B, ?_, ?_, ?_⟩
      · rw [List.flatten_cons, hB.1]
        exact List.take_append_drop k w
      · intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact hhead
        · exact hB.2.1 b hb
      · exact List.pairwise_cons.mpr ⟨hrel, hB.2.2⟩
  exact main w.length w rfl hw

private theorem wordFaces_prefix_lt {n : ℕ} (a : Shao.Path n) (μ : ℝ)
    (B : List (List (Fin n))) (hbelow : ∀ b ∈ B, StrictBelowChord a b)
    (hmean : ∀ b ∈ B, wordMean a b < μ) :
    ∀ j : ℕ, 0 < j → j ≤ B.flatten.length →
      wordSum a (B.flatten.take j) < (j : ℝ) * μ := by
  induction B with
  | nil => intro j hj0 hj; simp only [List.flatten_nil, List.length_nil] at hj; omega
  | cons b B ih =>
    intro j hj0 hj
    have hb := hbelow b (by simp)
    have hbmean := hmean b (by simp)
    have hbelowB : ∀ c ∈ B, StrictBelowChord a c := fun c hc => hbelow c (by simp [hc])
    have hmeanB : ∀ c ∈ B, wordMean a c < μ := fun c hc => hmean c (by simp [hc])
    have hjpos : (0 : ℝ) < j := by exact_mod_cast hj0
    by_cases hjb : j ≤ b.length
    · have hzero : j - b.length = 0 := by omega
      have ht : (b ++ B.flatten).take j = b.take j := by
        simp only [List.take_append, hzero, List.take_zero, List.append_nil]
      rw [List.flatten_cons, ht]
      have hpre : wordSum a (b.take j) ≤ (j : ℝ) * wordMean a b := by
        rcases lt_or_eq_of_le hjb with hlt | rfl
        · exact (hb.2 j hj0 hlt).le
        · rw [List.take_length]
          exact (wordSum_eq_length_mul_mean a b hb.1).le
      exact hpre.trans_lt (mul_lt_mul_of_pos_left hbmean hjpos)
    · have hbpos : 0 < b.length := by
        cases b with
        | nil => exact False.elim (hb.1 rfl)
        | cons i b => simp
      have hjtail : 0 < j - b.length := by omega
      have hjtaille : j - b.length ≤ B.flatten.length := by
        simp only [List.flatten_cons, List.length_append] at hj
        omega
      have htail := ih hbelowB hmeanB (j - b.length) hjtail hjtaille
      have ht : (b ++ B.flatten).take j = b ++ B.flatten.take (j - b.length) := by
        simp only [List.take_append, List.take_of_length_le (by omega : b.length ≤ j)]
      have hbfull := wordSum_eq_length_mul_mean a b hb.1
      have hblt := mul_lt_mul_of_pos_left hbmean (show (0 : ℝ) < b.length by exact_mod_cast hbpos)
      rw [List.flatten_cons, ht]
      simp only [wordSum, List.map_append, List.sum_append] at hbfull htail ⊢
      rw [Nat.cast_sub (by omega : b.length ≤ j)] at htail
      nlinarith only [hbfull, htail, hblt]

private theorem wordFaces_first_best {n : ℕ} (a : Shao.Path n)
    (w b : List (Fin n)) (B : List (List (Fin n))) (h : WordFaces a w (b :: B))
    (j : ℕ) (hj0 : 0 < j) (hj : j ≤ w.length) (hjb : j ≠ b.length) :
    wordMean a (w.take j) < wordMean a b := by
  have hb := h.2.1 b (by simp)
  have hrel : ∀ c ∈ B, wordMean a c < wordMean a b :=
    (List.pairwise_cons.mp h.2.2).1
  have hbelow : ∀ c ∈ B, StrictBelowChord a c := fun c hc => h.2.1 c (by simp [hc])
  have hf : b ++ B.flatten = w := h.1
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj0
  have hbound : wordSum a (w.take j) < (j : ℝ) * wordMean a b := by
    by_cases hlt : j < b.length
    · rw [← hf]
      have hzero : j - b.length = 0 := by omega
      simpa only [List.take_append, hzero, List.take_zero, List.append_nil] using hb.2 j hj0 hlt
    · have hjtail : 0 < j - b.length := by omega
      have hjtaille : j - b.length ≤ B.flatten.length := by
        rw [← hf, List.length_append] at hj
        omega
      have htail := wordFaces_prefix_lt a (wordMean a b) B hbelow hrel
        (j - b.length) hjtail hjtaille
      have hbfull := wordSum_eq_length_mul_mean a b hb.1
      have ht : (b ++ B.flatten).take j = b ++ B.flatten.take (j - b.length) := by
        simp only [List.take_append, List.take_of_length_le (by omega : b.length ≤ j)]
      rw [← hf, ht]
      simp only [wordSum, List.map_append, List.sum_append] at hbfull htail ⊢
      rw [Nat.cast_sub (by omega : b.length ≤ j)] at htail
      nlinarith only [hbfull, htail]
  unfold wordMean
  rw [List.length_take, Nat.min_eq_left hj]
  apply (div_lt_iff₀ hjpos).mpr
  simpa only [wordMean, mul_comm] using hbound

private theorem wordFaces_empty {n : ℕ} (a : Shao.Path n)
    (B : List (List (Fin n))) (hB : WordFaces a [] B) : B = [] := by
  cases B with
  | nil => rfl
  | cons b B =>
    have hb := (hB.2.1 b (by simp)).1
    have hf : b ++ B.flatten = [] := hB.1
    exact False.elim (hb (List.append_eq_nil_iff.mp hf).1)

private theorem wordFaces_unique {n : ℕ} (a : Shao.Path n)
    (w : List (Fin n)) (B C : List (List (Fin n)))
    (hB : WordFaces a w B) (hC : WordFaces a w C) : B = C := by
  induction B generalizing w C with
  | nil =>
    have hw : w = [] := by simpa only [List.flatten_nil] using hB.1.symm
    subst w
    exact (wordFaces_empty a C hC).symm
  | cons b B ih =>
    cases C with
    | nil =>
      have hw : w = [] := by simpa only [List.flatten_nil] using hC.1.symm
      subst w
      have hh := wordFaces_empty a (b :: B) hB
      cases hh
    | cons c C =>
      have hbn := (hB.2.1 b (by simp)).1
      have hcn := (hC.2.1 c (by simp)).1
      have hbp : 0 < b.length := by
        cases b with
        | nil => exact False.elim (hbn rfl)
        | cons i b => simp
      have hcp : 0 < c.length := by
        cases c with
        | nil => exact False.elim (hcn rfl)
        | cons i c => simp
      have hpB := wordFaces_first_prefix a w b B hB
      have hpC := wordFaces_first_prefix a w c C hC
      have hlen : b.length = c.length := by
        by_contra hne
        have hbc := wordFaces_first_best a w b B hB c.length hcp hpC.2 (fun h => hne h.symm)
        have hcb := wordFaces_first_best a w c C hC b.length hbp hpB.2 hne
        rw [hpC.1] at hbc
        rw [hpB.1] at hcb
        exact lt_asymm hbc hcb
      have hbc : b = c := by
        rw [hlen] at hpB
        exact hpB.1.symm.trans hpC.1
      subst c
      have hf : B.flatten = C.flatten := by
        have hh : b ++ B.flatten = b ++ C.flatten := hB.1.trans hC.1.symm
        simpa using congrArg (fun t : List (Fin n) => t.drop b.length) hh
      have hBt : WordFaces a B.flatten B :=
        ⟨rfl, fun v hv => hB.2.1 v (by simp [hv]), (List.pairwise_cons.mp hB.2.2).2⟩
      have hCt : WordFaces a B.flatten C :=
        ⟨hf.symm, fun v hv => hC.2.1 v (by simp [hv]), (List.pairwise_cons.mp hC.2.2).2⟩
      exact congrArg (List.cons b) (ih B.flatten C hBt hCt)

theorem exists_unique_faceDecomposition {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) (σ : Equiv.Perm (Fin n)) :
    ∃! B : List (List (Fin n)), FaceDecomposition a σ B := by
  let w := List.ofFn (fun i : Fin n => σ i)
  have hw : w.Nodup := List.nodup_ofFn.mpr σ.injective
  obtain ⟨B, hB⟩ := exists_wordFaces a ha w hw
  refine ⟨B, hB, ?_⟩
  intro C hC
  exact wordFaces_unique a w C B hC hB

private def positiveBlockTotal {n : ℕ} (a : Shao.Path n) : List (List (Fin n)) → ℝ
  | [] => 0
  | b :: B => max (wordSum a b) 0 + positiveBlockTotal a B

private theorem positiveBlockTotal_nonneg {n : ℕ} (a : Shao.Path n)
    (B : List (List (Fin n))) : 0 ≤ positiveBlockTotal a B := by
  induction B with
  | nil => exact le_rfl
  | cons b B ih => exact add_nonneg (le_max_right _ _) ih

private theorem positiveBlockTotal_eq_zero {n : ℕ} (a : Shao.Path n)
    (B : List (List (Fin n))) (h : ∀ b ∈ B, wordSum a b ≤ 0) :
    positiveBlockTotal a B = 0 := by
  induction B with
  | nil => rfl
  | cons b B ih =>
    simp only [positiveBlockTotal, max_eq_right (h b (by simp)), zero_add]
    exact ih fun c hc => h c (by simp [hc])

private theorem strictBelowChord_prefix_le {n : ℕ} (a : Shao.Path n)
    (b : List (Fin n)) (hb : StrictBelowChord a b) (j : ℕ) (hj : j ≤ b.length) :
    wordSum a (b.take j) ≤ max (wordSum a b) 0 := by
  by_cases hj0 : j = 0
  · simp [hj0, wordSum, le_max_right]
  by_cases hje : j = b.length
  · simp only [hje, List.take_length]
    exact le_max_left _ _
  have hjp : 0 < j := by omega
  have hpre := (hb.2 j hjp (by omega)).le
  have hfull := wordSum_eq_length_mul_mean a b hb.1
  by_cases hm : 0 ≤ wordMean a b
  · have hbound : (j : ℝ) * wordMean a b ≤ (b.length : ℝ) * wordMean a b :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hm
    exact hpre.trans (hbound.trans (hfull ▸ le_max_left _ _))
  · have hbound : (j : ℝ) * wordMean a b ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_le.mp hm).le
    exact hpre.trans (hbound.trans (le_max_right _ _))

private theorem wordFaces_maximum_spec {n : ℕ} (a : Shao.Path n)
    (w : List (Fin n)) (B : List (List (Fin n))) (h : WordFaces a w B) :
    (∀ j : ℕ, j ≤ w.length → wordSum a (w.take j) ≤ positiveBlockTotal a B) ∧
      ∃ j : ℕ, j ≤ w.length ∧ wordSum a (w.take j) = positiveBlockTotal a B := by
  induction B generalizing w with
  | nil =>
    have hw : w = [] := by simpa only [List.flatten_nil] using h.1.symm
    subst w
    exact ⟨by simp [wordSum, positiveBlockTotal], 0, by simp, by simp [wordSum, positiveBlockTotal]⟩
  | cons b B ih =>
    have hb := h.2.1 b (by simp)
    have hBt : WordFaces a B.flatten B :=
      ⟨rfl, fun v hv => h.2.1 v (by simp [hv]), (List.pairwise_cons.mp h.2.2).2⟩
    obtain ⟨hboundB, j, hj, hjeq⟩ := ih B.flatten hBt
    have hf : b ++ B.flatten = w := h.1
    by_cases hbpos : 0 < wordSum a b
    · have hpositive : positiveBlockTotal a (b :: B) =
          wordSum a b + positiveBlockTotal a B := by
        simp only [positiveBlockTotal, max_eq_left hbpos.le]
      constructor
      · intro k hk
        rw [hpositive, ← hf]
        by_cases hkb : k ≤ b.length
        · have ht : (b ++ B.flatten).take k = b.take k := by
            simp only [List.take_append, Nat.sub_eq_zero_of_le hkb, List.take_zero, List.append_nil]
          rw [ht]
          have hh := strictBelowChord_prefix_le a b hb k hkb
          rw [max_eq_left hbpos.le] at hh
          linarith [positiveBlockTotal_nonneg a B]
        · have htaille : k - b.length ≤ B.flatten.length := by
            rw [← hf, List.length_append] at hk
            omega
          have ht : (b ++ B.flatten).take k = b ++ B.flatten.take (k - b.length) := by
            simp only [List.take_append, List.take_of_length_le (by omega : b.length ≤ k)]
          rw [ht]
          have hh := hboundB (k - b.length) htaille
          simp only [wordSum, List.map_append, List.sum_append] at hh ⊢
          linarith
      · refine ⟨b.length + j, ?_, ?_⟩
        · rw [← hf, List.length_append]
          omega
        · rw [hpositive, ← hf, List.take_append]
          simp only [List.take_of_length_le (by omega : b.length ≤ b.length + j),
            Nat.add_sub_cancel_left, wordSum, List.map_append, List.sum_append] at hjeq ⊢
          linarith
    · have hbnonpos : wordSum a b ≤ 0 := (not_lt.mp hbpos)
      have hbmean : wordMean a b ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg hbnonpos (by positivity)
      have htailmean : ∀ c ∈ B, wordMean a c < 0 := by
        intro c hc
        exact ((List.pairwise_cons.mp h.2.2).1 c hc).trans_le hbmean
      have htailnonpos : ∀ c ∈ B, wordSum a c ≤ 0 := by
        intro c hc
        rw [wordSum_eq_length_mul_mean a c (hBt.2.1 c hc).1]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (htailmean c hc).le
      have hzero : positiveBlockTotal a (b :: B) = 0 := by
        rw [positiveBlockTotal, max_eq_right hbnonpos, positiveBlockTotal_eq_zero a B htailnonpos]
        simp
      constructor
      · intro k hk
        rw [hzero, ← hf]
        by_cases hkb : k ≤ b.length
        · have ht : (b ++ B.flatten).take k = b.take k := by
            simp only [List.take_append, Nat.sub_eq_zero_of_le hkb, List.take_zero, List.append_nil]
          rw [ht]
          simpa only [max_eq_right hbnonpos] using strictBelowChord_prefix_le a b hb k hkb
        · have htailpos : 0 < k - b.length := by omega
          have htaille : k - b.length ≤ B.flatten.length := by
            rw [← hf, List.length_append] at hk
            omega
          have hh := wordFaces_prefix_lt a 0 B hBt.2.1 htailmean
            (k - b.length) htailpos htaille
          have ht : (b ++ B.flatten).take k = b ++ B.flatten.take (k - b.length) := by
            simp only [List.take_append, List.take_of_length_le (by omega : b.length ≤ k)]
          rw [ht]
          simp only [wordSum, List.map_append, List.sum_append] at hh hbnonpos ⊢
          linarith
      · exact ⟨0, Nat.zero_le _, by simp [wordSum, hzero]⟩

private theorem wordSum_ofFn_prefix {n : ℕ} (a : Shao.Path n)
    (σ : Equiv.Perm (Fin n)) (j : ℕ) :
    wordSum a ((List.ofFn (fun i : Fin n => σ i)).take j) =
      Shao.prefixSum (reorder a σ) j := by
  unfold wordSum
  rw [List.map_take, List.map_ofFn, List.sum_take_ofFn]
  rfl

private theorem maximum_eq_positiveBlockTotal {n : ℕ} (a : Shao.Path n)
    (σ : Equiv.Perm (Fin n)) (B : List (List (Fin n))) (h : FaceDecomposition a σ B) :
    Shao.maxWithZero (reorder a σ) = positiveBlockTotal a B := by
  obtain ⟨hbound, j, hj, hjeq⟩ := wordFaces_maximum_spec a
    (List.ofFn (fun i : Fin n => σ i)) B h
  have hlen : (List.ofFn (fun i : Fin n => σ i)).length = n := List.length_ofFn
  apply le_antisymm
  · apply (Shao.maxWithZero_le_iff _ _).mpr
    intro k hk
    rw [← wordSum_ofFn_prefix a σ k]
    exact hbound k (hlen.symm ▸ hk)
  · have hjn : j ≤ n := hlen ▸ hj
    have hm := (Shao.maxWithZero_le_iff (reorder a σ) _).mp le_rfl j hjn
    rw [← wordSum_ofFn_prefix a σ j, hjeq] at hm
    exact hm

private theorem tail_ofFn {n : ℕ} (a : Shao.Path n) (k : ℕ) (hk : k ≤ n) :
    List.ofFn (tail a k hk) = (List.ofFn a).drop k := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_drop]
  · intro i hi hi'
    simp [tail]

private theorem tail_prefixSum_ofFn {n : ℕ} (a : Shao.Path n)
    (σ : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n) (j : ℕ) :
    Shao.prefixSum (tail (reorder a σ) k hk) j =
      wordSum a (((List.ofFn (fun i : Fin n => σ i)).drop k).take j) := by
  change (∑ i : Fin (n - k) with i.val < j, tail (reorder a σ) k hk i) = _
  rw [← List.sum_take_ofFn, tail_ofFn]
  simp only [wordSum, List.map_take, List.map_drop, List.map_ofFn]
  rfl

private theorem tail_maximum_eq_positiveBlockTotal {n : ℕ} (a : Shao.Path n)
    (σ : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n)
    (B : List (List (Fin n)))
    (h : WordFaces a ((List.ofFn (fun i : Fin n => σ i)).drop k) B) :
    Shao.maxWithZero (tail (reorder a σ) k hk) = positiveBlockTotal a B := by
  obtain ⟨hbound, j, hj, hjeq⟩ := wordFaces_maximum_spec a
    ((List.ofFn (fun i : Fin n => σ i)).drop k) B h
  have hlen : ((List.ofFn (fun i : Fin n => σ i)).drop k).length = n - k := by simp
  apply le_antisymm
  · apply (Shao.maxWithZero_le_iff _ _).mpr
    intro r hr
    rw [tail_prefixSum_ofFn]
    exact hbound r (hlen.symm ▸ hr)
  · have hjn : j ≤ n - k := hlen ▸ hj
    have hm := (Shao.maxWithZero_le_iff (tail (reorder a σ) k hk) _).mp le_rfl j hjn
    rw [tail_prefixSum_ofFn, hjeq] at hm
    exact hm

private theorem wordFaces_delete_block {n : ℕ} (a : Shao.Path n)
    (w : List (Fin n)) (A D : List (List (Fin n))) (b : List (Fin n))
    (h : WordFaces a w (A ++ b :: D)) :
    WordFaces a (A ++ D).flatten (A ++ D) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro c hc
    apply h.2.1 c
    simp only [List.mem_append] at hc ⊢
    rcases hc with hc | hc
    · exact Or.inl hc
    · exact Or.inr (by simp [hc])
  · obtain ⟨hA, hBD, hcross⟩ := List.pairwise_append.mp h.2.2
    apply List.pairwise_append.mpr
    refine ⟨hA, (List.pairwise_cons.mp hBD).2, ?_⟩
    intro c hc d hd
    exact hcross c hc d (by simp [hd])

private theorem positiveBlockTotal_append {n : ℕ} (a : Shao.Path n)
    (A D : List (List (Fin n))) :
    positiveBlockTotal a (A ++ D) = positiveBlockTotal a A + positiveBlockTotal a D := by
  induction A with
  | nil => simp [positiveBlockTotal]
  | cons b A ih => simp only [List.cons_append, positiveBlockTotal, ih, add_assoc]

private theorem wordSum_rotateWord {n : ℕ} (a : Shao.Path n)
    (b : List (Fin n)) (r : ℕ) : wordSum a (rotateWord b r) = wordSum a b := by
  have hs := congrArg (wordSum a) (List.take_append_drop r b)
  simp only [wordSum, rotateWord, List.map_append, List.sum_append] at hs ⊢
  linarith

private theorem cut_maximum_of_face_block {n : ℕ} (a : Shao.Path n)
    (σ τ : Equiv.Perm (Fin n)) (A D : List (List (Fin n))) (b : List (Fin n))
    (r : ℕ) (hr : r ≤ b.length)
    (hσ : FaceDecomposition a σ (A ++ b :: D))
    (hτ : List.ofFn (fun i : Fin n => τ i) = rotateWord b r ++ (A ++ D).flatten) :
    ∃ hk : b.length ≤ n,
      Shao.maxWithZero (reorder a σ) =
        max (Shao.prefixSum (reorder a τ) b.length) 0 +
          Shao.maxWithZero (tail (reorder a τ) b.length hk) := by
  have hrotlen := rotateWord_length b r hr
  have hk : b.length ≤ n := by
    have hh := congrArg List.length hτ
    simp only [List.length_ofFn, List.length_append, hrotlen] at hh
    omega
  refine ⟨hk, ?_⟩
  have hτtail : ((List.ofFn (fun i : Fin n => τ i)).drop b.length) = (A ++ D).flatten := by
    rw [hτ, ← hrotlen]
    simp
  have hτhead : (List.ofFn (fun i : Fin n => τ i)).take b.length = rotateWord b r := by
    rw [hτ, ← hrotlen]
    simp
  have hdelete := wordFaces_delete_block a (List.ofFn (fun i : Fin n => σ i)) A D b hσ
  have htail : Shao.maxWithZero (tail (reorder a τ) b.length hk) =
      positiveBlockTotal a (A ++ D) := by
    apply tail_maximum_eq_positiveBlockTotal a τ b.length hk
    rw [hτtail]
    exact hdelete
  have hhead : Shao.prefixSum (reorder a τ) b.length = wordSum a b := by
    rw [← wordSum_ofFn_prefix, hτhead, wordSum_rotateWord]
  rw [maximum_eq_positiveBlockTotal a σ (A ++ b :: D) hσ, hhead, htail,
    positiveBlockTotal_append, positiveBlockTotal, positiveBlockTotal_append]
  ring

private def markedSplit {α : Type*} : List (List α) → ℕ →
    List (List α) × List α × List (List α)
  | [], _ => ([], [], [])
  | b :: B, q =>
    if q ≤ b.length then ([], b, B)
    else let s := markedSplit B (q - b.length)
      (b :: s.1, s.2)

private theorem markedSplit_spec {α : Type*} (B : List (List α)) (q : ℕ)
    (hq0 : 0 < q) (hq : q ≤ B.flatten.length) :
    let s := markedSplit B q
    B = s.1 ++ s.2.1 :: s.2.2 ∧
      s.1.flatten.length < q ∧ q ≤ s.1.flatten.length + s.2.1.length := by
  induction B generalizing q with
  | nil => simp only [List.flatten_nil, List.length_nil] at hq; omega
  | cons b B ih =>
    by_cases hb : q ≤ b.length
    · simp only [markedSplit, ite_eq_left hb, List.nil_append, List.flatten_nil,
        List.length_nil, zero_add]
      exact ⟨trivial, hq0, hb⟩
    · have hq' : q - b.length ≤ B.flatten.length := by
        simp only [List.flatten_cons, List.length_append] at hq
        omega
      have hs := ih (q - b.length) (by omega) hq'
      simp only [markedSplit, ite_eq_right hb]
      change b :: B = (b :: (markedSplit B (q - b.length)).1) ++
          (markedSplit B (q - b.length)).2.1 :: (markedSplit B (q - b.length)).2.2 ∧ _
      refine ⟨?_, ?_, ?_⟩
      · simpa only [List.cons_append] using congrArg (List.cons b) hs.1
      · simp only [List.flatten_cons, List.length_append]
        omega
      · simp only [List.flatten_cons, List.length_append]
        omega

private theorem markedSplit_at {α : Type*} (A D : List (List α)) (b : List α)
    (t : ℕ) (ht0 : 0 < t) (ht : t ≤ b.length) :
    markedSplit (A ++ b :: D) (A.flatten.length + t) = (A, b, D) := by
  induction A with
  | nil => simp only [List.nil_append, List.flatten_nil, List.length_nil, zero_add,
      markedSplit, ite_eq_left ht]
  | cons c A ih =>
    simp only [List.cons_append, List.flatten_cons, List.length_append, markedSplit]
    rw [ite_eq_right (by omega : ¬(c.length + A.flatten.length + t ≤ c.length))]
    have heq : c.length + A.flatten.length + t - c.length = A.flatten.length + t := by omega
    rw [heq, ih]

private def canonicalFaces {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) (σ : Equiv.Perm (Fin n)) : List (List (Fin n)) :=
  Classical.choose (exists_unique_faceDecomposition a ha σ)

private theorem canonicalFaces_spec {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) (σ : Equiv.Perm (Fin n)) :
    FaceDecomposition a σ (canonicalFaces a ha σ) :=
  (Classical.choose_spec (exists_unique_faceDecomposition a ha σ)).1

private theorem canonicalFaces_eq {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) (σ : Equiv.Perm (Fin n))
    (B : List (List (Fin n))) (hB : FaceDecomposition a σ B) :
    canonicalFaces a ha σ = B :=
  ((Classical.choose_spec (exists_unique_faceDecomposition a ha σ)).2 B hB).symm

private theorem perm_ofFn_id {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (List.ofFn (fun i : Fin n => σ i)).Perm (List.ofFn (fun i : Fin n => i)) := by
  apply List.perm_iff_count.mpr
  intro i
  have hσmem : i ∈ List.ofFn (fun j : Fin n => σ j) := by
    obtain ⟨j, rfl⟩ := σ.surjective i
    exact List.mem_ofFn.mpr ⟨j, rfl⟩
  have hidmem : i ∈ List.ofFn (fun j : Fin n => j) := List.mem_ofFn.mpr ⟨i, rfl⟩
  have hidnd : (List.ofFn (fun j : Fin n => j)).Nodup :=
    List.nodup_ofFn.mpr (fun _ _ h => h)
  rw [List.count_eq_one_of_mem (List.nodup_ofFn.mpr σ.injective) hσmem,
    List.count_eq_one_of_mem hidnd hidmem]

private def permOfWord {n : ℕ} (w : List (Fin n))
    (hp : w.Perm (List.ofFn (fun i : Fin n => i))) : Equiv.Perm (Fin n) := by
  have hlen : w.length = n := by simpa only [List.length_ofFn] using hp.length_eq
  have hnd : w.Nodup := hp.nodup_iff.mpr (List.nodup_ofFn.mpr Function.injective_id)
  have hmem (i : Fin n) : i ∈ w := hp.mem_iff.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hbij : Function.Bijective w.get := List.get_bijective_iff.mpr
    (fun i => List.count_eq_one_of_mem hnd (hmem i))
  exact (finCongr hlen.symm).trans (Equiv.ofBijective w.get hbij)

private theorem permOfWord_apply {n : ℕ} (w : List (Fin n))
    (hp : w.Perm (List.ofFn (fun i : Fin n => i))) (i : Fin n) :
    permOfWord w hp i = w.get ⟨i.val, by
      have hl : w.length = n := by simpa only [List.length_ofFn] using hp.length_eq
      rw [hl]; exact i.is_lt⟩ := rfl

private theorem ofFn_permOfWord {n : ℕ} (w : List (Fin n))
    (hp : w.Perm (List.ofFn (fun i : Fin n => i))) :
    List.ofFn (fun i : Fin n => permOfWord w hp i) = w := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hp.length_eq.symm
  · intro i hi hi'
    simp only [List.getElem_ofFn, permOfWord_apply, List.get_eq_getElem]

private theorem rotateWord_perm {α : Type*} (b : List α) (r : ℕ) :
    (rotateWord b r).Perm b := by
  have hp : (b.drop r ++ b.take r).Perm (b.take r ++ b.drop r) := List.perm_append_comm
  simpa only [rotateWord, List.take_append_drop] using hp

private theorem cutWord_perm {α : Type*} (A D : List (List α)) (b : List α) (r : ℕ) :
    (rotateWord b r ++ (A ++ D).flatten).Perm ((A ++ b :: D).flatten) := by
  have hp := (rotateWord_perm b r).append_right (A.flatten ++ D.flatten)
  have hc := (List.perm_append_comm : (b ++ A.flatten).Perm (A.flatten ++ b)).append_right D.flatten
  simpa only [List.flatten_append, List.flatten_cons, List.append_assoc] using hp.trans
    (by simpa only [List.append_assoc] using hc)

private def markedPieces {n : ℕ} (a : Shao.Path n) (ha : DistinctDisjointMeans a)
    (p : Fin n × Equiv.Perm (Fin n)) : List (List (Fin n)) × List (Fin n) × List (List (Fin n)) :=
  markedSplit (canonicalFaces a ha p.2) (p.1.val + 1)

private theorem markedPieces_spec {n : ℕ} (a : Shao.Path n) (ha : DistinctDisjointMeans a)
    (p : Fin n × Equiv.Perm (Fin n)) :
    let s := markedPieces a ha p
    FaceDecomposition a p.2 (s.1 ++ s.2.1 :: s.2.2) ∧
      s.1.flatten.length < p.1.val + 1 ∧
      p.1.val + 1 ≤ s.1.flatten.length + s.2.1.length ∧ s.2.1.length ≤ n := by
  have hc := canonicalFaces_spec a ha p.2
  have hlen : (canonicalFaces a ha p.2).flatten.length = n := by
    rw [hc.1, List.length_ofFn]
  have hs := markedSplit_spec (canonicalFaces a ha p.2) (p.1.val + 1)
    (by omega) (by rw [hlen]; omega)
  change FaceDecomposition a p.2 ((markedPieces a ha p).1 ++
      (markedPieces a ha p).2.1 :: (markedPieces a ha p).2.2) ∧ _
  have heq : canonicalFaces a ha p.2 = (markedPieces a ha p).1 ++
      (markedPieces a ha p).2.1 :: (markedPieces a ha p).2.2 := hs.1
  have hfaces : FaceDecomposition a p.2 ((markedPieces a ha p).1 ++
      (markedPieces a ha p).2.1 :: (markedPieces a ha p).2.2) := heq ▸ hc
  refine ⟨hfaces, hs.2.1, hs.2.2, ?_⟩
  have hf := congrArg List.length hfaces.1
  simp only [List.flatten_append, List.flatten_cons, List.length_append, List.length_ofFn] at hf
  omega

private theorem markedCutWord_perm {n : ℕ} (a : Shao.Path n) (ha : DistinctDisjointMeans a)
    (p : Fin n × Equiv.Perm (Fin n)) :
    let s := markedPieces a ha p
    (rotateWord s.2.1 (p.1.val + 1 - s.1.flatten.length) ++ (s.1 ++ s.2.2).flatten).Perm
      (List.ofFn (fun i : Fin n => i)) := by
  have hs := markedPieces_spec a ha p
  have hp := cutWord_perm (markedPieces a ha p).1 (markedPieces a ha p).2.2
    (markedPieces a ha p).2.1 (p.1.val + 1 - (markedPieces a ha p).1.flatten.length)
  rw [hs.1.1] at hp
  exact hp.trans (perm_ofFn_id p.2)

private def markedForward {n : ℕ} (a : Shao.Path n) (ha : DistinctDisjointMeans a)
    (p : Fin n × Equiv.Perm (Fin n)) : Fin n × Equiv.Perm (Fin n) := by
  let s := markedPieces a ha p
  have hs := markedPieces_spec a ha p
  have hb0 : 0 < s.2.1.length := by
    change 0 < (markedPieces a ha p).2.1.length
    omega
  exact (⟨s.2.1.length - 1, by change (markedPieces a ha p).2.1.length - 1 < n; omega⟩,
    permOfWord
      (rotateWord s.2.1 (p.1.val + 1 - s.1.flatten.length) ++ (s.1 ++ s.2.2).flatten)
      (markedCutWord_perm a ha p))

private theorem markedForward_length {n : ℕ} (a : Shao.Path n) (ha : DistinctDisjointMeans a)
    (p : Fin n × Equiv.Perm (Fin n)) :
    (markedForward a ha p).1.val + 1 = (markedPieces a ha p).2.1.length := by
  have hs := markedPieces_spec a ha p
  change (markedPieces a ha p).2.1.length - 1 + 1 = (markedPieces a ha p).2.1.length
  omega

private theorem markedForward_word {n : ℕ} (a : Shao.Path n) (ha : DistinctDisjointMeans a)
    (p : Fin n × Equiv.Perm (Fin n)) :
    List.ofFn (fun i : Fin n => (markedForward a ha p).2 i) =
      rotateWord (markedPieces a ha p).2.1
          (p.1.val + 1 - (markedPieces a ha p).1.flatten.length) ++
        ((markedPieces a ha p).1 ++ (markedPieces a ha p).2.2).flatten := by
  exact ofFn_permOfWord _ (markedCutWord_perm a ha p)

private theorem tail_maximum_congr {n : ℕ} (a : Shao.Path n) (k l : ℕ)
    (hk : k ≤ n) (hl : l ≤ n) (h : k = l) :
    Shao.maxWithZero (tail a k hk) = Shao.maxWithZero (tail a l hl) := by
  subst l
  rfl

private theorem markedForward_maximum {n : ℕ} (a : Shao.Path n) (ha : DistinctDisjointMeans a)
    (p : Fin n × Equiv.Perm (Fin n)) :
    Shao.maxWithZero (reorder a p.2) =
      max (Shao.prefixSum (reorder a (markedForward a ha p).2)
        ((markedForward a ha p).1.val + 1)) 0 +
          Shao.maxWithZero (tail (reorder a (markedForward a ha p).2)
            ((markedForward a ha p).1.val + 1) (by omega)) := by
  have hs := markedPieces_spec a ha p
  have ht : p.1.val + 1 - (markedPieces a ha p).1.flatten.length ≤
      (markedPieces a ha p).2.1.length := by omega
  obtain ⟨hk, hcut⟩ := cut_maximum_of_face_block a p.2 (markedForward a ha p).2
    (markedPieces a ha p).1 (markedPieces a ha p).2.2 (markedPieces a ha p).2.1
    (p.1.val + 1 - (markedPieces a ha p).1.flatten.length) ht hs.1
    (markedForward_word a ha p)
  have hlen := markedForward_length a ha p
  have hpref := congrArg
    (fun k : ℕ => max (Shao.prefixSum (reorder a (markedForward a ha p).2) k) 0) hlen
  have htail := tail_maximum_congr (reorder a (markedForward a ha p).2)
    ((markedForward a ha p).1.val + 1) (markedPieces a ha p).2.1.length
    (by omega) hk hlen
  rw [hpref, htail]
  exact hcut

private theorem insert_strict_face {n : ℕ} (a : Shao.Path n) (H : List (Fin n))
    (hH : StrictBelowChord a H) (B : List (List (Fin n)))
    (hbelow : ∀ b ∈ B, StrictBelowChord a b)
    (hpair : B.Pairwise (fun u v => wordMean a v < wordMean a u))
    (hne : ∀ b ∈ B, wordMean a H ≠ wordMean a b) :
    ∃ A D : List (List (Fin n)), B = A ++ D ∧
      WordFaces a (A.flatten ++ H ++ D.flatten) (A ++ H :: D) := by
  induction B with
  | nil => exact ⟨[], [], rfl, by simpa [WordFaces] using hH⟩
  | cons b B ih =>
    have hb := hbelow b (by simp)
    obtain ⟨hrel, hpairB⟩ := List.pairwise_cons.mp hpair
    have hbelowB : ∀ c ∈ B, StrictBelowChord a c := fun c hc => hbelow c (by simp [hc])
    have hneB : ∀ c ∈ B, wordMean a H ≠ wordMean a c := fun c hc => hne c (by simp [hc])
    by_cases hHb : wordMean a b < wordMean a H
    · refine ⟨[], b :: B, rfl, ?_, ?_, ?_⟩
      · simp [List.append_assoc]
      · intro c hc
        simp only [List.nil_append, List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact hH
        · exact hbelow c (by simpa only [List.mem_cons] using hc)
      · apply List.pairwise_cons.mpr
        refine ⟨?_, hpair⟩
        intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact hHb
        · exact (hrel c hc).trans hHb
    · have hbH : wordMean a H < wordMean a b :=
        lt_of_le_of_ne (not_lt.mp hHb) (hne b (by simp))
      obtain ⟨A, D, hB, hAD⟩ := ih hbelowB hpairB hneB
      refine ⟨b :: A, D, ?_, ?_, ?_, ?_⟩
      · simpa only [List.cons_append] using congrArg (List.cons b) hB
      · simp only [List.cons_append, List.flatten_cons, List.flatten_append,
          List.append_assoc]
      · intro c hc
        simp only [List.cons_append, List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact hb
        · exact hAD.2.1 c hc
      · apply List.pairwise_cons.mpr
        refine ⟨?_, hAD.2.2⟩
        intro c hc
        change c ∈ A ++ H :: D at hc
        rcases List.mem_append.mp hc with hc | hc
        · exact hrel c (by rw [hB]; simp [hc])
        · rcases List.mem_cons.mp hc with rfl | hc
          · exact hbH
          · exact hrel c (by rw [hB]; simp [hc])

private theorem rotateWord_eq_rotate {α : Type*} (b : List α) (r : ℕ) (hr : r ≤ b.length) :
    rotateWord b r = b.rotate r := (List.rotate_eq_drop_append_take hr).symm

private theorem rotateWord_complement {α : Type*} (b : List α) (r : ℕ) (hr : r ≤ b.length) :
    rotateWord (rotateWord b r) (b.length - r) = b := by
  have hc : b.length - r ≤ (rotateWord b r).length := by rw [rotateWord_length b r hr]; omega
  rw [rotateWord_eq_rotate _ _ hc, rotateWord_eq_rotate b r hr, List.rotate_rotate,
    Nat.add_sub_of_le hr, List.rotate_length]

private theorem markedPieces_at {n : ℕ} (a : Shao.Path n) (ha : DistinctDisjointMeans a)
    (p : Fin n × Equiv.Perm (Fin n)) (A D : List (List (Fin n))) (b : List (Fin n))
    (t : ℕ) (ht0 : 0 < t) (ht : t ≤ b.length)
    (hfaces : FaceDecomposition a p.2 (A ++ b :: D))
    (hmarker : p.1.val + 1 = A.flatten.length + t) :
    markedPieces a ha p = (A, b, D) := by
  unfold markedPieces
  rw [canonicalFaces_eq a ha p.2 (A ++ b :: D) hfaces, hmarker]
  exact markedSplit_at A D b t ht0 ht

private theorem markedForward_surjective {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) : Function.Surjective (markedForward a ha) := by
  intro y
  let k := y.1.val + 1
  let w := List.ofFn (fun i : Fin n => y.2 i)
  let Q := w.take k
  let R := w.drop k
  have hk0 : 0 < k := by dsimp [k]; omega
  have hk : k ≤ n := by dsimp [k]; omega
  have hwlen : w.length = n := List.length_ofFn
  have hQlen : Q.length = k := by simp only [Q, List.length_take, hwlen, Nat.min_eq_left hk]
  have hQR : Q ++ R = w := List.take_append_drop k w
  have hwN : w.Nodup := List.nodup_ofFn.mpr y.2.injective
  have hQN : Q.Nodup := hwN.take
  have hRN : R.Nodup := hwN.drop
  have hQne : Q ≠ [] := by
    intro h
    have hh := congrArg List.length h
    rw [hQlen] at hh
    simp only [List.length_nil] at hh
    omega
  have hdQR : Q.Disjoint R := List.disjoint_of_nodup_append (hQR.symm ▸ hwN)
  obtain ⟨r, hr, _⟩ := exists_unique_rotation_strictBelowChord a ha Q hQN hQne
  let H := rotateWord Q r.val
  let t := k - r.val
  have hH : StrictBelowChord a H := hr
  have hHlen : H.length = k := (rotateWord_length Q r.val r.is_lt.le).trans hQlen
  have ht0 : 0 < t := by dsimp [t]; have hh := r.is_lt; omega
  have ht : t ≤ H.length := by dsimp [t]; rw [hHlen]; omega
  have hrotate : rotateWord H t = Q := by
    simpa only [hQlen] using rotateWord_complement Q r.val r.is_lt.le
  have hHN : H.Nodup := (rotateWord_perm Q r.val).nodup_iff.mpr hQN
  obtain ⟨B, hB⟩ := exists_wordFaces a ha R hRN
  have hBN : ∀ b ∈ B, b.Nodup := (List.nodup_flatten.mp (hB.1.symm ▸ hRN)).1
  have hne (b : List (Fin n)) (hb : b ∈ B) : wordMean a H ≠ wordMean a b := by
    apply wordMean_ne_of_disjoint a ha H b hHN (hBN b hb) _ hH.1 (hB.2.1 b hb).1
    apply List.disjoint_left.mpr
    intro i hiH hib
    have hiQ : i ∈ Q := (rotateWord_perm Q r.val).mem_iff.mp hiH
    have hiR : i ∈ R := by
      rw [← hB.1]
      exact List.mem_flatten.mpr ⟨b, hb, hib⟩
    exact List.disjoint_left.mp hdQR hiQ hiR
  obtain ⟨A, D, hBAD, hInsert⟩ := insert_strict_face a H hH B hB.2.1 hB.2.2 hne
  have hremain : (A ++ D).flatten = R := by rw [← hBAD]; exact hB.1
  have hcutword : rotateWord H t ++ (A ++ D).flatten = w := by
    rw [hrotate, hremain]
    exact hQR
  let v := (A ++ H :: D).flatten
  have hp : v.Perm (List.ofFn (fun i : Fin n => i)) := by
    have hh := cutWord_perm A D H t
    rw [hcutword] at hh
    exact hh.symm.trans (perm_ofFn_id y.2)
  let σ := permOfWord v hp
  have hσword : List.ofFn (fun i : Fin n => σ i) = v := ofFn_permOfWord v hp
  have hσfaces : FaceDecomposition a σ (A ++ H :: D) :=
    ⟨hσword.symm, hInsert.2.1, hInsert.2.2⟩
  have hvlen : A.flatten.length + H.length + D.flatten.length = n := by
    have hh := hp.length_eq
    simpa only [v, List.flatten_append, List.flatten_cons, List.length_append,
      List.length_ofFn, Nat.add_assoc] using hh
  let q := A.flatten.length + t
  have hq0 : 0 < q := by dsimp [q]; omega
  have hqn : q ≤ n := by dsimp [q]; omega
  let p : Fin n × Equiv.Perm (Fin n) := (⟨q - 1, by omega⟩, σ)
  have hmarker : p.1.val + 1 = A.flatten.length + t := by dsimp [p, q]; omega
  have hPieces : markedPieces a ha p = (A, H, D) :=
    markedPieces_at a ha p A D H t ht0 ht hσfaces hmarker
  have hfw : List.ofFn (fun i : Fin n => (markedForward a ha p).2 i) = w := by
    rw [markedForward_word, hPieces]
    change rotateWord H (p.1.val + 1 - A.flatten.length) ++ (A ++ D).flatten = w
    rw [hmarker, Nat.add_sub_cancel_left]
    exact hcutword
  have hfl := markedForward_length a ha p
  rw [hPieces] at hfl
  change (markedForward a ha p).1.val + 1 = H.length at hfl
  rw [hHlen] at hfl
  have hfirst : (markedForward a ha p).1 = y.1 := by
    apply Fin.ext
    dsimp [k] at hfl
    omega
  have hsecond : (markedForward a ha p).2 = y.2 := by
    apply Equiv.ext
    intro i
    exact congrFun (List.ofFn_inj.mp hfw) i
  exact ⟨p, Prod.ext hfirst hsecond⟩

private def markedBackward {n : ℕ} (a : Shao.Path n) (ha : DistinctDisjointMeans a)
    (y : Fin n × Equiv.Perm (Fin n)) : Fin n × Equiv.Perm (Fin n) :=
  Classical.choose (markedForward_surjective a ha y)

private theorem markedBackward_rightInverse {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) :
    Function.RightInverse (markedBackward a ha) (markedForward a ha) :=
  fun y => Classical.choose_spec (markedForward_surjective a ha y)

private theorem markedBackward_leftInverse {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) :
    Function.LeftInverse (markedBackward a ha) (markedForward a ha) := by
  have hinj : Function.Injective (markedForward a ha) :=
    Finite.injective_iff_surjective.mpr (markedForward_surjective a ha)
  intro p
  apply hinj
  exact markedBackward_rightInverse a ha (markedForward a ha p)

theorem exists_marked_cut_equiv {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) :
    ∃ e : (Fin n × Equiv.Perm (Fin n)) ≃ (Fin n × Equiv.Perm (Fin n)),
      ∀ p : Fin n × Equiv.Perm (Fin n),
        Shao.maxWithZero (reorder a p.2) =
          max (Shao.prefixSum (reorder a (e p).2) ((e p).1.val + 1)) 0 +
            Shao.maxWithZero
              (tail (reorder a (e p).2) ((e p).1.val + 1) (by omega)) := by
  let e : (Fin n × Equiv.Perm (Fin n)) ≃ (Fin n × Equiv.Perm (Fin n)) :=
    { toFun := markedForward a ha
      invFun := markedBackward a ha
      left_inv := markedBackward_leftInverse a ha
      right_inv := markedBackward_rightInverse a ha }
  exact ⟨e, markedForward_maximum a ha⟩

private theorem finite_spitzer_cut_identity_of_generic (n : ℕ) (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) (L : ℝ) :
    (n : ℝ) * (∑ σ : Equiv.Perm (Fin n),
      Real.exp (-Shao.maxWithZero (reorder a σ) / L)) =
      ∑ k : Fin n, ∑ σ : Equiv.Perm (Fin n),
        Real.exp (-max (Shao.prefixSum (reorder a σ) (k.val + 1)) 0 / L) *
          Real.exp (-Shao.maxWithZero (tail (reorder a σ) (k.val + 1) (by omega)) / L) := by
  classical
  obtain ⟨e, he⟩ := exists_marked_cut_equiv a ha
  let F : Fin n × Equiv.Perm (Fin n) → ℝ := fun p =>
    Real.exp (-Shao.maxWithZero (reorder a p.2) / L)
  let H : Fin n × Equiv.Perm (Fin n) → ℝ := fun p =>
    Real.exp (-max (Shao.prefixSum (reorder a p.2) (p.1.val + 1)) 0 / L) *
      Real.exp (-Shao.maxWithZero (tail (reorder a p.2) (p.1.val + 1) (by omega)) / L)
  have hpoint (p : Fin n × Equiv.Perm (Fin n)) : F p = H (e p) := by
    dsimp only [F, H]
    rw [he p]
    simp only [neg_add, add_div, Real.exp_add]
  have hsum : (∑ p : Fin n × Equiv.Perm (Fin n), F p) = ∑ p : Fin n × Equiv.Perm (Fin n), H p := by
    calc
      _ = ∑ p : Fin n × Equiv.Perm (Fin n), H (e p) :=
        Finset.sum_congr rfl (fun p _ => hpoint p)
      _ = _ := e.sum_comp H
  simpa only [F, H, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using hsum

private theorem continuous_reorder {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Continuous (fun a : Shao.Path n => reorder a σ) := by
  exact continuous_pi fun i => continuous_apply (σ i)

private theorem continuous_tail {n : ℕ} (k : ℕ) (hk : k ≤ n) :
    Continuous (fun a : Shao.Path n => tail a k hk) := by
  exact continuous_pi fun i => continuous_apply (⟨k + i.val, by omega⟩ : Fin n)

theorem finite_spitzer_cut_identity (n : ℕ) (a : Shao.Path n) (L : ℝ) :
    (n : ℝ) *
        (∑ σ : Equiv.Perm (Fin n),
          Real.exp (-Shao.maxWithZero (reorder a σ) / L)) =
      ∑ k : Fin n, ∑ σ : Equiv.Perm (Fin n),
        Real.exp (-max (Shao.prefixSum (reorder a σ) (k.val + 1)) 0 / L) *
          Real.exp
            (-Shao.maxWithZero
              (tail (reorder a σ) (k.val + 1) (by omega)) / L) := by
  let f : Shao.Path n → ℝ := fun a =>
    (n : ℝ) * ∑ σ : Equiv.Perm (Fin n), Real.exp (-Shao.maxWithZero (reorder a σ) / L)
  let g : Shao.Path n → ℝ := fun a =>
    ∑ k : Fin n, ∑ σ : Equiv.Perm (Fin n),
      Real.exp (-max (Shao.prefixSum (reorder a σ) (k.val + 1)) 0 / L) *
        Real.exp (-Shao.maxWithZero (tail (reorder a σ) (k.val + 1) (by omega)) / L)
  have hf : Continuous f := by
    apply continuous_const.mul
    apply continuous_finsetSum
    intro σ hσ
    exact Real.continuous_exp.comp
      (((Shao.continuous_maxWithZero).comp (continuous_reorder σ)).neg.div_const L)
  have hg : Continuous g := by
    apply continuous_finsetSum
    intro k hk
    apply continuous_finsetSum
    intro σ hσ
    apply Continuous.mul
    · exact Real.continuous_exp.comp
        ((((Shao.continuous_prefixSum (k.val + 1)).comp (continuous_reorder σ)).max
          continuous_const).neg.div_const L)
    · exact Real.continuous_exp.comp
        (((Shao.continuous_maxWithZero).comp
          ((continuous_tail (k.val + 1) (by omega)).comp (continuous_reorder σ))).neg.div_const L)
  have hclosed : IsClosed {b : Shao.Path n | f b = g b} := isClosed_eq hf hg
  have hsub : {b : Shao.Path n | DistinctDisjointMeans b} ⊆ {b : Shao.Path n | f b = g b} := by
    intro b hb
    exact finite_spitzer_cut_identity_of_generic n b hb L
  exact (closure_minimal hsub hclosed) (dense_distinctDisjointMeans n a)

end Shao.Probability.Spitzer
