import Shao.Probability.MeasurablePath
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.SpecialFunctions.Exp
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.List.Rotate

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

end Shao.Probability.Spitzer
