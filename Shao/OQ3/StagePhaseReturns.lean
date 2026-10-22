import Shao.OQ3.SourceGaussianLatticeGap
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecificLimits.Basic

/-!
The finite pigeonhole argument below is adapted from
Mathlib/NumberTheory/DiophantineApproximation/Basic.lean, lines 94–128.
Copyright (c) 2022 Michael Stoll. Authors: Michael Geißer, Michael Stoll.
That argument is released under the Apache License, Version 2.0.
The containing high-level module is not imported here.

Source application: current/oq3/proofs/r1/report.md, lines 486–489.
-/

namespace Shao.OQ3

open Filter
open scoped Topology

noncomputable section

private theorem finite_dirichlet (alpha : ℝ) {n : ℕ} (n_pos : 0 < n) :
    ∃ j k : ℤ, 0 < k ∧ k ≤ n ∧ |(k : ℝ) * alpha - j| ≤ 1 / ((n : ℝ) + 1) := by
  classical
  let f : ℤ → ℤ := fun m => ⌊Int.fract (alpha * m) * ((n : ℝ) + 1)⌋
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hfu := fun m : ℤ => mul_lt_of_lt_one_left hn (Int.fract_lt_one (alpha * m))
  conv in |_| ≤ _ => rw [mul_comm, le_div_iff₀ hn, ← abs_of_pos hn, ← abs_mul]
  let D := Finset.Icc (0 : ℤ) n
  by_cases! H : ∃ m ∈ D, f m = n
  · obtain ⟨m, hm, hf⟩ := H
    have hf' : ((n : ℤ) : ℝ) ≤ Int.fract (alpha * m) * ((n : ℝ) + 1) :=
      hf ▸ Int.floor_le (Int.fract (alpha * m) * ((n : ℝ) + 1))
    have hm0 : 0 < m := by
      have hf0 : f 0 = 0 := by simp only [f, Int.cast_zero, mul_zero, Int.fract_zero,
        zero_mul, Int.floor_zero]
      refine Ne.lt_of_le (fun h => n_pos.ne ?_) (Finset.mem_Icc.mp hm).1
      exact mod_cast hf0.symm.trans (h.symm ▸ hf : f 0 = n)
    refine ⟨⌊alpha * m⌋ + 1, m, hm0, (Finset.mem_Icc.mp hm).2, ?_⟩
    rw [Int.cast_add, ← sub_sub, sub_mul, Int.cast_one, one_mul, abs_le]
    refine ⟨le_sub_iff_add_le.mpr ?_, sub_le_iff_le_add.mpr
      (le_of_lt ((hfu m).trans (lt_one_add _)))⟩
    simpa only [neg_add_cancel_comm_assoc] using! hf'
  · have hD : (Finset.Ico (0 : ℤ) n).card < D.card := by
      rw [Int.card_Icc, Int.card_Ico]
      exact lt_add_one n
    have hfu' : ∀ m, f m ≤ n := fun m =>
      Int.lt_add_one_iff.mp (Int.floor_lt.mpr (mod_cast hfu m))
    have hwd : ∀ m : ℤ, m ∈ D → f m ∈ Finset.Ico (0 : ℤ) n := fun x hx =>
      Finset.mem_Ico.mpr ⟨Int.floor_nonneg.mpr
        (mul_nonneg (Int.fract_nonneg (alpha * x)) hn.le),
        Ne.lt_of_le (H x hx) (hfu' x)⟩
    obtain ⟨x, hx, y, hy, hxylt, hxy⟩ :
        ∃ x ∈ D, ∃ y ∈ D, x < y ∧ f x = f y := by
      obtain ⟨x, hx, y, hy, hne, heq⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to hD hwd
      rcases lt_trichotomy x y with (h | h | h)
      exacts [⟨x, hx, y, hy, h, heq⟩, False.elim (hne h), ⟨y, hy, x, hx, h, heq.symm⟩]
    refine ⟨⌊alpha * y⌋ - ⌊alpha * x⌋, y - x, sub_pos_of_lt hxylt,
      sub_le_iff_le_add.mpr (le_add_of_le_of_nonneg (Finset.mem_Icc.mp hy).2
        (Finset.mem_Icc.mp hx).1), ?_⟩
    convert_to! |Int.fract (alpha * y) * ((n : ℝ) + 1) -
      Int.fract (alpha * x) * ((n : ℝ) + 1)| ≤ 1
    · congr 1; push_cast; simp only [Int.fract]; ring
    exact (Int.abs_sub_lt_one_of_floor_eq_floor hxy.symm).le

private theorem fract_le_self_of_nonneg (x : ℝ) (hx : 0 ≤ x) : Int.fract x ≤ x := by
  have hf : 0 ≤ (⌊x⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr hx
  unfold Int.fract
  linarith only [hf]

private theorem exists_positive_phase_return (alpha eps : ℝ) (heps : 0 < eps) :
    ∃ n : ℕ, 0 < n ∧ Int.fract ((n : ℝ) * alpha) < eps := by
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt (lt_min heps (by norm_num : (0 : ℝ) < 1))
  obtain ⟨z, k, hk, _, herr⟩ := finite_dirichlet alpha (Nat.succ_pos M)
  let n : ℕ := k.toNat
  have hncast : (n : ℤ) = k := Int.toNat_of_nonneg hk.le
  have hn : 0 < n := by exact_mod_cast (show (0 : ℤ) < (n : ℤ) by rw [hncast]; exact hk)
  have hnr : (n : ℝ) = (k : ℝ) := by exact_mod_cast hncast
  let d : ℝ := (n : ℝ) * alpha - z
  have hd : |d| < min eps 1 := by
    apply lt_of_le_of_lt (by simpa only [d, hnr, Nat.cast_add, Nat.cast_one] using herr)
    have H : 1 / ((M : ℝ) + 1 + 1) ≤ 1 / ((M : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    simpa only [Nat.cast_succ, add_assoc] using H.trans_lt hM
  by_cases hd0 : 0 ≤ d
  · refine ⟨n, hn, ?_⟩
    have heq : (n : ℝ) * alpha = (z : ℝ) + d := by dsimp [d]; ring
    rw [heq, Int.fract_intCast_add]
    have hdeps : d < eps := by
      have H := hd.trans_le (min_le_left eps 1)
      simpa only [abs_of_nonneg hd0] using H
    exact (fract_le_self_of_nonneg d hd0).trans_lt hdeps
  · let e : ℝ := -d
    have he : 0 < e := by dsimp [e]; linarith only [hd0]
    have heeps : e < eps := by
      have H := hd.trans_le (min_le_left eps 1)
      simpa only [abs_of_neg (lt_of_not_ge hd0), e] using H
    have he1 : e < 1 := by
      have H := hd.trans_le (min_le_right eps 1)
      simpa only [abs_of_neg (lt_of_not_ge hd0), e] using H
    let m : ℕ := ⌊1 / e⌋₊
    have hm : 0 < m := by
      apply Nat.lt_of_lt_of_le Nat.zero_lt_one
      apply (Nat.one_le_floor_iff (1 / e)).mpr
      exact (le_div_iff₀ he).mpr (by linarith only [he1])
    have hme : (m : ℝ) * e ≤ 1 := by
      have H := Nat.floor_le (one_div_pos.mpr he).le
      exact (le_div_iff₀ he).mp H
    have hres : 1 - (m : ℝ) * e < e := by
      have H := (div_lt_iff₀ he).mp (Nat.lt_floor_add_one (1 / e))
      nlinarith only [H]
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have heq : ((m * n : ℕ) : ℝ) * alpha =
        (((m : ℤ) * z - 1 : ℤ) : ℝ) + (1 - (m : ℝ) * e) := by
      push_cast
      dsimp [e, d]
      ring
    rw [heq, Int.fract_intCast_add]
    exact (fract_le_self_of_nonneg _ (by linarith only [hme])).trans_lt
      (hres.trans heeps)

private theorem exists_larger_phase_return (alpha eps : ℝ) (heps : 0 < eps) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ Int.fract ((n : ℝ) * alpha) < eps := by
  obtain ⟨r, hr, hphase⟩ := exists_positive_phase_return (((B : ℝ) + 1) * alpha) eps heps
  refine ⟨(B + 1) * r, ?_, ?_⟩
  · have hr1 : 1 ≤ r := hr
    have H : B + 1 ≤ (B + 1) * r := by
      simpa only [mul_one] using Nat.mul_le_mul_left (B + 1) hr1
    omega
  · convert! hphase using 1
    push_cast
    ring

theorem exists_stage_phase_return_subsequence (J : ℕ) (q : ℝ) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      Tendsto (fun j : ℕ => Int.fract ((m j : ℝ) * q / dyadicMesh J))
        atTop (nhds 0) := by
  classical
  let alpha : ℝ := q / dyadicMesh J
  have hex (j B : ℕ) : ∃ n : ℕ, B < n ∧
      Int.fract ((n : ℝ) * alpha) < 1 / ((j : ℝ) + 2) :=
    exists_larger_phase_return alpha _ (by positivity) B
  let choose : ℕ → ℕ → ℕ := fun j B => Classical.choose (hex j B)
  have hchoose (j B : ℕ) : B < choose j B ∧
      Int.fract ((choose j B : ℝ) * alpha) < 1 / ((j : ℝ) + 2) :=
    Classical.choose_spec (hex j B)
  let m : ℕ → ℕ := Nat.rec (0 : ℕ) (fun j (prev : ℕ) => choose j prev)
  have hmono : StrictMono m := strictMono_nat_of_lt_succ (fun j => (hchoose j (m j)).1)
  have hbound (j : ℕ) : Int.fract ((Nat.cast (m j) : ℝ) * alpha) ≤ 1 / ((j : ℝ) + 1) := by
    cases j with
    | zero => simp [m]
    | succ j =>
      have H := (hchoose j (m j)).2.le
      simpa only [m, Nat.rec_add_one, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using H
  have hlimit : Tendsto (fun j : ℕ => Int.fract ((Nat.cast (m j) : ℝ) * alpha)) atTop (nhds 0) :=
    squeeze_zero (fun j => Int.fract_nonneg _) hbound tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨m, hmono, ?_⟩
  convert! hlimit using 1
  funext j
  congr 1
  dsimp [alpha]
  ring

end
end Shao.OQ3
