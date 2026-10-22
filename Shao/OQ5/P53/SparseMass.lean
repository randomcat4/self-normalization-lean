import Shao.OQ5.P53.SparseSelection
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Normalized masses for one fixed sparse selection

The first fifteen theorem statements apply to arbitrary real parameters and
arbitrary index functions. Genuine summability precedes normalization and all
tail identities. The last two estimates use the same fixed selection core.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Shao.OQ5.P53

noncomputable section

def sparseLabelMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) : ℝ :=
  if j = 0 then 1 - ∑' k : ℕ, sparsePositiveMass α x N k
  else sparsePositiveMass α x N j

def sparseHighMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) : ℝ :=
  ∑' k : ℕ, sparsePositiveMass α x N (j + k)

def sparsePriorMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range j, sparseLabelMass α x N k

private theorem mass_dyadic_pos (j : ℕ) : 0 < sparseDyadic j := by
  exact inv_pos.mpr (pow_pos (by norm_num : 0 < (2 : ℝ)) j)

private theorem mass_levelAmplitude_nonneg (α : ℝ) (x : ℕ → ℝ)
    (N : ℕ → ℕ) (j : ℕ) : 0 ≤ sparseLevelAmplitude α x N j := by
  unfold sparseLevelAmplitude
  split_ifs
  · exact le_rfl
  · unfold sparseAmplitude
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.sqrt_nonneg _)

private theorem mass_dyadic_future_hasSum (j : ℕ) :
    HasSum (fun k : ℕ => sparseDyadic (j + 1 + k)) (sparseDyadic j) := by
  have hfun : (fun k : ℕ => sparseDyadic (j + 1 + k)) =
      (fun k : ℕ => sparseDyadic j / 2 / (2 : ℝ) ^ k) := by
    funext k
    simp only [sparseDyadic, pow_add, pow_one, mul_inv_rev, div_eq_mul_inv]
    ring
  rw [hfun]
  exact hasSum_geometric_two' (sparseDyadic j)

private theorem mass_positive_majorant_hasSum :
    HasSum (fun k : ℕ => sparseDyadic (k + 3)) (1 / 4 : ℝ) := by
  have h := mass_dyadic_future_hasSum 2
  have hvalue : sparseDyadic 2 = (1 / 4 : ℝ) := by
    norm_num [sparseDyadic]
  have hfun : (fun k : ℕ => sparseDyadic (2 + 1 + k)) =
      (fun k : ℕ => sparseDyadic (k + 3)) := by
    funext k
    congr 1
    omega
  rw [hfun, hvalue] at h
  exact h

theorem sparsePositiveMass_nonneg (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) : 0 ≤ sparsePositiveMass α x N j := by
  unfold sparsePositiveMass
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (mass_dyadic_pos _).le (Real.exp_pos _).le

theorem sparsePositiveMass_pos (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hj : 1 ≤ j) : 0 < sparsePositiveMass α x N j := by
  have hj0 : j ≠ 0 := by omega
  rw [sparsePositiveMass, ite_eq_right hj0]
  exact mul_pos (mass_dyadic_pos _) (Real.exp_pos _)

theorem sparsePositiveMass_le_dyadic (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hj : 1 ≤ j) :
    sparsePositiveMass α x N j ≤ sparseDyadic (j + 2) := by
  have hj0 : j ≠ 0 := by omega
  have hexp : Real.exp (-((sparseLevelAmplitude α x N j) ^ α)) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (Real.rpow_nonneg (mass_levelAmplitude_nonneg α x N j) α))
  rw [sparsePositiveMass, ite_eq_right hj0]
  calc
    sparseDyadic (j + 2) * Real.exp (-((sparseLevelAmplitude α x N j) ^ α)) ≤
        sparseDyadic (j + 2) * 1 :=
      mul_le_mul_of_nonneg_left hexp (mass_dyadic_pos _).le
    _ = sparseDyadic (j + 2) := mul_one _

theorem summable_sparsePositiveMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    Summable (sparsePositiveMass α x N) := by
  have hshift : Summable (fun k : ℕ => sparsePositiveMass α x N (k + 1)) := by
    apply Summable.of_nonneg_of_le
      (fun k => sparsePositiveMass_nonneg α x N (k + 1))
      (f := fun k : ℕ => sparseDyadic (k + 3))
    · intro k
      simpa only [Nat.add_assoc] using
        sparsePositiveMass_le_dyadic α x N (k + 1) (by omega)
    · exact mass_positive_majorant_hasSum.summable
  exact (summable_nat_add_iff 1).mp hshift

theorem sparsePositiveMass_tsum_bounds (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    0 ≤ (∑' j : ℕ, sparsePositiveMass α x N j) ∧
    (∑' j : ℕ, sparsePositiveMass α x N j) ≤ 1 / 4 := by
  have hs := summable_sparsePositiveMass α x N
  have hshift := (summable_nat_add_iff 1).mpr hs
  have hsplit := hs.sum_add_tsum_nat_add 1
  have hzero : (∑ i ∈ Finset.range 1, sparsePositiveMass α x N i) = 0 := by
    simp [sparsePositiveMass]
  rw [hzero, zero_add] at hsplit
  refine ⟨tsum_nonneg (fun j => sparsePositiveMass_nonneg α x N j), ?_⟩
  calc
    (∑' j : ℕ, sparsePositiveMass α x N j) =
        ∑' k : ℕ, sparsePositiveMass α x N (k + 1) := hsplit.symm
    _ ≤ ∑' k : ℕ, sparseDyadic (k + 3) :=
      hshift.tsum_le_tsum (fun k => by
        simpa only [Nat.add_assoc] using
          sparsePositiveMass_le_dyadic α x N (k + 1) (by omega))
        mass_positive_majorant_hasSum.summable
    _ = 1 / 4 := mass_positive_majorant_hasSum.tsum_eq

theorem sparseLabelMass_nonneg (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) : 0 ≤ sparseLabelMass α x N j := by
  by_cases hj : j = 0
  · subst j
    change 0 ≤ 1 - ∑' k : ℕ, sparsePositiveMass α x N k
    linarith [(sparsePositiveMass_tsum_bounds α x N).2]
  · rw [sparseLabelMass, ite_eq_right hj]
    exact sparsePositiveMass_nonneg α x N j

theorem hasSum_sparseLabelMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    HasSum (sparseLabelMass α x N) 1 := by
  classical
  let S : ℝ := ∑' k : ℕ, sparsePositiveMass α x N k
  have hm := (summable_sparsePositiveMass α x N).hasSum.update 0 (1 - S)
  have hfun : Function.update (sparsePositiveMass α x N) 0 (1 - S) =
      sparseLabelMass α x N := by
    funext j
    by_cases hj : j = 0
    · subst j
      simp [sparseLabelMass, S]
    · simp [sparseLabelMass, hj]
  have hzero : sparsePositiveMass α x N 0 = 0 := by simp [sparsePositiveMass]
  have hvalue : (1 - S) - sparsePositiveMass α x N 0 + S = (1 : ℝ) := by
    rw [hzero]
    ring
  rw [hfun, hvalue] at hm
  exact hm

theorem sparseLabelMass_zero_ge (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    (3 / 4 : ℝ) ≤ sparseLabelMass α x N 0 := by
  change (3 / 4 : ℝ) ≤ 1 - ∑' k : ℕ, sparsePositiveMass α x N k
  linarith [(sparsePositiveMass_tsum_bounds α x N).2]

theorem sparseLabelMass_eq_positiveMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hj : 1 ≤ j) :
    sparseLabelMass α x N j = sparsePositiveMass α x N j := by
  exact ite_eq_right (by omega : j ≠ 0)

theorem summable_sparsePositiveMass_tail (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) : Summable (fun k : ℕ => sparsePositiveMass α x N (j + k)) := by
  simpa only [Nat.add_comm] using
    (summable_nat_add_iff j).mpr (summable_sparsePositiveMass α x N)

theorem sparseHighMass_bounds (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) : 0 ≤ sparseHighMass α x N j ∧ sparseHighMass α x N j ≤ 1 / 4 := by
  have hs := summable_sparsePositiveMass α x N
  have hsplit := hs.sum_add_tsum_nat_add j
  have hfun : (fun k : ℕ => sparsePositiveMass α x N (k + j)) =
      (fun k : ℕ => sparsePositiveMass α x N (j + k)) := by
    funext k
    congr 1
    omega
  rw [hfun] at hsplit
  have hpref : 0 ≤ ∑ i ∈ Finset.range j, sparsePositiveMass α x N i :=
    Finset.sum_nonneg (fun i _ => sparsePositiveMass_nonneg α x N i)
  refine ⟨tsum_nonneg (fun k => sparsePositiveMass_nonneg α x N (j + k)), ?_⟩
  change (∑' k : ℕ, sparsePositiveMass α x N (j + k)) ≤ 1 / 4
  linarith [(sparsePositiveMass_tsum_bounds α x N).2]

theorem sparseHighMass_succ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) :
    sparseHighMass α x N j = sparsePositiveMass α x N j + sparseHighMass α x N (j + 1) := by
  have hs := summable_sparsePositiveMass_tail α x N j
  have hsplit := hs.sum_add_tsum_nat_add 1
  have hpref : (∑ i ∈ Finset.range 1, sparsePositiveMass α x N (j + i)) =
      sparsePositiveMass α x N j := by simp
  have hfun : (fun i : ℕ => sparsePositiveMass α x N (j + (i + 1))) =
      (fun i : ℕ => sparsePositiveMass α x N ((j + 1) + i)) := by
    funext i
    congr 1
    omega
  rw [hpref, hfun] at hsplit
  exact hsplit.symm

theorem sparsePriorMass_zero (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : sparsePriorMass α x N 0 = 0 := by
  simp [sparsePriorMass]

theorem sparsePriorMass_eq_one_sub_highMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hj : 1 ≤ j) : sparsePriorMass α x N j = 1 - sparseHighMass α x N j := by
  have hm := hasSum_sparseLabelMass α x N
  have hsplit := hm.summable.sum_add_tsum_nat_add j
  rw [hm.tsum_eq] at hsplit
  have hfun : (fun k : ℕ => sparseLabelMass α x N (k + j)) =
      (fun k : ℕ => sparsePositiveMass α x N (j + k)) := by
    funext k
    rw [sparseLabelMass_eq_positiveMass α x N (k + j) (by omega)]
    congr 1
    omega
  rw [hfun] at hsplit
  change sparsePriorMass α x N j + sparseHighMass α x N j = 1 at hsplit
  linarith

theorem sparsePriorMass_bounds (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hj : 1 ≤ j) :
    (3 / 4 : ℝ) ≤ sparsePriorMass α x N j ∧ sparsePriorMass α x N j < 1 := by
  have hHpos : 0 < sparseHighMass α x N j := by
    exact (summable_sparsePositiveMass_tail α x N j).tsum_pos
      (fun k => sparsePositiveMass_nonneg α x N (j + k)) 0
      (by simpa only [Nat.add_zero] using sparsePositiveMass_pos α x N j hj)
  have heq := sparsePriorMass_eq_one_sub_highMass α x N j hj
  have hHupper := (sparseHighMass_bounds α x N j).2
  constructor <;> linarith

private theorem mass_core_step_bounds (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hN : SparseSelectionCore α x N) (m : ℕ) :
    4 ≤ N (m + 1) ∧
    (N (m + 1) : ℝ) * sparsePositiveMass α x N (m + 1) ≤ sparseDyadic (m + 1) ∧
    sparsePositiveMass α x N (m + 1) ≤ sparseDyadic (m + 1) / (N m : ℝ) ^ 2 := by
  rcases hN with ⟨_hzero, _hpow, hsteps⟩
  rcases hsteps m with ⟨_hnext, hfour, _hx, _hslow, _ht, _hd, _htlower,
    _htupper, _hdupper, hcurrent, hprevious⟩
  exact ⟨hfour, hcurrent, hprevious⟩

private theorem mass_core_index_pos (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hN : SparseSelectionCore α x N) (j : ℕ) (hj : 1 ≤ j) : 0 < (N j : ℝ) := by
  cases j with
  | zero => omega
  | succ m =>
    have hfour : 4 ≤ N (m + 1) := (mass_core_step_bounds α x N hN m).1
    have hpos : 0 < N (m + 1) := lt_of_lt_of_le (by decide : 0 < (4 : ℕ)) hfour
    exact_mod_cast hpos

private theorem mass_core_current_cost (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hN : SparseSelectionCore α x N) (j : ℕ) (hj : 1 ≤ j) :
    (N j : ℝ) * sparsePositiveMass α x N j ≤ sparseDyadic j := by
  cases j with
  | zero => omega
  | succ m => exact (mass_core_step_bounds α x N hN m).2.1

private theorem mass_core_future_term (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hN : SparseSelectionCore α x N) (j : ℕ) (hj : 1 ≤ j) (k : ℕ) :
    (N j : ℝ) * sparsePositiveMass α x N (j + 1 + k) ≤
      sparseDyadic (j + 1 + k) / (N j : ℝ) := by
  have hA : 0 < (N j : ℝ) := mass_core_index_pos α x N hN j hj
  have hAB : (N j : ℝ) ≤ (N (j + k) : ℝ) := by
    exact_mod_cast (sparseSelectionCore_strictMono α x N hN).monotone
      (by omega : j ≤ j + k)
  have hB : 0 < (N (j + k) : ℝ) := lt_of_lt_of_le hA hAB
  have hp := (mass_core_step_bounds α x N hN (j + k)).2.2
  have hindex : j + k + 1 = j + 1 + k := by omega
  rw [hindex] at hp
  have hBsq : 0 < (N (j + k) : ℝ) ^ 2 := by positivity
  have hbound : sparsePositiveMass α x N (j + 1 + k) * (N (j + k) : ℝ) ^ 2 ≤
      sparseDyadic (j + 1 + k) := (le_div_iff₀ hBsq).mp hp
  have hsq : (N j : ℝ) ^ 2 ≤ (N (j + k) : ℝ) ^ 2 := by
    nlinarith [mul_le_mul hAB hAB hA.le hB.le]
  have hprod := mul_le_mul_of_nonneg_right hsq
    (sparsePositiveMass_nonneg α x N (j + 1 + k))
  apply (le_div_iff₀ hA).mpr
  nlinarith [hbound, hprod]

theorem sparseHighMass_future_cost (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hN : SparseSelectionCore α x N)
    (j : ℕ) (hj : 1 ≤ j) :
    (N j : ℝ) * sparseHighMass α x N (j + 1) ≤ sparseDyadic j / (N j : ℝ) := by
  have hleft : HasSum
      (fun k : ℕ => (N j : ℝ) * sparsePositiveMass α x N ((j + 1) + k))
      ((N j : ℝ) * sparseHighMass α x N (j + 1)) :=
    (summable_sparsePositiveMass_tail α x N (j + 1)).hasSum.mul_left (N j : ℝ)
  have hright : HasSum
      (fun k : ℕ => sparseDyadic (j + 1 + k) / (N j : ℝ))
      (sparseDyadic j / (N j : ℝ)) := by
    simpa only [div_eq_mul_inv] using
      (mass_dyadic_future_hasSum j).mul_right (N j : ℝ)⁻¹
  calc
    (N j : ℝ) * sparseHighMass α x N (j + 1) =
        ∑' k : ℕ, (N j : ℝ) * sparsePositiveMass α x N ((j + 1) + k) :=
      hleft.tsum_eq.symm
    _ ≤ ∑' k : ℕ, sparseDyadic (j + 1 + k) / (N j : ℝ) :=
      hleft.summable.tsum_le_tsum
        (fun k => mass_core_future_term α x N hN j hj k) hright.summable
    _ = sparseDyadic j / (N j : ℝ) := hright.tsum_eq

theorem sparseHighMass_total_cost (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hN : SparseSelectionCore α x N)
    (j : ℕ) (hj : 1 ≤ j) :
    (N j : ℝ) * sparseHighMass α x N j ≤
      sparseDyadic j + sparseDyadic j / (N j : ℝ) := by
  have hcurrent := mass_core_current_cost α x N hN j hj
  have hfuture := sparseHighMass_future_cost α x N hN j hj
  rw [sparseHighMass_succ, mul_add]
  exact add_le_add hcurrent hfuture

end

end Shao.OQ5.P53
