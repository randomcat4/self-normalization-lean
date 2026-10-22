import Shao.OQ5.P53.SparseMass
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Tail masses and the original natural background power

All masses retain the literal definitions from SparseMass. Genuine summability
and HasSum are used before tail or prefix limits. Only the final two results
consume the same supplied selection core; the natural exponent is unchanged.
-/

set_option autoImplicit false

open Filter
open scoped BigOperators Topology

namespace Shao.OQ5.P53

noncomputable section

private theorem limits_dyadic_tendsto_zero :
    Tendsto sparseDyadic atTop (nhds 0) := by
  have h : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  change Tendsto (fun j : ℕ => ((2 : ℝ) ^ j)⁻¹) atTop (nhds 0)
  simpa only [one_div, inv_pow] using h

private theorem limits_core_index_one_le (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hN : SparseSelectionCore α x N) (j : ℕ) : 1 ≤ (N j : ℝ) := by
  have hpow : 2 ^ j ≤ N j := hN.2.1 j
  have hpowpos : 0 < (2 : ℕ) ^ j := pow_pos (by decide) j
  have hn : 1 ≤ N j := by omega
  exact_mod_cast hn

theorem tendsto_sparseHighMass_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  Tendsto (fun j : ℕ => sparseHighMass α x N j) atTop (nhds 0) := by
  intro α x N
  have hs := summable_sparsePositiveMass α x N
  have hconst : Tendsto (fun _ : ℕ => ∑' k : ℕ, sparsePositiveMass α x N k)
      atTop (nhds (∑' k : ℕ, sparsePositiveMass α x N k)) := tendsto_const_nhds
  have hdiff : Tendsto
      (fun j : ℕ => (∑' k : ℕ, sparsePositiveMass α x N k) -
        ∑ i ∈ Finset.range j, sparsePositiveMass α x N i)
      atTop (nhds 0) := by
    simpa only [sub_self] using hconst.sub hs.hasSum.tendsto_sum_nat
  apply hdiff.congr'
  exact Filter.Eventually.of_forall fun j => by
    have hsplit := hs.sum_add_tsum_nat_add j
    have htail : (∑' k : ℕ, sparsePositiveMass α x N (k + j)) =
        sparseHighMass α x N j := by
      unfold sparseHighMass
      apply tsum_congr
      intro k
      rw [Nat.add_comm]
    rw [htail] at hsplit
    linarith

theorem tendsto_sparsePriorMass_one :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  Tendsto (fun j : ℕ => sparsePriorMass α x N j) atTop (nhds 1) := by
  intro α x N
  exact (hasSum_sparseLabelMass α x N).tendsto_sum_nat

theorem tendsto_sparseHighMass_cost_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_ : SparseSelectionCore α x N),
  Tendsto (fun j : ℕ => (N j : ℝ) * sparseHighMass α x N j)
    atTop (nhds 0) := by
  intro α x N hN
  have hupper : ∀ᶠ j : ℕ in atTop,
      (N j : ℝ) * sparseHighMass α x N j ≤ 2 * sparseDyadic j := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
    have hindex := limits_core_index_one_le α x N hN j
    have hpos : 0 < (N j : ℝ) := lt_of_lt_of_le (by norm_num) hindex
    have hw : 0 ≤ sparseDyadic j :=
      inv_nonneg.mpr (pow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) j)
    have hdiv : sparseDyadic j / (N j : ℝ) ≤ sparseDyadic j := by
      apply (div_le_iff₀ hpos).mpr
      nlinarith [mul_nonneg hw (sub_nonneg.mpr hindex)]
    calc
      (N j : ℝ) * sparseHighMass α x N j ≤
          sparseDyadic j + sparseDyadic j / (N j : ℝ) :=
        sparseHighMass_total_cost α x N hN j hj
      _ ≤ 2 * sparseDyadic j := by linarith
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun j =>
      mul_nonneg (Nat.cast_nonneg _) (sparseHighMass_bounds α x N j).1)
    hupper ?_
  simpa only [mul_zero] using limits_dyadic_tendsto_zero.const_mul (2 : ℝ)

theorem tendsto_sparsePriorMass_background_power_one :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_ : SparseSelectionCore α x N),
  Tendsto (fun j : ℕ => (sparsePriorMass α x N j) ^ (2 * (N j - 2)))
    atTop (nhds 1) := by
  intro α x N hN
  have herror : Tendsto
      (fun j : ℕ => 1 - (sparsePriorMass α x N j) ^ (2 * (N j - 2)))
      atTop (nhds 0) := by
    refine squeeze_zero'
      (g := fun j : ℕ => (2 : ℝ) * ((N j : ℝ) * sparseHighMass α x N j))
      ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
      have hb := sparsePriorMass_bounds α x N j hj
      have hb0 : 0 ≤ sparsePriorMass α x N j := by linarith [hb.1]
      exact sub_nonneg.mpr (pow_le_one₀ hb0 hb.2.le)
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
      have hb := sparsePriorMass_bounds α x N j hj
      have hbase : sparsePriorMass α x N j - 1 = -sparseHighMass α x N j := by
        linarith [sparsePriorMass_eq_one_sub_highMass α x N j hj]
      have hBern := one_add_mul_sub_le_pow
        (show (-1 : ℝ) ≤ sparsePriorMass α x N j by linarith [hb.1])
        (2 * (N j - 2))
      rw [hbase] at hBern
      have hlen : 2 * (N j - 2) ≤ 2 * N j :=
        Nat.mul_le_mul_left 2 (Nat.sub_le _ _)
      have hlenr : ((2 * (N j - 2) : ℕ) : ℝ) ≤ 2 * (N j : ℝ) := by
        exact_mod_cast hlen
      have hprod := mul_le_mul_of_nonneg_right hlenr
        (sparseHighMass_bounds α x N j).1
      nlinarith [hBern, hprod]
    · simpa only [mul_zero] using
        (tendsto_sparseHighMass_cost_zero α x N hN).const_mul (2 : ℝ)
  have hback : Tendsto
      (fun j : ℕ => (1 : ℝ) -
        (1 - (sparsePriorMass α x N j) ^ (2 * (N j - 2))))
      atTop (nhds 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub herror : Tendsto
        (fun j : ℕ => (1 : ℝ) -
          (1 - (sparsePriorMass α x N j) ^ (2 * (N j - 2))))
        atTop (nhds ((1 : ℝ) - 0)))
  apply hback.congr'
  exact Filter.Eventually.of_forall fun j => by ring

end

end Shao.OQ5.P53
