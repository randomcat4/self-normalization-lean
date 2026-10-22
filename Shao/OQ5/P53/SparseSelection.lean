import Shao.OQ5.P53.SparseScales
import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Topology.Order.OrderClosed

/-!
# One recursive sparse selection for the P53 input sequence

The complete input sequence is fixed before this construction. The zero-level
coefficients are separate literal values; each positive successor satisfies
both current-level and fixed-previous-level mass constraints.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace Shao.OQ5.P53

noncomputable section

def sparseDyadic (j : ℕ) : ℝ := ((2 : ℝ) ^ j)⁻¹

def sparseLevelAmplitude (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else sparseAmplitude α x (N j)

def sparseLevelShift (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else sparseShift α x (N j)

def sparsePositiveMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else
    sparseDyadic (j + 2) * Real.exp (-((sparseLevelAmplitude α x N j) ^ α))

def SparseSelectionCore (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : Prop :=
  let t := sparseLevelAmplitude α x N
  let d := sparseLevelShift α x N
  let π := sparsePositiveMass α x N
  N 0 = 1 ∧
  (∀ j : ℕ, 2 ^ j ≤ N j) ∧
  ∀ m : ℕ,
    let j := m + 1
    2 * N m < N j ∧ 4 ≤ N j ∧
    0 < x (N j) ∧ 0 < sparseSlow α x (N j) ∧
    0 < t j ∧ 0 < d j ∧
    (N j : ℝ) ^ (3 / 4 : ℝ) ≤ t j ∧
    t j ≤ (N j : ℝ) ∧ d j ≤ 2 * (N j : ℝ) ∧
    (N j : ℝ) * π j ≤ sparseDyadic j ∧
    π j ≤ sparseDyadic j / (N m : ℝ) ^ 2

private theorem dyadic_pos (j : ℕ) : 0 < sparseDyadic j := by
  exact inv_pos.mpr (pow_pos (by norm_num : 0 < (2 : ℝ)) j)

private theorem dyadic_add_two (j : ℕ) :
    sparseDyadic (j + 2) = sparseDyadic j / 4 := by
  have htwo : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
  unfold sparseDyadic
  field_simp [pow_add, htwo]
  norm_num [pow_add]

private def SelectionStep (α : ℝ) (x : ℕ → ℝ) (m M n : ℕ) : Prop :=
  2 ^ (m + 1) ≤ n ∧ 2 * M < n ∧ 4 ≤ n ∧
  0 < x n ∧ 0 < sparseSlow α x n ∧
  0 < sparseAmplitude α x n ∧ 0 < sparseShift α x n ∧
  (n : ℝ) ^ (3 / 4 : ℝ) ≤ sparseAmplitude α x n ∧
  sparseAmplitude α x n ≤ (n : ℝ) ∧ sparseShift α x n ≤ 2 * (n : ℝ) ∧
  (n : ℝ) * (sparseDyadic ((m + 1) + 2) *
    Real.exp (-((sparseAmplitude α x n) ^ α))) ≤ sparseDyadic (m + 1) ∧
  sparseDyadic ((m + 1) + 2) * Real.exp (-((sparseAmplitude α x n) ^ α)) ≤
    sparseDyadic (m + 1) / (M : ℝ) ^ 2

private theorem exists_selectionStep (α : ℝ) (x : ℕ → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hSuper : Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α)
      atTop atTop)
    (hSmall : Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0))
    (m M : ℕ) (hM : 0 < M) : ∃ n : ℕ, SelectionStep α x m M n := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hcost : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * Real.exp (-((sparseAmplitude α x n) ^ α)) ≤ 4 :=
    (sparse_nat_mul_exp_cost_tendsto_zero α x hα0 hα1 hSuper hSmall).eventually_le_const
      (by norm_num : (0 : ℝ) < 4)
  have hexp : ∀ᶠ n : ℕ in atTop,
      Real.exp (-((sparseAmplitude α x n) ^ α)) ≤ 4 / (M : ℝ) ^ 2 :=
    (sparse_exp_cost_tendsto_zero α x hα0 hα1 hSuper hSmall).eventually_le_const
      (by positivity : (0 : ℝ) < 4 / (M : ℝ) ^ 2)
  have hgood : ∀ᶠ n : ℕ in atTop, SelectionStep α x m M n := by
    filter_upwards [sparse_eventually_pos α x hα0 hα1 hSuper hSmall,
      sparse_eventual_bounds α x hα0 hα1 hSuper hSmall, hcost, hexp,
      eventually_ge_atTop (2 ^ (m + 1)), eventually_ge_atTop (2 * M + 1)]
      with n hp hb hc he hpow hnext
    rcases hp with ⟨hn4, hx, _hr, _hc, hs, ht, hd⟩
    have hmul : 2 * M < n := lt_of_lt_of_le (Nat.lt_succ_self (2 * M)) hnext
    have hw : 0 ≤ sparseDyadic (m + 1) / 4 := by
      exact div_nonneg (dyadic_pos _).le (by norm_num)
    dsimp only [SelectionStep]
    refine ⟨hpow, hmul, hn4, hx, hs, ht, hd, hb.1, hb.2.1, hb.2.2, ?_, ?_⟩
    · rw [dyadic_add_two]
      calc
        (n : ℝ) * (sparseDyadic (m + 1) / 4 *
            Real.exp (-((sparseAmplitude α x n) ^ α))) =
            (sparseDyadic (m + 1) / 4) *
              ((n : ℝ) * Real.exp (-((sparseAmplitude α x n) ^ α))) := by ring
        _ ≤ (sparseDyadic (m + 1) / 4) * 4 := mul_le_mul_of_nonneg_left hc hw
        _ = sparseDyadic (m + 1) := by ring
    · rw [dyadic_add_two]
      calc
        sparseDyadic (m + 1) / 4 * Real.exp (-((sparseAmplitude α x n) ^ α)) ≤
            (sparseDyadic (m + 1) / 4) * (4 / (M : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left he hw
        _ = sparseDyadic (m + 1) / (M : ℝ) ^ 2 := by ring
  exact hgood.exists

private def nextIndex (α : ℝ) (x : ℕ → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hSuper : Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α)
      atTop atTop)
    (hSmall : Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0))
    (m : ℕ) (M : {n : ℕ // 0 < n}) : {n : ℕ // 0 < n} := by
  classical
  let hex := exists_selectionStep α x hα0 hα1 hSuper hSmall m M.val M.property
  refine ⟨Nat.find hex, ?_⟩
  have hn4 : 4 ≤ Nat.find hex := (Nat.find_spec hex).2.2.1
  exact lt_of_lt_of_le (by decide : 0 < (4 : ℕ)) hn4

private theorem nextIndex_selectionStep (α : ℝ) (x : ℕ → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hSuper : Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α)
      atTop atTop)
    (hSmall : Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0))
    (m : ℕ) (M : {n : ℕ // 0 < n}) :
    SelectionStep α x m M.val (nextIndex α x hα0 hα1 hSuper hSmall m M).val := by
  classical
  change SelectionStep α x m M.val
    (Nat.find (exists_selectionStep α x hα0 hα1 hSuper hSmall m M.val M.property))
  exact Nat.find_spec (exists_selectionStep α x hα0 hα1 hSuper hSmall m M.val M.property)

private def selectedIndex (α : ℝ) (x : ℕ → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hSuper : Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α)
      atTop atTop)
    (hSmall : Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0)) :
    ℕ → {n : ℕ // 0 < n} :=
  Nat.rec (motive := fun _ : ℕ => {n : ℕ // 0 < n}) ⟨1, by decide⟩
    (fun m M => nextIndex α x hα0 hα1 hSuper hSmall m M)

theorem exists_sparseSelectionCore (α : ℝ) (x : ℕ → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hSuper : Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α)
      atTop atTop)
    (hSmall : Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0)) :
    ∃ N : ℕ → ℕ, SparseSelectionCore α x N := by
  let N : ℕ → ℕ := fun m => (selectedIndex α x hα0 hα1 hSuper hSmall m).val
  have hsteps (m : ℕ) : SelectionStep α x m (N m) (N (m + 1)) := by
    exact nextIndex_selectionStep α x hα0 hα1 hSuper hSmall m
      (selectedIndex α x hα0 hα1 hSuper hSmall m)
  refine ⟨N, ?_⟩
  dsimp only [SparseSelectionCore]
  refine ⟨rfl, ?_, ?_⟩
  · intro j
    cases j with
    | zero =>
      change (1 : ℕ) ≤ 1
      exact le_rfl
    | succ m => exact (hsteps m).1
  · intro m
    simpa only [sparseLevelAmplitude, sparseLevelShift, sparsePositiveMass,
      Nat.add_one_ne_zero, ite_false] using (hsteps m).2

theorem sparseSelectionCore_strictMono (α : ℝ) (x : ℕ → ℝ)
    (N : ℕ → ℕ) (hN : SparseSelectionCore α x N) :
    StrictMono N := by
  rcases hN with ⟨_hzero, _hpow, hstep⟩
  apply strictMono_nat_of_lt_succ
  intro m
  have hnext : 2 * N m < N (m + 1) := (hstep m).1
  nlinarith [Nat.zero_le (N m)]

theorem sparseSelectionCore_tendsto (α : ℝ) (x : ℕ → ℝ)
    (N : ℕ → ℕ) (hN : SparseSelectionCore α x N) :
    Tendsto N atTop atTop := by
  exact (sparseSelectionCore_strictMono α x N hN).tendsto_atTop

end

end Shao.OQ5.P53
