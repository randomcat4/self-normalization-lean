import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The fixed p52 layer coefficients

These are the exact source sequences indexed by J = j + 6. The bounds hold
for every layer and do not use a probability model or moment assumptions.
-/

set_option autoImplicit false

namespace Shao.OQ5.P52

noncomputable section

/-- Source N_J with J=j+6, fixed independently of exponents and sample sizes. -/
def fixedLayerN (j : ℕ) : ℕ := 2 ^ (3 * (j + 6) ^ 3)

/-- The exact dyadic source amplitude. -/
def fixedLayerT (j : ℕ) : ℝ := (2 : ℝ) ^ (2 * (j + 6) ^ 3)

def fixedLayerC (j : ℕ) : ℝ := 1 + 1 / ((j + 6 : ℕ) : ℝ)

def fixedLayerTau (j : ℕ) : ℝ := 1 / 3 - 1 / ((j + 6 : ℕ) : ℝ)

def fixedLayerP (j : ℕ) : ℝ :=
  Real.exp (-((fixedLayerN j : ℝ) ^ fixedLayerTau j))

def fixedLayerQ (j : ℕ) : ℝ := (fixedLayerN j : ℝ) ^ (-fixedLayerC j)

private theorem sourceIndex_ge_six (j : ℕ) :
    (6 : ℝ) ≤ ((j + 6 : ℕ) : ℝ) := by
  exact_mod_cast (Nat.le_add_left 6 j)

private theorem sourceIndex_recip_bounds (j : ℕ) :
    0 < 1 / ((j + 6 : ℕ) : ℝ) ∧ 1 / ((j + 6 : ℕ) : ℝ) ≤ 1 / 6 := by
  have hj := sourceIndex_ge_six j
  have hjpos : (0 : ℝ) < ((j + 6 : ℕ) : ℝ) := by linarith
  exact ⟨one_div_pos.mpr hjpos, one_div_le_one_div_of_le (by norm_num) hj⟩

theorem fixedLayerN_ge_eight (j : ℕ) : 8 ≤ fixedLayerN j := by
  have hcube : 0 < (j + 6) ^ 3 := by positivity
  have hexponent : 3 ≤ 3 * (j + 6) ^ 3 := Nat.mul_le_mul_left 3 hcube
  change 2 ^ 3 ≤ 2 ^ (3 * (j + 6) ^ 3)
  exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hexponent

theorem fixedLayerT_pos (j : ℕ) : 0 < fixedLayerT j := by
  unfold fixedLayerT
  positivity

theorem fixedLayerC_bounds (j : ℕ) :
    1 < fixedLayerC j ∧ fixedLayerC j ≤ 7 / 6 := by
  have h := sourceIndex_recip_bounds j
  unfold fixedLayerC
  constructor <;> linarith [h.1, h.2]

theorem fixedLayerTau_bounds (j : ℕ) :
    1 / 6 ≤ fixedLayerTau j ∧ fixedLayerTau j < 1 / 3 := by
  have h := sourceIndex_recip_bounds j
  unfold fixedLayerTau
  constructor <;> linarith [h.1, h.2]

private theorem fixedLayerN_real_ge_eight (j : ℕ) :
    (8 : ℝ) ≤ (fixedLayerN j : ℝ) := by
  exact_mod_cast fixedLayerN_ge_eight j

theorem fixedLayerP_bounds (j : ℕ) :
    0 < fixedLayerP j ∧ fixedLayerP j < 1 / 2 := by
  have hN := fixedLayerN_real_ge_eight j
  have htau := (fixedLayerTau_bounds j).1
  have hpower : 1 < (fixedLayerN j : ℝ) ^ fixedLayerTau j :=
    Real.one_lt_rpow (by linarith) (by linarith)
  have hexpone : (2 : ℝ) < Real.exp 1 := by
    convert Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0) using 1; norm_num
  have hexpneg : Real.exp (-1) < 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) hexpone
  constructor
  · exact Real.exp_pos _
  · exact (Real.exp_lt_exp.mpr (neg_lt_neg hpower)).trans hexpneg

theorem fixedLayerQ_bounds (j : ℕ) :
    0 < fixedLayerQ j ∧ fixedLayerQ j < 1 / 8 := by
  have hN := fixedLayerN_real_ge_eight j
  have hNpos : (0 : ℝ) < (fixedLayerN j : ℝ) := by linarith
  have hC := (fixedLayerC_bounds j).1
  have hpower : (fixedLayerN j : ℝ) ^ (-fixedLayerC j) <
      (fixedLayerN j : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by linarith) (neg_lt_neg hC)
  have hinv : (fixedLayerN j : ℝ) ^ (-1 : ℝ) ≤ 1 / 8 := by
    rw [Real.rpow_neg_one, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hN
  exact ⟨Real.rpow_pos_of_pos hNpos _, hpower.trans_le hinv⟩

theorem fixedLayerP_add_Q_lt_one (j : ℕ) :
    fixedLayerP j + fixedLayerQ j < 1 := by
  linarith [(fixedLayerP_bounds j).2, (fixedLayerQ_bounds j).2]

theorem fixedLayerT_eq_rpow_N (j : ℕ) :
    fixedLayerT j = (fixedLayerN j : ℝ) ^ (2 / 3 : ℝ) := by
  have hexponent :
      ((3 * (j + 6) ^ 3 : ℕ) : ℝ) * (2 / 3 : ℝ) =
        ((2 * (j + 6) ^ 3 : ℕ) : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    ring
  unfold fixedLayerT fixedLayerN
  rw [Nat.cast_pow, Nat.cast_ofNat,
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) (3 * (j + 6) ^ 3) (2 / 3),
    hexponent, Real.rpow_natCast]

end
end Shao.OQ5.P52
