import Shao.OQ5.P35.FixedLawCoefficients
import Mathlib.Data.Nat.Choose.Basic

/-!
# The sharp finite binomial lower bound used in p35 (9)
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

theorem real_pow_div_le_choose (n K : ℕ) (hK : 0 < K) (hKn : K ≤ n) :
    ((n : ℝ) / (K : ℝ)) ^ K ≤ (n.choose K : ℝ) := by
  induction K generalizing n with
  | zero => omega
  | succ K ih =>
    cases K with
    | zero => simp
    | succ k =>
      cases n with
      | zero => omega
      | succ n =>
        have hkn : k + 1 ≤ n := by omega
        have hk0 : (0 : ℝ) < k + 1 := by positivity
        have hk1 : (0 : ℝ) < k + 1 + 1 := by positivity
        have hratio : ((n + 1 : ℕ) : ℝ) / ((k + 1 + 1 : ℕ) : ℝ) ≤
            (n : ℝ) / ((k + 1 : ℕ) : ℝ) := by
          apply (div_le_div_iff₀ (by exact_mod_cast Nat.zero_lt_succ (k + 1))
            (by exact_mod_cast Nat.zero_lt_succ k)).mpr
          push_cast
          have hn : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
          nlinarith
        have hind := ih n (by omega) hkn
        have hrec : ((n + 1).choose (k + 1 + 1) : ℝ) * ((k + 1 + 1 : ℕ) : ℝ) =
            ((n + 1 : ℕ) : ℝ) * (n.choose (k + 1) : ℝ) := by
          exact_mod_cast (Nat.add_one_mul_choose_eq n (k + 1)).symm
        rw [pow_succ]
        calc
          _ ≤ (n.choose (k + 1) : ℝ) *
              (((n + 1 : ℕ) : ℝ) / ((k + 1 + 1 : ℕ) : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact (pow_le_pow_left₀ (by positivity) hratio (k + 1)).trans hind
          _ = ((n + 1).choose (k + 1 + 1) : ℝ) := by
            rw [← mul_div_assoc]
            apply (div_eq_iff (by positivity : ((k + 1 + 1 : ℕ) : ℝ) ≠ 0)).mpr
            nlinarith [hrec]

end Shao.OQ5.P35
