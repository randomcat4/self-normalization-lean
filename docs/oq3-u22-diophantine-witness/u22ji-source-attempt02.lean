import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Shao.OQ3
open scoped BigOperators
noncomputable section

theorem real_parameter_diophantine_of_integer_ratios
    (n : ℕ) (alpha : Fin (n + 1) → ℝ) (h0 : 0 < alpha 0)
    (c Q : ℝ) (hc : 0 < c) (hQ : 0 ≤ Q)
    (hInteger : ∀ q : ℤ, Q < |(q : ℝ)| → ∃ j : Fin n, ∀ p : ℤ,
      c * Real.rpow |(q : ℝ)| (-(3 : ℝ) / 16) ≤
        |(q : ℝ) * (alpha j.succ / alpha 0) - (p : ℝ)|) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ,
      T < |t| → ∃ i : Fin (n + 1), ∀ k : ℤ,
        C * Real.rpow |t| (-(3 : ℝ) / 16) ≤
          |t * alpha i - 2 * Real.pi * (k : ℝ)| := by
  simp only [Real.rpow_eq_pow] at hInteger ⊢
  let g : ℝ := -(3 : ℝ) / 16
  let A : ℝ := alpha 0 / (2 * Real.pi)
  let K : ℝ := A + 1
  let M : ℝ := ∑ j : Fin n, |alpha j.succ / alpha 0|
  let B : ℝ := (2 * Real.pi) * c * K ^ g
  let C : ℝ := B / (M + 1)
  let T : ℝ := (Q + 1) / A + 1
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hA : 0 < A := div_pos h0 hp
  have hK : 0 < K := by dsimp [K]; linarith
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hM1 : 0 < M + 1 := by linarith
  have hB : 0 < B := mul_pos (mul_pos hp hc) (Real.rpow_pos_of_pos hK g)
  have hC : 0 < C := div_pos hB hM1
  have hT : 0 ≤ T := by
    have hdiv : 0 ≤ (Q + 1) / A := div_nonneg (by linarith) hA.le
    dsimp [T]
    linarith
  have hCeq : C * (M + 1) = B := div_mul_cancel₀ B (ne_of_gt hM1)
  refine ⟨C, hC, T, hT, ?_⟩
  intro t ht
  let q : ℤ := round (t * A)
  let d0 : ℝ := |t * alpha 0 - 2 * Real.pi * (q : ℝ)|
  let v : ℝ := |t| ^ g
  have hta : t * A = t * alpha 0 / (2 * Real.pi) := by dsimp [A]; ring
  have ht1 : 1 < |t| := by
    have hdiv : 0 ≤ (Q + 1) / A := div_nonneg (by linarith) hA.le
    change (Q + 1) / A + 1 < |t| at ht
    linarith
  have hv : 0 < v := Real.rpow_pos_of_pos (by linarith) g
  have hat : |t * A| = A * |t| := by rw [abs_mul, abs_of_pos hA, mul_comm]
  have hround : |t * A - (q : ℝ)| ≤ 1 / 2 := abs_sub_round (t * A)
  have hLower := abs_add_le (t * A - (q : ℝ)) (q : ℝ)
  rw [sub_add_cancel, hat] at hLower
  have hTA : Q + 1 < A * |t| := by
    have hdiv : (Q + 1) / A < |t| := by
      change (Q + 1) / A + 1 < |t| at ht
      linarith
    have hmul := (div_lt_iff₀ hA).mp hdiv
    nlinarith
  have hqlo : Q < |(q : ℝ)| := by linarith
  have hqpos : 0 < |(q : ℝ)| := lt_of_le_of_lt hQ hqlo
  have hUpper := abs_add_le ((q : ℝ) - t * A) (t * A)
  rw [sub_add_cancel, abs_sub_comm (q : ℝ) (t * A), hat] at hUpper
  have hqhi : |(q : ℝ)| ≤ K * |t| := by dsimp [K]; nlinarith
  have hqPower : K ^ g * v ≤ |(q : ℝ)| ^ g := by
    have h := Real.rpow_le_rpow_of_nonpos hqpos hqhi (show g ≤ 0 by norm_num [g])
    rw [Real.mul_rpow hK.le (abs_nonneg t)] at h
    exact h
  have hscale (i : Fin (n + 1)) (k : ℤ) :
      |t * alpha i - 2 * Real.pi * (k : ℝ)| =
        (2 * Real.pi) * |t * alpha i / (2 * Real.pi) - (k : ℝ)| := by
    calc
      _ = |(2 * Real.pi) * (t * alpha i / (2 * Real.pi) - (k : ℝ))| := by
        congr 1
        field_simp <;> ring
      _ = _ := by rw [abs_mul, abs_of_pos hp]
  have hnearest (i : Fin (n + 1)) (k : ℤ) :
      |t * alpha i - 2 * Real.pi *
          (round (t * alpha i / (2 * Real.pi)) : ℤ)| ≤
        |t * alpha i - 2 * Real.pi * (k : ℝ)| := by
    rw [hscale, hscale]
    exact mul_le_mul_of_nonneg_left (round_le _ k) hp.le
  by_cases hfirst : C * v ≤ d0
  · refine ⟨0, fun k => hfirst.trans ?_⟩
    simpa only [d0, q, hta] using hnearest 0 k
  · have hsmall : d0 < C * v := lt_of_not_ge hfirst
    obtain ⟨j, hj⟩ := hInteger q hqlo
    let r : ℝ := alpha j.succ / alpha 0
    let p : ℤ := round (t * alpha j.succ / (2 * Real.pi))
    let dj : ℝ := |t * alpha j.succ - 2 * Real.pi * (p : ℝ)|
    have hrM : |r| ≤ M := by
      change |alpha j.succ / alpha 0| ≤ ∑ k : Fin n, |alpha k.succ / alpha 0|
      exact Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have hidentity : (2 * Real.pi) * ((q : ℝ) * r - (p : ℝ)) =
        (t * alpha j.succ - 2 * Real.pi * (p : ℝ)) -
          r * (t * alpha 0 - 2 * Real.pi * (q : ℝ)) := by
      dsimp [r]
      field_simp [ne_of_gt h0] <;> ring
    have htri : (2 * Real.pi) * |(q : ℝ) * r - (p : ℝ)| ≤ dj + |r| * d0 := by
      calc
        _ = |(2 * Real.pi) * ((q : ℝ) * r - (p : ℝ))| := by
          rw [abs_mul, abs_of_pos hp]
        _ = |(t * alpha j.succ - 2 * Real.pi * (p : ℝ)) -
            r * (t * alpha 0 - 2 * Real.pi * (q : ℝ))| := congrArg abs hidentity
        _ ≤ |t * alpha j.succ - 2 * Real.pi * (p : ℝ)| +
            |-(r * (t * alpha 0 - 2 * Real.pi * (q : ℝ)))| :=
          abs_add_le _ _
        _ = _ := by rw [abs_neg, abs_mul]
    have hPaid : B * v ≤ dj + |r| * d0 := by
      calc
        _ = ((2 * Real.pi) * c) * (K ^ g * v) := by dsimp [B]; ring
        _ ≤ ((2 * Real.pi) * c) * |(q : ℝ)| ^ g :=
          mul_le_mul_of_nonneg_left hqPower (mul_nonneg hp.le hc.le)
        _ = (2 * Real.pi) * (c * |(q : ℝ)| ^ g) := by ring
        _ ≤ (2 * Real.pi) * |(q : ℝ) * r - (p : ℝ)| :=
          mul_le_mul_of_nonneg_left (hj p) hp.le
        _ ≤ _ := htri
    have hError : |r| * d0 ≤ M * (C * v) :=
      (mul_le_mul_of_nonneg_right hrM (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hsmall.le hM)
    have hBudget : B * v = C * v + M * (C * v) := by rw [← hCeq]; ring
    have hdj : C * v ≤ dj := by nlinarith
    exact ⟨j.succ, fun k => hdj.trans (hnearest j.succ k)⟩

end
end Shao.OQ3
