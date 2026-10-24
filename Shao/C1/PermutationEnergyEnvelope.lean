import Shao.C1.PermutationCompensation
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.Real.Sqrt

noncomputable section
namespace Shao.C1.PermutationEnergyEnvelope
open scoped BigOperators

def revealRemainingSum {n : ℕ} (a : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (r : Fin n) : ℝ :=
  (∑ i : Fin n, a i) -
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < r.val), a (σ i)

def revealRemainingEnergy {n : ℕ} (a : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (r : Fin n) : ℝ :=
  (∑ i : Fin n, (a i) ^ 2) -
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < r.val), (a (σ i)) ^ 2

theorem remaining_energy_bounds {n : ℕ} (a : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (r : Fin n) :
    (a (σ r)) ^ 2 ≤ revealRemainingEnergy a σ r ∧
      revealRemainingSum a σ r ^ 2 ≤ (n - r.val : ℕ) * revealRemainingEnergy a σ r := by
  classical
  let U : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => r.val ≤ i.val)
  have hU : U = Finset.Ici r := by
    ext i
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
    rfl
  have hcard : U.card = n - r.val := by rw [hU, Fin.card_Ici]
  have hd : (∑ i ∈ U, a (σ i)) = revealRemainingSum a σ r :=
    PermutationCompensation.remaining_sum n a r σ
  have hT : (∑ i ∈ U, (a (σ i)) ^ 2) = revealRemainingEnergy a σ r :=
    PermutationCompensation.remaining_square_sum n a r σ
  constructor
  · rw [← hT]
    exact Finset.single_le_sum (fun i _ => sq_nonneg (a (σ i)))
      (by simp only [U, Finset.mem_filter, Finset.mem_univ, le_refl, and_self])
  · have hcs := Finset.sum_mul_sq_le_sq_mul_sq U (fun _ : Fin n => (1 : ℝ))
      (fun i => a (σ i))
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hd, hT, hcard] at hcs
    exact hcs

theorem normalized_remaining_bounds {n : ℕ} (a : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (r : Fin n)
    (hT : 0 < revealRemainingEnergy a σ r) :
    |a (σ r)| ≤ Real.sqrt (revealRemainingEnergy a σ r) ∧
      (|revealRemainingSum a σ r| / Real.sqrt (revealRemainingEnergy a σ r)) ^ 2 ≤
        (n - r.val : ℕ) := by
  have hb := remaining_energy_bounds a σ r
  constructor
  · nlinarith [sq_abs (a (σ r)), Real.sqrt_nonneg (revealRemainingEnergy a σ r),
      Real.sq_sqrt hT.le]
  · rw [div_pow, sq_abs, Real.sq_sqrt hT.le]
    exact (div_le_iff₀ hT).mpr hb.2

theorem compensated_derivative_bound {n : ℕ} (a : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (r : Fin n) (C fy : ℝ) (hC : 0 ≤ C)
    (hT : 0 < revealRemainingEnergy a σ r)
    (hfy : |fy| ≤ C / Real.sqrt (revealRemainingEnergy a σ r) *
      (1 + |revealRemainingSum a σ r| / Real.sqrt (revealRemainingEnergy a σ r))) :
    |a (σ r) - (a (σ r)) ^ 2 * revealRemainingSum a σ r / revealRemainingEnergy a σ r| *
      |fy| ≤ 2 * C * (1 + (n - r.val : ℕ)) := by
  let b := a (σ r)
  let d := revealRemainingSum a σ r
  let T := revealRemainingEnergy a σ r
  let s := Real.sqrt T
  have hs : 0 < s := Real.sqrt_pos.mpr hT
  have hb := remaining_energy_bounds a σ r
  have hn := normalized_remaining_bounds a σ r hT
  change b ^ 2 ≤ T ∧ d ^ 2 ≤ (n - r.val : ℕ) * T at hb
  change |b| ≤ s ∧ (|d| / s) ^ 2 ≤ (n - r.val : ℕ) at hn
  change |fy| ≤ C / s * (1 + |d| / s) at hfy
  change |b - b ^ 2 * d / T| * |fy| ≤ 2 * C * (1 + (n - r.val : ℕ))
  have hterm : b ^ 2 * |d| / T ≤ |d| := by
    apply (div_le_iff₀ hT).mpr
    nlinarith [mul_le_mul_of_nonneg_right hb.1 (abs_nonneg d)]
  have hcoef : |b - b ^ 2 * d / T| ≤ s + |d| := by
    calc
      _ ≤ |b| + |b ^ 2 * d / T| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le b 0 (b ^ 2 * d / T)
      _ = |b| + b ^ 2 * |d| / T := by
        rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg b), abs_of_pos hT]
      _ ≤ s + |d| := add_le_add hn.1 hterm
  have hquad : (1 + |d| / s) ^ 2 ≤ 2 * (1 + (n - r.val : ℕ)) := by
    nlinarith [sq_nonneg (|d| / s - 1), hn.2]
  calc
    _ ≤ (s + |d|) * (C / s * (1 + |d| / s)) :=
      mul_le_mul hcoef hfy (abs_nonneg fy) (add_nonneg hs.le (abs_nonneg d))
    _ = C * (1 + |d| / s) ^ 2 := by field_simp
    _ ≤ C * (2 * (1 + (n - r.val : ℕ))) := mul_le_mul_of_nonneg_left hquad hC
    _ = _ := by ring

theorem actual_remainder_bound {n : ℕ} (a : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (r : Fin n) (C fy vNext vNow : ℝ) (hC : 0 ≤ C)
    (hT : 0 < revealRemainingEnergy a σ r)
    (hfy : |fy| ≤ C / Real.sqrt (revealRemainingEnergy a σ r) *
      (1 + |revealRemainingSum a σ r| / Real.sqrt (revealRemainingEnergy a σ r)))
    (hvNext : 0 ≤ vNext ∧ vNext ≤ 1) (hvNow : 0 ≤ vNow ∧ vNow ≤ 1) :
    |vNext - vNow -
      (a (σ r) - (a (σ r)) ^ 2 * revealRemainingSum a σ r / revealRemainingEnergy a σ r) * fy| ≤
        1 + 2 * C * (1 + (n - r.val : ℕ)) := by
  have hc := compensated_derivative_bound a σ r C fy hC hT hfy
  have hv : |vNext - vNow| ≤ 1 := abs_le.mpr ⟨by linarith [hvNext.1, hvNow.2],
    by linarith [hvNext.2, hvNow.1]⟩
  let c := a (σ r) - (a (σ r)) ^ 2 * revealRemainingSum a σ r / revealRemainingEnergy a σ r
  change |c| * |fy| ≤ _ at hc
  change |vNext - vNow - c * fy| ≤ _
  have ht := abs_sub_le (vNext - vNow) 0 (c * fy)
  simp only [sub_zero, zero_sub, abs_neg, abs_mul] at ht
  linarith

end Shao.C1.PermutationEnergyEnvelope
