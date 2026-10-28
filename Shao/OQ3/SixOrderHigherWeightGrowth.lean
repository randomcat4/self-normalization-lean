import Shao.OQ3.ComplexWeightedMonomialRemainderBounds
import Shao.OQ3.FiniteWordMonomialEncoding
import Mathlib.Tactic.Ring

namespace Shao.OQ3
open scoped BigOperators
noncomputable section

set_option maxHeartbeats 1000000 in
theorem complex_six_order_higher_weight_growth_bound
    (A : Fin 6 → ℝ) (hA : ∀ j, 0 ≤ A j) :
    let W : (Fin 6 → ℂ) → ℂ := fun a =>
      ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
        ∑ sigma : Fin q.val → Fin 6,
          if 2 ≤ (∑ l, ((sigma l).val + 1)) ∧
            (∑ l, ((sigma l).val + 1)) ≤ 6 then ∏ l, a (sigma l) else 0
    ∃ K : ℝ, 0 < K ∧ ∀ t r : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ r →
      ∀ a : Fin 6 → ℂ,
        (∀ j, ‖a j‖ ≤ A j * t ^ (j.val + 1) * r ^ (j.val + 3)) →
        ‖W a‖ ≤ K * t ^ 2 * (1 + r ^ 18) := by
  classical
  intro W
  let ι := Σ q : Fin 7, {sigma : Fin q.val → Fin 6 //
    2 ≤ (∑ l, ((sigma l).val + 1)) ∧ (∑ l, ((sigma l).val + 1)) ≤ 6}
  let p : ι → Fin 6 → ℕ := fun i j => Fintype.card {l : Fin i.1.val // i.2.val l = j}
  let w : Fin 6 → ℕ := fun j => j.val + 1
  let c : ι → ℂ := fun i => 1 / (i.1.val.factorial : ℂ)
  have htime (i : ι) : 2 ≤ ∑ j, w j * p i j := by
    have he := (finite_word_monomial_encoding i.2.val).2.1 w
    change (∑ j, w j * p i j) = ∑ l, ((i.2.val l).val + 1) at he
    rw [he]
    exact i.2.property.1
  have hspace (i : ι) : (∑ j, (w j + 2) * p i j) ≤ 18 := by
    have he := (finite_word_monomial_encoding i.2.val).2.1 (fun j : Fin 6 => w j + 2)
    change (∑ j, (w j + 2) * p i j) = ∑ l, ((i.2.val l).val + 3) at he
    rw [he]
    have hs : (∑ l, ((i.2.val l).val + 3)) =
        (∑ l, ((i.2.val l).val + 1)) + 2 * i.1.val := by
      calc
        _ = ∑ l, (((i.2.val l).val + 1) + 2) := by
          apply Finset.sum_congr rfl
          intro l hl
          omega
        _ = _ := by simp [Finset.sum_add_distrib, Nat.mul_comm]
    rw [hs]
    have hq : i.1.val ≤ 6 := Nat.le_of_lt_succ i.1.isLt
    have hw := i.2.property.2
    omega
  have hmonomial (i : ι) (a : Fin 6 → ℂ) :
      (∏ j, a j ^ p i j) = ∏ l, a (i.2.val l) :=
    (finite_word_monomial_encoding i.2.val).2.2 a
  have hidentity (a : Fin 6 → ℂ) : W a = ∑ i : ι, c i * ∏ j, a j ^ p i j := by
    have hsub (q : Fin 7) :
        (∑ sigma : Fin q.val → Fin 6,
          if 2 ≤ (∑ l, ((sigma l).val + 1)) ∧ (∑ l, ((sigma l).val + 1)) ≤ 6
            then ∏ l, a (sigma l) else 0) =
          ∑ sigma : {sigma : Fin q.val → Fin 6 //
            2 ≤ (∑ l, ((sigma l).val + 1)) ∧ (∑ l, ((sigma l).val + 1)) ≤ 6},
              ∏ l, a (sigma.val l) := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by intro sigma; simp) _
    calc
      W a = ∑ q : Fin 7, ∑ sigma : {sigma : Fin q.val → Fin 6 //
          2 ≤ (∑ l, ((sigma l).val + 1)) ∧ (∑ l, ((sigma l).val + 1)) ≤ 6},
            c ⟨q, sigma⟩ * ∏ j, a j ^ p ⟨q, sigma⟩ j := by
        dsimp only [W]
        apply Finset.sum_congr rfl
        intro q hq
        rw [hsub, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro sigma hsigma
        rw [hmonomial]
      _ = ∑ i : ι, c i * ∏ j, a j ^ p i j :=
        (Fintype.sum_sigma (fun i : ι => c i * ∏ j, a j ^ p i j)).symm
  let B : ℝ := ∑ i : ι, ‖c i‖ * ∏ j, A j ^ p i j
  have hprod (i : ι) : 0 ≤ ∏ j, A j ^ p i j :=
    Finset.prod_nonneg (fun j _ => pow_nonneg (hA j) _)
  have hB : 0 ≤ B := Finset.sum_nonneg
    (fun i _ => mul_nonneg (norm_nonneg _) (hprod i))
  refine ⟨B + 1, by linarith, ?_⟩
  intro t r ht0 ht1 hr a ha
  have hA' (j : Fin 6) : 0 ≤ A j * r ^ (w j + 2) :=
    mul_nonneg (hA j) (pow_nonneg hr _)
  have ha' (j : Fin 6) : ‖a j‖ ≤ (A j * r ^ (w j + 2)) * t ^ w j := by
    calc
      _ ≤ A j * t ^ (j.val + 1) * r ^ (j.val + 3) := ha j
      _ = _ := by dsimp only [w]; ring
  have htail := complex_weighted_polynomial_tail_bound
    a (fun j => A j * r ^ (w j + 2)) w c p 2 t ht0 ht1 hA' ha' htime
  have hrad (i : ι) : r ^ (∑ j, (w j + 2) * p i j) ≤ 1 + r ^ 18 := by
    by_cases hr1 : r ≤ 1
    · exact (pow_le_one₀ hr hr1).trans (le_add_of_nonneg_right (pow_nonneg hr _))
    · exact (pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hr1)) (hspace i)).trans
        (le_add_of_nonneg_left (by norm_num))
  have hproducts (i : ι) :
      (∏ j, (A j * r ^ (w j + 2)) ^ p i j) =
        (∏ j, A j ^ p i j) * r ^ (∑ j, (w j + 2) * p i j) := by
    simp_rw [mul_pow, ← pow_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hcoeff : (∑ i, ‖c i‖ * ∏ j, (A j * r ^ (w j + 2)) ^ p i j) ≤
      B * (1 + r ^ 18) := by
    dsimp only [B]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    rw [hproducts]
    calc
      _ = (‖c i‖ * ∏ j, A j ^ p i j) * r ^ (∑ j, (w j + 2) * p i j) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hrad i) (mul_nonneg (norm_nonneg _) (hprod i))
  calc
    ‖W a‖ = ‖∑ i : ι, c i * ∏ j, a j ^ p i j‖ := by rw [hidentity]
    _ ≤ (∑ i, ‖c i‖ * ∏ j, (A j * r ^ (w j + 2)) ^ p i j) * t ^ 2 := htail
    _ ≤ (B * (1 + r ^ 18)) * t ^ 2 :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg ht0 _)
    _ ≤ ((B + 1) * (1 + r ^ 18)) * t ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : B ≤ B + 1) (by positivity))
        (pow_nonneg ht0 _)
    _ = (B + 1) * t ^ 2 * (1 + r ^ 18) := by ring

end
end Shao.OQ3
