import Shao.OQ3.ComplexTwoScalePolynomialTail
import Shao.OQ3.FiniteWordMonomialEncoding

namespace Shao.OQ3
open scoped BigOperators
noncomputable section

theorem complex_exp_taylor_six_weighted_tail_bound
    (A : Fin 6 → ℝ) (hA : ∀ j, 0 ≤ A j) :
    let P : (Fin 6 → ℂ) → ℂ := fun a =>
      ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
        ∑ sigma : Fin q.val → Fin 6,
          if (∑ i, ((sigma i).val + 1)) ≤ 6 then ∏ i, a (sigma i) else 0
    ∃ K : ℝ, 0 < K ∧ ∀ t r : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ r →
      ∀ a : Fin 6 → ℂ,
        (∀ j, ‖a j‖ ≤ A j * t ^ (j.val + 1) * r ^ (j.val + 3)) →
        ‖(∑ q : Fin 7, (∑ j, a j) ^ q.val / (q.val.factorial : ℂ)) - P a‖ ≤
          K * t ^ 7 * (r ^ 9 + r ^ 48) := by
  classical
  intro P
  let ι := Σ q : Fin 7, {sigma : Fin q.val → Fin 6 //
    7 ≤ ∑ i, ((sigma i).val + 1)}
  let m : ι → Fin 6 → ℕ := fun i j =>
    Fintype.card {l : Fin i.1.val // i.2.val l = j}
  let w : Fin 6 → ℕ := fun j => j.val + 1
  let c : ι → ℂ := fun i => 1 / (i.1.val.factorial : ℂ)
  have hdeg (i : ι) :
      7 ≤ ∑ j, w j * m i j ∧
        9 ≤ ∑ j, (w j + 2) * m i j ∧
          (∑ j, (w j + 2) * m i j) ≤ 48 := by
    have henc := finite_word_monomial_encoding i.2.val
    have ht : (∑ j, w j * m i j) = ∑ l, ((i.2.val l).val + 1) :=
      henc.2.1 w
    have hr : (∑ j, (w j + 2) * m i j) = ∑ l, ((i.2.val l).val + 3) :=
      henc.2.1 (fun j => j.val + 3)
    rw [ht, hr]
    exact ⟨i.2.property, fin_six_word_physical_degree_bounds i.1.val
      (Nat.le_of_lt_succ i.1.isLt) i.2.val i.2.property⟩
  obtain ⟨K, hK, hES⟩ := complex_two_scale_weighted_polynomial_tail_bound c m w A hA hdeg
  have hmonomial (i : ι) (a : Fin 6 → ℂ) :
      (∏ j, a j ^ m i j) = ∏ l, a (i.2.val l) :=
    (finite_word_monomial_encoding i.2.val).2.2 a
  have hidentity (a : Fin 6 → ℂ) :
      (∑ q : Fin 7, (∑ j, a j) ^ q.val / (q.val.factorial : ℂ)) - P a =
        ∑ i : ι, c i * ∏ j, a j ^ m i j := by
    have hpower (q : Fin 7) :
        (∑ j, a j) ^ q.val / (q.val.factorial : ℂ) =
          (1 / (q.val.factorial : ℂ)) * ∑ sigma : Fin q.val → Fin 6,
            ∏ l, a (sigma l) := by
      rw [Fintype.sum_pow]
      ring
    have hsub (q : Fin 7) :
        (∑ sigma : Fin q.val → Fin 6,
          if 7 ≤ ∑ l, ((sigma l).val + 1) then ∏ l, a (sigma l) else 0) =
          ∑ sigma : {sigma : Fin q.val → Fin 6 //
            7 ≤ ∑ l, ((sigma l).val + 1)}, ∏ l, a (sigma.val l) := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by intro sigma; simp) _
    calc
      _ = ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
          ∑ sigma : Fin q.val → Fin 6,
            if 7 ≤ ∑ l, ((sigma l).val + 1) then ∏ l, a (sigma l) else 0 := by
        dsimp only [P]
        simp_rw [hpower]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro q hq
        rw [← mul_sub, ← Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro sigma hsigma
        by_cases h : (∑ l, ((sigma l).val + 1)) ≤ 6
        · have hh : ¬7 ≤ ∑ l, ((sigma l).val + 1) := by omega
          simp [h, hh]
        · have hh : 7 ≤ ∑ l, ((sigma l).val + 1) := by omega
          simp [h, hh]
      _ = ∑ q : Fin 7, ∑ sigma : {sigma : Fin q.val → Fin 6 //
            7 ≤ ∑ l, ((sigma l).val + 1)},
          c ⟨q, sigma⟩ * ∏ j, a j ^ m ⟨q, sigma⟩ j := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [hsub, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro sigma hsigma
        rw [hmonomial]
      _ = ∑ i : ι, c i * ∏ j, a j ^ m i j := (Fintype.sum_sigma _).symm
  refine ⟨K, hK, ?_⟩
  intro t r ht0 ht1 hr0 a ha
  rw [hidentity]
  exact hES t r ht0 ht1 hr0 a ha

end
end Shao.OQ3
