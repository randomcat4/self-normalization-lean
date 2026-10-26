import Shao.OQ6.FiniteHilbertSignMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false

namespace Shao.OQ6.FiniteSignExponential

noncomputable section

open scoped BigOperators
open Shao.OQ6.FiniteHilbertSignMoments (signValue cubeMean)

-- D01
def scalarSignSum
    (n : ℕ) (a : Fin n → ℝ) (s : Fin n → Bool) : ℝ :=
  ∑ i : Fin n, signValue (s i) * a i

-- D02
def scalarEnergy
    (n : ℕ) (a : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (a i) ^ (2 : ℕ)

-- T01
theorem finite_sign_exp_factorization
    (n : ℕ) (a : Fin n → ℝ) (lambda : ℝ) :
    cubeMean n (fun s : Fin n → Bool =>
      Real.exp (lambda * scalarSignSum n a s)) =
      ∏ i : Fin n,
        (Real.exp (lambda * a i) + Real.exp (-(lambda * a i))) / (2 : ℝ) := by
  let h : Fin n → Bool → ℝ := fun (i : Fin n) (b : Bool) =>
    Real.exp (lambda * signValue b * a i)
  have hPoint : ∀ s : Fin n → Bool,
      Real.exp (lambda * scalarSignSum n a s) =
        ∏ i : Fin n, h i (s i) := by
    intro s
    dsimp only [scalarSignSum]
    rw [Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    dsimp only [h]
    congr 1
    ring
  have hBool : ∀ i : Fin n, (∑ b : Bool, h i b) =
      Real.exp (lambda * a i) + Real.exp (-(lambda * a i)) := by
    intro i
    simp [h, signValue, neg_mul]
  unfold cubeMean
  simp_rw [hPoint]
  rw [← Fintype.prod_sum h]
  simp_rw [hBool]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [div_eq_mul_inv, mul_comm]

-- T02
theorem finite_sign_mgf_le
    (n : ℕ) (a : Fin n → ℝ) (lambda : ℝ) :
    cubeMean n (fun s : Fin n → Bool =>
      Real.exp (lambda * scalarSignSum n a s)) ≤
      Real.exp ((lambda ^ (2 : ℕ)) * scalarEnergy n a / (2 : ℝ)) := by
  rw [finite_sign_exp_factorization]
  simp_rw [← Real.cosh_eq]
  calc
    (∏ i : Fin n, Real.cosh (lambda * a i)) ≤
        ∏ i : Fin n, Real.exp (((lambda * a i) ^ (2 : ℕ)) / (2 : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        rw [Real.cosh_eq]
        positivity
      · intro i hi
        exact Real.cosh_le_exp_half_sq (lambda * a i)
    _ = Real.exp (∑ i : Fin n, ((lambda * a i) ^ (2 : ℕ)) / (2 : ℝ)) :=
      (Real.exp_sum Finset.univ
        (fun i : Fin n => ((lambda * a i) ^ (2 : ℕ)) / (2 : ℝ))).symm
    _ = Real.exp ((lambda ^ (2 : ℕ)) * scalarEnergy n a / (2 : ℝ)) := by
      congr 1
      simp only [scalarEnergy, mul_pow, Finset.mul_sum, Finset.sum_div]

-- T03
theorem finite_sign_two_sided_tail
    (n : ℕ) (a : Fin n → ℝ) (t : ℝ) (ht : (0 : ℝ) ≤ t) :
    cubeMean n (fun s : Fin n → Bool =>
      if t * Real.sqrt (scalarEnergy n a) < |scalarSignSum n a s|
      then (1 : ℝ) else (0 : ℝ)) ≤
      (2 : ℝ) * Real.exp (-(t ^ (2 : ℕ)) / (2 : ℝ)) := by
  let I : (Fin n → Bool) → ℝ := fun s : Fin n → Bool =>
    if t * Real.sqrt (scalarEnergy n a) < |scalarSignSum n a s|
    then (1 : ℝ) else (0 : ℝ)
  let Q : ℝ := scalarEnergy n a
  have hQnonneg : (0 : ℝ) ≤ Q := by
    dsimp only [Q, scalarEnergy]
    exact Finset.sum_nonneg (fun i hi => sq_nonneg (a i))
  by_cases hQzero : Q = (0 : ℝ)
  · let aSq : Fin n → ℝ := fun i : Fin n => (a i) ^ (2 : ℕ)
    have hSqSum : (∑ i : Fin n, aSq i) = (0 : ℝ) := by
      simpa only [Q, scalarEnergy, aSq] using hQzero
    have hSqNonneg : ∀ i : Fin n, (0 : ℝ) ≤ aSq i := by
      intro i
      exact sq_nonneg (a i)
    have haZero : ∀ i : Fin n, a i = (0 : ℝ) := by
      intro i
      have hSquareLe : (a i) ^ (2 : ℕ) ≤ (0 : ℝ) := by
        calc
          (a i) ^ (2 : ℕ) = aSq i := rfl
          _ ≤ ∑ j : Fin n, aSq j :=
            Finset.single_le_sum (fun j hj => hSqNonneg j) (Finset.mem_univ i)
          _ = (0 : ℝ) := hSqSum
      have hSquareZero : (a i) ^ (2 : ℕ) = (0 : ℝ) :=
        le_antisymm hSquareLe (sq_nonneg (a i))
      exact sq_eq_zero_iff.mp hSquareZero
    have hSignedZero : ∀ s : Fin n → Bool,
        scalarSignSum n a s = (0 : ℝ) := by
      intro s
      simp only [scalarSignSum, haZero, mul_zero, Finset.sum_const_zero]
    have hIZero : ∀ s : Fin n → Bool, I s = (0 : ℝ) := by
      intro s
      have hThreshold : (0 : ℝ) ≤ t * Real.sqrt (scalarEnergy n a) :=
        mul_nonneg ht (Real.sqrt_nonneg (scalarEnergy n a))
      dsimp only [I]
      rw [hSignedZero s, abs_zero, if_neg (not_lt_of_ge hThreshold)]
    have hMeanZero : cubeMean n I = (0 : ℝ) := by
      simp only [cubeMean, hIZero, Finset.sum_const_zero, mul_zero]
    change cubeMean n I ≤ (2 : ℝ) * Real.exp (-(t ^ (2 : ℕ)) / (2 : ℝ))
    rw [hMeanZero]
    exact mul_nonneg (by norm_num) (Real.exp_nonneg _)
  · have hQpos : (0 : ℝ) < Q :=
      lt_of_le_of_ne hQnonneg (Ne.symm hQzero)
    let r : ℝ := Real.sqrt Q
    have hrPositive : (0 : ℝ) < r := by
      dsimp only [r]
      exact Real.sqrt_pos.mpr hQpos
    let u : ℝ := t * r
    let lambda : ℝ := t / r
    let minusLambda : ℝ := -lambda
    let weight : ℝ := Real.exp (-(lambda * u))
    let Eplus : (Fin n → Bool) → ℝ := fun s : Fin n → Bool =>
      Real.exp (lambda * scalarSignSum n a s)
    let Eminus : (Fin n → Bool) → ℝ := fun s : Fin n → Bool =>
      Real.exp ((-lambda) * scalarSignSum n a s)
    let dominator : (Fin n → Bool) → ℝ := fun s : Fin n → Bool =>
      Real.exp (-(lambda * u)) * Real.exp (lambda * scalarSignSum n a s) +
        Real.exp (-(lambda * u)) * Real.exp ((-lambda) * scalarSignSum n a s)
    have hLambdaNonneg : (0 : ℝ) ≤ lambda :=
      div_nonneg ht (le_of_lt hrPositive)
    have hWeightNonneg : (0 : ℝ) ≤ weight := by
      dsimp only [weight]
      exact Real.exp_nonneg _
    have hEplusNonneg : ∀ s : Fin n → Bool, (0 : ℝ) ≤ Eplus s := by
      intro s
      dsimp only [Eplus]
      exact Real.exp_nonneg _
    have hEminusNonneg : ∀ s : Fin n → Bool, (0 : ℝ) ≤ Eminus s := by
      intro s
      dsimp only [Eminus]
      exact Real.exp_nonneg _
    have hPoint : ∀ s : Fin n → Bool, I s ≤ dominator s := by
      intro s
      change (if t * Real.sqrt (scalarEnergy n a) < |scalarSignSum n a s|
        then (1 : ℝ) else (0 : ℝ)) ≤ weight * Eplus s + weight * Eminus s
      by_cases hBad : t * Real.sqrt (scalarEnergy n a) < |scalarSignSum n a s|
      · rw [if_pos hBad]
        have hAbs : u < |scalarSignSum n a s| := by
          simpa only [u, r, Q] using hBad
        rcases lt_abs.mp hAbs with hPos | hNeg
        · have hArg : (0 : ℝ) ≤ -(lambda * u) + lambda * scalarSignSum n a s := by
            nlinarith [mul_nonneg hLambdaNonneg (sub_nonneg.mpr hPos.le)]
          have hOne : (1 : ℝ) ≤ weight * Eplus s := by
            dsimp only [weight, Eplus]
            rw [← Real.exp_add]
            exact Real.one_le_exp hArg
          exact hOne.trans
            (le_add_of_nonneg_right (mul_nonneg hWeightNonneg (hEminusNonneg s)))
        · have hArg : (0 : ℝ) ≤ -(lambda * u) + (-lambda) * scalarSignSum n a s := by
            nlinarith [mul_nonneg hLambdaNonneg (sub_nonneg.mpr hNeg.le)]
          have hOne : (1 : ℝ) ≤ weight * Eminus s := by
            dsimp only [weight, Eminus]
            rw [← Real.exp_add]
            exact Real.one_le_exp hArg
          exact hOne.trans
            (le_add_of_nonneg_left (mul_nonneg hWeightNonneg (hEplusNonneg s)))
      · rw [if_neg hBad]
        exact add_nonneg
          (mul_nonneg hWeightNonneg (hEplusNonneg s))
          (mul_nonneg hWeightNonneg (hEminusNonneg s))
    have hAverage : cubeMean n I ≤ cubeMean n dominator := by
      dsimp only [cubeMean]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun s hs => hPoint s)) (by positivity)
    have hDominatorAverage : cubeMean n dominator =
        weight * cubeMean n Eplus + weight * cubeMean n Eminus := by
      change ((2 : ℝ) ^ n)⁻¹ *
          (∑ s : Fin n → Bool, (weight * Eplus s + weight * Eminus s)) =
        weight * (((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool, Eplus s) +
          weight * (((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool, Eminus s)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    have hPlus : cubeMean n Eplus ≤
        Real.exp ((lambda ^ (2 : ℕ)) * Q / (2 : ℝ)) := by
      simpa only [Eplus, Q] using finite_sign_mgf_le n a lambda
    have hMinus : cubeMean n Eminus ≤
        Real.exp ((lambda ^ (2 : ℕ)) * Q / (2 : ℝ)) := by
      simpa only [Eminus, minusLambda, Q, neg_sq] using
        finite_sign_mgf_le n a minusLambda
    have hRSq : r ^ (2 : ℕ) = Q := by
      dsimp only [r]
      exact Real.sq_sqrt hQnonneg
    have hLambdaU : lambda * u = t ^ (2 : ℕ) := by
      dsimp only [lambda, u]
      field_simp [ne_of_gt hrPositive] <;> ring
    have hLambdaSquare : (lambda ^ (2 : ℕ)) * Q = t ^ (2 : ℕ) := by
      dsimp only [lambda]
      rw [div_pow, ← hRSq]
      exact div_mul_cancel₀ _ (pow_ne_zero _ (ne_of_gt hrPositive))
    have hExponent : -(lambda * u) + (lambda ^ (2 : ℕ)) * Q / (2 : ℝ) =
        -(t ^ (2 : ℕ)) / (2 : ℝ) := by
      rw [hLambdaU, hLambdaSquare]
      ring
    change cubeMean n I ≤ (2 : ℝ) * Real.exp (-(t ^ (2 : ℕ)) / (2 : ℝ))
    calc
      cubeMean n I ≤ cubeMean n dominator := hAverage
      _ = weight * cubeMean n Eplus + weight * cubeMean n Eminus :=
        hDominatorAverage
      _ ≤ weight * Real.exp ((lambda ^ (2 : ℕ)) * Q / (2 : ℝ)) +
          weight * Real.exp ((lambda ^ (2 : ℕ)) * Q / (2 : ℝ)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hPlus hWeightNonneg)
          (mul_le_mul_of_nonneg_left hMinus hWeightNonneg)
      _ = (2 : ℝ) * Real.exp (-(t ^ (2 : ℕ)) / (2 : ℝ)) := by
        rw [← two_mul]
        dsimp only [weight]
        rw [← Real.exp_add, hExponent]

end

end Shao.OQ6.FiniteSignExponential
