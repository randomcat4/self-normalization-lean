import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Sort

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Sym.Card

set_option autoImplicit false

universe u

namespace Shao.OQ6.StretchedExponentialSumMoments

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

def scalarMomentScale (β τ M0 : ℝ) : ℝ :=
  M0 * (τ * β) ^ (-(1 / β))

def sumMomentScale (β τ M0 : ℝ) : ℝ :=
  2 * (2 : ℝ) ^ (1 / β) * scalarMomentScale β τ M0

def coordinateSum {n : ℕ} {Ω : Type u}
    (Y : Fin n → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  ∑ i : Fin n, Y i (x i)

private theorem moment_scales_pos
    (β τ M0 : ℝ) (hβ : 0 < β) (hτ : 0 < τ) (hM0 : 1 ≤ M0) :
    0 < scalarMomentScale β τ M0 ∧ 0 < sumMomentScale β τ M0 := by
  have hM0pos : 0 < M0 := lt_of_lt_of_le zero_lt_one hM0
  have hK : 0 < scalarMomentScale β τ M0 := by
    unfold scalarMomentScale
    positivity
  refine ⟨hK, ?_⟩
  unfold sumMomentScale
  positivity

private theorem nat_power_le_stretched_exp
    (β τ : ℝ) (hβ : 0 < β) (hτ : 0 < τ)
    (ℓ : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    y ^ ℓ ≤
      ((τ * β) ^ (-(1 / β))) ^ ℓ *
        ((ℓ.factorial : ℝ) ^ (1 / β)) * Real.exp (τ * y ^ β) := by
  let reciprocalBeta : ℝ := 1 / β
  let scalarExpScale : ℝ := (τ * β) ^ (-reciprocalBeta)
  let scaledInput : ℝ := τ * β * y ^ β
  have hReciprocal : 0 < reciprocalBeta := by dsimp [reciprocalBeta]; positivity
  have hScale : 0 < τ * β := mul_pos hτ hβ
  have hInput : 0 ≤ scaledInput := mul_nonneg hScale.le (Real.rpow_nonneg hy β)
  have hFactorial : 0 < (ℓ.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos ℓ)
  have hBetaCancel : β * reciprocalBeta = 1 := by
    dsimp [reciprocalBeta]
    field_simp [ne_of_gt hβ]
  have hInputRoot : scaledInput ^ reciprocalBeta = (τ * β) ^ reciprocalBeta * y := by
    dsimp only [scaledInput]
    rw [Real.mul_rpow hScale.le (Real.rpow_nonneg hy β),
      ← Real.rpow_mul hy, hBetaCancel, Real.rpow_one]
  have hExp : (Real.exp scaledInput) ^ reciprocalBeta = Real.exp (τ * y ^ β) := by
    rw [← Real.exp_mul]
    congr 1
    dsimp only [scaledInput, reciprocalBeta]
    field_simp [ne_of_gt hβ]
    <;> ring
  have hTaylor : scaledInput ^ ℓ / (ℓ.factorial : ℝ) ≤ Real.exp scaledInput :=
    Real.pow_div_factorial_le_exp scaledInput hInput ℓ
  have hRaised : (scaledInput ^ ℓ / (ℓ.factorial : ℝ)) ^ reciprocalBeta ≤
      (Real.exp scaledInput) ^ reciprocalBeta :=
    Real.rpow_le_rpow (div_nonneg (pow_nonneg hInput ℓ) hFactorial.le) hTaylor hReciprocal.le
  rw [Real.div_rpow (pow_nonneg hInput ℓ) hFactorial.le,
    ← Real.rpow_pow_comm hInput reciprocalBeta ℓ, hInputRoot, mul_pow, hExp] at hRaised
  have hPaid : ((τ * β) ^ reciprocalBeta) ^ ℓ * y ^ ℓ ≤
      Real.exp (τ * y ^ β) * (ℓ.factorial : ℝ) ^ reciprocalBeta :=
    (div_le_iff₀ (Real.rpow_pos_of_pos hFactorial reciprocalBeta)).mp hRaised
  have hInverse : scalarExpScale ^ ℓ * ((τ * β) ^ reciprocalBeta) ^ ℓ = 1 := by
    dsimp only [scalarExpScale]
    rw [Real.rpow_neg hScale.le, ← mul_pow,
      inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hScale reciprocalBeta)), one_pow]
  calc
    y ^ ℓ = scalarExpScale ^ ℓ * (((τ * β) ^ reciprocalBeta) ^ ℓ * y ^ ℓ) := by
      rw [← mul_assoc, hInverse, one_mul]
    _ ≤ scalarExpScale ^ ℓ *
        (Real.exp (τ * y ^ β) * (ℓ.factorial : ℝ) ^ reciprocalBeta) :=
      mul_le_mul_of_nonneg_left hPaid
        (pow_nonneg (Real.rpow_nonneg hScale.le _) ℓ)
    _ = ((τ * β) ^ (-(1 / β))) ^ ℓ *
        ((ℓ.factorial : ℝ) ^ (1 / β)) * Real.exp (τ * y ^ β) := by
      dsimp only [scalarExpScale, reciprocalBeta]
      ring

private theorem scalar_nat_moment_from_exp
    (β τ M0 : ℝ) (hβ : 0 < β) (hτ : 0 < τ) (hM0 : 1 ≤ M0)
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y)
    (hYnonneg : ∀ᵐ ω ∂μ, 0 ≤ Y ω)
    (hYexpInt : Integrable (fun ω : Ω => Real.exp (τ * (Y ω) ^ β)) μ)
    (hYexpBound : (∫ ω : Ω, Real.exp (τ * (Y ω) ^ β) ∂μ) ≤ M0)
    (ℓ : ℕ) :
    Integrable (fun ω : Ω => (Y ω) ^ ℓ) μ ∧
      0 ≤ (∫ ω : Ω, (Y ω) ^ ℓ ∂μ) ∧
      (∫ ω : Ω, (Y ω) ^ ℓ ∂μ) ≤
        (scalarMomentScale β τ M0) ^ ℓ * ((ℓ.factorial : ℝ) ^ (1 / β)) := by
  letI instMeasurableAlias : MeasurableSpace Ω := inferInstance
  letI instScalarProbability : IsProbabilityMeasure μ := inferInstance
  let reciprocalBeta : ℝ := 1 / β
  let scalarExpScale : ℝ := (τ * β) ^ (-reciprocalBeta)
  let scalarMomentK : ℝ := scalarMomentScale β τ M0
  by_cases hExponentZero : ℓ = 0
  · subst ℓ
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, Real.one_rpow]
    refine ⟨integrable_const (1 : ℝ), ?_, ?_⟩ <;> norm_num
  · have hExponentNonzero : ℓ ≠ 0 := hExponentZero
    have hExponentPositive : 1 ≤ ℓ := by omega
    have hCoefficientNonneg :
        0 ≤ scalarExpScale ^ ℓ * (ℓ.factorial : ℝ) ^ reciprocalBeta := by
      dsimp only [scalarExpScale]
      positivity
    have hDom : ∀ᵐ ω ∂μ, (Y ω) ^ ℓ ≤
        (scalarExpScale ^ ℓ * (ℓ.factorial : ℝ) ^ reciprocalBeta) *
          Real.exp (τ * (Y ω) ^ β) := by
      filter_upwards [hYnonneg] with ω hω
      exact nat_power_le_stretched_exp β τ hβ hτ ℓ (Y ω) hω
    have hPowerNonneg : ∀ᵐ ω ∂μ, 0 ≤ (Y ω) ^ ℓ :=
      hYnonneg.mono (fun ω hω => pow_nonneg hω ℓ)
    have hDomInt : Integrable (fun ω : Ω =>
        (scalarExpScale ^ ℓ * (ℓ.factorial : ℝ) ^ reciprocalBeta) *
          Real.exp (τ * (Y ω) ^ β)) μ :=
      hYexpInt.const_mul _
    have hPowerInt : Integrable (fun ω : Ω => (Y ω) ^ ℓ) μ :=
      hDomInt.mono_nonneg (hY.pow_const ℓ).aestronglyMeasurable hPowerNonneg hDom
    have hM0Absorb : M0 ≤ M0 ^ ℓ := by
      simpa only [pow_one] using pow_le_pow_right₀ hM0 hExponentPositive
    refine ⟨hPowerInt, integral_nonneg_of_ae hPowerNonneg, ?_⟩
    calc
      (∫ ω : Ω, (Y ω) ^ ℓ ∂μ) ≤ ∫ ω : Ω,
          (scalarExpScale ^ ℓ * (ℓ.factorial : ℝ) ^ reciprocalBeta) *
            Real.exp (τ * (Y ω) ^ β) ∂μ := integral_mono_ae hPowerInt hDomInt hDom
      _ = (scalarExpScale ^ ℓ * (ℓ.factorial : ℝ) ^ reciprocalBeta) *
          (∫ ω : Ω, Real.exp (τ * (Y ω) ^ β) ∂μ) := integral_const_mul _ _
      _ ≤ (scalarExpScale ^ ℓ * (ℓ.factorial : ℝ) ^ reciprocalBeta) * M0 :=
        mul_le_mul_of_nonneg_left hYexpBound hCoefficientNonneg
      _ ≤ M0 ^ ℓ * (scalarExpScale ^ ℓ * (ℓ.factorial : ℝ) ^ reciprocalBeta) := by
        simpa only [mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_right hM0Absorb hCoefficientNonneg
      _ = (scalarMomentScale β τ M0) ^ ℓ * (ℓ.factorial : ℝ) ^ (1 / β) := by
        dsimp only [scalarExpScale, reciprocalBeta, scalarMomentScale]
        rw [mul_pow]
        ring

private theorem positive_factorial_prod_le
    (k j : ℕ) (ℓ : Fin j → ℕ)
    (hj : 1 ≤ j) (hℓ : ∀ i : Fin j, 1 ≤ ℓ i)
    (hsum : (∑ i : Fin j, ℓ i) = k) :
    (∏ i : Fin j, (ℓ i).factorial) ≤ (k - j + 1).factorial := by
  have hMerge : ∀ (u v : ℕ), 1 ≤ u → 1 ≤ v →
      u.factorial * v.factorial ≤ (u + v - 1).factorial := by
    intro u v hu hv
    have hV : 1 + (v - 1) = v := by omega
    have hVFactorial : v.factorial = (2 : ℕ).ascFactorial (v - 1) := by
      simpa only [Nat.factorial_one, one_mul, hV] using
        (Nat.factorial_mul_ascFactorial 1 (v - 1)).symm
    calc
      u.factorial * v.factorial = u.factorial * (2 : ℕ).ascFactorial (v - 1) := by
        rw [hVFactorial]
      _ ≤ u.factorial * (u + 1).ascFactorial (v - 1) :=
        Nat.mul_le_mul_left _ (Nat.ascFactorial_le (v - 1) (by omega))
      _ = (u + (v - 1)).factorial := Nat.factorial_mul_ascFactorial u (v - 1)
      _ = (u + v - 1).factorial := congr_arg Nat.factorial (by omega)
  have hInd : ∀ (j k : ℕ) (ℓ : Fin j → ℕ),
      1 ≤ j → (∀ i : Fin j, 1 ≤ ℓ i) → (∑ i : Fin j, ℓ i) = k →
        (∏ i : Fin j, (ℓ i).factorial) ≤ (k - j + 1).factorial := by
    intro j
    induction j with
    | zero =>
        intro k ℓ hj hℓ hsum
        omega
    | succ j ih =>
        intro k ℓ hj hℓ hsum
        let tailParts : Fin j → ℕ := fun i : Fin j => ℓ i.succ
        let tailTotal : ℕ := ∑ i : Fin j, tailParts i
        have hTailParts : ∀ i : Fin j, 1 ≤ tailParts i := fun i => hℓ i.succ
        have hSplit : ℓ 0 + tailTotal = k := by
          simpa only [Fin.sum_univ_succ, tailTotal, tailParts] using hsum
        by_cases hTailEmpty : j = 0
        · subst j
          have hOnly : ℓ 0 = k := by simpa [tailTotal, tailParts] using hSplit
          have hk : 1 ≤ k := hOnly ▸ hℓ 0
          simp [hOnly, Nat.sub_add_cancel hk]
        · have hTailPositive : 1 ≤ j := by omega
          have hTailTotal : j ≤ tailTotal := by
            calc
              j = ∑ i : Fin j, (1 : ℕ) := by simp
              _ ≤ ∑ i : Fin j, tailParts i :=
                Finset.sum_le_sum (fun i _ => hTailParts i)
              _ = tailTotal := rfl
          have hTailBound : (∏ i : Fin j, (tailParts i).factorial) ≤
              (tailTotal - j + 1).factorial :=
            ih tailTotal tailParts hTailPositive hTailParts rfl
          calc
            (∏ i : Fin (j + 1), (ℓ i).factorial) =
                (ℓ 0).factorial * ∏ i : Fin j, (tailParts i).factorial :=
              Fin.prod_univ_succ (fun i : Fin (j + 1) => (ℓ i).factorial)
            _ ≤ (ℓ 0).factorial * (tailTotal - j + 1).factorial :=
              Nat.mul_le_mul_left _ hTailBound
            _ ≤ (ℓ 0 + (tailTotal - j + 1) - 1).factorial :=
              hMerge (ℓ 0) (tailTotal - j + 1) (hℓ 0) (by omega)
            _ = (k - (j + 1) + 1).factorial := by
              have hHeadPositive : 1 ≤ ℓ 0 := hℓ 0
              exact congr_arg Nat.factorial (by omega)
  exact hInd j k ℓ hj hℓ hsum

private theorem positive_composition_count_eq
    (k j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    (((Finset.univ : Finset (Fin j → Fin (k + 1))).filter
      (fun ℓ : Fin j → Fin (k + 1) =>
        (∀ i : Fin j, 0 < (ℓ i : ℕ)) ∧
          (∑ i : Fin j, (ℓ i : ℕ)) = k)).card) =
      (k - 1).choose (j - 1) := by
  classical
  let compositionUniverse : Finset (Fin j → Fin (k + 1)) := Finset.univ
  by_cases hjk : j ≤ k
  · have hWeakCard :
        (Finset.piAntidiag (Finset.univ : Finset (Fin j)) (k - j)).card =
          (k - 1).choose (j - 1) := by
      rw [← Finset.map_sym_eq_piAntidiag (Finset.univ : Finset (Fin j)) (k - j),
        Finset.card_map, Finset.sym_univ, Finset.card_univ,
        Sym.card_sym_eq_choose, Fintype.card_fin]
      have hTop : j + (k - j) - 1 = k - 1 := by omega
      rw [hTop]
      exact Nat.choose_symm_of_eq_add (by omega : k - 1 = (k - j) + (j - 1))
    have hCard :
        (((Finset.univ : Finset (Fin j → Fin (k + 1))).filter
          (fun composition : Fin j → Fin (k + 1) =>
            (∀ i : Fin j, 0 < (composition i : ℕ)) ∧
              (∑ i : Fin j, (composition i : ℕ)) = k)).card) =
          (Finset.piAntidiag (Finset.univ : Finset (Fin j)) (k - j)).card := by
      refine Finset.card_bij
        (fun (composition : Fin j → Fin (k + 1)) _ =>
          fun i : Fin j => (composition i : ℕ) - 1) ?_ ?_ ?_
      · intro composition hComposition
        have hCompositionPositive : ∀ i : Fin j, 0 < (composition i : ℕ) :=
          (Finset.mem_filter.mp hComposition).2.1
        have hCompositionTotal : (∑ i : Fin j, (composition i : ℕ)) = k :=
          (Finset.mem_filter.mp hComposition).2.2
        let weakPartsNat : Fin j → ℕ := fun i : Fin j => (composition i : ℕ) - 1
        have hShift : (∑ i : Fin j, weakPartsNat i) + j = k := by
          calc
            (∑ i : Fin j, weakPartsNat i) + j =
                ∑ i : Fin j, ((composition i : ℕ) - 1 + 1) := by
              simp [Finset.sum_add_distrib, weakPartsNat]
            _ = ∑ i : Fin j, (composition i : ℕ) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact Nat.sub_add_cancel (hCompositionPositive i)
            _ = k := hCompositionTotal
        apply Finset.mem_piAntidiag.mpr
        refine ⟨?_, fun i _ => Finset.mem_univ i⟩
        change (∑ i : Fin j, weakPartsNat i) = k - j
        omega
      · intro left hLeft right hRight hEqual
        have hLeftPositive : ∀ i : Fin j, 0 < (left i : ℕ) :=
          (Finset.mem_filter.mp hLeft).2.1
        have hRightPositive : ∀ i : Fin j, 0 < (right i : ℕ) :=
          (Finset.mem_filter.mp hRight).2.1
        funext i
        apply Fin.ext
        have hCoordinate : (left i : ℕ) - 1 = (right i : ℕ) - 1 := congr_fun hEqual i
        have hLeftCoordinate : 0 < (left i : ℕ) := hLeftPositive i
        have hRightCoordinate : 0 < (right i : ℕ) := hRightPositive i
        omega
      · intro weakPartsNat hWeakMembership
        have hWeakTotal : (∑ i : Fin j, weakPartsNat i) = k - j :=
          (Finset.mem_piAntidiag.mp hWeakMembership).1
        have hLiftBound : ∀ i : Fin j, weakPartsNat i + 1 < k + 1 := by
          intro i
          have hSingle : weakPartsNat i ≤ ∑ t : Fin j, weakPartsNat t :=
            Finset.single_le_sum (fun t _ => Nat.zero_le (weakPartsNat t)) (Finset.mem_univ i)
          omega
        let liftedComposition : Fin j → Fin (k + 1) :=
          fun i : Fin j => ⟨weakPartsNat i + 1, hLiftBound i⟩
        refine ⟨liftedComposition, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · constructor
          · intro i
            exact Nat.succ_pos _
          · change (∑ i : Fin j, (weakPartsNat i + 1)) = k
            rw [Finset.sum_add_distrib, hWeakTotal]
            simpa using Nat.sub_add_cancel hjk
        · ext i
          exact Nat.add_sub_cancel _ _
    exact hCard.trans hWeakCard
  · have hEmpty : ((Finset.univ : Finset (Fin j → Fin (k + 1))).filter
        (fun composition : Fin j → Fin (k + 1) =>
          (∀ i : Fin j, 0 < (composition i : ℕ)) ∧
            (∑ i : Fin j, (composition i : ℕ)) = k)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro composition hComposition
      have hPositive : ∀ i : Fin j, 0 < (composition i : ℕ) :=
        (Finset.mem_filter.mp hComposition).2.1
      have hTotal : (∑ i : Fin j, (composition i : ℕ)) = k :=
        (Finset.mem_filter.mp hComposition).2.2
      have hLower : j ≤ ∑ i : Fin j, (composition i : ℕ) := by
        calc
          j = ∑ i : Fin j, (1 : ℕ) := by simp
          _ ≤ ∑ i : Fin j, (composition i : ℕ) :=
            Finset.sum_le_sum (fun i _ => hPositive i)
      omega
    rw [hEmpty, Nat.choose_eq_zero_of_lt (by omega : k - 1 < j - 1)]

private theorem choose_le_pow_div_factorial (n j : ℕ) :
    (n.choose j : ℝ) ≤ (n : ℝ) ^ j / (j.factorial : ℝ) := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos j) : 0 < (j.factorial : ℝ))).mpr
  have hNatural : n.choose j * j.factorial ≤ n ^ j := by
    simpa only [Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_comm]
      using Nat.descFactorial_le_pow n j
  exact_mod_cast hNatural

private theorem factorial_ratio_le_pow
    (k j : ℕ) (hjk : j ≤ k) :
    (k.factorial : ℝ) / (j.factorial : ℝ) ≤ (k : ℝ) ^ (k - j) := by
  have hFactorial : 0 < (j.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos j)
  have hIdentity : j.factorial * k.descFactorial (k - j) = k.factorial := by
    simpa only [Nat.sub_sub_self hjk] using
      (Nat.factorial_mul_descFactorial (Nat.sub_le k j))
  have hBound : (k.descFactorial (k - j) : ℝ) ≤ (k : ℝ) ^ (k - j) := by
    exact_mod_cast Nat.descFactorial_le_pow k (k - j)
  apply (div_le_iff₀ hFactorial).mpr
  calc
    (k.factorial : ℝ) = (j.factorial : ℝ) * (k.descFactorial (k - j) : ℝ) := by
      exact_mod_cast hIdentity.symm
    _ ≤ (j.factorial : ℝ) * (k : ℝ) ^ (k - j) :=
      mul_le_mul_of_nonneg_left hBound hFactorial.le
    _ = (k : ℝ) ^ (k - j) * (j.factorial : ℝ) := mul_comm _ _

private theorem factorial_tail_le_pow
    (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    (k - j + 1).factorial ≤ k ^ (k - j) := by
  have hTail : ((k - j + 1).factorial : ℝ) ≤ ((k - j + 1 : ℕ) : ℝ) ^ (k - j) := by
    simpa only [Nat.factorial_one, Nat.cast_one, div_one, Nat.add_sub_cancel]
      using factorial_ratio_le_pow (k - j + 1) 1 (by omega)
  have hBase : k - j + 1 ≤ k := by omega
  have hPower : ((k - j + 1 : ℕ) : ℝ) ^ (k - j) ≤ (k : ℝ) ^ (k - j) := by
    gcongr
  exact_mod_cast hTail.trans hPower

private theorem finite_sum_pow_eq_multinomial
    (n k : ℕ) (z : Fin n → ℝ) :
    (∑ i : Fin n, z i) ^ k =
      ∑ m : Fin n → Fin (k + 1),
        if (∑ i : Fin n, (m i : ℕ)) = k then
          ((k.factorial : ℝ) /
            (∏ i : Fin n, ((m i : ℕ).factorial : ℝ))) *
              (∏ i : Fin n, (z i) ^ (m i : ℕ))
        else 0 := by
  classical
  calc
    (∑ i : Fin n, z i) ^ k =
        ∑ naturalExponents ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) k,
          (Nat.multinomial (Finset.univ : Finset (Fin n)) naturalExponents : ℝ) *
            ∏ i : Fin n, z i ^ naturalExponents i :=
      Finset.sum_pow_eq_sum_piAntidiag Finset.univ z k
    _ = ∑ exponents ∈ (Finset.univ : Finset (Fin n → Fin (k + 1))).filter
        (fun exponents : Fin n → Fin (k + 1) => (∑ i : Fin n, (exponents i : ℕ)) = k),
          ((k.factorial : ℝ) / (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ))) *
            (∏ i : Fin n, z i ^ (exponents i : ℕ)) := by
      symm
      refine Finset.sum_bij (fun exponents _ => fun i : Fin n => (exponents i : ℕ)) ?_ ?_ ?_ ?_
      · intro exponents hExponents
        have hExponentTotal : (∑ i : Fin n, (exponents i : ℕ)) = k :=
          (Finset.mem_filter.mp hExponents).2
        exact Finset.mem_piAntidiag.mpr ⟨hExponentTotal, fun i _ => Finset.mem_univ i⟩
      · intro left hLeft right hRight hEqual
        funext i
        exact Fin.ext (congr_fun hEqual i)
      · intro naturalExponents hNaturalMembership
        have hNaturalTotal : (∑ i : Fin n, naturalExponents i) = k :=
          (Finset.mem_piAntidiag.mp hNaturalMembership).1
        have hNaturalBound : ∀ i : Fin n, naturalExponents i < k + 1 := by
          intro i
          have hSingle : naturalExponents i ≤ ∑ t : Fin n, naturalExponents t :=
            Finset.single_le_sum (fun t _ => Nat.zero_le (naturalExponents t)) (Finset.mem_univ i)
          omega
        let boundedNaturalExponents : Fin n → Fin (k + 1) :=
          fun i : Fin n => ⟨naturalExponents i, hNaturalBound i⟩
        refine ⟨boundedNaturalExponents, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        exact hNaturalTotal
      · intro exponents hExponents
        have hExponentTotal : (∑ i : Fin n, (exponents i : ℕ)) = k :=
          (Finset.mem_filter.mp hExponents).2
        have hDenominator : 0 < (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ)) := by
          exact Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (Nat.factorial_pos (exponents i : ℕ)))
        have hCoefficientIdentity :
            (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ)) *
              (Nat.multinomial (Finset.univ : Finset (Fin n))
                (fun i : Fin n => (exponents i : ℕ)) : ℝ) = (k.factorial : ℝ) := by
          have hNaturalCoefficientIdentity :
              (∏ i : Fin n, (exponents i : ℕ).factorial) *
                Nat.multinomial (Finset.univ : Finset (Fin n))
                  (fun i : Fin n => (exponents i : ℕ)) = k.factorial := by
            simpa only [hExponentTotal] using
              (Nat.multinomial_spec (Finset.univ : Finset (Fin n))
                (fun i : Fin n => (exponents i : ℕ)))
          exact_mod_cast hNaturalCoefficientIdentity
        have hCoefficient :
            (Nat.multinomial (Finset.univ : Finset (Fin n))
              (fun i : Fin n => (exponents i : ℕ)) : ℝ) =
                (k.factorial : ℝ) / (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ)) := by
          apply (eq_div_iff (ne_of_gt hDenominator)).mpr
          simpa only [mul_comm] using hCoefficientIdentity
        rw [← hCoefficient]
    _ = ∑ m : Fin n → Fin (k + 1),
        if (∑ i : Fin n, (m i : ℕ)) = k then
          ((k.factorial : ℝ) / (∏ i : Fin n, ((m i : ℕ).factorial : ℝ))) *
            (∏ i : Fin n, z i ^ (m i : ℕ))
        else 0 := by rw [Finset.sum_filter]

private theorem factorial_weighted_multinomial_le
    (n k : ℕ) (a : ℝ) (ha : 1 ≤ a) (hk : 1 ≤ k) :
    (∑ m : Fin n → Fin (k + 1),
      if (∑ i : Fin n, (m i : ℕ)) = k then
        (k.factorial : ℝ) *
          (∏ i : Fin n, ((m i : ℕ).factorial : ℝ) ^ (a - 1))
      else 0) ≤
        (2 * ((n : ℝ) + (k : ℝ) ^ a)) ^ k := by
  classical
  let factorialExcessExponent : ℝ := a - 1
  let exponentUniverse : Finset (Fin n → Fin (k + 1)) := Finset.univ
  have hExcess : 0 ≤ a - 1 := by linarith
  have hSupport : ∀ (supportSet : Finset (Fin n))
      (exponents : Fin n → Fin (k + 1)),
      (∑ i : Fin n, (exponents i : ℕ)) = k →
      Finset.univ.filter (fun i : Fin n => 0 < (exponents i : ℕ)) = supportSet →
      1 ≤ supportSet.card ∧ supportSet.card ≤ k ∧
        (∏ i : Fin n, (exponents i : ℕ).factorial) ≤ k ^ (k - supportSet.card) := by
    intro supportSet
    let supportCard : ℕ := supportSet.card
    let supportOrder : Fin supportCard ↪o Fin n :=
      supportSet.orderEmbOfFin (k := supportCard) rfl
    intro exponents
    let positiveSupport : Finset (Fin n) :=
      Finset.univ.filter (fun i : Fin n => 0 < (exponents i : ℕ))
    intro hExponentTotal hFixedSupport
    let supportPartsBounded : Fin supportCard → Fin (k + 1) :=
      fun r : Fin supportCard => exponents (supportOrder r)
    let supportPartsNat : Fin supportCard → ℕ :=
      fun r : Fin supportCard => (supportPartsBounded r : ℕ)
    have hOutside : ∀ i : Fin n, i ∉ supportSet → (exponents i : ℕ) = 0 := by
      intro i hi
      have hNotPositive : ¬ 0 < (exponents i : ℕ) := by
        intro hPositive
        apply hi
        rw [← hFixedSupport]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hPositive⟩
      omega
    have hPartsPositive : ∀ r : Fin supportCard, 1 ≤ supportPartsNat r := by
      intro r
      have hMember : supportOrder r ∈ supportSet :=
        Finset.orderEmbOfFin_mem supportSet rfl r
      rw [← hFixedSupport] at hMember
      exact (Finset.mem_filter.mp hMember).2
    have hSupportSum : (∑ i ∈ supportSet, (exponents i : ℕ)) = k := by
      calc
        (∑ i ∈ supportSet, (exponents i : ℕ)) =
            ∑ i : Fin n, (exponents i : ℕ) :=
          Finset.sum_subset (Finset.subset_univ supportSet)
            (fun i _ hi => hOutside i hi)
        _ = k := hExponentTotal
    have hPartsTotal : (∑ r : Fin supportCard, supportPartsNat r) = k := by
      calc
        (∑ r : Fin supportCard, supportPartsNat r) =
            ∑ i ∈ Finset.map supportOrder.toEmbedding Finset.univ, (exponents i : ℕ) := by
          rw [Finset.sum_map]
          rfl
        _ = ∑ i ∈ supportSet, (exponents i : ℕ) := by
          rw [Finset.map_orderEmbOfFin_univ]
        _ = k := hSupportSum
    have hSupportPositive : 1 ≤ supportCard := by
      by_contra hZero
      have hCardZero : supportCard = 0 := by omega
      have hEmpty : supportSet = ∅ := Finset.card_eq_zero.mp hCardZero
      have hKZero : k = 0 := by simpa [hEmpty] using hSupportSum.symm
      omega
    have hSupportLE : supportCard ≤ k := by
      calc
        supportCard = ∑ r : Fin supportCard, (1 : ℕ) := by simp
        _ ≤ ∑ r : Fin supportCard, supportPartsNat r :=
          Finset.sum_le_sum (fun r _ => hPartsPositive r)
        _ = k := hPartsTotal
    have hProduct : (∏ i : Fin n, (exponents i : ℕ).factorial) =
        ∏ r : Fin supportCard, (supportPartsNat r).factorial := by
      calc
        (∏ i : Fin n, (exponents i : ℕ).factorial) =
            ∏ i ∈ supportSet, (exponents i : ℕ).factorial := by
          symm
          exact Finset.prod_subset (Finset.subset_univ supportSet)
            (fun i _ hi => by rw [hOutside i hi, Nat.factorial_zero])
        _ = ∏ i ∈ Finset.map supportOrder.toEmbedding Finset.univ,
              (exponents i : ℕ).factorial := by rw [Finset.map_orderEmbOfFin_univ]
        _ = ∏ r : Fin supportCard, (supportPartsNat r).factorial := by
          rw [Finset.prod_map]
          rfl
    refine ⟨hSupportPositive, hSupportLE, ?_⟩
    rw [hProduct]
    exact (positive_factorial_prod_le k supportCard supportPartsNat hSupportPositive
      hPartsPositive hPartsTotal).trans (factorial_tail_le_pow k supportCard hSupportPositive hSupportLE)
  have hProductRpow : ∀ (exponents : Fin n → Fin (k + 1)) (s : Finset (Fin n)),
      (∏ i ∈ s, ((exponents i : ℕ).factorial : ℝ) ^ (a - 1)) =
        (∏ i ∈ s, ((exponents i : ℕ).factorial : ℝ)) ^ (a - 1) := by
    intro exponents s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.prod_insert hi, Real.mul_rpow
          (Nat.cast_nonneg _) (Finset.prod_nonneg (fun t _ => Nat.cast_nonneg _)), ih]
  have hWeight : ∀ (supportSet : Finset (Fin n))
      (exponents : Fin n → Fin (k + 1)),
      (∑ i : Fin n, (exponents i : ℕ)) = k →
      Finset.univ.filter (fun i : Fin n => 0 < (exponents i : ℕ)) = supportSet →
      (k.factorial : ℝ) * (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ) ^ (a - 1)) ≤
        (k.factorial : ℝ) * ((k : ℝ) ^ (a - 1)) ^ (k - supportSet.card) := by
    intro supportSet exponents hExponentTotal hFixedSupport
    have hFactorialBound : (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ)) ≤
        (k : ℝ) ^ (k - supportSet.card) := by
      exact_mod_cast (hSupport supportSet exponents hExponentTotal hFixedSupport).2.2
    rw [hProductRpow]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    calc
      (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ)) ^ (a - 1) ≤
          ((k : ℝ) ^ (k - supportSet.card)) ^ (a - 1) :=
        Real.rpow_le_rpow (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _))
          hFactorialBound hExcess
      _ = ((k : ℝ) ^ (a - 1)) ^ (k - supportSet.card) :=
        (Real.rpow_pow_comm (Nat.cast_nonneg _) _ _).symm
  have hFiberCard : ∀ (supportSet : Finset (Fin n)),
      1 ≤ supportSet.card →
      (((exponentUniverse.filter (fun exponents : Fin n → Fin (k + 1) =>
        (∑ i : Fin n, (exponents i : ℕ)) = k)).filter
          (fun exponents : Fin n → Fin (k + 1) =>
            Finset.univ.filter (fun i : Fin n => 0 < (exponents i : ℕ)) = supportSet)).card) ≤
        (k - 1).choose (supportSet.card - 1) := by
    intro supportSet hSupportPositive
    let supportCard : ℕ := supportSet.card
    let supportOrder : Fin supportCard ↪o Fin n :=
      supportSet.orderEmbOfFin (k := supportCard) rfl
    have hMap : Set.MapsTo
        (fun exponents : Fin n → Fin (k + 1) =>
          fun r : Fin supportCard => exponents (supportOrder r))
        (((exponentUniverse.filter (fun exponents : Fin n → Fin (k + 1) =>
          (∑ i : Fin n, (exponents i : ℕ)) = k)).filter
            (fun exponents : Fin n → Fin (k + 1) =>
              Finset.univ.filter (fun i : Fin n => 0 < (exponents i : ℕ)) = supportSet)) :
              Set (Fin n → Fin (k + 1)))
        (((Finset.univ : Finset (Fin supportCard → Fin (k + 1))).filter
          (fun composition : Fin supportCard → Fin (k + 1) =>
            (∀ r : Fin supportCard, 0 < (composition r : ℕ)) ∧
              (∑ r : Fin supportCard, (composition r : ℕ)) = k)) :
                Set (Fin supportCard → Fin (k + 1))) := by
      intro exponents hMembership
      have hExponentTotal : (∑ i : Fin n, (exponents i : ℕ)) = k :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hMembership).1).2
      have hFixedSupport :
          Finset.univ.filter (fun i : Fin n => 0 < (exponents i : ℕ)) = supportSet :=
        (Finset.mem_filter.mp hMembership).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro r
        have hMember : supportOrder r ∈ supportSet :=
          Finset.orderEmbOfFin_mem supportSet rfl r
        rw [← hFixedSupport] at hMember
        exact (Finset.mem_filter.mp hMember).2
      · calc
          (∑ r : Fin supportCard, (exponents (supportOrder r) : ℕ)) =
              ∑ i ∈ Finset.map supportOrder.toEmbedding Finset.univ, (exponents i : ℕ) := by
            rw [Finset.sum_map]
            rfl
          _ = ∑ i ∈ supportSet, (exponents i : ℕ) := by
            rw [Finset.map_orderEmbOfFin_univ]
          _ = ∑ i : Fin n, (exponents i : ℕ) := by
            exact Finset.sum_subset (Finset.subset_univ supportSet) (by
              intro i hi hNotMember
              have hNotPositive : ¬ 0 < (exponents i : ℕ) := by
                intro hPositive
                apply hNotMember
                rw [← hFixedSupport]
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hPositive⟩
              omega)
          _ = k := hExponentTotal
    have hInjective :
        ((((exponentUniverse.filter (fun exponents : Fin n → Fin (k + 1) =>
          (∑ i : Fin n, (exponents i : ℕ)) = k)).filter
            (fun exponents : Fin n → Fin (k + 1) =>
              Finset.univ.filter (fun i : Fin n => 0 < (exponents i : ℕ)) = supportSet)) :
                Set (Fin n → Fin (k + 1))).InjOn
          (fun exponents : Fin n → Fin (k + 1) =>
            fun r : Fin supportCard => exponents (supportOrder r))) := by
      intro left hLeft right hRight hEqual
      have hLeftSupport :
          Finset.univ.filter (fun i : Fin n => 0 < (left i : ℕ)) = supportSet :=
        (Finset.mem_filter.mp hLeft).2
      have hRightSupport :
          Finset.univ.filter (fun i : Fin n => 0 < (right i : ℕ)) = supportSet :=
        (Finset.mem_filter.mp hRight).2
      funext i
      by_cases hi : i ∈ supportSet
      · have hRange : i ∈ Set.range supportOrder := by
          change i ∈ Set.range (supportSet.orderEmbOfFin (k := supportCard) rfl)
          rw [Finset.range_orderEmbOfFin]
          exact hi
        obtain ⟨r, hr⟩ := hRange
        exact hr ▸ congr_fun hEqual r
      · apply Fin.ext
        have hLeftZero : (left i : ℕ) = 0 := by
          have hNotPositive : ¬ 0 < (left i : ℕ) := by
            intro hPositive
            apply hi
            rw [← hLeftSupport]
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hPositive⟩
          omega
        have hRightZero : (right i : ℕ) = 0 := by
          have hNotPositive : ¬ 0 < (right i : ℕ) := by
            intro hPositive
            apply hi
            rw [← hRightSupport]
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hPositive⟩
          omega
        exact hLeftZero.trans hRightZero.symm
    apply le_trans (Finset.card_le_card_of_injOn
      (fun exponents : Fin n → Fin (k + 1) =>
        fun r : Fin supportCard => exponents (supportOrder r)) hMap hInjective)
    exact le_of_eq (positive_composition_count_eq k supportCard hk hSupportPositive)
  have hFiber : ∀ (supportSet : Finset (Fin n)),
      (∑ exponents ∈ (exponentUniverse.filter
          (fun exponents : Fin n → Fin (k + 1) => (∑ i : Fin n, (exponents i : ℕ)) = k)).filter
            (fun exponents : Fin n → Fin (k + 1) =>
              Finset.univ.filter (fun i : Fin n => 0 < (exponents i : ℕ)) = supportSet),
        (k.factorial : ℝ) * (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ) ^ (a - 1))) ≤
        if 1 ≤ supportSet.card ∧ supportSet.card ≤ k then
          ((k - 1).choose (supportSet.card - 1) : ℝ) * (k.factorial : ℝ) *
            ((k : ℝ) ^ (a - 1)) ^ (k - supportSet.card)
        else 0 := by
    intro supportSet
    by_cases hGood : 1 ≤ supportSet.card ∧ supportSet.card ≤ k
    · rw [if_pos hGood]
      calc
        (∑ exponents ∈ (exponentUniverse.filter
            (fun exponents : Fin n → Fin (k + 1) => (∑ i : Fin n, (exponents i : ℕ)) = k)).filter
              (fun exponents : Fin n → Fin (k + 1) =>
                Finset.univ.filter (fun i : Fin n => 0 < (exponents i : ℕ)) = supportSet),
          (k.factorial : ℝ) * (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ) ^ (a - 1))) ≤
            ∑ exponents ∈ (exponentUniverse.filter
              (fun exponents : Fin n → Fin (k + 1) => (∑ i : Fin n, (exponents i : ℕ)) = k)).filter
                (fun exponents : Fin n → Fin (k + 1) =>
                  Finset.univ.filter (fun i : Fin n => 0 < (exponents i : ℕ)) = supportSet),
              (k.factorial : ℝ) * ((k : ℝ) ^ (a - 1)) ^ (k - supportSet.card) := by
          apply Finset.sum_le_sum
          intro exponents hMembership
          exact hWeight supportSet exponents
            (Finset.mem_filter.mp (Finset.mem_filter.mp hMembership).1).2
            (Finset.mem_filter.mp hMembership).2
        _ ≤ ((k - 1).choose (supportSet.card - 1) : ℝ) * (k.factorial : ℝ) *
              ((k : ℝ) ^ (a - 1)) ^ (k - supportSet.card) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by exact_mod_cast hFiberCard supportSet hGood.1)
              (Nat.cast_nonneg _))
            (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _) _)
    · rw [if_neg hGood]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro exponents hMembership
      have hBounds : 1 ≤ supportSet.card ∧ supportSet.card ≤ k :=
        ⟨(hSupport supportSet exponents
          (Finset.mem_filter.mp (Finset.mem_filter.mp hMembership).1).2
          (Finset.mem_filter.mp hMembership).2).1,
          (hSupport supportSet exponents
          (Finset.mem_filter.mp (Finset.mem_filter.mp hMembership).1).2
          (Finset.mem_filter.mp hMembership).2).2.1⟩
      exact (hGood hBounds).elim
  have hSupportCardCount : ∀ j : ℕ,
      (((Finset.univ : Finset (Finset (Fin n))).filter
        (fun supportSet : Finset (Fin n) => supportSet.card = j)).card) = n.choose j := by
    intro j
    have hSets : (Finset.univ : Finset (Finset (Fin n))).filter
        (fun supportSet : Finset (Fin n) => supportSet.card = j) =
          Finset.powersetCard j (Finset.univ : Finset (Fin n)) := by
      ext supportSet
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_powersetCard, Finset.subset_univ, true_and]
    rw [hSets, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hRegroup :
      (∑ supportSet : Finset (Fin n),
        if 1 ≤ supportSet.card ∧ supportSet.card ≤ k then
          ((k - 1).choose (supportSet.card - 1) : ℝ) * (k.factorial : ℝ) *
            ((k : ℝ) ^ (a - 1)) ^ (k - supportSet.card) else 0) =
        ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ j then
            (n.choose j : ℝ) * ((k - 1).choose (j - 1) : ℝ) * (k.factorial : ℝ) *
              ((k : ℝ) ^ (a - 1)) ^ (k - j) else 0 := by
    have hRestrict :
        (∑ supportSet ∈ (Finset.univ : Finset (Finset (Fin n))).filter
          (fun supportSet : Finset (Fin n) => supportSet.card ∈ Finset.range (k + 1)),
          if 1 ≤ supportSet.card ∧ supportSet.card ≤ k then
            ((k - 1).choose (supportSet.card - 1) : ℝ) * (k.factorial : ℝ) *
              ((k : ℝ) ^ (a - 1)) ^ (k - supportSet.card) else 0) =
          ∑ supportSet : Finset (Fin n),
            if 1 ≤ supportSet.card ∧ supportSet.card ≤ k then
              ((k - 1).choose (supportSet.card - 1) : ℝ) * (k.factorial : ℝ) *
                ((k : ℝ) ^ (a - 1)) ^ (k - supportSet.card) else 0 := by
      exact Finset.sum_subset (Finset.filter_subset _ _) (by
        intro supportSet _ hNotMember
        have hNotLE : ¬ supportSet.card ≤ k := by
          intro hLE
          apply hNotMember
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr (by omega)⟩
        simp only [and_false, hNotLE, if_false])
    rw [← hRestrict, ← Finset.sum_fiberwise_eq_sum_filter
      (Finset.univ : Finset (Finset (Fin n))) (Finset.range (k + 1))
      (fun supportSet : Finset (Fin n) => supportSet.card)]
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
    calc
      (∑ supportSet ∈ (Finset.univ : Finset (Finset (Fin n))).filter
          (fun supportSet : Finset (Fin n) => supportSet.card = j),
        if 1 ≤ supportSet.card ∧ supportSet.card ≤ k then
          ((k - 1).choose (supportSet.card - 1) : ℝ) * (k.factorial : ℝ) *
            ((k : ℝ) ^ (a - 1)) ^ (k - supportSet.card) else 0) =
          ∑ supportSet ∈ (Finset.univ : Finset (Finset (Fin n))).filter
            (fun supportSet : Finset (Fin n) => supportSet.card = j),
            if 1 ≤ j then ((k - 1).choose (j - 1) : ℝ) * (k.factorial : ℝ) *
              ((k : ℝ) ^ (a - 1)) ^ (k - j) else 0 := by
        apply Finset.sum_congr rfl
        intro supportSet hMembership
        rw [(Finset.mem_filter.mp hMembership).2]
        simp only [hjk, and_true]
      _ = if 1 ≤ j then
            (n.choose j : ℝ) * ((k - 1).choose (j - 1) : ℝ) * (k.factorial : ℝ) *
              ((k : ℝ) ^ (a - 1)) ^ (k - j) else 0 := by
        by_cases hjPositive : 1 ≤ j
        · simp only [if_pos hjPositive, Finset.sum_const, nsmul_eq_mul, hSupportCardCount]
          ring
        · simp only [if_neg hjPositive, Finset.sum_const_zero]
  have hCost : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      (n.choose j : ℝ) * (k.factorial : ℝ) *
        ((k : ℝ) ^ (a - 1)) ^ (k - j) ≤
          (n : ℝ) ^ j * ((k : ℝ) ^ a) ^ (k - j) := by
    intro j hj hjk
    have hKPositive : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
    have hJFactorial : 0 < (j.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos j)
    have hNNonneg : 0 ≤ (n : ℝ) ^ j := pow_nonneg (Nat.cast_nonneg n) j
    have hExcessNonneg : 0 ≤ ((k : ℝ) ^ (a - 1)) ^ (k - j) :=
      pow_nonneg (Real.rpow_nonneg hKPositive.le _) _
    have hKPowers : (k : ℝ) * (k : ℝ) ^ (a - 1) = (k : ℝ) ^ a := by
      rw [Real.rpow_sub_one (ne_of_gt hKPositive)]
      field_simp
    calc
      (n.choose j : ℝ) * (k.factorial : ℝ) * ((k : ℝ) ^ (a - 1)) ^ (k - j) ≤
          ((n : ℝ) ^ j / (j.factorial : ℝ)) * (k.factorial : ℝ) *
            ((k : ℝ) ^ (a - 1)) ^ (k - j) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (choose_le_pow_div_factorial n j) (Nat.cast_nonneg _))
          hExcessNonneg
      _ = (n : ℝ) ^ j * ((k.factorial : ℝ) / (j.factorial : ℝ)) *
          ((k : ℝ) ^ (a - 1)) ^ (k - j) := by ring
      _ ≤ (n : ℝ) ^ j * (k : ℝ) ^ (k - j) *
          ((k : ℝ) ^ (a - 1)) ^ (k - j) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (factorial_ratio_le_pow k j hjk) hNNonneg) hExcessNonneg
      _ = (n : ℝ) ^ j * ((k : ℝ) ^ a) ^ (k - j) := by
        rw [mul_assoc, ← mul_pow, hKPowers]
  have hGeometric : ∀ r : ℕ,
      (∑ j ∈ Finset.range (r + 1), (n : ℝ) ^ j * ((k : ℝ) ^ a) ^ (r - j)) ≤
        ((n : ℝ) + (k : ℝ) ^ a) ^ r := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
        have hShift :
            (∑ j ∈ Finset.range (r + 1),
              (n : ℝ) ^ j * ((k : ℝ) ^ a) ^ (r + 1 - j)) =
              (k : ℝ) ^ a *
                (∑ j ∈ Finset.range (r + 1), (n : ℝ) ^ j * ((k : ℝ) ^ a) ^ (r - j)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          have hjr : j ≤ r := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
          have hSubtract : r + 1 - j = (r - j) + 1 := by omega
          rw [hSubtract, pow_succ]
          ring
        have hBasePower : (n : ℝ) ^ r ≤ ((n : ℝ) + (k : ℝ) ^ a) ^ r := by
          gcongr
          exact le_add_of_nonneg_right (Real.rpow_nonneg (Nat.cast_nonneg k) a)
        calc
          (∑ j ∈ Finset.range (r + 1 + 1), (n : ℝ) ^ j * ((k : ℝ) ^ a) ^ (r + 1 - j)) =
              (k : ℝ) ^ a *
                (∑ j ∈ Finset.range (r + 1), (n : ℝ) ^ j * ((k : ℝ) ^ a) ^ (r - j)) +
                  (n : ℝ) ^ (r + 1) := by
            rw [Finset.sum_range_succ, hShift, Nat.sub_self, pow_zero, mul_one]
          _ ≤ (k : ℝ) ^ a * ((n : ℝ) + (k : ℝ) ^ a) ^ r +
              (n : ℝ) * ((n : ℝ) + (k : ℝ) ^ a) ^ r := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left ih (Real.rpow_nonneg (Nat.cast_nonneg k) a)
            · rw [pow_succ']
              exact mul_le_mul_of_nonneg_left hBasePower (Nat.cast_nonneg n)
          _ = ((n : ℝ) + (k : ℝ) ^ a) ^ (r + 1) := by
            rw [pow_succ]
            ring
  have hChooseBound : ∀ (u v : ℕ), u.choose v ≤ 2 ^ u := by
    intro u v
    have hSubset : Finset.powersetCard v (Finset.univ : Finset (Fin u)) ⊆
        Finset.powerset (Finset.univ : Finset (Fin u)) := by
      intro supportSet hMembership
      exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hMembership).1
    have hCount : (Finset.powersetCard v (Finset.univ : Finset (Fin u))).card ≤
        (Finset.powerset (Finset.univ : Finset (Fin u))).card :=
      Finset.card_le_card hSubset
    simpa only [Finset.card_powersetCard, Finset.card_powerset,
      Finset.card_univ, Fintype.card_fin] using hCount
  have hCompositionBound : ∀ j : ℕ, ((k - 1).choose (j - 1) : ℝ) ≤ (2 : ℝ) ^ k := by
    intro j
    have hNatBound : (k - 1).choose (j - 1) ≤ 2 ^ k :=
      (hChooseBound (k - 1) (j - 1)).trans
        (by
          calc
            (2 : ℕ) ^ (k - 1) ≤ 2 ^ (k - 1) * 2 := by omega
            _ = 2 ^ k := by rw [← pow_succ]; congr 1; omega)
    exact_mod_cast hNatBound
  calc
    (∑ m : Fin n → Fin (k + 1),
      if (∑ i : Fin n, (m i : ℕ)) = k then
        (k.factorial : ℝ) * (∏ i : Fin n, ((m i : ℕ).factorial : ℝ) ^ (a - 1)) else 0) =
        ∑ exponents ∈ exponentUniverse.filter
          (fun exponents : Fin n → Fin (k + 1) => (∑ i : Fin n, (exponents i : ℕ)) = k),
          (k.factorial : ℝ) * (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ) ^ (a - 1)) := by
      rw [Finset.sum_filter]
    _ = ∑ supportSet : Finset (Fin n),
          ∑ exponents ∈ (exponentUniverse.filter
            (fun exponents : Fin n → Fin (k + 1) => (∑ i : Fin n, (exponents i : ℕ)) = k)).filter
              (fun exponents : Fin n → Fin (k + 1) =>
                Finset.univ.filter (fun i : Fin n => 0 < (exponents i : ℕ)) = supportSet),
            (k.factorial : ℝ) * (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ) ^ (a - 1)) := by
      symm
      exact Finset.sum_fiberwise _
        (fun exponents : Fin n → Fin (k + 1) =>
          Finset.univ.filter (fun i : Fin n => 0 < (exponents i : ℕ))) _
    _ ≤ ∑ supportSet : Finset (Fin n),
          if 1 ≤ supportSet.card ∧ supportSet.card ≤ k then
            ((k - 1).choose (supportSet.card - 1) : ℝ) * (k.factorial : ℝ) *
              ((k : ℝ) ^ (a - 1)) ^ (k - supportSet.card) else 0 :=
      Finset.sum_le_sum (fun supportSet _ => hFiber supportSet)
    _ = ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ j then
            (n.choose j : ℝ) * ((k - 1).choose (j - 1) : ℝ) * (k.factorial : ℝ) *
              ((k : ℝ) ^ (a - 1)) ^ (k - j) else 0 := hRegroup
    _ ≤ ∑ j ∈ Finset.range (k + 1),
          (2 : ℝ) ^ k * ((n : ℝ) ^ j * ((k : ℝ) ^ a) ^ (k - j)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
      by_cases hjPositive : 1 ≤ j
      · rw [if_pos hjPositive]
        calc
          (n.choose j : ℝ) * ((k - 1).choose (j - 1) : ℝ) * (k.factorial : ℝ) *
              ((k : ℝ) ^ (a - 1)) ^ (k - j) =
            ((k - 1).choose (j - 1) : ℝ) *
              ((n.choose j : ℝ) * (k.factorial : ℝ) *
                ((k : ℝ) ^ (a - 1)) ^ (k - j)) := by ring
          _ ≤ (2 : ℝ) ^ k *
              ((n.choose j : ℝ) * (k.factorial : ℝ) *
                ((k : ℝ) ^ (a - 1)) ^ (k - j)) :=
            mul_le_mul_of_nonneg_right (hCompositionBound j)
              (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
                (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _) _))
          _ ≤ (2 : ℝ) ^ k * ((n : ℝ) ^ j * ((k : ℝ) ^ a) ^ (k - j)) :=
            mul_le_mul_of_nonneg_left (hCost j hjPositive hjk) (by positivity)
      · rw [if_neg hjPositive]
        positivity
    _ = (2 : ℝ) ^ k *
          (∑ j ∈ Finset.range (k + 1), (n : ℝ) ^ j * ((k : ℝ) ^ a) ^ (k - j)) := by
      rw [Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ k * ((n : ℝ) + (k : ℝ) ^ a) ^ k :=
      mul_le_mul_of_nonneg_left (hGeometric k) (by positivity)
    _ = (2 * ((n : ℝ) + (k : ℝ) ^ a)) ^ k := by rw [mul_pow]

private theorem coordinate_sum_measurable_nonneg
    {Ω : Type u} [MeasurableSpace Ω]
    (n : ℕ) (μ : Fin n → Measure Ω)
    (hμ : ∀ i : Fin n, IsProbabilityMeasure (μ i))
    (Y : Fin n → Ω → ℝ)
    (hY : ∀ i : Fin n, Measurable (Y i))
    (hYnonneg : ∀ i : Fin n, ∀ᵐ ω ∂(μ i), 0 ≤ Y i ω) :
    Measurable (coordinateSum Y) ∧
      (∀ᵐ x : Fin n → Ω ∂(Measure.pi μ), 0 ≤ coordinateSum Y x) := by
  classical
  letI instMeasurableAlias : MeasurableSpace Ω := inferInstance
  let sampleMeasure : Measure (Fin n → Ω) := Measure.pi μ
  let sampleSum : (Fin n → Ω) → ℝ := coordinateSum Y
  letI instCoordinateProbability : ∀ i : Fin n, IsProbabilityMeasure (μ i) := hμ
  letI instCoordinateSigmaFinite : ∀ i : Fin n, SigmaFinite (μ i) := fun i : Fin n => inferInstance
  letI instProductProbability : IsProbabilityMeasure (Measure.pi μ) := inferInstance
  constructor
  · exact Finset.measurable_sum Finset.univ
      (fun i _ => (hY i).comp (measurable_pi_apply i))
  · have hCoordinates : ∀ᵐ x : Fin n → Ω ∂(Measure.pi μ), ∀ i : Fin n, 0 ≤ Y i (x i) := by
      rw [ae_all_iff]
      intro i
      exact (Measure.tendsto_eval_ae_ae (μ := μ) (i := i)).eventually (hYnonneg i)
    filter_upwards [hCoordinates] with x hx
    exact Finset.sum_nonneg (fun i _ => hx i)

private theorem nonneg_real_moment_mono
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f)
    (hfnn : ∀ᵐ ω ∂μ, 0 ≤ f ω)
    (p r : ℝ) (hp : 0 < p) (hpr : p ≤ r)
    (hrInt : Integrable (fun ω : Ω => (f ω) ^ r) μ) :
    Integrable (fun ω : Ω => (f ω) ^ p) μ ∧
      (∫ ω : Ω, (f ω) ^ p ∂μ) ^ (1 / p) ≤
        (∫ ω : Ω, (f ω) ^ r ∂μ) ^ (1 / r) := by
  letI instMeasurableAlias : MeasurableSpace Ω := inferInstance
  letI instMomentProbability : IsProbabilityMeasure μ := inferInstance
  have hr : 0 < r := hp.trans_le hpr
  have hp0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hr0 : ENNReal.ofReal r ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hr)
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hrTop : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
  have hrNorm : Integrable (fun ω : Ω => ‖f ω‖ ^ r) μ := by
    refine hrInt.congr ?_
    filter_upwards [hfnn] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω]
  have hMemr : MemLp f (ENNReal.ofReal r) μ := by
    apply (integrable_norm_rpow_iff hf.aestronglyMeasurable hr0 hrTop).mp
    simpa only [ENNReal.toReal_ofReal hr.le] using hrNorm
  have hMemp : MemLp f (ENNReal.ofReal p) μ :=
    hMemr.mono_exponent (ENNReal.ofReal_le_ofReal hpr)
  have hpNorm : Integrable (fun ω : Ω => ‖f ω‖ ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp.le] using hMemp.integrable_norm_rpow hp0 hpTop
  have hpInt : Integrable (fun ω : Ω => (f ω) ^ p) μ := by
    refine hpNorm.congr ?_
    filter_upwards [hfnn] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω]
  refine ⟨hpInt, ?_⟩
  have hIntegralP : (∫ ω : Ω, ‖f ω‖ ^ p ∂μ) = ∫ ω : Ω, (f ω) ^ p ∂μ := by
    apply integral_congr_ae
    filter_upwards [hfnn] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω]
  have hIntegralR : (∫ ω : Ω, ‖f ω‖ ^ r ∂μ) = ∫ ω : Ω, (f ω) ^ r ∂μ := by
    apply integral_congr_ae
    filter_upwards [hfnn] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω]
  have hCompare : eLpNorm f (ENNReal.ofReal p) μ ≤ eLpNorm f (ENNReal.ofReal r) μ :=
    eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpr)
  rw [MemLp.eLpNorm_eq_integral_rpow_norm hp0 hpTop hMemp,
    MemLp.eLpNorm_eq_integral_rpow_norm hr0 hrTop hMemr,
    ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hr.le,
    hIntegralP, hIntegralR] at hCompare
  have hRNonneg : 0 ≤ (∫ ω : Ω, (f ω) ^ r ∂μ) := by
    apply integral_nonneg_of_ae
    filter_upwards [hfnn] with ω hω
    exact Real.rpow_nonneg hω r
  have hRRootNonneg : 0 ≤ (∫ ω : Ω, (f ω) ^ r ∂μ) ^ r⁻¹ :=
    Real.rpow_nonneg hRNonneg _
  simpa only [one_div] using (ENNReal.ofReal_le_ofReal_iff hRRootNonneg).mp hCompare

private theorem ceil_nat_bounds (q : ℝ) (hq : 1 ≤ q) :
    let k : ℕ := Nat.ceil q
    1 ≤ k ∧ q ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * q := by
  change 1 ≤ Nat.ceil q ∧ q ≤ (Nat.ceil q : ℝ) ∧ (Nat.ceil q : ℝ) ≤ 2 * q
  refine ⟨Nat.one_le_ceil_iff.mpr (lt_of_lt_of_le zero_lt_one hq), Nat.le_ceil q, ?_⟩
  have hceil : (Nat.ceil q : ℝ) < q + 1 :=
    Nat.ceil_lt_add_one (le_trans zero_le_one hq)
  exact hceil.le.trans (by linarith)

theorem sum_nat_moment_from_exp
    (β τ M0 : ℝ)
    (hβ : 0 < β) (hβone : β ≤ 1) (hτ : 0 < τ) (hM0 : 1 ≤ M0)
    {Ω : Type u} [MeasurableSpace Ω]
    (n : ℕ) (μ : Fin n → Measure Ω)
    (hμ : ∀ i : Fin n, IsProbabilityMeasure (μ i))
    (Y : Fin n → Ω → ℝ)
    (hY : ∀ i : Fin n, Measurable (Y i))
    (hYnonneg : ∀ i : Fin n, ∀ᵐ ω ∂(μ i), 0 ≤ Y i ω)
    (hYexpInt : ∀ i : Fin n,
      Integrable (fun ω : Ω => Real.exp (τ * (Y i ω) ^ β)) (μ i))
    (hYexpBound : ∀ i : Fin n,
      (∫ ω : Ω, Real.exp (τ * (Y i ω) ^ β) ∂(μ i)) ≤ M0)
    (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun x : Fin n → Ω => (coordinateSum Y x) ^ k) (Measure.pi μ) ∧
      (∫ x : Fin n → Ω, (coordinateSum Y x) ^ k ∂(Measure.pi μ)) ≤
        (2 * scalarMomentScale β τ M0 *
          ((n : ℝ) + (k : ℝ) ^ (1 / β))) ^ k := by
  classical
  letI instMeasurableAlias : MeasurableSpace Ω := inferInstance
  let reciprocalBeta : ℝ := 1 / β
  let scalarMomentK : ℝ := scalarMomentScale β τ M0
  let sampleMeasure : Measure (Fin n → Ω) := Measure.pi μ
  let sampleSum : (Fin n → Ω) → ℝ := coordinateSum Y
  letI instCoordinateProbability : ∀ i : Fin n, IsProbabilityMeasure (μ i) := hμ
  letI instCoordinateSigmaFinite : ∀ i : Fin n, SigmaFinite (μ i) := fun i : Fin n => inferInstance
  letI instProductProbability : IsProbabilityMeasure (Measure.pi μ) := inferInstance
  let exponentUniverse : Finset (Fin n → Fin (k + 1)) := Finset.univ
  have hK : 0 < scalarMomentK := (moment_scales_pos β τ M0 hβ hτ hM0).1
  have hA : 1 ≤ reciprocalBeta := by
    dsimp only [reciprocalBeta]
    apply (le_div_iff₀ hβ).mpr
    simpa only [one_mul] using hβone
  have hScalar : ∀ (exponents : Fin n → Fin (k + 1)) (coordinateIndex : Fin n),
      Integrable (fun ω : Ω => (Y coordinateIndex ω) ^ (exponents coordinateIndex : ℕ)) (μ coordinateIndex) ∧
        0 ≤ (∫ ω : Ω, (Y coordinateIndex ω) ^ (exponents coordinateIndex : ℕ) ∂(μ coordinateIndex)) ∧
        (∫ ω : Ω, (Y coordinateIndex ω) ^ (exponents coordinateIndex : ℕ) ∂(μ coordinateIndex)) ≤
          scalarMomentK ^ (exponents coordinateIndex : ℕ) *
            ((exponents coordinateIndex : ℕ).factorial : ℝ) ^ reciprocalBeta := by
    intro exponents
    let coordinatePowers : Fin n → Ω → ℝ :=
      fun (i : Fin n) (ω : Ω) => (Y i ω) ^ (exponents i : ℕ)
    let productMonomial : (Fin n → Ω) → ℝ :=
      fun x : Fin n → Ω => ∏ i : Fin n, coordinatePowers i (x i)
    intro coordinateIndex
    letI instProbabilityAtCoordinate : IsProbabilityMeasure (μ coordinateIndex) := hμ coordinateIndex
    exact scalar_nat_moment_from_exp β τ M0 hβ hτ hM0
      (μ coordinateIndex) (Y coordinateIndex) (hY coordinateIndex) (hYnonneg coordinateIndex)
      (hYexpInt coordinateIndex) (hYexpBound coordinateIndex) (exponents coordinateIndex : ℕ)
  have hProductInt : ∀ exponents : Fin n → Fin (k + 1),
      Integrable (fun x : Fin n → Ω => ∏ i : Fin n, (Y i (x i)) ^ (exponents i : ℕ)) sampleMeasure := by
    intro exponents
    exact Integrable.fintype_prod (fun i => (hScalar exponents i).1)
  have hProductBound : ∀ exponents : Fin n → Fin (k + 1),
      (∫ x : Fin n → Ω, ∏ i : Fin n, (Y i (x i)) ^ (exponents i : ℕ) ∂sampleMeasure) ≤
        ∏ i : Fin n, scalarMomentK ^ (exponents i : ℕ) *
          ((exponents i : ℕ).factorial : ℝ) ^ reciprocalBeta := by
    intro exponents
    rw [integral_fintype_prod_eq_prod (fun (i : Fin n) (ω : Ω) => (Y i ω) ^ (exponents i : ℕ))]
    exact Finset.prod_le_prod₀ (fun i _ => (hScalar exponents i).2.1)
      (fun i _ => (hScalar exponents i).2.2)
  have hNormalize : ∀ (exponents : Fin n → Fin (k + 1)),
      (∑ i : Fin n, (exponents i : ℕ)) = k →
        ((k.factorial : ℝ) / (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ))) *
          (∏ i : Fin n, scalarMomentK ^ (exponents i : ℕ) *
            ((exponents i : ℕ).factorial : ℝ) ^ reciprocalBeta) =
          scalarMomentK ^ k * ((k.factorial : ℝ) *
            (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ) ^ (reciprocalBeta - 1))) := by
    intro exponents hExponentTotal
    have hDenominator : 0 < (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ)) :=
      Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (Nat.factorial_pos (exponents i : ℕ)))
    have hFactorialPower :
        (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ) ^ reciprocalBeta) =
          (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ)) *
            (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ) ^ (reciprocalBeta - 1)) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      have hFactorial : ((exponents i : ℕ).factorial : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (exponents i : ℕ))
      rw [Real.rpow_sub_one hFactorial]
      field_simp [hFactorial]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hExponentTotal, hFactorialPower]
    field_simp [ne_of_gt hDenominator]
    <;> ring
  have hTermInt : ∀ exponents : Fin n → Fin (k + 1),
      Integrable (fun x : Fin n → Ω =>
        if (∑ i : Fin n, (exponents i : ℕ)) = k then
          ((k.factorial : ℝ) / (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ))) *
            (∏ i : Fin n, (Y i (x i)) ^ (exponents i : ℕ)) else 0) sampleMeasure := by
    intro exponents
    by_cases hExponentTotal : (∑ i : Fin n, (exponents i : ℕ)) = k
    · simpa only [if_pos hExponentTotal] using
        (hProductInt exponents).const_mul
          ((k.factorial : ℝ) / (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ)))
    · simpa only [if_neg hExponentTotal] using integrable_const (0 : ℝ)
  have hExpansion : ∀ x : Fin n → Ω, (sampleSum x) ^ k =
      ∑ exponents : Fin n → Fin (k + 1),
        if (∑ i : Fin n, (exponents i : ℕ)) = k then
          ((k.factorial : ℝ) / (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ))) *
            (∏ i : Fin n, (Y i (x i)) ^ (exponents i : ℕ)) else 0 := by
    intro x
    exact finite_sum_pow_eq_multinomial n k (fun i : Fin n => Y i (x i))
  have hPowerInt : Integrable (fun x : Fin n → Ω => (sampleSum x) ^ k) sampleMeasure := by
    have hFiniteInt : Integrable (fun x : Fin n → Ω =>
        ∑ exponents : Fin n → Fin (k + 1),
          if (∑ i : Fin n, (exponents i : ℕ)) = k then
            ((k.factorial : ℝ) / (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ))) *
              (∏ i : Fin n, (Y i (x i)) ^ (exponents i : ℕ)) else 0) sampleMeasure :=
      integrable_finsetSum Finset.univ (fun exponents _ => hTermInt exponents)
    exact hFiniteInt.congr (Filter.Eventually.of_forall (fun x => (hExpansion x).symm))
  have hTermBound : ∀ exponents : Fin n → Fin (k + 1),
      (∫ x : Fin n → Ω,
        (if (∑ i : Fin n, (exponents i : ℕ)) = k then
          ((k.factorial : ℝ) / (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ))) *
            (∏ i : Fin n, (Y i (x i)) ^ (exponents i : ℕ)) else 0) ∂sampleMeasure) ≤
        scalarMomentK ^ k *
          (if (∑ i : Fin n, (exponents i : ℕ)) = k then
            (k.factorial : ℝ) *
              (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ) ^ (reciprocalBeta - 1)) else 0) := by
    intro exponents
    by_cases hExponentTotal : (∑ i : Fin n, (exponents i : ℕ)) = k
    · simp only [if_pos hExponentTotal, integral_const_mul]
      exact (mul_le_mul_of_nonneg_left (hProductBound exponents) (by positivity)).trans_eq
        (hNormalize exponents hExponentTotal)
    · simp only [if_neg hExponentTotal, integral_zero, mul_zero, le_refl]
  refine ⟨hPowerInt, ?_⟩
  calc
    (∫ x : Fin n → Ω, (sampleSum x) ^ k ∂sampleMeasure) =
        ∑ exponents : Fin n → Fin (k + 1), ∫ x : Fin n → Ω,
          (if (∑ i : Fin n, (exponents i : ℕ)) = k then
            ((k.factorial : ℝ) / (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ))) *
              (∏ i : Fin n, (Y i (x i)) ^ (exponents i : ℕ)) else 0) ∂sampleMeasure := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hExpansion),
        integral_finsetSum Finset.univ (fun exponents _ => hTermInt exponents)]
    _ ≤ ∑ exponents : Fin n → Fin (k + 1), scalarMomentK ^ k *
        (if (∑ i : Fin n, (exponents i : ℕ)) = k then
          (k.factorial : ℝ) *
            (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ) ^ (reciprocalBeta - 1)) else 0) :=
      Finset.sum_le_sum (fun exponents _ => hTermBound exponents)
    _ = scalarMomentK ^ k * (∑ exponents : Fin n → Fin (k + 1),
        if (∑ i : Fin n, (exponents i : ℕ)) = k then
          (k.factorial : ℝ) *
            (∏ i : Fin n, ((exponents i : ℕ).factorial : ℝ) ^ (reciprocalBeta - 1)) else 0) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ scalarMomentK ^ k * (2 * ((n : ℝ) + (k : ℝ) ^ reciprocalBeta)) ^ k :=
      mul_le_mul_of_nonneg_left (factorial_weighted_multinomial_le n k reciprocalBeta hA hk)
        (pow_nonneg hK.le k)
    _ = (2 * scalarMomentScale β τ M0 * ((n : ℝ) + (k : ℝ) ^ (1 / β))) ^ k := by
      rw [← mul_pow]
      dsimp only [scalarMomentK, reciprocalBeta]
      congr 1
      ring

theorem sum_real_moment_from_exp
    (β τ M0 : ℝ)
    (hβ : 0 < β) (hβone : β ≤ 1) (hτ : 0 < τ) (hM0 : 1 ≤ M0)
    {Ω : Type u} [MeasurableSpace Ω]
    (n : ℕ) (μ : Fin n → Measure Ω)
    (hμ : ∀ i : Fin n, IsProbabilityMeasure (μ i))
    (Y : Fin n → Ω → ℝ)
    (hY : ∀ i : Fin n, Measurable (Y i))
    (hYnonneg : ∀ i : Fin n, ∀ᵐ ω ∂(μ i), 0 ≤ Y i ω)
    (hYexpInt : ∀ i : Fin n,
      Integrable (fun ω : Ω => Real.exp (τ * (Y i ω) ^ β)) (μ i))
    (hYexpBound : ∀ i : Fin n,
      (∫ ω : Ω, Real.exp (τ * (Y i ω) ^ β) ∂(μ i)) ≤ M0)
    (q : ℝ) (hq : 1 ≤ q) :
    Integrable (fun x : Fin n → Ω => (coordinateSum Y x) ^ q) (Measure.pi μ) ∧
      (∫ x : Fin n → Ω, (coordinateSum Y x) ^ q ∂(Measure.pi μ)) ^ (1 / q) ≤
        sumMomentScale β τ M0 * ((n : ℝ) + q ^ (1 / β)) := by
  letI instMeasurableAlias : MeasurableSpace Ω := inferInstance
  let reciprocalBeta : ℝ := 1 / β
  let scalarMomentK : ℝ := scalarMomentScale β τ M0
  let uniformMomentC : ℝ := sumMomentScale β τ M0
  let sampleMeasure : Measure (Fin n → Ω) := Measure.pi μ
  let sampleSum : (Fin n → Ω) → ℝ := coordinateSum Y
  let roundedExponent : ℕ := Nat.ceil q
  letI instCoordinateProbability : ∀ i : Fin n, IsProbabilityMeasure (μ i) := hμ
  letI instCoordinateSigmaFinite : ∀ i : Fin n, SigmaFinite (μ i) := fun i : Fin n => inferInstance
  letI instProductProbability : IsProbabilityMeasure (Measure.pi μ) := inferInstance
  have hRoundedExponentBounds : 1 ≤ roundedExponent ∧ q ≤ (roundedExponent : ℝ) ∧
      (roundedExponent : ℝ) ≤ 2 * q := ceil_nat_bounds q hq
  have hK : 0 < scalarMomentK := (moment_scales_pos β τ M0 hβ hτ hM0).1
  have hQ : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hA : 0 ≤ reciprocalBeta := by dsimp only [reciprocalBeta]; positivity
  have hRoundedPositive : 0 < (roundedExponent : ℝ) :=
    Nat.cast_pos.mpr hRoundedExponentBounds.1
  have hSum : Measurable sampleSum ∧ (∀ᵐ x ∂sampleMeasure, 0 ≤ sampleSum x) :=
    coordinate_sum_measurable_nonneg n μ hμ Y hY hYnonneg
  have hIntegerMoment :
      Integrable (fun x : Fin n → Ω => (sampleSum x) ^ roundedExponent) sampleMeasure ∧
        (∫ x : Fin n → Ω, (sampleSum x) ^ roundedExponent ∂sampleMeasure) ≤
          (2 * scalarMomentK * ((n : ℝ) + (roundedExponent : ℝ) ^ reciprocalBeta)) ^ roundedExponent :=
    sum_nat_moment_from_exp β τ M0 hβ hβone hτ hM0 n μ hμ Y hY
      hYnonneg hYexpInt hYexpBound roundedExponent hRoundedExponentBounds.1
  have hRoundedIntegral :
      (∫ x : Fin n → Ω, (sampleSum x) ^ (roundedExponent : ℝ) ∂sampleMeasure) =
        ∫ x : Fin n → Ω, (sampleSum x) ^ roundedExponent ∂sampleMeasure := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => Real.rpow_natCast (sampleSum x) roundedExponent)
  have hRoundedIntegrable :
      Integrable (fun x : Fin n → Ω => (sampleSum x) ^ (roundedExponent : ℝ)) sampleMeasure := by
    simpa only [Real.rpow_natCast] using hIntegerMoment.1
  have hRealMoment : Integrable (fun x : Fin n → Ω => (sampleSum x) ^ q) sampleMeasure ∧
      (∫ x : Fin n → Ω, (sampleSum x) ^ q ∂sampleMeasure) ^ (1 / q) ≤
        (∫ x : Fin n → Ω, (sampleSum x) ^ (roundedExponent : ℝ) ∂sampleMeasure) ^
          (1 / (roundedExponent : ℝ)) :=
    nonneg_real_moment_mono sampleMeasure sampleSum hSum.1 hSum.2 q (roundedExponent : ℝ)
      hQ hRoundedExponentBounds.2.1 hRoundedIntegrable
  have hIntegerIntegralNonneg :
      0 ≤ (∫ x : Fin n → Ω, (sampleSum x) ^ roundedExponent ∂sampleMeasure) := by
    apply integral_nonneg_of_ae
    exact hSum.2.mono (fun x hx => pow_nonneg hx roundedExponent)
  have hBaseNonneg :
      0 ≤ 2 * scalarMomentK * ((n : ℝ) + (roundedExponent : ℝ) ^ reciprocalBeta) := by
    positivity
  have hIntegerRoot :
      (∫ x : Fin n → Ω, (sampleSum x) ^ roundedExponent ∂sampleMeasure) ^
          (1 / (roundedExponent : ℝ)) ≤
        2 * scalarMomentK * ((n : ℝ) + (roundedExponent : ℝ) ^ reciprocalBeta) := by
    calc
      _ ≤ ((2 * scalarMomentK * ((n : ℝ) + (roundedExponent : ℝ) ^ reciprocalBeta)) ^
          roundedExponent) ^ (1 / (roundedExponent : ℝ)) :=
        Real.rpow_le_rpow hIntegerIntegralNonneg hIntegerMoment.2 (by positivity)
      _ = _ := by
        simpa only [one_div] using
          Real.pow_rpow_inv_natCast hBaseNonneg (Nat.ne_of_gt hRoundedExponentBounds.1)
  have hTwoPower : 1 ≤ (2 : ℝ) ^ reciprocalBeta := Real.one_le_rpow (by norm_num) hA
  have hRoundedPower : (roundedExponent : ℝ) ^ reciprocalBeta ≤
      (2 : ℝ) ^ reciprocalBeta * q ^ reciprocalBeta := by
    have hPower : (roundedExponent : ℝ) ^ reciprocalBeta ≤ (2 * q) ^ reciprocalBeta :=
      Real.rpow_le_rpow hRoundedPositive.le hRoundedExponentBounds.2.2 hA
    simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hQ.le] using hPower
  have hScaleBound : (n : ℝ) + (roundedExponent : ℝ) ^ reciprocalBeta ≤
      (2 : ℝ) ^ reciprocalBeta * ((n : ℝ) + q ^ reciprocalBeta) := by
    have hN : (n : ℝ) ≤ (2 : ℝ) ^ reciprocalBeta * (n : ℝ) :=
      le_mul_of_one_le_left (Nat.cast_nonneg n) hTwoPower
    nlinarith
  refine ⟨hRealMoment.1, ?_⟩
  calc
    _ ≤ (∫ x : Fin n → Ω, (sampleSum x) ^ roundedExponent ∂sampleMeasure) ^
        (1 / (roundedExponent : ℝ)) := by simpa only [hRoundedIntegral] using hRealMoment.2
    _ ≤ 2 * scalarMomentK * ((n : ℝ) + (roundedExponent : ℝ) ^ reciprocalBeta) := hIntegerRoot
    _ ≤ (2 * scalarMomentK) *
        ((2 : ℝ) ^ reciprocalBeta * ((n : ℝ) + q ^ reciprocalBeta)) :=
      mul_le_mul_of_nonneg_left hScaleBound (by positivity)
    _ = sumMomentScale β τ M0 * ((n : ℝ) + q ^ (1 / β)) := by
      dsimp only [sumMomentScale, scalarMomentK, reciprocalBeta]
      ring

theorem exists_uniform_sum_real_moment_bound
    (β τ M0 : ℝ)
    (hβ : 0 < β) (hβone : β ≤ 1) (hτ : 0 < τ) (hM0 : 1 ≤ M0) :
    ∃ C : ℝ, 0 < C ∧ C = sumMomentScale β τ M0 ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω]
        (n : ℕ) (μ : Fin n → Measure Ω)
        (hμ : ∀ i : Fin n, IsProbabilityMeasure (μ i))
        (Y : Fin n → Ω → ℝ)
        (hY : ∀ i : Fin n, Measurable (Y i))
        (hYnonneg : ∀ i : Fin n, ∀ᵐ ω ∂(μ i), 0 ≤ Y i ω)
        (hYexpInt : ∀ i : Fin n,
          Integrable (fun ω : Ω => Real.exp (τ * (Y i ω) ^ β)) (μ i))
        (hYexpBound : ∀ i : Fin n,
          (∫ ω : Ω, Real.exp (τ * (Y i ω) ^ β) ∂(μ i)) ≤ M0)
        (q : ℝ) (hq : 1 ≤ q),
        Integrable (fun x : Fin n → Ω => (coordinateSum Y x) ^ q) (Measure.pi μ) ∧
          (∫ x : Fin n → Ω, (coordinateSum Y x) ^ q ∂(Measure.pi μ)) ^ (1 / q) ≤
            C * ((n : ℝ) + q ^ (1 / β)) := by
  let uniformMomentC : ℝ := sumMomentScale β τ M0
  refine ⟨uniformMomentC, (moment_scales_pos β τ M0 hβ hτ hM0).2, rfl, ?_⟩
  intro Ω instMeasurableIntroduced n μ hμ Y hY hYnonneg hYexpInt hYexpBound q hq
  exact sum_real_moment_from_exp β τ M0 hβ hβone hτ hM0 n μ hμ Y hY
    hYnonneg hYexpInt hYexpBound q hq


end

end Shao.OQ6.StretchedExponentialSumMoments
