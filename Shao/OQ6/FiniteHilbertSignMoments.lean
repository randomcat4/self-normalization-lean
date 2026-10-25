import Shao.Probability.RademacherGrid
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false

namespace Shao.OQ6.FiniteHilbertSignMoments

noncomputable section

open MeasureTheory
open scoped BigOperators

def signValue (b : Bool) : ℝ := if b then 1 else -1

def signPath (n : ℕ) (s : Fin n → Bool) : Shao.Path n := fun j : Fin n => signValue (s j)

def cubeMean (n : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ := ((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool, f s

def signSum (n : ℕ) (d : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)) (s : Fin n → Bool) : EuclideanSpace ℝ (Fin d) := ∑ j : Fin n, signValue (s j) • v j

def pathSum (n : ℕ) (d : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)) (w : Shao.Path n) : EuclideanSpace ℝ (Fin d) := ∑ j : Fin n, w j • v j

def energy (n : ℕ) (d : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)) : ℝ := ∑ j : Fin n, ‖v j‖ ^ 2

def moment (n : ℕ) (d : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)) (q : ℝ) : ℝ := cubeMean n (fun s : Fin n → Bool => Real.rpow ‖signSum n d v s‖ q)

def hilbertConstant : ℝ := 2

private def scalarSignSum (n : ℕ) (a : Fin n → ℝ) (s : Fin n → Bool) : ℝ := ∑ j : Fin n, signValue (s j) * a j

private def pairCount (n : ℕ) (k : ℕ) (t : Fin k → Fin n × Fin n) (j : Fin n) : ℕ := ∑ r : Fin k, ((if (t r).1 = j then 1 else 0) + (if (t r).2 = j then 1 else 0))

private def evenPairs (n : ℕ) (k : ℕ) (t : Fin k → Fin n × Fin n) : Prop := ∀ j : Fin n, Even (pairCount n k t j)

private def pairSign (n : ℕ) (k : ℕ) (s : Fin n → Bool) (t : Fin k → Fin n × Fin n) : ℝ := ∏ r : Fin k, signValue (s (t r).1) * signValue (s (t r).2)

private def pairInner (n : ℕ) (d : ℕ) (k : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)) (t : Fin k → Fin n × Fin n) : ℝ := ∏ r : Fin k, inner ℝ (v (t r).1) (v (t r).2)

private def allocations (n : ℕ) (k : ℕ) : Finset (Fin n → Fin (k + 1)) := Finset.univ.filter (fun ell : Fin n → Fin (k + 1) => (∑ j : Fin n, (ell j).val) = k)

private def evenFactor (k : ℕ) : ℝ := (Nat.factorial (2 * k) : ℝ) / ((2 : ℝ) ^ k * (Nat.factorial k : ℝ))

private theorem cubeMean_product (n : ℕ) (h : Fin n → Bool → ℝ) : cubeMean n (fun s : Fin n → Bool => ∏ j : Fin n, h j (s j)) = ∏ j : Fin n, (h j true + h j false) / 2 := by
  classical
  have hbool : ∀ j : Fin n, (∑ b : Bool, h j b) = h j true + h j false := by
    intro j
    simp [Fintype.sum_bool, add_comm]
  unfold cubeMean
  calc
    ((2 : ℝ) ^ n)⁻¹ * (∑ s : Fin n → Bool, ∏ j : Fin n, h j (s j)) =
        ((2 : ℝ) ^ n)⁻¹ * ∏ j : Fin n, ∑ b : Bool, h j b := by
      rw [Fintype.prod_sum]
    _ = ((2 : ℝ) ^ n)⁻¹ * ∏ j : Fin n, (h j true + h j false) := by
      simp only [hbool]
    _ = ∏ j : Fin n, (h j true + h j false) / 2 := by
      rw [Finset.prod_div_distrib, Fin.prod_const]
      ring

private theorem sign_power_mean (n : ℕ) (e : Fin n → ℕ) : cubeMean n (fun s : Fin n → Bool => ∏ j : Fin n, signValue (s j) ^ e j) = if (∀ j : Fin n, Even (e j)) then 1 else 0 := by
  classical
  let h : Fin n → Bool → ℝ := fun (j : Fin n) (b : Bool) => signValue b ^ e j
  have heval : ∀ j : Fin n,
      (h j true + h j false) / 2 = if Even (e j) then 1 else 0 := by
    intro j
    by_cases he : Even (e j)
    · obtain ⟨l, hl⟩ := he
      have hekeep : Even (e j) := ⟨l, hl⟩
      have hp : (-1 : ℝ) ^ e j = 1 := by
        rw [hl, ← two_mul, pow_mul]
        norm_num
      norm_num [h, signValue, hp, hekeep]
    · have hodd : e j = 2 * (e j / 2) + 1 := by
        have hm : e j % 2 ≠ 0 := by
          intro hm
          exact he ⟨e j / 2, by omega⟩
        omega
      have hp : (-1 : ℝ) ^ e j = -1 := by
        rw [hodd, pow_add, pow_mul]
        norm_num
      norm_num [h, signValue, hp, he]
  change cubeMean n (fun s : Fin n → Bool => ∏ j : Fin n, h j (s j)) =
    if (∀ j : Fin n, Even (e j)) then 1 else 0
  rw [cubeMean_product n h]
  simp only [heval]
  by_cases he : ∀ j : Fin n, Even (e j)
  · rw [if_pos he]
    exact Finset.prod_eq_one (fun j _ => if_pos (he j))
  · obtain ⟨j, hj⟩ := not_forall.mp he
    rw [if_neg he]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

private theorem pair_sign_mean (n : ℕ) (k : ℕ) (t : Fin k → Fin n × Fin n) : cubeMean n (fun s : Fin n → Bool => pairSign n k s t) = @ite ℝ (evenPairs n k t) (Classical.propDecidable (evenPairs n k t)) 1 0 := by
  classical
  let e : Fin n → ℕ := fun j : Fin n => pairCount n k t j
  have hreg : ∀ s : Fin n → Bool,
      pairSign n k s t = ∏ j : Fin n, signValue (s j) ^ e j := by
    intro s
    dsimp only [pairSign, e, pairCount]
    symm
    simp_rw [← Finset.prod_pow_eq_pow_sum]
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro r _
    simp_rw [pow_add]
    rw [Finset.prod_mul_distrib]
    simp only [apply_ite, pow_one, pow_zero]
    simp [eq_comm]
  simp only [hreg]
  rw [sign_power_mean]
  by_cases he : ∀ j : Fin n, Even (e j)
  · have ht : evenPairs n k t := he
    simp only [if_pos he, if_pos ht]
  · have ht : ¬ evenPairs n k t := he
    simp only [if_neg he, if_neg ht]

private theorem hilbert_even_domination (n : ℕ) (d : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)) (k : ℕ) : cubeMean n (fun s : Fin n → Bool => ‖signSum n d v s‖ ^ (2 * k)) ≤ cubeMean n (fun s : Fin n → Bool => (scalarSignSum n (fun j : Fin n => ‖v j‖) s) ^ (2 * k)) := by
  classical
  let a : Fin n → ℝ := fun j : Fin n => ‖v j‖
  have hsq : ∀ s : Fin n → Bool, ‖signSum n d v s‖ ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n,
        signValue (s i) * signValue (s j) * inner ℝ (v i) (v j) := by
    intro s
    rw [← real_inner_self_eq_norm_sq (signSum n d v s)]
    simp only [signSum, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_comm (v i) (v j)]
    ring
  have hvec : ∀ s : Fin n → Bool, ‖signSum n d v s‖ ^ (2 * k) =
      ∑ t : Fin k → Fin n × Fin n, pairSign n k s t * pairInner n d k v t := by
    intro s
    rw [pow_mul, hsq s]
    have hpow :
        (∑ i : Fin n, ∑ j : Fin n,
          signValue (s i) * signValue (s j) * inner ℝ (v i) (v j)) ^ k =
        ∑ t : Fin k → Fin n × Fin n, ∏ r : Fin k,
          signValue (s (t r).1) * signValue (s (t r).2) * inner ℝ (v (t r).1) (v (t r).2) := by
      simpa only [Fintype.sum_prod_type, Function.uncurry] using
        Fintype.sum_pow (Function.uncurry (fun (i : Fin n) (j : Fin n) =>
          signValue (s i) * signValue (s j) * inner ℝ (v i) (v j))) k
    rw [hpow]
    apply Finset.sum_congr rfl
    intro t _
    dsimp only [pairSign, pairInner]
    rw [Finset.prod_mul_distrib]
  have hscalarSq : ∀ s : Fin n → Bool, scalarSignSum n a s ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n,
        signValue (s i) * signValue (s j) * (a i * a j) := by
    intro s
    rw [scalarSignSum, pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hscalar : ∀ s : Fin n → Bool, scalarSignSum n a s ^ (2 * k) =
      ∑ t : Fin k → Fin n × Fin n,
        pairSign n k s t * ∏ r : Fin k, a (t r).1 * a (t r).2 := by
    intro s
    rw [pow_mul, hscalarSq s]
    have hpow :
        (∑ i : Fin n, ∑ j : Fin n,
          signValue (s i) * signValue (s j) * (a i * a j)) ^ k =
        ∑ t : Fin k → Fin n × Fin n, ∏ r : Fin k,
          signValue (s (t r).1) * signValue (s (t r).2) * (a (t r).1 * a (t r).2) := by
      simpa only [Fintype.sum_prod_type, Function.uncurry] using
        Fintype.sum_pow (Function.uncurry (fun (i : Fin n) (j : Fin n) =>
          signValue (s i) * signValue (s j) * (a i * a j))) k
    rw [hpow]
    apply Finset.sum_congr rfl
    intro t _
    dsimp only [pairSign]
    rw [Finset.prod_mul_distrib]
  have hmeanVec : cubeMean n (fun s : Fin n → Bool => ‖signSum n d v s‖ ^ (2 * k)) =
      ∑ t : Fin k → Fin n × Fin n,
        (if evenPairs n k t then 1 else 0) * pairInner n d k v t := by
    unfold cubeMean
    simp only [hvec]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    have hps : ((2 : ℝ) ^ n)⁻¹ * (∑ s : Fin n → Bool, pairSign n k s t) =
        if evenPairs n k t then 1 else 0 := pair_sign_mean n k t
    rw [← Finset.sum_mul, ← mul_assoc, hps]
  have hmeanScalar :
      cubeMean n (fun s : Fin n → Bool => scalarSignSum n a s ^ (2 * k)) =
      ∑ t : Fin k → Fin n × Fin n,
        (if evenPairs n k t then 1 else 0) * ∏ r : Fin k, a (t r).1 * a (t r).2 := by
    unfold cubeMean
    simp only [hscalar]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    have hps : ((2 : ℝ) ^ n)⁻¹ * (∑ s : Fin n → Bool, pairSign n k s t) =
        if evenPairs n k t then 1 else 0 := pair_sign_mean n k t
    rw [← Finset.sum_mul, ← mul_assoc, hps]
  change cubeMean n (fun s : Fin n → Bool => ‖signSum n d v s‖ ^ (2 * k)) ≤
    cubeMean n (fun s : Fin n → Bool => scalarSignSum n a s ^ (2 * k))
  rw [hmeanVec, hmeanScalar]
  apply Finset.sum_le_sum
  intro t _
  by_cases ht : evenPairs n k t
  · simp only [if_pos ht, one_mul]
    calc
      pairInner n d k v t ≤ |pairInner n d k v t| := le_abs_self _
      _ = ∏ r : Fin k, |inner ℝ (v (t r).1) (v (t r).2)| := by
        simp only [pairInner, Finset.abs_prod]
      _ ≤ ∏ r : Fin k, a (t r).1 * a (t r).2 :=
        Finset.prod_le_prod₀ (fun r _ => abs_nonneg _)
          (fun r _ => by
            simpa only [a, Real.norm_eq_abs] using
              norm_inner_le_norm (𝕜 := ℝ) (v (t r).1) (v (t r).2))
  · simp only [if_neg ht, zero_mul, le_refl]

private theorem scalar_even_multinomial (n : ℕ) (a : Fin n → ℝ) (k : ℕ) : cubeMean n (fun s : Fin n → Bool => (scalarSignSum n a s) ^ (2 * k)) = ∑ ell ∈ allocations n k, ((Nat.factorial (2 * k) : ℝ) / ∏ j : Fin n, (Nat.factorial (2 * (ell j).val) : ℝ)) * ∏ j : Fin n, a j ^ (2 * (ell j).val) := by
  classical
  let toEven : (Fin n → Fin (k + 1)) → Fin n → ℕ := fun (ell : Fin n → Fin (k + 1)) (j : Fin n) => 2 * (ell j).val
  let fromEven : (Fin n → ℕ) → Fin n → Fin (k + 1) := fun (m : Fin n → ℕ) (j : Fin n) => ⟨(m j / 2) % (k + 1), Nat.mod_lt (m j / 2) (Nat.succ_pos k)⟩
  have hmult : ∀ s : Fin n → Bool, (scalarSignSum n a s) ^ (2 * k) =
      ∑ m ∈ Finset.piAntidiag Finset.univ (2 * k),
        (Nat.multinomial Finset.univ m : ℝ) *
          (∏ j : Fin n, signValue (s j) ^ m j) * ∏ j : Fin n, a j ^ m j := by
    intro s
    rw [scalarSignSum, Finset.sum_pow_eq_sum_piAntidiag]
    apply Finset.sum_congr rfl
    intro m _
    simp only [mul_pow, Finset.prod_mul_distrib]
    ring
  have hmean : cubeMean n (fun s : Fin n → Bool => (scalarSignSum n a s) ^ (2 * k)) =
      ∑ m ∈ Finset.piAntidiag Finset.univ (2 * k),
        (Nat.multinomial Finset.univ m : ℝ) *
          (if (∀ j : Fin n, Even (m j)) then 1 else 0) * ∏ j : Fin n, a j ^ m j := by
    unfold cubeMean
    simp only [hmult]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    have hsmean : ((2 : ℝ) ^ n)⁻¹ *
        (∑ s : Fin n → Bool, ∏ j : Fin n, signValue (s j) ^ m j) =
          if (∀ j : Fin n, Even (m j)) then 1 else 0 := sign_power_mean n m
    calc
      ((2 : ℝ) ^ n)⁻¹ *
          (∑ s : Fin n → Bool, (Nat.multinomial Finset.univ m : ℝ) *
            (∏ j : Fin n, signValue (s j) ^ m j) * ∏ j : Fin n, a j ^ m j) =
          (Nat.multinomial Finset.univ m : ℝ) *
            (((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool, ∏ j : Fin n, signValue (s j) ^ m j) *
              ∏ j : Fin n, a j ^ m j := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        ring
      _ = (Nat.multinomial Finset.univ m : ℝ) *
          (if (∀ j : Fin n, Even (m j)) then 1 else 0) * ∏ j : Fin n, a j ^ m j := by
        rw [hsmean]
  have hfilter :
      (∑ m ∈ Finset.piAntidiag Finset.univ (2 * k),
        (Nat.multinomial Finset.univ m : ℝ) *
          (if (∀ j : Fin n, Even (m j)) then 1 else 0) * ∏ j : Fin n, a j ^ m j) =
      ∑ m ∈ (Finset.piAntidiag Finset.univ (2 * k)).filter
          (fun m : Fin n → ℕ => ∀ j : Fin n, Even (m j)),
        (Nat.multinomial Finset.univ m : ℝ) * ∏ j : Fin n, a j ^ m j := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m _
    by_cases he : ∀ j : Fin n, Even (m j) <;> simp [he]
  rw [hmean, hfilter]
  symm
  apply Finset.sum_nbij' toEven fromEven
  · intro ell hell
    have hsum : (∑ j : Fin n, (ell j).val) = k := (Finset.mem_filter.mp hell).2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_piAntidiag.mpr
      constructor
      · dsimp only [toEven]
        rw [← Finset.mul_sum, hsum]
      · intro j _
        exact Finset.mem_univ j
    · intro j
      exact ⟨(ell j).val, by dsimp only [toEven]; omega⟩
  · intro m hm
    have hmAnti : m ∈ Finset.piAntidiag Finset.univ (2 * k) := (Finset.mem_filter.mp hm).1
    have hmEven : ∀ j : Fin n, Even (m j) := (Finset.mem_filter.mp hm).2
    have hsum : (∑ j : Fin n, m j) = 2 * k := (Finset.mem_piAntidiag.mp hmAnti).1
    have hhalf : ∀ j : Fin n, 2 * (m j / 2) = m j := by
      intro j
      obtain ⟨l, hl⟩ := hmEven j
      omega
    have hval : ∀ j : Fin n, (fromEven m j).val = m j / 2 := by
      intro j
      have hle : m j ≤ ∑ j : Fin n, m j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ j)
      have hh : 2 * (m j / 2) = m j := hhalf j
      exact Nat.mod_eq_of_lt (by omega)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hhalfsum : 2 * (∑ j : Fin n, m j / 2) = 2 * k := by
      rw [Finset.mul_sum]
      simpa only [hhalf] using hsum
    have hsumhalf : (∑ j : Fin n, m j / 2) = k := by omega
    simpa only [hval] using hsumhalf
  · intro ell _
    funext j
    apply Fin.ext
    change (2 * (ell j).val / 2) % (k + 1) = (ell j).val
    have hhalf : 2 * (ell j).val / 2 = (ell j).val := by omega
    rw [hhalf]
    exact Nat.mod_eq_of_lt (ell j).isLt
  · intro m hm
    have hmAnti : m ∈ Finset.piAntidiag Finset.univ (2 * k) := (Finset.mem_filter.mp hm).1
    have hmEven : ∀ j : Fin n, Even (m j) := (Finset.mem_filter.mp hm).2
    have hsum : (∑ j : Fin n, m j) = 2 * k := (Finset.mem_piAntidiag.mp hmAnti).1
    funext j
    have hle : m j ≤ ∑ j : Fin n, m j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ j)
    have hhalf : 2 * (m j / 2) = m j := by
      obtain ⟨l, hl⟩ := hmEven j
      omega
    have hbnd : m j / 2 < k + 1 := by omega
    change 2 * ((m j / 2) % (k + 1)) = m j
    rw [Nat.mod_eq_of_lt hbnd]
    exact hhalf
  · intro ell hell
    have hsum : (∑ j : Fin n, (ell j).val) = k := (Finset.mem_filter.mp hell).2
    have hspec : (∏ j : Fin n, (Nat.factorial (2 * (ell j).val) : ℝ)) *
        (Nat.multinomial Finset.univ (toEven ell) : ℝ) = (Nat.factorial (2 * k) : ℝ) := by
      have hnat : (∏ j : Fin n, Nat.factorial (toEven ell j)) *
          Nat.multinomial Finset.univ (toEven ell) = Nat.factorial (2 * k) := by
        rw [Nat.multinomial_spec]
        congr 1
        dsimp only [toEven]
        rw [← Finset.mul_sum, hsum]
      exact_mod_cast hnat
    have hden : (∏ j : Fin n, (Nat.factorial (2 * (ell j).val) : ℝ)) ≠ 0 := by positivity
    have hcoeff : (Nat.multinomial Finset.univ (toEven ell) : ℝ) =
        (Nat.factorial (2 * k) : ℝ) / ∏ j : Fin n, (Nat.factorial (2 * (ell j).val) : ℝ) := by
      apply (eq_div_iff hden).mpr
      nlinarith [hspec]
    rw [hcoeff]

private theorem even_factorial_lower (l : ℕ) : (2 : ℝ) ^ l * (Nat.factorial l : ℝ) ≤ (Nat.factorial (2 * l) : ℝ) := by
  induction l with
  | zero => norm_num
  | succ l ih =>
      have hl : 0 ≤ (l : ℝ) := Nat.cast_nonneg l
      have hfac : 0 ≤ (Nat.factorial (2 * l) : ℝ) := by positivity
      have hstep : (Nat.factorial (2 * (l + 1)) : ℝ) =
          (2 * (l : ℝ) + 2) * (2 * (l : ℝ) + 1) * (Nat.factorial (2 * l) : ℝ) := by
        rw [show 2 * (l + 1) = (2 * l + 1) + 1 by omega,
          Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        ring
      rw [hstep, pow_succ, Nat.factorial_succ]
      push_cast
      calc
        (2 : ℝ) ^ l * 2 * (((l : ℝ) + 1) * (Nat.factorial l : ℝ)) =
            (2 * (l : ℝ) + 2) * ((2 : ℝ) ^ l * (Nat.factorial l : ℝ)) := by ring
        _ ≤ (2 * (l : ℝ) + 2) * (Nat.factorial (2 * l) : ℝ) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ (2 * (l : ℝ) + 2) * ((2 * (l : ℝ) + 1) * (Nat.factorial (2 * l) : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (le_mul_of_one_le_left hfac (by linarith)) (by positivity)
        _ = (2 * (l : ℝ) + 2) * (2 * (l : ℝ) + 1) * (Nat.factorial (2 * l) : ℝ) := by ring

private theorem squared_multinomial (n : ℕ) (a : Fin n → ℝ) (k : ℕ) : (∑ j : Fin n, a j ^ 2) ^ k = ∑ ell ∈ allocations n k, ((Nat.factorial k : ℝ) / ∏ j : Fin n, (Nat.factorial (ell j).val : ℝ)) * ∏ j : Fin n, (a j ^ 2) ^ (ell j).val := by
  classical
  let toNat : (Fin n → Fin (k + 1)) → Fin n → ℕ := fun (ell : Fin n → Fin (k + 1)) (j : Fin n) => (ell j).val
  let fromNat : (Fin n → ℕ) → Fin n → Fin (k + 1) := fun (m : Fin n → ℕ) (j : Fin n) => ⟨m j % (k + 1), Nat.mod_lt (m j) (Nat.succ_pos k)⟩
  rw [Finset.sum_pow_eq_sum_piAntidiag Finset.univ (fun j : Fin n => a j ^ 2) k]
  symm
  apply Finset.sum_nbij' toNat fromNat
  · intro ell hell
    apply Finset.mem_piAntidiag.mpr
    constructor
    · exact (Finset.mem_filter.mp hell).2
    · intro j _
      exact Finset.mem_univ j
  · intro m hm
    have hsum : (∑ j : Fin n, m j) = k := (Finset.mem_piAntidiag.mp hm).1
    have hval : ∀ j : Fin n, (fromNat m j).val = m j := by
      intro j
      have hle : m j ≤ ∑ j : Fin n, m j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ j)
      exact Nat.mod_eq_of_lt (by omega)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [hval] using hsum
  · intro ell _
    funext j
    apply Fin.ext
    exact Nat.mod_eq_of_lt (ell j).isLt
  · intro m hm
    have hsum : (∑ j : Fin n, m j) = k := (Finset.mem_piAntidiag.mp hm).1
    funext j
    have hle : m j ≤ ∑ j : Fin n, m j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ j)
    exact Nat.mod_eq_of_lt (by omega)
  · intro ell hell
    have hsum : (∑ j : Fin n, (ell j).val) = k := (Finset.mem_filter.mp hell).2
    have hspec : (∏ j : Fin n, (Nat.factorial (ell j).val : ℝ)) *
        (Nat.multinomial Finset.univ (toNat ell) : ℝ) = (Nat.factorial k : ℝ) := by
      have hnat : (∏ j : Fin n, Nat.factorial (toNat ell j)) *
          Nat.multinomial Finset.univ (toNat ell) = Nat.factorial k := by
        rw [Nat.multinomial_spec]
        exact congrArg Nat.factorial hsum
      exact_mod_cast hnat
    have hden : (∏ j : Fin n, (Nat.factorial (ell j).val : ℝ)) ≠ 0 := by positivity
    have hcoeff : (Nat.multinomial Finset.univ (toNat ell) : ℝ) =
        (Nat.factorial k : ℝ) / ∏ j : Fin n, (Nat.factorial (ell j).val : ℝ) := by
      apply (eq_div_iff hden).mpr
      nlinarith [hspec]
    rw [hcoeff]

private theorem evenFactor_bound (k : ℕ) : evenFactor k ≤ (2 * (k : ℝ)) ^ k := by
  induction k with
  | zero => norm_num [evenFactor]
  | succ k ih =>
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      have hfac : (Nat.factorial k : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero k
      have hpow : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
      have hkp : (k : ℝ) + 1 ≠ 0 := by positivity
      have hstep : evenFactor (k + 1) = (2 * (k : ℝ) + 1) * evenFactor k := by
        unfold evenFactor
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
          Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, pow_succ]
        push_cast
        field_simp [hfac, hpow, hkp]
        <;> ring
      calc
        evenFactor (k + 1) = (2 * (k : ℝ) + 1) * evenFactor k := hstep
        _ ≤ (2 * (k : ℝ) + 1) * (2 * (k : ℝ)) ^ k :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 2) ^ k := by
          gcongr <;> linarith
        _ = (2 * ((k + 1 : ℕ) : ℝ)) ^ (k + 1) := by
          rw [pow_succ]
          push_cast
          ring

private theorem scalar_even_bound (n : ℕ) (a : Fin n → ℝ) (k : ℕ) : cubeMean n (fun s : Fin n → Bool => (scalarSignSum n a s) ^ (2 * k)) ≤ evenFactor k * (∑ j : Fin n, a j ^ 2) ^ k := by
  classical
  rw [scalar_even_multinomial n a k, squared_multinomial n a k, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ell hell
  let denEven : ℝ := ∏ j : Fin n, (Nat.factorial (2 * (ell j).val) : ℝ)
  let denHalf : ℝ := ∏ j : Fin n, (Nat.factorial (ell j).val : ℝ)
  have hsum : (∑ j : Fin n, (ell j).val) = k := (Finset.mem_filter.mp hell).2
  have hdenEven : 0 < denEven := by dsimp only [denEven]; positivity
  have hdenHalf : 0 < denHalf := by dsimp only [denHalf]; positivity
  have htwoprod : (∏ j : Fin n, (2 : ℝ) ^ (ell j).val) = (2 : ℝ) ^ k := by
    rw [Finset.prod_pow_eq_pow_sum, hsum]
  have hden : (2 : ℝ) ^ k * denHalf ≤ denEven := by
    calc
      (2 : ℝ) ^ k * denHalf =
          ∏ j : Fin n, (2 : ℝ) ^ (ell j).val * (Nat.factorial (ell j).val : ℝ) := by
        rw [Finset.prod_mul_distrib, htwoprod]
      _ ≤ denEven := by
        dsimp only [denEven]
        exact Finset.prod_le_prod₀ (fun j _ => by positivity)
          (fun j _ => even_factorial_lower (ell j).val)
  have hcoeff : (Nat.factorial (2 * k) : ℝ) / denEven ≤
      (Nat.factorial (2 * k) : ℝ) / ((2 : ℝ) ^ k * denHalf) :=
    div_le_div_of_nonneg_left (by positivity)
      (mul_pos (by positivity) hdenHalf) hden
  have hcancel : (Nat.factorial (2 * k) : ℝ) / ((2 : ℝ) ^ k * denHalf) =
      evenFactor k * ((Nat.factorial k : ℝ) / denHalf) := by
    unfold evenFactor
    have htwo : (2 : ℝ) ^ k ≠ 0 := by positivity
    have hkfac : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    field_simp [htwo, hkfac, ne_of_gt hdenHalf]
    <;> ring
  have hpowprod : (∏ j : Fin n, a j ^ (2 * (ell j).val)) =
      ∏ j : Fin n, (a j ^ 2) ^ (ell j).val := by
    apply Finset.prod_congr rfl
    intro j _
    exact pow_mul (a j) 2 (ell j).val
  have hnum : 0 ≤ ∏ j : Fin n, a j ^ (2 * (ell j).val) := by
    rw [hpowprod]
    exact Finset.prod_nonneg (fun j _ => pow_nonneg (sq_nonneg (a j)) (ell j).val)
  change (Nat.factorial (2 * k) : ℝ) / denEven *
      (∏ j : Fin n, a j ^ (2 * (ell j).val)) ≤
    evenFactor k * (((Nat.factorial k : ℝ) / denHalf) *
      ∏ j : Fin n, (a j ^ 2) ^ (ell j).val)
  calc
    (Nat.factorial (2 * k) : ℝ) / denEven * (∏ j : Fin n, a j ^ (2 * (ell j).val)) ≤
        (Nat.factorial (2 * k) : ℝ) / ((2 : ℝ) ^ k * denHalf) *
          (∏ j : Fin n, a j ^ (2 * (ell j).val)) :=
      mul_le_mul_of_nonneg_right hcoeff hnum
    _ = evenFactor k * (((Nat.factorial k : ℝ) / denHalf) *
        ∏ j : Fin n, (a j ^ 2) ^ (ell j).val) := by
      rw [hcancel, hpowprod]
      ring

private theorem hilbert_even_bound (n : ℕ) (d : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)) (k : ℕ) : cubeMean n (fun s : Fin n → Bool => ‖signSum n d v s‖ ^ (2 * k)) ≤ (2 * (k : ℝ)) ^ k * energy n d v ^ k := by
  let a : Fin n → ℝ := fun j : Fin n => ‖v j‖
  calc
    cubeMean n (fun s : Fin n → Bool => ‖signSum n d v s‖ ^ (2 * k)) ≤
        cubeMean n (fun s : Fin n → Bool => (scalarSignSum n a s) ^ (2 * k)) := by
      simpa only [a] using hilbert_even_domination n d v k
    _ ≤ evenFactor k * (∑ j : Fin n, a j ^ 2) ^ k := scalar_even_bound n a k
    _ ≤ (2 * (k : ℝ)) ^ k * energy n d v ^ k := by
      change evenFactor k * energy n d v ^ k ≤
        (2 * (k : ℝ)) ^ k * energy n d v ^ k
      exact mul_le_mul_of_nonneg_right (evenFactor_bound k)
        (pow_nonneg (by unfold energy; positivity) k)

private theorem rpow_tangent (x : ℝ) (r : ℝ) (hx : 0 ≤ x) (hr : 0 < r) (hr1 : r ≤ 1) : Real.rpow x r ≤ (1 - r) + r * x := by
  have hc : ConcaveOn ℝ (Set.Ici 0) (fun t : ℝ => Real.rpow t r) :=
    Real.concaveOn_rpow hr.le hr1
  have hd : HasDerivAt (fun t : ℝ => Real.rpow t r) r 1 := by
    simpa only [Real.rpow_eq_pow, Real.one_rpow, mul_one] using
      Real.hasDerivAt_rpow_const (x := 1) (p := r) (Or.inl one_ne_zero)
  rcases lt_trichotomy x 1 with hlt | hEq | hgt
  · have hs : r ≤ slope (fun t : ℝ => Real.rpow t r) x 1 :=
      hc.le_slope_of_hasDerivAt hx (by norm_num) hlt hd
    simp only [slope_def_field, Real.rpow_eq_pow, Real.one_rpow] at hs
    have hnum : r * (1 - x) ≤ 1 - Real.rpow x r := by
      simpa only [Real.rpow_eq_pow] using
        (le_div_iff₀ (sub_pos.mpr hlt)).mp hs
    linarith
  · subst x
    simp only [Real.rpow_eq_pow, Real.one_rpow]
    linarith
  · have hs : slope (fun t : ℝ => Real.rpow t r) 1 x ≤ r :=
      hc.slope_le_of_hasDerivAt (by norm_num) hx hgt hd
    simp only [slope_def_field, Real.rpow_eq_pow, Real.one_rpow] at hs
    have hnum : Real.rpow x r - 1 ≤ r * (x - 1) := by
      simpa only [Real.rpow_eq_pow] using
        (div_le_iff₀ (sub_pos.mpr hgt)).mp hs
    linarith

private theorem cubeMean_rpow_le (n : ℕ) (f : (Fin n → Bool) → ℝ) (r : ℝ) (hf : ∀ s : Fin n → Bool, 0 ≤ f s) (hr : 0 < r) (hr1 : r ≤ 1) : cubeMean n (fun s : Fin n → Bool => Real.rpow (f s) r) ≤ Real.rpow (cubeMean n f) r := by
  let B : ℝ := cubeMean n f
  have hB : 0 ≤ B := by
    dsimp only [B, cubeMean]
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) n))
      (Finset.sum_nonneg (fun s _ => hf s))
  by_cases hB0 : B = 0
  · have hsum0 : (∑ s : Fin n → Bool, f s) = 0 := by
      have hz : ((2 : ℝ) ^ n)⁻¹ * (∑ s : Fin n → Bool, f s) = 0 := hB0
      exact (mul_eq_zero.mp hz).resolve_left (by positivity)
    have hf0 : ∀ s : Fin n → Bool, f s = 0 := by
      intro s
      have hle : f s ≤ ∑ s : Fin n → Bool, f s :=
        Finset.single_le_sum (fun s _ => hf s) (Finset.mem_univ s)
      exact le_antisymm (hle.trans_eq hsum0) (hf s)
    simp only [cubeMean, hf0, Real.rpow_eq_pow, Real.zero_rpow (ne_of_gt hr), Finset.sum_const_zero,
      mul_zero, le_refl]
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    let g : (Fin n → Bool) → ℝ := fun s : Fin n → Bool => f s / B
    have hg : ∀ s : Fin n → Bool, 0 ≤ g s := by
      intro s
      exact div_nonneg (hf s) hBpos.le
    have hcard : ((2 : ℝ) ^ n)⁻¹ * (Fintype.card (Fin n → Bool) : ℝ) = 1 := by
      simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
        Nat.cast_ofNat]
      exact inv_mul_cancel₀ (by positivity)
    have hmean : cubeMean n g = 1 := by
      unfold cubeMean
      dsimp only [g]
      rw [← Finset.sum_div, ← mul_div_assoc]
      change B / B = 1
      exact div_self (ne_of_gt hBpos)
    have ht : cubeMean n (fun s : Fin n → Bool => Real.rpow (g s) r) ≤ 1 := by
      calc
        cubeMean n (fun s : Fin n → Bool => Real.rpow (g s) r) ≤
            cubeMean n (fun s : Fin n → Bool => (1 - r) + r * g s) := by
          unfold cubeMean
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum (fun s _ => rpow_tangent (g s) r (hg s) hr hr1))
            (inv_nonneg.mpr (pow_nonneg (by norm_num) n))
        _ = 1 := by
          unfold cubeMean at hmean ⊢
          simp only [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum,
            Finset.card_univ, nsmul_eq_mul]
          calc
            ((2 : ℝ) ^ n)⁻¹ *
                ((Fintype.card (Fin n → Bool) : ℝ) * (1 - r) +
                  r * ∑ s : Fin n → Bool, g s) =
                (((2 : ℝ) ^ n)⁻¹ * (Fintype.card (Fin n → Bool) : ℝ)) * (1 - r) +
                  r * (((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool, g s) := by ring
            _ = 1 := by rw [hcard, hmean]; ring
    have hscale : cubeMean n (fun s : Fin n → Bool => Real.rpow (f s) r) =
        Real.rpow B r * cubeMean n (fun s : Fin n → Bool => Real.rpow (g s) r) := by
      unfold cubeMean
      calc
        ((2 : ℝ) ^ n)⁻¹ * (∑ s : Fin n → Bool, Real.rpow (f s) r) =
            ((2 : ℝ) ^ n)⁻¹ *
              ∑ s : Fin n → Bool, Real.rpow B r * Real.rpow (g s) r := by
          congr 1
          apply Finset.sum_congr rfl
          intro s _
          have hfg : f s = B * g s := by
            dsimp only [g]
            field_simp [ne_of_gt hBpos] <;> ring
          simp only [Real.rpow_eq_pow]
          rw [hfg, Real.mul_rpow hBpos.le (hg s)]
        _ = Real.rpow B r *
            (((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool, Real.rpow (g s) r) := by
          rw [← Finset.mul_sum]
          ring
    change cubeMean n (fun s : Fin n → Bool => Real.rpow (f s) r) ≤ Real.rpow B r
    rw [hscale]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hBpos.le r) ht

private theorem cubeMean_Lp_mono (n : ℕ) (f : (Fin n → Bool) → ℝ) (p : ℝ) (q : ℝ) (hf : ∀ s : Fin n → Bool, 0 ≤ f s) (hq : 0 < q) (hqp : q ≤ p) : Real.rpow (cubeMean n (fun s : Fin n → Bool => Real.rpow (f s) q)) (1 / q) ≤ Real.rpow (cubeMean n (fun s : Fin n → Bool => Real.rpow (f s) p)) (1 / p) := by
  let r : ℝ := q / p
  let g : (Fin n → Bool) → ℝ := fun s : Fin n → Bool => Real.rpow (f s) p
  have hp : 0 < p := lt_of_lt_of_le hq hqp
  have hr : 0 < r := div_pos hq hp
  have hr1 : r ≤ 1 := (div_le_one hp).mpr hqp
  have hcomp : ∀ s : Fin n → Bool, Real.rpow (g s) r = Real.rpow (f s) q := by
    intro s
    dsimp only [g]
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul (hf s)]
    congr 1
    dsimp only [r]
    field_simp [ne_of_gt hp] <;> ring
  have hg : ∀ s : Fin n → Bool, 0 ≤ g s := by
    intro s
    exact Real.rpow_nonneg (hf s) p
  have hmean : cubeMean n (fun s : Fin n → Bool => Real.rpow (f s) q) ≤
      Real.rpow (cubeMean n g) r := by
    simpa only [hcomp] using cubeMean_rpow_le n g r hg hr hr1
  have hleft : 0 ≤ cubeMean n (fun s : Fin n → Bool => Real.rpow (f s) q) := by
    unfold cubeMean
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) n))
      (Finset.sum_nonneg (fun s _ => Real.rpow_nonneg (hf s) q))
  have hright : 0 ≤ cubeMean n g := by
    unfold cubeMean
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) n))
      (Finset.sum_nonneg (fun s _ => hg s))
  calc
    Real.rpow (cubeMean n (fun s : Fin n → Bool => Real.rpow (f s) q)) (1 / q) ≤
        Real.rpow (Real.rpow (cubeMean n g) r) (1 / q) :=
      Real.rpow_le_rpow hleft hmean (le_of_lt (one_div_pos.mpr hq))
    _ = Real.rpow (cubeMean n g) (1 / p) := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_mul hright]
      congr 1
      dsimp only [r]
      field_simp [ne_of_gt hp, ne_of_gt hq] <;> ring
    _ = Real.rpow (cubeMean n (fun s : Fin n → Bool => Real.rpow (f s) p)) (1 / p) := rfl

theorem hilbertConstant_pos : 0 < hilbertConstant := by
  norm_num [hilbertConstant]

theorem finite_hilbert_sign_moment_bound (n : ℕ) (d : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)) (q : ℝ) (hq : 2 ≤ q) : Real.rpow (moment n d v q) (1 / q) ≤ hilbertConstant * Real.sqrt q * Real.sqrt (energy n d v) := by
  let k : ℕ := Nat.ceil (q / 2)
  let p : ℝ := 2 * (k : ℝ)
  let A : ℝ := energy n d v
  let f : (Fin n → Bool) → ℝ := fun s : Fin n → Bool => ‖signSum n d v s‖
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hq
  have hk : 0 < k := Nat.ceil_pos.mpr (div_pos hq0 (by norm_num))
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hp : 0 < p := by dsimp only [p]; positivity
  have hqp : q ≤ p := by
    have hceil : q / 2 ≤ (k : ℝ) := Nat.le_ceil (q / 2)
    dsimp only [p]
    linarith
  have hpq : p ≤ 2 * q := by
    have hceil : (k : ℝ) < q / 2 + 1 := Nat.ceil_lt_add_one (le_of_lt (div_pos hq0 (by norm_num)))
    dsimp only [p]
    linarith
  have hA : 0 ≤ A := by
    dsimp only [A, energy]
    exact Finset.sum_nonneg (fun j _ => sq_nonneg ‖v j‖)
  have hf : ∀ s : Fin n → Bool, 0 ≤ f s := by
    intro s
    exact norm_nonneg (signSum n d v s)
  have hmono : Real.rpow (moment n d v q) (1 / q) ≤
      Real.rpow (cubeMean n (fun s : Fin n → Bool => Real.rpow (f s) p)) (1 / p) := by
    simpa only [moment, f] using cubeMean_Lp_mono n f p q hf hq0 hqp
  have hpcast : p = ((2 * k : ℕ) : ℝ) := by
    simp only [p, Nat.cast_mul, Nat.cast_ofNat]
  have hpow : ∀ s : Fin n → Bool,
      Real.rpow (f s) p = ‖signSum n d v s‖ ^ (2 * k) := by
    intro s
    simp only [Real.rpow_eq_pow]
    rw [hpcast, Real.rpow_natCast]
  have heven : cubeMean n (fun s : Fin n → Bool => Real.rpow (f s) p) ≤ p ^ k * A ^ k := by
    simpa only [hpow, p, A] using hilbert_even_bound n d v k
  have hmean : 0 ≤ cubeMean n (fun s : Fin n → Bool => Real.rpow (f s) p) := by
    unfold cubeMean
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) n))
      (Finset.sum_nonneg (fun s _ => Real.rpow_nonneg (hf s) p))
  have hU : 0 ≤ p ^ k * A ^ k := mul_nonneg (pow_nonneg hp.le k) (pow_nonneg hA k)
  have hbase : 0 ≤ Real.sqrt p * Real.sqrt A :=
    mul_nonneg (Real.sqrt_nonneg p) (Real.sqrt_nonneg A)
  have hpowered : Real.rpow (Real.sqrt p * Real.sqrt A) p = p ^ k * A ^ k := by
    calc
      Real.rpow (Real.sqrt p * Real.sqrt A) p =
          (Real.rpow (Real.sqrt p * Real.sqrt A) (2 : ℝ)) ^ k := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hbase] <;> rfl
      _ = p ^ k * A ^ k := by
        simp only [Real.rpow_eq_pow]
        rw [Real.rpow_two, mul_pow, Real.sq_sqrt hp.le, Real.sq_sqrt hA, mul_pow]
  have hroot : Real.rpow (p ^ k * A ^ k) (1 / p) ≤ Real.sqrt p * Real.sqrt A := by
    apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hU (1 / p)) hbase hp).mp
    simp only [Real.rpow_eq_pow] at hpowered ⊢
    rw [hpowered, ← Real.rpow_mul hU]
    have hexp : (1 / p) * p = 1 := by field_simp [ne_of_gt hp]
    rw [hexp, Real.rpow_one]
  have hs : Real.sqrt p ≤ 2 * Real.sqrt q := by
    by_contra hs
    have hlt : 2 * Real.sqrt q < Real.sqrt p := lt_of_not_ge hs
    have hsum : 0 < Real.sqrt p + 2 * Real.sqrt q :=
      add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr hp)
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg q))
    have hprod : 0 < (Real.sqrt p - 2 * Real.sqrt q) * (Real.sqrt p + 2 * Real.sqrt q) :=
      mul_pos (sub_pos.mpr hlt) hsum
    nlinarith [Real.sq_sqrt hp.le, Real.sq_sqrt hq0.le]
  calc
    Real.rpow (moment n d v q) (1 / q) ≤
        Real.rpow (cubeMean n (fun s : Fin n → Bool => Real.rpow (f s) p)) (1 / p) := hmono
    _ ≤ Real.rpow (p ^ k * A ^ k) (1 / p) :=
      Real.rpow_le_rpow hmean heven (le_of_lt (one_div_pos.mpr hp))
    _ ≤ Real.sqrt p * Real.sqrt A := hroot
    _ ≤ hilbertConstant * Real.sqrt q * Real.sqrt (energy n d v) := by
      change Real.sqrt p * Real.sqrt A ≤ (2 : ℝ) * Real.sqrt q * Real.sqrt A
      exact mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg A)

private theorem radMeasure_atomic (n : ℕ) : Shao.Probability.BrownianSup.radMeasure n = ((2 : ENNReal) ^ n)⁻¹ • ∑ s : Fin n → Bool, Measure.dirac (signPath n s) := by
  classical
  let nu : Measure (Shao.Path n) := ((2 : ENNReal) ^ n)⁻¹ • ∑ s : Fin n → Bool, Measure.dirac (signPath n s)
  change Measure.pi (fun _ : Fin n => Shao.OQ4.RademacherCosine.law) = nu
  apply Measure.pi_eq
  intro E hE
  have hrect : MeasurableSet (Set.univ.pi E) := MeasurableSet.univ_pi hE
  have hAtom : ∀ s : Fin n → Bool,
      Measure.dirac (signPath n s) (Set.univ.pi E) =
        ∏ j : Fin n, (if signValue (s j) ∈ E j then (1 : ENNReal) else 0) := by
    intro s
    rw [Measure.dirac_apply' _ hrect]
    simp [Set.indicator_apply, Fintype.prod_boole, Set.mem_pi, signPath]
  have hLaw : ∀ j : Fin n, Shao.OQ4.RademacherCosine.law (E j) =
      (1 / 2 : ENNReal) * ((if signValue true ∈ E j then 1 else 0) +
        (if signValue false ∈ E j then 1 else 0)) := by
    intro j
    simp [signValue]
    simp only [Shao.OQ4.RademacherCosine.law, Shao.OQ4.RademacherCosine.halfENNReal,
      Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ (hE j),
      smul_eq_mul, Set.indicator_apply, Pi.one_apply]
    simp only [one_div, mul_comm]
    rw [mul_add]
  have hweight : (∏ _j : Fin n, (1 / 2 : ENNReal)) = ((2 : ENNReal) ^ n)⁻¹ := by
    rw [Fin.prod_const, one_div, ← ENNReal.inv_pow]
  change (((2 : ENNReal) ^ n)⁻¹ • ∑ s : Fin n → Bool, Measure.dirac (signPath n s))
      (Set.univ.pi E) = ∏ j : Fin n, Shao.OQ4.RademacherCosine.law (E j)
  rw [Measure.smul_apply, Measure.finsetSum_apply]
  simp only [smul_eq_mul, hAtom]
  rw [← Fintype.prod_sum (fun (j : Fin n) (b : Bool) => if signValue b ∈ E j then (1 : ENNReal) else 0)]
  simp only [Fintype.sum_bool]
  rw [← hweight, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun j _ => (hLaw j).symm)

theorem rad_integrable_and_integral (n : ℕ) (f : Shao.Path n → ℝ) : Integrable f (Shao.Probability.BrownianSup.radMeasure n) ∧ (∫ w : Shao.Path n, f w ∂Shao.Probability.BrownianSup.radMeasure n) = cubeMean n (fun s : Fin n → Bool => f (signPath n s)) := by
  classical
  let c : ENNReal := ((2 : ENNReal) ^ n)⁻¹
  let cr : ℝ := ((2 : ℝ) ^ n)⁻¹
  have hc : c ≠ ⊤ := by
    dsimp only [c]
    apply ENNReal.inv_ne_top.mpr
    exact pow_ne_zero n (by norm_num)
  have hcReal : c.toReal = cr := by
    norm_num [c, cr, ENNReal.toReal_inv, ENNReal.toReal_pow]
  have hAtom : ∀ s : Fin n → Bool, Integrable f (Measure.dirac (signPath n s)) := by
    intro s
    let x : Shao.Path n := signPath n s
    exact (integrable_dirac (by simp) : Integrable f (Measure.dirac x))
  have hSum : Integrable f (∑ s : Fin n → Bool, Measure.dirac (signPath n s)) :=
    integrable_finsetSum_measure.mpr (fun s _ => hAtom s)
  constructor
  · rw [radMeasure_atomic n]
    change Integrable f (c • ∑ s : Fin n → Bool, Measure.dirac (signPath n s))
    exact hSum.smul_measure hc
  · rw [radMeasure_atomic n]
    change (∫ w : Shao.Path n, f w ∂(c • ∑ s : Fin n → Bool, Measure.dirac (signPath n s))) =
      cubeMean n (fun s : Fin n → Bool => f (signPath n s))
    rw [integral_smul_measure,
      integral_finsetSum_measure (fun s _ => hAtom s), hcReal]
    simp only [integral_dirac, smul_eq_mul, cubeMean, cr]

theorem pathSum_signPath (n : ℕ) (d : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)) (s : Fin n → Bool) : pathSum n d v (signPath n s) = signSum n d v s := by
  rfl

theorem rademacher_hilbert_moment_bound (n : ℕ) (d : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)) (q : ℝ) (hq : 2 ≤ q) : Integrable (fun w : Shao.Path n => Real.rpow ‖pathSum n d v w‖ q) (Shao.Probability.BrownianSup.radMeasure n) ∧ Real.rpow (∫ w : Shao.Path n, Real.rpow ‖pathSum n d v w‖ q ∂Shao.Probability.BrownianSup.radMeasure n) (1 / q) ≤ hilbertConstant * Real.sqrt q * Real.sqrt (energy n d v) := by
  let f : Shao.Path n → ℝ := fun w : Shao.Path n => Real.rpow ‖pathSum n d v w‖ q
  have hbridge : Integrable f (Shao.Probability.BrownianSup.radMeasure n) ∧
      (∫ w : Shao.Path n, f w ∂Shao.Probability.BrownianSup.radMeasure n) =
        cubeMean n (fun s : Fin n → Bool => f (signPath n s)) :=
    rad_integrable_and_integral n f
  constructor
  · exact hbridge.1
  · change Real.rpow (∫ w : Shao.Path n, f w ∂Shao.Probability.BrownianSup.radMeasure n)
        (1 / q) ≤ hilbertConstant * Real.sqrt q * Real.sqrt (energy n d v)
    rw [hbridge.2]
    simpa only [f, pathSum_signPath, moment] using
      finite_hilbert_sign_moment_bound n d v q hq


end

end Shao.OQ6.FiniteHilbertSignMoments
