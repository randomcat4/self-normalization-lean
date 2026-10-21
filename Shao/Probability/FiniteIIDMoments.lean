import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite iid identities using only second moments

Source: p35 section 5 and formula (16). Pair products always involve distinct
coordinates. The original variables may have a nonzero mean.
-/

set_option autoImplicit false

namespace Shao.Probability

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

def finiteFeatureSum {m : ℕ} {Ω : Type*} (Z : Fin m → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin m, Z i ω

def finiteLeaveOwnSquareSum {m : ℕ} {Ω : Type*} (Z : Fin m → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin m, Z i ω ^ 2 * (finiteFeatureSum Z ω - Z i ω) ^ 2

def finitePairProductSum {m : ℕ} {Ω : Type*} (Z : Fin m → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin m, ∑ l : Fin m, if i < l then Z i ω * Z l ω else 0

private def subsetSum {ι Ω : Type*} (s : Finset ι) (Z : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ s, Z i ω

private def subsetPair {ι Ω : Type*} [LinearOrder ι]
    (s : Finset ι) (Z : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, if i < j then Z i ω * Z j ω else 0

section Helpers

variable {ι Ω : Type*} [LinearOrder ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : ι → Ω → ℝ}

omit [LinearOrder ι] in
private theorem subset_sum_measurable (hZ : ∀ i, Measurable (Z i)) (s : Finset ι) :
    Measurable (subsetSum s Z) := by
  unfold subsetSum
  fun_prop

private theorem subset_pair_measurable (hZ : ∀ i, Measurable (Z i)) (s : Finset ι) :
    Measurable (subsetPair s Z) := by
  unfold subsetPair
  fun_prop

omit [LinearOrder ι] [IsProbabilityMeasure μ] in
private theorem subset_sum_memLp (h2 : ∀ i, MemLp (Z i) 2 μ) (s : Finset ι) :
    MemLp (subsetSum s Z) 2 μ :=
  memLp_finsetSum s (fun i _ => h2 i)

omit [LinearOrder ι] [IsProbabilityMeasure μ] in
private theorem distinct_product_memLp (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z μ) (h2 : ∀ i, MemLp (Z i) 2 μ)
    (i j : ι) (hij : i ≠ j) :
    MemLp (fun ω => Z i ω * Z j ω) 2 μ := by
  apply (memLp_two_iff_integrable_sq ((hZ i).mul (hZ j)).aestronglyMeasurable).mpr
  have hi : IndepFun (fun ω => Z i ω ^ 2) (fun ω => Z j ω ^ 2) μ :=
    (hIndep.indepFun hij).comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  simpa only [Function.comp_def, id_eq, mul_pow, Pi.mul_def] using
    hi.integrable_mul (h2 i).integrable_sq (h2 j).integrable_sq

private theorem subset_pair_memLp (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z μ) (h2 : ∀ i, MemLp (Z i) 2 μ) (s : Finset ι) :
    MemLp (subsetPair s Z) 2 μ := by
  apply memLp_finsetSum s
  intro i _
  apply memLp_finsetSum s
  intro j _
  by_cases hij : i < j
  · simpa only [hij, ite_true] using distinct_product_memLp hZ hIndep h2 i j hij.ne
  · simpa only [hij, ite_false] using (memLp_const (0 : ℝ) : MemLp (fun _ : Ω => (0 : ℝ)) 2 μ)

omit [LinearOrder ι] in
private theorem subset_sum_mean (h2 : ∀ i, MemLp (Z i) 2 μ)
    {u : ℝ} (hmean : ∀ i, (∫ ω, Z i ω ∂μ) = u) (s : Finset ι) :
    (∫ ω, subsetSum s Z ω ∂μ) = (s.card : ℝ) * u := by
  change (∫ ω, ∑ i ∈ s, Z i ω ∂μ) = _
  rw [integral_finsetSum s (fun i _ => (h2 i).integrable (by norm_num))]
  simp only [hmean, Finset.sum_const, nsmul_eq_mul]

omit [LinearOrder ι] in
private theorem subset_sum_second (hIndep : iIndepFun Z μ)
    (h2 : ∀ i, MemLp (Z i) 2 μ) {u M2 : ℝ}
    (hmean : ∀ i, (∫ ω, Z i ω ∂μ) = u)
    (hsecond : ∀ i, (∫ ω, Z i ω ^ 2 ∂μ) = M2) (s : Finset ι) :
    (∫ ω, subsetSum s Z ω ^ 2 ∂μ) =
      (s.card : ℝ) * M2 + (s.card : ℝ) * ((s.card : ℝ) - 1) * u ^ 2 := by
  have hv (i : ι) : variance (Z i) μ = M2 - u ^ 2 := by
    rw [variance_eq_sub (h2 i)]
    simp only [Pi.pow_apply, hmean, hsecond]
  have hvar := IndepFun.variance_sum (s := s) (fun i _ => h2 i)
    (fun i _ j _ hij => hIndep.indepFun hij)
  have hvar' : variance (subsetSum s Z) μ = (s.card : ℝ) * (M2 - u ^ 2) := by
    have he : (∑ i ∈ s, Z i) = subsetSum s Z := by
      funext ω
      simp [subsetSum]
    rw [he] at hvar
    simpa only [hv, Finset.sum_const, nsmul_eq_mul] using hvar
  rw [variance_eq_sub (subset_sum_memLp h2 s)] at hvar'
  have hm := subset_sum_mean h2 hmean s
  simp only [Pi.pow_apply] at hvar'
  rw [hm] at hvar'
  nlinarith

omit [MeasurableSpace Ω] in
private theorem subset_pair_insert (s : Finset ι) (a : ι) (ha : a ∉ s) (ω : Ω) :
    subsetPair (insert a s) Z ω = subsetPair s Z ω + Z a ω * subsetSum s Z ω := by
  classical
  have hterm (j : ι) (hj : j ∈ s) :
      (if a < j then Z a ω * Z j ω else 0) +
        (if j < a then Z j ω * Z a ω else 0) = Z a ω * Z j ω := by
    have hne : a ≠ j := by intro he; subst j; exact ha hj
    rcases lt_or_gt_of_ne hne with h | h <;> simp [h, not_lt_of_ge h.le, mul_comm]
  unfold subsetPair subsetSum
  simp only [Finset.sum_insert ha, lt_self_iff_false, ite_false, zero_add,
    Finset.sum_add_distrib]
  have he : (∑ j ∈ s, if a < j then Z a ω * Z j ω else 0) +
      (∑ j ∈ s, if j < a then Z j ω * Z a ω else 0) =
      Z a ω * ∑ j ∈ s, Z j ω := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  linarith

omit [IsProbabilityMeasure μ] in
private theorem subset_pair_sum_indep (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z μ) (s : Finset ι) (a : ι) (ha : a ∉ s) :
    IndepFun (fun ω => (subsetPair s Z ω, subsetSum s Z ω)) (Z a) μ := by
  classical
  have hd : Disjoint s {a} := by simpa using ha
  have h := hIndep.indepFun_finset s {a} hd hZ
  let f : (s → ℝ) → ℝ × ℝ := fun x =>
    ((∑ i : s, ∑ j : s, if i.val < j.val then x i * x j else 0),
      ∑ i : s, x i)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hc := h.comp hf (measurable_pi_apply (⟨a, by simp⟩ : ({a} : Finset ι)))
  have he : (fun ω => f (fun i : s => Z i ω)) =
      (fun ω => (subsetPair s Z ω, subsetSum s Z ω)) := by
    funext ω
    change ((∑ i : s, ∑ j : s, if i.val < j.val then Z i ω * Z j ω else 0),
      ∑ i : s, Z i ω) = (subsetPair s Z ω, subsetSum s Z ω)
    apply Prod.ext
    · change (∑ i : s, ∑ j : s, if i.val < j.val then Z i ω * Z j ω else 0) = _
      rw [Finset.sum_coe_sort s (fun i => ∑ j : s, if i < j.val then Z i ω * Z j ω else 0)]
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_coe_sort s (fun j => if i < j then Z i ω * Z j ω else 0)
    · exact Finset.sum_coe_sort s (fun i => Z i ω)
  change IndepFun (fun ω => f (fun i : s => Z i ω)) (Z a) μ at hc
  rw [he] at hc
  exact hc

private theorem centered_pair_moments (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z μ) (h2 : ∀ i, MemLp (Z i) 2 μ)
    (hmean : ∀ i, (∫ ω, Z i ω ∂μ) = 0) {v : ℝ}
    (hsecond : ∀ i, (∫ ω, Z i ω ^ 2 ∂μ) = v) (s : Finset ι) :
    (∫ ω, subsetPair s Z ω ∂μ) = 0 ∧
      (∫ ω, subsetPair s Z ω * subsetSum s Z ω ∂μ) = 0 ∧
      (∫ ω, subsetPair s Z ω ^ 2 ∂μ) =
        ((s.card : ℝ) * ((s.card : ℝ) - 1) / 2) * v ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [subsetPair, subsetSum]
  | @insert a s ha ih =>
    have hS2 := subset_sum_memLp h2 s
    have hP2 := subset_pair_memLp hZ hIndep h2 s
    have hS := hS2.integrable (by norm_num)
    have hP := hP2.integrable (by norm_num)
    have hX := (h2 a).integrable (by norm_num)
    have hSmean : (∫ ω, subsetSum s Z ω ∂μ) = 0 := by
      simpa using subset_sum_mean h2 hmean s
    have hSsq : (∫ ω, subsetSum s Z ω ^ 2 ∂μ) = (s.card : ℝ) * v := by
      simpa using subset_sum_second hIndep h2 hmean hsecond s
    have hblock := subset_pair_sum_indep hZ hIndep s a ha
    have hPSX : IndepFun (fun ω => subsetPair s Z ω * subsetSum s Z ω) (Z a) μ :=
      hblock.comp (measurable_fst.mul measurable_snd) measurable_id
    have hPX : IndepFun (subsetPair s Z) (Z a) μ :=
      hblock.comp measurable_fst measurable_id
    have hSX : IndepFun (subsetSum s Z) (Z a) μ :=
      hblock.comp measurable_snd measurable_id
    have hSX2 : IndepFun (fun ω => subsetSum s Z ω ^ 2) (fun ω => Z a ω ^ 2) μ :=
      hSX.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
    have hSXsq : IndepFun (fun ω => subsetSum s Z ω ^ 2) (Z a) μ :=
      hSX.comp (measurable_id.pow_const 2) measurable_id
    have hSsqX : IndepFun (subsetSum s Z) (fun ω => Z a ω ^ 2) μ :=
      hSX.comp measurable_id (measurable_id.pow_const 2)
    have hXS : Integrable (fun ω => Z a ω * subsetSum s Z ω) μ :=
      hSX.symm.integrable_mul hX hS
    have hXP : Integrable (fun ω => Z a ω * subsetPair s Z ω) μ :=
      hPX.symm.integrable_mul hX hP
    have hXSsq : Integrable (fun ω => Z a ω * subsetSum s Z ω ^ 2) μ :=
      hSXsq.symm.integrable_mul hX hS2.integrable_sq
    have hXsqS : Integrable (fun ω => Z a ω ^ 2 * subsetSum s Z ω) μ :=
      hSsqX.symm.integrable_mul (h2 a).integrable_sq hS
    have hXPS : Integrable (fun ω => Z a ω * (subsetPair s Z ω * subsetSum s Z ω)) μ :=
      hPSX.symm.integrable_mul hX (hP2.integrable_mul hS2)
    have hXsqSsq : Integrable (fun ω => Z a ω ^ 2 * subsetSum s Z ω ^ 2) μ :=
      hSX2.symm.integrable_mul (h2 a).integrable_sq hS2.integrable_sq
    have eXS : (∫ ω, Z a ω * subsetSum s Z ω ∂μ) = 0 := by
      rw [hSX.symm.integral_fun_mul_eq_mul_integral (hZ a).aestronglyMeasurable
        hS.aestronglyMeasurable, hmean, zero_mul]
    have eXP : (∫ ω, Z a ω * subsetPair s Z ω ∂μ) = 0 := by
      rw [hPX.symm.integral_fun_mul_eq_mul_integral (hZ a).aestronglyMeasurable
        hP.aestronglyMeasurable, hmean, zero_mul]
    have eXSsq : (∫ ω, Z a ω * subsetSum s Z ω ^ 2 ∂μ) = 0 := by
      rw [hSXsq.symm.integral_fun_mul_eq_mul_integral (hZ a).aestronglyMeasurable
        hS2.integrable_sq.aestronglyMeasurable, hmean, zero_mul]
    have eXsqS : (∫ ω, Z a ω ^ 2 * subsetSum s Z ω ∂μ) = 0 := by
      rw [hSsqX.symm.integral_fun_mul_eq_mul_integral
        (h2 a).integrable_sq.aestronglyMeasurable hS.aestronglyMeasurable,
        hSmean, mul_zero]
    have eXPS : (∫ ω, Z a ω * (subsetPair s Z ω * subsetSum s Z ω) ∂μ) = 0 := by
      rw [hPSX.symm.integral_fun_mul_eq_mul_integral (hZ a).aestronglyMeasurable
        (hP2.integrable_mul hS2).aestronglyMeasurable, hmean, zero_mul]
    have eXsqSsq : (∫ ω, Z a ω ^ 2 * subsetSum s Z ω ^ 2 ∂μ) =
        v * ((s.card : ℝ) * v) := by
      rw [hSX2.symm.integral_fun_mul_eq_mul_integral
        (h2 a).integrable_sq.aestronglyMeasurable hS2.integrable_sq.aestronglyMeasurable,
        hsecond, hSsq]
    have hPinsert : subsetPair (insert a s) Z =
        (fun ω => subsetPair s Z ω + Z a ω * subsetSum s Z ω) := by
      funext ω
      exact subset_pair_insert s a ha ω
    have hSinsert : subsetSum (insert a s) Z =
        (fun ω => subsetSum s Z ω + Z a ω) := by
      funext ω
      simp [subsetSum, ha, add_comm]
    constructor
    · rw [hPinsert, integral_add hP hXS, ih.1, eXS, add_zero]
    constructor
    · have he : (fun ω => subsetPair (insert a s) Z ω * subsetSum (insert a s) Z ω) =
          (fun ω => subsetPair s Z ω * subsetSum s Z ω + Z a ω * subsetPair s Z ω +
            Z a ω * subsetSum s Z ω ^ 2 + Z a ω ^ 2 * subsetSum s Z ω) := by
        funext ω
        rw [hPinsert, hSinsert]
        ring
      have hPS : Integrable (fun ω => subsetPair s Z ω * subsetSum s Z ω) μ :=
        hP2.integrable_mul hS2
      have hsum2 : Integrable (fun ω => subsetPair s Z ω * subsetSum s Z ω +
          Z a ω * subsetPair s Z ω) μ := hPS.add hXP
      have hsum3 : Integrable (fun ω => subsetPair s Z ω * subsetSum s Z ω +
          Z a ω * subsetPair s Z ω + Z a ω * subsetSum s Z ω ^ 2) μ := hsum2.add hXSsq
      rw [he, integral_add hsum3 hXsqS, integral_add hsum2 hXSsq,
        integral_add hPS hXP, ih.2.1, eXP, eXSsq, eXsqS]
      ring
    · have he : (fun ω => subsetPair (insert a s) Z ω ^ 2) =
          (fun ω => subsetPair s Z ω ^ 2 +
            2 * (Z a ω * (subsetPair s Z ω * subsetSum s Z ω)) +
            Z a ω ^ 2 * subsetSum s Z ω ^ 2) := by
        funext ω
        rw [hPinsert]
        ring
      have hsum : Integrable (fun ω => subsetPair s Z ω ^ 2 +
          2 * (Z a ω * (subsetPair s Z ω * subsetSum s Z ω))) μ :=
        hP2.integrable_sq.add (hXPS.const_mul 2)
      rw [he, integral_add hsum hXsqSsq,
        integral_add hP2.integrable_sq (hXPS.const_mul 2), integral_const_mul,
        ih.2.2, eXPS, eXsqSsq, Finset.card_insert_of_notMem ha, Nat.cast_add,
        Nat.cast_one]
      ring


omit [MeasurableSpace Ω] in
private theorem subset_pair_center (s : Finset ι) (u : ℝ) (ω : Ω) :
    subsetPair s Z ω = subsetPair s (fun i ω => Z i ω - u) ω +
      u * ((s.card : ℝ) - 1) * subsetSum s (fun i ω => Z i ω - u) ω +
      ((s.card : ℝ) * ((s.card : ℝ) - 1) / 2) * u ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [subsetPair, subsetSum]
  | @insert a s ha ih =>
    rw [subset_pair_insert s a ha, subset_pair_insert s a ha, ih,
      Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
    have hsum : subsetSum s Z ω =
        subsetSum s (fun i ω => Z i ω - u) ω + (s.card : ℝ) * u := by
      simp only [subsetSum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    simp only [subsetSum, Finset.sum_insert ha] at hsum ⊢
    rw [hsum]
    ring

end Helpers

section IID

variable {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [hμ : IsProbabilityMeasure μ]
variable {ν : Measure ℝ} [hν : IsProbabilityMeasure ν]
variable {Z : Fin m → Ω → ℝ}

include hμ hν

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
private theorem iid_coord_memLp
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) (i : Fin m) : MemLp (Z i) 2 μ :=
  (hLaw i).symm.memLp_snd hν2

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
private theorem iid_coord_mean
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν) (i : Fin m) :
    (∫ ω, Z i ω ∂μ) = ∫ z, z ∂ν :=
  (hLaw i).integral_eq

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
private theorem iid_coord_second
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν) (i : Fin m) :
    (∫ ω, Z i ω ^ 2 ∂μ) = ∫ z, z ^ 2 ∂ν :=
  (hLaw i).pow.integral_eq

omit hμ hν in
private theorem iid_leaveOwn_indep (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z μ) (i : Fin m) :
    IndepFun (fun ω => Z i ω ^ 2)
      (fun ω => (finiteFeatureSum Z ω - Z i ω) ^ 2) μ := by
  classical
  have hi : i ∉ (Finset.univ : Finset (Fin m)).erase i := by simp
  have h := (hIndep.indepFun_finsetSum_of_notMem hZ hi).symm
  have he : (fun ω => ∑ k ∈ (Finset.univ : Finset (Fin m)).erase i, Z k ω) =
      (fun ω => finiteFeatureSum Z ω - Z i ω) := by
    funext ω
    simp [finiteFeatureSum, Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  have ht : (∑ k ∈ (Finset.univ : Finset (Fin m)).erase i, Z k) =
      (fun ω => finiteFeatureSum Z ω - Z i ω) := by
    funext ω
    simpa only [Finset.sum_apply] using congrFun he ω
  rw [ht] at h
  exact h.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
private theorem iid_leaveOwn_term_integrable (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) (i : Fin m) :
    Integrable (fun ω => Z i ω ^ 2 * (finiteFeatureSum Z ω - Z i ω) ^ 2) μ := by
  have h2 := iid_coord_memLp hLaw hν2
  have hS2 : MemLp (finiteFeatureSum Z) 2 μ := subset_sum_memLp h2 Finset.univ
  exact (iid_leaveOwn_indep hZ hIndep i).integrable_mul
    (h2 i).integrable_sq (hS2.sub (h2 i)).integrable_sq

omit hμ hν in
theorem finite_iid_leaveOwnSquare_integrable
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) :
    Integrable (finiteLeaveOwnSquareSum Z) μ :=
  integrable_finsetSum Finset.univ (fun i _ => iid_leaveOwn_term_integrable hZ hIndep hLaw hν2 i)

omit hμ hν in
theorem finite_iid_leaveOwnSquare_integral
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) :
    (∫ ω, finiteLeaveOwnSquareSum Z ω ∂μ) =
      (m : ℝ) * (∫ z, z ^ 2 ∂ν) *
        (((m - 1 : ℕ) : ℝ) * (∫ z, z ^ 2 ∂ν) +
          ((m - 1 : ℕ) : ℝ) * ((m - 2 : ℕ) : ℝ) * (∫ z, z ∂ν) ^ 2) := by
  classical
  have h2 := iid_coord_memLp hLaw hν2
  have hterm (i : Fin m) : (∫ ω, Z i ω ^ 2 * (finiteFeatureSum Z ω - Z i ω) ^ 2 ∂μ) =
      (∫ z, z ^ 2 ∂ν) * (((m - 1 : ℕ) : ℝ) * (∫ z, z ^ 2 ∂ν) +
        ((m - 1 : ℕ) : ℝ) * ((m - 2 : ℕ) : ℝ) * (∫ z, z ∂ν) ^ 2) := by
    have hS2 : MemLp (finiteFeatureSum Z) 2 μ := subset_sum_memLp h2 Finset.univ
    rw [(iid_leaveOwn_indep hZ hIndep i).integral_fun_mul_eq_mul_integral
      (h2 i).integrable_sq.aestronglyMeasurable (hS2.sub (h2 i)).integrable_sq.aestronglyMeasurable,
      iid_coord_second hLaw i]
    have he : (fun ω => finiteFeatureSum Z ω - Z i ω) =
        subsetSum ((Finset.univ : Finset (Fin m)).erase i) Z := by
      funext ω
      simp [subsetSum, finiteFeatureSum, Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    simp_rw [congrFun he]
    rw [subset_sum_second hIndep h2 (iid_coord_mean hLaw) (iid_coord_second hLaw)]
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    by_cases hm : m = 1
    · simp [hm]
    · have hm2 : 2 ≤ m := by have := i.is_lt; omega
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_sub hm2]
      simp only [Nat.cast_one, Nat.cast_ofNat]
      ring
  change (∫ ω, ∑ i : Fin m, Z i ω ^ 2 * (finiteFeatureSum Z ω - Z i ω) ^ 2 ∂μ) = _
  rw [integral_finsetSum Finset.univ
    (fun i _ => iid_leaveOwn_term_integrable hZ hIndep hLaw hν2 i)]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

omit hμ hν in
theorem finite_iid_pairProduct_memLp_two
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) :
    MemLp (finitePairProductSum Z) 2 μ := by
  exact subset_pair_memLp hZ hIndep (iid_coord_memLp hLaw hν2) Finset.univ

omit hμ hν in
theorem finite_iid_sumSquare_integral
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) :
    (∫ ω, finiteFeatureSum Z ω ^ 2 ∂μ) =
      (m : ℝ) * (∫ z, z ^ 2 ∂ν) +
        (m : ℝ) * ((m - 1 : ℕ) : ℝ) * (∫ z, z ∂ν) ^ 2 := by
  have _ := hZ
  have h := subset_sum_second hIndep (iid_coord_memLp hLaw hν2)
    (iid_coord_mean hLaw) (iid_coord_second hLaw) Finset.univ
  change (∫ ω, finiteFeatureSum Z ω ^ 2 ∂μ) = _ at h
  simp only [Finset.card_univ, Fintype.card_fin] at h
  by_cases hm : m = 0
  · simpa [hm] using h
  · rw [Nat.cast_sub (by omega : 1 ≤ m)]
    simpa using h

omit hν in
private theorem iid_pair_statistics
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) :
    (∫ ω, finitePairProductSum Z ω ∂μ) = (m.choose 2 : ℝ) * (∫ z, z ∂ν) ^ 2 ∧
      variance (finitePairProductSum Z) μ =
        (m.choose 2 : ℝ) * (variance (id : ℝ → ℝ) ν) ^ 2 +
          (m : ℝ) * (((m - 1 : ℕ) : ℝ) ^ 2) *
            (∫ z, z ∂ν) ^ 2 * variance (id : ℝ → ℝ) ν := by
  classical
  let u : ℝ := ∫ z, z ∂ν
  let v : ℝ := variance (id : ℝ → ℝ) ν
  let Y : Fin m → Ω → ℝ := fun i ω => Z i ω - u
  have h2 := iid_coord_memLp hLaw hν2
  have hY : ∀ i, Measurable (Y i) := fun i => (hZ i).sub_const u
  have hY2 : ∀ i, MemLp (Y i) 2 μ := fun i => (h2 i).sub (memLp_const u)
  have hYi : iIndepFun Y μ :=
    hIndep.comp (fun _ x => x - u) (fun _ => measurable_id.sub_const u)
  have hYm (i : Fin m) : (∫ ω, Y i ω ∂μ) = 0 := by
    change (∫ ω, Z i ω - u ∂μ) = 0
    rw [integral_sub ((h2 i).integrable (by norm_num)) (integrable_const u),
      iid_coord_mean hLaw, integral_const, probReal_univ, one_smul]
    exact sub_self u
  have hYsq (i : Fin m) : (∫ ω, Y i ω ^ 2 ∂μ) = v := by
    have hi := (hLaw i).variance_eq
    rw [variance_eq_integral (hZ i).aemeasurable, iid_coord_mean hLaw] at hi
    exact hi
  let P : Ω → ℝ := subsetPair Finset.univ Y
  let S : Ω → ℝ := subsetSum Finset.univ Y
  have hP2 : MemLp P 2 μ := subset_pair_memLp hY hYi hY2 Finset.univ
  have hS2 : MemLp S 2 μ := subset_sum_memLp hY2 Finset.univ
  have hP : Integrable P μ := hP2.integrable (by norm_num)
  have hS : Integrable S μ := hS2.integrable (by norm_num)
  have hc := centered_pair_moments hY hYi hY2 hYm hYsq Finset.univ
  change (∫ ω, P ω ∂μ) = 0 ∧ (∫ ω, P ω * S ω ∂μ) = 0 ∧
    (∫ ω, P ω ^ 2 ∂μ) =
      (((Finset.univ : Finset (Fin m)).card : ℝ) *
        (((Finset.univ : Finset (Fin m)).card : ℝ) - 1) / 2) * v ^ 2 at hc
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  have hSm : (∫ ω, S ω ∂μ) = 0 := by
    simpa using subset_sum_mean hY2 hYm Finset.univ
  have hSsq : (∫ ω, S ω ^ 2 ∂μ) = (m : ℝ) * v := by
    simpa only [Finset.card_univ, Fintype.card_fin, zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero] using subset_sum_second hYi hY2 hYm hYsq Finset.univ
  have hcnt : (m : ℝ) * ((m : ℝ) - 1) / 2 = (m.choose 2 : ℝ) :=
    (Nat.cast_choose_two ℝ m).symm
  have hPm : (∫ ω, P ω ∂μ) = 0 := hc.1
  have hPsq : (∫ ω, P ω ^ 2 ∂μ) = (m.choose 2 : ℝ) * v ^ 2 := by
    rw [hc.2.2, hcnt]
  have hcov : covariance P S μ = 0 := by
    rw [covariance_eq_sub hP2 hS2]
    change (∫ ω, P ω * S ω ∂μ) - (∫ ω, P ω ∂μ) * (∫ ω, S ω ∂μ) = 0
    rw [hc.2.1, hPm, zero_mul, sub_zero]
  have hvP : variance P μ = (m.choose 2 : ℝ) * v ^ 2 := by
    rw [variance_eq_sub hP2]
    change (∫ ω, P ω ^ 2 ∂μ) - (∫ ω, P ω ∂μ) ^ 2 = _
    rw [hPsq, hPm, zero_pow (by decide : 2 ≠ 0), sub_zero]
  have hvS : variance S μ = (m : ℝ) * v := by
    rw [variance_eq_sub hS2]
    change (∫ ω, S ω ^ 2 ∂μ) - (∫ ω, S ω ∂μ) ^ 2 = _
    rw [hSsq, hSm, zero_pow (by decide : 2 ≠ 0), sub_zero]
  let c : ℝ := u * ((m : ℝ) - 1)
  let d : ℝ := (m.choose 2 : ℝ) * u ^ 2
  have hdec : finitePairProductSum Z = (fun ω => P ω + c * S ω + d) := by
    funext ω
    have h := subset_pair_center (Z := Z) Finset.univ u ω
    simp only [Finset.card_univ, Fintype.card_fin] at h
    rw [hcnt] at h
    exact h
  have hT2 : MemLp (fun ω => P ω + c * S ω) 2 μ := hP2.add (hS2.const_mul c)
  have hT : Integrable (fun ω => P ω + c * S ω) μ := hP.add (hS.const_mul c)
  constructor
  · rw [hdec, integral_add hT (integrable_const d),
      integral_add hP (hS.const_mul c), integral_const_mul, hPm, hSm,
      integral_const, probReal_univ, one_smul]
    simp only [mul_zero, add_zero, zero_add]
    rfl
  · rw [hdec, variance_add_const hT2.aestronglyMeasurable d,
      variance_fun_add hP2 (hS2.const_mul c), covariance_const_mul_right, hcov,
      variance_const_mul, hvP, hvS]
    dsimp [c]
    by_cases hm : m = 0
    · simp [hm]
    · rw [Nat.cast_sub (by omega : 1 ≤ m)]
      simp only [Nat.cast_one]
      dsimp [u, v]
      ring

omit hμ hν in
theorem finite_iid_pairProduct_integral
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) :
    (∫ ω, finitePairProductSum Z ω ∂μ) = (m.choose 2 : ℝ) * (∫ z, z ∂ν) ^ 2 :=
  (iid_pair_statistics hZ hIndep hLaw hν2).1

omit hμ hν in
theorem finite_iid_pairProduct_variance
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) :
    variance (finitePairProductSum Z) μ =
      (m.choose 2 : ℝ) * (variance (id : ℝ → ℝ) ν) ^ 2 +
        (m : ℝ) * (((m - 1 : ℕ) : ℝ) ^ 2) *
          (∫ z, z ∂ν) ^ 2 * variance (id : ℝ → ℝ) ν :=
  (iid_pair_statistics hZ hIndep hLaw hν2).2

end IID

end

end Shao.Probability
