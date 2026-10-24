import Shao.OQ6.CanonicalTilt
import Shao.OQ6.QuantitativeOverlap
import Shao.OQ6.ResidualDeletion
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Integration
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual finite-product residual moments

The finite objects are the existing unorderedPairSum and rowSum. Coordinate
independence refers to full observations. Repeated observed values are allowed.
The source target is p39(10); weighted deletion and the source quadratic
specialization are not asserted in this module.
-/

set_option autoImplicit false

namespace Shao.OQ6.FiniteTiltedMoments

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem coordinate_independence
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (n : ℕ) :
    iIndepFun (fun i (ξ : Fin n → Ω) => ξ i)
      (Measure.pi (fun _ : Fin n => ρ)) :=
  iIndepFun_pi (μ := fun _ : Fin n => ρ)
    (X := fun _ (o : Ω) => o) (fun _ => measurable_id.aemeasurable)

private theorem coordinate_map
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (n : ℕ) (i : Fin n) :
    (Measure.pi (fun _ : Fin n => ρ)).map
      (fun ξ : Fin n → Ω => ξ i) = ρ :=
  (measurePreserving_eval (μ := fun _ : Fin n => ρ) i).map_eq

private theorem pair_selection_preserving
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    MeasurePreserving
      (fun ξ : Fin n → Ω => (ξ i, ξ j))
      (Measure.pi (fun _ : Fin n => ρ)) (ρ.prod ρ) := by
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  have hi := (coordinate_independence ρ n).indepFun hij
  simpa only [coordinate_map] using hi.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable

private theorem shared_triple_selection_preserving
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (n : ℕ) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    MeasurePreserving
      (fun ξ : Fin n → Ω => (ξ i, (ξ j, ξ k)))
      (Measure.pi (fun _ : Fin n => ρ))
      (ρ.prod (ρ.prod ρ)) := by
  have hp := pair_selection_preserving ρ n j k hjk
  have hi := ((coordinate_independence ρ n).indepFun_prodMk
    (fun a => measurable_pi_apply a) j k i hij.symm hik.symm).symm
  refine ⟨(measurable_pi_apply i).prodMk
    ((measurable_pi_apply j).prodMk (measurable_pi_apply k)), ?_⟩
  simpa only [hp.map_eq, coordinate_map] using hi.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable
    ((measurable_pi_apply j).prodMk (measurable_pi_apply k)).aemeasurable

private theorem disjoint_four_selection_preserving
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (n : ℕ) (i j k l : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    MeasurePreserving
      (fun ξ : Fin n → Ω => ((ξ i, ξ j), (ξ k, ξ l)))
      (Measure.pi (fun _ : Fin n => ρ))
      ((ρ.prod ρ).prod (ρ.prod ρ)) := by
  have hp := pair_selection_preserving ρ n i j hij
  have hq := pair_selection_preserving ρ n k l hkl
  have hi := (coordinate_independence ρ n).indepFun_prodMk_prodMk
    (fun a => measurable_pi_apply a) i j k l hik hil hjk hjl
  refine ⟨((measurable_pi_apply i).prodMk (measurable_pi_apply j)).prodMk
    ((measurable_pi_apply k).prodMk (measurable_pi_apply l)), ?_⟩
  simpa only [hp.map_eq, hq.map_eq] using hi.map_prod_eq_prod_map_map
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
    ((measurable_pi_apply k).prodMk (measurable_pi_apply l)).aemeasurable

private theorem integral_pullback
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {P : Measure X} {Q : Measure Y} {T : X → Y}
    (hT : MeasurePreserving T P Q)
    (f : Y → ℝ) (hf : Integrable f Q) :
    (∫ ξ, f (T ξ) ∂P) = ∫ z, f z ∂Q := by
  have hfm : Integrable f (P.map T) := by
    rw [hT.map_eq]
    exact hf
  calc
    _ = ∫ z, f z ∂P.map T :=
      (integral_map hT.measurable.aemeasurable hfm.aestronglyMeasurable).symm
    _ = _ := by rw [hT.map_eq]

private theorem edge_memLp_two
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (r : Ω → Ω → ℝ)
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (ρ.prod ρ))
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    MemLp (fun ξ : Fin n → Ω => r (ξ i) (ξ j)) 2
      (Measure.pi (fun _ : Fin n => ρ)) :=
  hr2.comp_measurePreserving (pair_selection_preserving ρ n i j hij)

private theorem edge_product_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (r : Ω → Ω → ℝ)
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (ρ.prod ρ))
    (n : ℕ) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l) :
    Integrable (fun ξ : Fin n → Ω =>
      r (ξ i) (ξ j) * r (ξ k) (ξ l))
      (Measure.pi (fun _ : Fin n => ρ)) :=
  (edge_memLp_two ρ r hr2 n i j hij).integrable_mul
    (edge_memLp_two ρ r hr2 n k l hkl)

private theorem integral_edge_sq
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (r : Ω → Ω → ℝ)
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (ρ.prod ρ))
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (∫ ξ : Fin n → Ω, r (ξ i) (ξ j) ^ 2
      ∂Measure.pi (fun _ : Fin n => ρ)) =
      ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(ρ.prod ρ) :=
  integral_pullback (pair_selection_preserving ρ n i j hij)
    (fun z : Ω × Ω => r z.1 z.2 ^ 2) hr2.integrable_sq

private theorem integral_shared_edges
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (r : Ω → Ω → ℝ)
    (hB : Integrable
      (fun t : Ω × (Ω × Ω) => r t.1 t.2.1 * r t.1 t.2.2)
      (ρ.prod (ρ.prod ρ)))
    (n : ℕ) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∫ ξ : Fin n → Ω, r (ξ i) (ξ j) * r (ξ i) (ξ k)
      ∂Measure.pi (fun _ : Fin n => ρ)) =
      ∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
        ∂(ρ.prod (ρ.prod ρ)) :=
  integral_pullback (shared_triple_selection_preserving ρ n i j k hij hik hjk)
    (fun t : Ω × (Ω × Ω) => r t.1 t.2.1 * r t.1 t.2.2) hB

private theorem integral_disjoint_edges
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (r : Ω → Ω → ℝ)
    (hD : Integrable
      (fun d : (Ω × Ω) × (Ω × Ω) => r d.1.1 d.1.2 * r d.2.1 d.2.2)
      ((ρ.prod ρ).prod (ρ.prod ρ)))
    (n : ℕ) (i j k l : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (∫ ξ : Fin n → Ω, r (ξ i) (ξ j) * r (ξ k) (ξ l)
      ∂Measure.pi (fun _ : Fin n => ρ)) =
      ∫ d : (Ω × Ω) × (Ω × Ω), r d.1.1 d.1.2 * r d.2.1 d.2.2
        ∂((ρ.prod ρ).prod (ρ.prod ρ)) :=
  integral_pullback
    (disjoint_four_selection_preserving ρ n i j k l hij hik hil hjk hjl hkl)
    (fun d : (Ω × Ω) × (Ω × Ω) => r d.1.1 d.1.2 * r d.2.1 d.2.2) hD

private def edgeClassValue {n : ℕ} (A B D : ℝ) (i j k l : Fin n) : ℝ :=
  if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then A
  else if i = k ∨ i = l ∨ j = k ∨ j = l then B else D

private theorem integral_edge_product_class
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (r : Ω → Ω → ℝ)
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (ρ.prod ρ))
    (hsymm : ∀ x y, r x y = r y x)
    (hB : Integrable
      (fun t : Ω × (Ω × Ω) => r t.1 t.2.1 * r t.1 t.2.2)
      (ρ.prod (ρ.prod ρ)))
    (hD : Integrable
      (fun d : (Ω × Ω) × (Ω × Ω) => r d.1.1 d.1.2 * r d.2.1 d.2.2)
      ((ρ.prod ρ).prod (ρ.prod ρ)))
    (n : ℕ) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l) :
    (∫ ξ : Fin n → Ω, r (ξ i) (ξ j) * r (ξ k) (ξ l)
      ∂Measure.pi (fun _ : Fin n => ρ)) =
      edgeClassValue
        (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(ρ.prod ρ))
        (∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
          ∂(ρ.prod (ρ.prod ρ)))
        (∫ d : (Ω × Ω) × (Ω × Ω), r d.1.1 d.1.2 * r d.2.1 d.2.2
          ∂((ρ.prod ρ).prod (ρ.prod ρ))) i j k l := by
  classical
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · subst l
      simpa [edgeClassValue, pow_two] using integral_edge_sq ρ r hr2 n i j hij
    · simpa [edgeClassValue, hjl, hij, hij.symm, hkl, hkl.symm] using
        integral_shared_edges ρ r hB n i j l hij hkl hjl
  · by_cases hil : i = l
    · subst l
      by_cases hjk : j = k
      · subst k
        have heq : (fun ξ : Fin n → Ω =>
            r (ξ i) (ξ j) * r (ξ j) (ξ i)) =
            (fun ξ : Fin n → Ω => r (ξ i) (ξ j) ^ 2) := by
          funext ξ
          rw [hsymm (ξ j) (ξ i), pow_two]
        rw [heq, integral_edge_sq ρ r hr2 n i j hij]
        simp [edgeClassValue]
      · have heq : (fun ξ : Fin n → Ω =>
            r (ξ i) (ξ j) * r (ξ k) (ξ i)) =
            (fun ξ : Fin n → Ω => r (ξ i) (ξ j) * r (ξ i) (ξ k)) := by
          funext ξ
          rw [hsymm (ξ k) (ξ i)]
        rw [heq, integral_shared_edges ρ r hB n i j k hij hik hjk]
        simp [edgeClassValue, hik, hjk, hij]
    · by_cases hjk : j = k
      · subst k
        have heq : (fun ξ : Fin n → Ω =>
            r (ξ i) (ξ j) * r (ξ j) (ξ l)) =
            (fun ξ : Fin n → Ω => r (ξ j) (ξ i) * r (ξ j) (ξ l)) := by
          funext ξ
          rw [hsymm (ξ i) (ξ j)]
        rw [heq, integral_shared_edges ρ r hB n j i l hij.symm hkl hil]
        simp [edgeClassValue, hik, hil, hij, hij.symm]
      · by_cases hjl : j = l
        · subst l
          have heq : (fun ξ : Fin n → Ω =>
              r (ξ i) (ξ j) * r (ξ k) (ξ j)) =
              (fun ξ : Fin n → Ω => r (ξ j) (ξ i) * r (ξ j) (ξ k)) := by
            funext ξ
            rw [hsymm (ξ i) (ξ j), hsymm (ξ k) (ξ j)]
          rw [heq, integral_shared_edges ρ r hB n j i k hij.symm hjk hik]
          simp [edgeClassValue, hik, hil, hjk, hij, hij.symm]
        · rw [integral_disjoint_edges ρ r hD n i j k l hij hik hil hjk hjl hkl]
          simp [edgeClassValue, hik, hil, hjk, hjl]

private theorem card_erase_real
    {α : Type*} [DecidableEq α] (s : Finset α) (a : α) (ha : a ∈ s) :
    ((s.erase a).card : ℝ) = (s.card : ℝ) - 1 := by
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
    (Finset.sum_erase_eq_sub (s := s) (f := fun _ : α => (1 : ℝ)) ha)

private theorem card_erase_one {n : ℕ} (i : Fin n) :
    ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
  rw [card_erase_real _ _ (Finset.mem_univ i)]
  simp

private theorem card_erase_two {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (((Finset.univ.erase i).erase j).card : ℝ) = (n : ℝ) - 2 := by
  have hj : j ∈ (Finset.univ : Finset (Fin n)).erase i := by
    simp [hij.symm]
  rw [card_erase_real _ _ hj, card_erase_one i]
  ring

private theorem card_erase_three {n : ℕ} (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ((((Finset.univ.erase i).erase j).erase k).card : ℝ) = (n : ℝ) - 3 := by
  have hk : k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j := by
    simp [hik.symm, hjk.symm]
  rw [card_erase_real _ _ hk, card_erase_two i j hij]
  ring

private theorem sum_split
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) (a : α) (ha : a ∈ s) :
    (∑ x ∈ s, f x) = f a + ∑ x ∈ s.erase a, f x := by
  rw [Finset.sum_erase_eq_sub ha]
  ring

private theorem pair_choose_poly (n : ℕ) :
    (n : ℝ) * ((n : ℝ) - 1) = 2 * (n.choose 2 : ℝ) := by
  have h := Shao.OQ5.P35.pairCount_eq_choose n
  unfold Shao.OQ5.P35.pairCount at h
  nlinarith

private theorem triple_choose_poly (n : ℕ) :
    (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) =
      6 * (n.choose 3 : ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have h2 := pair_choose_poly n
      simp only [Nat.choose_succ_succ, Nat.cast_succ, Nat.cast_add, Nat.cast_one] at *
      nlinarith

private theorem quadruple_choose_poly (n : ℕ) :
    (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) =
      24 * (n.choose 4 : ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have h3 := triple_choose_poly n
      simp only [Nat.choose_succ_succ, Nat.cast_succ, Nat.cast_add, Nat.cast_one] at *
      nlinarith

private theorem sum_class_first
    {n : ℕ} (A B D : ℝ) (i j : Fin n) (hij : i ≠ j) :
    (∑ l ∈ Finset.univ.erase i, edgeClassValue A B D i j i l) =
      A + ((n : ℝ) - 2) * B := by
  classical
  have hj : j ∈ (Finset.univ : Finset (Fin n)).erase i := by simp [hij.symm]
  rw [sum_split _ (fun l => edgeClassValue A B D i j i l) j hj]
  have hrest :
      (∑ l ∈ (Finset.univ.erase i).erase j, edgeClassValue A B D i j i l) =
        ((n : ℝ) - 2) * B := by
    calc
      _ = ∑ l ∈ (Finset.univ.erase i).erase j, B := by
        apply Finset.sum_congr rfl
        intro l hl
        have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
        simp [edgeClassValue, hij, hij.symm, hlj.symm]
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [card_erase_two i j hij]
  rw [hrest]
  simp [edgeClassValue]

private theorem sum_class_second
    {n : ℕ} (A B D : ℝ) (i j : Fin n) (hij : i ≠ j) :
    (∑ l ∈ Finset.univ.erase j, edgeClassValue A B D i j j l) =
      A + ((n : ℝ) - 2) * B := by
  classical
  have hi : i ∈ (Finset.univ : Finset (Fin n)).erase j := by simp [hij]
  rw [sum_split _ (fun l => edgeClassValue A B D i j j l) i hi]
  have hrest :
      (∑ l ∈ (Finset.univ.erase j).erase i, edgeClassValue A B D i j j l) =
        ((n : ℝ) - 2) * B := by
    calc
      _ = ∑ l ∈ (Finset.univ.erase j).erase i, B := by
        apply Finset.sum_congr rfl
        intro l hl
        have hli : l ≠ i := (Finset.mem_erase.mp hl).1
        simp [edgeClassValue, hij, hli.symm]
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [card_erase_two j i hij.symm]
  rw [hrest]
  simp [edgeClassValue]

private theorem sum_class_other
    {n : ℕ} (A B D : ℝ) (i j k : Fin n)
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    (∑ l ∈ Finset.univ.erase k, edgeClassValue A B D i j k l) =
      2 * B + ((n : ℝ) - 3) * D := by
  classical
  have hi : i ∈ (Finset.univ : Finset (Fin n)).erase k := by simp [hki.symm]
  have hj : j ∈ ((Finset.univ : Finset (Fin n)).erase k).erase i := by
    simp [hki.symm, hkj.symm, hij.symm]
  rw [sum_split _ (fun l => edgeClassValue A B D i j k l) i hi]
  rw [sum_split _ (fun l => edgeClassValue A B D i j k l) j hj]
  have hrest :
      (∑ l ∈ ((Finset.univ.erase k).erase i).erase j,
        edgeClassValue A B D i j k l) = ((n : ℝ) - 3) * D := by
    calc
      _ = ∑ l ∈ ((Finset.univ.erase k).erase i).erase j, D := by
        apply Finset.sum_congr rfl
        intro l hl
        have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
        have hli : l ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
        simp [edgeClassValue, hki.symm, hkj.symm, hli.symm, hlj.symm]
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [card_erase_three k i j hki hkj hij]
  rw [hrest]
  simp [edgeClassValue, hki.symm, hkj.symm, hij, hij.symm]
  ring

private theorem sum_class_fixed_edge
    {n : ℕ} (A B D : ℝ) (i j : Fin n) (hij : i ≠ j) :
    (∑ k : Fin n, ∑ l ∈ Finset.univ.erase k, edgeClassValue A B D i j k l) =
      2 * A + 4 * ((n : ℝ) - 2) * B +
        ((n : ℝ) - 2) * ((n : ℝ) - 3) * D := by
  classical
  let f : Fin n → ℝ := fun k =>
    ∑ l ∈ Finset.univ.erase k, edgeClassValue A B D i j k l
  have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hj : j ∈ (Finset.univ : Finset (Fin n)).erase i := by simp [hij.symm]
  change (∑ k : Fin n, f k) = _
  rw [sum_split Finset.univ f i hi, sum_split _ f j hj]
  have hfi : f i = A + ((n : ℝ) - 2) * B := sum_class_first A B D i j hij
  have hfj : f j = A + ((n : ℝ) - 2) * B := sum_class_second A B D i j hij
  have hrest :
      (∑ k ∈ (Finset.univ.erase i).erase j, f k) =
        ((n : ℝ) - 2) * (2 * B + ((n : ℝ) - 3) * D) := by
    calc
      _ = ∑ k ∈ (Finset.univ.erase i).erase j,
          (2 * B + ((n : ℝ) - 3) * D) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
        have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
        exact sum_class_other A B D i j k hij hki hkj
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [card_erase_two i j hij]
  rw [hfi, hfj, hrest]
  ring

private theorem sum_off_diagonal_const (n : ℕ) (C : ℝ) :
    (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, C) =
      (n : ℝ) * ((n : ℝ) - 1) * C := by
  classical
  calc
    _ = ∑ i : Fin n, ((n : ℝ) - 1) * C := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [card_erase_one i]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

private theorem ordered_edge_pair_count_sum (n : ℕ) (A B D : ℝ) :
    (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
      ∑ k : Fin n, ∑ l ∈ Finset.univ.erase k, edgeClassValue A B D i j k l) =
      4 * ((n.choose 2 : ℝ) * A + 6 * (n.choose 3 : ℝ) * B +
        6 * (n.choose 4 : ℝ) * D) := by
  classical
  calc
    _ = ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
        (2 * A + 4 * ((n : ℝ) - 2) * B +
          ((n : ℝ) - 2) * ((n : ℝ) - 3) * D) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact sum_class_fixed_edge A B D i j (Finset.mem_erase.mp hj).1.symm
    _ = (n : ℝ) * ((n : ℝ) - 1) *
        (2 * A + 4 * ((n : ℝ) - 2) * B +
          ((n : ℝ) - 2) * ((n : ℝ) - 3) * D) :=
      sum_off_diagonal_const n _
    _ = 2 * ((n : ℝ) * ((n : ℝ) - 1)) * A +
        4 * ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) * B +
        ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3)) * D := by
      ring
    _ = _ := by
      rw [quadruple_choose_poly, triple_choose_poly, pair_choose_poly]
      ring

private theorem sum_row_class (n : ℕ) (A B : ℝ) :
    (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
      ∑ k ∈ Finset.univ.erase i, if j = k then A else B) =
      2 * (n.choose 2 : ℝ) * A + 6 * (n.choose 3 : ℝ) * B := by
  classical
  have hf (i j : Fin n) (hij : i ≠ j) :
      (∑ k ∈ Finset.univ.erase i, if j = k then A else B) =
        A + ((n : ℝ) - 2) * B := by
    have hj : j ∈ (Finset.univ : Finset (Fin n)).erase i := by simp [hij.symm]
    rw [sum_split _ (fun k => if j = k then A else B) j hj]
    have hrest :
        (∑ k ∈ (Finset.univ.erase i).erase j, if j = k then A else B) =
          ((n : ℝ) - 2) * B := by
      calc
        _ = ∑ k ∈ (Finset.univ.erase i).erase j, B := by
          apply Finset.sum_congr rfl
          intro k hk
          exact if_neg (Finset.mem_erase.mp hk).1.symm
        _ = _ := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [card_erase_two i j hij]
    rw [hrest]
    simp
  calc
    _ = ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
        (A + ((n : ℝ) - 2) * B) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hf i j (Finset.mem_erase.mp hj).1.symm
    _ = (n : ℝ) * ((n : ℝ) - 1) * (A + ((n : ℝ) - 2) * B) :=
      sum_off_diagonal_const n _
    _ = ((n : ℝ) * ((n : ℝ) - 1)) * A +
        ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) * B := by ring
    _ = _ := by rw [triple_choose_poly, pair_choose_poly]

private theorem integral_two_sums
    {X α β : Type*} [MeasurableSpace X]
    (P : Measure X) (s : Finset α) (t : α → Finset β)
    (f : α → β → X → ℝ)
    (hf : ∀ i ∈ s, ∀ j ∈ t i, Integrable (f i j) P) :
    (∫ ξ, ∑ i ∈ s, ∑ j ∈ t i, f i j ξ ∂P) =
      ∑ i ∈ s, ∑ j ∈ t i, ∫ ξ, f i j ξ ∂P := by
  classical
  rw [integral_finsetSum s (fun i hi => integrable_finsetSum (t i) (hf i hi))]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_finsetSum (t i) (hf i hi)

private theorem finite_row_memLp_two
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (r : Ω → Ω → ℝ)
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (ρ.prod ρ))
    (n : ℕ) (i : Fin n) :
    MemLp (fun ξ : Fin n → Ω =>
      Shao.OQ6.ResidualDeletion.rowSum (fun j k => r (ξ j) (ξ k)) i) 2
      (Measure.pi (fun _ : Fin n => ρ)) := by
  classical
  unfold Shao.OQ6.ResidualDeletion.rowSum
  exact memLp_finsetSum _ (fun j hj =>
    edge_memLp_two ρ r hr2 n i j (Finset.mem_erase.mp hj).1.symm)

private theorem finite_pair_sum_memLp_two
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (r : Ω → Ω → ℝ)
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (ρ.prod ρ))
    (n : ℕ) :
    MemLp (fun ξ : Fin n → Ω =>
      Shao.OQ5.P35.unorderedPairSum (fun i j => r (ξ i) (ξ j))) 2
      (Measure.pi (fun _ : Fin n => ρ)) := by
  classical
  unfold Shao.OQ5.P35.unorderedPairSum
  apply memLp_finsetSum
  intro i hi
  apply memLp_finsetSum
  intro j hj
  by_cases hij : i < j
  · simpa only [if_pos hij] using
      edge_memLp_two ρ r hr2 n i j (ne_of_lt hij)
  · simp only [if_neg hij]
    simp

private theorem finite_pair_sum_identity
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (r : Ω → Ω → ℝ)
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (ρ.prod ρ))
    (hsymm : ∀ x y, r x y = r y x)
    (hB : Integrable
      (fun t : Ω × (Ω × Ω) => r t.1 t.2.1 * r t.1 t.2.2)
      (ρ.prod (ρ.prod ρ)))
    (hD : Integrable
      (fun d : (Ω × Ω) × (Ω × Ω) => r d.1.1 d.1.2 * r d.2.1 d.2.2)
      ((ρ.prod ρ).prod (ρ.prod ρ)))
    (n : ℕ) :
    let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => ρ)
    let F : (Fin n → Ω) → ℝ := fun ξ =>
      Shao.OQ5.P35.unorderedPairSum (fun i j => r (ξ i) (ξ j))
    let A : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(ρ.prod ρ)
    let B : ℝ := ∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
      ∂(ρ.prod (ρ.prod ρ))
    let D : ℝ := ∫ d : (Ω × Ω) × (Ω × Ω),
      r d.1.1 d.1.2 * r d.2.1 d.2.2 ∂((ρ.prod ρ).prod (ρ.prod ρ))
    (∫ ξ : Fin n → Ω, F ξ ^ 2 ∂P) =
      (n.choose 2 : ℝ) * A + 6 * (n.choose 3 : ℝ) * B +
        6 * (n.choose 4 : ℝ) * D := by
  classical
  let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => ρ)
  let F : (Fin n → Ω) → ℝ := fun ξ =>
    Shao.OQ5.P35.unorderedPairSum (fun i j => r (ξ i) (ξ j))
  let A : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(ρ.prod ρ)
  let B : ℝ := ∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
    ∂(ρ.prod (ρ.prod ρ))
  let D : ℝ := ∫ d : (Ω × Ω) × (Ω × Ω),
    r d.1.1 d.1.2 * r d.2.1 d.2.2 ∂((ρ.prod ρ).prod (ρ.prod ρ))
  change (∫ ξ : Fin n → Ω, F ξ ^ 2 ∂P) =
    (n.choose 2 : ℝ) * A + 6 * (n.choose 3 : ℝ) * B +
      6 * (n.choose 4 : ℝ) * D
  have hproducts (i j k l : Fin n) (hj : j ∈ Finset.univ.erase i)
      (hl : l ∈ Finset.univ.erase k) :
      Integrable (fun ξ : Fin n → Ω =>
        r (ξ i) (ξ j) * r (ξ k) (ξ l)) P :=
    edge_product_integrable ρ r hr2 n i j k l
      (Finset.mem_erase.mp hj).1.symm (Finset.mem_erase.mp hl).1.symm
  have hquad :
      4 * (∫ ξ : Fin n → Ω, F ξ ^ 2 ∂P) =
        4 * ((n.choose 2 : ℝ) * A + 6 * (n.choose 3 : ℝ) * B +
          6 * (n.choose 4 : ℝ) * D) := by
    calc
      _ = ∫ ξ : Fin n → Ω, 4 * F ξ ^ 2 ∂P := by rw [integral_const_mul]
      _ = ∫ ξ : Fin n → Ω,
          ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
          ∑ k : Fin n, ∑ l ∈ Finset.univ.erase k,
            r (ξ i) (ξ j) * r (ξ k) (ξ l) ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ξ => by
          have hrows := Shao.OQ5.P35.offDiagonalSum_eq_two_unordered
            (fun i j => r (ξ i) (ξ j)) (fun i j => hsymm (ξ i) (ξ j))
          calc
            4 * F ξ ^ 2 =
                (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, r (ξ i) (ξ j)) ^ 2 := by
              rw [hrows]
              dsimp only [F]
              ring
            _ = _ := by
              rw [pow_two]
              simp_rw [Finset.sum_mul, Finset.mul_sum])
      _ = ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
          ∫ ξ : Fin n → Ω, ∑ k : Fin n, ∑ l ∈ Finset.univ.erase k,
            r (ξ i) (ξ j) * r (ξ k) (ξ l) ∂P := by
        exact integral_two_sums P Finset.univ (fun i => Finset.univ.erase i) _
          (fun i hi j hj => integrable_finsetSum Finset.univ (fun k hk =>
            integrable_finsetSum (Finset.univ.erase k) (fun l hl =>
              hproducts i j k l hj hl)))
      _ = ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
          ∑ k : Fin n, ∑ l ∈ Finset.univ.erase k,
            ∫ ξ : Fin n → Ω, r (ξ i) (ξ j) * r (ξ k) (ξ l) ∂P := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact integral_two_sums P Finset.univ (fun k => Finset.univ.erase k) _
          (fun k hk l hl => hproducts i j k l hj hl)
      _ = ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
          ∑ k : Fin n, ∑ l ∈ Finset.univ.erase k, edgeClassValue A B D i j k l := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        exact integral_edge_product_class ρ r hr2 hsymm hB hD n i j k l
          (Finset.mem_erase.mp hj).1.symm (Finset.mem_erase.mp hl).1.symm
      _ = _ := ordered_edge_pair_count_sum n A B D
  nlinarith

private theorem finite_row_square_identity
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (r : Ω → Ω → ℝ)
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (ρ.prod ρ))
    (hB : Integrable
      (fun t : Ω × (Ω × Ω) => r t.1 t.2.1 * r t.1 t.2.2)
      (ρ.prod (ρ.prod ρ)))
    (n : ℕ) :
    let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => ρ)
    let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Shao.OQ6.ResidualDeletion.rowSum (fun j k => r (ξ j) (ξ k)) i
    let A : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(ρ.prod ρ)
    let B : ℝ := ∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
      ∂(ρ.prod (ρ.prod ρ))
    (∫ ξ : Fin n → Ω, (∑ i : Fin n, ψ ξ i ^ 2) ∂P) =
      2 * (n.choose 2 : ℝ) * A + 6 * (n.choose 3 : ℝ) * B := by
  classical
  let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => ρ)
  let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Shao.OQ6.ResidualDeletion.rowSum (fun j k => r (ξ j) (ξ k)) i
  let A : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(ρ.prod ρ)
  let B : ℝ := ∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
    ∂(ρ.prod (ρ.prod ρ))
  change (∫ ξ : Fin n → Ω, (∑ i : Fin n, ψ ξ i ^ 2) ∂P) =
    2 * (n.choose 2 : ℝ) * A + 6 * (n.choose 3 : ℝ) * B
  have hrow (i : Fin n) : MemLp (fun ξ => ψ ξ i) 2 P :=
    finite_row_memLp_two ρ r hr2 n i
  have hproducts (i j k : Fin n) (hj : j ∈ Finset.univ.erase i)
      (hk : k ∈ Finset.univ.erase i) :
      Integrable (fun ξ : Fin n → Ω =>
        r (ξ i) (ξ j) * r (ξ i) (ξ k)) P :=
    edge_product_integrable ρ r hr2 n i j i k
      (Finset.mem_erase.mp hj).1.symm (Finset.mem_erase.mp hk).1.symm
  have hmoment (i j k : Fin n) (hj : j ∈ Finset.univ.erase i)
      (hk : k ∈ Finset.univ.erase i) :
      (∫ ξ : Fin n → Ω, r (ξ i) (ξ j) * r (ξ i) (ξ k) ∂P) =
        if j = k then A else B := by
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    have hik : i ≠ k := (Finset.mem_erase.mp hk).1.symm
    by_cases hjk : j = k
    · subst k
      simpa [P, A, pow_two] using integral_edge_sq ρ r hr2 n i j hij
    · rw [if_neg hjk]
      exact integral_shared_edges ρ r hB n i j k hij hik hjk
  calc
    _ = ∑ i : Fin n, ∫ ξ : Fin n → Ω, ψ ξ i ^ 2 ∂P :=
      integral_finsetSum Finset.univ (fun i hi => (hrow i).integrable_sq)
    _ = ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ Finset.univ.erase i,
        ∫ ξ : Fin n → Ω, r (ξ i) (ξ j) * r (ξ i) (ξ k) ∂P := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        _ = ∫ ξ : Fin n → Ω, ∑ j ∈ Finset.univ.erase i,
            ∑ k ∈ Finset.univ.erase i, r (ξ i) (ξ j) * r (ξ i) (ξ k) ∂P := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun ξ => by
            dsimp only [ψ, Shao.OQ6.ResidualDeletion.rowSum]
            rw [pow_two, Finset.sum_mul_sum])
        _ = _ := integral_two_sums P (Finset.univ.erase i)
          (fun _ => Finset.univ.erase i) _ (fun j hj k hk => hproducts i j k hj hk)
    _ = ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ Finset.univ.erase i,
        if j = k then A else B := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      exact hmoment i j k hj hk
    _ = _ := sum_row_class n A B

theorem unordered_pair_sum_second_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun z : Ω × Ω => r z.1 z.2))
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ))
    (hrsymm : ∀ o y, r o y = r y o)
    (hrcan : ∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0)
    (s : ℝ) (hs : 0 ≤ s)
    (hrsecond :
      (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)) ≤ s ^ 2)
    (L : Ω → ℝ) (hL : Measurable L) (K : ℝ)
    (hLnonneg : ∀ o, 0 ≤ L o)
    (hLle : ∀ o, L o ≤ K)
    (hLmass : (∫ o, L o ∂μ) = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hδsecond : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ ε ^ 2)
    (n : ℕ) :
    let ρ : Measure Ω :=
      μ.withDensity (fun o => ENNReal.ofReal (L o))
    let P : Measure (Fin n → Ω) :=
      Measure.pi (fun _ : Fin n => ρ)
    let F : (Fin n → Ω) → ℝ := fun ξ =>
      Shao.OQ5.P35.unorderedPairSum (fun i j => r (ξ i) (ξ j))
    let A : ℝ :=
      ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(ρ.prod ρ)
    let B : ℝ :=
      ∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
        ∂(ρ.prod (ρ.prod ρ))
    let D : ℝ :=
      ∫ d : (Ω × Ω) × (Ω × Ω),
        r d.1.1 d.1.2 * r d.2.1 d.2.2
        ∂((ρ.prod ρ).prod (ρ.prod ρ))
    IsProbabilityMeasure ρ ∧
      IsProbabilityMeasure P ∧
      MemLp F 2 P ∧
      Integrable (fun ξ => F ξ ^ 2) P ∧
      (∫ ξ : Fin n → Ω, F ξ ^ 2 ∂P) =
        (n.choose 2 : ℝ) * A +
          6 * (n.choose 3 : ℝ) * B +
          6 * (n.choose 4 : ℝ) * D ∧
      (∫ ξ : Fin n → Ω, F ξ ^ 2 ∂P) ≤
        ((n.choose 2 : ℝ) * K ^ 2 +
          6 * (n.choose 3 : ℝ) * K * ε ^ 2 +
          6 * (n.choose 4 : ℝ) * ε ^ 4) * s ^ 2 := by
  classical
  let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
  have hc := CanonicalTilt.pair_contraction μ r hr hr2 hrsymm hrcan s hs hrsecond
    L hL K hLnonneg hLle hLmass ε hε hδsecond
  rcases hc with ⟨hρ, hK, hL2, hδ2, hrρ2, hrρ1, hrρsq, hA,
    hweighted, hcentered, hcancel, hmean⟩
  letI : IsProbabilityMeasure ρ := hρ
  have hb := QuantitativeOverlap.shared_tilted_moment_bound μ r hr hr2 hrcan
    s hs hrsecond L hL K hLnonneg hLle hLmass ε hε hδsecond
  rcases hb with ⟨habs, hf2, hrows, hBI, hBid, hB0, hBle⟩
  have hd := QuantitativeOverlap.disjoint_tilted_moment_bound μ r hr hr2 hrsymm hrcan
    s hs hrsecond L hL K hLnonneg hLle hLmass ε hε hδsecond
  rcases hd with ⟨hDI, hDid, hD0, hDle⟩
  have hF2 := finite_pair_sum_memLp_two ρ r hrρ2 n
  have hid := finite_pair_sum_identity ρ r hrρ2 hrsymm hBI hDI n
  refine ⟨hρ, inferInstance, hF2, hF2.integrable_sq, hid, ?_⟩
  rw [hid]
  calc
    _ ≤ (n.choose 2 : ℝ) * (K ^ 2 * s ^ 2) +
        (6 * (n.choose 3 : ℝ)) * (K * ε ^ 2 * s ^ 2) +
        (6 * (n.choose 4 : ℝ)) * (s ^ 2 * ε ^ 4) :=
      add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg _))
          (mul_le_mul_of_nonneg_left hBle
            (mul_nonneg (by norm_num) (Nat.cast_nonneg _))))
        (mul_le_mul_of_nonneg_left hDle
          (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
    _ = _ := by ring

theorem row_square_sum_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun z : Ω × Ω => r z.1 z.2))
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ))
    (hrsymm : ∀ o y, r o y = r y o)
    (hrcan : ∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0)
    (s : ℝ) (hs : 0 ≤ s)
    (hrsecond :
      (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)) ≤ s ^ 2)
    (L : Ω → ℝ) (hL : Measurable L) (K : ℝ)
    (hLnonneg : ∀ o, 0 ≤ L o)
    (hLle : ∀ o, L o ≤ K)
    (hLmass : (∫ o, L o ∂μ) = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hδsecond : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ ε ^ 2)
    (n : ℕ) :
    let ρ : Measure Ω :=
      μ.withDensity (fun o => ENNReal.ofReal (L o))
    let P : Measure (Fin n → Ω) :=
      Measure.pi (fun _ : Fin n => ρ)
    let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Shao.OQ6.ResidualDeletion.rowSum
        (fun j k => r (ξ j) (ξ k)) i
    let Λsq : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ i : Fin n, ψ ξ i ^ 2
    let A : ℝ :=
      ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(ρ.prod ρ)
    let B : ℝ :=
      ∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
        ∂(ρ.prod (ρ.prod ρ))
    IsProbabilityMeasure ρ ∧
      IsProbabilityMeasure P ∧
      (∀ i : Fin n, MemLp (fun ξ => ψ ξ i) 2 P) ∧
      Integrable Λsq P ∧
      (∫ ξ : Fin n → Ω, Λsq ξ ∂P) =
        2 * (n.choose 2 : ℝ) * A +
          6 * (n.choose 3 : ℝ) * B ∧
      (∫ ξ : Fin n → Ω, Λsq ξ ∂P) ≤
        (2 * (n.choose 2 : ℝ) * K ^ 2 +
          6 * (n.choose 3 : ℝ) * K * ε ^ 2) * s ^ 2 := by
  classical
  let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
  have hc := CanonicalTilt.pair_contraction μ r hr hr2 hrsymm hrcan s hs hrsecond
    L hL K hLnonneg hLle hLmass ε hε hδsecond
  rcases hc with ⟨hρ, hK, hL2, hδ2, hrρ2, hrρ1, hrρsq, hA,
    hweighted, hcentered, hcancel, hmean⟩
  letI : IsProbabilityMeasure ρ := hρ
  have hb := QuantitativeOverlap.shared_tilted_moment_bound μ r hr hr2 hrcan
    s hs hrsecond L hL K hLnonneg hLle hLmass ε hε hδsecond
  rcases hb with ⟨habs, hf2, hrows, hBI, hBid, hB0, hBle⟩
  have hrow (i : Fin n) := finite_row_memLp_two ρ r hrρ2 n i
  have hΛ := integrable_finsetSum Finset.univ
    (fun i hi => (hrow i).integrable_sq)
  have hid := finite_row_square_identity ρ r hrρ2 hBI n
  refine ⟨hρ, inferInstance, hrow, hΛ, hid, ?_⟩
  rw [hid]
  calc
    _ ≤ (2 * (n.choose 2 : ℝ)) * (K ^ 2 * s ^ 2) +
        (6 * (n.choose 3 : ℝ)) * (K * ε ^ 2 * s ^ 2) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hA
          (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
        (mul_le_mul_of_nonneg_left hBle
          (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
    _ = _ := by ring

end

end Shao.OQ6.FiniteTiltedMoments
