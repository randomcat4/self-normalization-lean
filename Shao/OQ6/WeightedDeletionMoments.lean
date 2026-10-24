import Shao.OQ6.ActualQuadraticTiltMoments
import Shao.OQ6.PartialObservationTilt
import Shao.OQ6.FiniteTiltedMoments
import Shao.OQ6.ResidualDeletion
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Shao.OQ6.CappedSectionEnergy
import Shao.OQ6.CanonicalTilt
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Positivity

/-!
Original-length weighted deletion: local unelaborated production candidate.
The helper declarations below are frozen by frozen-helpers-A.json.
The public analytic theorem will be added after its dependencies are proved.
-/

set_option autoImplicit false

namespace Shao.OQ6.WeightedDeletionMoments

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem wd_insert_fubini
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ρ : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    (n : ℕ) (i : Fin n) :
    let J := {j : Fin n // j ≠ i}
    let P : Measure (J → Ω) := Measure.pi (fun _ : J => ρ)
    let H : Measure (Fin n → Ω) := Measure.pi
      (fun j : Fin n => if j = i then μ else ρ)
    let ins : Ω × (J → Ω) → Fin n → Ω := fun z j =>
      if hji : j = i then z.1 else z.2 ⟨j, hji⟩
    MeasurePreserving ins (μ.prod P) H ∧
      (∀ f : (Fin n → Ω) → ℝ, Integrable f H →
        Integrable (fun z : Ω × (J → Ω) => f (ins z)) (μ.prod P) ∧
        (∫ ξ, f ξ ∂H) =
          ∫ o, (∫ Y, f (ins (o, Y)) ∂P) ∂μ) := by
  classical
  dsimp only
  let J := {j : Fin n // j ≠ i}
  let P : Measure (J → Ω) := Measure.pi (fun _ : J => ρ)
  let H : Measure (Fin n → Ω) := Measure.pi
    (fun j : Fin n => if j = i then μ else ρ)
  let ins : Ω × (J → Ω) → Fin n → Ω := fun z j =>
    if hji : j = i then z.1 else z.2 ⟨j, hji⟩
  have him : Measurable ins := by
    apply measurable_pi_lambda
    intro j
    by_cases hji : j = i
    · simpa only [ins, dif_pos hji] using
        (measurable_fst : Measurable (fun z : Ω × (J → Ω) => z.1))
    · simpa only [ins, dif_neg hji, Function.comp_def] using
        (measurable_pi_apply (⟨j, hji⟩ : J)).comp measurable_snd
  let em : (Ω × (J → Ω)) ≃ᵐ (Fin n → Ω) :=
    { toEquiv :=
        { toFun := ins
          invFun := fun ξ => (ξ i, fun j => ξ j)
          left_inv := by
            rintro ⟨o, Y⟩
            apply Prod.ext
            · simp [ins]
            · funext j
              simp [ins, j.property]
          right_inv := by
            intro ξ
            funext j
            by_cases hji : j = i
            · subst j
              simp [ins]
            · simp [ins, hji] }
      measurable_toFun := him
      measurable_invFun := by
        refine (measurable_pi_apply i).prodMk ?_
        apply measurable_pi_lambda
        intro j
        exact measurable_pi_apply j.val }
  have hmp : MeasurePreserving ins (μ.prod P) H := by
    refine ⟨him, ?_⟩
    apply (Measure.pi_eq fun s hs => ?_).symm
    have hpre : em ⁻¹' Set.pi Set.univ s =
        s i ×ˢ Set.pi Set.univ (fun j : J => s j) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
        Set.mem_prod]
      change (∀ j : Fin n, ins z j ∈ s j) ↔
        z.1 ∈ s i ∧ ∀ j : J, z.2 j ∈ s j
      constructor
      · intro hz
        refine ⟨?_, ?_⟩
        · simpa [ins] using hz i
        · intro j
          simpa [ins, j.property] using hz j
      · rintro ⟨hi, hJ⟩ j
        by_cases hji : j = i
        · subst j
          simpa [ins] using hi
        · simpa [ins, hji] using hJ ⟨j, hji⟩
    change (μ.prod P).map em (Set.pi Set.univ s) = _
    rw [em.map_apply, hpre, Measure.prod_prod, Measure.pi_pi]
    letI : Fintype {j : Fin n // j = i} :=
      Subtype.fintype (fun j : Fin n => j = i)
    have hprod := Fintype.prod_subtype_mul_prod_subtype
      (fun j : Fin n => j = i)
      (fun j : Fin n => (if j = i then μ else ρ) (s j))
    have hone :
        (∏ j : {j : Fin n // j = i},
          (if j.val = i then μ else ρ) (s j)) = μ (s i) := by
      letI : Unique {j : Fin n // j = i} :=
        { default := ⟨i, rfl⟩
          uniq := fun j => Subtype.ext j.property }
      simp only [Fintype.prod_unique]
      rw [(default : {j : Fin n // j = i}).property]
      simp
    have hrest :
        (∏ j : {j : Fin n // ¬j = i},
          (if j.val = i then μ else ρ) (s j)) =
          ∏ j : J, ρ (s j) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [if_neg j.property]
    change
      (∏ j : {j : Fin n // j = i}, (if j.val = i then μ else ρ) (s j)) *
        (∏ j : {j : Fin n // ¬j = i}, (if j.val = i then μ else ρ) (s j)) =
        ∏ j : Fin n, (if j = i then μ else ρ) (s j) at hprod
    rw [hone, hrest] at hprod
    exact hprod
  refine ⟨hmp, ?_⟩
  intro f hf
  have hcomp : Integrable (fun z : Ω × (J → Ω) => f (ins z))
      (μ.prod P) := hmp.integrable_comp_of_integrable hf
  refine ⟨hcomp, ?_⟩
  have hfm : Integrable f ((μ.prod P).map ins) := by
    rw [hmp.map_eq]
    exact hf
  calc
    (∫ ξ, f ξ ∂H) = ∫ z, f (ins z) ∂(μ.prod P) := by
      rw [← hmp.map_eq]
      exact integral_map hmp.measurable.aemeasurable hfm.aestronglyMeasurable
    _ = ∫ o, (∫ Y, f (ins (o, Y)) ∂P) ∂μ := integral_prod _ hcomp

private theorem wd_deleted_row_reindex
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (r : Ω → Ω → ℝ)
    (n : ℕ) (i : Fin n)
    (e : Fin (n - 1) ≃ {j : Fin n // j ≠ i}) :
    let J := {j : Fin n // j ≠ i}
    let P : Measure (J → Ω) := Measure.pi (fun _ : J => ρ)
    let Pdel : Measure (Fin (n - 1) → Ω) :=
      Measure.pi (fun _ : Fin (n - 1) => ρ)
    let reindex : (J → Ω) → Fin (n - 1) → Ω :=
      fun Y k => Y (e k)
    let T : (J → Ω) → J → ℝ := fun Y j =>
      ∑ k ∈ Finset.univ.erase j, r (Y j) (Y k)
    let E : (Fin n → Ω) → Fin n → Fin n → ℝ :=
      fun ξ j k => r (ξ j) (ξ k)
    MeasurePreserving reindex P Pdel ∧
      (∀ Y : J → Ω,
        (∑ j : J, T Y j ^ 2) =
          ∑ k : Fin (n - 1),
            Shao.OQ6.ResidualDeletion.rowSum
              (fun u v => r (reindex Y u) (reindex Y v)) k ^ 2) ∧
      (∀ ξ : Fin n → Ω,
        (∑ j : Fin n,
          Shao.OQ6.ResidualDeletion.rowSum
            (Shao.OQ6.ResidualDeletion.eraseIncident (E ξ) i) j ^ 2) =
          ∑ j : J, T (fun k => ξ k) j ^ 2) := by
  classical
  dsimp only
  let J := {j : Fin n // j ≠ i}
  let P : Measure (J → Ω) := Measure.pi (fun _ : J => ρ)
  let Pdel : Measure (Fin (n - 1) → Ω) :=
    Measure.pi (fun _ : Fin (n - 1) => ρ)
  let reindex : (J → Ω) → Fin (n - 1) → Ω := fun Y k => Y (e k)
  let T : (J → Ω) → J → ℝ := fun Y j =>
    ∑ k ∈ Finset.univ.erase j, r (Y j) (Y k)
  let E : (Fin n → Ω) → Fin n → Fin n → ℝ :=
    fun ξ j k => r (ξ j) (ξ k)
  have hreindex : MeasurePreserving reindex P Pdel := by
    have hp := measurePreserving_piCongrLeft (α := fun _ : Fin (n - 1) => Ω)
      (fun _ : Fin (n - 1) => ρ) e.symm
    have heq :
        ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin (n - 1) => Ω) e.symm) =
          reindex := by
      funext Y k
      simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, reindex]
    rw [heq] at hp
    exact hp
  have hrow (Y : J → Ω) (k : Fin (n - 1)) :
      T Y (e k) = Shao.OQ6.ResidualDeletion.rowSum
        (fun u v => r (reindex Y u) (reindex Y v)) k := by
    unfold T Shao.OQ6.ResidualDeletion.rowSum
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ (e k)),
      Finset.sum_erase_eq_sub (Finset.mem_univ k)]
    rw [← e.sum_comp (fun j : J => r (Y (e k)) (Y j))]
  have hsumJ (f : Fin n → ℝ) (hfi : f i = 0) :
      (∑ j : Fin n, f j) = ∑ j : J, f j := by
    letI : Fintype {j : Fin n // j = i} :=
      Subtype.fintype (fun j : Fin n => j = i)
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun j : Fin n => j = i) f
    have hzero : (∑ j : {j : Fin n // j = i}, f j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [j.property, hfi]
    change
      (∑ j : {j : Fin n // j = i}, f j) + (∑ j : J, f j) =
        ∑ j : Fin n, f j at hsplit
    simpa only [hzero, zero_add] using hsplit.symm
  have herow (ξ : Fin n → Ω) (j : J) :
      Shao.OQ6.ResidualDeletion.rowSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (E ξ) i) j =
      T (fun k => ξ k) j := by
    let f : Fin n → ℝ :=
      Shao.OQ6.ResidualDeletion.eraseIncident (E ξ) i j
    have hfi : f i = 0 := by
      simp [f, Shao.OQ6.ResidualDeletion.eraseIncident]
    have hfk (k : J) : f k = r (ξ j) (ξ k) := by
      simp [f, Shao.OQ6.ResidualDeletion.eraseIncident, E, j.property, k.property]
    change (∑ k ∈ Finset.univ.erase j.val, f k) = _
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j.val), hsumJ f hfi]
    change (∑ k : J, f k) - f j.val = T (fun k => ξ k) j
    simp_rw [hfk]
    unfold T
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)]
  refine ⟨hreindex, ?_, ?_⟩
  · intro Y
    rw [← e.sum_comp (fun j : J => T Y j ^ 2)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hrow]
  · intro ξ
    rw [hsumJ
      (fun j => Shao.OQ6.ResidualDeletion.rowSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (E ξ) i) j ^ 2)
      (by simp [Shao.OQ6.ResidualDeletion.rowSum_eraseIncident])]
    apply Finset.sum_congr rfl
    intro j hj
    rw [herow]


private theorem wd_product_row_second
    {Ω J : Type*} [MeasurableSpace Ω] [Fintype J] [DecidableEq J]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (f : Ω → ℝ) (hf : Measurable f) (hf2 : MemLp f 2 ρ) :
    let P : Measure (J → Ω) := Measure.pi (fun _ : J => ρ)
    let S : (J → Ω) → ℝ := fun Y => ∑ j : J, f (Y j)
    let E : (J → Ω) → ℝ := fun Y => ∑ j : J, f (Y j) ^ 2
    MemLp S 2 P ∧ Integrable (fun Y => S Y ^ 2) P ∧
      Integrable E P ∧
      (∫ Y, S Y ^ 2 ∂P) =
        (Fintype.card J : ℝ) * (∫ y, f y ^ 2 ∂ρ) +
        (Fintype.card J : ℝ) * ((Fintype.card J : ℝ) - 1) *
          (∫ y, f y ∂ρ) ^ 2 ∧
      (∫ Y, E Y ∂P) =
        (Fintype.card J : ℝ) * (∫ y, f y ^ 2 ∂ρ) := by
  classical
  dsimp only
  let P : Measure (J → Ω) := Measure.pi (fun _ : J => ρ)
  let S : (J → Ω) → ℝ := fun Y => ∑ j : J, f (Y j)
  let E : (J → Ω) → ℝ := fun Y => ∑ j : J, f (Y j) ^ 2
  have hcoord (j : J) : MeasurePreserving (fun Y : J → Ω => Y j) P ρ :=
    measurePreserving_eval (μ := fun _ : J => ρ) j
  have hfj (j : J) : MemLp (fun Y : J → Ω => f (Y j)) 2 P :=
    hf2.comp_measurePreserving (hcoord j)
  have hS : MemLp S 2 P := memLp_finsetSum _ (fun j hj => hfj j)
  have hE : Integrable E P :=
    integrable_finsetSum _ (fun j hj => (hfj j).integrable_sq)
  have hpull (j : J) (q : Ω → ℝ) (hq : Measurable q) :
      (∫ Y, q (Y j) ∂P) = ∫ z, q z ∂ρ := by
    calc
      _ = ∫ z, q z ∂P.map (fun Y : J → Ω => Y j) :=
        (integral_map (hcoord j).measurable.aemeasurable hq.aestronglyMeasurable).symm
      _ = _ := by rw [(hcoord j).map_eq]
  have hprodI (j k : J) :
      Integrable (fun Y : J → Ω => f (Y j) * f (Y k)) P := by
    simpa only [Pi.mul_def] using (hfj j).integrable_mul (hfj k)
  have hprod (j k : J) :
      (∫ Y : J → Ω, f (Y j) * f (Y k) ∂P) =
        if j = k then (∫ y, f y ^ 2 ∂ρ) else (∫ y, f y ∂ρ) ^ 2 := by
    by_cases hjk : j = k
    · subst k
      rw [if_pos rfl]
      simpa only [pow_two] using
        hpull j (fun y : Ω => f y ^ (2 : ℕ)) (hf.pow_const (2 : ℕ))
    · rw [if_neg hjk]
      have hind : iIndepFun (fun l (Y : J → Ω) => Y l) P :=
        iIndepFun_pi (μ := fun _ : J => ρ)
          (X := fun _ (o : Ω) => o) (fun _ => measurable_id.aemeasurable)
      have hpair : MeasurePreserving (fun Y : J → Ω => (Y j, Y k))
          P (ρ.prod ρ) := by
        refine ⟨(measurable_pi_apply j).prodMk (measurable_pi_apply k), ?_⟩
        simpa only [(hcoord j).map_eq, (hcoord k).map_eq] using
          (hind.indepFun hjk).map_prod_eq_prod_map_map
            (measurable_pi_apply j).aemeasurable (measurable_pi_apply k).aemeasurable
      calc
        _ = ∫ z : Ω × Ω, f z.1 * f z.2
            ∂P.map (fun Y : J → Ω => (Y j, Y k)) :=
          (integral_map hpair.measurable.aemeasurable
            ((hf.comp measurable_fst).mul (hf.comp measurable_snd)).aestronglyMeasurable).symm
        _ = ∫ z : Ω × Ω, f z.1 * f z.2 ∂(ρ.prod ρ) := by rw [hpair.map_eq]
        _ = _ := by rw [integral_prod_mul]; ring
  have hinner (j : J) :
      (∑ k : J, if j = k then (∫ y, f y ^ 2 ∂ρ) else (∫ y, f y ∂ρ) ^ 2) =
        (∫ y, f y ^ 2 ∂ρ) +
          ((Fintype.card J : ℝ) - 1) * (∫ y, f y ∂ρ) ^ 2 := by
    have hcard : ((Finset.univ.erase j).card : ℝ) = (Fintype.card J : ℝ) - 1 := by
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ] using
        (Finset.sum_erase_eq_sub (s := Finset.univ)
          (f := fun _ : J => (1 : ℝ)) (Finset.mem_univ j))
    have hsplit :
        (∑ k : J, if j = k then (∫ y, f y ^ 2 ∂ρ) else (∫ y, f y ∂ρ) ^ 2) =
          (∫ y, f y ^ 2 ∂ρ) +
          ∑ k ∈ Finset.univ.erase j,
            if j = k then (∫ y, f y ^ 2 ∂ρ) else (∫ y, f y ∂ρ) ^ 2 := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)]
      simp
    rw [hsplit]
    congr 1
    calc
      _ = ∑ k ∈ Finset.univ.erase j, (∫ y, f y ∂ρ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro k hk
        exact if_neg (Finset.mem_erase.mp hk).1.symm
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; rw [hcard]
  refine ⟨hS, hS.integrable_sq, hE, ?_, ?_⟩
  · calc
      (∫ Y, S Y ^ 2 ∂P) =
          ∫ Y : J → Ω, ∑ j : J, ∑ k : J, f (Y j) * f (Y k) ∂P := by
        congr 1
        funext Y
        simp only [S, pow_two, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = ∑ j : J, ∑ k : J, ∫ Y : J → Ω, f (Y j) * f (Y k) ∂P := by
        calc
          _ = ∑ j : J, ∫ Y : J → Ω, (∑ k : J, f (Y j) * f (Y k)) ∂P :=
            integral_finsetSum Finset.univ (fun j hj =>
              integrable_finsetSum Finset.univ (fun k hk => hprodI j k))
          _ = _ := by
            apply Finset.sum_congr rfl
            intro j hj
            exact integral_finsetSum Finset.univ (fun k hk => hprodI j k)
      _ = ∑ j : J, ((∫ y, f y ^ 2 ∂ρ) +
          ((Fintype.card J : ℝ) - 1) * (∫ y, f y ∂ρ) ^ 2) := by
        simp_rw [hprod]
        apply Finset.sum_congr rfl
        intro j hj
        exact hinner j
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; ring
  · calc
      (∫ Y, E Y ∂P) = ∑ j : J, ∫ Y : J → Ω, f (Y j) ^ 2 ∂P :=
        integral_finsetSum _ (fun j hj => (hfj j).integrable_sq)
      _ = ∑ j : J, ∫ y, f y ^ 2 ∂ρ := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hpull j (fun y : Ω => f y ^ (2 : ℕ)) (hf.pow_const (2 : ℕ))
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

private theorem wd_conditional_row_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun z : Ω × Ω => r z.1 z.2))
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ))
    (hrcan : ∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0)
    (s : ℝ) (hs : 0 ≤ s)
    (hrsecond :
      (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)) ≤ s ^ 2)
    (L : Ω → ℝ) (hL : Measurable L) (K : ℝ)
    (hLnonneg : ∀ o, 0 ≤ L o) (hLle : ∀ o, L o ≤ K)
    (hLmass : (∫ o, L o ∂μ) = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hδsecond : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ ε ^ 2)
    (n : ℕ) (i : Fin n) :
    let J := {j : Fin n // j ≠ i}
    let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
    let P : Measure (J → Ω) := Measure.pi (fun _ : J => ρ)
    let R : Ω → ℝ := fun o => ∫ y, r o y ^ 2 ∂μ
    let S : Ω → (J → Ω) → ℝ := fun o Y => ∑ j : J, r o (Y j)
    let E : Ω → (J → Ω) → ℝ := fun o Y => ∑ j : J, r o (Y j) ^ 2
    IsProbabilityMeasure ρ ∧ IsProbabilityMeasure P ∧
      Measurable R ∧ Integrable R μ ∧ (∀ o, 0 ≤ R o) ∧
      (∫ o, R o ∂μ) ≤ s ^ 2 ∧
      (∀ᵐ o ∂μ,
        MemLp (S o) 2 P ∧ Integrable (fun Y => S o Y ^ 2) P ∧
        Integrable (E o) P ∧
        (∫ Y, S o Y ^ 2 ∂P) ≤
          ((n - 1 : ℕ) : ℝ) *
            (K + ((n - 2 : ℕ) : ℝ) * ε ^ 2) * R o ∧
        (∫ Y, E o Y ∂P) ≤ ((n - 1 : ℕ) : ℝ) * K * R o) := by
  classical
  dsimp only
  let J := {j : Fin n // j ≠ i}
  let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
  let P : Measure (J → Ω) := Measure.pi (fun _ : J => ρ)
  let R : Ω → ℝ := fun o => ∫ y, r o y ^ 2 ∂μ
  have hLi : Integrable L μ := Integrable.of_bound hL.aestronglyMeasurable K
    (Filter.Eventually.of_forall fun o => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hLnonneg o)] using hLle o)
  have hρ : IsProbabilityMeasure ρ := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hLi
        (Filter.Eventually.of_forall hLnonneg), hLmass]
    exact ENNReal.ofReal_one
  letI : IsProbabilityMeasure ρ := hρ
  have hsection := Shao.OQ6.CanonicalTilt.section_contraction
    μ r hr hr2 hrcan s hs hrsecond L hL K hLnonneg hLle hLmass ε hε hδsecond
  rcases hsection with ⟨hRm, hRi, hRid, hRle, hfm, hfμ, hfρ, hfμi, hfρi, hfbound, hrows⟩
  have hcard : (Fintype.card J : ℝ) = ((n - 1 : ℕ) : ℝ) := by
    letI : Fintype {j : Fin n // j = i} :=
      Subtype.fintype (fun j : Fin n => j = i)
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun j : Fin n => j = i) (fun _ : Fin n => (1 : ℝ))
    have hone : (∑ j : {j : Fin n // j = i}, (1 : ℝ)) = 1 := by
      letI : Unique {j : Fin n // j = i} :=
        { default := ⟨i, rfl⟩
          uniq := fun j => Subtype.ext j.property }
      simp
    rw [hone] at hsplit
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, Fintype.card_fin] at hsplit
    have hn1 : 1 ≤ n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    rw [Nat.cast_sub hn1]
    norm_num
    linarith
  refine ⟨hρ, inferInstance, hRm, hRi, ?_, hRle, ?_⟩
  · intro o
    exact integral_nonneg fun y => sq_nonneg (r o y)
  · filter_upwards [hrows] with o ho
    rcases ho with ⟨hrowμ, hrowρ, hrowμi, hrowρi, hrowsqμ, hrowsqρ,
      hrowLi, hrowδi, hrowmean, hrowcancel, hrowf, hrowq⟩
    have hrowm : Measurable (r o) :=
      hr.comp (measurable_const.prodMk measurable_id)
    have hprod := wd_product_row_second (J := J) ρ (r o) hrowm hrowρ
    rcases hprod with ⟨hS, hSi, hEi, hSid, hEid⟩
    have hfmean : (∫ y, r o y ∂ρ) ^ 2 ≤ ε ^ 2 * R o := by
      rw [hrowmean]
      simpa only [sq_abs] using hrowf
    refine ⟨hS, hSi, hEi, ?_, ?_⟩
    · rw [hSid, hcard]
      by_cases hn : n = 1
      · simp [hn]
      · have hn1 : 1 ≤ n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
        have hn2 : 2 ≤ n := Nat.succ_le_of_lt (lt_of_le_of_ne hn1 (Ne.symm hn))
        have hN1 : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
          exact_mod_cast (Nat.le_sub_of_add_le hn2)
        have hNsub : ((n - 1 : ℕ) : ℝ) - 1 = ((n - 2 : ℕ) : ℝ) := by
          rw [Nat.cast_sub hn1, Nat.cast_sub hn2]
          norm_num
          ring
        calc
          _ ≤ ((n - 1 : ℕ) : ℝ) * (K * R o) +
              ((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ) - 1) * (ε ^ 2 * R o) :=
            add_le_add
              (mul_le_mul_of_nonneg_left hrowq (Nat.cast_nonneg _))
              (mul_le_mul_of_nonneg_left hfmean
                (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hN1)))
          _ = _ := by rw [hNsub]; ring
    · rw [hEid, hcard]
      exact (mul_le_mul_of_nonneg_left hrowq (Nat.cast_nonneg _)).trans_eq (by ring)

private theorem wd_deleted_row_moment
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
    (hLnonneg : ∀ o, 0 ≤ L o) (hLle : ∀ o, L o ≤ K)
    (hLmass : (∫ o, L o ∂μ) = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hδsecond : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ ε ^ 2)
    (n : ℕ) (i : Fin n)
    (e : Fin (n - 1) ≃ {j : Fin n // j ≠ i}) :
    let J := {j : Fin n // j ≠ i}
    let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
    let P : Measure (J → Ω) := Measure.pi (fun _ : J => ρ)
    let T : (J → Ω) → J → ℝ := fun Y j =>
      ∑ k ∈ Finset.univ.erase j, r (Y j) (Y k)
    let M : (J → Ω) → ℝ := fun Y => ∑ j : J, T Y j ^ 2
    IsProbabilityMeasure ρ ∧ IsProbabilityMeasure P ∧
      (∀ j : J, MemLp (fun Y => T Y j) 2 P) ∧
      Integrable M P ∧
      (∫ Y, M Y ∂P) ≤
        (2 * ((n - 1).choose 2 : ℝ) * K ^ 2 +
          6 * ((n - 1).choose 3 : ℝ) * K * ε ^ 2) * s ^ 2 := by
  classical
  dsimp only
  let J := {j : Fin n // j ≠ i}
  let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
  let P : Measure (J → Ω) := Measure.pi (fun _ : J => ρ)
  let Pdel : Measure (Fin (n - 1) → Ω) :=
    Measure.pi (fun _ : Fin (n - 1) => ρ)
  let T : (J → Ω) → J → ℝ := fun Y j =>
    ∑ k ∈ Finset.univ.erase j, r (Y j) (Y k)
  let M : (J → Ω) → ℝ := fun Y => ∑ j : J, T Y j ^ 2
  let reindex : (J → Ω) → Fin (n - 1) → Ω := fun Y k => Y (e k)
  let ψ : (Fin (n - 1) → Ω) → Fin (n - 1) → ℝ := fun ξ k =>
    Shao.OQ6.ResidualDeletion.rowSum (fun u v => r (ξ u) (ξ v)) k
  let Λsq : (Fin (n - 1) → Ω) → ℝ := fun ξ => ∑ k : Fin (n - 1), ψ ξ k ^ 2
  have hgeneric := Shao.OQ6.FiniteTiltedMoments.row_square_sum_moment
    μ r hr hr2 hrsymm hrcan s hs hrsecond
    L hL K hLnonneg hLle hLmass ε hε hδsecond (n - 1)
  rcases hgeneric with ⟨hρ, hPdel, hψ, hΛ, hΛid, hΛbound⟩
  letI : IsProbabilityMeasure ρ := hρ
  have hre := wd_deleted_row_reindex ρ r n i e
  rcases hre with ⟨hpres, hsum, herase⟩
  change MeasurePreserving reindex P Pdel at hpres
  have hT (Y : J → Ω) (j : J) : T Y j = ψ (reindex Y) (e.symm j) := by
    unfold T ψ Shao.OQ6.ResidualDeletion.rowSum
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j),
      Finset.sum_erase_eq_sub (Finset.mem_univ (e.symm j))]
    rw [← e.sum_comp (fun k : J => r (Y j) (Y k))]
    simp [reindex]
  have hMi : Integrable M P :=
    (hpres.integrable_comp_of_integrable hΛ).congr
      (Filter.Eventually.of_forall fun Y => (hsum Y).symm)
  refine ⟨hρ, inferInstance, ?_, hMi, ?_⟩
  · intro j
    exact (memLp_congr_ae (Filter.Eventually.of_forall fun Y => hT Y j)).mpr
      ((hψ (e.symm j)).comp_measurePreserving hpres)
  · have hmap : Integrable Λsq (P.map reindex) := by
      rw [hpres.map_eq]
      exact hΛ
    calc
      (∫ Y, M Y ∂P) = ∫ Y, Λsq (reindex Y) ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall hsum)
      _ = ∫ ξ, Λsq ξ ∂Pdel := by
        rw [← hpres.map_eq]
        exact (integral_map hpres.measurable.aemeasurable hmap.aestronglyMeasurable).symm
      _ ≤ _ := hΛbound

private theorem wd_vector_integral_cauchy
    {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (U V : Ω → J → ℝ)
    (hU : ∀ j : J, MemLp (fun o => U o j) 2 ν)
    (hV : ∀ j : J, MemLp (fun o => V o j) 2 ν) :
    let A : Ω → ℝ := fun o => ∑ j : J, U o j ^ 2
    let B : Ω → ℝ := fun o => ∑ j : J, V o j ^ 2
    let dot : Ω → ℝ := fun o => ∑ j : J, U o j * V o j
    Integrable dot ν ∧
      (∫ o, |dot o| ∂ν) ≤
        Real.sqrt (∫ o, A o ∂ν) * Real.sqrt (∫ o, B o ∂ν) := by
  classical
  dsimp only
  let A : Ω → ℝ := fun o => ∑ j : J, U o j ^ 2
  let B : Ω → ℝ := fun o => ∑ j : J, V o j ^ 2
  let dot : Ω → ℝ := fun o => ∑ j : J, U o j * V o j
  have hprod (j : J) : Integrable (fun o => U o j * V o j) ν :=
    (hU j).integrable_mul (hV j)
  have hdot : Integrable dot ν := integrable_finsetSum _ (fun j hj => hprod j)
  have hsumabs : Integrable (fun o => ∑ j : J, |U o j * V o j|) ν :=
    integrable_finsetSum _ (fun j hj => (hprod j).abs)
  have hpoint (o : Ω) : |dot o| ≤ ∑ j : J, |U o j * V o j| :=
    Finset.abs_sum_le_sum_abs _ _
  have hcs (j : J) :
      (∫ o, |U o j * V o j| ∂ν) ≤
        Real.sqrt (∫ o, U o j ^ 2 ∂ν) * Real.sqrt (∫ o, V o j ^ 2 ∂ν) := by
    have hh := integral_mul_norm_le_Lp_mul_Lq
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
        (2 : ℝ).HolderConjugate 2)
      (by simpa using hU j) (by simpa using hV j)
    simpa only [norm_mul, Real.norm_eq_abs, Real.rpow_two,
      ← Real.sqrt_eq_rpow, sq_abs, abs_mul] using hh
  refine ⟨hdot, ?_⟩
  calc
    (∫ o, |dot o| ∂ν) ≤ ∫ o, (∑ j : J, |U o j * V o j|) ∂ν :=
      integral_mono hdot.abs hsumabs hpoint
    _ = ∑ j : J, ∫ o, |U o j * V o j| ∂ν :=
      integral_finsetSum _ (fun j hj => (hprod j).abs)
    _ ≤ ∑ j : J,
        Real.sqrt (∫ o, U o j ^ 2 ∂ν) * Real.sqrt (∫ o, V o j ^ 2 ∂ν) :=
      Finset.sum_le_sum (fun j hj => hcs j)
    _ ≤ Real.sqrt (∑ j : J, (Real.sqrt (∫ o, U o j ^ 2 ∂ν)) ^ 2) *
        Real.sqrt (∑ j : J, (Real.sqrt (∫ o, V o j ^ 2 ∂ν)) ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt (∑ j : J, ∫ o, U o j ^ 2 ∂ν) *
        Real.sqrt (∑ j : J, ∫ o, V o j ^ 2 ∂ν) := by
      simp_rw [Real.sq_sqrt (integral_nonneg fun o => sq_nonneg (U o _)),
        Real.sq_sqrt (integral_nonneg fun o => sq_nonneg (V o _))]
    _ = _ := by
      rw [← integral_finsetSum _ (fun j hj => (hU j).integrable_sq),
        ← integral_finsetSum _ (fun j hj => (hV j).integrable_sq)]

private theorem wd_mixed_row_cross_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgsecond : (∫ o, g o ^ 2 ∂μ) = 1)
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun z : Ω × Ω => r z.1 z.2))
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ))
    (hrsymm : ∀ o y, r o y = r y o)
    (hrcan : ∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0)
    (s : ℝ) (hs : 0 ≤ s)
    (hrsecond :
      (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)) ≤ s ^ 2)
    (L : Ω → ℝ) (hL : Measurable L) (K : ℝ)
    (hLnonneg : ∀ o, 0 ≤ L o) (hLle : ∀ o, L o ≤ K)
    (hLmass : (∫ o, L o ∂μ) = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hδsecond : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ ε ^ 2)
    (a : ℝ) (ha : 0 ≤ a)
    (n : ℕ) (hn : 3 ≤ n) (i : Fin n) :
    let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
    let H : Measure (Fin n → Ω) := Measure.pi
      (fun j : Fin n => if j = i then μ else ρ)
    let cap : (Fin n → Ω) → ℝ := fun ξ => min |a * g (ξ i)| 1
    let E : (Fin n → Ω) → Fin n → Fin n → ℝ :=
      fun ξ j k => r (ξ j) (ξ k)
    let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
      Shao.OQ6.ResidualDeletion.rowSum (E ξ) j
    let ψdel : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
      Shao.OQ6.ResidualDeletion.rowSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (E ξ) i) j
    let Λsq : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, ψ ξ j ^ 2
    let Λdelsq : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, ψdel ξ j ^ 2
    let cross : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j ∈ Finset.univ.erase i,
        2 * r (ξ i) (ξ j) * (ψ ξ j - r (ξ i) (ξ j))
    let Bdel : ℝ :=
      (2 * ((n - 1).choose 2 : ℝ) * K ^ 2 +
        6 * ((n - 1).choose 3 : ℝ) * K * ε ^ 2) * s ^ 2
    IsProbabilityMeasure H ∧
      Integrable (fun ξ => cap ξ * |ψ ξ i|) H ∧
      (∫ ξ, cap ξ * |ψ ξ i| ∂H) ≤
        a * s * Real.sqrt
          (((n - 1 : ℕ) : ℝ) * (K + ((n - 2 : ℕ) : ℝ) * ε ^ 2)) ∧
      Integrable (fun ξ => cap ξ * |cross ξ|) H ∧
      (∫ ξ, cap ξ * |cross ξ| ∂H) ≤
        2 * a * s * Real.sqrt (((n - 1 : ℕ) : ℝ) * K * Bdel) ∧
      Integrable (fun ξ => cap ξ * |Λsq ξ - Λdelsq ξ|) H ∧
      (∫ ξ, cap ξ * |Λsq ξ - Λdelsq ξ| ∂H) ≤
        s ^ 2 * ((n - 1 : ℕ) : ℝ) *
          (2 * K + ((n - 2 : ℕ) : ℝ) * ε ^ 2) +
        2 * a * s * Real.sqrt (((n - 1 : ℕ) : ℝ) * K * Bdel) := by
  classical
  dsimp only
  let J := {j : Fin n // j ≠ i}
  let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
  let P : Measure (J → Ω) := Measure.pi (fun _ : J => ρ)
  let H : Measure (Fin n → Ω) := Measure.pi
    (fun j : Fin n => if j = i then μ else ρ)
  let ins : Ω × (J → Ω) → Fin n → Ω := fun z j =>
    if hji : j = i then z.1 else z.2 ⟨j, hji⟩
  let capO : Ω → ℝ := fun o => min |a * g o| 1
  let cap : (Fin n → Ω) → ℝ := fun ξ => capO (ξ i)
  let E : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ j k => r (ξ j) (ξ k)
  let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
    Shao.OQ6.ResidualDeletion.rowSum (E ξ) j
  let ψdel : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
    Shao.OQ6.ResidualDeletion.rowSum
      (Shao.OQ6.ResidualDeletion.eraseIncident (E ξ) i) j
  let Λsq : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, ψ ξ j ^ 2
  let Λdelsq : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, ψdel ξ j ^ 2
  let cross : (Fin n → Ω) → ℝ := fun ξ =>
    ∑ j ∈ Finset.univ.erase i,
      2 * r (ξ i) (ξ j) * (ψ ξ j - r (ξ i) (ξ j))
  let R : Ω → ℝ := fun o => ∫ y, r o y ^ 2 ∂μ
  let S : Ω × (J → Ω) → ℝ := fun z => ∑ j : J, r z.1 (z.2 j)
  let T : (J → Ω) → J → ℝ := fun Y j =>
    ∑ k ∈ Finset.univ.erase j, r (Y j) (Y k)
  let M : (J → Ω) → ℝ := fun Y => ∑ j : J, T Y j ^ 2
  let A : Ω × (J → Ω) → ℝ := fun z => ∑ j : J, r z.1 (z.2 j) ^ 2
  let dot : Ω × (J → Ω) → ℝ := fun z => ∑ j : J, r z.1 (z.2 j) * T z.2 j
  let Brow : ℝ := ((n - 1 : ℕ) : ℝ) * (K + ((n - 2 : ℕ) : ℝ) * ε ^ 2)
  let Bedge : ℝ := ((n - 1 : ℕ) : ℝ) * K
  let Bdel : ℝ :=
    (2 * ((n - 1).choose 2 : ℝ) * K ^ 2 +
      6 * ((n - 1).choose 3 : ℝ) * K * ε ^ 2) * s ^ 2
  let Bcross : ℝ := Real.sqrt Bedge * Real.sqrt Bdel
  have hrows := wd_conditional_row_moments
    μ r hr hr2 hrcan s hs hrsecond L hL K hLnonneg hLle hLmass ε hε hδsecond n i
  rcases hrows with ⟨hρ, hP, hRm, hRi, hR0, hRbound, hrows⟩
  letI : IsProbabilityMeasure ρ := hρ
  letI : IsProbabilityMeasure P := hP
  letI : ∀ j : Fin n, IsProbabilityMeasure (if j = i then μ else ρ) :=
    fun j => by split_ifs <;> infer_instance
  have hH : IsProbabilityMeasure H := inferInstance
  have hLi : Integrable L μ := Integrable.of_bound hL.aestronglyMeasurable K
    (Filter.Eventually.of_forall fun o => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hLnonneg o)] using hLle o)
  have hK : 1 ≤ K := by
    have hh := integral_mono hLi (integrable_const K) hLle
    simpa only [hLmass, integral_const, probReal_univ, one_smul] using hh
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hBrow0 : 0 ≤ Brow := by dsimp [Brow]; positivity
  have hBedge0 : 0 ≤ Bedge := by dsimp [Bedge]; positivity
  have hBdel0 : 0 ≤ Bdel := by dsimp [Bdel]; positivity
  have hBcross0 : 0 ≤ Bcross := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hcm : Measurable capO := by
    have hag : Measurable (fun o => a * g o) := measurable_const.mul hg
    simpa only [capO, Real.norm_eq_abs] using hag.norm.min measurable_const
  have hc0 (o : Ω) : 0 ≤ capO o := le_min (abs_nonneg _) (by norm_num)
  have hc1 (o : Ω) : capO o ≤ 1 := min_le_right _ _
  have hcapped := Shao.OQ6.CappedSectionEnergy.capped_sqrt_energy_bound
    μ g hg hg2 hgsecond R hRm hR0 hRi s hs hRbound a ha
  rcases hcapped with ⟨hcapRi, hcapRbound⟩
  have hsums (f : Fin n → ℝ) :
      (∑ j ∈ Finset.univ.erase i, f j) = ∑ j : J, f j := by
    letI : Fintype {j : Fin n // j = i} := Subtype.fintype (fun j : Fin n => j = i)
    have hsplit := Fintype.sum_subtype_add_sum_subtype (fun j : Fin n => j = i) f
    have hone : (∑ j : {j : Fin n // j = i}, f j) = f i := by
      letI : Unique {j : Fin n // j = i} :=
        { default := ⟨i, rfl⟩
          uniq := fun j => Subtype.ext j.property }
      simp only [Fintype.sum_unique]
      rw [(default : {j : Fin n // j = i}).property]
    change (∑ j : {j : Fin n // j = i}, f j) + (∑ j : J, f j) = ∑ j : Fin n, f j at hsplit
    rw [hone] at hsplit
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    linarith
  have hsumzero (f : Fin n → ℝ) (hfi : f i = 0) :
      (∑ j : Fin n, f j) = ∑ j : J, f j := by
    rw [← hsums, Finset.sum_erase_eq_sub (Finset.mem_univ i), hfi, sub_zero]
  let er : J ≃ ↥(Finset.univ.erase i) :=
    { toFun := fun j => ⟨j, by simpa using j.property⟩
      invFun := fun j => ⟨j, (Finset.mem_erase.mp j.property).1⟩
      left_inv := by intro j; rfl
      right_inv := by intro j; rfl }
  let e : Fin (n - 1) ≃ J :=
    (Finset.equivFinOfCardEq (by simp : (Finset.univ.erase i).card = n - 1)).symm.trans er.symm
  have hdeleted := wd_deleted_row_moment μ r hr hr2 hrsymm hrcan s hs hrsecond
    L hL K hLnonneg hLle hLmass ε hε hδsecond n i e
  rcases hdeleted with ⟨hρ', hP', hT2, hMi, hMbound⟩
  change Integrable M P at hMi
  change (∫ Y, M Y ∂P) ≤ Bdel at hMbound
  have hrj (j : J) : Measurable (fun z : Ω × (J → Ω) => r z.1 (z.2 j)) := by
    simpa only [Function.comp_def] using hr.comp
      (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have hSm : Measurable S := Finset.measurable_sum _ (fun j hj => hrj j)
  have hAm : Measurable A := Finset.measurable_sum _ (fun j hj => (hrj j).pow_const (2 : ℕ))
  have hTm (j : J) : Measurable (fun Y => T Y j) := by
    apply Finset.measurable_sum
    intro k hk
    have hsel : Measurable (fun Y : J → Ω => (Y j, Y k)) :=
      (measurable_pi_apply j).prodMk (measurable_pi_apply k)
    simpa only [Function.comp_def] using
      hr.comp hsel
  have hdm : Measurable dot := Finset.measurable_sum _
    (fun j hj => (hrj j).mul ((hTm j).comp measurable_snd))
  have hA0 (z : Ω × (J → Ω)) : 0 ≤ A z :=
    Finset.sum_nonneg (fun j hj => sq_nonneg _)
  have hsections := Shao.OQ6.CanonicalTilt.section_contraction
    μ r hr hr2 hrcan s hs hrsecond L hL K hLnonneg hLle hLmass ε hε hδsecond
  rcases hsections with ⟨_, _, _, _, _, _, _, _, _, _, hsections⟩
  have hgood : ∀ᵐ o ∂μ,
      Integrable (fun Y => S (o, Y)) P ∧
      Integrable (fun Y => S (o, Y) ^ 2) P ∧
      Integrable (fun Y => A (o, Y)) P ∧
      Integrable (fun Y => dot (o, Y)) P ∧
      (∫ Y, |S (o, Y)| ∂P) ≤ Real.sqrt Brow * Real.sqrt (R o) ∧
      (∫ Y, S (o, Y) ^ 2 ∂P) ≤ Brow * R o ∧
      (∫ Y, A (o, Y) ∂P) ≤ Bedge * R o ∧
      (∫ Y, |dot (o, Y)| ∂P) ≤ Bcross * Real.sqrt (R o) := by
    filter_upwards [hrows, hsections] with o ho hsec
    rcases ho with ⟨hS2, hSsq, hAi, hSbound, hAbound⟩
    have hU (j : J) : MemLp (fun Y : J → Ω => r o (Y j)) 2 P := by
      have hsingle : MemLp (r o) 2 ρ := hsec.2.1
      exact hsingle.comp_measurePreserving (measurePreserving_eval (μ := fun _ : J => ρ) j)
    have hv := wd_vector_integral_cauchy P
      (fun Y j => r o (Y j)) T hU hT2
    rcases hv with ⟨hdi, hdbound⟩
    have hSabs : (∫ Y, |S (o, Y)| ∂P) ≤ Real.sqrt Brow * Real.sqrt (R o) := by
      have hh := integral_mul_norm_le_Lp_mul_Lq
        (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ : (2 : ℝ).HolderConjugate 2)
        (by simpa using hS2) (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : J → Ω => (1 : ℝ)) 2 P))
      have hh' : (∫ Y, |S (o, Y)| ∂P) ≤ Real.sqrt (∫ Y, S (o, Y) ^ 2 ∂P) := by
        simpa only [norm_mul, Real.norm_eq_abs, Real.rpow_two, ← Real.sqrt_eq_rpow,
          sq_abs, norm_one, one_pow, integral_const, probReal_univ, one_smul,
          Real.sqrt_one, mul_one] using hh
      calc
        _ ≤ Real.sqrt (Brow * R o) := hh'.trans (Real.sqrt_le_sqrt hSbound)
        _ = _ := Real.sqrt_mul hBrow0 _
    have hdabs : (∫ Y, |dot (o, Y)| ∂P) ≤ Bcross * Real.sqrt (R o) := by
      calc
        _ ≤ Real.sqrt (∫ Y, A (o, Y) ∂P) * Real.sqrt (∫ Y, M Y ∂P) := hdbound
        _ ≤ Real.sqrt (Bedge * R o) * Real.sqrt Bdel :=
          mul_le_mul (Real.sqrt_le_sqrt hAbound) (Real.sqrt_le_sqrt hMbound)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = _ := by rw [Real.sqrt_mul hBedge0]; dsimp [Bcross]; ring
    exact ⟨hS2.integrable (by norm_num), hSsq, hAi, hdi, hSabs, hSbound, hAbound, hdabs⟩
  have hlift (F : Ω × (J → Ω) → ℝ) (hFm : Measurable F)
      (hFi : ∀ᵐ o ∂μ, Integrable (fun Y => F (o, Y)) P)
      (b : Ω → ℝ) (hbi : Integrable b μ)
      (hb : ∀ᵐ o ∂μ, (∫ Y, ‖F (o, Y)‖ ∂P) ≤ b o) :
      Integrable F (μ.prod P) := by
    apply (integrable_prod_iff hFm.aestronglyMeasurable).mpr
    refine ⟨hFi, hbi.mono' ?_ ?_⟩
    · exact hFm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    · filter_upwards [hb] with o ho
      have hn : 0 ≤ (∫ Y : J → Ω, ‖F (o, Y)‖ ∂P) :=
        integral_nonneg (fun Y : J → Ω => norm_nonneg (F (o, Y)))
      change |∫ Y : J → Ω, ‖F (o, Y)‖ ∂P| ≤ b o
      rw [abs_of_nonneg hn]
      exact ho
  have hcost (F : Ω × (J → Ω) → ℝ) (hFm : Measurable F)
      (hFi : ∀ᵐ o ∂μ, Integrable (fun Y => F (o, Y)) P)
      (t : ℝ) (ht : 0 ≤ t)
      (hFb : ∀ᵐ o ∂μ, (∫ Y, |F (o, Y)| ∂P) ≤ t * Real.sqrt (R o)) :
      Integrable (fun z => capO z.1 * |F z|) (μ.prod P) ∧
      (∫ z, capO z.1 * |F z| ∂(μ.prod P)) ≤ a * s * t := by
    have hZm : Measurable (fun z : Ω × (J → Ω) => capO z.1 * |F z|) :=
      by simpa only [Real.norm_eq_abs, Pi.mul_def, Function.comp_def] using
        (hcm.comp measurable_fst).mul hFm.norm
    have hZi := hlift (fun z => capO z.1 * |F z|) hZm
      (by filter_upwards [hFi] with o ho; exact ho.abs.const_mul (capO o))
      (fun o => t * (capO o * Real.sqrt (R o))) (hcapRi.const_mul t)
      (by
        filter_upwards [hFb] with o ho
        simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (hc0 o), integral_const_mul]
        calc
          _ ≤ capO o * (t * Real.sqrt (R o)) := mul_le_mul_of_nonneg_left ho (hc0 o)
          _ = _ := by ring)
    refine ⟨hZi, ?_⟩
    calc
      _ = ∫ o, (∫ Y, capO o * |F (o, Y)| ∂P) ∂μ := integral_prod _ hZi
      _ ≤ ∫ o, t * (capO o * Real.sqrt (R o)) ∂μ := by
        apply integral_mono_ae hZi.integral_prod_left (hcapRi.const_mul t)
        filter_upwards [hFb] with o ho
        rw [integral_const_mul]
        nlinarith [mul_le_mul_of_nonneg_left ho (hc0 o)]
      _ = t * (∫ o, capO o * Real.sqrt (R o) ∂μ) := integral_const_mul _ _
      _ ≤ t * (a * s) := mul_le_mul_of_nonneg_left hcapRbound ht
      _ = _ := by ring
  have henergy (F : Ω × (J → Ω) → ℝ) (hFm : Measurable F)
      (hF0 : ∀ z, 0 ≤ F z)
      (hFi : ∀ᵐ o ∂μ, Integrable (fun Y => F (o, Y)) P)
      (t : ℝ) (ht : 0 ≤ t)
      (hFb : ∀ᵐ o ∂μ, (∫ Y, F (o, Y) ∂P) ≤ t * R o) :
      Integrable F (μ.prod P) ∧ (∫ z, F z ∂(μ.prod P)) ≤ t * s ^ 2 := by
    have hFiProd := hlift F hFm hFi (fun o => t * R o) (hRi.const_mul t)
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 _)] using hFb)
    refine ⟨hFiProd, ?_⟩
    calc
      _ = ∫ o, (∫ Y, F (o, Y) ∂P) ∂μ := integral_prod _ hFiProd
      _ ≤ ∫ o, t * R o ∂μ := integral_mono_ae hFiProd.integral_prod_left (hRi.const_mul t) hFb
      _ = t * (∫ o, R o ∂μ) := integral_const_mul _ _
      _ ≤ t * s ^ 2 := mul_le_mul_of_nonneg_left hRbound ht
  have hScost := hcost S hSm
    (by filter_upwards [hgood] with o ho; exact ho.1)
    (Real.sqrt Brow) (Real.sqrt_nonneg _)
    (by filter_upwards [hgood] with o ho; exact ho.2.2.2.2.1)
  have hdcost := hcost dot hdm
    (by filter_upwards [hgood] with o ho; exact ho.2.2.2.1)
    Bcross hBcross0
    (by filter_upwards [hgood] with o ho; exact ho.2.2.2.2.2.2.2)
  have hSenergy := henergy (fun z => S z ^ 2) (hSm.pow_const (2 : ℕ)) (fun z => sq_nonneg _)
    (by filter_upwards [hgood] with o ho; exact ho.2.1)
    Brow hBrow0 (by filter_upwards [hgood] with o ho; exact ho.2.2.2.2.2.1)
  have hAenergy := henergy A hAm hA0
    (by filter_upwards [hgood] with o ho; exact ho.2.2.1)
    Bedge hBedge0 (by filter_upwards [hgood] with o ho; exact ho.2.2.2.2.2.2.1)
  have hinsert := wd_insert_fubini μ ρ n i
  rcases hinsert with ⟨hins, hfubini⟩
  change MeasurePreserving ins (μ.prod P) H at hins
  have hcapins (z : Ω × (J → Ω)) : cap (ins z) = capO z.1 := by simp [cap, ins]
  have hrowins (z : Ω × (J → Ω)) : ψ (ins z) i = S z := by
    change (∑ j ∈ Finset.univ.erase i, r (ins z i) (ins z j)) = _
    rw [hsums]
    apply Finset.sum_congr rfl
    intro j hj
    simp [ins, j.property, S]
  have herow (ξ : Fin n → Ω) (j : J) : ψdel ξ j = T (fun k => ξ k) j := by
    let f : Fin n → ℝ := Shao.OQ6.ResidualDeletion.eraseIncident (E ξ) i j
    have hfi : f i = 0 := by simp [f, Shao.OQ6.ResidualDeletion.eraseIncident]
    have hfk (k : J) : f k = r (ξ j) (ξ k) := by
      simp [f, Shao.OQ6.ResidualDeletion.eraseIncident, E, j.property, k.property]
    change (∑ k ∈ Finset.univ.erase j.val, f k) = _
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j.val), hsumzero f hfi]
    change (∑ k : J, f k) - f j.val = T (fun k => ξ k) j
    simp_rw [hfk]
    unfold T
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)]
  have hdelins (z : Ω × (J → Ω)) (j : J) : ψdel (ins z) j = T z.2 j := by
    rw [herow]
    congr 1
    funext k
    simp [ins, k.property]
  have hrowminus (z : Ω × (J → Ω)) (j : J) :
      ψ (ins z) j - r z.1 (z.2 j) = T z.2 j := by
    have hid := Shao.OQ6.ResidualDeletion.rowSum_eraseIncident (E (ins z)) i j
    change ψdel (ins z) j = if j.val = i then 0 else
      ψ (ins z) j - r (ins z j) (ins z i) at hid
    rw [if_neg j.property] at hid
    rw [show ins z j = z.2 j by simp [ins, j.property],
      show ins z i = z.1 by simp [ins]] at hid
    rw [hrsymm (z.2 j) z.1] at hid
    rw [hdelins] at hid
    exact hid.symm
  have hcrossins (z : Ω × (J → Ω)) : cross (ins z) = 2 * dot z := by
    change (∑ j ∈ Finset.univ.erase i,
      2 * r (ins z i) (ins z j) * (ψ (ins z) j - r (ins z i) (ins z j))) = _
    rw [hsums]
    change _ = 2 * (∑ j : J, r z.1 (z.2 j) * T z.2 j)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show ins z i = z.1 by simp [ins],
      show ins z j = z.2 j by simp [ins, j.property]]
    rw [hrowminus]
    ring
  have hsquareins (z : Ω × (J → Ω)) :
      (∑ j ∈ Finset.univ.erase i, r (ins z i) (ins z j) ^ 2) = A z := by
    rw [hsums]
    apply Finset.sum_congr rfl
    intro j hj
    simp [ins, j.property, A]
  have hsigned (ξ : Fin n → Ω) :
      Λsq ξ - Λdelsq ξ = ψ ξ i ^ 2 + cross ξ +
        ∑ j ∈ Finset.univ.erase i, r (ξ i) (ξ j) ^ 2 := by
    have h := Shao.OQ6.ResidualDeletion.rowSqSum_sub_eraseIncident
      (E ξ) (fun j k => hrsymm (ξ j) (ξ k)) i
    simpa only [Λsq, Λdelsq, ψ, ψdel, cross, E, Finset.sum_add_distrib, add_assoc] using h
  have hLpoint (z : Ω × (J → Ω)) :
      cap (ins z) * |Λsq (ins z) - Λdelsq (ins z)| ≤
        S z ^ 2 + 2 * (capO z.1 * |dot z|) + A z := by
    rw [hcapins, hsigned, hrowins, hcrossins, hsquareins]
    have habs : |S z ^ 2 + 2 * dot z + A z| ≤ S z ^ 2 + 2 * |dot z| + A z := by
      calc
        _ ≤ |S z ^ 2 + 2 * dot z| + |A z| := abs_add_le _ _
        _ ≤ (|S z ^ 2| + |2 * dot z|) + |A z| := add_le_add (abs_add_le _ _) le_rfl
        _ = _ := by rw [abs_of_nonneg (sq_nonneg _), abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg (hA0 z)]
    have hb := mul_le_mul_of_nonneg_left habs (hc0 z.1)
    have hcS := mul_le_mul_of_nonneg_right (hc1 z.1) (sq_nonneg (S z))
    have hcA := mul_le_mul_of_nonneg_right (hc1 z.1) (hA0 z)
    nlinarith [hcS, hcA]
  have hEdgeM (j k : Fin n) : Measurable (fun ξ : Fin n → Ω => r (ξ j) (ξ k)) := by
    have hsel : Measurable (fun ξ : Fin n → Ω => (ξ j, ξ k)) :=
      (measurable_pi_apply j).prodMk (measurable_pi_apply k)
    simpa only [Function.comp_def] using
      hr.comp hsel
  have hψm (j : Fin n) : Measurable (fun ξ => ψ ξ j) :=
    Finset.measurable_sum _ (fun k hk => hEdgeM j k)
  have hψdm (j : Fin n) : Measurable (fun ξ => ψdel ξ j) := by
    by_cases hji : j = i
    · simp only [ψdel, Shao.OQ6.ResidualDeletion.rowSum_eraseIncident, if_pos hji]
      exact measurable_const
    · simpa only [ψdel, Shao.OQ6.ResidualDeletion.rowSum_eraseIncident, if_neg hji,
        ψ, E, Pi.sub_def] using (hψm j).sub (hEdgeM j i)
  have hΛm : Measurable Λsq := Finset.measurable_sum _ (fun j hj => (hψm j).pow_const (2 : ℕ))
  have hΛdm : Measurable Λdelsq := Finset.measurable_sum _ (fun j hj => (hψdm j).pow_const (2 : ℕ))
  have hcrossm : Measurable cross := Finset.measurable_sum _
    (fun j hj => ((hEdgeM i j).const_mul 2).mul ((hψm j).sub (hEdgeM i j)))
  have hcapm : Measurable cap := hcm.comp (measurable_pi_apply i)
  have htransport (f : (Fin n → Ω) → ℝ) (hfm : Measurable f)
      (hfi : Integrable (fun z => f (ins z)) (μ.prod P)) :
      Integrable f H ∧ (∫ ξ, f ξ ∂H) = ∫ z, f (ins z) ∂(μ.prod P) := by
    have hfH := (hins.integrable_comp hfm.aestronglyMeasurable).mp hfi
    refine ⟨hfH, ?_⟩
    calc
      _ = ∫ ξ, f ξ ∂(μ.prod P).map ins := by rw [hins.map_eq]
      _ = _ := integral_map hins.measurable.aemeasurable hfm.aestronglyMeasurable
  have hrowcomp : (fun z => cap (ins z) * |ψ (ins z) i|) =
      fun z => capO z.1 * |S z| := by funext z; rw [hcapins, hrowins]
  have hrowH := htransport (fun ξ => cap ξ * |ψ ξ i|)
    (by simpa only [Real.norm_eq_abs, Pi.mul_def] using hcapm.mul (hψm i).norm)
    (by rw [hrowcomp]; exact hScost.1)
  have hcrosscomp : (fun z => cap (ins z) * |cross (ins z)|) =
      fun z => 2 * (capO z.1 * |dot z|) := by
    funext z
    rw [hcapins, hcrossins, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hcrossH := htransport (fun ξ => cap ξ * |cross ξ|)
    (by simpa only [Real.norm_eq_abs, Pi.mul_def] using hcapm.mul hcrossm.norm)
    (by rw [hcrosscomp]; exact hdcost.1.const_mul 2)
  have hmajor : Integrable (fun z => S z ^ 2 + 2 * (capO z.1 * |dot z|) + A z) (μ.prod P) :=
    (hSenergy.1.add (hdcost.1.const_mul 2)).add hAenergy.1
  have hLcomp : Integrable
      (fun z => cap (ins z) * |Λsq (ins z) - Λdelsq (ins z)|) (μ.prod P) := by
    have hm : Measurable (fun ξ => cap ξ * |Λsq ξ - Λdelsq ξ|) := by
      simpa only [Real.norm_eq_abs, Pi.mul_def, Pi.sub_def] using
        hcapm.mul (hΛm.sub hΛdm).norm
    apply hmajor.mono' (hm.comp hins.measurable).aestronglyMeasurable
    refine Filter.Eventually.of_forall fun z => ?_
    change ‖cap (ins z) * |Λsq (ins z) - Λdelsq (ins z)|‖ ≤
      S z ^ 2 + 2 * (capO z.1 * |dot z|) + A z
    simpa only [Real.norm_eq_abs, abs_mul, abs_abs, hcapins, abs_of_nonneg (hc0 z.1)] using hLpoint z
  have hLH := htransport (fun ξ => cap ξ * |Λsq ξ - Λdelsq ξ|)
    (by simpa only [Real.norm_eq_abs, Pi.mul_def, Pi.sub_def] using
      hcapm.mul (hΛm.sub hΛdm).norm) hLcomp
  have hBcross : Bcross = Real.sqrt (((n - 1 : ℕ) : ℝ) * K * Bdel) := by
    dsimp only [Bcross, Bedge]
    exact (Real.sqrt_mul hBedge0 _).symm
  refine ⟨hH, hrowH.1, ?_, hcrossH.1, ?_, hLH.1, ?_⟩
  · rw [hrowH.2, hrowcomp]
    exact hScost.2
  · rw [hcrossH.2, hcrosscomp, integral_const_mul]
    calc
      _ ≤ 2 * (a * s * Bcross) := mul_le_mul_of_nonneg_left hdcost.2 (by norm_num)
      _ = _ := by rw [hBcross]; ring
  · rw [hLH.2]
    calc
      _ ≤ ∫ z, (S z ^ 2 + 2 * (capO z.1 * |dot z|) + A z) ∂(μ.prod P) :=
        integral_mono hLcomp hmajor hLpoint
      _ = (∫ z, S z ^ 2 ∂(μ.prod P)) +
          2 * (∫ z, capO z.1 * |dot z| ∂(μ.prod P)) + ∫ z, A z ∂(μ.prod P) := by
        rw [integral_add
          (f := fun z => S z ^ 2 + 2 * (capO z.1 * |dot z|)) (g := A)
          (hSenergy.1.add (hdcost.1.const_mul 2)) hAenergy.1,
          integral_add (f := fun z => S z ^ 2)
          (g := fun z => 2 * (capO z.1 * |dot z|)) hSenergy.1 (hdcost.1.const_mul 2),
          integral_const_mul]
      _ ≤ Brow * s ^ 2 + 2 * (a * s * Bcross) + Bedge * s ^ 2 :=
        add_le_add (add_le_add hSenergy.2
          (mul_le_mul_of_nonneg_left hdcost.2 (by norm_num))) hAenergy.2
      _ = _ := by rw [hBcross]; dsimp only [Brow, Bedge]; ring


private theorem wd_scalar_deletion_bounds
    (C s : ℝ) (hC : 1 ≤ C) (hs : 0 ≤ s)
    (n : ℕ) (hn : 3 ≤ n) (x : ℝ) (hx : 0 ≤ x) :
    let a : ℝ := x / Real.sqrt (n : ℝ)
    let K : ℝ := 2 * C
    let ε : ℝ := 2 * C * a
    let Bdel : ℝ :=
      (2 * ((n - 1).choose 2 : ℝ) * K ^ 2 +
        6 * ((n - 1).choose 3 : ℝ) * K * ε ^ 2) * s ^ 2
    (n : ℝ) * 2 *
        (a * s * Real.sqrt
          (((n - 1 : ℕ) : ℝ) * (K + ((n - 2 : ℕ) : ℝ) * ε ^ 2)) /
          (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))) ≤
      4 * Real.sqrt 2 * C * s * (1 + x) ^ 2 / Real.sqrt (n : ℝ) ∧
    (n : ℝ) * 2 *
        (2 * a * s * Real.sqrt (((n - 1 : ℕ) : ℝ) * K * Bdel)) ≤
      16 * C ^ 2 * s ^ 2 * (n : ℝ) ^ 2 * x * (1 + x) ∧
    (n : ℝ) * 2 *
        (s ^ 2 * ((n - 1 : ℕ) : ℝ) *
          (2 * K + ((n - 2 : ℕ) : ℝ) * ε ^ 2) +
          2 * a * s * Real.sqrt (((n - 1 : ℕ) : ℝ) * K * Bdel)) ≤
      24 * C ^ 2 * s ^ 2 * (n : ℝ) ^ 2 * (1 + x) ^ 2 := by
  let N : ℝ := (n : ℝ)
  let m : ℝ := ((n - 1 : ℕ) : ℝ)
  let p : ℝ := ((n - 2 : ℕ) : ℝ)
  let a : ℝ := x / Real.sqrt N
  let K : ℝ := 2 * C
  let ε : ℝ := 2 * C * a
  let Bdel : ℝ :=
    (2 * ((n - 1).choose 2 : ℝ) * K ^ 2 +
      6 * ((n - 1).choose 3 : ℝ) * K * ε ^ 2) * s ^ 2
  change
    N * 2 * (a * s * Real.sqrt (m * (K + p * ε ^ 2)) /
        (Real.sqrt N * (N - 1))) ≤
      4 * Real.sqrt 2 * C * s * (1 + x) ^ 2 / Real.sqrt N ∧
    N * 2 * (2 * a * s * Real.sqrt (m * K * Bdel)) ≤
      16 * C ^ 2 * s ^ 2 * N ^ 2 * x * (1 + x) ∧
    N * 2 * (s ^ 2 * m * (2 * K + p * ε ^ 2) +
        2 * a * s * Real.sqrt (m * K * Bdel)) ≤
      24 * C ^ 2 * s ^ 2 * N ^ 2 * (1 + x) ^ 2
  have hN : 3 ≤ N := by dsimp only [N]; exact_mod_cast hn
  have hN0 : 0 ≤ N := by linarith only [hN]
  have hNpos : 0 < N := by linarith only [hN]
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 3) hn
  have hn2 : 2 ≤ n := le_trans (by decide : 2 ≤ 3) hn
  have hm : m = N - 1 := by
    dsimp only [m, N]
    rw [Nat.cast_sub hn1]
    norm_num
  have hp : p = N - 2 := by
    dsimp only [p, N]
    rw [Nat.cast_sub hn2]
    norm_num
  have hm0 : 0 ≤ m := by linarith only [hm, hN]
  have hmpos : 0 < m := by linarith only [hm, hN]
  have hmN : m ≤ N := by linarith only [hm]
  have hpN : p ≤ N := by linarith only [hp]
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hC2 : C ≤ C ^ 2 := by
    have ht := mul_nonneg hC0 (sub_nonneg.mpr hC)
    nlinarith only [ht]
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  have ha0 : 0 ≤ a := by dsimp only [a]; positivity
  have hroot : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hrootSq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0
  have haN : a * Real.sqrt N = x := by
    dsimp only [a]
    exact div_mul_cancel₀ x hroot.ne'
  have haN2 : a ^ 2 * N = x ^ 2 := by
    have ht := congrArg (fun t : ℝ => t ^ 2) haN
    simpa only [mul_pow, hrootSq] using ht
  have hNa : N * a = x * Real.sqrt N := by
    calc
      N * a = (Real.sqrt N ^ 2) * a := by rw [hrootSq]
      _ = (a * Real.sqrt N) * Real.sqrt N := by ring
      _ = x * Real.sqrt N := by rw [haN]
  have hεN : N * ε ^ 2 = 4 * C ^ 2 * x ^ 2 := by
    calc
      N * ε ^ 2 = 4 * C ^ 2 * (a ^ 2 * N) := by dsimp only [ε]; ring
      _ = 4 * C ^ 2 * x ^ 2 := by rw [haN2]
  have hεsmall : p * ε ^ 2 ≤ 4 * C ^ 2 * x ^ 2 := by
    calc
      _ ≤ N * ε ^ 2 := mul_le_mul_of_nonneg_right hpN (sq_nonneg ε)
      _ = _ := hεN
  have hchoose2 : ∀ k : ℕ,
      (k : ℝ) * ((k : ℝ) - 1) = 2 * (k.choose 2 : ℝ) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        simp only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_succ,
          Nat.cast_add, Nat.cast_one] at ih ⊢
        nlinarith only [ih]
  have hchoose3 : ∀ k : ℕ,
      (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) =
        6 * (k.choose 3 : ℝ) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        have h2 := hchoose2 k
        simp only [Nat.choose_succ_succ, Nat.cast_succ,
          Nat.cast_add, Nat.cast_one] at ih h2 ⊢
        nlinarith only [ih, h2]
  have hpair : (N - 1) * (N - 2) ≤ N ^ 2 := by
    nlinarith only [hN]
  have hc2 : 2 * ((n - 1).choose 2 : ℝ) ≤ N ^ 2 := by
    rw [← hchoose2 (n - 1)]
    change m * (m - 1) ≤ N ^ 2
    rw [hm]
    nlinarith only [hpair]
  have hc3 : 6 * ((n - 1).choose 3 : ℝ) ≤ N ^ 3 := by
    rw [← hchoose3 (n - 1)]
    change m * (m - 1) * (m - 2) ≤ N ^ 3
    rw [hm]
    calc
      (N - 1) * (N - 1 - 1) * (N - 1 - 2) =
          (N - 1) * (N - 2) * (N - 3) := by ring
      _ ≤ N ^ 2 * (N - 3) :=
        mul_le_mul_of_nonneg_right hpair (by linarith only [hN])
      _ ≤ N ^ 2 * N :=
        mul_le_mul_of_nonneg_left (by linarith : N - 3 ≤ N) (sq_nonneg N)
      _ = N ^ 3 := by ring
  have hterm2 : 2 * ((n - 1).choose 2 : ℝ) * K ^ 2 ≤ N ^ 2 * K ^ 2 :=
    mul_le_mul_of_nonneg_right hc2 (sq_nonneg K)
  have hterm3 : 6 * ((n - 1).choose 3 : ℝ) * K * ε ^ 2 ≤
      N ^ 3 * K * ε ^ 2 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc3 hK0) (sq_nonneg ε)
  have hBdel : Bdel ≤ s ^ 2 * N ^ 2 * K * (K + 4 * C ^ 2 * x ^ 2) := by
    calc
      _ ≤ (N ^ 2 * K ^ 2 + N ^ 3 * K * ε ^ 2) * s ^ 2 :=
        mul_le_mul_of_nonneg_right (add_le_add hterm2 hterm3) (sq_nonneg s)
      _ = s ^ 2 * N ^ 2 * K * (K + N * ε ^ 2) := by ring
      _ = _ := by rw [hεN]
  have hKsmall : K ≤ 4 * C ^ 2 := by
    dsimp only [K]
    nlinarith only [hC0, hC2]
  have hTmax : K + 4 * C ^ 2 * x ^ 2 ≤ 4 * C ^ 2 * (1 + x) ^ 2 := by
    have ht := mul_nonneg (sq_nonneg C) hx
    nlinarith only [hKsmall, ht]
  have hT : K + p * ε ^ 2 ≤ (2 * C * (1 + x)) ^ 2 := by
    nlinarith only [hεsmall, hTmax]
  have hrootT : Real.sqrt (K + p * ε ^ 2) ≤ 2 * C * (1 + x) := by
    calc
      _ ≤ Real.sqrt ((2 * C * (1 + x)) ^ 2) := Real.sqrt_le_sqrt hT
      _ = _ := Real.sqrt_sq (by positivity)
  have hrootrow : Real.sqrt (m * (K + p * ε ^ 2)) ≤
      Real.sqrt m * (2 * C * (1 + x)) := by
    rw [Real.sqrt_mul hm0]
    exact mul_le_mul_of_nonneg_left hrootT (Real.sqrt_nonneg m)
  have hrootNm : Real.sqrt N * Real.sqrt m ≤ Real.sqrt 2 * (N - 1) := by
    have hrel : N ≤ 2 * m := by linarith only [hm, hN]
    have hrootrel : Real.sqrt N ≤ Real.sqrt 2 * Real.sqrt m := by
      calc
        _ ≤ Real.sqrt (2 * m) := Real.sqrt_le_sqrt hrel
        _ = _ := Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) m
    calc
      _ ≤ (Real.sqrt 2 * Real.sqrt m) * Real.sqrt m :=
        mul_le_mul_of_nonneg_right hrootrel (Real.sqrt_nonneg m)
      _ = Real.sqrt 2 * (Real.sqrt m ^ 2) := by ring
      _ = Real.sqrt 2 * (N - 1) := by rw [Real.sq_sqrt hm0, hm]
  have hrowratio : Real.sqrt N * Real.sqrt (m * (K + p * ε ^ 2)) ≤
      2 * Real.sqrt 2 * C * (1 + x) * (N - 1) := by
    calc
      _ ≤ Real.sqrt N * (Real.sqrt m * (2 * C * (1 + x))) :=
        mul_le_mul_of_nonneg_left hrootrow hroot.le
      _ = (2 * C * (1 + x)) * (Real.sqrt N * Real.sqrt m) := by ring
      _ ≤ (2 * C * (1 + x)) * (Real.sqrt 2 * (N - 1)) :=
        mul_le_mul_of_nonneg_left hrootNm (by positivity)
      _ = _ := by ring
  have hden : 0 < Real.sqrt N * (N - 1) :=
    mul_pos hroot (by linarith only [hN])
  have hfirstRaw :
      N * 2 * (a * s * Real.sqrt (m * (K + p * ε ^ 2)) /
        (Real.sqrt N * (N - 1))) ≤
      4 * Real.sqrt 2 * C * s * x * (1 + x) / Real.sqrt N := by
    calc
      _ = (2 * s * (N * a) * Real.sqrt (m * (K + p * ε ^ 2))) /
          (Real.sqrt N * (N - 1)) := by ring
      _ = (2 * s * x * (Real.sqrt N * Real.sqrt (m * (K + p * ε ^ 2)))) /
          (Real.sqrt N * (N - 1)) := by rw [hNa]; ring
      _ ≤ _ := by
        apply (div_le_div_iff₀ hden hroot).2
        have ht := mul_le_mul_of_nonneg_left hrowratio
          (show 0 ≤ 2 * s * x * Real.sqrt N by positivity)
        nlinarith only [ht]
  have hfirst :
      N * 2 * (a * s * Real.sqrt (m * (K + p * ε ^ 2)) /
        (Real.sqrt N * (N - 1))) ≤
      4 * Real.sqrt 2 * C * s * (1 + x) ^ 2 / Real.sqrt N := by
    refine hfirstRaw.trans ?_
    apply (div_le_div_iff_of_pos_right hroot).2
    have ht : x * (1 + x) ≤ (1 + x) ^ 2 := by nlinarith only [hx]
    have hu := mul_le_mul_of_nonneg_left ht
      (show 0 ≤ 4 * Real.sqrt 2 * C * s by positivity)
    nlinarith only [hu]
  have hBfinal : Bdel ≤ 4 * C ^ 2 * s ^ 2 * N ^ 2 * K * (1 + x) ^ 2 := by
    calc
      _ ≤ s ^ 2 * N ^ 2 * K * (K + 4 * C ^ 2 * x ^ 2) := hBdel
      _ ≤ s ^ 2 * N ^ 2 * K * (4 * C ^ 2 * (1 + x) ^ 2) :=
        mul_le_mul_of_nonneg_left hTmax (by positivity)
      _ = _ := by ring
  have hcrossinside : m * K * Bdel ≤
      (4 * C ^ 2 * s * N * Real.sqrt N * (1 + x)) ^ 2 := by
    calc
      _ ≤ m * K * (4 * C ^ 2 * s ^ 2 * N ^ 2 * K * (1 + x) ^ 2) :=
        mul_le_mul_of_nonneg_left hBfinal (mul_nonneg hm0 hK0)
      _ ≤ N * K * (4 * C ^ 2 * s ^ 2 * N ^ 2 * K * (1 + x) ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hmN hK0) (by positivity)
      _ = _ := by
        simp only [mul_pow, hrootSq]
        dsimp only [K]
        ring
  have hcrossroot : Real.sqrt (m * K * Bdel) ≤
      4 * C ^ 2 * s * N * Real.sqrt N * (1 + x) := by
    calc
      _ ≤ Real.sqrt ((4 * C ^ 2 * s * N * Real.sqrt N * (1 + x)) ^ 2) :=
        Real.sqrt_le_sqrt hcrossinside
      _ = _ := Real.sqrt_sq (by positivity)
  have hcross : 2 * a * s * Real.sqrt (m * K * Bdel) ≤
      8 * C ^ 2 * s ^ 2 * N * x * (1 + x) := by
    calc
      _ ≤ 2 * a * s * (4 * C ^ 2 * s * N * Real.sqrt N * (1 + x)) :=
        mul_le_mul_of_nonneg_left hcrossroot (by positivity)
      _ = 8 * C ^ 2 * s ^ 2 * N * (a * Real.sqrt N) * (1 + x) := by ring
      _ = _ := by rw [haN]
  have hsecond : N * 2 * (2 * a * s * Real.sqrt (m * K * Bdel)) ≤
      16 * C ^ 2 * s ^ 2 * N ^ 2 * x * (1 + x) := by
    have ht := mul_le_mul_of_nonneg_left hcross (show 0 ≤ N * 2 by positivity)
    nlinarith only [ht]
  have h2K : 2 * K ≤ 4 * C ^ 2 := by dsimp only [K]; nlinarith only [hC2]
  have hsquareinside : 2 * K + p * ε ^ 2 ≤ 4 * C ^ 2 * (1 + x ^ 2) := by
    nlinarith only [h2K, hεsmall]
  have hsquare : s ^ 2 * m * (2 * K + p * ε ^ 2) ≤
      4 * C ^ 2 * s ^ 2 * N * (1 + x ^ 2) := by
    calc
      _ ≤ s ^ 2 * m * (4 * C ^ 2 * (1 + x ^ 2)) :=
        mul_le_mul_of_nonneg_left hsquareinside (by positivity)
      _ ≤ s ^ 2 * N * (4 * C ^ 2 * (1 + x ^ 2)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmN (sq_nonneg s)) (by positivity)
      _ = _ := by ring
  have hpoly : 4 * (1 + x ^ 2) + 8 * x * (1 + x) ≤
      12 * (1 + x) ^ 2 := by nlinarith only [hx]
  have htotal : s ^ 2 * m * (2 * K + p * ε ^ 2) +
      2 * a * s * Real.sqrt (m * K * Bdel) ≤
      12 * C ^ 2 * s ^ 2 * N * (1 + x) ^ 2 := by
    have ht := mul_le_mul_of_nonneg_left hpoly
      (show 0 ≤ C ^ 2 * s ^ 2 * N by positivity)
    nlinarith only [hsquare, hcross, ht]
  refine ⟨hfirst, hsecond, ?_⟩
  have ht := mul_le_mul_of_nonneg_left htotal (show 0 ≤ N * 2 by positivity)
  nlinarith only [ht]

theorem actual_quadratic_weighted_deletion_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 3 ≤ n)
    (x : ℝ) (hx : 0 ≤ x)
    (hwindow : x ≤ Real.sqrt (n : ℝ) /
      (2 * Real.exp (1 / 2 : ℝ))) :
    let C : ℝ := Real.exp (1 / 2 : ℝ)
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
    let s : ℝ := 1 + Real.sqrt v
    let a : ℝ := x / Real.sqrt (n : ℝ)
    let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
    let w : Ω → ℝ := fun o => Real.exp (φ o)
    let m : ℝ := ∫ o, w o ∂μ
    let L : Ω → ℝ := fun o => w o / m
    let ρ : Measure Ω :=
      μ.withDensity (fun o => ENNReal.ofReal (L o))
    let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let I : ℝ := m ^ n
    let R : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Real.exp (∑ j ∈ Finset.univ.erase i, φ (ξ j)) / I
    let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      min |a * g (ξ i)| 1
    let e : (Fin n → Ω) → Fin n → Fin n → ℝ :=
      fun ξ j k => r (ξ j) (ξ k)
    let F : (Fin n → Ω) → ℝ := fun ξ =>
      Shao.OQ5.P35.unorderedPairSum (e ξ)
    let Fdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Shao.OQ5.P35.unorderedPairSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i)
    let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
      Shao.OQ6.ResidualDeletion.rowSum (e ξ) j
    let ψdel : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ i j =>
      Shao.OQ6.ResidualDeletion.rowSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i) j
    let Λsq : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j : Fin n, ψ ξ j ^ 2
    let Λdelsq : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      ∑ j : Fin n, ψdel ξ i j ^ 2
    let D₁ : (Fin n → Ω) → ℝ := fun ξ =>
      F ξ / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    let D₁del : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Fdel ξ i / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    let cross : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      ∑ j ∈ Finset.univ.erase i,
        2 * r (ξ i) (ξ j) * (ψ ξ j - r (ξ i) (ξ j))
    (∀ ξ i, Λsq ξ - Λdelsq ξ i = ψ ξ i ^ 2 + cross ξ i +
      ∑ j ∈ Finset.univ.erase i, r (ξ i) (ξ j) ^ 2) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i|) P₀) ∧
      (∑ i : Fin n,
        ∫ ξ, R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i| ∂P₀) ≤
          4 * Real.sqrt 2 * C * s * (1 + x) ^ 2 /
            Real.sqrt (n : ℝ) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => R ξ i * cap ξ i * |cross ξ i|) P₀) ∧
      (∑ i : Fin n,
        ∫ ξ, R ξ i * cap ξ i * |cross ξ i| ∂P₀) ≤
          16 * C ^ 2 * s ^ 2 * (n : ℝ) ^ 2 * x * (1 + x) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => R ξ i * cap ξ i * |Λsq ξ - Λdelsq ξ i|) P₀) ∧
      (∑ i : Fin n,
        ∫ ξ, R ξ i * cap ξ i * |Λsq ξ - Λdelsq ξ i| ∂P₀) ≤
          24 * C ^ 2 * s ^ 2 * (n : ℝ) ^ 2 * (1 + x) ^ 2 := by
  classical
  dsimp only
  let C : ℝ := Real.exp (1 / 2 : ℝ)
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
  let s : ℝ := 1 + Real.sqrt v
  let a : ℝ := x / Real.sqrt (n : ℝ)
  let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
  let w : Ω → ℝ := fun o => Real.exp (φ o)
  let m : ℝ := ∫ o, w o ∂μ
  let L : Ω → ℝ := fun o => w o / m
  let ρ : Measure Ω :=
    μ.withDensity (fun o => ENNReal.ofReal (L o))
  let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let I : ℝ := m ^ n
  let R : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Real.exp (∑ j ∈ Finset.univ.erase i, φ (ξ j)) / I
  let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    min |a * g (ξ i)| 1
  let e : (Fin n → Ω) → Fin n → Fin n → ℝ :=
    fun ξ j k => r (ξ j) (ξ k)
  let F : (Fin n → Ω) → ℝ := fun ξ =>
    Shao.OQ5.P35.unorderedPairSum (e ξ)
  let Fdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Shao.OQ5.P35.unorderedPairSum
      (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i)
  let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
    Shao.OQ6.ResidualDeletion.rowSum (e ξ) j
  let ψdel : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ i j =>
    Shao.OQ6.ResidualDeletion.rowSum
      (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i) j
  let Λsq : (Fin n → Ω) → ℝ := fun ξ =>
    ∑ j : Fin n, ψ ξ j ^ 2
  let Λdelsq : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    ∑ j : Fin n, ψdel ξ i j ^ 2
  let D₁ : (Fin n → Ω) → ℝ := fun ξ =>
    F ξ / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
  let D₁del : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Fdel ξ i / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
  let cross : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    ∑ j ∈ Finset.univ.erase i,
      2 * r (ξ i) (ξ j) * (ψ ξ j - r (ξ i) (ξ j))
  let K : ℝ := 2 * C
  let ε : ℝ := 2 * C * a
  let den : ℝ := Real.sqrt (n : ℝ) * ((n : ℝ) - 1)
  let H : Fin n → Measure (Fin n → Ω) := fun i => Measure.pi
    (fun j : Fin n => if j = i then μ else ρ)
  let rowBound : ℝ := a * s * Real.sqrt
    (((n - 1 : ℕ) : ℝ) * (K + ((n - 2 : ℕ) : ℝ) * ε ^ 2))
  let Bdel : ℝ :=
    (2 * ((n - 1).choose 2 : ℝ) * K ^ 2 +
      6 * ((n - 1).choose 3 : ℝ) * K * ε ^ 2) * s ^ 2
  let crossBound : ℝ := 2 * a * s * Real.sqrt (((n - 1 : ℕ) : ℝ) * K * Bdel)
  let lambdaBound : ℝ := s ^ 2 * ((n - 1 : ℕ) : ℝ) *
    (2 * K + ((n - 2 : ℕ) : ℝ) * ε ^ 2) + crossBound
  have source := Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
    μ h hh hh2 hhsymm hcenter hprojectionsecond n hn x hx hwindow
  rcases source with
    ⟨hg, hg2, hgmean, hgsecond, hr, hr2, hrsymm, hrcan,
      hv, hs1, hvs, hw, hmlo, hmhi, hL, hL1, hLb, hLmass,
      hδint, hδbd, htilt, hρprob, hFullExp, hFullNorm, hFullPos,
      hFullPoint, hFullDensity, hFullProduct, hFullProb,
      hFullF2, hFullFsq, hFullRows, hFullΛ,
      hFullFid, hFullΛid, hFullFbin, hFullΛbin,
      hFullFpoly, hFullΛpoly, hFullFfinal, hFullΛfinal⟩
  change Measurable g at hg
  change MemLp g 2 μ at hg2
  change (∫ o, g o ^ 2 ∂μ) = 1 at hgsecond
  change Measurable (fun z : Ω × Ω => r z.1 z.2) at hr
  change MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ) at hr2
  change (∀ o y, r o y = r y o) at hrsymm
  change (∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0) at hrcan
  change 1 ≤ s at hs1
  change v ≤ s ^ 2 at hvs
  change Measurable L at hL
  change (∀ o, 0 < L o ∧ L o ≤ 2 * C) at hLb
  change (∫ o, L o ∂μ) = 1 at hLmass
  change (∫ o, (L o - 1) ^ 2 ∂μ) ≤ 4 * C ^ 2 * a ^ 2 at hδbd
  change IsProbabilityMeasure ρ at hρprob
  letI : IsProbabilityMeasure ρ := hρprob
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs1
  have hC1 : 1 ≤ C := by
    dsimp only [C]
    exact Real.one_le_exp (by norm_num)
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC1
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < den := mul_pos hsqrtn (by linarith only [hn3])
  have ha : 0 ≤ a := div_nonneg hx hsqrtn.le
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hδsecond : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ ε ^ 2 := by
    calc
      _ ≤ 4 * C ^ 2 * a ^ 2 := hδbd
      _ = _ := by dsimp only [ε]; ring
  have hdiff (ξ : Fin n → Ω) (i : Fin n) :
      D₁ ξ - D₁del ξ i = ψ ξ i / den := by
    change F ξ / den - Fdel ξ i / den = ψ ξ i / den
    rw [← sub_div]
    congr 1
    exact Shao.OQ6.ResidualDeletion.unorderedPairSum_sub_eraseIncident
      (e ξ) (fun j k => hrsymm (ξ j) (ξ k)) i
  have hsigned (ξ : Fin n → Ω) (i : Fin n) :
      Λsq ξ - Λdelsq ξ i = ψ ξ i ^ 2 + cross ξ i +
        ∑ j ∈ Finset.univ.erase i, r (ξ i) (ξ j) ^ 2 := by
    have hid := Shao.OQ6.ResidualDeletion.rowSqSum_sub_eraseIncident
      (e ξ) (fun j k => hrsymm (ξ j) (ξ k)) i
    simpa only [Λsq, Λdelsq, ψ, ψdel, cross, e, Finset.sum_add_distrib, add_assoc] using hid
  have hper (i : Fin n) :
      Integrable (fun ξ => R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i|) P₀ ∧
      (∫ ξ, R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i| ∂P₀) ≤ 2 * (rowBound / den) ∧
      Integrable (fun ξ => R ξ i * cap ξ i * |cross ξ i|) P₀ ∧
      (∫ ξ, R ξ i * cap ξ i * |cross ξ i| ∂P₀) ≤ 2 * crossBound ∧
      Integrable (fun ξ => R ξ i * cap ξ i * |Λsq ξ - Λdelsq ξ i|) P₀ ∧
      (∫ ξ, R ξ i * cap ξ i * |Λsq ξ - Λdelsq ξ i| ∂P₀) ≤ 2 * lambdaBound := by
    have mixed := wd_mixed_row_cross_bounds μ g hg hg2 hgsecond r hr hr2 hrsymm hrcan
      s hs0 hvs L hL K (fun o => (hLb o).1.le) (fun o => (hLb o).2)
      hLmass ε hε hδsecond a ha n hn i
    rcases mixed with ⟨hHi, hrowI, hrowB, hcrossI, hcrossB, hlambdaI, hlambdaB⟩
    change (∫ ξ, cap ξ i * |ψ ξ i| ∂H i) ≤ rowBound at hrowB
    change (∫ ξ, cap ξ i * |cross ξ i| ∂H i) ≤ crossBound at hcrossB
    change (∫ ξ, cap ξ i * |Λsq ξ - Λdelsq ξ i| ∂H i) ≤ lambdaBound at hlambdaB
    have part := Shao.OQ6.PartialObservationTilt.actual_quadratic_partial_source_transport
      μ h hh hh2 hhsymm hcenter hprojectionsecond n hn i x hx hwindow
    rcases part with
      ⟨hw', hmlo', hmhi', hmpos, hIpos, hmInvPos, hmInvLe, htilt', hρ',
        hNormAll, hExpMinus, hNormMinus, hPoint, hMinusTilt, hHprob, hHdensity,
        hQscale, hQfinite, hQmass, hRbound, hEdges, hDi, hΛi, hXi, hTransport⟩
    change Integrable (fun ξ => D₁ ξ - D₁del ξ i) (H i) at hDi
    change Integrable (fun ξ => Λsq ξ - Λdelsq ξ i) (H i) at hΛi
    change Integrable (fun ξ => cross ξ i) (H i) at hXi
    rcases hTransport (fun ξ => D₁ ξ - D₁del ξ i) hDi with ⟨hDw, hDeq, _, _, _, _, _⟩
    rcases hTransport (fun ξ => cross ξ i) hXi with ⟨hXw, hXeq, _, _, _, _, _⟩
    rcases hTransport (fun ξ => Λsq ξ - Λdelsq ξ i) hΛi with ⟨hLw, hLeq, _, _, _, _, _⟩
    change (∫ ξ, R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i| ∂P₀) =
      m⁻¹ * (∫ ξ, cap ξ i * |D₁ ξ - D₁del ξ i| ∂H i) at hDeq
    change (∫ ξ, R ξ i * cap ξ i * |cross ξ i| ∂P₀) =
      m⁻¹ * (∫ ξ, cap ξ i * |cross ξ i| ∂H i) at hXeq
    change (∫ ξ, R ξ i * cap ξ i * |Λsq ξ - Λdelsq ξ i| ∂P₀) =
      m⁻¹ * (∫ ξ, cap ξ i * |Λsq ξ - Λdelsq ξ i| ∂H i) at hLeq
    have hcap0 (ξ : Fin n → Ω) : 0 ≤ cap ξ i := le_min (abs_nonneg _) (by norm_num)
    have hD0 : 0 ≤ ∫ ξ, cap ξ i * |D₁ ξ - D₁del ξ i| ∂H i :=
      integral_nonneg fun ξ => mul_nonneg (hcap0 ξ) (abs_nonneg _)
    have hX0 : 0 ≤ ∫ ξ, cap ξ i * |cross ξ i| ∂H i :=
      integral_nonneg fun ξ => mul_nonneg (hcap0 ξ) (abs_nonneg _)
    have hL0 : 0 ≤ ∫ ξ, cap ξ i * |Λsq ξ - Λdelsq ξ i| ∂H i :=
      integral_nonneg fun ξ => mul_nonneg (hcap0 ξ) (abs_nonneg _)
    have hcapdiff (ξ : Fin n → Ω) :
        cap ξ i * |D₁ ξ - D₁del ξ i| = cap ξ i * |ψ ξ i| / den := by
      rw [hdiff, abs_div, abs_of_pos hden]
      ring
    have hDordinary : (∫ ξ, cap ξ i * |D₁ ξ - D₁del ξ i| ∂H i) ≤ rowBound / den := by
      simp_rw [hcapdiff]
      simp only [div_eq_mul_inv, integral_mul_const]
      exact mul_le_mul_of_nonneg_right hrowB (inv_nonneg.mpr hden.le)
    refine ⟨hDw, ?_, hXw, ?_, hLw, ?_⟩
    · rw [hDeq]
      exact (mul_le_mul_of_nonneg_right hmInvLe hD0).trans
        (mul_le_mul_of_nonneg_left hDordinary (by norm_num))
    · rw [hXeq]
      exact (mul_le_mul_of_nonneg_right hmInvLe hX0).trans
        (mul_le_mul_of_nonneg_left hcrossB (by norm_num))
    · rw [hLeq]
      exact (mul_le_mul_of_nonneg_right hmInvLe hL0).trans
        (mul_le_mul_of_nonneg_left hlambdaB (by norm_num))
  have scalar := wd_scalar_deletion_bounds C s hC1 hs0 n hn x hx
  change (n : ℝ) * 2 * (rowBound / den) ≤
      4 * Real.sqrt 2 * C * s * (1 + x) ^ 2 / Real.sqrt (n : ℝ) ∧
    (n : ℝ) * 2 * crossBound ≤
      16 * C ^ 2 * s ^ 2 * (n : ℝ) ^ 2 * x * (1 + x) ∧
    (n : ℝ) * 2 * lambdaBound ≤
      24 * C ^ 2 * s ^ 2 * (n : ℝ) ^ 2 * (1 + x) ^ 2 at scalar
  refine ⟨hsigned, fun i => (hper i).1, ?_, fun i => (hper i).2.2.1, ?_,
    fun i => (hper i).2.2.2.2.1, ?_⟩
  · calc
      _ ≤ ∑ i : Fin n, 2 * (rowBound / den) := Finset.sum_le_sum (fun i hi => (hper i).2.1)
      _ = (n : ℝ) * 2 * (rowBound / den) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ ≤ _ := scalar.1
  · calc
      _ ≤ ∑ i : Fin n, 2 * crossBound := Finset.sum_le_sum (fun i hi => (hper i).2.2.2.1)
      _ = (n : ℝ) * 2 * crossBound := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ ≤ _ := scalar.2.1
  · calc
      _ ≤ ∑ i : Fin n, 2 * lambdaBound := Finset.sum_le_sum (fun i hi => (hper i).2.2.2.2.2)
      _ = (n : ℝ) * 2 * lambdaBound := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ ≤ _ := scalar.2.2
end

end Shao.OQ6.WeightedDeletionMoments
