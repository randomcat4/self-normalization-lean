import Shao.OQ6.ActualQuadraticTiltMoments
import Shao.OQ6.FiniteTiltedMoments
import Shao.OQ6.ResidualDeletion
import Shao.OQ6.CanonicalTilt
import Shao.OQ6.CappedSectionEnergy
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Independence.Integration
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace Shao.OQ6.UntiltedCompactCost

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem uc_insert_measurePreserving
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (i : Fin n) :
    let J := {j : Fin n // j ≠ i}
    let Pdel : Measure (J → Ω) := Measure.pi (fun _ : J => μ)
    let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let ins : Ω × (J → Ω) → Fin n → Ω := fun t j =>
      if hji : j = i then t.1 else t.2 ⟨j, hji⟩
    MeasurePreserving ins (μ.prod Pdel) P₀ := by
  classical
  dsimp only
  let J := {j : Fin n // j ≠ i}
  let Pdel : Measure (J → Ω) := Measure.pi (fun _ : J => μ)
  let P₀ : Measure (Fin n → Ω) := Measure.pi
    (fun j : Fin n => if j = i then μ else μ)
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
  have hmp : MeasurePreserving ins (μ.prod Pdel) P₀ := by
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
    change (μ.prod Pdel).map em (Set.pi Set.univ s) = _
    rw [em.map_apply, hpre, Measure.prod_prod, Measure.pi_pi]
    letI : Fintype {j : Fin n // j = i} :=
      Subtype.fintype (fun j : Fin n => j = i)
    have hprod := Fintype.prod_subtype_mul_prod_subtype
      (fun j : Fin n => j = i)
      (fun j : Fin n => (if j = i then μ else μ) (s j))
    have hone :
        (∏ j : {j : Fin n // j = i},
          (if j.val = i then μ else μ) (s j)) = μ (s i) := by
      letI : Unique {j : Fin n // j = i} :=
        { default := ⟨i, rfl⟩
          uniq := fun j => Subtype.ext j.property }
      simp only [Fintype.prod_unique]
      rw [(default : {j : Fin n // j = i}).property]
      simp
    have hrest :
        (∏ j : {j : Fin n // ¬j = i},
          (if j.val = i then μ else μ) (s j)) =
          ∏ j : J, μ (s j) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [if_neg j.property]
    change
      (∏ j : {j : Fin n // j = i}, (if j.val = i then μ else μ) (s j)) *
        (∏ j : {j : Fin n // ¬j = i}, (if j.val = i then μ else μ) (s j)) =
        ∏ j : Fin n, (if j = i then μ else μ) (s j) at hprod
    rw [hone, hrest] at hprod
    exact hprod
  simpa only [P₀, ite_self] using hmp

private theorem uc_iid_row_energy
    {Ω J : Type*} [MeasurableSpace Ω] [Fintype J] [DecidableEq J]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun t : Ω × Ω => r t.1 t.2))
    (hr2 : MemLp (fun t : Ω × Ω => r t.1 t.2) 2 (μ.prod μ))
    (hrsymm : ∀ o y, r o y = r y o)
    (hrcan : ∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0)
    (s : ℝ) (hs : 0 ≤ s)
    (hrsecond :
      (∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)) ≤ s ^ 2) :
    let P : Measure (J → Ω) := Measure.pi (fun _ : J => μ)
    let ψ : (J → Ω) → J → ℝ := fun ξ j =>
      ∑ k ∈ Finset.univ.erase j, r (ξ j) (ξ k)
    let Λsq : (J → Ω) → ℝ := fun ξ => ∑ j : J, ψ ξ j ^ 2
    (∀ j : J, MemLp (fun ξ => ψ ξ j) 2 P) ∧
      Integrable Λsq P ∧
      (∫ ξ, Λsq ξ ∂P) ≤
        2 * ((Fintype.card J).choose 2 : ℝ) * s ^ 2 := by
  classical
  dsimp only
  let P : Measure (J → Ω) := Measure.pi (fun _ : J => μ)
  let Pfin : Measure (Fin (Fintype.card J) → Ω) :=
    Measure.pi (fun _ : Fin (Fintype.card J) => μ)
  let ψ : (J → Ω) → J → ℝ := fun ξ j =>
    ∑ k ∈ Finset.univ.erase j, r (ξ j) (ξ k)
  let Λsq : (J → Ω) → ℝ := fun ξ => ∑ j : J, ψ ξ j ^ 2
  let ψfin : (Fin (Fintype.card J) → Ω) → Fin (Fintype.card J) → ℝ :=
    fun ξ k => Shao.OQ6.ResidualDeletion.rowSum (fun u v => r (ξ u) (ξ v)) k
  let Λfin : (Fin (Fintype.card J) → Ω) → ℝ := fun ξ =>
    ∑ k : Fin (Fintype.card J), ψfin ξ k ^ 2
  have hμ : μ.withDensity (fun _ : Ω => ENNReal.ofReal (1 : ℝ)) = μ := by simp
  have hgeneric := Shao.OQ6.FiniteTiltedMoments.row_square_sum_moment
    μ r hr hr2 hrsymm hrcan s hs hrsecond
    (fun _ => 1) measurable_const 1 (fun _ => by norm_num)
    (fun _ => le_rfl) (by simp) 0 (by norm_num) (by simp) (Fintype.card J)
  rcases hgeneric with ⟨_, _, hψfin, hΛfin, _, hbound⟩
  have hψfin' : ∀ k : Fin (Fintype.card J),
      MemLp (fun ξ => ψfin ξ k) 2 Pfin := by
    simpa only [hμ] using hψfin
  have hΛfin' : Integrable Λfin Pfin := by simpa only [hμ] using hΛfin
  have hbound' : (∫ ξ, Λfin ξ ∂Pfin) ≤
      2 * ((Fintype.card J).choose 2 : ℝ) * s ^ 2 := by
    simpa only [hμ, one_pow, mul_one, zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero] using hbound
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let reindex : (J → Ω) → Fin (Fintype.card J) → Ω := fun ξ k => ξ (e k)
  have hmp : MeasurePreserving reindex P Pfin := by
    have hp := measurePreserving_piCongrLeft (α := fun _ : Fin (Fintype.card J) => Ω)
      (fun _ : Fin (Fintype.card J) => μ) e.symm
    have heq :
        ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card J) => Ω) e.symm) =
          reindex := by
      funext ξ k
      simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, reindex]
    rw [heq] at hp
    exact hp
  have hrow (ξ : J → Ω) (k : Fin (Fintype.card J)) :
      ψ ξ (e k) = ψfin (reindex ξ) k := by
    unfold ψ ψfin Shao.OQ6.ResidualDeletion.rowSum
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ (e k)),
      Finset.sum_erase_eq_sub (Finset.mem_univ k)]
    rw [← e.sum_comp (fun j : J => r (ξ (e k)) (ξ j))]
  have henergy (ξ : J → Ω) : Λsq ξ = Λfin (reindex ξ) := by
    dsimp only [Λsq, Λfin]
    rw [← e.sum_comp (fun j : J => ψ ξ j ^ 2)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hrow]
  have hΛ : Integrable Λsq P :=
    (hmp.integrable_comp_of_integrable hΛfin').congr
      (Filter.Eventually.of_forall fun ξ => (henergy ξ).symm)
  refine ⟨?_, hΛ, ?_⟩
  · intro j
    have hrowj (ξ : J → Ω) : ψ ξ j = ψfin (reindex ξ) (e.symm j) := by
      simpa only [e.apply_symm_apply] using hrow ξ (e.symm j)
    exact (memLp_congr_ae (Filter.Eventually.of_forall hrowj)).mpr
      ((hψfin' (e.symm j)).comp_measurePreserving hmp)
  · have hmap : Integrable Λfin (P.map reindex) := by
      rw [hmp.map_eq]
      exact hΛfin'
    calc
      (∫ ξ, Λsq ξ ∂P) = ∫ ξ, Λfin (reindex ξ) ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall henergy)
      _ = ∫ ξ, Λfin ξ ∂Pfin := by
        rw [← hmp.map_eq]
        exact (integral_map hmp.measurable.aemeasurable hmap.aestronglyMeasurable).symm
      _ ≤ _ := hbound'

private theorem uc_vector_integral_cauchy
    {X J : Type*} [MeasurableSpace X] [Fintype J]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (U V : X → J → ℝ)
    (hU : ∀ j : J, MemLp (fun x => U x j) 2 ν)
    (hV : ∀ j : J, MemLp (fun x => V x j) 2 ν) :
    let A : X → ℝ := fun x => ∑ j : J, U x j ^ 2
    let B : X → ℝ := fun x => ∑ j : J, V x j ^ 2
    let dot : X → ℝ := fun x => ∑ j : J, U x j * V x j
    Integrable dot ν ∧
      (∫ x, |dot x| ∂ν) ≤
        Real.sqrt (∫ x, A x ∂ν) * Real.sqrt (∫ x, B x ∂ν) := by
  classical
  dsimp only
  let A : X → ℝ := fun o => ∑ j : J, U o j ^ 2
  let B : X → ℝ := fun o => ∑ j : J, V o j ^ 2
  let dot : X → ℝ := fun o => ∑ j : J, U o j * V o j
  have hprod (j : J) : Integrable (fun o => U o j * V o j) ν :=
    (hU j).integrable_mul (hV j)
  have hdot : Integrable dot ν := integrable_finsetSum _ (fun j hj => hprod j)
  have hsumabs : Integrable (fun o => ∑ j : J, |U o j * V o j|) ν :=
    integrable_finsetSum _ (fun j hj => (hprod j).abs)
  have hpoint (o : X) : |dot o| ≤ ∑ j : J, |U o j * V o j| :=
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

theorem untilted_compact_weighted_deletion_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgsecond : (∫ o, g o ^ 2 ∂μ) = 1)
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun t : Ω × Ω => r t.1 t.2))
    (hr2 : MemLp (fun t : Ω × Ω => r t.1 t.2) 2 (μ.prod μ))
    (hrsymm : ∀ o y, r o y = r y o)
    (hrcan : ∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0)
    (s : ℝ) (hs : 0 ≤ s)
    (hrsecond :
      (∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)) ≤ s ^ 2)
    (n : ℕ) (hn : 3 ≤ n)
    (z : ℝ) (hz : 0 ≤ z) :
    let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      min (|g (ξ i)| / Real.sqrt (n : ℝ)) (1 / (1 + z))
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
        (fun ξ => cap ξ i * |D₁ ξ - D₁del ξ i|) P₀) ∧
      (∑ i : Fin n,
        ∫ ξ, cap ξ i * |D₁ ξ - D₁del ξ i| ∂P₀) ≤
          2 * s / Real.sqrt (n : ℝ) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => cap ξ i * |cross ξ i|) P₀) ∧
      (∑ i : Fin n,
        ∫ ξ, cap ξ i * |cross ξ i| ∂P₀) ≤
          2 * s ^ 2 * (n : ℝ) ^ 2 ∧
      (∀ i : Fin n, Integrable
        (fun ξ => cap ξ i * |Λsq ξ - Λdelsq ξ i|) P₀) ∧
      (∑ i : Fin n,
        ∫ ξ, cap ξ i * |Λsq ξ - Λdelsq ξ i| ∂P₀) ≤
          4 * s ^ 2 * (n : ℝ) ^ 2 := by
  classical
  dsimp only
  let N : ℝ := (n : ℝ)
  let q : ℝ := Real.sqrt N
  let den : ℝ := q * (N - 1)
  let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let capO : Ω → ℝ := fun o => min (|g o| / q) (1 / (1 + z))
  let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i => capO (ξ i)
  let e : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ j k => r (ξ j) (ξ k)
  let F : (Fin n → Ω) → ℝ := fun ξ => Shao.OQ5.P35.unorderedPairSum (e ξ)
  let Fdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Shao.OQ5.P35.unorderedPairSum (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i)
  let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ j => Shao.OQ6.ResidualDeletion.rowSum (e ξ) j
  let ψdel : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ i j =>
    Shao.OQ6.ResidualDeletion.rowSum (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i) j
  let Λsq : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, ψ ξ j ^ 2
  let Λdelsq : (Fin n → Ω) → Fin n → ℝ := fun ξ i => ∑ j : Fin n, ψdel ξ i j ^ 2
  let D₁ : (Fin n → Ω) → ℝ := fun ξ => F ξ / den
  let D₁del : (Fin n → Ω) → Fin n → ℝ := fun ξ i => Fdel ξ i / den
  let cross : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    ∑ j ∈ Finset.univ.erase i, 2 * r (ξ i) (ξ j) * (ψ ξ j - r (ξ i) (ξ j))
  have hN : 3 ≤ N := by dsimp only [N]; exact_mod_cast hn
  have hN0 : 0 ≤ N := by linarith
  have hNp : 0 < N := by linarith
  have hq : 0 < q := Real.sqrt_pos.2 hNp
  have hq2 : q ^ 2 = N := Real.sq_sqrt hN0
  have hden : 0 < den := mul_pos hq (by linarith)
  have hz1 : 0 < 1 + z := by linarith
  have hfrac : 1 / (1 + z) ≤ (1 : ℝ) := (div_le_iff₀ hz1).2 (by linarith)
  have hc0 (o : Ω) : 0 ≤ capO o := le_min (div_nonneg (abs_nonneg _) hq.le) (by positivity)
  have hc1 (o : Ω) : capO o ≤ 1 := (min_le_right _ _).trans hfrac
  have hcg (o : Ω) : capO o ≤ |g o| / q := min_le_left _ _
  have hcm : Measurable capO := by
    simpa only [capO, Real.norm_eq_abs] using (hg.norm.div_const q).min measurable_const
  have hcapm (i : Fin n) : Measurable (fun ξ => cap ξ i) := hcm.comp (measurable_pi_apply i)
  have hcoord (i : Fin n) : MeasurePreserving (fun ξ : Fin n → Ω => ξ i) P₀ μ :=
    measurePreserving_eval (μ := fun _ : Fin n => μ) i
  have hpull (i : Fin n) (f : Ω → ℝ) (hf : Measurable f) :
      (∫ ξ, f (ξ i) ∂P₀) = ∫ o, f o ∂μ := by
    calc
      _ = ∫ o, f o ∂P₀.map (fun ξ : Fin n → Ω => ξ i) :=
        (integral_map (hcoord i).measurable.aemeasurable hf.aestronglyMeasurable).symm
      _ = _ := by rw [(hcoord i).map_eq]
  have hpair (i j : Fin n) (hij : i ≠ j) :
      MeasurePreserving (fun ξ : Fin n → Ω => (ξ i, ξ j)) P₀ (μ.prod μ) := by
    have hind : iIndepFun (fun k (ξ : Fin n → Ω) => ξ k) P₀ :=
      iIndepFun_pi (μ := fun _ : Fin n => μ)
        (X := fun _ (o : Ω) => o) (fun _ => measurable_id.aemeasurable)
    refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
    simpa only [(hcoord i).map_eq, (hcoord j).map_eq] using
      (hind.indepFun hij).map_prod_eq_prod_map_map
        (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  have he2 (i j : Fin n) (hij : i ≠ j) :
      MemLp (fun ξ : Fin n → Ω => r (ξ i) (ξ j)) 2 P₀ :=
    hr2.comp_measurePreserving (hpair i j hij)
  have hem (i j : Fin n) : Measurable (fun ξ : Fin n → Ω => r (ξ i) (ξ j)) := by
    have hsel : Measurable (fun ξ : Fin n → Ω => (ξ i, ξ j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    simpa only [Function.comp_def] using hr.comp hsel
  have heB (i j : Fin n) (hij : i ≠ j) :
      (∫ ξ, r (ξ i) (ξ j) ^ 2 ∂P₀) ≤ s ^ 2 := by
    have hid : (∫ ξ, r (ξ i) (ξ j) ^ 2 ∂P₀) =
        ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ) := by
      calc
        _ = ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂P₀.map (fun ξ : Fin n → Ω => (ξ i, ξ j)) :=
          (integral_map (hpair i j hij).measurable.aemeasurable
            (hr.pow_const 2).aestronglyMeasurable).symm
        _ = _ := by rw [(hpair i j hij).map_eq]
    rw [hid]
    exact hrsecond
  have hrows := uc_iid_row_energy (J := Fin n) μ r hr hr2 hrsymm hrcan s hs hrsecond
  rcases hrows with ⟨hψ2, hΛi, hΛB⟩
  change (∀ i : Fin n, MemLp (fun ξ => ψ ξ i) 2 P₀) at hψ2
  change Integrable Λsq P₀ at hΛi
  simp only [Fintype.card_fin] at hΛB
  change (∫ ξ, Λsq ξ ∂P₀) ≤ 2 * (n.choose 2 : ℝ) * s ^ 2 at hΛB
  have hchoose2 : ∀ k : ℕ, (k : ℝ) * ((k : ℝ) - 1) = 2 * (k.choose 2 : ℝ) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        simp only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_succ,
          Nat.cast_add, Nat.cast_one] at ih ⊢
        nlinarith only [ih]
  have hΛB' : (∫ ξ, Λsq ξ ∂P₀) ≤ N ^ 2 * s ^ 2 := by
    apply hΛB.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg s)
    rw [← hchoose2 n]
    change N * (N - 1) ≤ N ^ 2
    nlinarith
  have hψm (i : Fin n) : Measurable (fun ξ => ψ ξ i) :=
    Finset.measurable_sum _ (fun j hj => hem i j)
  have hψd2 (i j : Fin n) : MemLp (fun ξ => ψdel ξ i j) 2 P₀ := by
    by_cases hji : j = i
    · simp only [ψdel, Shao.OQ6.ResidualDeletion.rowSum_eraseIncident, if_pos hji]
      exact memLp_const 0
    · simpa only [ψdel, Shao.OQ6.ResidualDeletion.rowSum_eraseIncident, if_neg hji, ψ, e,
        Pi.sub_def] using (hψ2 j).sub (he2 j i hji)
  have hψdm (i j : Fin n) : Measurable (fun ξ => ψdel ξ i j) := by
    by_cases hji : j = i
    · simp only [ψdel, Shao.OQ6.ResidualDeletion.rowSum_eraseIncident, if_pos hji]
      exact measurable_const
    · simpa only [ψdel, Shao.OQ6.ResidualDeletion.rowSum_eraseIncident, if_neg hji, ψ, e,
        Pi.sub_def] using (hψm j).sub (hem j i)
  have hΛdi (i : Fin n) : Integrable (fun ξ => Λdelsq ξ i) P₀ :=
    integrable_finsetSum _ (fun j hj => (hψd2 i j).integrable_sq)
  have hΛm : Measurable Λsq := Finset.measurable_sum _ (fun j hj => (hψm j).pow_const 2)
  have hΛdm (i : Fin n) : Measurable (fun ξ => Λdelsq ξ i) :=
    Finset.measurable_sum _ (fun j hj => (hψdm i j).pow_const 2)
  have hcrossm (i : Fin n) : Measurable (fun ξ => cross ξ i) :=
    Finset.measurable_sum _ (fun j hj => ((hem i j).const_mul 2).mul ((hψm j).sub (hem i j)))
  have hcrossi (i : Fin n) : Integrable (fun ξ => cross ξ i) P₀ := by
    apply integrable_finsetSum
    intro j hj
    have hej := he2 i j (Ne.symm (Finset.mem_erase.mp hj).1)
    simpa only [Pi.mul_apply, Pi.sub_apply, mul_assoc] using (hej.integrable_mul ((hψ2 j).sub hej)).const_mul 2
  have hweight (f : (Fin n → Ω) → ℝ) (hfm : Measurable f) (hfi : Integrable f P₀)
      (i : Fin n) : Integrable (fun ξ => cap ξ i * |f ξ|) P₀ := by
    apply hfi.abs.mono' ((hcapm i).mul hfm.norm).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ξ => by
      change |cap ξ i * (|f ξ|)| ≤ |f ξ|
      rw [abs_of_nonneg (mul_nonneg (hc0 _) (abs_nonneg _))]
      exact mul_le_of_le_one_left (abs_nonneg _) (hc1 _)
  have hcrossW (i : Fin n) := hweight (fun ξ => cross ξ i) (hcrossm i) (hcrossi i) i
  have hΛW (i : Fin n) := hweight (fun ξ => Λsq ξ - Λdelsq ξ i)
    (hΛm.sub (hΛdm i)) (hΛi.sub (hΛdi i)) i
  have hDdiff (ξ : Fin n → Ω) (i : Fin n) : D₁ ξ - D₁del ξ i = ψ ξ i / den := by
    dsimp only [D₁, D₁del]
    rw [← sub_div]
    rw [Shao.OQ6.ResidualDeletion.unorderedPairSum_sub_eraseIncident
      (e ξ) (fun j k => hrsymm (ξ j) (ξ k)) i]
  have hDW (i : Fin n) : Integrable (fun ξ => cap ξ i * |D₁ ξ - D₁del ξ i|) P₀ := by
    simp_rw [hDdiff]
    exact hweight (fun ξ => ψ ξ i / den) ((hψm i).div_const den)
      (((hψ2 i).integrable (by norm_num)).div_const den) i
  have hcapSqI (i : Fin n) : Integrable (fun ξ => cap ξ i ^ 2) P₀ := by
    apply (integrable_const (1 : ℝ)).mono' ((hcapm i).pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ξ => by
      change |cap ξ i ^ 2| ≤ 1
      rw [abs_of_nonneg (sq_nonneg _)]
      have hc := hc0 (ξ i)
      have hc' := hc1 (ξ i)
      nlinarith
  have hcap2 (i : Fin n) : MemLp (fun ξ => cap ξ i) 2 P₀ :=
    (memLp_two_iff_integrable_sq (hcapm i).aestronglyMeasurable).2 (hcapSqI i)
  have hcapSqB (i : Fin n) : (∫ ξ, cap ξ i ^ 2 ∂P₀) ≤ 1 / N := by
    calc
      _ ≤ ∫ ξ, g (ξ i) ^ 2 / q ^ 2 ∂P₀ := by
        apply integral_mono (hcapSqI i) ((hg2.comp_measurePreserving (hcoord i)).integrable_sq.div_const _)
        intro ξ
        have hc := hcg (ξ i)
        have hc' := hc0 (ξ i)
        have hgp : 0 ≤ |g (ξ i)| / q := div_nonneg (abs_nonneg _) hq.le
        calc
          _ ≤ (|g (ξ i)| / q) ^ 2 := by nlinarith
          _ = _ := by
            rw [div_pow, sq_abs]
            rfl
      _ = 1 / N := by rw [integral_div, hpull i _ (hg.pow_const 2), hgsecond, hq2]
  have hcapEnergy : (∫ ξ, (∑ i : Fin n, cap ξ i ^ 2) ∂P₀) ≤ 1 := by
    rw [integral_finsetSum _ (fun i hi => hcapSqI i)]
    calc
      _ ≤ ∑ i : Fin n, (1 / N : ℝ) := Finset.sum_le_sum (fun i hi => hcapSqB i)
      _ = 1 := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; dsimp only [N]; field_simp [hNp.ne']
  have hrowCost : (∑ i : Fin n, ∫ ξ, cap ξ i * |ψ ξ i| ∂P₀) ≤ N * s := by
    have hψabs2 (i : Fin n) : MemLp (fun ξ => |ψ ξ i|) 2 P₀ := by
      simpa only [Real.norm_eq_abs] using (hψ2 i).norm
    have hv := uc_vector_integral_cauchy P₀ cap (fun ξ i => |ψ ξ i|) hcap2 hψabs2
    rcases hv with ⟨hdi, hdb⟩
    have hdot0 (ξ : Fin n → Ω) : 0 ≤ ∑ i : Fin n, cap ξ i * |ψ ξ i| :=
      Finset.sum_nonneg (fun i hi => mul_nonneg (hc0 _) (abs_nonneg _))
    have hb : Real.sqrt (∫ ξ, Λsq ξ ∂P₀) ≤ N * s := by
      calc
        _ ≤ Real.sqrt (N ^ 2 * s ^ 2) := Real.sqrt_le_sqrt hΛB'
        _ = N * s := by rw [← mul_pow, Real.sqrt_sq (mul_nonneg hN0 hs)]
    have ha : Real.sqrt (∫ ξ, (∑ i : Fin n, cap ξ i ^ 2) ∂P₀) ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hcapEnergy
    calc
      _ = ∫ ξ, (∑ i : Fin n, cap ξ i * |ψ ξ i|) ∂P₀ :=
        (integral_finsetSum _ (fun i hi => hweight _ (hψm i) ((hψ2 i).integrable (by norm_num)) i)).symm
      _ ≤ Real.sqrt (∫ ξ, (∑ i : Fin n, cap ξ i ^ 2) ∂P₀) * Real.sqrt (∫ ξ, Λsq ξ ∂P₀) := by
        simpa only [hdot0, abs_of_nonneg, sq_abs] using hdb
      _ ≤ 1 * (N * s) := mul_le_mul ha hb (Real.sqrt_nonneg _) (by norm_num)
      _ = N * s := one_mul _
  have hDsum : (∑ i : Fin n, ∫ ξ, cap ξ i * |D₁ ξ - D₁del ξ i| ∂P₀) ≤ 2 * s / q := by
    calc
      _ = (∑ i : Fin n, ∫ ξ, cap ξ i * |ψ ξ i| ∂P₀) / den := by
        simp_rw [hDdiff, abs_div, abs_of_pos hden, ← mul_div_assoc, integral_div]
        rw [Finset.sum_div]
      _ ≤ (N * s) / den := div_le_div_of_nonneg_right hrowCost hden.le
      _ ≤ 2 * s / q := by
        apply (div_le_iff₀ hden).2
        have hid : 2 * s / q * den = 2 * s * (N - 1) := by
          dsimp only [den]
          field_simp [hq.ne']
        rw [hid]
        nlinarith
  let R : Ω → ℝ := fun o => ∫ y, r o y ^ 2 ∂μ
  have hsection := Shao.OQ6.CanonicalTilt.section_contraction
    μ r hr hr2 hrcan s hs hrsecond (fun _ => 1) measurable_const 1
    (fun _ => by norm_num) (fun _ => le_rfl) (by simp) 0 (by norm_num) (by simp)
  rcases hsection with ⟨hRm, hRi, _, hRB, _, _, _, _, _, _, hsections⟩
  change Measurable R at hRm
  change Integrable R μ at hRi
  change (∫ o, R o ∂μ) ≤ s ^ 2 at hRB
  have hR0 (o : Ω) : 0 ≤ R o := integral_nonneg fun y => sq_nonneg _
  have hcapEnergy0 := Shao.OQ6.CappedSectionEnergy.capped_sqrt_energy_bound
    μ g hg hg2 hgsecond R hRm hR0 hRi s hs hRB (1 / q) (by positivity)
  rcases hcapEnergy0 with ⟨hcapRi0, hcapRB0⟩
  have hcapDom (o : Ω) : capO o ≤ min |(1 / q) * g o| 1 := by
    apply le_min _ (hc1 o)
    calc
      capO o ≤ |g o| / q := hcg o
      _ = |(1 / q) * g o| := by rw [abs_mul, abs_div, abs_one, abs_of_pos hq]; ring
  have hcapRi : Integrable (fun o => capO o * Real.sqrt (R o)) μ := by
    apply hcapRi0.mono' (hcm.mul hRm.sqrt).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun o => by
      change |capO o * Real.sqrt (R o)| ≤ min |(1 / q) * g o| 1 * Real.sqrt (R o)
      rw [abs_of_nonneg (mul_nonneg (hc0 o) (Real.sqrt_nonneg _))]
      exact mul_le_mul_of_nonneg_right (hcapDom o) (Real.sqrt_nonneg _)
  have hcapRB : (∫ o, capO o * Real.sqrt (R o) ∂μ) ≤ s / q := by
    calc
      _ ≤ ∫ o, min |(1 / q) * g o| 1 * Real.sqrt (R o) ∂μ :=
        integral_mono hcapRi hcapRi0 (fun o => mul_le_mul_of_nonneg_right (hcapDom o) (Real.sqrt_nonneg _))
      _ ≤ (1 / q) * s := hcapRB0
      _ = s / q := by ring
  have hcrossB (i : Fin n) : (∫ ξ, cap ξ i * |cross ξ i| ∂P₀) ≤ 2 * N * s ^ 2 := by
    let J := {j : Fin n // j ≠ i}
    let Pdel : Measure (J → Ω) := Measure.pi (fun _ : J => μ)
    let ins : Ω × (J → Ω) → Fin n → Ω := fun t j =>
      if hji : j = i then t.1 else t.2 ⟨j, hji⟩
    let T : (J → Ω) → J → ℝ := fun Y j => ∑ k ∈ Finset.univ.erase j, r (Y j) (Y k)
    let M : (J → Ω) → ℝ := fun Y => ∑ j : J, T Y j ^ 2
    let dot : Ω × (J → Ω) → ℝ := fun t => ∑ j : J, r t.1 (t.2 j) * T t.2 j
    have hcard : (Fintype.card J : ℝ) = N - 1 := by
      letI : Fintype {j : Fin n // j = i} := Subtype.fintype (fun j : Fin n => j = i)
      have hsplit := Fintype.sum_subtype_add_sum_subtype
        (fun j : Fin n => j = i) (fun _ : Fin n => (1 : ℝ))
      have hone : (∑ j : {j : Fin n // j = i}, (1 : ℝ)) = 1 := by
        letI : Unique {j : Fin n // j = i} :=
          { default := ⟨i, rfl⟩
            uniq := fun j => Subtype.ext j.property }
        simp
      rw [hone] at hsplit
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        Fintype.card_fin] at hsplit
      change (1 : ℝ) + (Fintype.card J : ℝ) = N at hsplit
      linarith
    have hT := uc_iid_row_energy (J := J) μ r hr hr2 hrsymm hrcan s hs hrsecond
    rcases hT with ⟨hT2, hMi, hMB⟩
    change (∀ j : J, MemLp (fun Y => T Y j) 2 Pdel) at hT2
    change Integrable M Pdel at hMi
    change (∫ Y, M Y ∂Pdel) ≤ 2 * ((Fintype.card J).choose 2 : ℝ) * s ^ 2 at hMB
    have hMB' : (∫ Y, M Y ∂Pdel) ≤ N ^ 2 * s ^ 2 := by
      apply hMB.trans
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg s)
      rw [← hchoose2 (Fintype.card J), hcard]
      nlinarith
    have hMroot : Real.sqrt (∫ Y, M Y ∂Pdel) ≤ N * s := by
      calc
        _ ≤ Real.sqrt (N ^ 2 * s ^ 2) := Real.sqrt_le_sqrt hMB'
        _ = N * s := by rw [← mul_pow, Real.sqrt_sq (mul_nonneg hN0 hs)]
    have hdotB : ∀ᵐ o ∂μ,
        (∫ Y, |dot (o, Y)| ∂Pdel) ≤ N * s * q * Real.sqrt (R o) := by
      filter_upwards [hsections] with o ho
      have hrow2 : MemLp (r o) 2 μ := ho.1
      have hrowm : Measurable (r o) := hr.comp (measurable_const.prodMk measurable_id)
      have hU2 (j : J) : MemLp (fun Y : J → Ω => r o (Y j)) 2 Pdel :=
        hrow2.comp_measurePreserving (measurePreserving_eval (μ := fun _ : J => μ) j)
      have hAid : (∫ Y, (∑ j : J, r o (Y j) ^ 2) ∂Pdel) = (Fintype.card J : ℝ) * R o := by
        rw [integral_finsetSum _ (fun j hj => (hU2 j).integrable_sq)]
        have hpullJ (j : J) : (∫ Y : J → Ω, r o (Y j) ^ 2 ∂Pdel) = R o := by
          have hm := measurePreserving_eval (μ := fun _ : J => μ) j
          calc
            _ = ∫ y, r o y ^ 2 ∂Pdel.map (fun Y : J → Ω => Y j) :=
              (integral_map hm.measurable.aemeasurable (hrowm.pow_const 2).aestronglyMeasurable).symm
            _ = R o := by rw [hm.map_eq]
        simp_rw [hpullJ]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hAB : (∫ Y, (∑ j : J, r o (Y j) ^ 2) ∂Pdel) ≤ N * R o := by
        rw [hAid, hcard]
        nlinarith [hR0 o]
      have hv := uc_vector_integral_cauchy Pdel (fun Y j => r o (Y j)) T hU2 hT2
      calc
        (∫ Y, |dot (o, Y)| ∂Pdel) ≤
            Real.sqrt (∫ Y, (∑ j : J, r o (Y j) ^ 2) ∂Pdel) * Real.sqrt (∫ Y, M Y ∂Pdel) := hv.2
        _ ≤ Real.sqrt (N * R o) * (N * s) :=
          mul_le_mul (Real.sqrt_le_sqrt hAB) hMroot (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = N * s * q * Real.sqrt (R o) := by rw [Real.sqrt_mul hN0]; dsimp only [q]; ring
    have hsums (f : Fin n → ℝ) : (∑ j ∈ Finset.univ.erase i, f j) = ∑ j : J, f j := by
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
    have hsumzero (f : Fin n → ℝ) (hfi : f i = 0) : (∑ j : Fin n, f j) = ∑ j : J, f j := by
      rw [← hsums, Finset.sum_erase_eq_sub (Finset.mem_univ i), hfi, sub_zero]
    have herow (ξ : Fin n → Ω) (j : J) : ψdel ξ i j = T (fun k => ξ k) j := by
      let f : Fin n → ℝ := Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i j
      have hfi : f i = 0 := by simp [f, Shao.OQ6.ResidualDeletion.eraseIncident]
      have hfk (k : J) : f k = r (ξ j) (ξ k) := by
        simp [f, Shao.OQ6.ResidualDeletion.eraseIncident, e, j.property, k.property]
      change (∑ k ∈ Finset.univ.erase j.val, f k) = _
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ j.val), hsumzero f hfi]
      change (∑ k : J, f k) - f j.val = T (fun k => ξ k) j
      simp_rw [hfk]
      unfold T
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)]
    have hdelins (t : Ω × (J → Ω)) (j : J) : ψdel (ins t) i j = T t.2 j := by
      rw [herow]
      congr 1
      funext k
      simp [ins, k.property]
    have hrowminus (t : Ω × (J → Ω)) (j : J) : ψ (ins t) j - r t.1 (t.2 j) = T t.2 j := by
      have hid := Shao.OQ6.ResidualDeletion.rowSum_eraseIncident (e (ins t)) i j
      change ψdel (ins t) i j = if j.val = i then 0 else ψ (ins t) j - r (ins t j) (ins t i) at hid
      rw [if_neg j.property] at hid
      rw [show ins t j = t.2 j by simp [ins, j.property], show ins t i = t.1 by simp [ins]] at hid
      rw [hrsymm (t.2 j) t.1, hdelins] at hid
      exact hid.symm
    have hcrossins (t : Ω × (J → Ω)) : cross (ins t) i = 2 * dot t := by
      change (∑ j ∈ Finset.univ.erase i,
        2 * r (ins t i) (ins t j) * (ψ (ins t) j - r (ins t i) (ins t j))) = _
      rw [hsums]
      change _ = 2 * (∑ j : J, r t.1 (t.2 j) * T t.2 j)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [show ins t i = t.1 by simp [ins], show ins t j = t.2 j by simp [ins, j.property], hrowminus]
      ring
    have hcapins (t : Ω × (J → Ω)) : cap (ins t) i = capO t.1 := by simp [cap, ins]
    have hins := uc_insert_measurePreserving μ n i
    change MeasurePreserving ins (μ.prod Pdel) P₀ at hins
    have hcompI : Integrable (fun t => cap (ins t) i * |cross (ins t) i|) (μ.prod Pdel) :=
      hins.integrable_comp_of_integrable (hcrossW i)
    have hmap : Integrable (fun ξ => cap ξ i * |cross ξ i|) ((μ.prod Pdel).map ins) := by
      rw [hins.map_eq]
      exact hcrossW i
    calc
      _ = ∫ t, cap (ins t) i * |cross (ins t) i| ∂(μ.prod Pdel) := by
        rw [← hins.map_eq]
        exact integral_map hins.measurable.aemeasurable hmap.aestronglyMeasurable
      _ = ∫ o, (∫ Y, cap (ins (o, Y)) i * |cross (ins (o, Y)) i| ∂Pdel) ∂μ := integral_prod _ hcompI
      _ ≤ ∫ o, (2 * N * s * q) * (capO o * Real.sqrt (R o)) ∂μ := by
        apply integral_mono_ae hcompI.integral_prod_left (hcapRi.const_mul _)
        filter_upwards [hdotB] with o ho
        have hinner : (∫ Y, cap (ins (o, Y)) i * |cross (ins (o, Y)) i| ∂Pdel) =
            (2 * capO o) * (∫ Y, |dot (o, Y)| ∂Pdel) := by
          calc
            _ = ∫ Y, (2 * capO o) * |dot (o, Y)| ∂Pdel := by
              congr 1
              funext Y
              rw [hcapins, hcrossins, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
              ring
            _ = _ := integral_const_mul _ _
        rw [hinner]
        have hh := mul_le_mul_of_nonneg_left ho (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hc0 o))
        nlinarith only [hh]
      _ = (2 * N * s * q) * (∫ o, capO o * Real.sqrt (R o) ∂μ) := integral_const_mul _ _
      _ ≤ (2 * N * s * q) * (s / q) :=
        mul_le_mul_of_nonneg_left hcapRB (by positivity)
      _ = 2 * N * s ^ 2 := by field_simp [hq.ne'] <;> ring
  have hcrossSum : (∑ i : Fin n, ∫ ξ, cap ξ i * |cross ξ i| ∂P₀) ≤ 2 * s ^ 2 * N ^ 2 := by
    calc
      _ ≤ ∑ i : Fin n, (2 * N * s ^ 2) := Finset.sum_le_sum (fun i hi => hcrossB i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; dsimp only [N]; ring
  have hsigned (ξ : Fin n → Ω) (i : Fin n) :
      Λsq ξ - Λdelsq ξ i = ψ ξ i ^ 2 + cross ξ i + ∑ j ∈ Finset.univ.erase i, r (ξ i) (ξ j) ^ 2 := by
    have h := Shao.OQ6.ResidualDeletion.rowSqSum_sub_eraseIncident (e ξ)
      (fun j k => hrsymm (ξ j) (ξ k)) i
    simpa only [Λsq, Λdelsq, ψ, ψdel, cross, e, Finset.sum_add_distrib, add_assoc] using h
  have hEdgeI (i : Fin n) : Integrable (fun ξ => ∑ j ∈ Finset.univ.erase i, r (ξ i) (ξ j) ^ 2) P₀ :=
    integrable_finsetSum _ (fun j hj => (he2 i j (Ne.symm (Finset.mem_erase.mp hj).1)).integrable_sq)
  have hEdgeB (i : Fin n) : (∫ ξ, (∑ j ∈ Finset.univ.erase i, r (ξ i) (ξ j) ^ 2) ∂P₀) ≤ N * s ^ 2 := by
    rw [integral_finsetSum _ (fun j hj => (he2 i j (Ne.symm (Finset.mem_erase.mp hj).1)).integrable_sq)]
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, s ^ 2 :=
        Finset.sum_le_sum (fun j hj => heB i j (Ne.symm (Finset.mem_erase.mp hj).1))
      _ = ((n - 1 : ℕ) : ℝ) * s ^ 2 := by simp
      _ ≤ N * s ^ 2 := mul_le_mul_of_nonneg_right (by dsimp only [N]; exact_mod_cast Nat.sub_le n 1) (sq_nonneg s)
  have hΛsum : (∑ i : Fin n, ∫ ξ, cap ξ i * |Λsq ξ - Λdelsq ξ i| ∂P₀) ≤ 4 * s ^ 2 * N ^ 2 := by
    have hi (i : Fin n) : (∫ ξ, cap ξ i * |Λsq ξ - Λdelsq ξ i| ∂P₀) ≤
        (∫ ξ, ψ ξ i ^ 2 ∂P₀) + (∫ ξ, cap ξ i * |cross ξ i| ∂P₀) + N * s ^ 2 := by
      calc
        _ ≤ ∫ ξ, (ψ ξ i ^ 2 + cap ξ i * |cross ξ i| + ∑ j ∈ Finset.univ.erase i, r (ξ i) (ξ j) ^ 2) ∂P₀ := by
          apply integral_mono (hΛW i) (((hψ2 i).integrable_sq.add (hcrossW i)).add (hEdgeI i))
          intro ξ
          change cap ξ i * |Λsq ξ - Λdelsq ξ i| ≤
            ψ ξ i ^ 2 + cap ξ i * |cross ξ i| + ∑ j ∈ Finset.univ.erase i, r (ξ i) (ξ j) ^ 2
          rw [hsigned]
          let a := ψ ξ i ^ 2
          let b := cross ξ i
          let c := ∑ j ∈ Finset.univ.erase i, r (ξ i) (ξ j) ^ 2
          have ha : 0 ≤ a := sq_nonneg _
          have hc : 0 ≤ c := Finset.sum_nonneg (fun j hj => sq_nonneg _)
          have habs : |a + b + c| ≤ a + |b| + c := by
            calc
              _ ≤ |a + b| + |c| := abs_add_le _ _
              _ ≤ (|a| + |b|) + |c| := add_le_add (abs_add_le _ _) le_rfl
              _ = _ := by rw [abs_of_nonneg ha, abs_of_nonneg hc]
          have hh := mul_le_mul_of_nonneg_left habs (hc0 (ξ i))
          have hha := mul_le_mul_of_nonneg_right (hc1 (ξ i)) ha
          have hhc := mul_le_mul_of_nonneg_right (hc1 (ξ i)) hc
          change cap ξ i * |a + b + c| ≤ a + cap ξ i * |b| + c
          nlinarith only [hh, hha, hhc]
        _ = (∫ ξ, ψ ξ i ^ 2 ∂P₀) + (∫ ξ, cap ξ i * |cross ξ i| ∂P₀) +
            ∫ ξ, (∑ j ∈ Finset.univ.erase i, r (ξ i) (ξ j) ^ 2) ∂P₀ := by
          have houter := integral_add ((hψ2 i).integrable_sq.add (hcrossW i)) (hEdgeI i)
          have hinner := integral_add (hψ2 i).integrable_sq (hcrossW i)
          simpa only [Pi.add_apply] using
            houter.trans (congrArg (fun t : ℝ =>
              t + ∫ ξ, (∑ j ∈ Finset.univ.erase i, r (ξ i) (ξ j) ^ 2) ∂P₀) hinner)
        _ ≤ _ := add_le_add le_rfl (hEdgeB i)
    calc
      _ ≤ ∑ i : Fin n, ((∫ ξ, ψ ξ i ^ 2 ∂P₀) + (∫ ξ, cap ξ i * |cross ξ i| ∂P₀) + N * s ^ 2) :=
        Finset.sum_le_sum (fun i hi' => hi i)
      _ = (∫ ξ, Λsq ξ ∂P₀) + (∑ i : Fin n, ∫ ξ, cap ξ i * |cross ξ i| ∂P₀) + N ^ 2 * s ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← integral_finsetSum _ (fun i hi' => (hψ2 i).integrable_sq)]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp only [N, Λsq]
        ring
      _ ≤ _ := by nlinarith only [hΛB', hcrossSum]
  exact ⟨hsigned, hDW, hDsum, hcrossW, hcrossSum, hΛW, hΛsum⟩

end

end Shao.OQ6.UntiltedCompactCost
