import Shao.OQ6.UniformPMomentLowEnergy
import Shao.OQ6.OriginalCountablyGeneratedModel
import Shao.OQ6.ActualPhysicalCompactCDF
import Shao.OQ6.CompactTailBounds
import Shao.OQ6.UntiltedCompactCost
import Shao.OQ6.ActualRemainderEnvelope
import Shao.OQ6.ResidualDeletionMeasurable

set_option autoImplicit false

namespace Shao.OQ6.UniformPMomentOriginalPhysicalCompactCDF

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

universe u
private theorem finite_projection_residual_numerator
    {n : ℕ} (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ)
    (hn : 3 ≤ n) :
    (∑ i : Fin n, g i) / Real.sqrt (n : ℝ) +
      Shao.OQ5.P35.unorderedPairSum r /
        (Real.sqrt (n : ℝ) * ((n : ℝ) - 1)) =
      Real.sqrt (n : ℝ) *
        Shao.OQ6.FiniteRows.uStatistic (fun i j => g i + g j + r i j) / 2
:= by
  classical
  let N : ℝ := (n : ℝ)
  let q : ℝ := Real.sqrt N
  let S : ℝ := ∑ i : Fin n, g i
  let H0 : Fin n → Fin n → ℝ := fun i j => g i + g j
  have hN3 : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hNpos : 0 < N := by linarith
  have hNne : N ≠ 0 := hNpos.ne'
  have hN1ne : N - 1 ≠ 0 := by linarith
  have hqpos : 0 < q := Real.sqrt_pos.mpr hNpos
  have hqsq : q ^ 2 = N := Real.sq_sqrt hNpos.le
  have hq1ne : q ^ 2 - 1 ≠ 0 := by rw [hqsq]; exact hN1ne
  have herase (i : Fin n) :
      (∑ j ∈ Finset.univ.erase i, H0 i j) = (N - 2) * g i + S := by
    have hsumg : (∑ j ∈ Finset.univ.erase i, g j) = S - g i := by
      have ht := Finset.sum_erase_add Finset.univ g (Finset.mem_univ i)
      change (∑ j ∈ Finset.univ.erase i, g j) + g i = S at ht
      linarith
    have hsumc : (∑ j ∈ Finset.univ.erase i, g i) = (N - 1) * g i := by
      have ht := Finset.sum_erase_add Finset.univ (fun _ : Fin n => g i)
        (Finset.mem_univ i)
      have hfull : (∑ _j : Fin n, g i) = N * g i := by simp [N]
      rw [hfull] at ht
      linarith
    dsimp only [H0]
    rw [Finset.sum_add_distrib, hsumc, hsumg]
    ring
  have hpair0 : Shao.OQ5.P35.unorderedPairSum H0 = (N - 1) * S := by
    have ht := Shao.OQ5.P35.offDiagonalSum_eq_two_unordered H0
      (fun i j => add_comm (g i) (g j))
    simp_rw [herase] at ht
    have hsum :
        (∑ i : Fin n, ((N - 2) * g i + S)) = 2 * (N - 1) * S := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change (N - 2) * S + N * S = 2 * (N - 1) * S
      ring
    rw [hsum] at ht
    linarith
  have hsplit :
      Shao.OQ5.P35.unorderedPairSum (fun i j => g i + g j + r i j) =
        Shao.OQ5.P35.unorderedPairSum H0 + Shao.OQ5.P35.unorderedPairSum r := by
    unfold Shao.OQ5.P35.unorderedPairSum
    simp only [H0]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring
  have hchoose : (n.choose 2 : ℝ) = N * (N - 1) / 2 := by
    have ht := Shao.OQ5.P35.pairCount_eq_choose n
    simpa only [Shao.OQ5.P35.pairCount, N] using ht.symm
  have hU :
      Shao.OQ6.FiniteRows.uStatistic (fun i j => g i + g j + r i j) =
        2 * S / N + 2 * Shao.OQ5.P35.unorderedPairSum r / (N * (N - 1)) := by
    unfold Shao.OQ6.FiniteRows.uStatistic
    rw [hsplit, hpair0, hchoose]
    field_simp [hNne, hN1ne] <;> ring
  change S / q + Shao.OQ5.P35.unorderedPairSum r / (q * (N - 1)) =
    q * Shao.OQ6.FiniteRows.uStatistic (fun i j => g i + g j + r i j) / 2
  rw [hU, ← hqsq]
  field_simp [hqpos.ne', hq1ne] <;> ring

private theorem compact_retained_deletion_measurability
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun t : Ω × Ω => r t.1 t.2))
    (n : ℕ) (hn : 3 ≤ n) (s : ℝ) (hs : 1 ≤ s) :
    let N : ℝ := (n : ℝ)
    let q : ℝ := Real.sqrt N
    let eDeleted : ∀ i : Fin n, ({j : Fin n // j ≠ i} → Ω) → Fin n → Fin n → ℝ :=
      fun i η j k => if hj : j = i then 0 else if hk : k = i then 0 else
        r (η ⟨j, hj⟩) (η ⟨k, hk⟩)
    let Adeleted : ∀ i : Fin n, ({j : Fin n // j ≠ i} → Ω) → ℝ :=
      fun i η => |Shao.OQ5.P35.unorderedPairSum (eDeleted i η) / (q * (N - 1))|
    let Bdeleted : ∀ i : Fin n, ({j : Fin n // j ≠ i} → Ω) → ℝ :=
      fun i η => 4096 * (s / q +
        (∑ j : Fin n, Shao.OQ6.ResidualDeletion.rowSum (eDeleted i η) j ^ 2) /
          (s * (N ^ 2 * q)))
    (∀ i : Fin n, Measurable (Adeleted i)) ∧
      (∀ i : Fin n, Measurable (Bdeleted i)) ∧
      (∀ (i : Fin n) (η : {j : Fin n // j ≠ i} → Ω), 0 ≤ Adeleted i η) ∧
      (∀ (i : Fin n) (η : {j : Fin n // j ≠ i} → Ω), 0 ≤ Bdeleted i η)
:= by
  classical
  intro N q eDeleted Adeleted Bdeleted
  have hN3 : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hNpos : 0 < N := by linarith only [hN3]
  have hqpos : 0 < q := Real.sqrt_pos.mpr hNpos
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hs
  have hdenpos : 0 < s * (N ^ 2 * q) := by positivity
  have hEdm (i : Fin n) : Measurable (eDeleted i) := by
    apply Measurable.of_eval
    intro j
    apply Measurable.of_eval
    intro k
    by_cases hj : j = i
    · simpa only [eDeleted, dif_pos hj] using
        (measurable_const : Measurable (fun _ : ({j : Fin n // j ≠ i} → Ω) => (0 : ℝ)))
    · by_cases hk : k = i
      · simpa only [eDeleted, dif_neg hj, dif_pos hk] using
          (measurable_const : Measurable (fun _ : ({j : Fin n // j ≠ i} → Ω) => (0 : ℝ)))
      · have hpair : Measurable
            (fun η : ({j : Fin n // j ≠ i} → Ω) =>
              (η (⟨j, hj⟩ : {j : Fin n // j ≠ i}),
                η (⟨k, hk⟩ : {j : Fin n // j ≠ i}))) :=
          (measurable_pi_apply (⟨j, hj⟩ : {j : Fin n // j ≠ i})).prodMk
            (measurable_pi_apply (⟨k, hk⟩ : {j : Fin n // j ≠ i}))
        simpa only [eDeleted, dif_neg hj, dif_neg hk, Function.comp_def] using
          hr.comp hpair
  have hEdentry (i j k : Fin n) :
      Measurable (fun η : ({j : Fin n // j ≠ i} → Ω) => eDeleted i η j k) :=
    (measurable_pi_apply k).comp ((measurable_pi_apply j).comp (hEdm i))
  have hEdpair (i : Fin n) : Measurable
      (fun η : ({j : Fin n // j ≠ i} → Ω) => Shao.OQ5.P35.unorderedPairSum (eDeleted i η)) := by
    dsimp only [Shao.OQ5.P35.unorderedPairSum]
    apply Finset.measurable_sum
    intro j hj
    apply Finset.measurable_sum
    intro k hk
    by_cases hjk : j < k
    · simpa only [if_pos hjk] using hEdentry i j k
    · simpa only [if_neg hjk] using
        (measurable_const : Measurable (fun _ : ({j : Fin n // j ≠ i} → Ω) => (0 : ℝ)))
  have hEdrow (i j : Fin n) : Measurable
      (fun η : ({j : Fin n // j ≠ i} → Ω) =>
        Shao.OQ6.ResidualDeletion.rowSum (eDeleted i η) j) := by
    dsimp only [Shao.OQ6.ResidualDeletion.rowSum]
    exact Finset.measurable_sum _ (fun k _ => hEdentry i j k)
  have hEdenergy (i : Fin n) : Measurable
      (fun η : ({j : Fin n // j ≠ i} → Ω) =>
        ∑ j : Fin n, Shao.OQ6.ResidualDeletion.rowSum (eDeleted i η) j ^ 2) :=
    Finset.measurable_sum _ (fun j _ => (hEdrow i j).pow_const 2)
  have hAdm (i : Fin n) : Measurable (Adeleted i) :=
    continuous_abs.measurable.comp ((hEdpair i).div_const (q * (N - 1)))
  have hBdm (i : Fin n) : Measurable (Bdeleted i) :=
    (measurable_const.add ((hEdenergy i).div_const (s * (N ^ 2 * q)))).const_mul 4096
  have hAdnonneg (i : Fin n) (η : {j : Fin n // j ≠ i} → Ω) : 0 ≤ Adeleted i η :=
    abs_nonneg _
  have hBdnonneg (i : Fin n) (η : {j : Fin n // j ≠ i} → Ω) : 0 ≤ Bdeleted i η := by
    dsimp only [Bdeleted]
    exact mul_nonneg (by norm_num)
      (add_nonneg (div_nonneg hspos.le hqpos.le)
        (div_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg _)) hdenpos.le))
  exact ⟨hAdm, hBdm, hAdnonneg, hBdnonneg⟩

private theorem actual_compact_cost_admissibility
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond : (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 3 ≤ n) (y : ℝ) (hy : 0 ≤ y) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
    let s : ℝ := 1 + Real.sqrt v
    let N : ℝ := (n : ℝ)
    let q : ℝ := Real.sqrt N
    let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let e : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ζ j k => r (ζ j) (ζ k)
    let F : (Fin n → Ω) → ℝ := fun ζ => Shao.OQ5.P35.unorderedPairSum (e ζ)
    let ψ : (Fin n → Ω) → Fin n → ℝ := fun ζ j => Shao.OQ6.ResidualDeletion.rowSum (e ζ) j
    let Λsq : (Fin n → Ω) → ℝ := fun ζ => ∑ j : Fin n, ψ ζ j ^ 2
    let D1 : (Fin n → Ω) → ℝ := fun ζ => F ζ / (q * (N - 1))
    let A : (Fin n → Ω) → ℝ := fun ζ => |D1 ζ|
    let Benv : (Fin n → Ω) → ℝ := fun ζ =>
      4096 * (s / q + Λsq ζ / (s * (N ^ 2 * q)))
    let eDeleted : ∀ i : Fin n, ({j : Fin n // j ≠ i} → Ω) → Fin n → Fin n → ℝ :=
      fun i η j k => if hj : j = i then 0 else if hk : k = i then 0 else
        r (η ⟨j, hj⟩) (η ⟨k, hk⟩)
    let Adeleted : ∀ i : Fin n, ({j : Fin n // j ≠ i} → Ω) → ℝ :=
      fun i η => |Shao.OQ5.P35.unorderedPairSum (eDeleted i η) / (q * (N - 1))|
    let Bdeleted : ∀ i : Fin n, ({j : Fin n // j ≠ i} → Ω) → ℝ :=
      fun i η => 4096 * (s / q +
        (∑ j : Fin n, Shao.OQ6.ResidualDeletion.rowSum (eDeleted i η) j ^ 2) /
          (s * (N ^ 2 * q)))
    let cap : (Fin n → Ω) → Fin n → ℝ := fun ζ i => min (|g (ζ i)| / q) (1 / (1 + y))
    let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ζ i =>
      cap ζ i * (|A ζ - Adeleted i (fun j => ζ j.1)| +
        y * |Benv ζ - Bdeleted i (fun j => ζ j.1)|)
    let fullTest : (Fin n → Ω) → ℝ := fun ζ => A ζ + y * Benv ζ
    let δ : Fin n → ℝ := fun i =>
      ∫ ζ, ((1 + y) * (g (ζ i) / q)) ^ 2 * min |(1 + y) * (g (ζ i) / q)| 1 ∂P₀
    let Lcompact : ℝ := N * (∫ o, Shao.truncationF ((1 + y) * (g o / q)) ∂μ)
    let Kcost : ℝ := (∑ i : Fin n, δ i) + (∫ ζ, fullTest ζ ∂P₀) +
      ∑ i : Fin n, ∫ ζ, deletedTest ζ i ∂P₀
    Measurable g ∧ MemLp g 2 μ ∧ (∫ o, g o ∂μ) = 0 ∧ (∫ o, g o ^ 2 ∂μ) = 1 ∧
      Measurable (fun t : Ω × Ω => r t.1 t.2) ∧ (∀ o z : Ω, r o z = r z o) ∧
      Measurable D1 ∧ Measurable A ∧ Measurable Benv ∧
      (∀ i : Fin n, Measurable (Adeleted i)) ∧
      (∀ i : Fin n, Measurable (Bdeleted i)) ∧
      (∀ ζ : Fin n → Ω, 0 ≤ A ζ) ∧ (∀ ζ : Fin n → Ω, 0 ≤ Benv ζ) ∧
      (∀ (i : Fin n) (η : {j : Fin n // j ≠ i} → Ω), 0 ≤ Adeleted i η) ∧
      (∀ (i : Fin n) (η : {j : Fin n // j ≠ i} → Ω), 0 ≤ Bdeleted i η) ∧
      Integrable fullTest P₀ ∧
      (∀ i : Fin n, Integrable (fun ζ => deletedTest ζ i) P₀) ∧
      (∑ i : Fin n, δ i) = Lcompact ∧ 0 ≤ Lcompact ∧
      Kcost ≤ Lcompact + 16 * (1 + 4096) * (1 + y) * s / q
:= by
  classical
  intro g r v s N q P₀ e F ψ Λsq D1 A Benv eDeleted Adeleted Bdeleted cap deletedTest fullTest δ Lcompact Kcost
  have hdata := Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
    μ h hh hh2 hhsymm hcenter hprojectionsecond 3 (by omega) 0 (by norm_num) (by positivity)
  dsimp only at hdata
  rcases hdata with ⟨hgm, hg2, hgmean, hgsecond, hrm, _, hrsymm, _, _, hs1, _, _⟩
  change Measurable g at hgm
  change MemLp g 2 μ at hg2
  change (∫ o, g o ∂μ) = 0 at hgmean
  change (∫ o, g o ^ 2 ∂μ) = 1 at hgsecond
  change Measurable (fun t : Ω × Ω => r t.1 t.2) at hrm
  change (∀ o t, r o t = r t o) at hrsymm
  change 1 ≤ s at hs1
  have hN3 : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hNpos : 0 < N := by linarith only [hN3]
  have hNne : N ≠ 0 := hNpos.ne'
  have hqpos : 0 < q := Real.sqrt_pos.mpr hNpos
  have hqsq : q ^ 2 = N := Real.sq_sqrt hNpos.le
  have hN1pos : 0 < N - 1 := by linarith only [hN3]
  have hspos : 0 < s := by linarith only [hs1]
  have hdenpos : 0 < s * (N ^ 2 * q) := by positivity
  let Fdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Shao.OQ5.P35.unorderedPairSum (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i)
  let ψdel : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ i j =>
    Shao.OQ6.ResidualDeletion.rowSum (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i) j
  let Λdelsq : (Fin n → Ω) → Fin n → ℝ := fun ξ i => ∑ j : Fin n, ψdel ξ i j ^ 2
  let D1del : (Fin n → Ω) → Fin n → ℝ := fun ξ i => Fdel ξ i / (q * (N - 1))
  let Adel : (Fin n → Ω) → Fin n → ℝ := fun ξ i => |D1del ξ i|
  let Bdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    4096 * (s / q + Λdelsq ξ i / (s * (N ^ 2 * q)))
  let projectionTest : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Shao.truncationF ((1 + y) * (g (ξ i) / q))
  let deletedOriginal : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    cap ξ i * (|A ξ - Adel ξ i| + y * |Benv ξ - Bdel ξ i|)
  have hem (j k : Fin n) : Measurable (fun ξ => e ξ j k) := by
    have hpair : Measurable (fun ξ : Fin n → Ω => (ξ j, ξ k)) :=
      (measurable_pi_apply j).prodMk (measurable_pi_apply k)
    exact hrm.comp hpair
  have hFm : Measurable F := by
    dsimp only [F, Shao.OQ5.P35.unorderedPairSum]
    apply Finset.measurable_sum
    intro j hj
    apply Finset.measurable_sum
    intro k hk
    by_cases hjk : j < k
    · simpa only [if_pos hjk] using hem j k
    · simpa only [if_neg hjk] using
        (measurable_const : Measurable (fun _ : Fin n → Ω => (0 : ℝ)))
  have hψm (j : Fin n) : Measurable (fun ξ => ψ ξ j) := by
    dsimp only [ψ, Shao.OQ6.ResidualDeletion.rowSum]
    exact Finset.measurable_sum _ (fun k _ => hem j k)
  have hΛm : Measurable Λsq :=
    Finset.measurable_sum _ (fun j _ => (hψm j).pow_const 2)
  have hD1m : Measurable D1 := hFm.div_const (q * (N - 1))
  have hAm : Measurable A := continuous_abs.measurable.comp hD1m
  have hBm : Measurable Benv :=
    (measurable_const.add (hΛm.div_const (s * (N ^ 2 * q)))).const_mul 4096
  have hAnonneg (ξ : Fin n → Ω) : 0 ≤ A ξ := abs_nonneg _
  have hΛnonneg (ξ : Fin n → Ω) : 0 ≤ Λsq ξ :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hBnonneg (ξ : Fin n → Ω) : 0 ≤ Benv ξ := by
    dsimp only [Benv]
    exact mul_nonneg (by norm_num)
      (add_nonneg (div_nonneg hspos.le hqpos.le)
        (div_nonneg (hΛnonneg ξ) hdenpos.le))
  have hDeletedData := compact_retained_deletion_measurability r hrm n hn s hs1
  change (∀ i : Fin n, Measurable (Adeleted i)) ∧
    (∀ i : Fin n, Measurable (Bdeleted i)) ∧
    (∀ (i : Fin n) (η : {j : Fin n // j ≠ i} → Ω), 0 ≤ Adeleted i η) ∧
    (∀ (i : Fin n) (η : {j : Fin n // j ≠ i} → Ω), 0 ≤ Bdeleted i η) at hDeletedData
  rcases hDeletedData with ⟨hAdm, hBdm, hAdnonneg, hBdnonneg⟩
  have hEdpull (i : Fin n) (ξ : Fin n → Ω) :
      eDeleted i (fun j => ξ j.1) = Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i := by
    funext j k
    by_cases hj : j = i
    · simp [eDeleted, Shao.OQ6.ResidualDeletion.eraseIncident, e, hj]
    · by_cases hk : k = i
      · simp [eDeleted, Shao.OQ6.ResidualDeletion.eraseIncident, e, hj, hk]
      · simp [eDeleted, Shao.OQ6.ResidualDeletion.eraseIncident, e, hj, hk]
  have hAdpull (i : Fin n) (ξ : Fin n → Ω) :
      Adeleted i (fun j => ξ j.1) = Adel ξ i := by
    dsimp only [Adeleted, Adel, D1del, Fdel]
    rw [hEdpull]
  have hBdpull (i : Fin n) (ξ : Fin n → Ω) :
      Bdeleted i (fun j => ξ j.1) = Bdel ξ i := by
    dsimp only [Bdeleted, Bdel, Λdelsq, ψdel]
    rw [hEdpull]
  have hDeletedSame : deletedTest = deletedOriginal := by
    funext ξ i
    dsimp only [deletedTest, deletedOriginal]
    rw [hAdpull, hBdpull]
  have hcost := Shao.OQ6.UntiltedCompactCost.actual_quadratic_compact_source_cost
    μ h hh hh2 hhsymm hcenter hprojectionsecond n hn y hy 4096 (by norm_num)
  dsimp only at hcost
  rcases hcost with ⟨hProjI, hLeq, hLnonneg, hLupper, hAi, hAdeli, hBi, hBdeli,
    hAdiffi, hBdiffi, hDeletedI, hResidualBound, hSourceBound⟩
  change (∑ i : Fin n, ∫ ξ, projectionTest ξ i ∂P₀) = Lcompact at hLeq
  change 0 ≤ (∑ i : Fin n, ∫ ξ, projectionTest ξ i ∂P₀) at hLnonneg
  rw [hLeq] at hLnonneg
  change Integrable A P₀ at hAi
  change Integrable Benv P₀ at hBi
  change (∀ i : Fin n, Integrable (fun ξ => deletedOriginal ξ i) P₀) at hDeletedI
  change (∑ i : Fin n, ∫ ξ, projectionTest ξ i ∂P₀) +
    ((∫ ξ, A ξ ∂P₀) + y * (∫ ξ, Benv ξ ∂P₀) +
      ∑ i : Fin n, ∫ ξ, deletedOriginal ξ i ∂P₀) ≤
    (∑ i : Fin n, ∫ ξ, projectionTest ξ i ∂P₀) +
      16 * (1 + 4096) * (1 + y) * s / q at hSourceBound
  rw [← hDeletedSame] at hDeletedI hSourceBound
  rw [hLeq] at hSourceBound
  have hFullI : Integrable fullTest P₀ := hAi.add (hBi.const_mul y)
  have hFullEq : (∫ ξ, fullTest ξ ∂P₀) =
      (∫ ξ, A ξ ∂P₀) + y * (∫ ξ, Benv ξ ∂P₀) := by
    dsimp only [fullTest]
    rw [integral_add hAi (hBi.const_mul y), integral_const_mul]
  have hDeltaEq (i : Fin n) : δ i = ∫ ξ, projectionTest ξ i ∂P₀ := rfl
  have hL0Eq : (∑ i : Fin n, δ i) = Lcompact := by
    simpa only [hDeltaEq] using hLeq
  have hKbound : Kcost ≤ Lcompact + 16 * (1 + 4096) * (1 + y) * s / q := by
    dsimp only [Kcost]
    rw [hL0Eq, hFullEq]
    linarith only [hSourceBound]
  exact ⟨hgm, hg2, hgmean, hgsecond, hrm, hrsymm, hD1m, hAm, hBm, hAdm, hBdm,
    hAnonneg, hBnonneg, hAdnonneg, hBdnonneg, hFullI, hDeletedI, hL0Eq, hLnonneg, hKbound⟩

private theorem actual_compact_numerator_threshold_bounds
    (C : ℝ)
    (hSZC : Shao.OQ6.NormalizedIntegrableCDFAssembly.ScalarShaoZhouFiniteCostCDFInput.{u} C)
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond : (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 3 ≤ n) (y : ℝ) (hy : 0 ≤ y) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
    let s : ℝ := 1 + Real.sqrt v
    let N : ℝ := (n : ℝ)
    let q : ℝ := Real.sqrt N
    let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let J : (Fin n → Ω) → ℝ := fun ζ =>
      Shao.OQ6.FiniteRows.uncenteredSq (fun i j => h (ζ i) (ζ j))
    let Vsq : (Fin n → Ω) → ℝ := fun ζ => (∑ i : Fin n, g (ζ i) ^ 2) / N
    let W : (Fin n → Ω) → ℝ := fun ζ => (∑ i : Fin n, g (ζ i)) / q
    let D2 : (Fin n → Ω) → ℝ := fun ζ => if 0 < Vsq ζ then J ζ / Vsq ζ - 1 else 0
    let G : Set (Fin n → Ω) := {ζ | (1 / 2 : ℝ) ≤ Vsq ζ ∧
      |W ζ| ≤ Real.sqrt q * (4 + Real.sqrt (Vsq ζ))}
    let D1 : (Fin n → Ω) → ℝ := fun ζ =>
      Shao.OQ5.P35.unorderedPairSum (fun i j => r (ζ i) (ζ j)) / (q * (N - 1))
    let D2c : (Fin n → Ω) → ℝ := fun ζ =>
      if ζ ∈ G then max (D2 ζ) (-(1 / 2 : ℝ)) else 0
    let Lcompact : ℝ := N * (∫ o, Shao.truncationF ((1 + y) * (g o / q)) ∂μ)
    let Ecost : ℝ := C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q)
    s ≤ q →
      |P₀.real {ζ | y * Real.sqrt (Vsq ζ) * Real.sqrt (1 + D2c ζ) < W ζ + D1 ζ} -
        (1 - Shao.OQ4.standardNormalCDF y)| ≤ Ecost ∧
      |P₀.real {ζ | y * Real.sqrt (Vsq ζ) * Real.sqrt (1 + D2c ζ) ≤ W ζ + D1 ζ} -
        (1 - Shao.OQ4.standardNormalCDF y)| ≤ Ecost
:= by
  classical
  intro g r v s N q P₀ J Vsq W D2 G D1 D2c Lcompact Ecost hscale
  let z : ℝ := y
  let O : Fin n → (Fin n → Ω) → Ω := fun i ξ => ξ i
  let g0 : Fin n → Ω → ℝ := fun _ o => g o / q
  let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ξ => g (ξ i) / q
  let W0 : (Fin n → Ω) → ℝ := fun ξ => ∑ i : Fin n, ξ0 i ξ
  let V0 : (Fin n → Ω) → ℝ := fun ξ => Real.sqrt (∑ i : Fin n, (ξ0 i ξ) ^ 2)
  let e : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ j k => r (ξ j) (ξ k)
  let F : (Fin n → Ω) → ℝ := fun ξ => Shao.OQ5.P35.unorderedPairSum (e ξ)
  let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ j => Shao.OQ6.ResidualDeletion.rowSum (e ξ) j
  let Λsq : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, ψ ξ j ^ 2
  let A : (Fin n → Ω) → ℝ := fun ξ => |D1 ξ|
  let B : (Fin n → Ω) → ℝ := fun ξ => 4096 * (s / q + Λsq ξ / (s * (N ^ 2 * q)))
  let eDeleted : ∀ i : Fin n, ({j : Fin n // j ≠ i} → Ω) → Fin n → Fin n → ℝ := fun i η j k => if hj : j = i then 0 else if hk : k = i then 0 else r (η ⟨j, hj⟩) (η ⟨k, hk⟩)
  let Adeleted : ∀ i : Fin n, ({j : Fin n // j ≠ i} → Ω) → ℝ := fun i η => |Shao.OQ5.P35.unorderedPairSum (eDeleted i η) / (q * (N - 1))|
  let Bdeleted : ∀ i : Fin n, ({j : Fin n // j ≠ i} → Ω) → ℝ := fun i η => 4096 * (s / q + (∑ j : Fin n, Shao.OQ6.ResidualDeletion.rowSum (eDeleted i η) j ^ 2) / (s * (N ^ 2 * q)))
  let κ0 : (Fin n → Ω) → ℝ := fun _ => 0
  let b0 : (Fin n → Ω) → ℝ := fun ξ => Real.sqrt (1 + D2c ξ)
  let N0 : (Fin n → Ω) → ℝ := fun ξ => W0 ξ + D1 ξ
  let d0 : (Fin n → Ω) → ℝ := fun ξ => V0 ξ * b0 ξ
  let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i => min (|g (ξ i)| / q) (1 / (1 + z))
  let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    cap ξ i * (|A ξ - Adeleted i (fun j => ξ j.1)| +
      z * |B ξ - Bdeleted i (fun j => ξ j.1)|)
  let fullTest : (Fin n → Ω) → ℝ := fun ξ => A ξ + z * B ξ
  let δ0 : Fin n → ℝ := fun i => ∫ ξ, ((1 + z) * ξ0 i ξ) ^ 2 * min |(1 + z) * ξ0 i ξ| 1 ∂P₀
  let K0 : ℝ := (∑ i : Fin n, δ0 i) + (∫ ξ, fullTest ξ ∂P₀) + ∑ i : Fin n, ∫ ξ, deletedTest ξ i ∂P₀
  let Fgt : Set (Fin n → Ω) := {ξ | y * d0 ξ < N0 ξ}
  let Fge : Set (Fin n → Ω) := {ξ | y * d0 ξ ≤ N0 ξ}
  have hcost := actual_compact_cost_admissibility
    μ h hh hh2 hhsymm hcenter hprojectionsecond n hn y hy
  rcases hcost with ⟨hgm, hg2, hgmean, hgsecond, hrm, hrsymm,
    hD1m, hAm, hBm, hAdm, hBdm, hAnonneg, hBnonneg, hAdnonneg, hBdnonneg,
    hFullI, hDeletedI, hL0Eq, hLnonneg, hKbound⟩
  change Measurable g at hgm
  change MemLp g 2 μ at hg2
  change (∫ o, g o ∂μ) = 0 at hgmean
  change (∫ o, g o ^ 2 ∂μ) = 1 at hgsecond
  change Measurable D1 at hD1m
  change Measurable A at hAm
  change Measurable B at hBm
  change (∀ i : Fin n, Measurable (Adeleted i)) at hAdm
  change (∀ i : Fin n, Measurable (Bdeleted i)) at hBdm
  change (∀ ξ : Fin n → Ω, 0 ≤ A ξ) at hAnonneg
  change (∀ ξ : Fin n → Ω, 0 ≤ B ξ) at hBnonneg
  change (∀ (i : Fin n) (η : {j : Fin n // j ≠ i} → Ω), 0 ≤ Adeleted i η) at hAdnonneg
  change (∀ (i : Fin n) (η : {j : Fin n // j ≠ i} → Ω), 0 ≤ Bdeleted i η) at hBdnonneg
  change Integrable fullTest P₀ at hFullI
  change (∀ i : Fin n, Integrable (fun ξ => deletedTest ξ i) P₀) at hDeletedI
  change K0 ≤ Lcompact + 16 * (1 + 4096) * (1 + y) * s / q at hKbound
  have hN3 : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hNpos : 0 < N := by linarith only [hN3]
  have hNne : N ≠ 0 := hNpos.ne'
  have hqpos : 0 < q := Real.sqrt_pos.mpr hNpos
  have hqsq : q ^ 2 = N := Real.sq_sqrt hNpos.le
  have hs1 : 1 ≤ s := by
    dsimp only [s]
    linarith only [Real.sqrt_nonneg v]
  have hCpos : 0 < C := lt_trans (by norm_num : (0 : ℝ) < 1) hSZC.1
  have hz : 0 ≤ z := hy
  have hO (i : Fin n) : Measurable (O i) := measurable_pi_apply i
  have hOindep : ProbabilityTheory.iIndepFun O P₀ := by
    simpa only [O] using
      (ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin n => μ)
        (X := fun _ (o : Ω) => o) (fun _ => measurable_id.aemeasurable))
  have hcoord (i : Fin n) : MeasurePreserving (fun ξ : Fin n → Ω => ξ i) P₀ μ :=
    measurePreserving_eval (μ := fun _ : Fin n => μ) i
  have hpull (i : Fin n) (f : Ω → ℝ) (hf : Measurable f) :
      (∫ ξ, f (ξ i) ∂P₀) = ∫ o, f o ∂μ := by
    calc
      _ = ∫ o, f o ∂P₀.map (fun ξ : Fin n → Ω => ξ i) :=
        (integral_map (hcoord i).measurable.aemeasurable hf.aestronglyMeasurable).symm
      _ = _ := by rw [(hcoord i).map_eq]
  have hg0m (i : Fin n) : Measurable (g0 i) := hgm.div_const q
  have hg0Lp (i : Fin n) : MemLp (fun ξ => g0 i (O i ξ)) 2 P₀ := by
    simpa only [g0, O, div_eq_mul_inv, Function.comp_def] using
      ((hg2.comp_measurePreserving (hcoord i)).mul_const q⁻¹)
  have hg0mean (i : Fin n) : (∫ ξ, g0 i (O i ξ) ∂P₀) = 0 := by
    change (∫ ξ, g (ξ i) / q ∂P₀) = 0
    rw [integral_div, hpull i g hgm, hgmean, zero_div]
  have hg0second (i : Fin n) : (∫ ξ, (g0 i (O i ξ)) ^ 2 ∂P₀) = 1 / N := by
    change (∫ ξ, (g (ξ i) / q) ^ 2 ∂P₀) = 1 / N
    simp_rw [div_pow]
    rw [integral_div, hpull i (fun o => g o ^ 2) (hgm.pow_const 2), hgsecond, hqsq]
  have hg0energy : (∑ i : Fin n, ∫ ξ, (g0 i (O i ξ)) ^ 2 ∂P₀) = 1 := by
    simp_rw [hg0second]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change N * (1 / N) = 1
    field_simp [hNne]
  have hξm (i : Fin n) : Measurable (ξ0 i) := (hgm.comp (hO i)).div_const q
  have hW0m : Measurable W0 := Finset.measurable_sum _ (fun i _ => hξm i)
  have hV0m : Measurable V0 :=
    (Finset.measurable_sum _ (fun i _ => (hξm i).pow_const 2)).sqrt
  have hJm : Measurable J := by
    dsimp [J, Shao.OQ6.FiniteRows.uncenteredSq, Shao.OQ6.FiniteRows.rowMean]
    fun_prop
  have hVm : Measurable Vsq := by
    dsimp only [Vsq]
    exact (Finset.measurable_sum _ (fun i _ =>
      (hgm.comp (measurable_pi_apply i)).pow_const 2)).div_const N
  have hWm : Measurable W := by
    dsimp only [W]
    exact (Finset.measurable_sum _ (fun i _ =>
      hgm.comp (measurable_pi_apply i))).div_const q
  have hGm : MeasurableSet G :=
    (measurableSet_le measurable_const hVm).inter
      (measurableSet_le (continuous_abs.measurable.comp hWm)
        (measurable_const.mul (measurable_const.add hVm.sqrt)))
  have hD2m : Measurable D2 :=
    Measurable.ite (measurableSet_lt measurable_const hVm)
      ((hJm.div hVm).sub_const 1) measurable_const
  have hD2cm : Measurable D2c :=
    Measurable.ite hGm (hD2m.max measurable_const) measurable_const
  have hb0m : Measurable b0 := (measurable_const.add hD2cm).sqrt
  have hN0m : Measurable N0 := hW0m.add hD1m
  have hd0m : Measurable d0 := hV0m.mul hb0m
  have hFgtm : MeasurableSet Fgt := measurableSet_lt (measurable_const.mul hd0m) hN0m
  have hFgem : MeasurableSet Fge := measurableSet_le (measurable_const.mul hd0m) hN0m
  have hKernel (ξ : Fin n → Ω) :
      (fun i j => g (ξ i) + g (ξ j) + e ξ i j) = (fun i j => h (ξ i) (ξ j)) := by
    funext i j
    dsimp only [e, r]
    ring
  have hEnergyPoint (ξ : Fin n → Ω) : (∑ i : Fin n, (ξ0 i ξ) ^ 2) = Vsq ξ := by
    dsimp only [ξ0, Vsq]
    simp only [div_pow, ← Finset.sum_div, hqsq]
  have hW0Eq (ξ : Fin n → Ω) : W0 ξ = W ξ := by
    dsimp only [W0, ξ0, W]
    rw [Finset.sum_div]
  have hEnvelope (ξ : Fin n → Ω) (hξ : ξ ∈ G) : |D2 ξ| ≤ B ξ := by
    have hVp : 0 < Vsq ξ := by linarith [hξ.1]
    have ht := Shao.OQ6.ActualRemainderEnvelope.actual_uncentered_remainder_envelope
      (fun i => g (ξ i)) (e ξ) (fun i j => hrsymm (ξ i) (ξ j)) hn
      1 (by norm_num) s hs1 (by simpa only [mul_one, N, q] using hscale)
    dsimp only at ht
    rw [hKernel ξ] at ht
    have hWbound : |(∑ i : Fin n, g (ξ i)) / Real.sqrt (n : ℝ)| ≤
        Real.sqrt (1 : ℝ) * Real.sqrt (Real.sqrt (n : ℝ)) *
          (4 + Real.sqrt ((∑ i : Fin n, g (ξ i) ^ 2) / (n : ℝ))) := by
      simpa only [Real.sqrt_one, one_mul, W, Vsq, N, q] using hξ.2
    rw [show D2 ξ = J ξ / Vsq ξ - 1 by exact if_pos hVp]
    simpa only [Real.sqrt_one, one_mul, mul_one, B, Λsq, ψ,
      Shao.OQ6.ResidualDeletion.rowSum, J, Vsq, N, q] using ht hξ.1 hWbound
  have hD2cBound (ξ : Fin n → Ω) : |D2c ξ| ≤ B ξ := by
    by_cases hξ : ξ ∈ G
    · rw [show D2c ξ = max (D2 ξ) (-(1 / 2 : ℝ)) by exact if_pos hξ]
      by_cases hd : -(1 / 2 : ℝ) ≤ D2 ξ
      · rw [max_eq_left hd]
        exact hEnvelope ξ hξ
      · have hd' : D2 ξ ≤ -(1 / 2 : ℝ) := (lt_of_not_ge hd).le
        rw [max_eq_right hd']
        norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        have hnegative : -(D2 ξ) ≤ |D2 ξ| := neg_le_abs _
        linarith [hEnvelope ξ hξ]
    · rw [show D2c ξ = 0 by exact if_neg hξ, abs_zero]
      exact hBnonneg ξ
  have hD2cPos (ξ : Fin n → Ω) : 0 < 1 + D2c ξ := by
    by_cases hξ : ξ ∈ G
    · have ht : -(1 / 2 : ℝ) ≤ max (D2 ξ) (-(1 / 2 : ℝ)) := le_max_right _ _
      rw [show D2c ξ = max (D2 ξ) (-(1 / 2 : ℝ)) by exact if_pos hξ]
      linarith
    · rw [show D2c ξ = 0 by exact if_neg hξ]
      norm_num
  have hCapEq (i : Fin n) (ξ : Fin n → Ω) :
      min |g0 i (O i ξ)| (1 + y)⁻¹ = cap ξ i := by
    simp only [g0, O, cap, z, abs_div, abs_of_pos hqpos, one_div]
  have hEngineDeleted (i : Fin n) : Integrable
      (fun ξ : Fin n → Ω =>
        min |g0 i (O i ξ)| (1 + y)⁻¹ *
          (|A (fun j => O j ξ) - Adeleted i (fun j => O j.1 ξ)| +
            y * |B (fun j => O j ξ) - Bdeleted i (fun j => O j.1 ξ)|)) P₀ := by
    simpa only [O, g0, cap, deletedTest, z,
      abs_div, abs_of_pos hqpos, one_div] using hDeletedI i
  have hEngineFull : Integrable
      (fun ξ : Fin n → Ω => A (fun i => O i ξ) + y * B (fun i => O i ξ)) P₀ := by
    simpa only [O, fullTest, z] using hFullI
  have hEngine := Shao.OQ6.CompactTailBounds.ambient_weighted_ae_compact_tail_bounds
    C hSZC P₀ n (by omega) O hO hOindep g0 hg0m hg0Lp hg0mean hg0energy
    D1 D2c A B Adeleted Bdeleted hD1m hD2cm hAm hBm hAdm hBdm
    (Filter.Eventually.of_forall hAnonneg)
    (Filter.Eventually.of_forall hBnonneg)
    (fun i => Filter.Eventually.of_forall (fun ξ => hAdnonneg i (fun j => ξ j.1)))
    (fun i => Filter.Eventually.of_forall (fun ξ => hBdnonneg i (fun j => ξ j.1)))
    (Filter.Eventually.of_forall (fun _ => le_refl _))
    (Filter.Eventually.of_forall hD2cBound)
    (Filter.Eventually.of_forall hD2cPos)
    κ0 measurable_const y hy hEngineFull hEngineDeleted
  dsimp only at hEngine
  have hTailGT : |P₀.real Fgt - (1 - Shao.OQ4.standardNormalCDF y)| ≤ C * K0 := by
    simpa only [Fgt, N0, d0, W0, V0, b0, K0, δ0, fullTest, deletedTest,
      cap, ξ0, g0, O, z, abs_div, abs_of_pos hqpos,
      one_div, mul_assoc] using hEngine.1
  have hTailGE : |P₀.real Fge - (1 - Shao.OQ4.standardNormalCDF y)| ≤ C * K0 := by
    simpa only [Fge, N0, d0, W0, V0, b0, K0, δ0, fullTest, deletedTest,
      cap, ξ0, g0, O, z, abs_div, abs_of_pos hqpos,
      one_div, mul_assoc] using hEngine.2.1
  have hCostPaid : C * K0 ≤ Ecost :=
    mul_le_mul_of_nonneg_left hKbound hCpos.le
  constructor
  · simpa only [Fgt, N0, d0, b0, V0, hEnergyPoint, hW0Eq, mul_assoc] using
      hTailGT.trans hCostPaid
  · simpa only [Fge, N0, d0, b0, V0, hEnergyPoint, hW0Eq, mul_assoc] using
      hTailGE.trans hCostPaid

private theorem actual_common_compact_localization
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond : (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (cg : ℝ)
    (hLow : ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n => μ)).real
          {ζ : Fin n → Ω | (∑ i : Fin n, (∫ y, h (ζ i) y ∂μ) ^ (2 : ℕ)) ≤ (n : ℝ) / 2} ≤
        Real.exp (-cg * (n : ℝ)))
    (n : ℕ) (hn : 3 ≤ n) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
    let s : ℝ := 1 + Real.sqrt v
    let N : ℝ := (n : ℝ)
    let q : ℝ := Real.sqrt N
    let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let U : (Fin n → Ω) → ℝ := fun ζ =>
      Shao.OQ6.FiniteRows.uStatistic (fun i j => h (ζ i) (ζ j))
    let J : (Fin n → Ω) → ℝ := fun ζ =>
      Shao.OQ6.FiniteRows.uncenteredSq (fun i j => h (ζ i) (ζ j))
    let R2 : (Fin n → Ω) → ℝ := fun ζ =>
      Shao.OQ6.FiniteRows.jackknifeSq (fun i j => h (ζ i) (ζ j))
    let T : (Fin n → Ω) → ℝ := fun ζ =>
      if 0 < R2 ζ then q * U ζ / Real.sqrt (R2 ζ) else 0
    let Tstar : (Fin n → Ω) → ℝ := fun ζ =>
      if 0 < J ζ then q * U ζ / (2 * Real.sqrt (J ζ)) else 0
    let Vsq : (Fin n → Ω) → ℝ := fun ζ => (∑ i : Fin n, g (ζ i) ^ 2) / N
    let W : (Fin n → Ω) → ℝ := fun ζ => (∑ i : Fin n, g (ζ i)) / q
    let D2 : (Fin n → Ω) → ℝ := fun ζ => if 0 < Vsq ζ then J ζ / Vsq ζ - 1 else 0
    let G : Set (Fin n → Ω) := {ζ | (1 / 2 : ℝ) ≤ Vsq ζ ∧
      |W ζ| ≤ Real.sqrt q * (4 + Real.sqrt (Vsq ζ))}
    let Hcpt : Set (Fin n → Ω) := {ζ | ζ ∈ G ∧ -(1 / 2 : ℝ) ≤ D2 ζ}
    let Z : Set (Fin n → Ω) := {ζ | R2 ζ = 0}
    let c_n : ℝ := 4 * (N - 1) / (N - 2) ^ 2
    let τ : ℝ → ℝ := fun x => x / Real.sqrt (1 + c_n * x ^ 2)
    Measurable U ∧ Measurable J ∧ Measurable R2 ∧ Measurable T ∧ Measurable Tstar ∧
      MeasurableSet G ∧ MeasurableSet Hcpt ∧ MeasurableSet Z ∧
      P₀.real Gᶜ ≤ Real.exp (-cg * N) + 1 / (16 * q) ∧
      P₀.real Hcptᶜ ≤ Real.exp (-cg * N) + ((1 / 16 : ℝ) + 16384 * s) / q ∧
      P₀.real Z ≤ Real.exp (-cg * N) + ((1 / 16 : ℝ) + 16720 * s) / q ∧
      (∀ ζ ∈ Hcpt, (1 / 2 : ℝ) ≤ Vsq ζ ∧
        (1 / 2 : ℝ) ≤ 1 + D2 ζ ∧ (1 / 4 : ℝ) ≤ J ζ) ∧
      (∀ x : ℝ, |P₀.real {ζ | T ζ ≤ x} - P₀.real {ζ | Tstar ζ ≤ τ x}| ≤ P₀.real Z) ∧
      (∀ x : ℝ, |P₀.real {ζ | T ζ < x} - P₀.real {ζ | Tstar ζ < τ x}| ≤ P₀.real Z)
:= by
  classical
  intro g r v s N q P₀ U J R2 T Tstar Vsq W D2 G Hcpt Z c_n τ
  have hdata := Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
    μ h hh hh2 hhsymm hcenter hprojectionsecond 3 (by omega) 0 (by norm_num) (by positivity)
  dsimp only at hdata
  rcases hdata with ⟨hgm, hg2, hgmean, hgsecond, _⟩
  change Measurable g at hgm
  change MemLp g 2 μ at hg2
  change (∫ o, g o ∂μ) = 0 at hgmean
  change (∫ o, g o ^ 2 ∂μ) = 1 at hgsecond
  obtain ⟨oldProjectionClock, _, hProjection⟩ :=
    Shao.OQ6.CompactGoodEvent.original_projection_compact_good_event
      μ g hgm hg2 hgmean hgsecond
  obtain ⟨oldLocalizationClock, _, hLocalization⟩ :=
    Shao.OQ6.CompactGoodEvent.actual_uncentered_compact_localization_events
      μ h hh hh2 hhsymm hcenter hprojectionsecond
  obtain ⟨oldPhysicalClock, _, hPhysical⟩ :=
    Shao.OQ6.PhysicalCompact.actual_physical_zero_probability_and_compact_transport
      μ h hh hh2 hhsymm hcenter hprojectionsecond
  have hN3 : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hNpos : 0 < N := by linarith only [hN3]
  have hqpos : 0 < q := Real.sqrt_pos.mpr hNpos
  have h147n := hPhysical n hn
  dsimp only at h147n
  rcases h147n with ⟨hUm, hJm, hRm, hT, hTm, _, hZm, _, _, _, _, _,
    hHZ, _, hClosedIdentity, hOpenIdentity, hClosedTailIdentity, hOpenTailIdentity,
    hClosedDiff, hOpenDiff, _, _⟩
  change Measurable U at hUm
  change Measurable J at hJm
  change Measurable R2 at hRm
  change Measurable T at hT
  change Measurable Tstar at hTm
  change MeasurableSet Z at hZm
  change P₀.real (Hcpt ∩ Z) ≤ 336 * s / q at hHZ
  change (∀ x : ℝ, |P₀.real {ξ | T ξ ≤ x} -
    P₀.real {ξ | Tstar ξ ≤ τ x}| ≤ P₀.real Z) at hClosedDiff
  change (∀ x : ℝ, |P₀.real {ξ | T ξ < x} -
    P₀.real {ξ | Tstar ξ < τ x}| ≤ P₀.real Z) at hOpenDiff
  have hloc := hLocalization n hn
  dsimp only at hloc
  rcases hloc with ⟨hGm, hHm, _, _, _, _, hDfail, _, hGood⟩
  change MeasurableSet G at hGm
  change MeasurableSet Hcpt at hHm
  change P₀.real {ξ | ξ ∈ G ∧ D2 ξ < -(1 / 2 : ℝ)} ≤ 16384 * s / q at hDfail
  change (∀ ξ ∈ Hcpt, (1 / 2 : ℝ) ≤ Vsq ξ ∧
    (1 / 2 : ℝ) ≤ 1 + D2 ξ ∧ (1 / 4 : ℝ) ≤ J ξ) at hGood
  have hproj := hProjection n (by omega)
  dsimp only at hproj
  rcases hproj with ⟨_, hWi, hWsecond, _, _⟩
  change Integrable (fun ξ => W ξ ^ 2) P₀ at hWi
  change (∫ ξ, W ξ ^ 2 ∂P₀) = 1 at hWsecond
  have hClosedLow := hLow n
  change P₀.real {ξ | (∑ i : Fin n, g (ξ i) ^ 2) ≤ N / 2} ≤
    Real.exp (-cg * N) at hClosedLow
  have hLowInclusion :
      {ξ : Fin n → Ω | Vsq ξ ≤ (1 / 2 : ℝ)} ⊆
        {ξ : Fin n → Ω | (∑ i : Fin n, g (ξ i) ^ 2) ≤ N / 2} := by
    intro ξ hξ
    change (∑ i : Fin n, g (ξ i) ^ 2) / N ≤ (1 / 2 : ℝ) at hξ
    have ht : (∑ i : Fin n, g (ξ i) ^ 2) ≤ (1 / 2 : ℝ) * N :=
      (div_le_iff₀ hNpos).mp hξ
    calc
      (∑ i : Fin n, g (ξ i) ^ 2) ≤ (1 / 2 : ℝ) * N := ht
      _ = N / 2 := by ring
  have hLowVsq : P₀.real {ξ | Vsq ξ ≤ (1 / 2 : ℝ)} ≤ Real.exp (-cg * N) :=
    (measureReal_mono hLowInclusion).trans hClosedLow
  have hWm : Measurable W := by
    dsimp only [W]
    exact (Finset.measurable_sum _ (fun i _ =>
      hgm.comp (measurable_pi_apply i))).div_const q
  let Abad : Set (Fin n → Ω) := {ξ | 16 * q < W ξ ^ 2}
  have hAbadm : MeasurableSet Abad := measurableSet_lt measurable_const (hWm.pow_const 2)
  have hmark : (16 * q) * P₀.real Abad ≤ 1 := by
    calc
      (16 * q) * P₀.real Abad = ∫ ξ, Abad.indicator (fun _ => 16 * q) ξ ∂P₀ := by
        rw [integral_indicator_const _ hAbadm, smul_eq_mul, mul_comm]
      _ ≤ ∫ ξ, W ξ ^ 2 ∂P₀ := by
        apply integral_mono ((integrable_const _).indicator hAbadm) hWi
        intro ξ
        by_cases hξ : ξ ∈ Abad
        · rw [Set.indicator_of_mem hξ]
          exact le_of_lt hξ
        · rw [Set.indicator_of_notMem hξ]
          exact sq_nonneg _
      _ = 1 := hWsecond
  have hAbadprob : P₀.real Abad ≤ 1 / (16 * q) :=
    (le_div_iff₀ (by positivity : 0 < 16 * q)).2
      (by simpa only [mul_comm] using hmark)
  have hGsub : Gᶜ ⊆ {ξ | Vsq ξ ≤ (1 / 2 : ℝ)} ∪ Abad := by
    intro ξ hξ
    by_cases hV : (1 / 2 : ℝ) ≤ Vsq ξ
    · right
      have hbad : ¬ |W ξ| ≤ Real.sqrt q * (4 + Real.sqrt (Vsq ξ)) := by
        intro hh'
        exact hξ ⟨hV, hh'⟩
      have hlarge : 4 * Real.sqrt q < |W ξ| := by
        have hbase : 4 * Real.sqrt q ≤ Real.sqrt q * (4 + Real.sqrt (Vsq ξ)) := by
          nlinarith only [mul_nonneg (Real.sqrt_nonneg q) (Real.sqrt_nonneg (Vsq ξ))]
        exact hbase.trans_lt (lt_of_not_ge hbad)
      change 16 * q < W ξ ^ 2
      have hmul : 0 < (|W ξ| - 4 * Real.sqrt q) * (|W ξ| + 4 * Real.sqrt q) :=
        mul_pos (by linarith only [hlarge])
          (by linarith only [hlarge, Real.sqrt_nonneg q])
      nlinarith only [hmul, sq_abs (W ξ), Real.sq_sqrt hqpos.le]
    · exact Or.inl (le_of_lt (lt_of_not_ge hV))
  have hGfail : P₀.real Gᶜ ≤ Real.exp (-cg * N) + 1 / (16 * q) := by
    calc
      P₀.real Gᶜ ≤ P₀.real ({ξ | Vsq ξ ≤ (1 / 2 : ℝ)} ∪ Abad) := measureReal_mono hGsub
      _ ≤ P₀.real {ξ | Vsq ξ ≤ (1 / 2 : ℝ)} + P₀.real Abad := measureReal_union_le _ _
      _ ≤ Real.exp (-cg * N) + 1 / (16 * q) := add_le_add hLowVsq hAbadprob
  have hHsub : Hcptᶜ ⊆ Gᶜ ∪ {ξ | ξ ∈ G ∧ D2 ξ < -(1 / 2 : ℝ)} := by
    intro ξ hξ
    by_cases hG : ξ ∈ G
    · exact Or.inr ⟨hG, lt_of_not_ge (fun hd => hξ ⟨hG, hd⟩)⟩
    · exact Or.inl hG
  have hHfail : P₀.real Hcptᶜ ≤
      Real.exp (-cg * N) + ((1 / 16 : ℝ) + 16384 * s) / q := by
    calc
      P₀.real Hcptᶜ ≤ P₀.real (Gᶜ ∪ {ξ | ξ ∈ G ∧ D2 ξ < -(1 / 2 : ℝ)}) :=
        measureReal_mono hHsub
      _ ≤ P₀.real Gᶜ + P₀.real {ξ | ξ ∈ G ∧ D2 ξ < -(1 / 2 : ℝ)} :=
        measureReal_union_le _ _
      _ ≤ (Real.exp (-cg * N) + 1 / (16 * q)) + 16384 * s / q :=
        add_le_add hGfail hDfail
      _ = Real.exp (-cg * N) + ((1 / 16 : ℝ) + 16384 * s) / q := by ring
  have hZsub : Z ⊆ Hcptᶜ ∪ (Hcpt ∩ Z) := by
    intro ξ hξ
    by_cases hH : ξ ∈ Hcpt
    · exact Or.inr ⟨hH, hξ⟩
    · exact Or.inl hH
  have hZfail : P₀.real Z ≤
      Real.exp (-cg * N) + ((1 / 16 : ℝ) + 16720 * s) / q := by
    calc
      P₀.real Z ≤ P₀.real (Hcptᶜ ∪ (Hcpt ∩ Z)) := measureReal_mono hZsub
      _ ≤ P₀.real Hcptᶜ + P₀.real (Hcpt ∩ Z) := measureReal_union_le _ _
      _ ≤ (Real.exp (-cg * N) + ((1 / 16 : ℝ) + 16384 * s) / q) + 336 * s / q :=
        add_le_add hHfail hHZ
      _ = Real.exp (-cg * N) + ((1 / 16 : ℝ) + 16720 * s) / q := by ring
  exact ⟨hUm, hJm, hRm, hT, hTm, hGm, hHm, hZm, hGfail, hHfail, hZfail,
    hGood, hClosedDiff, hOpenDiff⟩

private theorem actual_common_uncentered_compact_bounds
    (C : ℝ)
    (hSZC : Shao.OQ6.NormalizedIntegrableCDFAssembly.ScalarShaoZhouFiniteCostCDFInput.{u} C)
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond : (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (cg : ℝ)
    (hLow : ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n => μ)).real
          {ζ : Fin n → Ω | (∑ i : Fin n, (∫ y, h (ζ i) y ∂μ) ^ (2 : ℕ)) ≤ (n : ℝ) / 2} ≤
        Real.exp (-cg * (n : ℝ)))
    (n : ℕ) (hn : 3 ≤ n) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
    let s : ℝ := 1 + Real.sqrt v
    let N : ℝ := (n : ℝ)
    let q : ℝ := Real.sqrt N
    let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let U : (Fin n → Ω) → ℝ := fun ζ =>
      Shao.OQ6.FiniteRows.uStatistic (fun i j => h (ζ i) (ζ j))
    let J : (Fin n → Ω) → ℝ := fun ζ =>
      Shao.OQ6.FiniteRows.uncenteredSq (fun i j => h (ζ i) (ζ j))
    let Tstar : (Fin n → Ω) → ℝ := fun ζ =>
      if 0 < J ζ then q * U ζ / (2 * Real.sqrt (J ζ)) else 0
    Measurable Tstar ∧
      ∀ y : ℝ, 0 ≤ y →
        let Lcompact : ℝ := N * (∫ o, Shao.truncationF ((1 + y) * (g o / q)) ∂μ)
        let error : ℝ := C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) +
          Real.exp (-cg * N) + ((1 / 16 : ℝ) + 16384 * s) / q
        |P₀.real {ζ | Tstar ζ ≤ y} - Shao.OQ4.standardNormalCDF y| ≤ error ∧
        |P₀.real {ζ | Tstar ζ < y} - Shao.OQ4.standardNormalCDF y| ≤ error ∧
        |P₀.real {ζ | y < Tstar ζ} - (1 - Shao.OQ4.standardNormalCDF y)| ≤ error ∧
        |P₀.real {ζ | y ≤ Tstar ζ} - (1 - Shao.OQ4.standardNormalCDF y)| ≤ error
:= by
  classical
  intro g r v s N q P₀ U J Tstar
  let Vsq : (Fin n → Ω) → ℝ := fun ξ => (∑ i : Fin n, g (ξ i) ^ 2) / N
  let W : (Fin n → Ω) → ℝ := fun ξ => (∑ i : Fin n, g (ξ i)) / q
  let D2 : (Fin n → Ω) → ℝ := fun ξ => if 0 < Vsq ξ then J ξ / Vsq ξ - 1 else 0
  let G : Set (Fin n → Ω) := {ξ | (1 / 2 : ℝ) ≤ Vsq ξ ∧
    |W ξ| ≤ Real.sqrt q * (4 + Real.sqrt (Vsq ξ))}
  let Hcpt : Set (Fin n → Ω) := {ξ | ξ ∈ G ∧ -(1 / 2 : ℝ) ≤ D2 ξ}
  have hloc := actual_common_compact_localization
    μ h hh hh2 hhsymm hcenter hprojectionsecond cg hLow n hn
  rcases hloc with ⟨_, hJm, _, _, hTm, hGm, hHm, _, _, hHfail, _, hGood, _, _⟩
  change Measurable J at hJm
  change Measurable Tstar at hTm
  change MeasurableSet G at hGm
  change MeasurableSet Hcpt at hHm
  change P₀.real Hcptᶜ ≤ Real.exp (-cg * N) + ((1 / 16 : ℝ) + 16384 * s) / q at hHfail
  change (∀ ξ ∈ Hcpt, (1 / 2 : ℝ) ≤ Vsq ξ ∧
    (1 / 2 : ℝ) ≤ 1 + D2 ξ ∧ (1 / 4 : ℝ) ≤ J ξ) at hGood
  have hN3 : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hNpos : 0 < N := by linarith only [hN3]
  have hqpos : 0 < q := Real.sqrt_pos.mpr hNpos
  have hs1 : 1 ≤ s := by
    dsimp only [s]
    linarith only [Real.sqrt_nonneg v]
  refine ⟨hTm, ?_⟩
  intro y hy Lcompact error
  by_cases hscale : s ≤ q
  ·
    let e : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ j k => r (ξ j) (ξ k)
    let D1 : (Fin n → Ω) → ℝ := fun ξ =>
      Shao.OQ5.P35.unorderedPairSum (e ξ) / (q * (N - 1))
    let D2c : (Fin n → Ω) → ℝ := fun ξ =>
      if ξ ∈ G then max (D2 ξ) (-(1 / 2 : ℝ)) else 0
    let N0 : (Fin n → Ω) → ℝ := fun ξ => W ξ + D1 ξ
    let d0 : (Fin n → Ω) → ℝ := fun ξ => Real.sqrt (Vsq ξ) * Real.sqrt (1 + D2c ξ)
    let Fle : Set (Fin n → Ω) := {ξ | N0 ξ ≤ y * d0 ξ}
    let Flt : Set (Fin n → Ω) := {ξ | N0 ξ < y * d0 ξ}
    let Fgt : Set (Fin n → Ω) := {ξ | y * d0 ξ < N0 ξ}
    let Fge : Set (Fin n → Ω) := {ξ | y * d0 ξ ≤ N0 ξ}
    let Ecost : ℝ := C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q)
    have hthreshold := actual_compact_numerator_threshold_bounds
      C hSZC μ h hh hh2 hhsymm hcenter hprojectionsecond n hn y hy
    have hTailPair :
        |P₀.real Fgt - (1 - Shao.OQ4.standardNormalCDF y)| ≤ Ecost ∧
        |P₀.real Fge - (1 - Shao.OQ4.standardNormalCDF y)| ≤ Ecost := by
      simpa only [Fgt, Fge, N0, d0, Ecost, mul_assoc] using hthreshold hscale
    rcases hTailPair with ⟨hTailGT, hTailGE⟩
    have hdata := Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
      μ h hh hh2 hhsymm hcenter hprojectionsecond 3 (by omega) 0 (by norm_num) (by positivity)
    rcases hdata with ⟨hgm, _, _⟩
    change Measurable g at hgm
    have hVm : Measurable Vsq := by
      dsimp only [Vsq]
      exact (Finset.measurable_sum _ (fun i _ =>
        (hgm.comp (measurable_pi_apply i)).pow_const 2)).div_const N
    have hWm : Measurable W := by
      dsimp only [W]
      exact (Finset.measurable_sum _ (fun i _ =>
        hgm.comp (measurable_pi_apply i))).div_const q
    have hD1m : Measurable D1 := by
      dsimp [D1, e, r, Shao.OQ5.P35.unorderedPairSum]
      fun_prop
    have hD2m : Measurable D2 :=
      Measurable.ite (measurableSet_lt measurable_const hVm)
        ((hJm.div hVm).sub_const 1) measurable_const
    have hD2cm : Measurable D2c :=
      Measurable.ite hGm (hD2m.max measurable_const) measurable_const
    have hN0m : Measurable N0 := hWm.add hD1m
    have hd0m : Measurable d0 := hVm.sqrt.mul (measurable_const.add hD2cm).sqrt
    have hFlem : MeasurableSet Fle := measurableSet_le hN0m (measurable_const.mul hd0m)
    have hFltm : MeasurableSet Flt := measurableSet_lt hN0m (measurable_const.mul hd0m)
    have hFgtm : MeasurableSet Fgt := measurableSet_lt (measurable_const.mul hd0m) hN0m
    have hFgem : MeasurableSet Fge := measurableSet_le (measurable_const.mul hd0m) hN0m
    have hKernel (ξ : Fin n → Ω) :
        (fun i j => g (ξ i) + g (ξ j) + e ξ i j) = (fun i j => h (ξ i) (ξ j)) := by
      funext i j
      dsimp only [e, r]
      ring
    have hNumerator (ξ : Fin n → Ω) : N0 ξ = q * U ξ / 2 := by
      have ht := finite_projection_residual_numerator (fun i => g (ξ i)) (e ξ) hn
      rw [hKernel ξ] at ht
      simpa only [N0, W, D1, U, N, q] using ht
    have hComplementError (E : Set (Fin n → Ω)) (hE : MeasurableSet E) (a : ℝ) :
        |P₀.real Eᶜ - (1 - a)| = |P₀.real E - a| := by
      have he : P₀.real Eᶜ = 1 - P₀.real E := by
        simpa only [probReal_univ] using measureReal_compl (μ := P₀) hE
      rw [he, show (1 - P₀.real E) - (1 - a) = -(P₀.real E - a) by ring, abs_neg]
    have hFleComp : Fle = Fgtᶜ := by
      ext ξ
      simp only [Fle, Fgt, Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
    have hFltComp : Flt = Fgeᶜ := by
      ext ξ
      simp only [Flt, Fge, Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    have hCDFLE : |P₀.real Fle - Shao.OQ4.standardNormalCDF y| ≤ Ecost := by
      have ht := hComplementError Fgt hFgtm (1 - Shao.OQ4.standardNormalCDF y)
      rw [show 1 - (1 - Shao.OQ4.standardNormalCDF y) =
        Shao.OQ4.standardNormalCDF y by ring, ← hFleComp] at ht
      rw [ht]
      exact hTailGT
    have hCDFLT : |P₀.real Flt - Shao.OQ4.standardNormalCDF y| ≤ Ecost := by
      have ht := hComplementError Fge hFgem (1 - Shao.OQ4.standardNormalCDF y)
      rw [show 1 - (1 - Shao.OQ4.standardNormalCDF y) =
        Shao.OQ4.standardNormalCDF y by ring, ← hFltComp] at ht
      rw [ht]
      exact hTailGE
    have hAgree (ξ : Fin n → Ω) (hξ : ξ ∈ Hcpt) :
        (Tstar ξ ≤ y ↔ ξ ∈ Fle) ∧ (Tstar ξ < y ↔ ξ ∈ Flt) ∧
        (y < Tstar ξ ↔ ξ ∈ Fgt) ∧ (y ≤ Tstar ξ ↔ ξ ∈ Fge) := by
      have hgood := hGood ξ hξ
      have hVp : 0 < Vsq ξ := by linarith only [hgood.1]
      have hJp : 0 < J ξ := by linarith only [hgood.2.2]
      have hclip : D2c ξ = D2 ξ := by
        rw [show D2c ξ = max (D2 ξ) (-(1 / 2 : ℝ)) by exact if_pos hξ.1,
          max_eq_left hξ.2]
      have hprod : Vsq ξ * (1 + D2c ξ) = J ξ := by
        rw [hclip, show D2 ξ = J ξ / Vsq ξ - 1 by exact if_pos hVp]
        field_simp [hVp.ne']
        <;> ring
      have hden : d0 ξ = Real.sqrt (J ξ) := by
        calc
          d0 ξ = Real.sqrt (Vsq ξ * (1 + D2c ξ)) := (Real.sqrt_mul hVp.le _).symm
          _ = Real.sqrt (J ξ) := by rw [hprod]
      have hdp : 0 < d0 ξ := by rw [hden]; exact Real.sqrt_pos.mpr hJp
      have hquot : Tstar ξ = N0 ξ / d0 ξ := by
        rw [show Tstar ξ = q * U ξ / (2 * Real.sqrt (J ξ)) by exact if_pos hJp,
          hNumerator ξ, hden, div_div]
      rw [hquot]
      exact ⟨(div_le_iff₀ hdp), (div_lt_iff₀ hdp),
        (lt_div_iff₀ hdp), (le_div_iff₀ hdp)⟩
    have hCompare (E Fset : Set (Fin n → Ω)) (hE : MeasurableSet E)
        (hF : MeasurableSet Fset)
        (hEF : ∀ ξ ∈ Hcpt, ξ ∈ E ↔ ξ ∈ Fset) :
        |P₀.real E - P₀.real Fset| ≤ P₀.real Hcptᶜ := by
      have hsub : ((E \ Fset) ∪ (Fset \ E)) ⊆ Hcptᶜ := by
        intro ξ hξ
        change ξ ∉ Hcpt
        intro hH
        have ht := hEF ξ hH
        rcases Set.mem_symmDiff.mp hξ with ⟨he, hf⟩ | ⟨hf, he⟩
        · exact hf (ht.mp he)
        · exact he (ht.mpr hf)
      exact (abs_measureReal_sub_le_measureReal_symmDiff
        hE.nullMeasurableSet hF.nullMeasurableSet).trans (measureReal_mono hsub)
    have hPaid (E Fset : Set (Fin n → Ω)) (hE : MeasurableSet E)
        (hF : MeasurableSet Fset)
        (hEF : ∀ ξ ∈ Hcpt, ξ ∈ E ↔ ξ ∈ Fset)
        (a : ℝ) (hGaussian : |P₀.real Fset - a| ≤ Ecost) :
        |P₀.real E - a| ≤ error := by
      have hDiff := hCompare E Fset hE hF hEF
      calc
        |P₀.real E - a| ≤ |P₀.real E - P₀.real Fset| + |P₀.real Fset - a| :=
          abs_sub_le _ _ _
        _ ≤ P₀.real Hcptᶜ + Ecost := add_le_add hDiff hGaussian
        _ ≤ error := by dsimp only [error, Ecost]; linarith only [hHfail]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hPaid _ Fle (measurableSet_le hTm measurable_const) hFlem
        (fun ξ hξ => (hAgree ξ hξ).1) _ hCDFLE
    · exact hPaid _ Flt (measurableSet_lt hTm measurable_const) hFltm
        (fun ξ hξ => (hAgree ξ hξ).2.1) _ hCDFLT
    · exact hPaid _ Fgt (measurableSet_lt measurable_const hTm) hFgtm
        (fun ξ hξ => (hAgree ξ hξ).2.2.1) _ hTailGT
    · exact hPaid _ Fge (measurableSet_le measurable_const hTm) hFgem
        (fun ξ hξ => (hAgree ξ hξ).2.2.2) _ hTailGE
  · have hslarge : q ≤ s := (lt_of_not_ge hscale).le
    have hratio : 1 ≤ s / q := by
      apply (le_div_iff₀ hqpos).2
      simpa only [one_mul] using hslarge
    have hLnonneg : 0 ≤ Lcompact :=
      mul_nonneg hNpos.le (integral_nonneg (fun o => Shao.truncationF_nonneg _))
    have hcoeff : (1 : ℝ) ≤ 16 * (1 + 4096) * (1 + y) := by linarith only [hy]
    have hRate : 1 ≤ Lcompact + 16 * (1 + 4096) * (1 + y) * s / q := by
      have ht := mul_le_mul_of_nonneg_right hcoeff
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) hratio)
      have he : 16 * (1 + 4096) * (1 + y) * (s / q) =
          16 * (1 + 4096) * (1 + y) * s / q := by ring
      rw [he] at ht
      linarith only [hLnonneg, hratio, ht]
    have hRate0 : 0 ≤ Lcompact + 16 * (1 + 4096) * (1 + y) * s / q :=
      le_trans (by norm_num) hRate
    have hCRate := mul_le_mul_of_nonneg_right hSZC.1.le hRate0
    have hBad0 : 0 ≤ ((1 / 16 : ℝ) + 16384 * s) / q := by positivity
    have hErrorOne : 1 ≤ error := by
      dsimp only [error]
      linarith only [hRate, hCRate, Real.exp_pos (-cg * N), hBad0]
    have hPhi0 : 0 ≤ Shao.OQ4.standardNormalCDF y := by
      rw [Shao.OQ4.standardNormalCDF_eq_real]
      exact measureReal_nonneg
    have hPhi1 : Shao.OQ4.standardNormalCDF y ≤ 1 := by
      rw [Shao.OQ4.standardNormalCDF_eq_real]
      exact measureReal_le_one
    have hUnit (E : Set (Fin n → Ω)) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
        |P₀.real E - a| ≤ error := by
      have hp0 : 0 ≤ P₀.real E := measureReal_nonneg
      have hp1 : P₀.real E ≤ 1 := measureReal_le_one
      apply le_trans _ hErrorOne
      apply abs_le.mpr
      constructor <;> linarith
    exact ⟨hUnit _ _ hPhi0 hPhi1, hUnit _ _ hPhi0 hPhi1,
      hUnit _ _ (by linarith) (by linarith), hUnit _ _ (by linarith) (by linarith)⟩

private theorem actual_common_physical_compact_raw_bounds
    (C : ℝ)
    (hSZC : Shao.OQ6.NormalizedIntegrableCDFAssembly.ScalarShaoZhouFiniteCostCDFInput.{u} C)
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond : (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (cg : ℝ)
    (hLow : ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n => μ)).real
          {ζ : Fin n → Ω | (∑ i : Fin n, (∫ y, h (ζ i) y ∂μ) ^ (2 : ℕ)) ≤ (n : ℝ) / 2} ≤
        Real.exp (-cg * (n : ℝ)))
    (n : ℕ) (hn : 3 ≤ n) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
    let s : ℝ := 1 + Real.sqrt v
    let N : ℝ := (n : ℝ)
    let q : ℝ := Real.sqrt N
    let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let U : (Fin n → Ω) → ℝ := fun ζ =>
      Shao.OQ6.FiniteRows.uStatistic (fun i j => h (ζ i) (ζ j))
    let R2 : (Fin n → Ω) → ℝ := fun ζ =>
      Shao.OQ6.FiniteRows.jackknifeSq (fun i j => h (ζ i) (ζ j))
    let T : (Fin n → Ω) → ℝ := fun ζ =>
      if 0 < R2 ζ then q * U ζ / Real.sqrt (R2 ζ) else 0
    let c_n : ℝ := 4 * (N - 1) / (N - 2) ^ 2
    let τ : ℝ → ℝ := fun x => x / Real.sqrt (1 + c_n * x ^ 2)
    Measurable T ∧
      ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
        let y : ℝ := τ x
        let Lcompact : ℝ := N * (∫ o, Shao.truncationF ((1 + y) * (g o / q)) ∂μ)
        let error : ℝ := C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) +
          2 * Real.exp (-cg * N) + ((1 / 8 : ℝ) + 33104 * s) / q + 12 / N
        |P₀.real {ζ | T ζ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
        |P₀.real {ζ | T ζ < x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
        |P₀.real {ζ | x < T ζ} - (1 - Shao.OQ4.standardNormalCDF x)| ≤ error ∧
        |P₀.real {ζ | x ≤ T ζ} - (1 - Shao.OQ4.standardNormalCDF x)| ≤ error
:= by
  classical
  intro g r v s N q P₀ U R2 T c_n τ
  let J : (Fin n → Ω) → ℝ := fun ξ =>
    Shao.OQ6.FiniteRows.uncenteredSq (fun i j => h (ξ i) (ξ j))
  let Tstar : (Fin n → Ω) → ℝ := fun ξ =>
    if 0 < J ξ then q * U ξ / (2 * Real.sqrt (J ξ)) else 0
  let Z : Set (Fin n → Ω) := {ξ | R2 ξ = 0}
  have hloc := actual_common_compact_localization
    μ h hh hh2 hhsymm hcenter hprojectionsecond cg hLow n hn
  rcases hloc with ⟨_, _, _, hT, hTm, _, _, _, _, _, hZfail, _, hClosedDiff, hOpenDiff⟩
  change Measurable T at hT
  change Measurable Tstar at hTm
  change P₀.real Z ≤ Real.exp (-cg * N) + ((1 / 16 : ℝ) + 16720 * s) / q at hZfail
  change (∀ x : ℝ, |P₀.real {ξ | T ξ ≤ x} -
    P₀.real {ξ | Tstar ξ ≤ τ x}| ≤ P₀.real Z) at hClosedDiff
  change (∀ x : ℝ, |P₀.real {ξ | T ξ < x} -
    P₀.real {ξ | Tstar ξ < τ x}| ≤ P₀.real Z) at hOpenDiff
  have huncentered := actual_common_uncentered_compact_bounds
    C hSZC μ h hh hh2 hhsymm hcenter hprojectionsecond cg hLow n hn
  rcases huncentered with ⟨_, h169bound⟩
  refine ⟨hT, ?_⟩
  intro x hx hx1
  intro y Lcompact error
  have hfinite := Shao.OQ6.PhysicalCompact.finite_physical_studentizer_conversion
    (fun _ _ : Fin n => (0 : ℝ)) (by intro i j; rfl) hn
  dsimp only at hfinite
  rcases hfinite with ⟨_, _, _, _, _, _, hτrange, hPhiMove⟩
  change (∀ x : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ τ x ∧ τ x ≤ 1) at hτrange
  change (∀ x : ℝ, |x| ≤ 1 →
    |Shao.OQ4.standardNormalCDF (τ x) - Shao.OQ4.standardNormalCDF x| ≤ 12 / N) at hPhiMove
  have hy : 0 ≤ y := (hτrange x hx hx1).1
  have hxabs : |x| ≤ 1 := by simpa only [abs_of_nonneg hx] using hx1
  have h169y := h169bound y hy
  dsimp only at h169y
  rcases h169y with ⟨hClosed169, hOpen169, _, _⟩
  change |P₀.real {ξ | Tstar ξ ≤ y} - Shao.OQ4.standardNormalCDF y| ≤
    C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) +
      Real.exp (-cg * N) + ((1 / 16 : ℝ) + 16384 * s) / q at hClosed169
  change |P₀.real {ξ | Tstar ξ < y} - Shao.OQ4.standardNormalCDF y| ≤
    C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) +
      Real.exp (-cg * N) + ((1 / 16 : ℝ) + 16384 * s) / q at hOpen169
  have hMove : |Shao.OQ4.standardNormalCDF y - Shao.OQ4.standardNormalCDF x| ≤ 12 / N :=
    hPhiMove x hxabs
  have hclosed : |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤ error := by
    calc
      |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤
          |P₀.real {ξ | T ξ ≤ x} - P₀.real {ξ | Tstar ξ ≤ y}| +
            |P₀.real {ξ | Tstar ξ ≤ y} - Shao.OQ4.standardNormalCDF x| := abs_sub_le _ _ _
      _ ≤ |P₀.real {ξ | T ξ ≤ x} - P₀.real {ξ | Tstar ξ ≤ y}| +
          (|P₀.real {ξ | Tstar ξ ≤ y} - Shao.OQ4.standardNormalCDF y| +
            |Shao.OQ4.standardNormalCDF y - Shao.OQ4.standardNormalCDF x|) :=
        add_le_add (le_refl _) (abs_sub_le _ _ _)
      _ ≤ (Real.exp (-cg * N) + ((1 / 16 : ℝ) + 16720 * s) / q) +
          ((C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) +
            Real.exp (-cg * N) + ((1 / 16 : ℝ) + 16384 * s) / q) + 12 / N) :=
        add_le_add ((hClosedDiff x).trans hZfail) (add_le_add hClosed169 hMove)
      _ = error := by dsimp only [error]; ring
  have hopen : |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤ error := by
    calc
      |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤
          |P₀.real {ξ | T ξ < x} - P₀.real {ξ | Tstar ξ < y}| +
            |P₀.real {ξ | Tstar ξ < y} - Shao.OQ4.standardNormalCDF x| := abs_sub_le _ _ _
      _ ≤ |P₀.real {ξ | T ξ < x} - P₀.real {ξ | Tstar ξ < y}| +
          (|P₀.real {ξ | Tstar ξ < y} - Shao.OQ4.standardNormalCDF y| +
            |Shao.OQ4.standardNormalCDF y - Shao.OQ4.standardNormalCDF x|) :=
        add_le_add (le_refl _) (abs_sub_le _ _ _)
      _ ≤ (Real.exp (-cg * N) + ((1 / 16 : ℝ) + 16720 * s) / q) +
          ((C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) +
            Real.exp (-cg * N) + ((1 / 16 : ℝ) + 16384 * s) / q) + 12 / N) :=
        add_le_add ((hOpenDiff x).trans hZfail) (add_le_add hOpen169 hMove)
      _ = error := by dsimp only [error]; ring
  have hComplementError (E : Set (Fin n → Ω)) (hE : MeasurableSet E) (a : ℝ) :
      |P₀.real Eᶜ - (1 - a)| = |P₀.real E - a| := by
    have he : P₀.real Eᶜ = 1 - P₀.real E := by
      simpa only [probReal_univ] using measureReal_compl (μ := P₀) hE
    rw [he, show (1 - P₀.real E) - (1 - a) = -(P₀.real E - a) by ring, abs_neg]
  refine ⟨hclosed, hopen, ?_, ?_⟩
  · have he : {ξ | x < T ξ} = {ξ | T ξ ≤ x}ᶜ := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    rw [he, hComplementError _ (measurableSet_le hT measurable_const)
      (Shao.OQ4.standardNormalCDF x)]
    exact hclosed
  · have he : {ξ | x ≤ T ξ} = {ξ | T ξ < x}ᶜ := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
    rw [he, hComplementError _ (measurableSet_lt hT measurable_const)
      (Shao.OQ4.standardNormalCDF x)]
    exact hopen

private theorem countably_generated_uniform_compact_rate
    (C : ℝ)
    (hSZC : Shao.OQ6.NormalizedIntegrableCDFAssembly.ScalarShaoZhouFiniteCostCDFInput.{u} C)
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (B : ℝ) (hB : 1 ≤ B) :
    let tB : ℝ := Real.rpow (1 / (4 * B)) (2 / (p - 2))
    let cg : ℝ := tB / 4
    let K : ℝ := 131112 * C + 33117 + 2 / cg
    0 < cg ∧ 0 < K ∧
        ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω]
          [MeasurableSpace.CountablyGenerated Ω]
          (μ : Measure Ω) [IsProbabilityMeasure μ]
          (h : Ω → Ω → ℝ)
          (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
          (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
          (hhsymm : ∀ o y, h o y = h y o)
          (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
          (hprojectionsecond :
            (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
          (hgp : Integrable (fun o => Real.rpow |∫ y, h o y ∂μ| p) μ)
          (hβBound : (∫ o, Real.rpow |∫ y, h o y ∂μ| p ∂μ) ≤ B),
          let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
          let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
          let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
          let s : ℝ := 1 + Real.sqrt v
          let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
          ∀ (n : ℕ), 3 ≤ n →
            let N : ℝ := (n : ℝ)
            let q : ℝ := Real.sqrt N
            let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
            let U : (Fin n → Ω) → ℝ := fun ξ =>
              Shao.OQ6.FiniteRows.uStatistic (fun i j => h (ξ i) (ξ j))
            let R2 : (Fin n → Ω) → ℝ := fun ξ =>
              Shao.OQ6.FiniteRows.jackknifeSq (fun i j => h (ξ i) (ξ j))
            let T : (Fin n → Ω) → ℝ := fun ξ =>
              if 0 < R2 ξ then q * U ξ / Real.sqrt (R2 ξ) else 0
            Measurable T ∧
              P₀.real {ξ | (∑ i : Fin n, g (ξ i) ^ (2 : ℕ)) ≤ N / 2} ≤
                Real.exp (-cg * N) ∧
              ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
                let error : ℝ := K *
                  (β / Real.rpow N ((p - 2) / 2) + s / q)
                |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
                |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
                |P₀.real {ξ | x < T ξ} -
                  (1 - Shao.OQ4.standardNormalCDF x)| ≤ error ∧
                |P₀.real {ξ | x ≤ T ξ} -
                  (1 - Shao.OQ4.standardNormalCDF x)| ≤ error
:= by
  classical
  intro tB cg K
  have hClockData : 0 < cg ∧
      ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
        (hgsecond : (∫ o, g o ^ 2 ∂μ) = 1)
        (hgp : Integrable (fun o => Real.rpow |g o| p) μ)
        (hβBound : (∫ o, Real.rpow |g o| p ∂μ) ≤ B),
        ∀ n : ℕ, (Measure.pi (fun _ : Fin n => μ)).real
          {ξ : Fin n → Ω | (∑ i : Fin n, g (ξ i) ^ (2 : ℕ)) ≤ (n : ℝ) / 2} ≤
            Real.exp (-cg * (n : ℝ)) := by
    have hUniform := Shao.OQ6.UniformPMomentLowEnergy.actual_uniform_pmoment_low_energy.{u}
      p hp2 hp3 B hB
    dsimp only at hUniform
    rcases hUniform with ⟨_, _, _, _, hcg, _, hLow⟩
    change 0 < cg at hcg
    refine ⟨hcg, ?_⟩
    intro Ω mΩ μ hμ g hg hg2 hgsecond hgp hβBound n
    have hLowModel := hLow μ g hg hg2 hgsecond hgp hβBound
    have hLowN := hLowModel.2.2.2.2.2 n
    exact hLowN.2.2.2.2.2.2.2
  rcases hClockData with ⟨hcg, hLowActual⟩
  have hC : 0 < C := lt_trans (by norm_num : (0 : ℝ) < 1) hSZC.1
  have hdivc : 0 ≤ 2 / cg := div_nonneg (by norm_num) hcg.le
  have hK : 0 < K := by
    dsimp only [K]
    nlinarith only [hC, hdivc]
  have hKA : 8 * C ≤ K := by
    dsimp only [K]
    nlinarith only [hC, hdivc]
  have hKB : 131104 * C + 33117 + 2 / cg ≤ K := by
    dsimp only [K]
    nlinarith only [hC]
  refine ⟨hcg, hK, ?_⟩
  intro Ω mΩ hcgΩ μ hμ h hh hh2 hhsymm hcenter hprojectionsecond hgp hβBound g r v s β
  have hdata := Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
    μ h hh hh2 hhsymm hcenter hprojectionsecond 3 (by omega) 0 (by norm_num) (by positivity)
  dsimp only at hdata
  rcases hdata with ⟨hgm, hg2, _, hgsecond, _, _, _, _, _, hs1, _, _⟩
  change Measurable g at hgm
  change MemLp g 2 μ at hg2
  change (∫ o, g o ^ 2 ∂μ) = 1 at hgsecond
  change 1 ≤ s at hs1
  change Integrable (fun o => Real.rpow |g o| p) μ at hgp
  change (∫ o, Real.rpow |g o| p ∂μ) ≤ B at hβBound
  have hβ : 0 ≤ β := integral_nonneg (fun o => Real.rpow_nonneg (abs_nonneg (g o)) p)
  have hLowModel : ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n => μ)).real
        {ξ : Fin n → Ω | (∑ i : Fin n, g (ξ i) ^ (2 : ℕ)) ≤ (n : ℝ) / 2} ≤
          Real.exp (-cg * (n : ℝ)) :=
    hLowActual μ g hgm hg2 hgsecond hgp hβBound
  intro n hn N q P₀ U R2 T
  let c_n : ℝ := 4 * (N - 1) / (N - 2) ^ 2
  let τ : ℝ → ℝ := fun x => x / Real.sqrt (1 + c_n * x ^ 2)
  have hRawData := actual_common_physical_compact_raw_bounds
    C hSZC μ h hh hh2 hhsymm hcenter hprojectionsecond cg hLowModel n hn
  rcases hRawData with ⟨hT, hRaw⟩
  change Measurable T at hT
  have hN3 : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hNpos : 0 < N := by linarith only [hN3]
  have hqpos : 0 < q := Real.sqrt_pos.mpr hNpos
  have hqsq : q ^ 2 = N := Real.sq_sqrt hNpos.le
  have hq : 0 < q := hqpos
  have hN : 0 < N := hNpos
  have hs : 1 ≤ s := hs1
  have hc : 0 < cg := hcg
  let H0 : Fin n → Fin n → ℝ := fun _ _ => 0
  have hq1 : 1 ≤ q := by
    by_contra hnot
    have hlt : q < 1 := lt_of_not_ge hnot
    have hprod := mul_pos (sub_pos.mpr hlt) (by linarith only [hq] : 0 < 1 + q)
    nlinarith only [hprod, hqsq, hN3]
  have hqN : q ≤ N := by
    have hprod := mul_nonneg hq.le (sub_nonneg.mpr hq1)
    nlinarith only [hprod, hqsq]
  have hden : 0 < Real.rpow N ((p - 2) / 2) := Real.rpow_pos_of_pos hN _
  have hβden : 0 ≤ β / Real.rpow N ((p - 2) / 2) :=
    div_nonneg hβ hden.le
  have hs0 : 0 ≤ s := by linarith only [hs]
  have hsq : 0 ≤ s / q := div_nonneg hs0 hq.le
  have hunit : 1 / q ≤ s / q := div_le_div_of_nonneg_right hs hq.le
  have hNrecip : 1 / N ≤ 1 / q :=
    (div_le_div_iff₀ hN hq).2 (by simpa only [one_mul] using hqN)
  have hexpden : cg * q ≤ Real.exp (cg * N) := by
    have hprod := mul_le_mul_of_nonneg_left hqN hc.le
    have hexp := Real.add_one_le_exp (cg * N)
    linarith only [hprod, hexp]
  have hexpbase : Real.exp (-cg * N) ≤ 1 / (cg * q) := by
    calc
      Real.exp (-cg * N) = 1 / Real.exp (cg * N) := by
        rw [show -cg * N = -(cg * N) by ring, Real.exp_neg, one_div]
      _ ≤ 1 / (cg * q) :=
        (div_le_div_iff₀ (Real.exp_pos _) (mul_pos hc hq)).2
          (by simpa only [one_mul] using hexpden)
  have hexpunit : 1 / (cg * q) ≤ (1 / cg) * (s / q) := by
    have hmul := mul_le_mul_of_nonneg_left hunit
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hc.le)
    convert hmul using 1 <;> field_simp [hc.ne', hq.ne'] <;> ring
  have hexp : 2 * Real.exp (-cg * N) ≤ (2 / cg) * (s / q) := by
    calc
      2 * Real.exp (-cg * N) ≤ 2 * ((1 / cg) * (s / q)) :=
        mul_le_mul_of_nonneg_left (hexpbase.trans hexpunit) (by norm_num)
      _ = (2 / cg) * (s / q) := by ring
  have h12 : 12 / N ≤ 12 * (s / q) := by
    calc
      12 / N = 12 * (1 / N) := by ring
      _ ≤ 12 * (s / q) :=
        mul_le_mul_of_nonneg_left (hNrecip.trans hunit) (by norm_num)
  have h18 : (1 / 8 : ℝ) / q ≤ (1 / 8 : ℝ) * (s / q) := by
    have hmul := mul_le_mul_of_nonneg_left hunit
      (by norm_num : (0 : ℝ) ≤ 1 / 8)
    convert hmul using 1 <;> ring
  have hpoly : ((1 / 8 : ℝ) + 33104 * s) / q + 12 / N ≤
      33117 * (s / q) := by
    calc
      ((1 / 8 : ℝ) + 33104 * s) / q + 12 / N =
          (1 / 8 : ℝ) / q + 33104 * (s / q) + 12 / N := by ring
      _ ≤ (1 / 8 : ℝ) * (s / q) + 33104 * (s / q) + 12 * (s / q) := by
        linarith only [h12, h18]
      _ ≤ 33117 * (s / q) := by linarith only [hsq]
  have hfinite :=
    Shao.OQ6.PhysicalCompact.finite_physical_studentizer_conversion
      H0 (by intro i j; rfl) hn
  dsimp only at hfinite
  rcases hfinite with ⟨_, _, _, _, _, _, hτrange, _⟩
  change (∀ x : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ τ x ∧ τ x ≤ 1) at hτrange
  refine ⟨hT, hLowModel n, ?_⟩
  intro x hx hx1
  let error : ℝ := K * (β / Real.rpow N ((p - 2) / 2) + s / q)
  let y : ℝ := τ x
  let Lcompact : ℝ := N *
    (∫ o, Shao.truncationF ((1 + y) * (g o / q)) ∂μ)
  change
    |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
    |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
    |P₀.real {ξ | x < T ξ} - (1 - Shao.OQ4.standardNormalCDF x)| ≤ error ∧
    |P₀.real {ξ | x ≤ T ξ} - (1 - Shao.OQ4.standardNormalCDF x)| ≤ error
  have hy : 0 ≤ y := (hτrange x hx hx1).1
  have hy1 : y ≤ 1 := (hτrange x hx hx1).2
  have hmoment := Shao.OQ6.ActualPhysicalCompactCDF.normalized_observation_truncation_budget_le_rpow_moment
    μ g hgm hg2 p hp2.le hp3 hgp n (le_trans (by norm_num : 1 ≤ 3) hn) y hy
  dsimp only at hmoment
  have hL := hmoment.2.2
  change Lcompact ≤ β * Real.rpow (1 + y) p /
    Real.rpow N ((p - 2) / 2) at hL
  have hscale : Real.rpow (1 + y) p ≤ 8 := by
    calc
      Real.rpow (1 + y) p ≤ Real.rpow (2 : ℝ) p :=
        Real.rpow_le_rpow (by linarith only [hy])
          (by linarith only [hy1]) (by linarith only [hp2])
      _ ≤ Real.rpow (2 : ℝ) (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hp3
      _ = (2 : ℝ) ^ 3 := Real.rpow_natCast 2 3
      _ = 8 := by norm_num
  have hL8 : Lcompact ≤ 8 * (β / Real.rpow N ((p - 2) / 2)) := by
    calc
      Lcompact ≤ β * Real.rpow (1 + y) p /
          Real.rpow N ((p - 2) / 2) := hL
      _ ≤ β * 8 / Real.rpow N ((p - 2) / 2) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hscale hβ) hden.le
      _ = 8 * (β / Real.rpow N ((p - 2) / 2)) := by ring
  have hrescoef : 16 * (1 + 4096) * (1 + y) ≤ (131104 : ℝ) := by
    linarith only [hy1]
  have hres := mul_le_mul_of_nonneg_right hrescoef hsq
  have hinside :
      Lcompact + 16 * (1 + 4096) * (1 + y) * s / q ≤
        8 * (β / Real.rpow N ((p - 2) / 2)) + 131104 * (s / q) := by
    calc
      Lcompact + 16 * (1 + 4096) * (1 + y) * s / q =
          Lcompact + (16 * (1 + 4096) * (1 + y)) * (s / q) := by ring
      _ ≤ 8 * (β / Real.rpow N ((p - 2) / 2)) + 131104 * (s / q) :=
        add_le_add hL8 hres
  have hanalytic :
      C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) ≤
        8 * C * (β / Real.rpow N ((p - 2) / 2)) + 131104 * C * (s / q) := by
    calc
      _ ≤ C * (8 * (β / Real.rpow N ((p - 2) / 2)) + 131104 * (s / q)) :=
        mul_le_mul_of_nonneg_left hinside hC.le
      _ = _ := by ring
  have hfee :
      C * (Lcompact + 16 * (1 + 4096) * (1 + y) * s / q) +
        2 * Real.exp (-cg * N) + ((1 / 8 : ℝ) + 33104 * s) / q + 12 / N ≤
      error := by
    have hA := mul_le_mul_of_nonneg_right hKA hβden
    have hB := mul_le_mul_of_nonneg_right hKB hsq
    dsimp only [error]
    nlinarith only [hanalytic, hexp, hpoly, hA, hB]
  have hphysicalx := hRaw x hx hx1
  rcases hphysicalx with ⟨h1, h2, h3, h4⟩
  exact ⟨h1.trans hfee, h2.trans hfee, h3.trans hfee, h4.trans hfee⟩

theorem uniform_pmoment_original_physical_compact_cdf_tail_rpow_rate
    (C : ℝ)
    (hSZC : Shao.OQ6.NormalizedIntegrableCDFAssembly.ScalarShaoZhouFiniteCostCDFInput.{u} C)
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (B : ℝ) (hB : 1 ≤ B) :
    let tB : ℝ := Real.rpow (1 / (4 * B)) (2 / (p - 2))
    let cg : ℝ := tB / 4
    0 < cg ∧
      ∃ K : ℝ, 0 < K ∧
        ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω]
          (μ : Measure Ω) [IsProbabilityMeasure μ]
          (h : Ω → Ω → ℝ)
          (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
          (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
          (hhsymm : ∀ o y, h o y = h y o)
          (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
          (hprojectionsecond :
            (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
          (hgp : Integrable (fun o => Real.rpow |∫ y, h o y ∂μ| p) μ)
          (hβBound : (∫ o, Real.rpow |∫ y, h o y ∂μ| p ∂μ) ≤ B),
          let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
          let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
          let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
          let s : ℝ := 1 + Real.sqrt v
          let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
          ∀ (n : ℕ), 3 ≤ n →
            let N : ℝ := (n : ℝ)
            let q : ℝ := Real.sqrt N
            let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
            let U : (Fin n → Ω) → ℝ := fun ξ =>
              Shao.OQ6.FiniteRows.uStatistic (fun i j => h (ξ i) (ξ j))
            let R2 : (Fin n → Ω) → ℝ := fun ξ =>
              Shao.OQ6.FiniteRows.jackknifeSq (fun i j => h (ξ i) (ξ j))
            let T : (Fin n → Ω) → ℝ := fun ξ =>
              if 0 < R2 ξ then q * U ξ / Real.sqrt (R2 ξ) else 0
            Measurable T ∧
              P₀.real {ξ | (∑ i : Fin n, g (ξ i) ^ (2 : ℕ)) ≤ N / 2} ≤
                Real.exp (-cg * N) ∧
              ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
                let error : ℝ := K *
                  (β / Real.rpow N ((p - 2) / 2) + s / q)
                |P₀.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
                |P₀.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
                |P₀.real {ξ | x < T ξ} -
                  (1 - Shao.OQ4.standardNormalCDF x)| ≤ error ∧
                |P₀.real {ξ | x ≤ T ξ} -
                  (1 - Shao.OQ4.standardNormalCDF x)| ≤ error
:= by
  classical
  intro tB cg
  let K : ℝ := 131112 * C + 33117 + 2 / cg
  have hClass := countably_generated_uniform_compact_rate C hSZC p hp2 hp3 B hB
  rcases hClass with ⟨hcg, hK, hCountable⟩
  change 0 < cg at hcg
  change 0 < K at hK
  refine ⟨hcg, K, hK, ?_⟩
  intro Ω mΩ μ hμ h hh hh2 hhsymm hcenter hprojectionsecond hgp hβBound g r v s β
  have hdataOriginal := Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
    μ h hh hh2 hhsymm hcenter hprojectionsecond 3 (by norm_num) 0
      (by norm_num) (by positivity)
  dsimp only at hdataOriginal
  rcases hdataOriginal with ⟨hgOriginalData, hg2OriginalData, _, hgsecondOriginalData, _⟩
  change Measurable g at hgOriginalData
  change MemLp g 2 μ at hg2OriginalData
  change (∫ o, g o ^ 2 ∂μ) = 1 at hgsecondOriginalData
  change Integrable (fun o => Real.rpow |g o| p) μ at hgp
  change (∫ o, Real.rpow |g o| p ∂μ) ≤ B at hβBound
  have hLowOriginal : ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n => μ)).real
        {ξ : Fin n → Ω | (∑ i : Fin n, g (ξ i) ^ (2 : ℕ)) ≤ (n : ℝ) / 2} ≤
          Real.exp (-cg * (n : ℝ)) := by
    have hUniform := Shao.OQ6.UniformPMomentLowEnergy.actual_uniform_pmoment_low_energy.{u}
      p hp2 hp3 B hB
    dsimp only at hUniform
    rcases hUniform with ⟨_, _, _, _, _, _, hLow⟩
    have hLowModel := hLow μ g hgOriginalData hg2OriginalData
      hgsecondOriginalData hgp hβBound
    intro n
    have hLowN := hLowModel.2.2.2.2.2 n
    exact hLowN.2.2.2.2.2.2.2
  have hmodel :=
    Shao.OQ6.OriginalCountablyGeneratedModel.actual_normalized_original_countably_generated_model.{u, 0, 0}
      μ h hh hh2 hhsymm hcenter hprojectionsecond
  dsimp only at hmodel
  obtain ⟨m₀, hm₀, hcg₀, hh₀, _, hmodel₀⟩ := hmodel
  rcases hmodel₀ with
    ⟨hprob₀, _, hgeq, _, hv, _, _, hh₂₀, hcenter₀, hg₀, _, _,
      hgsecond₀, _, _, _, _, hglaw, _, _, hfinite, _⟩
  let μ₀ : @Measure Ω m₀ := μ.trim hm₀
  have hid : Measurable[mΩ, m₀] (id : Ω → Ω) := measurable_id'' hm₀
  letI : MeasurableSpace Ω := m₀
  letI : MeasurableSpace.CountablyGenerated Ω := hcg₀
  letI : IsProbabilityMeasure μ₀ := hprob₀
  let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
  let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
  let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(μ₀.prod μ₀)
  let ν : Measure ℝ := @Measure.map Ω ℝ mΩ (borel ℝ) g μ
  change g₀ = g at hgeq
  change v₀ = v at hv
  change Measurable g₀ at hg₀
  change (∫ o, g₀ o ^ 2 ∂μ₀) = 1 at hgsecond₀
  change μ₀.map g₀ = ν at hglaw
  have hgOriginal : Measurable[mΩ, borel ℝ] g := by
    rw [← hgeq]
    exact hg₀.comp hid
  let F : ℝ → ℝ := fun z => Real.rpow |z| p
  have hFcont : Continuous F := by
    dsimp only [F]
    simpa only [Real.rpow_eq_pow, Function.comp_def] using
      (Real.continuous_rpow_const
        (show 0 ≤ p by linarith only [hp2])).comp continuous_abs
  have hFν : Integrable F ν := by
    letI : MeasurableSpace Ω := mΩ
    change Integrable F (μ.map g)
    exact (integrable_map_measure hFcont.aestronglyMeasurable
      hgOriginal.aemeasurable).2 hgp
  have hFν₀ : Integrable F (μ₀.map g₀) := by
    rw [hglaw]
    exact hFν
  have hgp₀ : Integrable (fun o => Real.rpow |g₀ o| p) μ₀ :=
    (integrable_map_measure hFν₀.aestronglyMeasurable hg₀.aemeasurable).1 hFν₀
  have hβ₀ : (∫ o, Real.rpow |g₀ o| p ∂μ₀) = β := by
    calc
      (∫ o, Real.rpow |g₀ o| p ∂μ₀) = ∫ z, F z ∂(μ₀.map g₀) :=
        (integral_map hg₀.aemeasurable hFν₀.aestronglyMeasurable).symm
      _ = ∫ z, F z ∂ν := by rw [hglaw]
      _ = β := by
        letI : MeasurableSpace Ω := mΩ
        change (∫ z, F z ∂(μ.map g)) = β
        rw [integral_map hgOriginal.aemeasurable hFν.aestronglyMeasurable]
  have hβBound₀ : (∫ o, Real.rpow |g₀ o| p ∂μ₀) ≤ B := by
    rw [hβ₀]
    exact hβBound
  have hphysical := @hCountable Ω m₀ hcg₀ μ₀ hprob₀ h hh₀ hh₂₀ hhsymm
    hcenter₀ hgsecond₀ hgp₀ hβBound₀
  dsimp only at hphysical
  dsimp only [v₀, r₀, g₀] at hv
  rw [hβ₀, hv] at hphysical
  intro n hn N q P U R2 T
  let mN : MeasurableSpace (Fin n → Ω) :=
    @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ)
  let mN₀ : MeasurableSpace (Fin n → Ω) :=
    @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => m₀)
  let Pc : @Measure (Fin n → Ω) mN₀ :=
    @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
      (fun _ : Fin n => m₀) (fun _ : Fin n => μ₀)
  have hbound := hphysical n hn
  rcases hbound with ⟨hT₀, _, hbounds⟩
  change Measurable[mN₀, borel ℝ] T at hT₀
  have hprod := hfinite (Fin n) (inferInstance : Fintype (Fin n))
  rcases hprod with ⟨_, hidN, _, hTarget⟩
  change Measurable[mN, mN₀] (id : (Fin n → Ω) → Fin n → Ω) at hidN
  have hT : Measurable[mN, borel ℝ] T := hT₀.comp hidN
  have hTlaw := hTarget ℝ (borel ℝ) T hT₀
  change
    @Measure.map (Fin n → Ω) ℝ mN₀ (borel ℝ) T Pc =
      @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) T P at hTlaw
  have hEvent (B : Set ℝ) (hB : MeasurableSet B) :
      Pc (T ⁻¹' B) = P (T ⁻¹' B) := by
    calc
      Pc (T ⁻¹' B) =
          (@Measure.map (Fin n → Ω) ℝ mN₀ (borel ℝ) T Pc) B :=
        (Measure.map_apply (μ := Pc) hT₀ hB).symm
      _ = (@Measure.map (Fin n → Ω) ℝ mN (borel ℝ) T P) B :=
        congrArg (fun L : Measure ℝ => L B) hTlaw
      _ = P (T ⁻¹' B) := by
        letI : MeasurableSpace (Fin n → Ω) := mN
        exact Measure.map_apply (μ := P) hT hB
  have hrealEvent (B : Set ℝ) (hB : MeasurableSet B) :
      Pc.real (T ⁻¹' B) = P.real (T ⁻¹' B) := by
    simpa only [Measure.real_def] using
      congrArg ENNReal.toReal (hEvent B hB)
  have hClosedLowOriginal := hLowOriginal n
  change P.real {ξ | (∑ i : Fin n, g (ξ i) ^ (2 : ℕ)) ≤ N / 2} ≤
    Real.exp (-cg * N) at hClosedLowOriginal
  refine ⟨hT, hClosedLowOriginal, ?_⟩
  intro x hx hx1 error
  have hle : Pc.real {ξ | T ξ ≤ x} = P.real {ξ | T ξ ≤ x} :=
    hrealEvent (Set.Iic x) measurableSet_Iic
  have hlt : Pc.real {ξ | T ξ < x} = P.real {ξ | T ξ < x} :=
    hrealEvent (Set.Iio x) measurableSet_Iio
  have hgt : Pc.real {ξ | x < T ξ} = P.real {ξ | x < T ξ} :=
    hrealEvent (Set.Ioi x) measurableSet_Ioi
  have hge : Pc.real {ξ | x ≤ T ξ} = P.real {ξ | x ≤ T ξ} :=
    hrealEvent (Set.Ici x) measurableSet_Ici
  have hfour := hbounds x hx hx1
  change
    |Pc.real {ξ | T ξ ≤ x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
    |Pc.real {ξ | T ξ < x} - Shao.OQ4.standardNormalCDF x| ≤ error ∧
    |Pc.real {ξ | x < T ξ} - (1 - Shao.OQ4.standardNormalCDF x)| ≤ error ∧
    |Pc.real {ξ | x ≤ T ξ} - (1 - Shao.OQ4.standardNormalCDF x)| ≤ error at hfour
  rw [hle, hlt, hgt, hge] at hfour
  exact hfour
end
end Shao.OQ6.UniformPMomentOriginalPhysicalCompactCDF
