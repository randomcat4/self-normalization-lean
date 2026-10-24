import Shao.OQ6.CompactTailBounds
import Shao.OQ6.UntiltedCompactCost
import Shao.OQ6.CompactGoodEvent
import Shao.OQ6.ActualRemainderEnvelope
import Shao.OQ6.ResidualDeletionMeasurable
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Shao.OQ6.ActualUncenteredCompactCDF

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology symmDiff

universe u

private theorem finite_projection_residual_numerator
    {n : ℕ} (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ)
    (hn : 3 ≤ n) :
    (∑ i : Fin n, g i) / Real.sqrt (n : ℝ) +
      Shao.OQ5.P35.unorderedPairSum r /
        (Real.sqrt (n : ℝ) * ((n : ℝ) - 1)) =
      Real.sqrt (n : ℝ) *
        Shao.OQ6.FiniteRows.uStatistic (fun i j => g i + g j + r i j) / 2 := by
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

theorem actual_uncentered_compact_cdf_tail_bounds_nonnegative
    (C : ℝ)
    (hSZ : Shao.OQ6.NormalizedIntegrableCDFAssembly.ScalarShaoZhouFiniteCostCDFInput.{u} C)
    {Ω : Type u} [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
    let s : ℝ := 1 + Real.sqrt v
    ∃ c_g : ℝ, 0 < c_g ∧
      ∀ (n : ℕ), 3 ≤ n →
        let N : ℝ := (n : ℝ)
        let q : ℝ := Real.sqrt N
        let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
        let U : (Fin n → Ω) → ℝ := fun ξ =>
          Shao.OQ6.FiniteRows.uStatistic (fun i j => h (ξ i) (ξ j))
        let J : (Fin n → Ω) → ℝ := fun ξ =>
          Shao.OQ6.FiniteRows.uncenteredSq (fun i j => h (ξ i) (ξ j))
        let Tstar : (Fin n → Ω) → ℝ := fun ξ =>
          if 0 < J ξ then q * U ξ / (2 * Real.sqrt (J ξ)) else 0
        Measurable Tstar ∧
          ∀ y : ℝ, 0 ≤ y →
            let z : ℝ := y
            let Lcompact : ℝ := N *
              (∫ o, Shao.truncationF ((1 + z) * (g o / q)) ∂μ)
            let error : ℝ :=
              C * (Lcompact + 16 * (1 + 4096) * (1 + z) * s / q) +
                Real.exp (-c_g * N) + ((1 / 16 : ℝ) + 16384 * s) / q
            |P₀.real {ξ | Tstar ξ ≤ y} - Shao.OQ4.standardNormalCDF y| ≤ error ∧
            |P₀.real {ξ | Tstar ξ < y} - Shao.OQ4.standardNormalCDF y| ≤ error ∧
            |P₀.real {ξ | y < Tstar ξ} -
              (1 - Shao.OQ4.standardNormalCDF y)| ≤ error ∧
            |P₀.real {ξ | y ≤ Tstar ξ} -
              (1 - Shao.OQ4.standardNormalCDF y)| ≤ error := by
  classical
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
  let s : ℝ := 1 + Real.sqrt v
  have hdata := Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
    μ h hh hh2 hhsymm hcenter hprojectionsecond 3 (by omega) 0 (by norm_num) (by positivity)
  dsimp only at hdata
  rcases hdata with ⟨hgm, hg2, hgmean, hgsecond, hrm, hr2, hrsymm, hrcan,
    hv0, hs1, hvs, hrest⟩
  change Measurable g at hgm
  change MemLp g 2 μ at hg2
  change (∫ o, g o ∂μ) = 0 at hgmean
  change (∫ o, g o ^ 2 ∂μ) = 1 at hgsecond
  change Measurable (fun t : Ω × Ω => r t.1 t.2) at hrm
  change MemLp (fun t : Ω × Ω => r t.1 t.2) 2 (μ.prod μ) at hr2
  change (∀ o t, r o t = r t o) at hrsymm
  change (∀ᵐ o ∂μ, (∫ t, r o t ∂μ) = 0) at hrcan
  change 0 ≤ v at hv0
  change 1 ≤ s at hs1
  change v ≤ s ^ 2 at hvs
  obtain ⟨c_g, hc_g, hlocalization⟩ :=
    Shao.OQ6.CompactGoodEvent.actual_uncentered_compact_localization_events
      μ h hh hh2 hhsymm hcenter hprojectionsecond
  refine ⟨c_g, hc_g, ?_⟩
  intro n hn
  let N : ℝ := (n : ℝ)
  let q : ℝ := Real.sqrt N
  let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let U : (Fin n → Ω) → ℝ := fun ξ => Shao.OQ6.FiniteRows.uStatistic (fun i j => h (ξ i) (ξ j))
  let J : (Fin n → Ω) → ℝ := fun ξ => Shao.OQ6.FiniteRows.uncenteredSq (fun i j => h (ξ i) (ξ j))
  let Tstar : (Fin n → Ω) → ℝ := fun ξ => if 0 < J ξ then q * U ξ / (2 * Real.sqrt (J ξ)) else 0
  have hN3 : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hNpos : 0 < N := by linarith
  have hNne : N ≠ 0 := hNpos.ne'
  have hqpos : 0 < q := Real.sqrt_pos.mpr hNpos
  have hqsq : q ^ 2 = N := Real.sq_sqrt hNpos.le
  have hN1pos : 0 < N - 1 := by linarith
  have hspos : 0 < s := by linarith
  have hdenpos : 0 < s * (N ^ 2 * q) := by positivity
  have hCpos : 0 < C := lt_trans (by norm_num) hSZ.1
  have hhentry (i j : Fin n) : Measurable (fun ξ : Fin n → Ω => h (ξ i) (ξ j)) := by
    have hpair : Measurable (fun ξ : Fin n → Ω => (ξ i, ξ j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    exact hh.comp hpair
  have hUm : Measurable U := by
    dsimp only [U, Shao.OQ6.FiniteRows.uStatistic, Shao.OQ5.P35.unorderedPairSum]
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    apply Finset.measurable_sum
    intro j hj
    by_cases hij : i < j
    · simpa only [if_pos hij] using hhentry i j
    · simpa only [if_neg hij] using
        (measurable_const : Measurable (fun _ : Fin n → Ω => (0 : ℝ)))
  have hJm : Measurable J := by
    dsimp only [J, Shao.OQ6.FiniteRows.uncenteredSq]
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.pow_const
    dsimp only [Shao.OQ6.FiniteRows.rowMean]
    apply Measurable.const_mul
    exact Finset.measurable_sum _ (fun j _ => hhentry i j)
  have hTm : Measurable Tstar :=
    Measurable.ite (measurableSet_lt measurable_const hJm)
      ((measurable_const.mul hUm).div (measurable_const.mul hJm.sqrt)) measurable_const
  refine ⟨hTm, ?_⟩
  intro y hy
  let z : ℝ := y
  let Lcompact : ℝ := N * (∫ o, Shao.truncationF ((1 + z) * (g o / q)) ∂μ)
  let error : ℝ := C * (Lcompact + 16 * (1 + 4096) * (1 + z) * s / q) + Real.exp (-c_g * N) + ((1 / 16 : ℝ) + 16384 * s) / q
  let O : Fin n → (Fin n → Ω) → Ω := fun i ξ => ξ i
  let g0 : Fin n → Ω → ℝ := fun _ o => g o / q
  let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ξ => g (ξ i) / q
  let W0 : (Fin n → Ω) → ℝ := fun ξ => ∑ i : Fin n, ξ0 i ξ
  let V0 : (Fin n → Ω) → ℝ := fun ξ => Real.sqrt (∑ i : Fin n, (ξ0 i ξ) ^ 2)
  let e : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ j k => r (ξ j) (ξ k)
  let F : (Fin n → Ω) → ℝ := fun ξ => Shao.OQ5.P35.unorderedPairSum (e ξ)
  let Fdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i => Shao.OQ5.P35.unorderedPairSum (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i)
  let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ j => Shao.OQ6.ResidualDeletion.rowSum (e ξ) j
  let ψdel : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ i j => Shao.OQ6.ResidualDeletion.rowSum (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i) j
  let Λsq : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, ψ ξ j ^ 2
  let Λdelsq : (Fin n → Ω) → Fin n → ℝ := fun ξ i => ∑ j : Fin n, ψdel ξ i j ^ 2
  let D1 : (Fin n → Ω) → ℝ := fun ξ => F ξ / (q * (N - 1))
  let D1del : (Fin n → Ω) → Fin n → ℝ := fun ξ i => Fdel ξ i / (q * (N - 1))
  let A : (Fin n → Ω) → ℝ := fun ξ => |D1 ξ|
  let Adel : (Fin n → Ω) → Fin n → ℝ := fun ξ i => |D1del ξ i|
  let B : (Fin n → Ω) → ℝ := fun ξ => 4096 * (s / q + Λsq ξ / (s * (N ^ 2 * q)))
  let Bdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i => 4096 * (s / q + Λdelsq ξ i / (s * (N ^ 2 * q)))
  let Vsq : (Fin n → Ω) → ℝ := fun ξ => (∑ i : Fin n, g (ξ i) ^ 2) / N
  let W : (Fin n → Ω) → ℝ := fun ξ => (∑ i : Fin n, g (ξ i)) / q
  let D2 : (Fin n → Ω) → ℝ := fun ξ => if 0 < Vsq ξ then J ξ / Vsq ξ - 1 else 0
  let G : Set (Fin n → Ω) := {ξ | (1 / 2 : ℝ) ≤ Vsq ξ ∧ |W ξ| ≤ Real.sqrt q * (4 + Real.sqrt (Vsq ξ))}
  let Hcpt : Set (Fin n → Ω) := {ξ | ξ ∈ G ∧ -(1 / 2 : ℝ) ≤ D2 ξ}
  let D2c : (Fin n → Ω) → ℝ := fun ξ => if ξ ∈ G then max (D2 ξ) (-(1 / 2 : ℝ)) else 0
  let eDeleted : ∀ i : Fin n, ({j : Fin n // j ≠ i} → Ω) → Fin n → Fin n → ℝ := fun i η j k => if hj : j = i then 0 else if hk : k = i then 0 else r (η ⟨j, hj⟩) (η ⟨k, hk⟩)
  let Adeleted : ∀ i : Fin n, ({j : Fin n // j ≠ i} → Ω) → ℝ := fun i η => |Shao.OQ5.P35.unorderedPairSum (eDeleted i η) / (q * (N - 1))|
  let Bdeleted : ∀ i : Fin n, ({j : Fin n // j ≠ i} → Ω) → ℝ := fun i η => 4096 * (s / q + (∑ j : Fin n, Shao.OQ6.ResidualDeletion.rowSum (eDeleted i η) j ^ 2) / (s * (N ^ 2 * q)))
  let κ0 : (Fin n → Ω) → ℝ := fun _ => 0
  let b0 : (Fin n → Ω) → ℝ := fun ξ => Real.sqrt (1 + D2c ξ)
  let N0 : (Fin n → Ω) → ℝ := fun ξ => W0 ξ + D1 ξ
  let d0 : (Fin n → Ω) → ℝ := fun ξ => V0 ξ * b0 ξ
  let projectionTest : (Fin n → Ω) → Fin n → ℝ := fun ξ i => Shao.truncationF ((1 + z) * (g (ξ i) / q))
  let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i => min (|g (ξ i)| / q) (1 / (1 + z))
  let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ξ i => cap ξ i * (|A ξ - Adel ξ i| + z * |B ξ - Bdel ξ i|)
  let fullTest : (Fin n → Ω) → ℝ := fun ξ => A ξ + z * B ξ
  let δ0 : Fin n → ℝ := fun i => ∫ ξ, ((1 + z) * ξ0 i ξ) ^ 2 * min |(1 + z) * ξ0 i ξ| 1 ∂P₀
  let K0 : ℝ := (∑ i : Fin n, δ0 i) + (∫ ξ, fullTest ξ ∂P₀) + ∑ i : Fin n, ∫ ξ, deletedTest ξ i ∂P₀
  let Fle : Set (Fin n → Ω) := {ξ | N0 ξ ≤ y * d0 ξ}
  let Flt : Set (Fin n → Ω) := {ξ | N0 ξ < y * d0 ξ}
  let Fgt : Set (Fin n → Ω) := {ξ | y * d0 ξ < N0 ξ}
  let Fge : Set (Fin n → Ω) := {ξ | y * d0 ξ ≤ N0 ξ}
  change
    |P₀.real {ξ | Tstar ξ ≤ y} - Shao.OQ4.standardNormalCDF y| ≤ error ∧
    |P₀.real {ξ | Tstar ξ < y} - Shao.OQ4.standardNormalCDF y| ≤ error ∧
    |P₀.real {ξ | y < Tstar ξ} - (1 - Shao.OQ4.standardNormalCDF y)| ≤ error ∧
    |P₀.real {ξ | y ≤ Tstar ξ} - (1 - Shao.OQ4.standardNormalCDF y)| ≤ error
  have hz : 0 ≤ z := hy
  have hO (i : Fin n) : Measurable (O i) := measurable_pi_apply i
  have hOindep : iIndepFun O P₀ := by
    simpa only [O] using
      (iIndepFun_pi (μ := fun _ : Fin n => μ)
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
  have hBm : Measurable B :=
    (measurable_const.add (hΛm.div_const (s * (N ^ 2 * q)))).const_mul 4096
  have hVm : Measurable Vsq := by
    dsimp only [Vsq]
    exact (Finset.measurable_sum _ (fun i _ =>
      (hgm.comp (measurable_pi_apply i)).pow_const 2)).div_const N
  have hWm : Measurable W := by
    dsimp only [W]
    exact (Finset.measurable_sum _ (fun i _ =>
      hgm.comp (measurable_pi_apply i))).div_const q
  have hD2m : Measurable D2 :=
    Measurable.ite (measurableSet_lt measurable_const hVm)
      ((hJm.div hVm).sub_const 1) measurable_const
  have hloc := hlocalization n hn
  dsimp only at hloc
  rcases hloc with ⟨hGm, hHm, hΛint, hBlocInt, hBint, hGfail, hDfail, hHfail, hGood⟩
  change MeasurableSet G at hGm
  change MeasurableSet Hcpt at hHm
  change P₀.real Hcptᶜ ≤ Real.exp (-c_g * N) + ((1 / 16 : ℝ) + 16384 * s) / q at hHfail
  change (∀ ξ ∈ Hcpt, (1 / 2 : ℝ) ≤ Vsq ξ ∧
    (1 / 2 : ℝ) ≤ 1 + D2 ξ ∧ (1 / 4 : ℝ) ≤ J ξ) at hGood
  have hD2cm : Measurable D2c :=
    Measurable.ite hGm (hD2m.max measurable_const) measurable_const
  have hb0m : Measurable b0 := (measurable_const.add hD2cm).sqrt
  have hN0m : Measurable N0 := hW0m.add hD1m
  have hd0m : Measurable d0 := hV0m.mul hb0m
  have hFlem : MeasurableSet Fle := measurableSet_le hN0m (measurable_const.mul hd0m)
  have hFltm : MeasurableSet Flt := measurableSet_lt hN0m (measurable_const.mul hd0m)
  have hFgtm : MeasurableSet Fgt := measurableSet_lt (measurable_const.mul hd0m) hN0m
  have hFgem : MeasurableSet Fge := measurableSet_le (measurable_const.mul hd0m) hN0m
  have hAnonneg (ξ : Fin n → Ω) : 0 ≤ A ξ := abs_nonneg _
  have hΛnonneg (ξ : Fin n → Ω) : 0 ≤ Λsq ξ :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hBnonneg (ξ : Fin n → Ω) : 0 ≤ B ξ := by
    dsimp only [B]
    exact mul_nonneg (by norm_num)
      (add_nonneg (div_nonneg hspos.le hqpos.le)
        (div_nonneg (hΛnonneg ξ) hdenpos.le))
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
          hrm.comp hpair
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
  have hcost := Shao.OQ6.UntiltedCompactCost.actual_quadratic_compact_source_cost
    μ h hh hh2 hhsymm hcenter hprojectionsecond n hn z hz 4096 (by norm_num)
  dsimp only at hcost
  rcases hcost with ⟨hProjI, hLeq, hLnonneg, hLupper, hAi, hAdeli, hBi, hBdeli,
    hAdiffi, hBdiffi, hDeletedI, hResidualBound, hSourceBound⟩
  change (∀ i : Fin n, Integrable (fun ξ => projectionTest ξ i) P₀) at hProjI
  change (∑ i : Fin n, ∫ ξ, projectionTest ξ i ∂P₀) = Lcompact at hLeq
  change 0 ≤ (∑ i : Fin n, ∫ ξ, projectionTest ξ i ∂P₀) at hLnonneg
  rw [hLeq] at hLnonneg
  change Integrable A P₀ at hAi
  change (∀ i : Fin n, Integrable (fun ξ => Adel ξ i) P₀) at hAdeli
  change Integrable B P₀ at hBi
  change (∀ i : Fin n, Integrable (fun ξ => Bdel ξ i) P₀) at hBdeli
  change (∀ i : Fin n, Integrable
    (fun ξ => cap ξ i * |A ξ - Adel ξ i|) P₀) at hAdiffi
  change (∀ i : Fin n, Integrable
    (fun ξ => cap ξ i * |B ξ - Bdel ξ i|) P₀) at hBdiffi
  change (∀ i : Fin n, Integrable (fun ξ => deletedTest ξ i) P₀) at hDeletedI
  change (∑ i : Fin n, ∫ ξ, projectionTest ξ i ∂P₀) +
    ((∫ ξ, A ξ ∂P₀) + z * (∫ ξ, B ξ ∂P₀) +
      ∑ i : Fin n, ∫ ξ, deletedTest ξ i ∂P₀) ≤
    (∑ i : Fin n, ∫ ξ, projectionTest ξ i ∂P₀) +
      16 * (1 + 4096) * (1 + z) * s / q at hSourceBound
  rw [hLeq] at hSourceBound
  have hFullI : Integrable fullTest P₀ := hAi.add (hBi.const_mul z)
  have hFullEq : (∫ ξ, fullTest ξ ∂P₀) =
      (∫ ξ, A ξ ∂P₀) + z * (∫ ξ, B ξ ∂P₀) := by
    dsimp only [fullTest]
    rw [integral_add hAi (hBi.const_mul z), integral_const_mul]
  have hDeltaEq (i : Fin n) : δ0 i = ∫ ξ, projectionTest ξ i ∂P₀ := rfl
  have hL0Eq : (∑ i : Fin n, δ0 i) = Lcompact := by
    simpa only [hDeltaEq] using hLeq
  have hKbound : K0 ≤ Lcompact + 16 * (1 + 4096) * (1 + z) * s / q := by
    dsimp only [K0]
    rw [hL0Eq, hFullEq]
    linarith [hSourceBound]
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
  have hNumerator (ξ : Fin n → Ω) : N0 ξ = q * U ξ / 2 := by
    have ht := finite_projection_residual_numerator (fun i => g (ξ i)) (e ξ) hn
    rw [hKernel ξ] at ht
    simpa only [N0, W0, ξ0, D1, F, U, N, q, Finset.sum_div] using ht
  by_cases hscale : s ≤ q
  · have hEnvelope (ξ : Fin n → Ω) (hξ : ξ ∈ G) : |D2 ξ| ≤ B ξ := by
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
      simpa only [O, g0, cap, hAdpull, hBdpull, deletedTest, z,
        abs_div, abs_of_pos hqpos, one_div] using hDeletedI i
    have hEngineFull : Integrable
        (fun ξ : Fin n → Ω => A (fun i => O i ξ) + y * B (fun i => O i ξ)) P₀ := by
      simpa only [O, fullTest, z] using hFullI
    have hEngine := Shao.OQ6.CompactTailBounds.ambient_weighted_ae_compact_tail_bounds
      C hSZ P₀ n (by omega) O hO hOindep g0 hg0m hg0Lp hg0mean hg0energy
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
        cap, ξ0, g0, O, z, hAdpull, hBdpull, abs_div, abs_of_pos hqpos,
        one_div, mul_assoc] using hEngine.1
    have hTailGE : |P₀.real Fge - (1 - Shao.OQ4.standardNormalCDF y)| ≤ C * K0 := by
      simpa only [Fge, N0, d0, W0, V0, b0, K0, δ0, fullTest, deletedTest,
        cap, ξ0, g0, O, z, hAdpull, hBdpull, abs_div, abs_of_pos hqpos,
        one_div, mul_assoc] using hEngine.2.1
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
    have hCDFLE : |P₀.real Fle - Shao.OQ4.standardNormalCDF y| ≤ C * K0 := by
      have ht := hComplementError Fgt hFgtm (1 - Shao.OQ4.standardNormalCDF y)
      rw [show 1 - (1 - Shao.OQ4.standardNormalCDF y) =
        Shao.OQ4.standardNormalCDF y by ring, ← hFleComp] at ht
      rw [ht]
      exact hTailGT
    have hCDFLT : |P₀.real Flt - Shao.OQ4.standardNormalCDF y| ≤ C * K0 := by
      have ht := hComplementError Fge hFgem (1 - Shao.OQ4.standardNormalCDF y)
      rw [show 1 - (1 - Shao.OQ4.standardNormalCDF y) =
        Shao.OQ4.standardNormalCDF y by ring, ← hFltComp] at ht
      rw [ht]
      exact hTailGE
    have hAgree (ξ : Fin n → Ω) (hξ : ξ ∈ Hcpt) :
        (Tstar ξ ≤ y ↔ ξ ∈ Fle) ∧ (Tstar ξ < y ↔ ξ ∈ Flt) ∧
        (y < Tstar ξ ↔ ξ ∈ Fgt) ∧ (y ≤ Tstar ξ ↔ ξ ∈ Fge) := by
      have hgood := hGood ξ hξ
      have hVp : 0 < Vsq ξ := by linarith [hgood.1]
      have hJp : 0 < J ξ := by linarith [hgood.2.2]
      have hclip : D2c ξ = D2 ξ := by
        rw [show D2c ξ = max (D2 ξ) (-(1 / 2 : ℝ)) by exact if_pos hξ.1,
          max_eq_left hξ.2]
      have hprod : Vsq ξ * (1 + D2c ξ) = J ξ := by
        rw [hclip, show D2 ξ = J ξ / Vsq ξ - 1 by exact if_pos hVp]
        field_simp [hVp.ne']
        <;> ring
      have hVroot : V0 ξ = Real.sqrt (Vsq ξ) := by
        dsimp only [V0]
        rw [hEnergyPoint ξ]
      have hden : d0 ξ = Real.sqrt (J ξ) := by
        calc
          d0 ξ = Real.sqrt (Vsq ξ) * Real.sqrt (1 + D2c ξ) := by
            dsimp only [d0, b0]
            rw [hVroot]
          _ = Real.sqrt (Vsq ξ * (1 + D2c ξ)) := (Real.sqrt_mul hVp.le _).symm
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
      have hsub : E ∆ Fset ⊆ Hcptᶜ := by
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
        (a : ℝ) (hGaussian : |P₀.real Fset - a| ≤ C * K0) :
        |P₀.real E - a| ≤ error := by
      have hDiff := hCompare E Fset hE hF hEF
      have hCostPaid := mul_le_mul_of_nonneg_left hKbound hCpos.le
      calc
        |P₀.real E - a| ≤ |P₀.real E - P₀.real Fset| + |P₀.real Fset - a| :=
          abs_sub_le _ _ _
        _ ≤ P₀.real Hcptᶜ + C * K0 := add_le_add hDiff hGaussian
        _ ≤ error := by dsimp only [error]; linarith [hHfail, hCostPaid]
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
    have hcoeff : (1 : ℝ) ≤ 16 * (1 + 4096) * (1 + z) := by nlinarith [hz]
    have hRate : 1 ≤ Lcompact + 16 * (1 + 4096) * (1 + z) * s / q := by
      have ht := mul_le_mul_of_nonneg_right hcoeff
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) hratio)
      have he : 16 * (1 + 4096) * (1 + z) * (s / q) =
          16 * (1 + 4096) * (1 + z) * s / q := by ring
      rw [he] at ht
      linarith [hLnonneg, hratio]
    have hRate0 : 0 ≤ Lcompact + 16 * (1 + 4096) * (1 + z) * s / q :=
      le_trans (by norm_num) hRate
    have hCRate := mul_le_mul_of_nonneg_right hSZ.1.le hRate0
    have hBad0 : 0 ≤ ((1 / 16 : ℝ) + 16384 * s) / q := by positivity
    have hErrorOne : 1 ≤ error := by
      dsimp only [error]
      linarith [hRate, hCRate, Real.exp_pos (-c_g * N), hBad0]
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

end

end Shao.OQ6.ActualUncenteredCompactCDF
