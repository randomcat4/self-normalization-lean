import Shao.OQ6.UntiltedCompactCostFoundation
import Shao.OQ6.ActualQuadraticTiltMoments
import Shao.OQ6.FiniteTiltedMoments
import Shao.OQ6.ResidualDeletion
import Shao.OQ6.CanonicalTilt
import Shao.OQ6.CappedSectionEnergy
import Shao.Basic.TruncationBudget
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

theorem actual_quadratic_compact_source_cost
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 3 ≤ n)
    (z : ℝ) (hz : 0 ≤ z)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
    let s : ℝ := 1 + Real.sqrt v
    let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let projectionTest : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Shao.truncationF ((1 + z) * (g (ξ i) / Real.sqrt (n : ℝ)))
    let Lcompact : ℝ :=
      ∑ i : Fin n, ∫ ξ, projectionTest ξ i ∂P₀
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
    let A : (Fin n → Ω) → ℝ := fun ξ => |D₁ ξ|
    let Adel : (Fin n → Ω) → Fin n → ℝ := fun ξ i => |D₁del ξ i|
    let B : (Fin n → Ω) → ℝ := fun ξ =>
      C₀ * (s / Real.sqrt (n : ℝ) +
        Λsq ξ / (s * ((n : ℝ) ^ 2 * Real.sqrt (n : ℝ))))
    let Bdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      C₀ * (s / Real.sqrt (n : ℝ) +
        Λdelsq ξ i / (s * ((n : ℝ) ^ 2 * Real.sqrt (n : ℝ))))
    let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      cap ξ i * (|A ξ - Adel ξ i| + z * |B ξ - Bdel ξ i|)
    let residualCost : ℝ :=
      (∫ ξ, A ξ ∂P₀) + z * (∫ ξ, B ξ ∂P₀) +
        ∑ i : Fin n, ∫ ξ, deletedTest ξ i ∂P₀
    let sourceCost : ℝ := Lcompact + residualCost
    (∀ i : Fin n, Integrable (fun ξ => projectionTest ξ i) P₀) ∧
      Lcompact = (n : ℝ) *
        (∫ o, Shao.truncationF
          ((1 + z) * (g o / Real.sqrt (n : ℝ))) ∂μ) ∧
      0 ≤ Lcompact ∧ Lcompact ≤ (1 + z) ^ 2 ∧
      Integrable A P₀ ∧
      (∀ i : Fin n, Integrable (fun ξ => Adel ξ i) P₀) ∧
      Integrable B P₀ ∧
      (∀ i : Fin n, Integrable (fun ξ => Bdel ξ i) P₀) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => cap ξ i * |A ξ - Adel ξ i|) P₀) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => cap ξ i * |B ξ - Bdel ξ i|) P₀) ∧
      (∀ i : Fin n, Integrable (fun ξ => deletedTest ξ i) P₀) ∧
      residualCost ≤
        16 * (1 + C₀) * (1 + z) * s / Real.sqrt (n : ℝ) ∧
      sourceCost ≤ Lcompact +
        16 * (1 + C₀) * (1 + z) * s / Real.sqrt (n : ℝ) := by
  classical
  dsimp only
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
  let s : ℝ := 1 + Real.sqrt v
  let N : ℝ := (n : ℝ)
  let q : ℝ := Real.sqrt N
  let den : ℝ := q * (N - 1)
  let K : ℝ := s * (N ^ 2 * q)
  let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let projectionTest : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Shao.truncationF ((1 + z) * (g (ξ i) / q))
  let Lcompact : ℝ := ∑ i : Fin n, ∫ ξ, projectionTest ξ i ∂P₀
  let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i => min (|g (ξ i)| / q) (1 / (1 + z))
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
  let A : (Fin n → Ω) → ℝ := fun ξ => |D₁ ξ|
  let Adel : (Fin n → Ω) → Fin n → ℝ := fun ξ i => |D₁del ξ i|
  let B : (Fin n → Ω) → ℝ := fun ξ => C₀ * (s / q + Λsq ξ / K)
  let Bdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i => C₀ * (s / q + Λdelsq ξ i / K)
  let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    cap ξ i * (|A ξ - Adel ξ i| + z * |B ξ - Bdel ξ i|)
  let residualCost : ℝ := (∫ ξ, A ξ ∂P₀) + z * (∫ ξ, B ξ ∂P₀) +
    ∑ i : Fin n, ∫ ξ, deletedTest ξ i ∂P₀
  let sourceCost : ℝ := Lcompact + residualCost
  have hN : 3 ≤ N := by dsimp only [N]; exact_mod_cast hn
  have hN0 : 0 ≤ N := by linarith
  have hNp : 0 < N := by linarith
  have hq : 0 < q := Real.sqrt_pos.2 hNp
  have hq2 : q ^ 2 = N := Real.sq_sqrt hN0
  have hden : 0 < den := mul_pos hq (by linarith)
  have hactual := Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
    μ h hh hh2 hhsymm hcenter hprojectionsecond n hn 0 (by norm_num) (by positivity)
  rcases hactual with ⟨hgm, hg2, hgmean, hgsecond, hrm, hr2, hrsymm, hrcan, hv0, hs1, hvB, _⟩
  change Measurable g at hgm
  change MemLp g 2 μ at hg2
  change (∫ o, g o ^ 2 ∂μ) = 1 at hgsecond
  change Measurable (fun t : Ω × Ω => r t.1 t.2) at hrm
  change MemLp (fun t : Ω × Ω => r t.1 t.2) 2 (μ.prod μ) at hr2
  change (∀ o y, r o y = r y o) at hrsymm
  change (∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0) at hrcan
  change 1 ≤ s at hs1
  change v ≤ s ^ 2 at hvB
  have hs : 0 ≤ s := le_trans (by norm_num) hs1
  have hsp : 0 < s := lt_of_lt_of_le (by norm_num) hs1
  have hK : 0 < K := mul_pos hsp (mul_pos (sq_pos_of_pos hNp) hq)
  have hcoord (i : Fin n) : MeasurePreserving (fun ξ : Fin n → Ω => ξ i) P₀ μ :=
    measurePreserving_eval (μ := fun _ : Fin n => μ) i
  have hpull (i : Fin n) (f : Ω → ℝ) (hf : Measurable f) :
      (∫ ξ, f (ξ i) ∂P₀) = ∫ o, f o ∂μ := by
    calc
      _ = ∫ o, f o ∂P₀.map (fun ξ : Fin n → Ω => ξ i) :=
        (integral_map (hcoord i).measurable.aemeasurable hf.aestronglyMeasurable).symm
      _ = _ := by rw [(hcoord i).map_eq]
  have hprojM (i : Fin n) : Measurable (fun ξ => projectionTest ξ i) :=
    Shao.continuous_truncationF.measurable.comp
      ((((hgm.comp (measurable_pi_apply i)).div_const q).const_mul (1 + z)))
  have hproj2 (i : Fin n) : MemLp (fun ξ => (1 + z) * (g (ξ i) / q)) 2 P₀ := by
    simpa only [div_eq_mul_inv, Function.comp_apply] using
      (((hg2.comp_measurePreserving (hcoord i)).mul_const q⁻¹).const_mul (1 + z))
  have hprojI (i : Fin n) : Integrable (fun ξ => projectionTest ξ i) P₀ := by
    apply (hproj2 i).integrable_sq.mono' (hprojM i).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ξ => by
      change |Shao.truncationF ((1 + z) * (g (ξ i) / q))| ≤ _
      rw [abs_of_nonneg (Shao.truncationF_nonneg _)]
      exact Shao.truncationF_le_sq _
  have hprojB (i : Fin n) : (∫ ξ, projectionTest ξ i ∂P₀) ≤ (1 + z) ^ 2 / N := by
    calc
      _ ≤ ∫ ξ, ((1 + z) * (g (ξ i) / q)) ^ 2 ∂P₀ :=
        integral_mono (hprojI i) (hproj2 i).integrable_sq (fun ξ => Shao.truncationF_le_sq _)
      _ = (1 + z) ^ 2 / N := by
        simp_rw [mul_pow, div_pow]
        rw [integral_const_mul, integral_div, hpull i _ (hgm.pow_const 2), hgsecond, hq2]
        ring
  have hLid : Lcompact = N * (∫ o, Shao.truncationF ((1 + z) * (g o / q)) ∂μ) := by
    have hf : Measurable (fun o => Shao.truncationF ((1 + z) * (g o / q))) :=
      Shao.continuous_truncationF.measurable.comp ((hgm.div_const q).const_mul (1 + z))
    dsimp only [Lcompact, projectionTest]
    simp_rw [hpull _ _ hf]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, N]
  have hL0 : 0 ≤ Lcompact := Finset.sum_nonneg (fun i hi => integral_nonneg (fun ξ => Shao.truncationF_nonneg _))
  have hLB : Lcompact ≤ (1 + z) ^ 2 := by
    calc
      _ ≤ ∑ i : Fin n, ((1 + z) ^ 2 / N) := Finset.sum_le_sum (fun i hi => hprojB i)
      _ = (1 + z) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        change N * ((1 + z) ^ 2 / N) = (1 + z) ^ 2
        field_simp [hNp.ne']
  have hμ : μ.withDensity (fun _ : Ω => ENNReal.ofReal (1 : ℝ)) = μ := by simp
  have hgenericF := Shao.OQ6.FiniteTiltedMoments.unordered_pair_sum_second_moment
    μ r hrm hr2 hrsymm hrcan s hs hvB
    (fun _ => 1) measurable_const 1 (fun _ => by norm_num)
    (fun _ => le_rfl) (by simp) 0 (by norm_num) (by simp) n
  rcases hgenericF with ⟨_, _, hF2', hFsq', _, hFB'⟩
  have hF2 : MemLp F 2 P₀ := by simpa only [hμ] using hF2'
  have hFI : Integrable F P₀ := hF2.integrable (by norm_num)
  have hFB : (∫ ξ, F ξ ^ 2 ∂P₀) ≤ (n.choose 2 : ℝ) * s ^ 2 := by
    simpa only [hμ, one_pow, mul_one, zero_pow (by decide : 2 ≠ 0),
      zero_pow (by decide : 4 ≠ 0), mul_zero, add_zero] using hFB'
  have hrow := Shao.OQ6.FiniteTiltedMoments.row_square_sum_moment
    μ r hrm hr2 hrsymm hrcan s hs hvB
    (fun _ => 1) measurable_const 1 (fun _ => by norm_num)
    (fun _ => le_rfl) (by simp) 0 (by norm_num) (by simp) n
  rcases hrow with ⟨_, _, hψ2, hΛi, _, hΛB⟩
  simp only [hμ] at hψ2 hΛi
  change (∀ i : Fin n, MemLp (fun ξ => ψ ξ i) 2 P₀) at hψ2
  change Integrable Λsq P₀ at hΛi
  simp only [hμ, one_pow, mul_one, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero] at hΛB
  change (∫ ξ, Λsq ξ ∂P₀) ≤ 2 * (n.choose 2 : ℝ) * s ^ 2 at hΛB
  have hchoose : (n : ℝ) * ((n : ℝ) - 1) = 2 * (n.choose 2 : ℝ) := by
    have hall : ∀ k : ℕ, (k : ℝ) * ((k : ℝ) - 1) = 2 * (k.choose 2 : ℝ) := by
      intro k
      induction k with
      | zero => norm_num
      | succ k ih =>
          simp only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_succ,
            Nat.cast_add, Nat.cast_one] at ih ⊢
          nlinarith only [ih]
    exact hall n
  have hFB'' : (∫ ξ, F ξ ^ 2 ∂P₀) ≤ ((N - 1) * s) ^ 2 := by
    apply hFB.trans
    have hh : (n.choose 2 : ℝ) ≤ (N - 1) ^ 2 := by
      change N * (N - 1) = 2 * (n.choose 2 : ℝ) at hchoose
      nlinarith only [hN, hchoose, sq_nonneg (N - 2)]
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg s)
    nlinarith only [hh']
  have hΛB' : (∫ ξ, Λsq ξ ∂P₀) ≤ N ^ 2 * s ^ 2 := by
    apply hΛB.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg s)
    rw [← hchoose]
    change N * (N - 1) ≤ N ^ 2
    nlinarith only [hN0]
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
  have hψd2 (i j : Fin n) : MemLp (fun ξ => ψdel ξ i j) 2 P₀ := by
    by_cases hji : j = i
    · simp only [ψdel, Shao.OQ6.ResidualDeletion.rowSum_eraseIncident, if_pos hji]
      exact memLp_const 0
    · simpa only [ψdel, Shao.OQ6.ResidualDeletion.rowSum_eraseIncident, if_neg hji, ψ, e,
        Pi.sub_def] using (hψ2 j).sub (he2 j i hji)
  have hΛdi (i : Fin n) : Integrable (fun ξ => Λdelsq ξ i) P₀ :=
    integrable_finsetSum _ (fun j hj => (hψd2 i j).integrable_sq)
  have hFdelid (ξ : Fin n → Ω) (i : Fin n) : Fdel ξ i = F ξ - ψ ξ i := by
    have hh := Shao.OQ6.ResidualDeletion.unorderedPairSum_sub_eraseIncident (e ξ)
      (fun j k => hrsymm (ξ j) (ξ k)) i
    change F ξ - Fdel ξ i = ψ ξ i at hh
    linarith
  have hFdI (i : Fin n) : Integrable (fun ξ => Fdel ξ i) P₀ :=
    (hFI.sub ((hψ2 i).integrable (by norm_num))).congr
      (Filter.Eventually.of_forall fun ξ => (hFdelid ξ i).symm)
  have hAI : Integrable A P₀ := (hFI.div_const den).abs
  have hAdI (i : Fin n) : Integrable (fun ξ => Adel ξ i) P₀ := ((hFdI i).div_const den).abs
  have hBI : Integrable B P₀ := ((integrable_const (s / q)).add (hΛi.div_const K)).const_mul C₀
  have hBdI (i : Fin n) : Integrable (fun ξ => Bdel ξ i) P₀ :=
    ((integrable_const (s / q)).add ((hΛdi i).div_const K)).const_mul C₀
  have hAmag : (∫ ξ, A ξ ∂P₀) ≤ s / q := by
    have hh := integral_mul_norm_le_Lp_mul_Lq
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ : (2 : ℝ).HolderConjugate 2)
      (by simpa using hF2) (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Fin n → Ω => (1 : ℝ)) 2 P₀))
    have hCS : (∫ ξ, |F ξ| ∂P₀) ≤ Real.sqrt (∫ ξ, F ξ ^ 2 ∂P₀) := by
      simpa only [norm_mul, Real.norm_eq_abs, Real.rpow_two, ← Real.sqrt_eq_rpow,
        sq_abs, norm_one, one_pow, integral_const, probReal_univ, one_smul,
        Real.sqrt_one, mul_one] using hh
    have hFabsB : (∫ ξ, |F ξ| ∂P₀) ≤ (N - 1) * s := by
      calc
        _ ≤ Real.sqrt (∫ ξ, F ξ ^ 2 ∂P₀) := hCS
        _ ≤ Real.sqrt (((N - 1) * s) ^ 2) := Real.sqrt_le_sqrt hFB''
        _ = (N - 1) * s := Real.sqrt_sq (mul_nonneg (by linarith) hs)
    calc
      _ = (∫ ξ, |F ξ| ∂P₀) / den := by simp only [A, D₁, abs_div, abs_of_pos hden, integral_div]
      _ ≤ ((N - 1) * s) / den := div_le_div_of_nonneg_right hFabsB hden.le
      _ = s / q := by dsimp only [den]; field_simp [hq.ne', (show N - 1 ≠ 0 by linarith)] <;> ring
  have hBmag : (∫ ξ, B ξ ∂P₀) ≤ 2 * C₀ * s / q := by
    calc
      _ = C₀ * (s / q + (∫ ξ, Λsq ξ ∂P₀) / K) := by
        rw [show B = (fun ξ => C₀ * (s / q + Λsq ξ / K)) from rfl,
          integral_const_mul, integral_add (integrable_const _) (hΛi.div_const K)]
        simp only [integral_div, integral_const, probReal_univ, one_smul]
      _ ≤ C₀ * (s / q + N ^ 2 * s ^ 2 / K) :=
        mul_le_mul_of_nonneg_left (add_le_add (le_refl (s / q)) (div_le_div_of_nonneg_right hΛB' hK.le)) hC₀
      _ = 2 * C₀ * s / q := by dsimp only [K]; field_simp [hsp.ne', hNp.ne', hq.ne'] <;> ring
  have hU := untilted_compact_weighted_deletion_bounds μ g hgm hg2 hgsecond
    r hrm hr2 hrsymm hrcan s hs hvB n hn z hz
  rcases hU with ⟨_, hDUi, hDUB, _, _, hΛDUi, hΛDUB⟩
  change (∀ i : Fin n, Integrable (fun ξ => cap ξ i * |D₁ ξ - D₁del ξ i|) P₀) at hDUi
  change (∑ i : Fin n, ∫ ξ, cap ξ i * |D₁ ξ - D₁del ξ i| ∂P₀) ≤ 2 * s / q at hDUB
  change (∀ i : Fin n, Integrable (fun ξ => cap ξ i * |Λsq ξ - Λdelsq ξ i|) P₀) at hΛDUi
  change (∑ i : Fin n, ∫ ξ, cap ξ i * |Λsq ξ - Λdelsq ξ i| ∂P₀) ≤ 4 * s ^ 2 * N ^ 2 at hΛDUB
  have hc0 (ξ : Fin n → Ω) (i : Fin n) : 0 ≤ cap ξ i :=
    le_min (div_nonneg (abs_nonneg _) hq.le) (by positivity)
  have hcapm (i : Fin n) : Measurable (fun ξ => cap ξ i) := by
    simpa only [cap, Real.norm_eq_abs, Function.comp_apply] using
      (((hgm.comp (measurable_pi_apply i)).norm.div_const q).min measurable_const)
  have hApoint (ξ : Fin n → Ω) (i : Fin n) :
      cap ξ i * |A ξ - Adel ξ i| ≤ cap ξ i * |D₁ ξ - D₁del ξ i| :=
    mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub (D₁ ξ) (D₁del ξ i)) (hc0 ξ i)
  have hAdelI (i : Fin n) : Integrable (fun ξ => cap ξ i * |A ξ - Adel ξ i|) P₀ := by
    apply (hDUi i).mono'
      ((hcapm i).aestronglyMeasurable.mul (hAI.sub (hAdI i)).abs.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun ξ => by
      change |cap ξ i * (|A ξ - Adel ξ i|)| ≤ _
      rw [abs_of_nonneg (mul_nonneg (hc0 ξ i) (abs_nonneg _))]
      exact hApoint ξ i
  have hAdelB : (∑ i : Fin n, ∫ ξ, cap ξ i * |A ξ - Adel ξ i| ∂P₀) ≤ 2 * s / q := by
    apply (Finset.sum_le_sum (fun i hi => integral_mono (hAdelI i) (hDUi i) (fun ξ => hApoint ξ i))).trans hDUB
  have hBdiff (ξ : Fin n → Ω) (i : Fin n) : B ξ - Bdel ξ i = (C₀ / K) * (Λsq ξ - Λdelsq ξ i) := by
    dsimp only [B, Bdel]
    ring
  have hBabs (ξ : Fin n → Ω) (i : Fin n) : |B ξ - Bdel ξ i| = (C₀ / K) * |Λsq ξ - Λdelsq ξ i| := by
    rw [hBdiff, abs_mul, abs_of_nonneg (div_nonneg hC₀ hK.le)]
  have hBdelI (i : Fin n) : Integrable (fun ξ => cap ξ i * |B ξ - Bdel ξ i|) P₀ := by
    have heq : (fun ξ => cap ξ i * |B ξ - Bdel ξ i|) =
        (fun ξ => (C₀ / K) * (cap ξ i * |Λsq ξ - Λdelsq ξ i|)) := by
      funext ξ
      rw [hBabs]
      ring
    rw [heq]
    exact (hΛDUi i).const_mul _
  have hBdelB : (∑ i : Fin n, ∫ ξ, cap ξ i * |B ξ - Bdel ξ i| ∂P₀) ≤ 4 * C₀ * s / q := by
    calc
      _ = (C₀ / K) * (∑ i : Fin n, ∫ ξ, cap ξ i * |Λsq ξ - Λdelsq ξ i| ∂P₀) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        calc
          _ = ∫ ξ, (C₀ / K) * (cap ξ i * |Λsq ξ - Λdelsq ξ i|) ∂P₀ := by
            congr 1
            funext ξ
            rw [hBabs]
            ring
          _ = _ := integral_const_mul _ _
      _ ≤ (C₀ / K) * (4 * s ^ 2 * N ^ 2) :=
        mul_le_mul_of_nonneg_left hΛDUB (div_nonneg hC₀ hK.le)
      _ = 4 * C₀ * s / q := by dsimp only [K]; field_simp [hsp.ne', hNp.ne', hq.ne'] <;> ring
  have hdeletedEq (i : Fin n) : (fun ξ => deletedTest ξ i) =
      (fun ξ => cap ξ i * |A ξ - Adel ξ i| + z * (cap ξ i * |B ξ - Bdel ξ i|)) := by
    funext ξ
    dsimp only [deletedTest]
    ring
  have hdeletedI (i : Fin n) : Integrable (fun ξ => deletedTest ξ i) P₀ := by
    rw [hdeletedEq]
    exact (hAdelI i).add ((hBdelI i).const_mul z)
  have hdeletedSum : (∑ i : Fin n, ∫ ξ, deletedTest ξ i ∂P₀) ≤ 2 * s / q + z * (4 * C₀ * s / q) := by
    have hsplit (i : Fin n) : (∫ ξ, deletedTest ξ i ∂P₀) =
        (∫ ξ, cap ξ i * |A ξ - Adel ξ i| ∂P₀) + z * (∫ ξ, cap ξ i * |B ξ - Bdel ξ i| ∂P₀) := by
      rw [hdeletedEq, integral_add (hAdelI i) ((hBdelI i).const_mul z), integral_const_mul]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    exact add_le_add hAdelB (mul_le_mul_of_nonneg_left hBdelB hz)
  have hres : residualCost ≤ 16 * (1 + C₀) * (1 + z) * s / q := by
    calc
      _ ≤ s / q + z * (2 * C₀ * s / q) + (2 * s / q + z * (4 * C₀ * s / q)) :=
        add_le_add (add_le_add hAmag (mul_le_mul_of_nonneg_left hBmag hz)) hdeletedSum
      _ = (3 + 6 * C₀ * z) * s / q := by ring
      _ ≤ 16 * (1 + C₀) * (1 + z) * s / q := by
        apply div_le_div_of_nonneg_right _ hq.le
        apply mul_le_mul_of_nonneg_right _ hs
        nlinarith only [hC₀, hz, mul_nonneg hC₀ hz]
  exact ⟨hprojI, hLid, hL0, hLB, hAI, hAdI, hBI, hBdI, hAdelI, hBdelI,
    hdeletedI, hres, add_le_add (le_refl Lcompact) hres⟩

end

end Shao.OQ6.UntiltedCompactCost
