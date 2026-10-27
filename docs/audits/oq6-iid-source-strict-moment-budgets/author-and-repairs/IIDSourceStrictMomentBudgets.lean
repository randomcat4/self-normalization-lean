import Shao.OQ6.ActualPhysicalCompactCDF
import Shao.Probability.TruncationIntegrals
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false

universe u

namespace Shao.OQ6.IIDSourceStrictMomentBudgets

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

theorem actual_iid_source_z_strict_moment_budgets
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (hgp : Integrable (fun o : Ω => Real.rpow |g o| p) μ)
    (cBudget : ℝ) (hcBudget : 0 < cBudget) :
    let β : ℝ := ∫ o : Ω, Real.rpow |g o| p ∂μ
    let c : ℝ :=
      Real.rpow (min (1 / 2 : ℝ) cBudget / 2) (1 / p)
    0 ≤ β ∧
      0 < c ∧
      Real.rpow c p = min (1 / 2 : ℝ) cBudget / 2 ∧
      Real.rpow c p < min (1 / 2 : ℝ) cBudget ∧
      (∀ (n : ℕ) (_hn : 1 ≤ n) (z : ℝ) (_hz : 1 ≤ z),
        let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
        let N : ℝ := Real.sqrt (n : ℝ)
        let ξ : Fin n → (Fin n → Ω) → ℝ :=
          fun i ω => g (ω i) / N
        let projectionTest : (Fin n → Ω) → Fin n → ℝ :=
          fun ω i => Shao.truncationF (z * ξ i ω)
        let δ : Fin n → ℝ :=
          fun i => ∫ ω : Fin n → Ω, projectionTest ω i ∂P
        let L : ℝ := ∑ i : Fin n, δ i
        let scalarBudget : ℝ :=
          ∫ o : Ω, Shao.truncationF (z * (g o / N)) ∂μ
        IsProbabilityMeasure P ∧
          Integrable (fun o : Ω => Shao.truncationF (z * (g o / N))) μ ∧
          (∀ i : Fin n, Integrable (fun ω : Fin n → Ω =>
            projectionTest ω i) P) ∧
          (∀ i : Fin n, δ i = scalarBudget) ∧
          L = (n : ℝ) * scalarBudget ∧
          (∀ i : Fin n, L = (n : ℝ) * δ i) ∧
          (∀ i : Fin n, 0 ≤ δ i) ∧
          0 ≤ L ∧
          L ≤ β * Real.rpow z p /
            Real.rpow (n : ℝ) ((p - 2) / 2) ∧
          (β = 0 → L = 0 ∧ (∀ i : Fin n, δ i = 0)) ∧
          ((β = 0 ∨
              (0 < β ∧ z ≤ c * Real.rpow β (-1 / p) *
                Real.rpow (n : ℝ) ((p - 2) / (2 * p)))) →
            L ≤ Real.rpow c p ∧
              (∀ i : Fin n, δ i < (1 / 2 : ℝ)) ∧
              L < cBudget * z ^ 2))
 := by
  let β : ℝ := ∫ o : Ω, Real.rpow |g o| p ∂μ
  let c : ℝ :=
    Real.rpow (min (1 / 2 : ℝ) cBudget / 2) (1 / p)
  have hp0 : 0 < p := lt_trans (by norm_num : (0 : ℝ) < 2) hp2
  have hpne : p ≠ 0 := hp0.ne'
  have hβ0 : 0 ≤ β := by
    dsimp only [β]
    exact integral_nonneg (fun o : Ω => Real.rpow_nonneg (abs_nonneg (g o)) p)
  have hminPos : 0 < min (1 / 2 : ℝ) cBudget :=
    lt_min (by norm_num) hcBudget
  have hhalfMinPos : 0 < min (1 / 2 : ℝ) cBudget / 2 :=
    div_pos hminPos (by norm_num)
  have hcPos : 0 < c := Real.rpow_pos_of_pos hhalfMinPos (1 / p)
  have hcpower : Real.rpow c p = min (1 / 2 : ℝ) cBudget / 2 := by
    dsimp only [c]
    rw [← Real.rpow_mul hhalfMinPos.le]
    have hexponent : (1 / p) * p = (1 : ℝ) := by
      field_simp [hpne]
    rw [hexponent, Real.rpow_one]
  have hcSmall : Real.rpow c p < min (1 / 2 : ℝ) cBudget := by
    rw [hcpower]
    linarith only [hminPos]
  refine ⟨hβ0, hcPos, hcpower, hcSmall, ?_⟩
  intro n hn z hz
  let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let N : ℝ := Real.sqrt (n : ℝ)
  let ξ : Fin n → (Fin n → Ω) → ℝ :=
    fun i ω => g (ω i) / N
  let projectionTest : (Fin n → Ω) → Fin n → ℝ :=
    fun ω i => Shao.truncationF (z * ξ i ω)
  let δ : Fin n → ℝ :=
    fun i => ∫ ω : Fin n → Ω, projectionTest ω i ∂P
  let L : ℝ := ∑ i : Fin n, δ i
  let scalarBudget : ℝ :=
    ∫ o : Ω, Shao.truncationF (z * (g o / N)) ∂μ
  let f : Ω → ℝ := fun o : Ω => Shao.truncationF (z * (g o / N))
  have hP : IsProbabilityMeasure P := by
    dsimp only [P]
    infer_instance
  have hnReal : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnPos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnReal
  have hz0 : 0 ≤ z := by linarith only [hz]
  have hshift : 1 + (z - 1) = z := by ring
  have hnormalized :
      Integrable (fun o : Ω => Shao.truncationF (z * (g o / N))) μ ∧
        (n : ℝ) * scalarBudget ≤
          β * Real.rpow z p * (n : ℝ) / Real.rpow N p ∧
        (n : ℝ) * scalarBudget ≤
          β * Real.rpow z p / Real.rpow (n : ℝ) ((p - 2) / 2) := by
    simpa only [N, β, scalarBudget, hshift] using
      (Shao.OQ6.ActualPhysicalCompactCDF.normalized_observation_truncation_budget_le_rpow_moment
        μ g hg hg2 p hp2.le hp3 hgp n hn (z - 1) (by linarith only [hz]))
  have hfm : Measurable f := by
    dsimp only [f]
    exact Shao.continuous_truncationF.measurable.comp ((hg.div_const N).const_mul z)
  have hcoord (i : Fin n) :
      MeasurePreserving (fun ω : Fin n → Ω => ω i) P μ :=
    measurePreserving_eval (μ := fun _ : Fin n => μ) i
  have hPiInt (i : Fin n) :
      Integrable (fun ω : Fin n → Ω => projectionTest ω i) P := by
    change Integrable (fun ω : Fin n → Ω => f (ω i)) P
    exact (hcoord i).integrable_comp_of_integrable hnormalized.1
  have hδeq (i : Fin n) : δ i = scalarBudget := by
    change (∫ ω : Fin n → Ω, f (ω i) ∂P) = ∫ o : Ω, f o ∂μ
    calc
      _ = ∫ o : Ω, f o ∂P.map (fun ω : Fin n → Ω => ω i) :=
        (integral_map (hcoord i).measurable.aemeasurable hfm.aestronglyMeasurable).symm
      _ = _ := by rw [(hcoord i).map_eq]
  have hLidentity : L = (n : ℝ) * scalarBudget := by
    dsimp only [L]
    simp_rw [hδeq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hLi (i : Fin n) : L = (n : ℝ) * δ i := by
    rw [hδeq i]
    exact hLidentity
  have hδ0 (i : Fin n) : 0 ≤ δ i := by
    dsimp only [δ]
    exact integral_nonneg (fun ω : Fin n → Ω =>
      Shao.truncationF_nonneg (z * ξ i ω))
  have hL0 : 0 ≤ L := Finset.sum_nonneg (fun i _ => hδ0 i)
  have hδle (i : Fin n) : δ i ≤ L := by
    calc
      δ i = 1 * δ i := (one_mul _).symm
      _ ≤ (n : ℝ) * δ i := mul_le_mul_of_nonneg_right hnReal (hδ0 i)
      _ = L := (hLi i).symm
  have hRate : L ≤ β * Real.rpow z p /
      Real.rpow (n : ℝ) ((p - 2) / 2) := by
    rw [hLidentity]
    exact hnormalized.2.2
  have hzero : β = 0 → L = 0 ∧ (∀ i : Fin n, δ i = 0) := by
    intro hβzero
    have hLleZero : L ≤ 0 := by
      simpa only [hβzero, zero_mul, zero_div] using hRate
    have hLzero : L = 0 := le_antisymm hLleZero hL0
    refine ⟨hLzero, ?_⟩
    intro i
    apply le_antisymm _ (hδ0 i)
    simpa only [hLzero] using hδle i
  have hstrict :
      (β = 0 ∨
          (0 < β ∧ z ≤ c * Real.rpow β (-1 / p) *
            Real.rpow (n : ℝ) ((p - 2) / (2 * p)))) →
        L ≤ Real.rpow c p ∧
          (∀ i : Fin n, δ i < (1 / 2 : ℝ)) ∧
          L < cBudget * z ^ 2 := by
    intro hwindow
    have hLc : L ≤ Real.rpow c p := by
      rcases hwindow with hβzero | ⟨hβpos, hwindow⟩
      · rw [(hzero hβzero).1]
        exact Real.rpow_nonneg hcPos.le p
      · have hdenPos : 0 < Real.rpow (n : ℝ) ((p - 2) / 2) :=
          Real.rpow_pos_of_pos hnPos _
        have hβrootNonneg : 0 ≤ Real.rpow β (-1 / p) :=
          Real.rpow_nonneg hβpos.le _
        have hnrootNonneg :
            0 ≤ Real.rpow (n : ℝ) ((p - 2) / (2 * p)) :=
          Real.rpow_nonneg hnPos.le _
        have hPowBound : Real.rpow z p ≤
            Real.rpow (c * Real.rpow β (-1 / p) *
              Real.rpow (n : ℝ) ((p - 2) / (2 * p))) p :=
          Real.rpow_le_rpow hz0 hwindow hp0.le
        have hβpower : Real.rpow (Real.rpow β (-1 / p)) p = β⁻¹ := by
          rw [← Real.rpow_mul hβpos.le]
          have hexponent : (-1 / p) * p = (-1 : ℝ) := by
            field_simp [hpne]
          rw [hexponent, Real.rpow_neg_one]
        have hnpower :
            Real.rpow (Real.rpow (n : ℝ) ((p - 2) / (2 * p))) p =
              Real.rpow (n : ℝ) ((p - 2) / 2) := by
          rw [← Real.rpow_mul hnPos.le]
          congr 1
          field_simp [hpne] <;> ring
        have hWindowPower : Real.rpow z p ≤
            Real.rpow c p * β⁻¹ * Real.rpow (n : ℝ) ((p - 2) / 2) := by
          calc
            Real.rpow z p ≤
                Real.rpow (c * Real.rpow β (-1 / p) *
                  Real.rpow (n : ℝ) ((p - 2) / (2 * p))) p := hPowBound
            _ = Real.rpow c p * β⁻¹ *
                Real.rpow (n : ℝ) ((p - 2) / 2) := by
              rw [Real.mul_rpow (mul_nonneg hcPos.le hβrootNonneg) hnrootNonneg,
                Real.mul_rpow hcPos.le hβrootNonneg, hβpower, hnpower]
        have hRateWindow : β * Real.rpow z p /
            Real.rpow (n : ℝ) ((p - 2) / 2) ≤ Real.rpow c p := by
          calc
            β * Real.rpow z p / Real.rpow (n : ℝ) ((p - 2) / 2) ≤
                β * (Real.rpow c p * β⁻¹ *
                  Real.rpow (n : ℝ) ((p - 2) / 2)) /
                    Real.rpow (n : ℝ) ((p - 2) / 2) :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hWindowPower hβpos.le) hdenPos.le
            _ = Real.rpow c p := by
              field_simp [hβpos.ne', hdenPos.ne'] <;> ring
        exact hRate.trans hRateWindow
    have hCphalf : Real.rpow c p < (1 / 2 : ℝ) :=
      hcSmall.trans_le (min_le_left _ _)
    have hCpcBudget : Real.rpow c p < cBudget :=
      hcSmall.trans_le (min_le_right _ _)
    have hzsq : (1 : ℝ) ≤ z ^ 2 := by
      nlinarith only [hz, sq_nonneg (z - 1)]
    have hBudgetScale : cBudget ≤ cBudget * z ^ 2 := by
      calc
        cBudget = cBudget * 1 := (mul_one _).symm
        _ ≤ cBudget * z ^ 2 := mul_le_mul_of_nonneg_left hzsq hcBudget.le
    refine ⟨hLc, ?_, ?_⟩
    · intro i
      exact lt_of_le_of_lt (hδle i) (lt_of_le_of_lt hLc hCphalf)
    · exact lt_of_lt_of_le (lt_of_le_of_lt hLc hCpcBudget) hBudgetScale
  exact ⟨hP, hnormalized.1, hPiInt, hδeq, hLidentity, hLi, hδ0, hL0,
    hRate, hzero, hstrict⟩

end

end Shao.OQ6.IIDSourceStrictMomentBudgets
