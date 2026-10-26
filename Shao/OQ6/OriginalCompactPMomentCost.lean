import Shao.OQ6.OriginalCompactExpectationFees
import Shao.OQ6.ActualPhysicalCompactCDF
import Shao.OQ6.ActualQuadraticTiltMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false

universe u

namespace Shao.OQ6.OriginalCompactPMomentCost

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

/- Original p51 S26-S27 analytic budget only. The p-moment premise is explicit.
   Preserve the original n/n-1/n-2 statistics, named B1 budgets and continuous cap.
   Shao-Zhou (2016) attribution and inherited p54 repair boundaries remain;
   no CDF, source application, atom/zero-denominator, S11, general S15,
   DC, full OQ56 or novelty conclusion is claimed by this consumer. -/

private theorem compact_rpow_le_eight
    (p z : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.rpow (1 + z) p ≤ 8 := by
  calc
    Real.rpow (1 + z) p ≤ Real.rpow 2 p :=
      Real.rpow_le_rpow (by linarith only [hz])
        (by linarith only [hz1]) (by linarith only [hp2])
    _ ≤ Real.rpow 2 3 :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hp3
    _ = (2 : ℝ) ^ 3 := Real.rpow_natCast 2 3
    _ = 8 := by norm_num

theorem actual_original_compact_pmoment_cost
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (hgp : Integrable (fun o => Real.rpow |∫ y, h o y ∂μ| p) μ)
    (n : ℕ) (hn : 4 ≤ n)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
    let rho : ℝ := Real.sqrt v
    let sigma : ℝ := 1 + rho
    let N : ℝ := Real.sqrt (n : ℝ)
    let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let projectionTest : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Shao.truncationF ((1 + z) * (g (ξ i) / N))
    let Lcompact : ℝ :=
      ∑ i : Fin n, ∫ ξ, projectionTest ξ i ∂P₀
    let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      min (|g (ξ i)| / N) (1 / (1 + z))
    let D : (Fin n → Ω) → ℝ :=
      Shao.OQ5.P51.residualStatisticD n r
    let Ddel : (Fin n → Ω) → Fin n → ℝ :=
      Shao.OQ5.P51.residualStatisticDDeleted n r
    let J : (Fin n → Ω) → ℝ :=
      Shao.OQ5.P51.residualEnergyJ n r
    let Jdel : (Fin n → Ω) → Fin n → ℝ :=
      Shao.OQ5.P51.residualEnergyJDeleted n r
    let A : (Fin n → Ω) → ℝ := fun ξ => |D ξ|
    let Adel : (Fin n → Ω) → Fin n → ℝ := fun ξ i => |Ddel ξ i|
    let B₁ : (Fin n → Ω) → ℝ :=
      Shao.OQ5.P51.studentizerClipBudget n r C₀ rho 1
    let B₁del : (Fin n → Ω) → Fin n → ℝ :=
      Shao.OQ5.P51.studentizerClipBudgetDeleted n r C₀ rho 1
    let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      cap ξ i * (|A ξ - Adel ξ i| + z * |B₁ ξ - B₁del ξ i|)
    let residualFee : ℝ :=
      (∫ ξ, A ξ ∂P₀) + z * (∫ ξ, B₁ ξ ∂P₀) +
        ∑ i : Fin n, ∫ ξ, deletedTest ξ i ∂P₀
    let sourceCost : ℝ := Lcompact + residualFee
    (∀ i : Fin n, Integrable (fun ξ => projectionTest ξ i) P₀) ∧
      Lcompact = (n : ℝ) *
        (∫ o, Shao.truncationF ((1 + z) * (g o / N)) ∂μ) ∧
      0 ≤ Lcompact ∧
      Lcompact ≤ (1 + z) ^ 2 ∧
      Lcompact ≤ 4 ∧
      (∀ ξ : Fin n → Ω,
        B₁ ξ = C₀ * (sigma / N + J ξ / (sigma * N))) ∧
      (∀ (ξ : Fin n → Ω) (i : Fin n),
        B₁del ξ i = C₀ * (sigma / N + Jdel ξ i / (sigma * N))) ∧
      Integrable A P₀ ∧
      (∀ i : Fin n, Integrable (fun ξ => Adel ξ i) P₀) ∧
      Integrable B₁ P₀ ∧
      (∀ i : Fin n, Integrable (fun ξ => B₁del ξ i) P₀) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => cap ξ i * |A ξ - Adel ξ i|) P₀) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => cap ξ i * |B₁ ξ - B₁del ξ i|) P₀) ∧
      (∀ i : Fin n, Integrable (fun ξ => deletedTest ξ i) P₀) ∧
      residualFee ≤
        128 * (1 + C₀) * (1 + rho + rho ^ 2) / N ∧
      sourceCost ≤ Lcompact +
        128 * (1 + C₀) * (1 + rho + rho ^ 2) / N ∧
      0 ≤ β ∧
      Integrable (fun o => Shao.truncationF ((1 + z) * (g o / N))) μ ∧
      Lcompact ≤ β * Real.rpow (1 + z) p /
        Real.rpow (n : ℝ) ((p - 2) / 2) ∧
      Lcompact ≤ 8 * β / Real.rpow (n : ℝ) ((p - 2) / 2) ∧
      sourceCost ≤ 8 * β / Real.rpow (n : ℝ) ((p - 2) / 2) +
        128 * (1 + C₀) * (1 + rho + rho ^ 2) / N := by
  classical
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
  let rho : ℝ := Real.sqrt v
  let sigma : ℝ := 1 + rho
  let N : ℝ := Real.sqrt (n : ℝ)
  let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let projectionTest : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Shao.truncationF ((1 + z) * (g (ξ i) / N))
  let Lcompact : ℝ := ∑ i : Fin n, ∫ ξ, projectionTest ξ i ∂P₀
  let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    min (|g (ξ i)| / N) (1 / (1 + z))
  let D : (Fin n → Ω) → ℝ := Shao.OQ5.P51.residualStatisticD n r
  let Ddel : (Fin n → Ω) → Fin n → ℝ :=
    Shao.OQ5.P51.residualStatisticDDeleted n r
  let J : (Fin n → Ω) → ℝ := Shao.OQ5.P51.residualEnergyJ n r
  let Jdel : (Fin n → Ω) → Fin n → ℝ :=
    Shao.OQ5.P51.residualEnergyJDeleted n r
  let A : (Fin n → Ω) → ℝ := fun ξ => |D ξ|
  let Adel : (Fin n → Ω) → Fin n → ℝ := fun ξ i => |Ddel ξ i|
  let B₁ : (Fin n → Ω) → ℝ :=
    Shao.OQ5.P51.studentizerClipBudget n r C₀ rho 1
  let B₁del : (Fin n → Ω) → Fin n → ℝ :=
    Shao.OQ5.P51.studentizerClipBudgetDeleted n r C₀ rho 1
  let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    cap ξ i * (|A ξ - Adel ξ i| + z * |B₁ ξ - B₁del ξ i|)
  let residualFee : ℝ :=
    (∫ ξ, A ξ ∂P₀) + z * (∫ ξ, B₁ ξ ∂P₀) +
      ∑ i : Fin n, ∫ ξ, deletedTest ξ i ∂P₀
  let sourceCost : ℝ := Lcompact + residualFee
  change (∀ i : Fin n, Integrable (fun ξ => projectionTest ξ i) P₀) ∧
    Lcompact = (n : ℝ) *
      (∫ o, Shao.truncationF ((1 + z) * (g o / N)) ∂μ) ∧
    0 ≤ Lcompact ∧
    Lcompact ≤ (1 + z) ^ 2 ∧
    Lcompact ≤ 4 ∧
    (∀ ξ : Fin n → Ω,
      B₁ ξ = C₀ * (sigma / N + J ξ / (sigma * N))) ∧
    (∀ (ξ : Fin n → Ω) (i : Fin n),
      B₁del ξ i = C₀ * (sigma / N + Jdel ξ i / (sigma * N))) ∧
    Integrable A P₀ ∧
    (∀ i : Fin n, Integrable (fun ξ => Adel ξ i) P₀) ∧
    Integrable B₁ P₀ ∧
    (∀ i : Fin n, Integrable (fun ξ => B₁del ξ i) P₀) ∧
    (∀ i : Fin n, Integrable
      (fun ξ => cap ξ i * |A ξ - Adel ξ i|) P₀) ∧
    (∀ i : Fin n, Integrable
      (fun ξ => cap ξ i * |B₁ ξ - B₁del ξ i|) P₀) ∧
    (∀ i : Fin n, Integrable (fun ξ => deletedTest ξ i) P₀) ∧
    residualFee ≤
      128 * (1 + C₀) * (1 + rho + rho ^ 2) / N ∧
    sourceCost ≤ Lcompact +
      128 * (1 + C₀) * (1 + rho + rho ^ 2) / N ∧
    0 ≤ β ∧
    Integrable (fun o => Shao.truncationF ((1 + z) * (g o / N))) μ ∧
    Lcompact ≤ β * Real.rpow (1 + z) p /
      Real.rpow (n : ℝ) ((p - 2) / 2) ∧
    Lcompact ≤ 8 * β / Real.rpow (n : ℝ) ((p - 2) / 2) ∧
    sourceCost ≤ 8 * β / Real.rpow (n : ℝ) ((p - 2) / 2) +
      128 * (1 + C₀) * (1 + rho + rho ^ 2) / N
  have hbase :=
    Shao.OQ6.OriginalCompactExpectationFees.actual_original_compact_expectation_fees
      μ h hh hh2 hhsymm hcenter hprojectionsecond n hn z hz hz1 C₀ hC₀
  change (∀ i : Fin n, Integrable (fun ξ => projectionTest ξ i) P₀) ∧
    Lcompact = (n : ℝ) *
      (∫ o, Shao.truncationF ((1 + z) * (g o / N)) ∂μ) ∧
    0 ≤ Lcompact ∧
    Lcompact ≤ (1 + z) ^ 2 ∧
    Lcompact ≤ 4 ∧
    (∀ ξ : Fin n → Ω,
      B₁ ξ = C₀ * (sigma / N + J ξ / (sigma * N))) ∧
    (∀ (ξ : Fin n → Ω) (i : Fin n),
      B₁del ξ i = C₀ * (sigma / N + Jdel ξ i / (sigma * N))) ∧
    Integrable A P₀ ∧
    (∀ i : Fin n, Integrable (fun ξ => Adel ξ i) P₀) ∧
    Integrable B₁ P₀ ∧
    (∀ i : Fin n, Integrable (fun ξ => B₁del ξ i) P₀) ∧
    (∀ i : Fin n, Integrable
      (fun ξ => cap ξ i * |A ξ - Adel ξ i|) P₀) ∧
    (∀ i : Fin n, Integrable
      (fun ξ => cap ξ i * |B₁ ξ - B₁del ξ i|) P₀) ∧
    (∀ i : Fin n, Integrable (fun ξ => deletedTest ξ i) P₀) ∧
    residualFee ≤
      128 * (1 + C₀) * (1 + rho + rho ^ 2) / N ∧
    sourceCost ≤ Lcompact +
      128 * (1 + C₀) * (1 + rho + rho ^ 2) / N at hbase
  rcases hbase with
    ⟨hprojectionL1, hLidentity, hLnonneg, hLsquare, hLfour,
      hBformula, hBdelformula, hAint, hAdelint, hBint, hBdelint,
      hAcapint, hBcapint, hdeletedint, hresidual, hsource⟩
  have hn3 : 3 ≤ n := le_trans (by norm_num : 3 ≤ 4) hn
  have hn1 : 1 ≤ n := le_trans (by norm_num : 1 ≤ 4) hn
  have hnposNat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 4) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
  have hactual :=
    Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
      μ h hh hh2 hhsymm hcenter hprojectionsecond n hn3 0
      (by norm_num) (by positivity)
  have hgm : Measurable g := hactual.1
  have hg2 : MemLp g 2 μ := hactual.2.1
  have hnormalized :=
    Shao.OQ6.ActualPhysicalCompactCDF.normalized_observation_truncation_budget_le_rpow_moment
      μ g hgm hg2 p hp2.le hp3 hgp n hn1 z hz
  rcases hnormalized with ⟨hscalarL1, _, hnormalizedRate⟩
  change Integrable (fun o => Shao.truncationF ((1 + z) * (g o / N))) μ
    at hscalarL1
  change (n : ℝ) *
      (∫ o, Shao.truncationF ((1 + z) * (g o / N)) ∂μ) ≤
    β * Real.rpow (1 + z) p / Real.rpow (n : ℝ) ((p - 2) / 2)
    at hnormalizedRate
  have hbeta : 0 ≤ β := by
    dsimp only [β]
    exact integral_nonneg (fun o => Real.rpow_nonneg (abs_nonneg (g o)) p)
  have hden : 0 < Real.rpow (n : ℝ) ((p - 2) / 2) :=
    Real.rpow_pos_of_pos hnpos _
  have hfactor : Real.rpow (1 + z) p ≤ 8 :=
    compact_rpow_le_eight p z hp2 hp3 hz hz1
  have hLmoment : Lcompact ≤
      β * Real.rpow (1 + z) p / Real.rpow (n : ℝ) ((p - 2) / 2) := by
    calc
      Lcompact = (n : ℝ) *
          (∫ o, Shao.truncationF ((1 + z) * (g o / N)) ∂μ) := hLidentity
      _ ≤ β * Real.rpow (1 + z) p /
          Real.rpow (n : ℝ) ((p - 2) / 2) := hnormalizedRate
  have hnumerator : β * Real.rpow (1 + z) p ≤ 8 * β := by
    calc
      β * Real.rpow (1 + z) p ≤ β * 8 :=
        mul_le_mul_of_nonneg_left hfactor hbeta
      _ = 8 * β := mul_comm _ _
  have hLmomentEight : Lcompact ≤
      8 * β / Real.rpow (n : ℝ) ((p - 2) / 2) :=
    hLmoment.trans (div_le_div_of_nonneg_right hnumerator hden.le)
  have hcost : sourceCost ≤
      8 * β / Real.rpow (n : ℝ) ((p - 2) / 2) +
        128 * (1 + C₀) * (1 + rho + rho ^ 2) / N := by
    calc
      sourceCost = Lcompact + residualFee := rfl
      _ ≤ 8 * β / Real.rpow (n : ℝ) ((p - 2) / 2) +
          128 * (1 + C₀) * (1 + rho + rho ^ 2) / N :=
        add_le_add hLmomentEight hresidual
  exact ⟨hprojectionL1, hLidentity, hLnonneg, hLsquare, hLfour,
    hBformula, hBdelformula, hAint, hAdelint, hBint, hBdelint,
    hAcapint, hBcapint, hdeletedint, hresidual, hsource,
    hbeta, hscalarL1, hLmoment, hLmomentEight, hcost⟩

end

end Shao.OQ6.OriginalCompactPMomentCost
