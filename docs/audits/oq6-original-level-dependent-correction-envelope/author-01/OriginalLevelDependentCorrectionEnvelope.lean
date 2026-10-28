import Shao.OQ6.OriginalLevelDependentClippedSourcePackage
import Shao.OQ6.OriginalClippedCostIntegrability
import Shao.OQ6.LiteralDeletedRemainderEnvelope

set_option autoImplicit false

universe u

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology MeasureTheory
open Shao.OQ5.P51

namespace Shao.OQ6.OriginalLevelDependentCorrectionEnvelope

noncomputable section

theorem actual_original_level_dependent_correction_envelope
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond : (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 4 ≤ n)
    (z : ℝ) (hz : 1 ≤ z)
    (hwindow : z ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ))) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
    let rho : ℝ := Real.sqrt v
    let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let N : ℝ := Real.sqrt (n : ℝ)
    let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
    let D : (Fin n → Ω) → ℝ := residualStatisticD n r
    let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
    let Ddelete : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
    let Jdelete : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
    let A : (Fin n → Ω) → ℝ := fun ζ => |D ζ|
    let Adelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ => |Ddelete ζ i|
    let B : (Fin n → Ω) → ℝ := studentizerClipBudget n r 512 rho z
    let Bdelete : Fin n → (Fin n → Ω) → ℝ :=
      fun i ζ => studentizerClipBudgetDeleted n r 512 rho z ζ i
    let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho z
    let V : (Fin n → Ω) → ℝ := fun ζ => Real.sqrt (∑ j : Fin n, (ξ0 j ζ) ^ 2)
    let Vdelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, (ξ0 j ζ) ^ 2)
    let H : (Fin n → Ω) → ℝ := fun ζ => (1 + V ζ) * (N + z * Real.sqrt (1 + B ζ))
    let Hdelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ =>
      (1 + Vdelete i ζ) * (N + z * Real.sqrt (1 + Bdelete i ζ))
    let M : ℝ → (Fin n → Ω) → ℝ := fun ε ζ => 4 * ε * N * H ζ
    let Mdelete : ℝ → Fin n → (Fin n → Ω) → ℝ := fun ε i ζ =>
      4 * ε * N * Hdelete i ζ
    let κ : Fin n → ℝ := fun i =>
      4 * N * ((∫ ζ, H ζ ∂P) + (∫ ζ, Hdelete i ζ ∂P))
    let Δ : ℝ → Fin n → (Fin n → Ω) → ℝ := fun ε i ζ =>
      (A ζ + M ε ζ) - (Adelete i ζ + Mdelete ε i ζ) - (A ζ - Adelete i ζ)
    MemLp D 2 P ∧
    (∀ i : Fin n, MemLp (fun ζ => Ddelete ζ i) 2 P) ∧
    Integrable J P ∧ (∀ i : Fin n, Integrable (fun ζ => Jdelete ζ i) P) ∧
    Integrable A P ∧ (∀ i : Fin n, Integrable (Adelete i) P) ∧
    Integrable B P ∧ (∀ i : Fin n, Integrable (Bdelete i) P) ∧ Integrable e P ∧
    (∀ ζ : Fin n → Ω, 0 ≤ A ζ ∧ 0 ≤ B ζ ∧ |e ζ| ≤ B ζ) ∧
    (∀ (i : Fin n) (ζ : Fin n → Ω), 0 ≤ Adelete i ζ ∧ 0 ≤ Bdelete i ζ) ∧
    (∀ i : Fin n, Measurable (ξ0 i) ∧ MemLp (ξ0 i) 2 P ∧ (∫ ζ, ξ0 i ζ ∂P) = 0) ∧
    (∑ i : Fin n, ∫ ζ, (ξ0 i ζ) ^ 2 ∂P) = 1 ∧
    (∀ ζ : Fin n → Ω, V ζ = projectionV n g ζ) ∧
    Measurable H ∧ Integrable H P ∧
    (∀ i : Fin n, Measurable (Hdelete i) ∧ Integrable (Hdelete i) P) ∧
    (∀ ζ : Fin n → Ω, 0 < H ζ) ∧
    (∀ (i : Fin n) (ζ : Fin n → Ω), 0 < Hdelete i ζ) ∧
    (∀ ε : ℝ, Measurable (M ε) ∧ Integrable (M ε) P ∧
      Integrable (fun ζ => |M ε ζ|) P) ∧
    (∀ (ε : ℝ) (i : Fin n), Measurable (Mdelete ε i) ∧ Integrable (Mdelete ε i) P ∧
      Integrable (fun ζ => |Mdelete ε i ζ|) P) ∧
    (∀ ε : ℝ, 0 ≤ ε → ∀ ζ : Fin n → Ω,
      0 ≤ M ε ζ ∧ ∀ i : Fin n, 0 ≤ Mdelete ε i ζ) ∧
    (∀ i : Fin n, 0 ≤ κ i) ∧
    (∀ (ε : ℝ) (i : Fin n),
      (∫ ζ, M ε ζ ∂P) + (∫ ζ, Mdelete ε i ζ ∂P) = ε * κ i) ∧
    (∀ (ε : ℝ) (i : Fin n),
      (∫ ζ, |M ε ζ| ∂P) + (∫ ζ, |Mdelete ε i ζ| ∂P) = |ε| * κ i) ∧
    (∀ (ε : ℝ) (i : Fin n) (ζ : Fin n → Ω),
      Δ ε i ζ = M ε ζ - Mdelete ε i ζ) ∧
    (∀ (ε : ℝ) (i : Fin n) (ζ : Fin n → Ω),
      |Δ ε i ζ| ≤ |M ε ζ| + |Mdelete ε i ζ|) ∧
    (∀ (ε : ℝ) (i : Fin n), Measurable (Δ ε i) ∧ Integrable (Δ ε i) P ∧
      Integrable (fun ζ => |Δ ε i ζ|) P ∧
      (∫ ζ, |Δ ε i ζ| ∂P) ≤ |ε| * κ i) ∧
    (∀ i : Fin n, Filter.Tendsto (fun ε : ℝ => ∫ ζ, |Δ ε i ζ| ∂P)
      (nhds (0 : ℝ)) (nhds (0 : ℝ)))
 := by
  classical
  intro g r v rho P N ξ0 D J Ddelete Jdelete A Adelete B Bdelete e V Vdelete
    H Hdelete M Mdelete κ Δ
  letI : IsProbabilityMeasure P :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ)))
  have hn1 : 1 ≤ n := Nat.le_trans (by norm_num) hn
  have hn3 : 3 ≤ n := Nat.le_trans (by norm_num) hn
  have hn4R : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR : (0 : ℝ) < (n : ℝ) := by linarith only [hn4R]
  have hN2 : N ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hnNe : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hC0 : (0 : ℝ) ≤ 512 := by norm_num
  have hz0 : (0 : ℝ) ≤ z := le_trans (by norm_num : (0 : ℝ) ≤ 1) hz
  have hrho : 0 ≤ rho := Real.sqrt_nonneg v
  rcases Shao.OQ6.OriginalClippedCostIntegrability.actual_original_clipped_cost_integrability
      μ h hh hh2 hhsymm hcenter hprojectionsecond n hn 512 hC0 with
    ⟨hD2, hDdelete2, hJI, hJdeleteI, hAI, hAdeleteI, _⟩
  rcases Shao.OQ6.OriginalLevelDependentClippedSourcePackage.actual_original_level_dependent_clipped_source_package
      μ h hh hh2 hhsymm hcenter hprojectionsecond n hn z hz hwindow with
    ⟨_, _, _, _, _, hBm, _, hem, _, _, _, _, _, _, hglobal, _, _,
      hdeletes, _⟩
  have hBI : Integrable B P := by
    change Integrable (fun ζ : Fin n → Ω =>
      512 * (((1 + rho) * z) / N + J ζ / ((1 + rho) * z * N))) P
    exact ((integrable_const (((1 + rho) * z) / N)).add
      (hJI.div_const ((1 + rho) * z * N))).const_mul 512
  have hBdeleteI (i : Fin n) : Integrable (Bdelete i) P := by
    change Integrable (fun ζ : Fin n → Ω =>
      512 * (((1 + rho) * z) / N + Jdelete ζ i / ((1 + rho) * z * N))) P
    exact ((integrable_const (((1 + rho) * z) / N)).add
      ((hJdeleteI i).div_const ((1 + rho) * z * N))).const_mul 512
  have hFullBounds (ζ : Fin n → Ω) :
      0 ≤ A ζ ∧ 0 ≤ B ζ ∧ |e ζ| ≤ B ζ := by
    exact ⟨abs_nonneg _,
      studentizerClipBudget_nonneg n r 512 rho z ζ hC0 hrho hz0,
      (hglobal ζ).2.1⟩
  have hDeletedBounds (i : Fin n) (ζ : Fin n → Ω) :
      0 ≤ Adelete i ζ ∧ 0 ≤ Bdelete i ζ := by
    exact (clippedDeletion_envelopes_nonneg n r 512 rho z ζ i
      hC0 hrho hz0).2.2
  have heI : Integrable e P := by
    apply hBI.mono' hem.aestronglyMeasurable
    exact ae_of_all P (fun ζ : Fin n → Ω => by
      simpa only [Real.norm_eq_abs] using (hFullBounds ζ).2.2)
  have hBdeleteM (i : Fin n) : Measurable (Bdelete i) :=
    (hdeletes i).2.2.2.2.1
  have hwindow0 : (0 : ℝ) ≤ Real.sqrt (n : ℝ) /
      (2 * Real.exp (1 / 2 : ℝ)) :=
    div_nonneg (Real.sqrt_nonneg (n : ℝ))
      (mul_nonneg (by norm_num) (Real.exp_pos (1 / 2 : ℝ)).le)
  rcases Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
      μ h hh hh2 hhsymm hcenter hprojectionsecond n hn3 0 (le_refl 0) hwindow0 with
    ⟨hgm, hg2, hgmean, hgsecond, _⟩
  have hcoord (i : Fin n) :
      MeasurePreserving (fun ζ : Fin n → Ω => ζ i) P μ :=
    measurePreserving_eval (μ := fun _ : Fin n => μ) i
  have hpull (i : Fin n) (f : Ω → ℝ) (hf : Measurable f) :
      (∫ ζ, f (ζ i) ∂P) = ∫ o, f o ∂μ := by
    calc
      _ = ∫ o, f o ∂P.map (fun ζ : Fin n → Ω => ζ i) :=
        (integral_map (hcoord i).measurable.aemeasurable hf.aestronglyMeasurable).symm
      _ = _ := by rw [(hcoord i).map_eq]
  have hξm (i : Fin n) : Measurable (ξ0 i) :=
    (hgm.comp (measurable_pi_apply i)).div_const N
  have hξ2 (i : Fin n) : MemLp (ξ0 i) 2 P := by
    simpa only [ξ0, div_eq_mul_inv, Function.comp_def] using
      ((hg2.comp_measurePreserving (hcoord i)).mul_const N⁻¹)
  have hξmean (i : Fin n) : (∫ ζ, ξ0 i ζ ∂P) = 0 := by
    change (∫ ζ, g (ζ i) / N ∂P) = 0
    rw [integral_div, hpull i g hgm, hgmean, zero_div]
  have hξsecond (i : Fin n) : (∫ ζ, (ξ0 i ζ) ^ 2 ∂P) = 1 / (n : ℝ) := by
    change (∫ ζ, (g (ζ i) / N) ^ 2 ∂P) = 1 / (n : ℝ)
    simp_rw [div_pow]
    rw [integral_div, hpull i (fun o => g o ^ 2) (hgm.pow_const 2), hgsecond, hN2]
  have hξenergy : (∑ i : Fin n, ∫ ζ, (ξ0 i ζ) ^ 2 ∂P) = 1 := by
    simp_rw [hξsecond]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hnNe]
  have hVeq (ζ : Fin n → Ω) : V ζ = projectionV n g ζ := by
    change Real.sqrt (∑ i : Fin n, (g (ζ i) / N) ^ 2) =
      Real.sqrt ((∑ i : Fin n, (g (ζ i)) ^ 2) / (n : ℝ))
    congr 1
    simp only [div_pow, ← Finset.sum_div, hN2]
  rcases Shao.OQ6.LiteralDeletedRemainderEnvelope.literal_deleted_remainder_envelope_spec
      P n hn1 ξ0 hξm hξ2 hξenergy B Bdelete hBm hBdeleteM
      (fun ζ : Fin n → Ω => (hFullBounds ζ).2.1)
      (fun (i : Fin n) (ζ : Fin n → Ω) => (hDeletedBounds i ζ).2)
      hBI hBdeleteI z hz0 with
    ⟨_, _, _, _, _, _, _, hHm, hHI, hHdelete, hHpos, hHdeletePos,
      hMm, hMI, hMabsI, hMnonneg, _, _, _, _, hκnonneg, hPairIntegral,
      hPairAbsIntegral, _, _, _, _, hΔeq, hΔabs, _, hΔspec, hΔI, hΔlimit⟩
  exact ⟨hD2, hDdelete2, hJI, hJdeleteI, hAI, hAdeleteI, hBI, hBdeleteI,
    heI, hFullBounds, hDeletedBounds,
    (fun i : Fin n => ⟨hξm i, hξ2 i, hξmean i⟩), hξenergy, hVeq,
    hHm, hHI, hHdelete, hHpos, hHdeletePos,
    (fun ε : ℝ => ⟨(hMm ε).1, (hMI ε).1, (hMabsI ε).1⟩),
    (fun (ε : ℝ) (i : Fin n) =>
      ⟨(hMm ε).2 i, (hMI ε).2 i, (hMabsI ε).2 i⟩),
    hMnonneg, hκnonneg, hPairIntegral, hPairAbsIntegral,
    hΔeq A Adelete, hΔabs A Adelete,
    (fun (ε : ℝ) (i : Fin n) =>
      ⟨(hΔspec A Adelete ε i).1, (hΔspec A Adelete ε i).2.1,
        (hΔspec A Adelete ε i).2.2, hΔI A Adelete ε i⟩),
    hΔlimit A Adelete⟩

end

end Shao.OQ6.OriginalLevelDependentCorrectionEnvelope
