import Shao.OQ6.UntiltedCompactCost
import Shao.OQ5.P51.ClippedDeletionEnvelope
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

universe u

namespace Shao.OQ6.OriginalCompactExpectationFees

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

/- Original p51 is an UNCERTIFIED_REPAIR_CANDIDATE with external
   Shao-Zhou (2016) attribution and inherited p54 repair boundaries.
   This module is a local, not-yet-kernel-checked implementation candidate
   for the untilted combined compact expectation fee budget only.
   Sharp individual rho/rho^2 fees, the p-moment rate of Lcompact,
   CDF/source Theorem 2.2, S11, general S15, DC and full OQ56 remain open. -/

private theorem original_compact_denominator_control
    (n : ℕ) (hn : 4 ≤ n) :
    let q : ℝ := (n : ℝ)
    let N : ℝ := Real.sqrt q
    let kappa : ℝ := (q / (q - 2)) ^ 2
    0 < q ∧ 0 < q - 2 ∧ 0 < N ∧
      1 ≤ kappa ∧ kappa ≤ 4 := by
  dsimp only
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hq : 0 < (n : ℝ) := by linarith only [hnR]
  have hq2 : 0 < (n : ℝ) - 2 := by linarith only [hnR]
  have hN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hq
  have hratio1 : (1 : ℝ) ≤ (n : ℝ) / ((n : ℝ) - 2) :=
    (le_div_iff₀ hq2).2 (by linarith only [hnR])
  have hratio2 : (n : ℝ) / ((n : ℝ) - 2) ≤ 2 :=
    (div_le_iff₀ hq2).2 (by linarith only [hnR])
  refine ⟨hq, hq2, hN, ?_, ?_⟩
  · nlinarith only [hratio1,
      sq_nonneg ((n : ℝ) / ((n : ℝ) - 2) - 1)]
  · have hproduct :
        0 ≤ (2 - (n : ℝ) / ((n : ℝ) - 2)) *
          (2 + (n : ℝ) / ((n : ℝ) - 2)) :=
      mul_nonneg (by linarith only [hratio2])
        (by linarith only [hratio1])
    nlinarith only [hproduct]

private theorem original_compact_budget_shift
    (q N sigma C₀ L : ℝ)
    (hq : q ≠ 0) (hq2 : q - 2 ≠ 0)
    (hN : N ≠ 0) (hsigma : sigma ≠ 0) :
    let kappa : ℝ := (q / (q - 2)) ^ 2
    let Cprime : ℝ := C₀ * kappa
    let delta : ℝ := (Cprime - C₀) * sigma / N
    C₀ * (sigma / N + (L / (q - 2) ^ 2) / (sigma * N)) =
      Cprime * (sigma / N + L / (sigma * (q ^ 2 * N))) - delta := by
  dsimp only
  field_simp [hq, hq2, hN, hsigma] <;> ring

private theorem original_compact_reparameterized_bound
    (C₀ rho z N kappa : ℝ)
    (hC₀ : 0 ≤ C₀) (hrho : 0 ≤ rho)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hN : 0 < N)
    (hkappa1 : 1 ≤ kappa) (hkappa4 : kappa ≤ 4) :
    16 * (1 + C₀ * kappa) * (1 + z) * (1 + rho) / N ≤
      128 * (1 + C₀) * (1 + rho + rho ^ 2) / N := by
  have hC : 1 + C₀ * kappa ≤ 4 * (1 + C₀) := by
    nlinarith only [hC₀,
      mul_nonneg hC₀ (sub_nonneg.mpr hkappa4)]
  have hzplus : 0 ≤ 1 + z := by linarith only [hz]
  have hzplus2 : 1 + z ≤ 2 := by linarith only [hz1]
  have hrhoplus : 0 ≤ 1 + rho := by linarith only [hrho]
  have hrhosq : 1 + rho ≤ 1 + rho + rho ^ 2 := by
    nlinarith only [sq_nonneg rho]
  have hnum :
      16 * (1 + C₀ * kappa) * (1 + z) * (1 + rho) ≤
        128 * (1 + C₀) * (1 + rho + rho ^ 2) := by
    calc
      16 * (1 + C₀ * kappa) * (1 + z) * (1 + rho) ≤
          16 * (4 * (1 + C₀)) * (1 + z) * (1 + rho) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hC (by norm_num)) hzplus) hrhoplus
      _ ≤ 16 * (4 * (1 + C₀)) * 2 * (1 + rho) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hzplus2 (by positivity)) hrhoplus
      _ = 128 * (1 + C₀) * (1 + rho) := by ring
      _ ≤ 128 * (1 + C₀) * (1 + rho + rho ^ 2) :=
        mul_le_mul_of_nonneg_left hrhosq (by positivity)
  exact div_le_div_of_nonneg_right hnum hN.le

theorem actual_original_compact_expectation_fees
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 4 ≤ n)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
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
        128 * (1 + C₀) * (1 + rho + rho ^ 2) / N := by
  classical
  dsimp only
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
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
  let q : ℝ := (n : ℝ)
  let kappa : ℝ := (q / (q - 2)) ^ 2
  let Cprime : ℝ := C₀ * kappa
  let delta : ℝ := (Cprime - C₀) * sigma / N
  let e : (Fin n → Ω) → Fin n → Fin n → ℝ :=
    fun ξ j k => r (ξ j) (ξ k)
  let F : (Fin n → Ω) → ℝ := fun ξ =>
    Shao.OQ5.P35.unorderedPairSum (e ξ)
  let Fdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Shao.OQ5.P35.unorderedPairSum
      (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i)
  let psi : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
    Shao.OQ6.ResidualDeletion.rowSum (e ξ) j
  let psidel : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ i j =>
    Shao.OQ6.ResidualDeletion.rowSum
      (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i) j
  let LambdaSq : (Fin n → Ω) → ℝ := fun ξ =>
    ∑ j : Fin n, psi ξ j ^ 2
  let LambdaDelSq : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    ∑ j : Fin n, psidel ξ i j ^ 2
  let Bprime : (Fin n → Ω) → ℝ := fun ξ =>
    Cprime * (sigma / N + LambdaSq ξ / (sigma * (q ^ 2 * N)))
  let Bprimedel : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Cprime * (sigma / N + LambdaDelSq ξ i / (sigma * (q ^ 2 * N)))
  let deletedTestPrime : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    cap ξ i * (|A ξ - Adel ξ i| + z * |Bprime ξ - Bprimedel ξ i|)
  let residualCostPrime : ℝ :=
    (∫ ξ, A ξ ∂P₀) + z * (∫ ξ, Bprime ξ ∂P₀) +
      ∑ i : Fin n, ∫ ξ, deletedTestPrime ξ i ∂P₀
  haveI : IsProbabilityMeasure P₀ := by
    dsimp only [P₀]
    infer_instance
  have hrho : 0 ≤ rho := Real.sqrt_nonneg v
  have hsigma : 0 < sigma := by
    dsimp only [sigma]
    linarith only [hrho]
  have hdenominators :
      0 < q ∧ 0 < q - 2 ∧ 0 < N ∧ 1 ≤ kappa ∧ kappa ≤ 4 :=
    original_compact_denominator_control n hn
  rcases hdenominators with ⟨hq, hq2, hN, hkappa1, hkappa4⟩
  have hCprime0 : 0 ≤ Cprime := by
    dsimp only [Cprime]
    exact mul_nonneg hC₀ (le_trans (by norm_num : (0 : ℝ) ≤ 1) hkappa1)
  have hCprimeGe : C₀ ≤ Cprime := by
    dsimp only [Cprime]
    nlinarith only [mul_nonneg hC₀ (sub_nonneg.mpr hkappa1)]
  have hdelta : 0 ≤ delta := by
    dsimp only [delta]
    exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr hCprimeGe) hsigma.le) hN.le
  have hn3 : 3 ≤ n := le_trans (by norm_num : 3 ≤ 4) hn
  have hOld :=
    Shao.OQ6.UntiltedCompactCost.actual_quadratic_compact_source_cost
      μ h hh hh2 hhsymm hcenter hprojectionsecond n hn3 z hz Cprime hCprime0
  change
    (∀ i : Fin n, Integrable (fun ξ => projectionTest ξ i) P₀) ∧
      Lcompact = (n : ℝ) *
        (∫ o, Shao.truncationF ((1 + z) * (g o / N)) ∂μ) ∧
      0 ≤ Lcompact ∧ Lcompact ≤ (1 + z) ^ 2 ∧
      Integrable A P₀ ∧
      (∀ i : Fin n, Integrable (fun ξ => Adel ξ i) P₀) ∧
      Integrable Bprime P₀ ∧
      (∀ i : Fin n, Integrable (fun ξ => Bprimedel ξ i) P₀) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => cap ξ i * |A ξ - Adel ξ i|) P₀) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => cap ξ i * |Bprime ξ - Bprimedel ξ i|) P₀) ∧
      (∀ i : Fin n, Integrable (fun ξ => deletedTestPrime ξ i) P₀) ∧
      residualCostPrime ≤ 16 * (1 + Cprime) * (1 + z) * sigma / N ∧
      Lcompact + residualCostPrime ≤
        Lcompact + 16 * (1 + Cprime) * (1 + z) * sigma / N at hOld
  rcases hOld with
    ⟨hProjectionInt, hProjectionId, hL0, hLBound, hAInt, hAdelInt,
      hBprimeInt, hBprimedelInt, hWeightedAInt, hWeightedBprimeInt,
      hDeletedPrimeInt, hPrimeBound, hPrimeSourceBound⟩
  have hJ (ξ : Fin n → Ω) : J ξ = LambdaSq ξ / (q - 2) ^ 2 :=
    Shao.OQ5.P51.residualEnergyJ_eq_rowSqSum n r ξ
  have hJdel (ξ : Fin n → Ω) (i : Fin n) :
      Jdel ξ i = LambdaDelSq ξ i / (q - 2) ^ 2 := by
    rfl
  have hBform (ξ : Fin n → Ω) :
      B₁ ξ = C₀ * (sigma / N + J ξ / (sigma * N)) := by
    simp only [B₁, Shao.OQ5.P51.studentizerClipBudget, sigma, N, J, mul_one]
  have hBdelForm (ξ : Fin n → Ω) (i : Fin n) :
      B₁del ξ i = C₀ * (sigma / N + Jdel ξ i / (sigma * N)) := by
    simp only [B₁del, Shao.OQ5.P51.studentizerClipBudgetDeleted,
      sigma, N, Jdel, mul_one]
  have hBshift (ξ : Fin n → Ω) : B₁ ξ = Bprime ξ - delta := by
    rw [hBform ξ, hJ ξ]
    exact original_compact_budget_shift q N sigma C₀ (LambdaSq ξ)
      hq.ne' hq2.ne' hN.ne' hsigma.ne'
  have hBdelShift (ξ : Fin n → Ω) (i : Fin n) :
      B₁del ξ i = Bprimedel ξ i - delta := by
    rw [hBdelForm ξ i, hJdel ξ i]
    exact original_compact_budget_shift q N sigma C₀ (LambdaDelSq ξ i)
      hq.ne' hq2.ne' hN.ne' hsigma.ne'
  have hBdiff (ξ : Fin n → Ω) (i : Fin n) :
      B₁ ξ - B₁del ξ i = Bprime ξ - Bprimedel ξ i := by
    rw [hBshift ξ, hBdelShift ξ i]
    ring
  have hBfun : B₁ = (fun ξ => Bprime ξ - delta) := by
    funext ξ
    exact hBshift ξ
  have hBdelFun (i : Fin n) :
      (fun ξ => B₁del ξ i) = (fun ξ => Bprimedel ξ i - delta) := by
    funext ξ
    exact hBdelShift ξ i
  have hBInt : Integrable B₁ P₀ := by
    rw [hBfun]
    exact hBprimeInt.sub (integrable_const delta)
  have hBdelInt (i : Fin n) : Integrable (fun ξ => B₁del ξ i) P₀ := by
    rw [hBdelFun i]
    exact (hBprimedelInt i).sub (integrable_const delta)
  have hWeightedBInt (i : Fin n) :
      Integrable (fun ξ => cap ξ i * |B₁ ξ - B₁del ξ i|) P₀ := by
    simpa only [hBdiff] using hWeightedBprimeInt i
  have hDeletedEq (ξ : Fin n → Ω) (i : Fin n) :
      deletedTest ξ i = deletedTestPrime ξ i := by
    dsimp only [deletedTest, deletedTestPrime]
    rw [hBdiff]
  have hDeletedInt (i : Fin n) :
      Integrable (fun ξ => deletedTest ξ i) P₀ := by
    simpa only [hDeletedEq] using hDeletedPrimeInt i
  have hBIntegral : (∫ ξ, B₁ ξ ∂P₀) = (∫ ξ, Bprime ξ ∂P₀) - delta := by
    rw [hBfun, integral_sub hBprimeInt (integrable_const delta)]
    simp only [integral_const, probReal_univ, one_smul]
  have hDeletedSum :
      (∑ i : Fin n, ∫ ξ, deletedTest ξ i ∂P₀) =
        ∑ i : Fin n, ∫ ξ, deletedTestPrime ξ i ∂P₀ := by
    simp_rw [hDeletedEq]
  have hFeeId : residualFee = residualCostPrime - z * delta := by
    dsimp only [residualFee, residualCostPrime]
    rw [hBIntegral, hDeletedSum]
    ring
  have hFeeLe : residualFee ≤ residualCostPrime := by
    rw [hFeeId]
    exact sub_le_self _ (mul_nonneg hz hdelta)
  have hResidualBound :
      residualFee ≤ 128 * (1 + C₀) * (1 + rho + rho ^ 2) / N := by
    exact le_trans hFeeLe (le_trans hPrimeBound
      (original_compact_reparameterized_bound C₀ rho z N kappa
        hC₀ hrho hz hz1 hN hkappa1 hkappa4))
  have hLfour : Lcompact ≤ 4 := by
    apply le_trans hLBound
    have hproduct : 0 ≤ (1 - z) * (3 + z) :=
      mul_nonneg (by linarith only [hz1]) (by linarith only [hz])
    nlinarith only [hproduct]
  exact ⟨hProjectionInt, hProjectionId, hL0, hLBound, hLfour,
    hBform, hBdelForm, hAInt, hAdelInt, hBInt, hBdelInt,
    hWeightedAInt, hWeightedBInt, hDeletedInt, hResidualBound,
    add_le_add (le_refl Lcompact) hResidualBound⟩

end

end Shao.OQ6.OriginalCompactExpectationFees
