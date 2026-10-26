import Shao.OQ5.P51.ClippedDeletionEnvelope
import Shao.OQ6.OriginalRhoTiltedMoments
import Shao.OQ6.RhoWeightedDeletionMoments
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace Shao.OQ6.OriginalClippedExpectationFees

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem four_fee_scalar_envelope
    (C rho y C0 N : ℝ)
    (hC : 1 ≤ C) (hrho : 0 ≤ rho) (hy : 1 ≤ y)
    (hC0 : 0 ≤ C0) (hN : 0 < N) :
    (8 * C ^ 2 * rho * y * (1 + y ^ 2) / N +
      C0 * ((1 + rho) * y ^ 3 +
        56 * C ^ 4 * rho ^ 2 * y * (1 + y ^ 2) / (1 + rho)) / N +
      4 * Real.sqrt 2 * C * rho * (1 + y) ^ 2 / N +
      96 * C ^ 2 * C0 * rho ^ 2 * (1 + y) ^ 2 / ((1 + rho) * N)) ≤
      (256 * C ^ 4 * (1 + C0)) *
        (1 + rho + rho ^ 2) * (1 + y) ^ 3 / N := by
  let A : ℝ := 1 + rho + rho ^ 2
  let Y : ℝ := (1 + y) ^ 3
  have hy0 : 0 ≤ y := by linarith
  have hC0pos : 0 ≤ C := by linarith
  have hsigma : 0 < 1 + rho := by linarith
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hY0 : 0 ≤ Y := by dsimp only [Y]; positivity
  have hrA : rho ≤ A := by dsimp only [A]; nlinarith [sq_nonneg rho]
  have hsA : 1 + rho ≤ A := by dsimp only [A]; nlinarith [sq_nonneg rho]
  have hr2A : rho ^ 2 ≤ A := by dsimp only [A]; linarith
  have hwY : y * (1 + y ^ 2) ≤ Y := by
    dsimp only [Y]
    nlinarith [sq_nonneg y]
  have hy3Y : y ^ 3 ≤ Y := by
    dsimp only [Y]
    nlinarith [sq_nonneg y]
  have hy2Y : (1 + y) ^ 2 ≤ Y := by
    dsimp only [Y]
    nlinarith [mul_nonneg (sq_nonneg (1 + y)) hy0]
  have hC21 : 1 ≤ C ^ 2 := by nlinarith [sq_nonneg (C - 1)]
  have hC41 : 1 ≤ C ^ 4 := by nlinarith [sq_nonneg (C ^ 2 - 1)]
  have hC24 : C ^ 2 ≤ C ^ 4 := by nlinarith [sq_nonneg (C ^ 2 - 1)]
  have hC14 : C ≤ C ^ 4 := by
    have hC12 : C ≤ C ^ 2 := by nlinarith [sq_nonneg (C - 1)]
    linarith
  have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
      Real.sqrt_nonneg (2 : ℝ)]
  have hrdivA : rho ^ 2 / (1 + rho) ≤ A := by
    apply (div_le_iff₀ hsigma).2
    nlinarith [mul_nonneg hA0 hrho]
  have hprod1 : rho * (y * (1 + y ^ 2)) ≤ A * Y :=
    mul_le_mul hrA hwY (by positivity) hA0
  have hprod3 : rho * (1 + y) ^ 2 ≤ A * Y :=
    mul_le_mul hrA hy2Y (sq_nonneg _) hA0
  have hprod4 : (rho ^ 2 / (1 + rho)) * (1 + y) ^ 2 ≤ A * Y :=
    mul_le_mul hrdivA hy2Y (sq_nonneg _) hA0
  have hprod2 : rho ^ 2 * y * (1 + y ^ 2) / (1 + rho) ≤ A * Y := by
    calc
      rho ^ 2 * y * (1 + y ^ 2) / (1 + rho) =
          (rho ^ 2 / (1 + rho)) * (y * (1 + y ^ 2)) := by ring
      _ ≤ A * Y := mul_le_mul hrdivA hwY (by positivity) hA0
  have h1 : 8 * C ^ 2 * rho * y * (1 + y ^ 2) ≤ 8 * C ^ 4 * A * Y := by
    calc
      8 * C ^ 2 * rho * y * (1 + y ^ 2) =
          (8 * C ^ 2) * (rho * (y * (1 + y ^ 2))) := by ring
      _ ≤ (8 * C ^ 2) * (A * Y) :=
        mul_le_mul_of_nonneg_left hprod1 (by positivity)
      _ ≤ (8 * C ^ 4) * (A * Y) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hC24 (by norm_num)) (mul_nonneg hA0 hY0)
      _ = 8 * C ^ 4 * A * Y := by ring
  have h2first : (1 + rho) * y ^ 3 ≤ C ^ 4 * A * Y := by
    calc
      (1 + rho) * y ^ 3 ≤ A * Y :=
        mul_le_mul hsA hy3Y (pow_nonneg hy0 _) hA0
      _ ≤ C ^ 4 * (A * Y) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hC41 (mul_nonneg hA0 hY0)
      _ = C ^ 4 * A * Y := by ring
  have h2second :
      56 * C ^ 4 * rho ^ 2 * y * (1 + y ^ 2) / (1 + rho) ≤
        56 * C ^ 4 * (A * Y) := by
    calc
      56 * C ^ 4 * rho ^ 2 * y * (1 + y ^ 2) / (1 + rho) =
          (56 * C ^ 4) * (rho ^ 2 * y * (1 + y ^ 2) / (1 + rho)) := by ring
      _ ≤ (56 * C ^ 4) * (A * Y) :=
        mul_le_mul_of_nonneg_left hprod2 (by positivity)
  have h2 :
      C0 * ((1 + rho) * y ^ 3 +
        56 * C ^ 4 * rho ^ 2 * y * (1 + y ^ 2) / (1 + rho)) ≤
        57 * C ^ 4 * C0 * A * Y := by
    calc
      C0 * ((1 + rho) * y ^ 3 +
          56 * C ^ 4 * rho ^ 2 * y * (1 + y ^ 2) / (1 + rho)) ≤
          C0 * (C ^ 4 * A * Y + 56 * C ^ 4 * (A * Y)) :=
        mul_le_mul_of_nonneg_left (add_le_add h2first h2second) hC0
      _ = 57 * C ^ 4 * C0 * A * Y := by ring
  have h3coeff : 4 * Real.sqrt 2 * C ≤ 8 * C ^ 4 := by
    calc
      4 * Real.sqrt 2 * C ≤ 4 * 2 * C :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt2 (by norm_num)) hC0pos
      _ ≤ 8 * C ^ 4 := by linarith
  have h3 :
      4 * Real.sqrt 2 * C * rho * (1 + y) ^ 2 ≤ 8 * C ^ 4 * A * Y := by
    calc
      4 * Real.sqrt 2 * C * rho * (1 + y) ^ 2 =
          (4 * Real.sqrt 2 * C) * (rho * (1 + y) ^ 2) := by ring
      _ ≤ (8 * C ^ 4) * (A * Y) :=
        mul_le_mul h3coeff hprod3 (by positivity) (by positivity)
      _ = 8 * C ^ 4 * A * Y := by ring
  have h4coeff : 96 * C ^ 2 * C0 ≤ 96 * C ^ 4 * C0 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hC24 (by norm_num)) hC0
  have h4 :
      96 * C ^ 2 * C0 * (rho ^ 2 / (1 + rho)) * (1 + y) ^ 2 ≤
        96 * C ^ 4 * C0 * A * Y := by
    calc
      96 * C ^ 2 * C0 * (rho ^ 2 / (1 + rho)) * (1 + y) ^ 2 =
          (96 * C ^ 2 * C0) * ((rho ^ 2 / (1 + rho)) * (1 + y) ^ 2) := by ring
      _ ≤ (96 * C ^ 4 * C0) * (A * Y) :=
        mul_le_mul h4coeff hprod4 (by positivity) (by positivity)
      _ = 96 * C ^ 4 * C0 * A * Y := by ring
  calc
    (8 * C ^ 2 * rho * y * (1 + y ^ 2) / N +
        C0 * ((1 + rho) * y ^ 3 +
          56 * C ^ 4 * rho ^ 2 * y * (1 + y ^ 2) / (1 + rho)) / N +
        4 * Real.sqrt 2 * C * rho * (1 + y) ^ 2 / N +
        96 * C ^ 2 * C0 * rho ^ 2 * (1 + y) ^ 2 / ((1 + rho) * N)) =
        (8 * C ^ 2 * rho * y * (1 + y ^ 2) +
          C0 * ((1 + rho) * y ^ 3 +
            56 * C ^ 4 * rho ^ 2 * y * (1 + y ^ 2) / (1 + rho)) +
          4 * Real.sqrt 2 * C * rho * (1 + y) ^ 2 +
          96 * C ^ 2 * C0 * (rho ^ 2 / (1 + rho)) * (1 + y) ^ 2) / N := by
      field_simp [ne_of_gt hN, ne_of_gt hsigma]
      <;> ring
    _ ≤ (8 * C ^ 4 * A * Y + 57 * C ^ 4 * C0 * A * Y +
          8 * C ^ 4 * A * Y + 96 * C ^ 4 * C0 * A * Y) / N :=
      div_le_div_of_nonneg_right
        (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) (le_of_lt hN)
    _ = (16 + 153 * C0) * (C ^ 4 * A * Y) / N := by ring
    _ ≤ (256 * (1 + C0)) * (C ^ 4 * A * Y) / N := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hN)
      exact mul_le_mul_of_nonneg_right (by linarith : 16 + 153 * C0 ≤ 256 * (1 + C0))
        (by positivity)
    _ = (256 * C ^ 4 * (1 + C0)) *
        (1 + rho + rho ^ 2) * (1 + y) ^ 3 / N := by
      dsimp only [A, Y]
      ring

theorem actual_quadratic_clipped_expectation_fees
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond : (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 4 ≤ n) (y : ℝ) (hy : 1 ≤ y)
    (hwindow : y ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ)))
    (C0 : ℝ) (hC0 : 0 ≤ C0) :
    let C : ℝ := Real.exp (1 / 2 : ℝ)
    let g : Ω → ℝ := fun o => ∫ z, h o z ∂μ
    let r : Ω → Ω → ℝ := fun o z => h o z - g o - g z
    let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
    let rho : ℝ := Real.sqrt v
    let sigma : ℝ := 1 + rho
    let a : ℝ := y / Real.sqrt (n : ℝ)
    let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
    let w : Ω → ℝ := fun o => Real.exp (φ o)
    let m : ℝ := ∫ o, w o ∂μ
    let I : ℝ := m ^ n
    let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let S : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, φ (ξ j)
    let Pₐ : Measure (Fin n → Ω) := P₀.tilted S
    let R : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Real.exp (∑ j ∈ Finset.univ.erase i, φ (ξ j)) / I
    let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i => min |a * g (ξ i)| 1
    let D : (Fin n → Ω) → ℝ := Shao.OQ5.P51.residualStatisticD n r
    let Ddel : (Fin n → Ω) → Fin n → ℝ := Shao.OQ5.P51.residualStatisticDDeleted n r
    let J : (Fin n → Ω) → ℝ := Shao.OQ5.P51.residualEnergyJ n r
    let Jdel : (Fin n → Ω) → Fin n → ℝ := Shao.OQ5.P51.residualEnergyJDeleted n r
    let B : (Fin n → Ω) → ℝ := Shao.OQ5.P51.studentizerClipBudget n r C0 rho y
    let Bdel : (Fin n → Ω) → Fin n → ℝ :=
      Shao.OQ5.P51.studentizerClipBudgetDeleted n r C0 rho y
    let fD : ℝ := y * (∫ ξ, |D ξ| ∂Pₐ)
    let fB : ℝ := y ^ 2 * (∫ ξ, B ξ ∂Pₐ)
    let fDdel : ℝ := ∑ i : Fin n,
      ∫ ξ, R ξ i * cap ξ i * abs (abs (D ξ) - abs (Ddel ξ i)) ∂P₀
    let fBdel : ℝ := y * (∑ i : Fin n,
      ∫ ξ, R ξ i * cap ξ i * abs (B ξ - Bdel ξ i) ∂P₀)
    let fee : ℝ := fD + fB + fDdel + fBdel
    let K : ℝ := 256 * C ^ 4 * (1 + C0)
    IsProbabilityMeasure Pₐ ∧
      Integrable (fun ξ => abs (D ξ)) Pₐ ∧
      Integrable B Pₐ ∧
      (∀ i : Fin n, Integrable
        (fun ξ => R ξ i * cap ξ i * abs (abs (D ξ) - abs (Ddel ξ i))) P₀) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => R ξ i * cap ξ i * abs (B ξ - Bdel ξ i)) P₀) ∧
      fD ≤ 8 * C ^ 2 * rho * y * (1 + y ^ 2) / Real.sqrt (n : ℝ) ∧
      fB ≤ C0 * (sigma * y ^ 3 +
        56 * C ^ 4 * rho ^ 2 * y * (1 + y ^ 2) / sigma) / Real.sqrt (n : ℝ) ∧
      fDdel ≤ 4 * Real.sqrt 2 * C * rho * (1 + y) ^ 2 / Real.sqrt (n : ℝ) ∧
      fBdel ≤ 96 * C ^ 2 * C0 * rho ^ 2 * (1 + y) ^ 2 /
        (sigma * Real.sqrt (n : ℝ)) ∧
      fee ≤ K * (1 + rho + rho ^ 2) * (1 + y) ^ 3 / Real.sqrt (n : ℝ) := by
  dsimp only
  let C : ℝ := Real.exp (1 / 2 : ℝ)
  let g : Ω → ℝ := fun o => ∫ z, h o z ∂μ
  let r : Ω → Ω → ℝ := fun o z => h o z - g o - g z
  let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
  let rho : ℝ := Real.sqrt v
  let sigma : ℝ := 1 + rho
  let a : ℝ := y / Real.sqrt (n : ℝ)
  let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
  let w : Ω → ℝ := fun o => Real.exp (φ o)
  let m : ℝ := ∫ o, w o ∂μ
  let I : ℝ := m ^ n
  let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let S : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, φ (ξ j)
  let Pₐ : Measure (Fin n → Ω) := P₀.tilted S
  let R : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Real.exp (∑ j ∈ Finset.univ.erase i, φ (ξ j)) / I
  let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i => min |a * g (ξ i)| 1
  let D : (Fin n → Ω) → ℝ := Shao.OQ5.P51.residualStatisticD n r
  let Ddel : (Fin n → Ω) → Fin n → ℝ := Shao.OQ5.P51.residualStatisticDDeleted n r
  let J : (Fin n → Ω) → ℝ := Shao.OQ5.P51.residualEnergyJ n r
  let Jdel : (Fin n → Ω) → Fin n → ℝ := Shao.OQ5.P51.residualEnergyJDeleted n r
  let B : (Fin n → Ω) → ℝ := Shao.OQ5.P51.studentizerClipBudget n r C0 rho y
  let Bdel : (Fin n → Ω) → Fin n → ℝ :=
    Shao.OQ5.P51.studentizerClipBudgetDeleted n r C0 rho y
  let fD : ℝ := y * (∫ ξ, |D ξ| ∂Pₐ)
  let fB : ℝ := y ^ 2 * (∫ ξ, B ξ ∂Pₐ)
  let fDdel : ℝ := ∑ i : Fin n,
    ∫ ξ, R ξ i * cap ξ i * abs (abs (D ξ) - abs (Ddel ξ i)) ∂P₀
  let fBdel : ℝ := y * (∑ i : Fin n,
    ∫ ξ, R ξ i * cap ξ i * abs (B ξ - Bdel ξ i) ∂P₀)
  let fee : ℝ := fD + fB + fDdel + fBdel
  let K : ℝ := 256 * C ^ 4 * (1 + C0)
  let N : ℝ := Real.sqrt (n : ℝ)
  let b : ℝ := sigma * y * N
  let q : ℝ := C0 / b
  let HJ : (Fin n → Ω) → Fin n → ℝ :=
    fun ξ i => R ξ i * cap ξ i * abs (J ξ - Jdel ξ i)
  let TJ : ℝ := ∑ i : Fin n, ∫ ξ, HJ ξ i ∂P₀
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN : 0 < N := by
    dsimp only [N]
    exact Real.sqrt_pos.mpr (by linarith)
  have hy0 : 0 ≤ y := by linarith
  have hypos : 0 < y := by linarith
  have hrho : 0 ≤ rho := Real.sqrt_nonneg v
  have hsigma : 0 < sigma := by dsimp only [sigma]; linarith
  have hb : 0 < b := by dsimp only [b]; positivity
  have hq : 0 ≤ q := div_nonneg hC0 (le_of_lt hb)
  have hC : 1 ≤ C := by
    dsimp only [C]
    exact Real.one_le_exp_iff.mpr (by norm_num)
  have h213 := Shao.OQ6.OriginalRhoTiltedMoments.actual_quadratic_rho_moments
    μ h hh hh2 hhsymm hcenter hprojectionsecond n hn y hy hwindow
  dsimp only at h213
  rcases h213 with ⟨_, _, _, _, _, hPa, _, _, _, _, _, hJL1raw,
    _, hDL1raw, _, _, _, _, _, _, _, hJboundraw, hDboundraw⟩
  haveI : IsProbabilityMeasure Pₐ := hPa
  have hJfun : J = (fun ξ : Fin n → Ω => ∑ i : Fin n,
      (Shao.OQ6.ResidualDeletion.rowSum
        (fun j k : Fin n => r (ξ j) (ξ k)) i / ((n : ℝ) - 2)) ^ 2) := by
    funext ξ
    dsimp only [J, Shao.OQ5.P51.residualEnergyJ]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Shao.OQ5.P51.residualU_eq_erased_row]
    rfl
  have hJdelfun : Jdel = (fun (ξ : Fin n → Ω) (i : Fin n) => ∑ j : Fin n,
      (Shao.OQ6.ResidualDeletion.rowSum
        (Shao.OQ6.ResidualDeletion.eraseIncident
          (fun k l : Fin n => r (ξ k) (ξ l)) i) j / ((n : ℝ) - 2)) ^ 2) := by
    funext ξ i
    simp only [Jdel, Shao.OQ5.P51.residualEnergyJDeleted,
      div_pow, ← Finset.sum_div]
  have hJL1 : Integrable J Pₐ := by
    rw [hJfun]
    exact hJL1raw
  have hDabsL1 : Integrable (fun ξ => abs (D ξ)) Pₐ := by
    simpa only [D, Shao.OQ5.P51.residualStatisticD,
      Shao.OQ6.CanonicalDoubleGhostScalarMoments.originalUpper,
      Shao.OQ5.P35.unorderedPairSum] using hDL1raw
  have hJmoment : (∫ ξ, J ξ ∂Pₐ) ≤
      56 * C ^ 4 * rho ^ 2 * (1 + y ^ 2) := by
    rw [hJfun]
    exact hJboundraw
  have hDmoment : (∫ ξ, abs (D ξ) ∂Pₐ) ≤
      8 * C ^ 2 * rho * (1 + y ^ 2) / N := by
    simpa only [D, N, Shao.OQ5.P51.residualStatisticD,
      Shao.OQ6.CanonicalDoubleGhostScalarMoments.originalUpper,
      Shao.OQ5.P35.unorderedPairSum] using hDboundraw
  have h214 := Shao.OQ6.RhoWeightedDeletionMoments.actual_quadratic_rho_weighted_deletion_bounds
    μ h hh hh2 hhsymm hcenter hprojectionsecond n hn y hy0 hwindow
  dsimp only at h214
  rcases h214 with ⟨_, _, _, _, _, _, _, hDdelL1raw,
    hDdelboundraw, hJdelL1raw, hJdelboundraw⟩
  have hDdelL1 : ∀ i : Fin n, Integrable
      (fun ξ => R ξ i * cap ξ i * abs (abs (D ξ) - abs (Ddel ξ i))) P₀ := by
    simpa only [D, Ddel, Shao.OQ5.P51.residualStatisticD,
      Shao.OQ5.P51.residualStatisticDDeleted,
      Shao.OQ6.CanonicalDoubleGhostScalarMoments.originalUpper,
      Shao.OQ5.P35.unorderedPairSum] using hDdelL1raw
  have hDdelFee : fDdel ≤
      4 * Real.sqrt 2 * C * rho * (1 + y) ^ 2 / N := by
    simpa only [fDdel, D, Ddel, N, Shao.OQ5.P51.residualStatisticD,
      Shao.OQ5.P51.residualStatisticDDeleted,
      Shao.OQ6.CanonicalDoubleGhostScalarMoments.originalUpper,
      Shao.OQ5.P35.unorderedPairSum] using hDdelboundraw
  have hJdelL1 : ∀ i : Fin n, Integrable (fun ξ => HJ ξ i) P₀ := by
    intro i
    dsimp only [HJ]
    rw [hJfun, hJdelfun]
    exact hJdelL1raw i
  have hTJ : TJ ≤ 96 * C ^ 2 * rho ^ 2 * (1 + y) ^ 2 := by
    dsimp only [TJ, HJ]
    rw [hJfun, hJdelfun]
    exact hJdelboundraw
  have hrsym : ∀ o z : Ω, r o z = r z o := by
    intro o z
    dsimp only [r]
    rw [hhsymm o z]
    ring
  have hBpoint : ∀ ξ : Fin n → Ω,
      B ξ = C0 * (sigma * y / N) + q * J ξ := by
    intro ξ
    dsimp only [B, J, Shao.OQ5.P51.studentizerClipBudget, q, b, N, sigma]
    ring
  have hBfun : B = (fun ξ : Fin n → Ω => C0 * (sigma * y / N) + q * J ξ) :=
    funext hBpoint
  have hBL1 : Integrable B Pₐ := by
    rw [hBfun]
    exact (integrable_const (C0 * (sigma * y / N))).add (hJL1.const_mul q)
  have hBmean : (∫ ξ, B ξ ∂Pₐ) =
      C0 * (sigma * y / N) + q * (∫ ξ, J ξ ∂Pₐ) := by
    rw [hBfun, integral_add (integrable_const _) (hJL1.const_mul q),
      integral_const_mul q]
    simp
  have hBdiff : ∀ (ξ : Fin n → Ω) (i : Fin n),
      abs (B ξ - Bdel ξ i) = q * abs (J ξ - Jdel ξ i) := by
    intro ξ i
    have hcost := Shao.OQ5.P51.clippedDeletion_cost_identities
      n r hrsym C0 rho y ξ i hn hC0 hrho hy
    dsimp only at hcost
    have hdiff := hcost.2.2.2.2.1
    change B ξ - Bdel ξ i = C0 * (J ξ - Jdel ξ i) / b at hdiff
    rw [hdiff, abs_div, abs_mul, abs_of_nonneg hC0, abs_of_pos hb]
    dsimp only [q]
    ring
  have hBW : ∀ (ξ : Fin n → Ω) (i : Fin n),
      R ξ i * cap ξ i * abs (B ξ - Bdel ξ i) = q * HJ ξ i := by
    intro ξ i
    rw [hBdiff]
    dsimp only [HJ]
    ring
  have hBdelL1 : ∀ i : Fin n, Integrable
      (fun ξ => R ξ i * cap ξ i * abs (B ξ - Bdel ξ i)) P₀ := by
    intro i
    have heq : (fun ξ : Fin n → Ω => R ξ i * cap ξ i * abs (B ξ - Bdel ξ i)) =
        (fun ξ : Fin n → Ω => q * HJ ξ i) := funext (fun ξ => hBW ξ i)
    rw [heq]
    exact (hJdelL1 i).const_mul q
  have hBdelIntegral : ∀ i : Fin n,
      (∫ ξ, R ξ i * cap ξ i * abs (B ξ - Bdel ξ i) ∂P₀) =
        q * (∫ ξ, HJ ξ i ∂P₀) := by
    intro i
    calc
      (∫ ξ, R ξ i * cap ξ i * abs (B ξ - Bdel ξ i) ∂P₀) =
          ∫ ξ, q * HJ ξ i ∂P₀ :=
        integral_congr_ae (Filter.Eventually.of_forall (fun ξ => hBW ξ i))
      _ = q * (∫ ξ, HJ ξ i ∂P₀) := integral_const_mul _ _
  have hDfee : fD ≤ 8 * C ^ 2 * rho * y * (1 + y ^ 2) / N := by
    dsimp only [fD]
    calc
      y * (∫ ξ, abs (D ξ) ∂Pₐ) ≤
          y * (8 * C ^ 2 * rho * (1 + y ^ 2) / N) :=
        mul_le_mul_of_nonneg_left hDmoment hy0
      _ = 8 * C ^ 2 * rho * y * (1 + y ^ 2) / N := by ring
  have hBfee : fB ≤ C0 * (sigma * y ^ 3 +
      56 * C ^ 4 * rho ^ 2 * y * (1 + y ^ 2) / sigma) / N := by
    dsimp only [fB]
    rw [hBmean]
    calc
      y ^ 2 * (C0 * (sigma * y / N) + q * (∫ ξ, J ξ ∂Pₐ)) ≤
          y ^ 2 * (C0 * (sigma * y / N) +
            q * (56 * C ^ 4 * rho ^ 2 * (1 + y ^ 2))) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hJmoment hq)) (sq_nonneg y)
      _ = C0 * (sigma * y ^ 3 +
          56 * C ^ 4 * rho ^ 2 * y * (1 + y ^ 2) / sigma) / N := by
        dsimp only [q, b]
        field_simp [ne_of_gt hN, ne_of_gt hypos, ne_of_gt hsigma]
        <;> ring
  have hBdelFeeEq : fBdel = (C0 / (sigma * N)) * TJ := by
    dsimp only [fBdel, TJ]
    simp_rw [hBdelIntegral]
    rw [← Finset.mul_sum]
    dsimp only [q, b]
    field_simp [ne_of_gt hN, ne_of_gt hypos, ne_of_gt hsigma]
    <;> ring
  have hBdelFee : fBdel ≤
      96 * C ^ 2 * C0 * rho ^ 2 * (1 + y) ^ 2 / (sigma * N) := by
    rw [hBdelFeeEq]
    calc
      (C0 / (sigma * N)) * TJ ≤
          (C0 / (sigma * N)) * (96 * C ^ 2 * rho ^ 2 * (1 + y) ^ 2) :=
        mul_le_mul_of_nonneg_left hTJ (by positivity)
      _ = 96 * C ^ 2 * C0 * rho ^ 2 * (1 + y) ^ 2 / (sigma * N) := by ring
  refine ⟨hPa, hDabsL1, hBL1, hDdelL1, hBdelL1,
    hDfee, hBfee, hDdelFee, hBdelFee, ?_⟩
  change fD + fB + fDdel + fBdel ≤
    (256 * C ^ 4 * (1 + C0)) * (1 + rho + rho ^ 2) * (1 + y) ^ 3 / N
  exact le_trans (add_le_add (add_le_add (add_le_add hDfee hBfee) hDdelFee) hBdelFee)
    (four_fee_scalar_envelope C rho y C0 N hC hrho hy hC0 hN)

end

end Shao.OQ6.OriginalClippedExpectationFees
