import Shao.OQ6.ActualQuadraticTiltMoments
import Shao.OQ6.FiniteTiltedMoments
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Shao.OQ6.OriginalRhoTiltedMoments

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/- Original p51 S3/S5, in the existing actual normalized-kernel model.
The canonical/full-law machinery is reused from the qualified Shao--Zhou
source-facing modules. Weighted deletion and probability closure are separate. -/

private theorem rho_choose_bounds
    (n : ℕ) (hn : 4 ≤ n) :
    (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 ∧
      6 * (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 ∧
      6 * (n.choose 4 : ℝ) ≤ (n : ℝ) ^ 4 / 4 := by
  have h2 := Nat.choose_le_pow_div (α := ℝ) 2 n
  have h3 := Nat.choose_le_pow_div (α := ℝ) 3 n
  have h4 := Nat.choose_le_pow_div (α := ℝ) 4 n
  norm_num at h2 h3 h4
  refine ⟨h2, ?_, ?_⟩
  · linarith only [h3]
  · linarith only [h4]

private theorem rho_coefficient_bounds
    (n : ℕ) (hn : 4 ≤ n)
    (y C : ℝ) (hC : 1 ≤ C) :
    let a : ℝ := y / Real.sqrt (n : ℝ)
    (4 * C ^ 2 * (n.choose 2 : ℝ) +
      48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2 +
      96 * C ^ 4 * (n.choose 4 : ℝ) * a ^ 4) ≤
        14 * C ^ 4 * (n : ℝ) ^ 2 * (1 + y ^ 4) ∧
    (8 * C ^ 2 * (n.choose 2 : ℝ) +
      48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2) ≤
        14 * C ^ 4 * (n : ℝ) ^ 2 * (1 + y ^ 2) := by
  dsimp only
  let a : ℝ := y / Real.sqrt (n : ℝ)
  have hN : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hN
  have hNne : (n : ℝ) ≠ 0 := ne_of_gt hNpos
  have hq2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  have hq4 : Real.sqrt (n : ℝ) ^ 4 = (n : ℝ) ^ 2 := by
    calc
      _ = (Real.sqrt (n : ℝ) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hq2]
  have ha2 : (n : ℝ) ^ 3 * a ^ 2 = (n : ℝ) ^ 2 * y ^ 2 := by
    dsimp only [a]
    rw [div_pow, hq2]
    field_simp [hNne]
    <;> ring
  have ha4 : (n : ℝ) ^ 4 * a ^ 4 = (n : ℝ) ^ 2 * y ^ 4 := by
    dsimp only [a]
    rw [div_pow, hq4]
    field_simp [hNne]
    <;> ring
  rcases rho_choose_bounds n hn with ⟨hc2, hc3, hc4⟩
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hC2 : 1 ≤ C ^ 2 := by nlinarith only [hC, sq_nonneg (C - 1)]
  have h24 : C ^ 2 ≤ C ^ 4 := by
    have hm : 0 ≤ C ^ 2 * (C ^ 2 - 1) :=
      mul_nonneg (sq_nonneg C) (sub_nonneg.mpr hC2)
    nlinarith only [hm]
  have h34 : C ^ 3 ≤ C ^ 4 := by
    have hm : 0 ≤ C ^ 3 * (C - 1) :=
      mul_nonneg (pow_nonneg hC0 3) (sub_nonneg.mpr hC)
    nlinarith only [hm]
  have h40 : 0 ≤ C ^ 4 := pow_nonneg hC0 4
  have hy20 : 0 ≤ y ^ 2 := sq_nonneg y
  have hy40 : 0 ≤ y ^ 4 := by positivity
  have hy24 : y ^ 2 ≤ 1 + y ^ 4 := by
    nlinarith only [sq_nonneg (y ^ 2 - 1), hy20]
  have hA : 4 * C ^ 2 * (n.choose 2 : ℝ) ≤
      2 * C ^ 2 * (n : ℝ) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hc2 (by positivity : 0 ≤ 4 * C ^ 2)
    nlinarith only [hm]
  have hB : 48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2 ≤
      8 * C ^ 3 * (n : ℝ) ^ 2 * y ^ 2 := by
    calc
      _ = (8 * C ^ 3 * a ^ 2) * (6 * (n.choose 3 : ℝ)) := by ring
      _ ≤ (8 * C ^ 3 * a ^ 2) * (n : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hc3 (by positivity)
      _ = 8 * C ^ 3 * ((n : ℝ) ^ 3 * a ^ 2) := by ring
      _ = _ := by rw [ha2]; ring
  have hE : 96 * C ^ 4 * (n.choose 4 : ℝ) * a ^ 4 ≤
      4 * C ^ 4 * (n : ℝ) ^ 2 * y ^ 4 := by
    calc
      _ = (16 * C ^ 4 * a ^ 4) * (6 * (n.choose 4 : ℝ)) := by ring
      _ ≤ (16 * C ^ 4 * a ^ 4) * ((n : ℝ) ^ 4 / 4) :=
        mul_le_mul_of_nonneg_left hc4 (by positivity)
      _ = 4 * C ^ 4 * ((n : ℝ) ^ 4 * a ^ 4) := by ring
      _ = _ := by rw [ha4]; ring
  have hAr : 8 * C ^ 2 * (n.choose 2 : ℝ) ≤
      4 * C ^ 2 * (n : ℝ) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hc2 (by positivity : 0 ≤ 8 * C ^ 2)
    nlinarith only [hm]
  have hF0 : 2 * C ^ 2 ≤ 2 * C ^ 4 * (1 + y ^ 4) := by
    nlinarith only [h24, mul_nonneg h40 hy40]
  have hF2 : 8 * C ^ 3 * y ^ 2 ≤ 8 * C ^ 4 * (1 + y ^ 4) := by
    calc
      _ ≤ 8 * C ^ 4 * y ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith only [h34]) hy20
      _ ≤ _ := mul_le_mul_of_nonneg_left hy24 (by positivity)
  have hF4 : 4 * C ^ 4 * y ^ 4 ≤ 4 * C ^ 4 * (1 + y ^ 4) := by
    nlinarith only [h40]
  have hFp : 2 * C ^ 2 + 8 * C ^ 3 * y ^ 2 + 4 * C ^ 4 * y ^ 4 ≤
      14 * C ^ 4 * (1 + y ^ 4) := by
    nlinarith only [hF0, hF2, hF4]
  have hR0 : 4 * C ^ 2 ≤ 4 * C ^ 4 := by nlinarith only [h24]
  have hR2 : 8 * C ^ 3 * y ^ 2 ≤ 8 * C ^ 4 * y ^ 2 :=
    mul_le_mul_of_nonneg_right (by nlinarith only [h34]) hy20
  have hRp : 4 * C ^ 2 + 8 * C ^ 3 * y ^ 2 ≤
      14 * C ^ 4 * (1 + y ^ 2) := by
    nlinarith only [hR0, hR2, h40, mul_nonneg h40 hy20]
  constructor
  · calc
      _ ≤ (n : ℝ) ^ 2 *
          (2 * C ^ 2 + 8 * C ^ 3 * y ^ 2 + 4 * C ^ 4 * y ^ 4) := by
        nlinarith only [hA, hB, hE]
      _ ≤ (n : ℝ) ^ 2 * (14 * C ^ 4 * (1 + y ^ 4)) :=
        mul_le_mul_of_nonneg_left hFp (sq_nonneg _)
      _ = _ := by ring
  · calc
      _ ≤ (n : ℝ) ^ 2 * (4 * C ^ 2 + 8 * C ^ 3 * y ^ 2) := by
        nlinarith only [hAr, hB]
      _ ≤ (n : ℝ) ^ 2 * (14 * C ^ 4 * (1 + y ^ 2)) :=
        mul_le_mul_of_nonneg_left hRp (sq_nonneg _)
      _ = _ := by ring

private theorem integral_abs_sq_le_second
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (f : X → ℝ) (hf : MemLp f 2 P) :
    Integrable (fun z => |f z|) P ∧
      (∫ z, |f z| ∂P) ^ 2 ≤ ∫ z, f z ^ 2 ∂P := by
  have hAbs2 : MemLp (fun z => |f z|) 2 P := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hAbsI : Integrable (fun z => |f z|) P :=
    MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hAbs2
  let c : ℝ := ∫ z, |f z| ∂P
  have hDiff2 : MemLp (fun z => |f z| - c) 2 P :=
    hAbs2.sub (memLp_const c)
  have hSqI : Integrable (fun z => |f z| ^ 2) P := hAbs2.integrable_sq
  have hLinI : Integrable (fun z => 2 * c * |f z|) P :=
    hAbsI.const_mul (2 * c)
  have hExpand : (∫ z, (|f z| - c) ^ 2 ∂P) =
      (∫ z, f z ^ 2 ∂P) - c ^ 2 := by
    calc
      _ = ∫ z, (|f z| ^ 2 - 2 * c * |f z|) + c ^ 2 ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by ring
      _ = ((∫ z, |f z| ^ 2 ∂P) - 2 * c * (∫ z, |f z| ∂P)) + c ^ 2 := by
        rw [integral_add (hSqI.sub' hLinI) (integrable_const (c ^ 2)),
          integral_sub hSqI hLinI, integral_const_mul, integral_const,
          probReal_univ, one_smul]
      _ = (∫ z, f z ^ 2 ∂P) - c ^ 2 := by
        simp only [sq_abs]
        change (∫ z, f z ^ 2 ∂P) - 2 * c * c + c ^ 2 = _
        ring
  have hNonneg : 0 ≤ (∫ z, (|f z| - c) ^ 2 ∂P) :=
    integral_nonneg fun z => sq_nonneg _
  refine ⟨hAbsI, ?_⟩
  change c ^ 2 ≤ _
  linarith only [hNonneg, hExpand]

theorem actual_quadratic_rho_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o z, h o z = h z o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ z, h o z ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 4 ≤ n)
    (y : ℝ) (hy : 1 ≤ y)
    (hwindow : y ≤ Real.sqrt (n : ℝ) /
      (2 * Real.exp (1 / 2 : ℝ))) :
    let C : ℝ := Real.exp (1 / 2 : ℝ)
    let g : Ω → ℝ := fun o => ∫ z, h o z ∂μ
    let r : Ω → Ω → ℝ := fun o z => h o z - g o - g z
    let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
    let rho : ℝ := Real.sqrt v
    let a : ℝ := y / Real.sqrt (n : ℝ)
    let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
    let w : Ω → ℝ := fun o => Real.exp (φ o)
    let m : ℝ := ∫ o, w o ∂μ
    let L : Ω → ℝ := fun o => w o / m
    let ν : Measure Ω :=
      μ.withDensity (fun o => ENNReal.ofReal (L o))
    let P₀ : Measure (Fin n → Ω) :=
      Measure.pi (fun _ : Fin n => μ)
    let S : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j : Fin n, φ (ξ j)
    let Pₐ : Measure (Fin n → Ω) := P₀.tilted S
    let F : (Fin n → Ω) → ℝ := fun ξ =>
      Shao.OQ5.P35.unorderedPairSum (fun i j => r (ξ i) (ξ j))
    let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Shao.OQ6.ResidualDeletion.rowSum
        (fun j k => r (ξ j) (ξ k)) i
    let Λsq : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ i : Fin n, ψ ξ i ^ 2
    let u : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      ψ ξ i / ((n : ℝ) - 2)
    let J : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ i : Fin n, u ξ i ^ 2
    let D : (Fin n → Ω) → ℝ := fun ξ =>
      F ξ / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    0 ≤ rho ∧ rho ^ 2 = v ∧
      μ.tilted φ = ν ∧ IsProbabilityMeasure ν ∧
      Pₐ = Measure.pi (fun _ : Fin n => ν) ∧
      IsProbabilityMeasure Pₐ ∧
      MemLp F 2 Pₐ ∧ Integrable (fun ξ => F ξ ^ 2) Pₐ ∧
      Integrable (fun ξ => |F ξ|) Pₐ ∧
      (∀ i : Fin n, MemLp (fun ξ => ψ ξ i) 2 Pₐ) ∧
      Integrable Λsq Pₐ ∧ Integrable J Pₐ ∧
      Integrable D Pₐ ∧ Integrable (fun ξ => |D ξ|) Pₐ ∧
      (∀ ξ, J ξ = Λsq ξ / ((n : ℝ) - 2) ^ 2) ∧
      (∫ ξ, J ξ ∂Pₐ) =
        (∫ ξ, Λsq ξ ∂Pₐ) / ((n : ℝ) - 2) ^ 2 ∧
      (∫ ξ, |D ξ| ∂Pₐ) =
        (∫ ξ, |F ξ| ∂Pₐ) /
          (Real.sqrt (n : ℝ) * ((n : ℝ) - 1)) ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤ rho ^ 2 *
        (4 * C ^ 2 * (n.choose 2 : ℝ) +
          48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2 +
          96 * C ^ 4 * (n.choose 4 : ℝ) * a ^ 4) ∧
      (∫ ξ, Λsq ξ ∂Pₐ) ≤ rho ^ 2 *
        (8 * C ^ 2 * (n.choose 2 : ℝ) +
          48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2) ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤
        14 * C ^ 4 * rho ^ 2 * (n : ℝ) ^ 2 * (1 + y ^ 4) ∧
      (∫ ξ, Λsq ξ ∂Pₐ) ≤
        14 * C ^ 4 * rho ^ 2 * (n : ℝ) ^ 2 * (1 + y ^ 2) ∧
      (∫ ξ, J ξ ∂Pₐ) ≤
        56 * C ^ 4 * rho ^ 2 * (1 + y ^ 2) ∧
      (∫ ξ, |D ξ| ∂Pₐ) ≤
        8 * C ^ 2 * rho * (1 + y ^ 2) / Real.sqrt (n : ℝ) := by
  classical
  dsimp only
  let C : ℝ := Real.exp (1 / 2 : ℝ)
  let g : Ω → ℝ := fun o => ∫ z, h o z ∂μ
  let r : Ω → Ω → ℝ := fun o z => h o z - g o - g z
  let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
  let rho : ℝ := Real.sqrt v
  let a : ℝ := y / Real.sqrt (n : ℝ)
  let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
  let w : Ω → ℝ := fun o => Real.exp (φ o)
  let m : ℝ := ∫ o, w o ∂μ
  let L : Ω → ℝ := fun o => w o / m
  let ν : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
  let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let S : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, φ (ξ j)
  let Pₐ : Measure (Fin n → Ω) := P₀.tilted S
  let F : (Fin n → Ω) → ℝ := fun ξ =>
    Shao.OQ5.P35.unorderedPairSum (fun i j => r (ξ i) (ξ j))
  let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Shao.OQ6.ResidualDeletion.rowSum (fun j k => r (ξ j) (ξ k)) i
  let Λsq : (Fin n → Ω) → ℝ := fun ξ => ∑ i : Fin n, ψ ξ i ^ 2
  let u : (Fin n → Ω) → Fin n → ℝ := fun ξ i => ψ ξ i / ((n : ℝ) - 2)
  let J : (Fin n → Ω) → ℝ := fun ξ => ∑ i : Fin n, u ξ i ^ 2
  let D : (Fin n → Ω) → ℝ := fun ξ =>
    F ξ / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
  let N : ℝ := (n : ℝ)
  let q : ℝ := Real.sqrt N
  let dD : ℝ := q * (N - 1)
  let dJ : ℝ := (N - 2) ^ 2
  let LF : ℝ := ∫ ξ, |F ξ| ∂Pₐ
  let TF : ℝ := 4 * C ^ 2 * rho * N * (1 + y ^ 2)
  have hn3 : 3 ≤ n := le_trans (by norm_num) hn
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy
  have source := ActualQuadraticTiltMoments.actual_quadratic_source_moments
    μ h hh hh2 hhsymm hcenter hprojectionsecond n hn3 y hy0 hwindow
  rcases source with
    ⟨hg, hg2, hgmean, hgsecond, hr, hr2, hrsymm, hrcan,
      hv, hs1, hvs, hw, hmlo, hmhi, hL, hL1, hLb, hLmass,
      hdeltaInt, hdeltaBd, hNuEq, hNuProb, hFullExp, hFullNorm,
      hFullPos, hprod, hPaDensity, hPaProd, hPaProb,
      hF2, hFI, hrows, hLambdaI, hFid, hLambdaId, _, _, _, _, _, _⟩
  letI : IsProbabilityMeasure Pₐ := hPaProb
  have hN4 : (4 : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN4
  have hqpos : 0 < q := Real.sqrt_pos.2 hNpos
  have hNm1 : 0 < N - 1 := by linarith only [hN4]
  have hNm2 : 0 < N - 2 := by linarith only [hN4]
  have hdD : 0 < dD := mul_pos hqpos hNm1
  have hdJ : 0 < dJ := sq_pos_of_pos hNm2
  have hCpos : 0 < C := Real.exp_pos _
  have hC1 : 1 ≤ C := by
    dsimp only [C]
    exact Real.one_le_exp (by norm_num)
  have hrho : 0 ≤ rho := Real.sqrt_nonneg v
  have hrhosq : rho ^ 2 = v := Real.sq_sqrt hv
  have hrsecond : (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)) ≤ rho ^ 2 := by
    change v ≤ rho ^ 2
    exact hrhosq.ge
  have ha : 0 ≤ a := div_nonneg hy0 (Real.sqrt_nonneg _)
  have hepsilon : 0 ≤ 2 * C * a :=
    mul_nonneg (mul_nonneg (by norm_num) hCpos.le) ha
  have hdelta : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ (2 * C * a) ^ 2 := by
    calc
      _ ≤ 4 * C ^ 2 * a ^ 2 := hdeltaBd
      _ = _ := by ring
  have hFgen := FiniteTiltedMoments.unordered_pair_sum_second_moment
    μ r hr hr2 hrsymm hrcan rho hrho hrsecond L hL (2 * C)
    (fun o => (hLb o).1.le) (fun o => (hLb o).2) hLmass
    (2 * C * a) hepsilon hdelta n
  rcases hFgen with ⟨_, _, _, _, _, hFbound⟩
  have hRgen := FiniteTiltedMoments.row_square_sum_moment
    μ r hr hr2 hrsymm hrcan rho hrho hrsecond L hL (2 * C)
    (fun o => (hLb o).1.le) (fun o => (hLb o).2) hLmass
    (2 * C * a) hepsilon hdelta n
  rcases hRgen with ⟨_, _, _, _, _, hRbound⟩
  change (∫ ξ, F ξ ^ 2 ∂Measure.pi (fun _ : Fin n => ν)) ≤
    ((n.choose 2 : ℝ) * (2 * C) ^ 2 +
      6 * (n.choose 3 : ℝ) * (2 * C) * (2 * C * a) ^ 2 +
      6 * (n.choose 4 : ℝ) * (2 * C * a) ^ 4) * rho ^ 2 at hFbound
  change (∫ ξ, Λsq ξ ∂Measure.pi (fun _ : Fin n => ν)) ≤
    (2 * (n.choose 2 : ℝ) * (2 * C) ^ 2 +
      6 * (n.choose 3 : ℝ) * (2 * C) * (2 * C * a) ^ 2) * rho ^ 2 at hRbound
  rw [← hPaProd] at hFbound hRbound
  have hFchoose : (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤ rho ^ 2 *
      (4 * C ^ 2 * (n.choose 2 : ℝ) +
        48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2 +
        96 * C ^ 4 * (n.choose 4 : ℝ) * a ^ 4) := by
    calc
      _ ≤ ((n.choose 2 : ℝ) * (2 * C) ^ 2 +
          6 * (n.choose 3 : ℝ) * (2 * C) * (2 * C * a) ^ 2 +
          6 * (n.choose 4 : ℝ) * (2 * C * a) ^ 4) * rho ^ 2 := hFbound
      _ = _ := by ring
  have hRchoose : (∫ ξ, Λsq ξ ∂Pₐ) ≤ rho ^ 2 *
      (8 * C ^ 2 * (n.choose 2 : ℝ) +
        48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2) := by
    calc
      _ ≤ (2 * (n.choose 2 : ℝ) * (2 * C) ^ 2 +
          6 * (n.choose 3 : ℝ) * (2 * C) * (2 * C * a) ^ 2) * rho ^ 2 := hRbound
      _ = _ := by ring
  rcases rho_coefficient_bounds n hn y C hC1 with ⟨hFcoef, hRcoef⟩
  have hFfinal : (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤
      14 * C ^ 4 * rho ^ 2 * N ^ 2 * (1 + y ^ 4) := by
    calc
      _ ≤ rho ^ 2 *
          (4 * C ^ 2 * (n.choose 2 : ℝ) +
            48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2 +
            96 * C ^ 4 * (n.choose 4 : ℝ) * a ^ 4) := hFchoose
      _ ≤ rho ^ 2 * (14 * C ^ 4 * N ^ 2 * (1 + y ^ 4)) :=
        mul_le_mul_of_nonneg_left hFcoef (sq_nonneg rho)
      _ = _ := by ring
  have hRfinal : (∫ ξ, Λsq ξ ∂Pₐ) ≤
      14 * C ^ 4 * rho ^ 2 * N ^ 2 * (1 + y ^ 2) := by
    calc
      _ ≤ rho ^ 2 *
          (8 * C ^ 2 * (n.choose 2 : ℝ) +
            48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2) := hRchoose
      _ ≤ rho ^ 2 * (14 * C ^ 4 * N ^ 2 * (1 + y ^ 2)) :=
        mul_le_mul_of_nonneg_left hRcoef (sq_nonneg rho)
      _ = _ := by ring
  have hJpoint : ∀ ξ, J ξ = Λsq ξ / dJ := by
    intro ξ
    dsimp only [J, u, Λsq, dJ, N]
    simp_rw [div_pow]
    rw [← Finset.sum_div]
  have hJfun : J = (fun ξ => Λsq ξ / dJ) := funext hJpoint
  have hJI : Integrable J Pₐ := by
    rw [hJfun]
    exact hLambdaI.div_const dJ
  have hJintegral : (∫ ξ, J ξ ∂Pₐ) = (∫ ξ, Λsq ξ ∂Pₐ) / dJ := by
    rw [hJfun]
    simp only [div_eq_mul_inv, integral_mul_const]
  have hNtw : N ≤ 2 * (N - 2) := by linarith only [hN4]
  have hNsquareRatio : N ^ 2 ≤ 4 * (N - 2) ^ 2 := by
    have hs := pow_le_pow_left₀ hNpos.le hNtw 2
    nlinarith only [hs]
  have hJbound : (∫ ξ, J ξ ∂Pₐ) ≤ 56 * C ^ 4 * rho ^ 2 * (1 + y ^ 2) := by
    rw [hJintegral]
    apply (div_le_iff₀ hdJ).2
    calc
      _ ≤ 14 * C ^ 4 * rho ^ 2 * N ^ 2 * (1 + y ^ 2) := hRfinal
      _ ≤ 56 * C ^ 4 * rho ^ 2 * (1 + y ^ 2) * dJ := by
        have hm := mul_le_mul_of_nonneg_left hNsquareRatio
          (by positivity : 0 ≤ 14 * C ^ 4 * rho ^ 2 * (1 + y ^ 2))
        dsimp only [dJ]
        nlinarith only [hm]
  rcases integral_abs_sq_le_second Pₐ F hF2 with ⟨hFabsI, hLFsq⟩
  have hFI1 : Integrable F Pₐ :=
    MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hF2
  have hLFnonneg : 0 ≤ LF := integral_nonneg fun ξ => abs_nonneg _
  have hTFnonneg : 0 ≤ TF := by dsimp only [TF]; positivity
  have hpolysq : 14 * (1 + y ^ 4) ≤ 16 * (1 + y ^ 2) ^ 2 := by
    nlinarith only [sq_nonneg y, sq_nonneg (y ^ 2)]
  have hLFsqTF : LF ^ 2 ≤ TF ^ 2 := by
    calc
      _ ≤ ∫ ξ, F ξ ^ 2 ∂Pₐ := hLFsq
      _ ≤ 14 * C ^ 4 * rho ^ 2 * N ^ 2 * (1 + y ^ 4) := hFfinal
      _ ≤ TF ^ 2 := by
        have hm := mul_le_mul_of_nonneg_left hpolysq
          (by positivity : 0 ≤ C ^ 4 * rho ^ 2 * N ^ 2)
        dsimp only [TF]
        nlinarith only [hm]
  have hLFle : LF ≤ TF := by
    by_contra hnot
    have hlt : TF < LF := lt_of_not_ge hnot
    have hd : 0 < LF - TF := sub_pos.mpr hlt
    have hs : 0 < LF + TF := by linarith only [hlt, hTFnonneg]
    have hp : 0 < (LF - TF) * (LF + TF) := mul_pos hd hs
    nlinarith only [hp, hLFsqTF]
  have hDI : Integrable D Pₐ := by
    change Integrable (fun ξ => F ξ / dD) Pₐ
    exact hFI1.div_const dD
  have hDabsI : Integrable (fun ξ => |D ξ|) Pₐ := by
    simpa only [Real.norm_eq_abs] using hDI.norm
  have hDpoint : ∀ ξ, |D ξ| = |F ξ| / dD := by
    intro ξ
    change |F ξ / dD| = |F ξ| / dD
    rw [abs_div, abs_of_pos hdD]
  have hDintegral : (∫ ξ, |D ξ| ∂Pₐ) = LF / dD := by
    calc
      _ = ∫ ξ, |F ξ| / dD ∂Pₐ :=
        integral_congr_ae (Filter.Eventually.of_forall hDpoint)
      _ = LF / dD := by simp only [div_eq_mul_inv, integral_mul_const, LF]
  have hNratio : N ≤ 2 * (N - 1) := by linarith only [hN4]
  have hDbound : (∫ ξ, |D ξ| ∂Pₐ) ≤
      8 * C ^ 2 * rho * (1 + y ^ 2) / q := by
    rw [hDintegral]
    apply (div_le_iff₀ hdD).2
    calc
      LF ≤ TF := hLFle
      _ ≤ (8 * C ^ 2 * rho * (1 + y ^ 2) / q) * dD := by
        have hm := mul_le_mul_of_nonneg_left hNratio
          (by positivity : 0 ≤ 4 * C ^ 2 * rho * (1 + y ^ 2))
        have heq : (8 * C ^ 2 * rho * (1 + y ^ 2) / q) * dD =
            8 * C ^ 2 * rho * (1 + y ^ 2) * (N - 1) := by
          dsimp only [dD]
          field_simp [ne_of_gt hqpos]
          <;> ring
        rw [heq]
        dsimp only [TF]
        nlinarith only [hm]
  exact ⟨hrho, hrhosq, hNuEq, hNuProb, hPaProd, hPaProb,
    hF2, hFI, hFabsI, hrows, hLambdaI, hJI, hDI, hDabsI,
    hJpoint, hJintegral, hDintegral, hFchoose, hRchoose,
    hFfinal, hRfinal, hJbound, hDbound⟩

end

end Shao.OQ6.OriginalRhoTiltedMoments
