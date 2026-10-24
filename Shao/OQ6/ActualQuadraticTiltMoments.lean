import Shao.OQ6.QuadraticTilt
import Shao.OQ6.ObservationProductTilt
import Shao.OQ6.FiniteTiltedMoments
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The actual normalized-kernel substitution in original p39(10).  The first
projection and canonical residual are derived from the whole observation
kernel before the quadratic change of measure is used.  The finite moment
identities reuse the qualified full-observation public interface of139.
The probability engine in the original source remains due to Shao--Zhou.
Weighted deletion, partial tilts, probability costs and original roots are
not consequences asserted by this module.
-/

set_option autoImplicit false

namespace Shao.OQ6.ActualQuadraticTiltMoments

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem aq_mean_square_le
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : MemLp f 2 μ) :
    (∫ y, f y ∂μ) ^ 2 ≤ ∫ y, f y ^ 2 ∂μ := by
  let m : ℝ := ∫ y, f y ∂μ
  have hf1 : Integrable f μ := hf.integrable (by norm_num)
  have hf2 : Integrable (fun y => f y ^ 2) μ := hf.integrable_sq
  have hlin : Integrable (fun y => (2 * m) * f y) μ :=
    hf1.const_mul (2 * m)
  have hconst : Integrable (fun _ : α => m ^ 2) μ := integrable_const _
  have heq : (fun y => (f y - m) ^ 2) =
      (fun y => f y ^ 2 - (2 * m) * f y + m ^ 2) := by
    funext y
    ring
  have hcenter : (∫ y, (f y - m) ^ 2 ∂μ) =
      (∫ y, f y ^ 2 ∂μ) - m ^ 2 := by
    rw [heq, integral_add (f := fun y => f y ^ 2 - (2 * m) * f y) (g := fun _ : α => m ^ 2) (hf2.sub hlin) hconst,
      integral_sub (f := fun y => f y ^ 2) (g := fun y => (2 * m) * f y) hf2 hlin, integral_const_mul, integral_const,
      probReal_univ, one_smul]
    change (∫ y, f y ^ 2 ∂μ) - (2 * m) * m + m ^ 2 = _
    ring
  have hnonneg : 0 ≤ ∫ y, (f y - m) ^ 2 ∂μ :=
    integral_nonneg fun y => sq_nonneg (f y - m)
  rw [hcenter] at hnonneg
  exact sub_nonneg.mp hnonneg

private theorem aq_projection_L2
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ)) :
    Measurable (fun o => ∫ y, h o y ∂μ) ∧
      MemLp (fun o => ∫ y, h o y ∂μ) 2 μ := by
  have hg : Measurable (fun o => ∫ y, h o y ∂μ) :=
    hh.stronglyMeasurable.integral_prod_right'.measurable
  have hHsq : Integrable (fun z : Ω × Ω => h z.1 z.2 ^ 2)
      (μ.prod μ) := hh2.integrable_sq
  have hQ : Integrable (fun o => ∫ y, h o y ^ 2 ∂μ) μ :=
    hHsq.integral_prod_left
  have hgSq : Integrable (fun o => (∫ y, h o y ∂μ) ^ 2) μ := by
    apply hQ.mono' (hg.pow_const 2).aestronglyMeasurable
    filter_upwards [hHsq.prod_right_ae] with o ho
    have hrowmeas : Measurable (h o) := hh.comp measurable_prodMk_left
    have hrow2 : MemLp (h o) 2 μ :=
      (memLp_two_iff_integrable_sq hrowmeas.aestronglyMeasurable).2 ho
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact aq_mean_square_le μ (h o) hrow2
  exact ⟨hg, (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hgSq⟩

private theorem aq_tilted_density
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (φ : α → ℝ) :
    μ.tilted φ = μ.withDensity (fun o =>
      ENNReal.ofReal (Real.exp (φ o) / ∫ y, Real.exp (φ y) ∂μ)) := by
  apply Measure.ext
  intro A hA
  rw [tilted_apply' μ φ hA, withDensity_apply _ hA]

private theorem aq_pair_choose_poly (n : ℕ) :
    (n : ℝ) * ((n : ℝ) - 1) = 2 * (n.choose 2 : ℝ) := by
  have h := Shao.OQ5.P35.pairCount_eq_choose n
  unfold Shao.OQ5.P35.pairCount at h
  nlinarith

private theorem aq_triple_choose_poly (n : ℕ) :
    (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) =
      6 * (n.choose 3 : ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have h2 := aq_pair_choose_poly n
      simp only [Nat.choose_succ_succ, Nat.cast_succ, Nat.cast_add, Nat.cast_one] at *
      nlinarith

private theorem aq_quadruple_choose_poly (n : ℕ) :
    (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) =
      24 * (n.choose 4 : ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have h3 := aq_triple_choose_poly n
      simp only [Nat.choose_succ_succ, Nat.cast_succ, Nat.cast_add, Nat.cast_one] at *
      nlinarith

private theorem aq_choose_bounds (n : ℕ) (hn : 3 ≤ n) :
    (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 ∧
      6 * (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 ∧
      6 * (n.choose 4 : ℝ) ≤ (n : ℝ) ^ 4 / 4 := by
  have hN : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hN2 : 0 ≤ (n : ℝ) - 2 := by linarith
  have hN3 : 0 ≤ (n : ℝ) - 3 := by linarith
  have hpair : (n : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) ^ 2 := by
    nlinarith only [hN0]
  have htriple : (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) ≤
      (n : ℝ) ^ 3 := by
    calc
      _ ≤ (n : ℝ) ^ 2 * ((n : ℝ) - 2) :=
        mul_le_mul_of_nonneg_right hpair hN2
      _ ≤ (n : ℝ) ^ 2 * (n : ℝ) :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
      _ = _ := by ring
  have hquadruple :
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) ≤
        (n : ℝ) ^ 4 := by
    calc
      _ ≤ (n : ℝ) ^ 3 * ((n : ℝ) - 3) :=
        mul_le_mul_of_nonneg_right htriple hN3
      _ ≤ (n : ℝ) ^ 3 * (n : ℝ) :=
        mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hN0 3)
      _ = _ := by ring
  refine ⟨?_, ?_, ?_⟩
  · nlinarith only [hpair, aq_pair_choose_poly n]
  · rw [← aq_triple_choose_poly]
    exact htriple
  · nlinarith only [hquadruple, aq_quadruple_choose_poly n]

private theorem aq_final_polynomials (C x : ℝ) (hC : 1 ≤ C) :
    2 * C ^ 2 + 8 * C ^ 3 * x ^ 2 + 4 * C ^ 4 * x ^ 4 ≤
        14 * C ^ 4 * (1 + x ^ 4) ∧
      4 * C ^ 2 + 8 * C ^ 3 * x ^ 2 ≤
        14 * C ^ 4 * (1 + x ^ 2) := by
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hC2 : 1 ≤ C ^ 2 := by nlinarith only [hC, sq_nonneg (C - 1)]
  have h24 : C ^ 2 ≤ C ^ 4 := by
    have h := mul_nonneg (sq_nonneg C) (sub_nonneg.mpr hC2)
    nlinarith only [h]
  have h34 : C ^ 3 ≤ C ^ 4 := by
    have h := mul_nonneg (pow_nonneg hC0 3) (sub_nonneg.mpr hC)
    nlinarith only [h]
  have h40 : 0 ≤ C ^ 4 := pow_nonneg hC0 4
  have hx20 : 0 ≤ x ^ 2 := sq_nonneg x
  have hx40 : 0 ≤ x ^ 4 := by positivity
  have hx24 : x ^ 2 ≤ 1 + x ^ 4 := by
    nlinarith only [sq_nonneg (x ^ 2 - 1), hx20]
  have hF0 : 2 * C ^ 2 ≤ 2 * C ^ 4 * (1 + x ^ 4) := by
    calc
      _ ≤ 2 * C ^ 4 := by nlinarith only [h24]
      _ ≤ _ := by nlinarith only [mul_nonneg h40 hx40]
  have hF2 : 8 * C ^ 3 * x ^ 2 ≤ 8 * C ^ 4 * (1 + x ^ 4) := by
    calc
      _ ≤ 8 * C ^ 4 * x ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith only [h34]) hx20
      _ ≤ _ := mul_le_mul_of_nonneg_left hx24 (by nlinarith only [h40])
  have hF4 : 4 * C ^ 4 * x ^ 4 ≤ 4 * C ^ 4 * (1 + x ^ 4) := by
    nlinarith only [h40]
  have hR0 : 4 * C ^ 2 ≤ 4 * C ^ 4 := by nlinarith only [h24]
  have hR2 : 8 * C ^ 3 * x ^ 2 ≤ 8 * C ^ 4 * x ^ 2 :=
    mul_le_mul_of_nonneg_right (by nlinarith only [h34]) hx20
  refine ⟨?_, ?_⟩
  · nlinarith only [hF0, hF2, hF4]
  · nlinarith only [hR0, hR2, h40, mul_nonneg h40 hx20]

theorem actual_quadratic_source_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 3 ≤ n)
    (x : ℝ) (hx : 0 ≤ x)
    (hwindow : x ≤ Real.sqrt (n : ℝ) /
      (2 * Real.exp (1 / 2 : ℝ))) :
    let C : ℝ := Real.exp (1 / 2 : ℝ)
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
    let s : ℝ := 1 + Real.sqrt v
    let a : ℝ := x / Real.sqrt (n : ℝ)
    let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
    let w : Ω → ℝ := fun o => Real.exp (φ o)
    let m : ℝ := ∫ o, w o ∂μ
    let L : Ω → ℝ := fun o => w o / m
    let ρ : Measure Ω :=
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
    let A : ℝ :=
      ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(ρ.prod ρ)
    let B : ℝ :=
      ∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
        ∂(ρ.prod (ρ.prod ρ))
    let D : ℝ :=
      ∫ d : (Ω × Ω) × (Ω × Ω),
        r d.1.1 d.1.2 * r d.2.1 d.2.2
        ∂((ρ.prod ρ).prod (ρ.prod ρ))
    Measurable g ∧ MemLp g 2 μ ∧ (∫ o, g o ∂μ) = 0 ∧
      (∫ o, g o ^ 2 ∂μ) = 1 ∧
      Measurable (fun z : Ω × Ω => r z.1 z.2) ∧
      MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ) ∧
      (∀ o y, r o y = r y o) ∧
      (∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0) ∧
      0 ≤ v ∧ 1 ≤ s ∧ v ≤ s ^ 2 ∧
      Integrable w μ ∧ (1 / 2 : ℝ) ≤ m ∧ m ≤ (3 / 2 : ℝ) ∧
      Measurable L ∧ Integrable L μ ∧
      (∀ o, 0 < L o ∧ L o ≤ 2 * C) ∧
      (∫ o, L o ∂μ) = 1 ∧
      Integrable (fun o => (L o - 1) ^ 2) μ ∧
      (∫ o, (L o - 1) ^ 2 ∂μ) ≤ 4 * C ^ 2 * a ^ 2 ∧
      μ.tilted φ = ρ ∧ IsProbabilityMeasure ρ ∧
      Integrable (fun ξ => Real.exp (S ξ)) P₀ ∧
      (∫ ξ, Real.exp (S ξ) ∂P₀) = m ^ n ∧ 0 < m ^ n ∧
      (∀ ξ, Real.exp (S ξ) / m ^ n =
        ∏ j : Fin n, L (ξ j)) ∧
      Pₐ = P₀.withDensity
        (fun ξ => ENNReal.ofReal (∏ j : Fin n, L (ξ j))) ∧
      Pₐ = Measure.pi (fun _ : Fin n => ρ) ∧
      IsProbabilityMeasure Pₐ ∧
      MemLp F 2 Pₐ ∧ Integrable (fun ξ => F ξ ^ 2) Pₐ ∧
      (∀ i : Fin n, MemLp (fun ξ => ψ ξ i) 2 Pₐ) ∧
      Integrable Λsq Pₐ ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) =
        (n.choose 2 : ℝ) * A +
          6 * (n.choose 3 : ℝ) * B +
          6 * (n.choose 4 : ℝ) * D ∧
      (∫ ξ, Λsq ξ ∂Pₐ) =
        2 * (n.choose 2 : ℝ) * A +
          6 * (n.choose 3 : ℝ) * B ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤ s ^ 2 *
        (4 * C ^ 2 * (n.choose 2 : ℝ) +
          48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2 +
          96 * C ^ 4 * (n.choose 4 : ℝ) * a ^ 4) ∧
      (∫ ξ, Λsq ξ ∂Pₐ) ≤ s ^ 2 *
        (8 * C ^ 2 * (n.choose 2 : ℝ) +
          48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2) ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤ s ^ 2 * (n : ℝ) ^ 2 *
        (2 * C ^ 2 + 8 * C ^ 3 * x ^ 2 + 4 * C ^ 4 * x ^ 4) ∧
      (∫ ξ, Λsq ξ ∂Pₐ) ≤ s ^ 2 * (n : ℝ) ^ 2 *
        (4 * C ^ 2 + 8 * C ^ 3 * x ^ 2) ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤
        14 * C ^ 4 * s ^ 2 * (n : ℝ) ^ 2 * (1 + x ^ 4) ∧
      (∫ ξ, Λsq ξ ∂Pₐ) ≤
        14 * C ^ 4 * s ^ 2 * (n : ℝ) ^ 2 * (1 + x ^ 2) := by
  classical
  dsimp only
  let C : ℝ := Real.exp (1 / 2 : ℝ)
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
  let s : ℝ := 1 + Real.sqrt v
  let a : ℝ := x / Real.sqrt (n : ℝ)
  let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
  let w : Ω → ℝ := fun o => Real.exp (φ o)
  let m : ℝ := ∫ o, w o ∂μ
  let L : Ω → ℝ := fun o => w o / m
  let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
  let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let S : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, φ (ξ j)
  let Pₐ : Measure (Fin n → Ω) := P₀.tilted S
  let F : (Fin n → Ω) → ℝ := fun ξ =>
    Shao.OQ5.P35.unorderedPairSum (fun i j => r (ξ i) (ξ j))
  let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Shao.OQ6.ResidualDeletion.rowSum (fun j k => r (ξ j) (ξ k)) i
  let Λsq : (Fin n → Ω) → ℝ := fun ξ => ∑ i : Fin n, ψ ξ i ^ 2
  let A : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(ρ.prod ρ)
  let B : ℝ := ∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
    ∂(ρ.prod (ρ.prod ρ))
  let D : ℝ := ∫ d : (Ω × Ω) × (Ω × Ω),
    r d.1.1 d.1.2 * r d.2.1 d.2.2 ∂((ρ.prod ρ).prod (ρ.prod ρ))
  rcases aq_projection_L2 μ h hh hh2 with ⟨hg, hg2⟩
  have hh1 : Integrable (fun z : Ω × Ω => h z.1 z.2) (μ.prod μ) :=
    hh2.integrable (by norm_num)
  have hg1 : Integrable g μ := hg2.integrable (by norm_num)
  have hg0 : (∫ o, g o ∂μ) = 0 := by
    calc
      _ = ∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ) :=
        (integral_prod _ hh1).symm
      _ = 0 := hcenter
  have hr : Measurable (fun z : Ω × Ω => r z.1 z.2) :=
    (hh.sub (hg.comp measurable_fst)).sub (hg.comp measurable_snd)
  have hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ) :=
    (hh2.sub (hg2.comp_fst μ)).sub (hg2.comp_snd μ)
  have hrsymm : ∀ o y, r o y = r y o := by
    intro o y
    dsimp only [r]
    rw [hhsymm o y]
    ring
  have hrcan : ∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0 := by
    filter_upwards [hh1.prod_right_ae] with o ho
    have hc : Integrable (fun _ : Ω => g o) μ := integrable_const _
    change (∫ y, h o y - g o - g y ∂μ) = 0
    rw [integral_sub (f := fun y => h o y - g o) (g := g) (ho.sub hc) hg1, integral_sub (f := fun y => h o y) (g := fun _ : Ω => g o) ho hc,
      integral_const, probReal_univ, one_smul, hg0]
    change g o - g o - 0 = 0
    ring
  have hv : 0 ≤ v := integral_nonneg fun z => sq_nonneg (r z.1 z.2)
  have hs1 : 1 ≤ s := by
    dsimp only [s]
    linarith only [Real.sqrt_nonneg v]
  have hs : 0 ≤ s := le_trans (by norm_num) hs1
  have hvle : v ≤ s ^ 2 := by
    have hsq := Real.sq_sqrt hv
    have hroot := Real.sqrt_nonneg v
    dsimp only [s]
    nlinarith only [hsq, hroot]
  have hN : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hN
  have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hNpos
  have hrootSq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hNpos.le
  have ha0 : 0 ≤ a := div_nonneg hx hroot.le
  have ha : |a| ≤ (2 * Real.exp (1 / 2 : ℝ))⁻¹ := by
    rw [abs_of_nonneg ha0]
    change x / Real.sqrt (n : ℝ) ≤ (2 * C)⁻¹
    apply (div_le_iff₀ hroot).2
    calc
      x ≤ Real.sqrt (n : ℝ) / (2 * C) := hwindow
      _ = (2 * C)⁻¹ * Real.sqrt (n : ℝ) := by
        rw [div_eq_mul_inv]
        ring
  have ht := QuadraticTilt.normalizer_density_L2 μ g hg hg2
    hprojectionsecond a ha
  rcases ht with ⟨hw, hml, hmu, hLm, hLint, hLb, hLmass,
    hTiltProb, hdevI, hdev⟩
  have hρeq : μ.tilted φ = ρ := aq_tilted_density μ φ
  have hρp : IsProbabilityMeasure ρ := by
    rw [← hρeq]
    exact hTiltProb
  letI : IsProbabilityMeasure ρ := hρp
  have hfull := Shao.OQ6.finite_observation_product_tilt n
    (fun _ : Fin n => μ) (fun _ : Fin n => φ) (fun _ => hw)
  rcases hfull with ⟨hSInt, hNorm, hNormPos, hPaLaw⟩
  have hI : (∫ ξ, Real.exp (S ξ) ∂P₀) = m ^ n := by
    change (∫ ξ, Real.exp (S ξ) ∂P₀) = ∏ _ : Fin n, m at hNorm
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hNorm
  have hmn : 0 < m ^ n := by
    have hmp : 0 < m := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hml
    exact pow_pos hmp n
  have hprod : ∀ ξ, Real.exp (S ξ) / m ^ n = ∏ j : Fin n, L (ξ j) := by
    intro ξ
    have hi : Real.exp (S ξ) / (∏ _ : Fin n, m) =
        ∏ j : Fin n, Real.exp (φ (ξ j)) / m := by
      dsimp only [S]
      rw [Finset.prod_div_distrib, ← Real.exp_sum]
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hi
  have hPaDensity : Pₐ = P₀.withDensity
      (fun ξ => ENNReal.ofReal (∏ j : Fin n, L (ξ j))) := by
    calc
      Pₐ = P₀.withDensity (fun ξ => ENNReal.ofReal
          (Real.exp (S ξ) / ∫ η, Real.exp (S η) ∂P₀)) :=
        aq_tilted_density P₀ S
      _ = _ := by
        congr 1
        funext ξ
        rw [hI, hprod ξ]
  have hPaProd : Pₐ = Measure.pi (fun _ : Fin n => ρ) := by
    change Pₐ = Measure.pi (fun _ : Fin n => μ.tilted φ) at hPaLaw
    rw [hρeq] at hPaLaw
    exact hPaLaw
  have hPaProb : IsProbabilityMeasure Pₐ := by
    rw [hPaProd]
    infer_instance
  have hCpos : 0 < C := Real.exp_pos _
  have hε : 0 ≤ 2 * C * a := mul_nonneg (by positivity) ha0
  have hδ : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ (2 * C * a) ^ 2 := by
    calc
      _ ≤ 4 * C ^ 2 * a ^ 2 := hdev
      _ = _ := by ring
  have hFdata := FiniteTiltedMoments.unordered_pair_sum_second_moment
    μ r hr hr2 hrsymm hrcan s hs hvle L hLm (2 * C)
    (fun o => (hLb o).1.le) (fun o => (hLb o).2) hLmass
    (2 * C * a) hε hδ n
  rcases hFdata with ⟨_, _, hF2, hFI, hFid, hFbound⟩
  have hRdata := FiniteTiltedMoments.row_square_sum_moment
    μ r hr hr2 hrsymm hrcan s hs hvle L hLm (2 * C)
    (fun o => (hLb o).1.le) (fun o => (hLb o).2) hLmass
    (2 * C * a) hε hδ n
  rcases hRdata with ⟨_, _, hrows, hΛI, hΛid, hΛbound⟩
  change MemLp F 2 (Measure.pi (fun _ : Fin n => ρ)) at hF2
  change Integrable (fun ξ => F ξ ^ 2)
    (Measure.pi (fun _ : Fin n => ρ)) at hFI
  change (∀ i : Fin n, MemLp (fun ξ => ψ ξ i) 2
    (Measure.pi (fun _ : Fin n => ρ))) at hrows
  change Integrable Λsq (Measure.pi (fun _ : Fin n => ρ)) at hΛI
  change (∫ ξ, F ξ ^ 2 ∂Measure.pi (fun _ : Fin n => ρ)) =
    (n.choose 2 : ℝ) * A + 6 * (n.choose 3 : ℝ) * B +
      6 * (n.choose 4 : ℝ) * D at hFid
  change (∫ ξ, Λsq ξ ∂Measure.pi (fun _ : Fin n => ρ)) =
    2 * (n.choose 2 : ℝ) * A + 6 * (n.choose 3 : ℝ) * B at hΛid
  rw [← hPaProd] at hF2 hFI hrows hΛI hFid hΛid hFbound hΛbound
  have hFb : (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤ s ^ 2 *
      (4 * C ^ 2 * (n.choose 2 : ℝ) +
        48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2 +
        96 * C ^ 4 * (n.choose 4 : ℝ) * a ^ 4) := by
    calc
      _ ≤ ((n.choose 2 : ℝ) * (2 * C) ^ 2 +
          6 * (n.choose 3 : ℝ) * (2 * C) * (2 * C * a) ^ 2 +
          6 * (n.choose 4 : ℝ) * (2 * C * a) ^ 4) * s ^ 2 := hFbound
      _ = _ := by ring
  have hΛb : (∫ ξ, Λsq ξ ∂Pₐ) ≤ s ^ 2 *
      (8 * C ^ 2 * (n.choose 2 : ℝ) +
        48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2) := by
    calc
      _ ≤ (2 * (n.choose 2 : ℝ) * (2 * C) ^ 2 +
          6 * (n.choose 3 : ℝ) * (2 * C) * (2 * C * a) ^ 2) * s ^ 2 := hΛbound
      _ = _ := by ring
  rcases aq_choose_bounds n hn with ⟨hc2, hc3, hc4⟩
  have haN : a * Real.sqrt (n : ℝ) = x := by
    exact div_mul_cancel₀ x hroot.ne'
  have haN2 : a ^ 2 * (n : ℝ) = x ^ 2 := by
    have he := congrArg (fun t : ℝ => t ^ 2) haN
    simpa only [mul_pow, hrootSq] using he
  have haN4 : a ^ 4 * (n : ℝ) ^ 2 = x ^ 4 := by
    have he := congrArg (fun t : ℝ => t ^ 2) haN2
    nlinarith only [he]
  have hAterm : 4 * C ^ 2 * (n.choose 2 : ℝ) ≤
      2 * C ^ 2 * (n : ℝ) ^ 2 := by
    calc
      _ ≤ (4 * C ^ 2) * ((n : ℝ) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hc2 (by positivity)
      _ = _ := by ring
  have hBterm : 48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2 ≤
      8 * C ^ 3 * (n : ℝ) ^ 2 * x ^ 2 := by
    calc
      _ = (8 * C ^ 3 * a ^ 2) * (6 * (n.choose 3 : ℝ)) := by ring
      _ ≤ (8 * C ^ 3 * a ^ 2) * (n : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hc3 (by positivity)
      _ = (8 * C ^ 3 * (n : ℝ) ^ 2) * (a ^ 2 * (n : ℝ)) := by ring
      _ = _ := by rw [haN2]
  have hDterm : 96 * C ^ 4 * (n.choose 4 : ℝ) * a ^ 4 ≤
      4 * C ^ 4 * (n : ℝ) ^ 2 * x ^ 4 := by
    calc
      _ = (16 * C ^ 4 * a ^ 4) * (6 * (n.choose 4 : ℝ)) := by ring
      _ ≤ (16 * C ^ 4 * a ^ 4) * ((n : ℝ) ^ 4 / 4) :=
        mul_le_mul_of_nonneg_left hc4 (by positivity)
      _ = (4 * C ^ 4 * (n : ℝ) ^ 2) * (a ^ 4 * (n : ℝ) ^ 2) := by ring
      _ = _ := by rw [haN4]
  have hRterm : 8 * C ^ 2 * (n.choose 2 : ℝ) ≤
      4 * C ^ 2 * (n : ℝ) ^ 2 := by
    nlinarith only [hAterm]
  have hFpoly : (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤ s ^ 2 * (n : ℝ) ^ 2 *
      (2 * C ^ 2 + 8 * C ^ 3 * x ^ 2 + 4 * C ^ 4 * x ^ 4) := by
    calc
      _ ≤ s ^ 2 * (4 * C ^ 2 * (n.choose 2 : ℝ) +
          48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2 +
          96 * C ^ 4 * (n.choose 4 : ℝ) * a ^ 4) := hFb
      _ ≤ s ^ 2 * (2 * C ^ 2 * (n : ℝ) ^ 2 +
          8 * C ^ 3 * (n : ℝ) ^ 2 * x ^ 2 +
          4 * C ^ 4 * (n : ℝ) ^ 2 * x ^ 4) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add hAterm hBterm) hDterm)
          (sq_nonneg s)
      _ = _ := by ring
  have hΛpoly : (∫ ξ, Λsq ξ ∂Pₐ) ≤ s ^ 2 * (n : ℝ) ^ 2 *
      (4 * C ^ 2 + 8 * C ^ 3 * x ^ 2) := by
    calc
      _ ≤ s ^ 2 * (8 * C ^ 2 * (n.choose 2 : ℝ) +
          48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2) := hΛb
      _ ≤ s ^ 2 * (4 * C ^ 2 * (n : ℝ) ^ 2 +
          8 * C ^ 3 * (n : ℝ) ^ 2 * x ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hRterm hBterm) (sq_nonneg s)
      _ = _ := by ring
  have hC1 : 1 ≤ C := by
    simpa only [Real.exp_zero] using
      (Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2))
  rcases aq_final_polynomials C x hC1 with ⟨hpolyF, hpolyR⟩
  have hFfinal : (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤
      14 * C ^ 4 * s ^ 2 * (n : ℝ) ^ 2 * (1 + x ^ 4) := by
    calc
      _ ≤ s ^ 2 * (n : ℝ) ^ 2 *
          (2 * C ^ 2 + 8 * C ^ 3 * x ^ 2 + 4 * C ^ 4 * x ^ 4) := hFpoly
      _ ≤ s ^ 2 * (n : ℝ) ^ 2 * (14 * C ^ 4 * (1 + x ^ 4)) :=
        mul_le_mul_of_nonneg_left hpolyF (mul_nonneg (sq_nonneg s) (sq_nonneg _))
      _ = _ := by ring
  have hΛfinal : (∫ ξ, Λsq ξ ∂Pₐ) ≤
      14 * C ^ 4 * s ^ 2 * (n : ℝ) ^ 2 * (1 + x ^ 2) := by
    calc
      _ ≤ s ^ 2 * (n : ℝ) ^ 2 * (4 * C ^ 2 + 8 * C ^ 3 * x ^ 2) := hΛpoly
      _ ≤ s ^ 2 * (n : ℝ) ^ 2 * (14 * C ^ 4 * (1 + x ^ 2)) :=
        mul_le_mul_of_nonneg_left hpolyR (mul_nonneg (sq_nonneg s) (sq_nonneg _))
      _ = _ := by ring
  exact ⟨hg, hg2, hg0, hprojectionsecond, hr, hr2, hrsymm, hrcan,
    hv, hs1, hvle, hw, hml, hmu, hLm, hLint, hLb, hLmass, hdevI,
    hdev, hρeq, hρp, hSInt, hI, hmn, hprod, hPaDensity, hPaProd,
    hPaProb, hF2, hFI, hrows, hΛI, hFid, hΛid, hFb, hΛb,
    hFpoly, hΛpoly, hFfinal, hΛfinal⟩

end

end Shao.OQ6.ActualQuadraticTiltMoments
