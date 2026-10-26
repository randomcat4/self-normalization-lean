/- Unit193 original bounded-product statistics. Author source; server validation pending. -/

import Shao.OQ6.BoundedMeanSumMoments
import Shao.OQ6.CanonicalDoubleGhostRowMoments
import Shao.OQ6.CanonicalDoubleGhostScalarMoments
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false
universe u
namespace Shao.OQ6.BoundedProductEnvelopeTails
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ6.StretchedExponentialSumMoments (coordinateSum)
open Shao.OQ6.DoubleGhostSignInvariance (pairedLaw)
open Shao.OQ6.CanonicalDoubleGhostRowMoments (pairedEnergy sampleLaw originalRows)
open Shao.OQ6.CanonicalDoubleGhostScalarMoments (originalUpper)

private def pairSquare
    {Ω : Type u}
    (v : Ω → ℝ)
    (p : Ω × Ω) :
  ℝ :=
  (v p.1 + v p.2) ^ 2

def squareSum
    (n : ℕ)
    {Ω : Type u}
    (w : Ω → ℝ)
    (x : Fin n → Ω) :
  ℝ :=
  ∑ i : Fin n, (w (x i)) ^ 2

def commonMomentScale
    (M : ℝ) :
  ℝ :=
  64 * (M + 1)

def envelopeTailScale
    (M : ℝ) :
  ℝ :=
  4 * M + 8

def squareTailScale
    (M : ℝ) :
  ℝ :=
  Real.exp 1 * (M + 1)

def scalarTailScale
    (M : ℝ) :
  ℝ :=
  8 * Real.exp 1 * envelopeTailScale M

def rowTailScale
    (M : ℝ) :
  ℝ :=
  8 * (Real.exp 1) ^ 2 * (envelopeTailScale M) ^ 2

def tailScale
    (M : ℝ) :
  ℝ :=
  max (squareTailScale M) (max (scalarTailScale M) (rowTailScale M))

private theorem aestronglyMeasurable_of_square_integrable
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    (w : Ω → ℝ)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hSq : Integrable (fun a : Ω => (w a) ^ 2) ν) :
  AEStronglyMeasurable w ν := by
  let squared : Ω → ℝ := fun (a : Ω) => (w a) ^ 2
  let recovered : Ω → ℝ := fun (a : Ω) => Real.sqrt (squared a)
  have hs : AEStronglyMeasurable squared ν := hSq.aestronglyMeasurable
  have hr : AEStronglyMeasurable recovered ν :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hs
  apply hr.congr
  filter_upwards [hW] with a ha
  change Real.sqrt ((w a) ^ 2) = w a
  exact Real.sqrt_sq ha

private theorem pair_seed_bounded_mean
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (v : Ω → ℝ)
    (R M : ℝ)
    (hR0 : 0 ≤ R)
    (hM0 : 0 ≤ M)
    (hv : Measurable v)
    (hv0 : ∀ᵐ a : Ω ∂ν, 0 ≤ v a)
    (hvR : ∀ᵐ a : Ω ∂ν, v a ≤ R)
    (hvSq : Integrable (fun a : Ω => (v a) ^ 2) ν)
    (hvSqBound : (∫ a : Ω, (v a) ^ 2 ∂ν) ≤ M) :
  Measurable (pairSquare v) ∧
  (∀ z : Ω × Ω, 0 ≤ pairSquare v z) ∧
  (∀ᵐ z : Ω × Ω ∂ν.prod ν, pairSquare v z ≤ 4 * R ^ 2) ∧
  Integrable (pairSquare v) (ν.prod ν) ∧
  (∫ z : Ω × Ω, pairSquare v z ∂ν.prod ν) ≤ 4 * M := by
  let v2 : Ω → ℝ := fun (a : Ω) => (v a) ^ 2
  let leftSquare : Ω × Ω → ℝ := fun (z : Ω × Ω) => v2 z.1 * (1 : ℝ)
  let rightSquare : Ω × Ω → ℝ := fun (z : Ω × Ω) => (1 : ℝ) * v2 z.2
  let dominatingSeed : Ω × Ω → ℝ := fun (z : Ω × Ω) => 2 * leftSquare z + 2 * rightSquare z
  let coordinateBounds : Ω × Ω → Prop := fun (z : Ω × Ω) => 0 ≤ v z.1 ∧ v z.1 ≤ R ∧ 0 ≤ v z.2 ∧ v z.2 ≤ R
  have hleft : Integrable leftSquare (ν.prod ν) := by
    simpa [leftSquare, v2] using hvSq.mul_prod (integrable_const (μ := ν) (1 : ℝ))
  have hright : Integrable rightSquare (ν.prod ν) := by
    simpa [rightSquare, v2] using (integrable_const (μ := ν) (1 : ℝ)).mul_prod hvSq
  have hdom : Integrable dominatingSeed (ν.prod ν) := by
    exact (hleft.const_mul 2).add (hright.const_mul 2)
  have hmeas : Measurable (pairSquare v) := by
    exact ((hv.comp measurable_fst).add (hv.comp measurable_snd)).pow_const 2
  have hnn : ∀ z : Ω × Ω, 0 ≤ pairSquare v z := by
    intro z
    exact sq_nonneg _
  have hcoordinate : ∀ᵐ z : Ω × Ω ∂ν.prod ν, coordinateBounds z := by
    filter_upwards [
      (measurePreserving_fst (μ := ν) (ν := ν)).quasiMeasurePreserving.ae hv0,
      (measurePreserving_fst (μ := ν) (ν := ν)).quasiMeasurePreserving.ae hvR,
      (measurePreserving_snd (μ := ν) (ν := ν)).quasiMeasurePreserving.ae hv0,
      (measurePreserving_snd (μ := ν) (ν := ν)).quasiMeasurePreserving.ae hvR] with z h0a hRa h0b hRb
    exact ⟨h0a, hRa, h0b, hRb⟩
  have hbound : ∀ᵐ z : Ω × Ω ∂ν.prod ν, pairSquare v z ≤ 4 * R ^ 2 := by
    filter_upwards [hcoordinate] with z hz
    change 0 ≤ v z.1 ∧ v z.1 ≤ R ∧ 0 ≤ v z.2 ∧ v z.2 ≤ R at hz
    dsimp [pairSquare]
    nlinarith [sq_nonneg (2 * R - (v z.1 + v z.2)),
      mul_nonneg (sub_nonneg.mpr (add_le_add hz.2.1 hz.2.2.2))
        (add_nonneg (by positivity : 0 ≤ 2 * R) (add_nonneg hz.1 hz.2.2.1))]
  have hdominate : ∀ z : Ω × Ω, ‖pairSquare v z‖ ≤ dominatingSeed z := by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn z)]
    dsimp [pairSquare, dominatingSeed, leftSquare, rightSquare, v2]
    nlinarith [sq_nonneg (v z.1 - v z.2)]
  have hint : Integrable (pairSquare v) (ν.prod ν) :=
    hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hdominate)
  have hleftIntegral : (∫ z : Ω × Ω, leftSquare z ∂ν.prod ν) = ∫ a : Ω, (v a) ^ 2 ∂ν := by
    simpa [leftSquare, v2] using integral_prod_mul (μ := ν) (ν := ν) v2 (1 : Ω → ℝ)
  have hrightIntegral : (∫ z : Ω × Ω, rightSquare z ∂ν.prod ν) = ∫ a : Ω, (v a) ^ 2 ∂ν := by
    simpa [rightSquare, v2] using integral_prod_mul (μ := ν) (ν := ν) (1 : Ω → ℝ) v2
  have hdomIntegral : (∫ z : Ω × Ω, dominatingSeed z ∂ν.prod ν) =
      4 * (∫ a : Ω, (v a) ^ 2 ∂ν) := by
    change (∫ z : Ω × Ω, 2 * leftSquare z + 2 * rightSquare z ∂ν.prod ν) = _
    rw [integral_add (hleft.const_mul 2) (hright.const_mul 2),
      integral_const_mul, integral_const_mul, hleftIntegral, hrightIntegral]
    ring
  refine ⟨hmeas, hnn, hbound, hint, ?_⟩
  calc
    (∫ z : Ω × Ω, pairSquare v z ∂ν.prod ν) ≤
        ∫ z : Ω × Ω, dominatingSeed z ∂ν.prod ν := by
      apply integral_mono_ae hint hdom
      exact Filter.Eventually.of_forall fun z => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (hnn z)] using hdominate z
    _ = 4 * (∫ a : Ω, (v a) ^ 2 ∂ν) := hdomIntegral
    _ ≤ 4 * M := mul_le_mul_of_nonneg_left hvSqBound (by norm_num)

private theorem paired_energy_representative_ae
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (w v : Ω → ℝ)
    (hwv : w =ᵐ[ν] v) :
  pairedEnergy n w =ᵐ[pairedLaw n ν]
  coordinateSum (fun _ : Fin n => pairSquare v) := by
  let μPair : Fin n → Measure (Ω × Ω) := fun (_ : Fin n) => ν.prod ν
  letI instμPair : ∀ i : Fin n, IsProbabilityMeasure (μPair i) := fun (_ : Fin n) => inferInstance
  let pairAgreement : Ω × Ω → Prop := fun (z : Ω × Ω) => w z.1 = v z.1 ∧ w z.2 = v z.2
  let allCoordinateAgreement : (Fin n → Ω × Ω) → Prop := fun (z : Fin n → Ω × Ω) => ∀ i : Fin n, pairAgreement (z i)
  let Y : Fin n → (Ω × Ω) → ℝ := fun (_ : Fin n) (z : Ω × Ω) => pairSquare v z
  have hpair : ∀ᵐ z : Ω × Ω ∂ν.prod ν, pairAgreement z := by
    filter_upwards [
      (measurePreserving_fst (μ := ν) (ν := ν)).quasiMeasurePreserving.ae hwv,
      (measurePreserving_snd (μ := ν) (ν := ν)).quasiMeasurePreserving.ae hwv] with z hfst hsnd
    exact ⟨hfst, hsnd⟩
  have hcoords : ∀ i : Fin n, ∀ᵐ z : Fin n → Ω × Ω ∂Measure.pi μPair,
      pairAgreement (z i) := by
    intro i
    exact (measurePreserving_eval μPair i).quasiMeasurePreserving.ae hpair
  have hall : ∀ᵐ z : Fin n → Ω × Ω ∂Measure.pi μPair, allCoordinateAgreement z := by
    exact Filter.eventually_all.2 hcoords
  change ∀ᵐ z : Fin n → Ω × Ω ∂Measure.pi μPair, pairedEnergy n w z = coordinateSum Y z
  filter_upwards [hall] with z hz
  change (∑ i : Fin n, (w (z i).1 + w (z i).2) ^ 2) =
    ∑ i : Fin n, (v (z i).1 + v (z i).2) ^ 2
  apply Finset.sum_congr rfl
  intro i hi
  rcases hz i with ⟨hfst, hsnd⟩
  rw [hfst, hsnd]

private theorem square_sum_representative_ae
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (w v : Ω → ℝ)
    (hwv : w =ᵐ[ν] v) :
  squareSum n w =ᵐ[sampleLaw n ν]
  coordinateSum (fun (_ : Fin n) (a : Ω) => (v a) ^ 2) := by
  let μSample : Fin n → Measure Ω := fun (_ : Fin n) => ν
  letI instμSample : ∀ i : Fin n, IsProbabilityMeasure (μSample i) := fun (_ : Fin n) => hν
  let allCoordinateAgreement : (Fin n → Ω) → Prop := fun (x : Fin n → Ω) => ∀ i : Fin n, w (x i) = v (x i)
  let Y : Fin n → Ω → ℝ := fun (_ : Fin n) (a : Ω) => (v a) ^ 2
  have hcoords : ∀ i : Fin n, ∀ᵐ x : Fin n → Ω ∂Measure.pi μSample,
      w (x i) = v (x i) := by
    intro i
    exact (measurePreserving_eval μSample i).quasiMeasurePreserving.ae hwv
  have hall : ∀ᵐ x : Fin n → Ω ∂Measure.pi μSample, allCoordinateAgreement x := by
    exact Filter.eventually_all.2 hcoords
  change ∀ᵐ x : Fin n → Ω ∂Measure.pi μSample, squareSum n w x = coordinateSum Y x
  filter_upwards [hall] with x hx
  change (∑ i : Fin n, (w (x i)) ^ 2) = ∑ i : Fin n, (v (x i)) ^ 2
  apply Finset.sum_congr rfl
  intro i hi
  rw [hx i]

private theorem strict_moment_markov
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω)
    [hμ : IsFiniteMeasure μ]
    (X : Ω → ℝ)
    (p K : ℝ)
    (hp : 0 < p)
    (hK : 0 < K)
    (hX : ∀ a : Ω, 0 ≤ X a)
    (hXp : Integrable (fun a : Ω => Real.rpow (X a) p) μ)
    (hMoment : Real.rpow (∫ a : Ω, Real.rpow (X a) p ∂μ) (1 / p) ≤ K) :
  μ.real {a : Ω | Real.exp 1 * K < X a} ≤ Real.exp (-p) := by
  let Y : Ω → ℝ := fun (a : Ω) => Real.rpow (X a) p
  let J : ℝ := ∫ a : Ω, Y a ∂μ
  let A : ℝ := Real.rpow (Real.exp 1 * K) p
  let bad : Set Ω := {a : Ω | Real.exp 1 * K < X a}
  let powerClosed : Set Ω := {a : Ω | A ≤ Y a}
  let mass : ℝ := μ.real powerClosed
  have hY : ∀ a : Ω, 0 ≤ Y a := by
    intro a
    exact Real.rpow_nonneg (hX a) p
  have hJ : 0 ≤ J := integral_nonneg_of_ae (Filter.Eventually.of_forall hY)
  have hKp : 0 < Real.rpow K p := Real.rpow_pos_of_pos hK p
  have hA : 0 < A := Real.rpow_pos_of_pos (mul_pos (Real.exp_pos 1) hK) p
  have hJBound : J ≤ Real.rpow K p := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hJ (1 / p)) hMoment hp.le
    have hInverse : Real.rpow (Real.rpow J (1 / p)) p = J := by
      simpa only [Real.rpow_eq_pow, one_div] using
        (Real.rpow_inv_rpow hJ (ne_of_gt hp))
    change Real.rpow (Real.rpow J (1 / p)) p ≤ Real.rpow K p at hh
    simpa only [hInverse] using hh
  have hsubset : bad ⊆ powerClosed := by
    intro a ha
    change Real.rpow (Real.exp 1 * K) p ≤ Real.rpow (X a) p
    exact Real.rpow_le_rpow (le_of_lt (mul_pos (Real.exp_pos 1) hK)) (le_of_lt ha) hp.le
  have hmarkov : A * mass ≤ J := by
    exact mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hY) hXp A
  have hAeq : A = Real.exp p * Real.rpow K p := by
    dsimp [A]
    rw [Real.mul_rpow (le_of_lt (Real.exp_pos 1)) hK.le, Real.exp_one_rpow]
  have hmass : mass ≤ Real.exp (-p) := by
    have hCancel : A * Real.exp (-p) = Real.rpow K p := by
      rw [hAeq]
      calc
        (Real.exp p * Real.rpow K p) * Real.exp (-p) =
            (Real.exp p * Real.exp (-p)) * Real.rpow K p := by ring
        _ = Real.rpow K p := by rw [← Real.exp_add]; simp
    have hScaledBound : A * mass ≤ A * Real.exp (-p) := by
      rw [hCancel]
      exact hmarkov.trans hJBound
    by_contra hNot
    have hPositiveGap : 0 < A * (mass - Real.exp (-p)) :=
      mul_pos hA (sub_pos.mpr (lt_of_not_ge hNot))
    nlinarith only [hScaledBound, hPositiveGap]
  calc
    μ.real bad ≤ μ.real powerClosed := measureReal_mono hsubset
    _ ≤ Real.exp (-p) := hmass

private theorem bounded_window_energy_bounds
    (n : ℕ)
    (R M q : ℝ)
    (hM0 : 0 ≤ M)
    (hq : 2 ≤ q)
    (hWindow : 2 * R ^ 2 * q ≤ (n : ℝ)) :
  4 * M * (n : ℝ) + 8 * R ^ 2 * q ≤ envelopeTailScale M * (n : ℝ) ∧
  4 * M * (n : ℝ) + 16 * R ^ 2 * q ≤ envelopeTailScale M * (n : ℝ) ∧
  M * (n : ℝ) + 2 * R ^ 2 * q ≤ (M + 1) * (n : ℝ) := by
  dsimp [envelopeTailScale]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem zero_statistics
    {Ω : Type u}
    (r : Ω → Ω → ℝ)
    (w : Ω → ℝ)
    (x : Fin 0 → Ω) :
  squareSum 0 w x = 0 ∧ originalUpper 0 r x = 0 ∧ originalRows 0 r x = 0 := by
  constructor
  · simp [squareSum]
  constructor
  · simp [originalUpper]
  · exact Subsingleton.elim _ _

private theorem row_square_strict_threshold
    (L X : ℝ)
    (hL : 0 ≤ L)
    (hX : 0 ≤ X)
    (h : L ^ 2 < X ^ 2) :
  L < X := by
  by_contra hnot
  have hle : X ≤ L := le_of_not_gt hnot
  have hm := mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hL hX)
  nlinarith

theorem bounded_scales_pos
    (M : ℝ)
    (hM0 : 0 ≤ M) :
  0 < commonMomentScale M ∧ 0 < envelopeTailScale M ∧
  0 < squareTailScale M ∧ 0 < scalarTailScale M ∧
  0 < rowTailScale M ∧ 0 < tailScale M := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hc : 0 < envelopeTailScale M := by dsimp [envelopeTailScale]; linarith
  refine ⟨?_, hc, ?_, ?_, ?_, ?_⟩
  · dsimp [commonMomentScale]; positivity
  · dsimp [squareTailScale]; positivity
  · dsimp [scalarTailScale]; positivity
  · dsimp [rowTailScale]; positivity
  · apply lt_of_lt_of_le (show 0 < squareTailScale M by dsimp [squareTailScale]; positivity)
    exact le_max_left _ _

theorem paired_energy_real_moment_from_bound
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (w : Ω → ℝ)
    (R M p : ℝ)
    (hR0 : 0 ≤ R)
    (hM0 : 0 ≤ M)
    (hp : 1 ≤ p)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hWR : ∀ᵐ a : Ω ∂ν, w a ≤ R)
    (hSq : Integrable (fun a : Ω => (w a) ^ 2) ν)
    (hSqBound : (∫ a : Ω, (w a) ^ 2 ∂ν) ≤ M) :
  Integrable (fun z : Fin n → Ω × Ω => Real.rpow (pairedEnergy n w z) p)
    (pairedLaw n ν) ∧
  Real.rpow (∫ z : Fin n → Ω × Ω, Real.rpow (pairedEnergy n w z) p ∂pairedLaw n ν)
    (1 / p) ≤ 4 * M * (n : ℝ) + 8 * R ^ 2 * p := by
  let hw : AEStronglyMeasurable w ν := aestronglyMeasurable_of_square_integrable ν w hW hSq
  let v : Ω → ℝ := hw.mk w
  let μPair : Fin n → Measure (Ω × Ω) := fun (_ : Fin n) => ν.prod ν
  letI instμPair : ∀ i : Fin n, IsProbabilityMeasure (μPair i) := fun (_ : Fin n) => inferInstance
  let Y : Fin n → (Ω × Ω) → ℝ := fun (_ : Fin n) (z : Ω × Ω) => pairSquare v z
  let sumRep : (Fin n → Ω × Ω) → ℝ := coordinateSum Y
  let powerRep : (Fin n → Ω × Ω) → ℝ := fun (z : Fin n → Ω × Ω) => Real.rpow (sumRep z) p
  let powerOriginal : (Fin n → Ω × Ω) → ℝ := fun (z : Fin n → Ω × Ω) => Real.rpow (pairedEnergy n w z) p
  have hwv : w =ᵐ[ν] v := hw.ae_eq_mk
  have hv : Measurable v := hw.measurable_mk
  have hv0 : ∀ᵐ a : Ω ∂ν, 0 ≤ v a := by
    filter_upwards [hW, hwv] with a ha he
    simpa only [← he] using ha
  have hvR : ∀ᵐ a : Ω ∂ν, v a ≤ R := by
    filter_upwards [hWR, hwv] with a ha he
    simpa only [← he] using ha
  have hvSq : Integrable (fun a : Ω => (v a) ^ 2) ν := by
    apply hSq.congr
    filter_upwards [hwv] with a he
    rw [he]
  have hvSqBound : (∫ a : Ω, (v a) ^ 2 ∂ν) ≤ M := by
    calc
      (∫ a : Ω, (v a) ^ 2 ∂ν) = ∫ a : Ω, (w a) ^ 2 ∂ν := by
        apply integral_congr_ae
        filter_upwards [hwv] with a he
        rw [he]
      _ ≤ M := hSqBound
  rcases pair_seed_bounded_mean ν v R M hR0 hM0 hv hv0 hvR hvSq hvSqBound with
    ⟨hYmeas, hYnn, hYbound, hYint, hYmean⟩
  have hraw := Shao.OQ6.BoundedMeanSumMoments.sum_real_moment_from_bound
    (4 * M) (4 * R ^ 2) (by positivity) (by positivity)
    n μPair (fun i => inferInstance) Y
    (fun i => hYmeas)
    (fun i => Filter.Eventually.of_forall hYnn)
    (fun i => hYbound)
    (fun i => hYmean) p hp
  have hRepInt : Integrable powerRep (pairedLaw n ν) := hraw.1
  have hRepBound : Real.rpow (∫ z : Fin n → Ω × Ω, powerRep z ∂pairedLaw n ν) (1 / p) ≤
      4 * M * (n : ℝ) + 8 * R ^ 2 * p := by
    calc
      _ ≤ (n : ℝ) * (4 * M) + 2 * (4 * R ^ 2) * p := hraw.2
      _ = _ := by ring
  have hEnergy := paired_energy_representative_ae n ν w v hwv
  have hPower : powerOriginal =ᵐ[pairedLaw n ν] powerRep := by
    filter_upwards [hEnergy] with z hz
    change Real.rpow (pairedEnergy n w z) p = Real.rpow (coordinateSum Y z) p
    rw [hz]
  refine ⟨hRepInt.congr hPower.symm, ?_⟩
  have hIntegral : (∫ z : Fin n → Ω × Ω, powerOriginal z ∂pairedLaw n ν) =
      ∫ z : Fin n → Ω × Ω, powerRep z ∂pairedLaw n ν := integral_congr_ae hPower
  change Real.rpow (∫ z : Fin n → Ω × Ω, powerOriginal z ∂pairedLaw n ν) (1 / p) ≤ _
  rw [hIntegral]
  exact hRepBound

theorem square_sum_real_moment_from_bound
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (w : Ω → ℝ)
    (R M p : ℝ)
    (hR0 : 0 ≤ R)
    (hM0 : 0 ≤ M)
    (hp : 1 ≤ p)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hWR : ∀ᵐ a : Ω ∂ν, w a ≤ R)
    (hSq : Integrable (fun a : Ω => (w a) ^ 2) ν)
    (hSqBound : (∫ a : Ω, (w a) ^ 2 ∂ν) ≤ M) :
  Integrable (fun x : Fin n → Ω => Real.rpow (squareSum n w x) p) (sampleLaw n ν) ∧
  Real.rpow (∫ x : Fin n → Ω, Real.rpow (squareSum n w x) p ∂sampleLaw n ν)
    (1 / p) ≤ M * (n : ℝ) + 2 * R ^ 2 * p := by
  let hw : AEStronglyMeasurable w ν := aestronglyMeasurable_of_square_integrable ν w hW hSq
  let v : Ω → ℝ := hw.mk w
  let μSample : Fin n → Measure Ω := fun (_ : Fin n) => ν
  letI instμSample : ∀ i : Fin n, IsProbabilityMeasure (μSample i) := fun (_ : Fin n) => hν
  let Y : Fin n → Ω → ℝ := fun (_ : Fin n) (a : Ω) => (v a) ^ 2
  let sumRep : (Fin n → Ω) → ℝ := coordinateSum Y
  let powerRep : (Fin n → Ω) → ℝ := fun (x : Fin n → Ω) => Real.rpow (sumRep x) p
  let powerOriginal : (Fin n → Ω) → ℝ := fun (x : Fin n → Ω) => Real.rpow (squareSum n w x) p
  have hwv : w =ᵐ[ν] v := hw.ae_eq_mk
  have hv : Measurable v := hw.measurable_mk
  have hvSq : Integrable (fun a : Ω => (v a) ^ 2) ν := by
    apply hSq.congr
    filter_upwards [hwv] with a he
    rw [he]
  have hvSqBound : (∫ a : Ω, (v a) ^ 2 ∂ν) ≤ M := by
    calc
      (∫ a : Ω, (v a) ^ 2 ∂ν) = ∫ a : Ω, (w a) ^ 2 ∂ν := by
        apply integral_congr_ae
        filter_upwards [hwv] with a he
        rw [he]
      _ ≤ M := hSqBound
  have hYmeas : ∀ i : Fin n, Measurable (Y i) := by
    intro i
    exact hv.pow_const 2
  have hYnn : ∀ i : Fin n, ∀ᵐ a : Ω ∂μSample i, 0 ≤ Y i a := by
    intro i
    exact Filter.Eventually.of_forall fun a => sq_nonneg _
  have hYbound : ∀ i : Fin n, ∀ᵐ a : Ω ∂μSample i, Y i a ≤ R ^ 2 := by
    intro i
    filter_upwards [hwv, hW, hWR] with a he ha hb
    change (v a) ^ 2 ≤ R ^ 2
    rw [← he]
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (add_nonneg hR0 ha)]
  have hraw := Shao.OQ6.BoundedMeanSumMoments.sum_real_moment_from_bound
    M (R ^ 2) hM0 (sq_nonneg R) n μSample (fun i => inferInstance) Y
    hYmeas hYnn hYbound (fun i => hvSqBound) p hp
  have hRepInt : Integrable powerRep (sampleLaw n ν) := hraw.1
  have hRepBound : Real.rpow (∫ x : Fin n → Ω, powerRep x ∂sampleLaw n ν) (1 / p) ≤
      M * (n : ℝ) + 2 * R ^ 2 * p := by
    calc
      _ ≤ (n : ℝ) * M + 2 * R ^ 2 * p := hraw.2
      _ = _ := by ring
  have hSquare := square_sum_representative_ae n ν w v hwv
  have hPower : powerOriginal =ᵐ[sampleLaw n ν] powerRep := by
    filter_upwards [hSquare] with x hx
    change Real.rpow (squareSum n w x) p = Real.rpow (coordinateSum Y x) p
    rw [hx]
  refine ⟨hRepInt.congr hPower.symm, ?_⟩
  have hIntegral : (∫ x : Fin n → Ω, powerOriginal x ∂sampleLaw n ν) =
      ∫ x : Fin n → Ω, powerRep x ∂sampleLaw n ν := integral_congr_ae hPower
  change Real.rpow (∫ x : Fin n → Ω, powerOriginal x ∂sampleLaw n ν) (1 / p) ≤ _
  rw [hIntegral]
  exact hRepBound

theorem canonical_scalar_bounded_product_moment
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (r : Ω → Ω → ℝ)
    (w : Ω → ℝ)
    (R M q : ℝ)
    (hR0 : 0 ≤ R)
    (hM0 : 0 ≤ M)
    (hr : Measurable (Function.uncurry r))
    (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
    (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
    (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hWR : ∀ᵐ a : Ω ∂ν, w a ≤ R)
    (hSq : Integrable (fun a : Ω => (w a) ^ 2) ν)
    (hSqBound : (∫ a : Ω, (w a) ^ 2 ∂ν) ≤ M)
    (hEnv : ∀ᵐ z : Ω × Ω ∂ν.prod ν, |r z.1 z.2| ≤ w z.1 * w z.2)
    (hq : 2 ≤ q)
    (hsym : ∀ a b : Ω, r a b = r b a) :
  Integrable (fun x : Fin n → Ω => Real.rpow |originalUpper n r x| q) (sampleLaw n ν) ∧
  Real.rpow (∫ x : Fin n → Ω, Real.rpow |originalUpper n r x| q ∂sampleLaw n ν)
    (1 / q) ≤ 8 * q * (4 * M * (n : ℝ) + 8 * R ^ 2 * q) := by
  let energyPower : (Fin n → Ω × Ω) → ℝ := fun (z : Fin n → Ω × Ω) => Real.rpow (pairedEnergy n w z) q
  let statPower : (Fin n → Ω) → ℝ := fun (x : Fin n → Ω) => Real.rpow |originalUpper n r x| q
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hEnergy := paired_energy_real_moment_from_bound n ν w R M q hR0 hM0 hq1 hW hWR hSq hSqBound
  have hScalar := Shao.OQ6.CanonicalDoubleGhostScalarMoments.canonical_scalar_qmoment_bound
    n ν r w q hr hr1 hcR hcL hsym hq hW hEnv hEnergy.1
  refine ⟨hScalar.1, hScalar.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hEnergy.2 (by positivity)

theorem canonical_row_bounded_product_moment
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (r : Ω → Ω → ℝ)
    (w : Ω → ℝ)
    (R M q : ℝ)
    (hR0 : 0 ≤ R)
    (hM0 : 0 ≤ M)
    (hr : Measurable (Function.uncurry r))
    (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
    (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
    (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hWR : ∀ᵐ a : Ω ∂ν, w a ≤ R)
    (hSq : Integrable (fun a : Ω => (w a) ^ 2) ν)
    (hSqBound : (∫ a : Ω, (w a) ^ 2 ∂ν) ≤ M)
    (hEnv : ∀ᵐ z : Ω × Ω ∂ν.prod ν, |r z.1 z.2| ≤ w z.1 * w z.2)
    (hq : 2 ≤ q) :
  Integrable (fun x : Fin n → Ω => Real.rpow ‖originalRows n r x‖ q) (sampleLaw n ν) ∧
  Real.rpow (∫ x : Fin n → Ω, Real.rpow ‖originalRows n r x‖ q ∂sampleLaw n ν)
    (1 / q) ≤ 2 * Real.sqrt q * (4 * M * (n : ℝ) + 8 * R ^ 2 * q) := by
  let energyPower : (Fin n → Ω × Ω) → ℝ := fun (z : Fin n → Ω × Ω) => Real.rpow (pairedEnergy n w z) q
  let statPower : (Fin n → Ω) → ℝ := fun (x : Fin n → Ω) => Real.rpow ‖originalRows n r x‖ q
  have hq1 : 1 ≤ q := by linarith
  have hEnergy := paired_energy_real_moment_from_bound n ν w R M q hR0 hM0 hq1 hW hWR hSq hSqBound
  have hRow := Shao.OQ6.CanonicalDoubleGhostRowMoments.canonical_row_qmoment_bound
    n ν r w q hr hr1 hcR hcL hq hW hEnv hEnergy.1
  refine ⟨hRow.1, hRow.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hEnergy.2 (by positivity)

theorem canonical_bounded_product_moments
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (r : Ω → Ω → ℝ)
    (w : Ω → ℝ)
    (R M q : ℝ)
    (hR0 : 0 ≤ R)
    (hM0 : 0 ≤ M)
    (hr : Measurable (Function.uncurry r))
    (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
    (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
    (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hWR : ∀ᵐ a : Ω ∂ν, w a ≤ R)
    (hSq : Integrable (fun a : Ω => (w a) ^ 2) ν)
    (hSqBound : (∫ a : Ω, (w a) ^ 2 ∂ν) ≤ M)
    (hEnv : ∀ᵐ z : Ω × Ω ∂ν.prod ν, |r z.1 z.2| ≤ w z.1 * w z.2)
    (hq : 2 ≤ q)
    (hsym : ∀ a b : Ω, r a b = r b a) :
  Integrable (fun x : Fin n → Ω => Real.rpow |originalUpper n r x| q) (sampleLaw n ν) ∧
  Integrable (fun x : Fin n → Ω => Real.rpow ‖originalRows n r x‖ (2 * q)) (sampleLaw n ν) ∧
  Real.rpow (∫ x : Fin n → Ω, Real.rpow |originalUpper n r x| q ∂sampleLaw n ν)
    (1 / q) ≤ commonMomentScale M * q * ((n : ℝ) + R ^ 2 * q) ∧
  Real.rpow (∫ x : Fin n → Ω, Real.rpow ‖originalRows n r x‖ (2 * q) ∂sampleLaw n ν)
    (1 / (2 * q)) ≤ commonMomentScale M * Real.sqrt q * ((n : ℝ) + R ^ 2 * q) := by
  let rowExponent : ℝ := 2 * q
  let scalarPower : (Fin n → Ω) → ℝ := fun (x : Fin n → Ω) => Real.rpow |originalUpper n r x| q
  let rowPower : (Fin n → Ω) → ℝ := fun (x : Fin n → Ω) => Real.rpow ‖originalRows n r x‖ rowExponent
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hq0 : 0 ≤ q := by linarith
  have htwoq : 0 ≤ 2 * q := by positivity
  have hrowq : 2 ≤ rowExponent := by dsimp [rowExponent]; linarith
  have hScalar := canonical_scalar_bounded_product_moment n ν r w R M q hR0 hM0
    hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hq hsym
  have hRow := canonical_row_bounded_product_moment n ν r w R M rowExponent hR0 hM0
    hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hrowq
  have hsqrt : Real.sqrt (2 * q) ≤ 2 * Real.sqrt q := by
    by_contra hnot
    have hh : 2 * Real.sqrt q < Real.sqrt (2 * q) := lt_of_not_ge hnot
    have hpos : 0 < Real.sqrt (2 * q) + 2 * Real.sqrt q := by
      linarith [Real.sqrt_nonneg q]
    have hp := mul_pos (sub_pos.mpr hh) hpos
    nlinarith [Real.sq_sqrt hq0, Real.sq_sqrt htwoq]
  refine ⟨hScalar.1, hRow.1, hScalar.2.trans ?_, hRow.2.trans ?_⟩
  · have hd : 0 ≤ q * ((32 * M + 64) * (n : ℝ) + 64 * M * (R ^ 2 * q)) := by positivity
    dsimp [commonMomentScale]
    nlinarith [hd]
  · have hbase : 0 ≤ 4 * M * (n : ℝ) + 16 * R ^ 2 * q := by positivity
    have hfirst : 2 * Real.sqrt (2 * q) * (4 * M * (n : ℝ) + 16 * R ^ 2 * q) ≤
        4 * Real.sqrt q * (4 * M * (n : ℝ) + 16 * R ^ 2 * q) := by
      exact mul_le_mul_of_nonneg_right (by linarith [hsqrt]) hbase
    have hd : 0 ≤ Real.sqrt q * ((48 * M + 64) * (n : ℝ) + 64 * M * (R ^ 2 * q)) := by positivity
    change 2 * Real.sqrt (2 * q) * (4 * M * (n : ℝ) + 8 * R ^ 2 * (2 * q)) ≤ _
    dsimp [commonMomentScale]
    nlinarith [hfirst, hd]

theorem square_sum_bounded_tail
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (w : Ω → ℝ)
    (R M q : ℝ)
    (hR0 : 0 ≤ R)
    (hM0 : 0 ≤ M)
    (hq : 2 ≤ q)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hWR : ∀ᵐ a : Ω ∂ν, w a ≤ R)
    (hSq : Integrable (fun a : Ω => (w a) ^ 2) ν)
    (hSqBound : (∫ a : Ω, (w a) ^ 2 ∂ν) ≤ M)
    (hWindow : 2 * R ^ 2 * q ≤ (n : ℝ)) :
  (sampleLaw n ν).real {x : Fin n → Ω | squareTailScale M * (n : ℝ) < squareSum n w x}
  ≤ Real.exp (-q) := by
  let μ : Measure (Fin n → Ω) := sampleLaw n ν
  letI instμ : IsProbabilityMeasure μ := by dsimp only [μ, sampleLaw]; infer_instance
  let X : (Fin n → Ω) → ℝ := squareSum n w
  let powerX : (Fin n → Ω) → ℝ := fun (x : Fin n → Ω) => Real.rpow (X x) (q)
  by_cases hn : n = 0
  · subst n
    simpa [squareSum] using (Real.exp_pos (-q)).le
  · have hnPos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    let K : ℝ := (M + 1) * (n : ℝ)
    let markovBad : Set (Fin n → Ω) := {x : Fin n → Ω | Real.exp 1 * K < X x}
    have hqPos : 0 < q := by linarith
    have hKPos : 0 < K := by dsimp [K]; positivity
    have hMoment := square_sum_real_moment_from_bound n ν w R M q hR0 hM0
      (by linarith) hW hWR hSq hSqBound
    have hBounds := bounded_window_energy_bounds n R M q hM0 hq hWindow
    have hPowerL1 : Integrable powerX μ := hMoment.1
    have hRoot : Real.rpow (∫ x : Fin n → Ω, powerX x ∂μ) (1 / q) ≤ K :=
      hMoment.2.trans hBounds.2.2
    have hXnonneg : ∀ x : Fin n → Ω, 0 ≤ X x := by
      intro x
      dsimp [X, squareSum]
      exact Finset.sum_nonneg fun i hi => sq_nonneg _
    have hMarkov := strict_moment_markov μ X q K hqPos hKPos hXnonneg hPowerL1 hRoot
    change μ.real markovBad ≤ Real.exp (-q) at hMarkov
    simpa [μ, markovBad, X, K, squareTailScale, mul_assoc] using hMarkov

theorem canonical_scalar_bounded_product_tail
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (r : Ω → Ω → ℝ)
    (w : Ω → ℝ)
    (R M q : ℝ)
    (hR0 : 0 ≤ R)
    (hM0 : 0 ≤ M)
    (hr : Measurable (Function.uncurry r))
    (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
    (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
    (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hWR : ∀ᵐ a : Ω ∂ν, w a ≤ R)
    (hSq : Integrable (fun a : Ω => (w a) ^ 2) ν)
    (hSqBound : (∫ a : Ω, (w a) ^ 2 ∂ν) ≤ M)
    (hEnv : ∀ᵐ z : Ω × Ω ∂ν.prod ν, |r z.1 z.2| ≤ w z.1 * w z.2)
    (hq : 2 ≤ q)
    (hsym : ∀ a b : Ω, r a b = r b a)
    (hWindow : 2 * R ^ 2 * q ≤ (n : ℝ)) :
  (sampleLaw n ν).real {x : Fin n → Ω | scalarTailScale M * (n : ℝ) * q < |originalUpper n r x|}
  ≤ Real.exp (-q) := by
  let μ : Measure (Fin n → Ω) := sampleLaw n ν
  letI instμ : IsProbabilityMeasure μ := by dsimp only [μ, sampleLaw]; infer_instance
  let X : (Fin n → Ω) → ℝ := fun (x : Fin n → Ω) => |originalUpper n r x|
  let powerX : (Fin n → Ω) → ℝ := fun (x : Fin n → Ω) => Real.rpow (X x) (q)
  by_cases hn : n = 0
  · subst n
    simpa [originalUpper] using (Real.exp_pos (-q)).le
  · have hnPos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    let K : ℝ := 8 * envelopeTailScale M * (n : ℝ) * q
    let markovBad : Set (Fin n → Ω) := {x : Fin n → Ω | Real.exp 1 * K < X x}
    have hqPos : 0 < q := by linarith
    have hq0 : 0 ≤ q := hqPos.le
    have hCen : 0 < envelopeTailScale M := (bounded_scales_pos M hM0).2.1
    have hKPos : 0 < K := by dsimp [K]; positivity
    have hMoment := canonical_scalar_bounded_product_moment n ν r w R M q hR0 hM0
      hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hq hsym
    have hBounds := bounded_window_energy_bounds n R M q hM0 hq hWindow
    have hPowerL1 : Integrable powerX μ := hMoment.1
    have hRoot : Real.rpow (∫ x : Fin n → Ω, powerX x ∂μ) (1 / q) ≤ K := by
      calc
        _ ≤ 8 * q * (4 * M * (n : ℝ) + 8 * R ^ 2 * q) := hMoment.2
        _ ≤ 8 * q * (envelopeTailScale M * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hBounds.1 (by positivity)
        _ = K := by dsimp [K]; ring
    have hXnonneg : ∀ x : Fin n → Ω, 0 ≤ X x := by
      intro x
      exact abs_nonneg _
    have hMarkov := strict_moment_markov μ X q K hqPos hKPos hXnonneg hPowerL1 hRoot
    change μ.real markovBad ≤ Real.exp (-q) at hMarkov
    simpa [μ, markovBad, X, K, scalarTailScale, mul_assoc, mul_left_comm, mul_comm] using hMarkov

theorem canonical_row_bounded_product_tail
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (r : Ω → Ω → ℝ)
    (w : Ω → ℝ)
    (R M q : ℝ)
    (hR0 : 0 ≤ R)
    (hM0 : 0 ≤ M)
    (hr : Measurable (Function.uncurry r))
    (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
    (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
    (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hWR : ∀ᵐ a : Ω ∂ν, w a ≤ R)
    (hSq : Integrable (fun a : Ω => (w a) ^ 2) ν)
    (hSqBound : (∫ a : Ω, (w a) ^ 2 ∂ν) ≤ M)
    (hEnv : ∀ᵐ z : Ω × Ω ∂ν.prod ν, |r z.1 z.2| ≤ w z.1 * w z.2)
    (hq : 2 ≤ q)
    (hWindow : 2 * R ^ 2 * q ≤ (n : ℝ)) :
  (sampleLaw n ν).real {x : Fin n → Ω | rowTailScale M * (n : ℝ) ^ 2 * q < ‖originalRows n r x‖ ^ 2}
  ≤ Real.exp (-(2 * q)) := by
  let μ : Measure (Fin n → Ω) := sampleLaw n ν
  letI instμ : IsProbabilityMeasure μ := by dsimp only [μ, sampleLaw]; infer_instance
  let X : (Fin n → Ω) → ℝ := fun (x : Fin n → Ω) => ‖originalRows n r x‖
  let powerX : (Fin n → Ω) → ℝ := fun (x : Fin n → Ω) => Real.rpow (X x) (2 * q)
  by_cases hn : n = 0
  · subst n
    have hz : ∀ x : Fin 0 → Ω, originalRows 0 r x = 0 := by
      intro x
      exact (zero_statistics r w x).2.2
    simpa [hz] using (Real.exp_pos (-(2 * q))).le
  · have hnPos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    let K : ℝ := 2 * Real.sqrt (2 * q) * envelopeTailScale M * (n : ℝ)
    let markovBad : Set (Fin n → Ω) := {x : Fin n → Ω | Real.exp 1 * K < X x}
    let squareBad : Set (Fin n → Ω) := {x : Fin n → Ω | rowTailScale M * (n : ℝ) ^ 2 * q < (X x) ^ 2}
    have hqPos : 0 < q := by linarith
    have htwoqPos : 0 < 2 * q := by positivity
    have htwoq : 2 ≤ 2 * q := by linarith
    have hCen : 0 < envelopeTailScale M := (bounded_scales_pos M hM0).2.1
    have hsqrtPos : 0 < Real.sqrt (2 * q) := by
      have hnonneg := Real.sqrt_nonneg (2 * q)
      have hsquare := Real.sq_sqrt htwoqPos.le
      nlinarith
    have hKPos : 0 < K := by dsimp [K]; positivity
    have hMoment := canonical_row_bounded_product_moment n ν r w R M (2 * q) hR0 hM0
      hr hr1 hcR hcL hW hWR hSq hSqBound hEnv htwoq
    have hBounds := bounded_window_energy_bounds n R M q hM0 hq hWindow
    have hPowerL1 : Integrable powerX μ := hMoment.1
    have hRoot : Real.rpow (∫ x : Fin n → Ω, powerX x ∂μ) (1 / (2 * q)) ≤ K := by
      calc
        _ ≤ 2 * Real.sqrt (2 * q) * (4 * M * (n : ℝ) + 8 * R ^ 2 * (2 * q)) := hMoment.2
        _ = 2 * Real.sqrt (2 * q) * (4 * M * (n : ℝ) + 16 * R ^ 2 * q) := by ring
        _ ≤ 2 * Real.sqrt (2 * q) * (envelopeTailScale M * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hBounds.2.1 (by positivity)
        _ = K := by dsimp [K]; ring
    have hXnonneg : ∀ x : Fin n → Ω, 0 ≤ X x := by
      intro x
      exact norm_nonneg _
    have hMarkov := strict_moment_markov μ X (2 * q) K htwoqPos hKPos hXnonneg hPowerL1 hRoot
    change μ.real markovBad ≤ Real.exp (-(2 * q)) at hMarkov
    have hKsquare : (Real.exp 1 * K) ^ 2 = rowTailScale M * (n : ℝ) ^ 2 * q := by
      dsimp [K, rowTailScale]
      simp only [mul_pow, Real.sq_sqrt htwoqPos.le]
      ring
    have hsubset : squareBad ⊆ markovBad := by
      intro x hx
      apply row_square_strict_threshold (Real.exp 1 * K) (X x)
        (le_of_lt (mul_pos (Real.exp_pos 1) hKPos)) (hXnonneg x)
      rw [hKsquare]
      exact hx
    have hProbability : μ.real squareBad ≤ Real.exp (-(2 * q)) :=
      (measureReal_mono hsubset).trans hMarkov
    simpa [μ, squareBad, X] using hProbability

theorem canonical_bounded_product_tails
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (r : Ω → Ω → ℝ)
    (w : Ω → ℝ)
    (R M q : ℝ)
    (hR0 : 0 ≤ R)
    (hM0 : 0 ≤ M)
    (hr : Measurable (Function.uncurry r))
    (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
    (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
    (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hWR : ∀ᵐ a : Ω ∂ν, w a ≤ R)
    (hSq : Integrable (fun a : Ω => (w a) ^ 2) ν)
    (hSqBound : (∫ a : Ω, (w a) ^ 2 ∂ν) ≤ M)
    (hEnv : ∀ᵐ z : Ω × Ω ∂ν.prod ν, |r z.1 z.2| ≤ w z.1 * w z.2)
    (hq : 2 ≤ q)
    (hsym : ∀ a b : Ω, r a b = r b a)
    (hWindow : 2 * R ^ 2 * q ≤ (n : ℝ)) :
  (sampleLaw n ν).real {x : Fin n → Ω | tailScale M * (n : ℝ) < squareSum n w x} ≤ Real.exp (-q) ∧
  (sampleLaw n ν).real {x : Fin n → Ω | tailScale M * (n : ℝ) * q < |originalUpper n r x|} ≤ Real.exp (-q) ∧
  (sampleLaw n ν).real {x : Fin n → Ω | tailScale M * (n : ℝ) ^ 2 * q < ‖originalRows n r x‖ ^ 2} ≤ Real.exp (-(2 * q)) ∧
  (sampleLaw n ν).real {x : Fin n → Ω | tailScale M * (n : ℝ) < squareSum n w x} +
    (sampleLaw n ν).real {x : Fin n → Ω | tailScale M * (n : ℝ) * q < |originalUpper n r x|} +
    (sampleLaw n ν).real {x : Fin n → Ω | tailScale M * (n : ℝ) ^ 2 * q < ‖originalRows n r x‖ ^ 2} ≤ 2 * Real.exp (-q) + Real.exp (-(2 * q)) ∧
  (sampleLaw n ν).real {x : Fin n → Ω | tailScale M * (n : ℝ) < squareSum n w x} +
    (sampleLaw n ν).real {x : Fin n → Ω | tailScale M * (n : ℝ) * q < |originalUpper n r x|} +
    (sampleLaw n ν).real {x : Fin n → Ω | tailScale M * (n : ℝ) ^ 2 * q < ‖originalRows n r x‖ ^ 2} ≤ 3 * Real.exp (-q) := by
  let μ : Measure (Fin n → Ω) := sampleLaw n ν
  letI instμ : IsProbabilityMeasure μ := by dsimp only [μ, sampleLaw]; infer_instance
  let badQ : Set (Fin n → Ω) := {x : Fin n → Ω | tailScale M * (n : ℝ) < squareSum n w x}
  let badF : Set (Fin n → Ω) := {x : Fin n → Ω | tailScale M * (n : ℝ) * q < |originalUpper n r x|}
  let badL : Set (Fin n → Ω) := {x : Fin n → Ω | tailScale M * (n : ℝ) ^ 2 * q < ‖originalRows n r x‖ ^ 2}
  let ownQ : Set (Fin n → Ω) := {x : Fin n → Ω | squareTailScale M * (n : ℝ) < squareSum n w x}
  let ownF : Set (Fin n → Ω) := {x : Fin n → Ω | scalarTailScale M * (n : ℝ) * q < |originalUpper n r x|}
  let ownL : Set (Fin n → Ω) := {x : Fin n → Ω | rowTailScale M * (n : ℝ) ^ 2 * q < ‖originalRows n r x‖ ^ 2}
  let massQ : ℝ := μ.real badQ
  let massF : ℝ := μ.real badF
  let massL : ℝ := μ.real badL
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hq0 : 0 ≤ q := by linarith
  have hQscale : squareTailScale M ≤ tailScale M := le_max_left _ _
  have hFscale : scalarTailScale M ≤ tailScale M :=
    le_trans (le_max_left (scalarTailScale M) (rowTailScale M))
      (le_max_right (squareTailScale M) (max (scalarTailScale M) (rowTailScale M)))
  have hLscale : rowTailScale M ≤ tailScale M :=
    le_trans (le_max_right (scalarTailScale M) (rowTailScale M))
      (le_max_right (squareTailScale M) (max (scalarTailScale M) (rowTailScale M)))
  have hQsubset : badQ ⊆ ownQ := by
    intro x hx
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hQscale hn0) hx
  have hFsubset : badF ⊆ ownF := by
    intro x hx
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hFscale hn0) hq0) hx
  have hLsubset : badL ⊆ ownL := by
    intro x hx
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLscale (sq_nonneg (n : ℝ))) hq0) hx
  have hQ : μ.real ownQ ≤ Real.exp (-q) :=
    square_sum_bounded_tail n ν w R M q hR0 hM0 hq hW hWR hSq hSqBound hWindow
  have hF : μ.real ownF ≤ Real.exp (-q) :=
    canonical_scalar_bounded_product_tail n ν r w R M q hR0 hM0
      hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hq hsym hWindow
  have hL : μ.real ownL ≤ Real.exp (-(2 * q)) :=
    canonical_row_bounded_product_tail n ν r w R M q hR0 hM0
      hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hq hWindow
  have hmassQ : massQ ≤ Real.exp (-q) := (measureReal_mono hQsubset).trans hQ
  have hmassF : massF ≤ Real.exp (-q) := (measureReal_mono hFsubset).trans hF
  have hmassL : massL ≤ Real.exp (-(2 * q)) := (measureReal_mono hLsubset).trans hL
  have hsum : massQ + massF + massL ≤ 2 * Real.exp (-q) + Real.exp (-(2 * q)) := by
    linarith
  have hExp : Real.exp (-(2 * q)) ≤ Real.exp (-q) := Real.exp_le_exp.mpr (by linarith)
  refine ⟨hmassQ, hmassF, hmassL, hsum, ?_⟩
  linarith

end
end Shao.OQ6.BoundedProductEnvelopeTails
