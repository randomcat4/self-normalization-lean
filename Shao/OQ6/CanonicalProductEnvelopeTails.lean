import Shao.OQ6.StretchedExponentialSumMoments
import Shao.OQ6.CanonicalDoubleGhostRowMoments
import Shao.OQ6.CanonicalDoubleGhostScalarMoments
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false
universe u
namespace Shao.OQ6.CanonicalProductEnvelopeTails
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ6.StretchedExponentialSumMoments
open Shao.OQ6.DoubleGhostSignInvariance
open Shao.OQ6.CanonicalDoubleGhostRowMoments
open Shao.OQ6.CanonicalDoubleGhostScalarMoments

private def rootRecovery
    (α : ℝ)
    (t : ℝ) :
  ℝ :=
  Real.rpow t (1 / α)

private def pairSquare
    {Ω : Type u}
    (v : Ω → ℝ)
    (p : Ω × Ω) :
  ℝ :=
  (v p.1 + v p.2) ^ 2

def envelopeMomentScale
    (α : ℝ)
    (τ : ℝ)
    (M : ℝ) :
  ℝ :=
  sumMomentScale (α / 2) (τ / Real.rpow 2 α) (M ^ 2)

def commonMomentScale
    (α : ℝ)
    (τ : ℝ)
    (M : ℝ) :
  ℝ :=
  max (8 * envelopeMomentScale α τ M) (2 * Real.sqrt 2 * Real.rpow 2 (2 / α) * envelopeMomentScale α τ M)

def scalarTailScale
    (α : ℝ)
    (τ : ℝ)
    (M : ℝ) :
  ℝ :=
  16 * Real.exp 1 * envelopeMomentScale α τ M

def rowTailScale
    (α : ℝ)
    (τ : ℝ)
    (M : ℝ) :
  ℝ :=
  32 * (Real.exp 1) ^ 2 * (envelopeMomentScale α τ M) ^ 2

def tailScale
    (α : ℝ)
    (τ : ℝ)
    (M : ℝ) :
  ℝ :=
  max (scalarTailScale α τ M) (rowTailScale α τ M)

private theorem continuous_rootRecovery
    (α : ℝ)
    (hα : 0 < α) :
  Continuous (rootRecovery α) := by
  change Continuous (fun t : ℝ => t ^ (1 / α))
  exact Real.continuous_rpow_const (q := 1 / α) (by positivity)

private theorem rootRecovery_rpow
    (α : ℝ)
    (a : ℝ)
    (hα : 0 < α)
    (ha : 0 ≤ a) :
  rootRecovery α (Real.rpow a α) = a := by
  simpa only [rootRecovery, Real.rpow_eq_pow, one_div] using
    (Real.rpow_rpow_inv ha (ne_of_gt hα))

private theorem aestronglyMeasurable_of_exp_moment
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    (w : Ω → ℝ)
    (α : ℝ)
    (τ : ℝ)
    (hα : 0 < α)
    (hτ : 0 < τ)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hExp : Integrable (fun a : Ω => Real.exp (τ * Real.rpow (w a) α)) ν) :
  AEStronglyMeasurable w ν := by
  let powerEnvelope : Ω → ℝ := fun a : Ω => Real.rpow (w a) α
  let rootedEnvelope : Ω → ℝ := fun a : Ω => rootRecovery α (Real.rpow (w a) α)
  have hPower : AEMeasurable powerEnvelope ν := by
    exact Real.aemeasurable_of_aemeasurable_exp_mul (ne_of_gt hτ) hExp.aemeasurable
  have hRoot : AEStronglyMeasurable rootedEnvelope ν := by
    exact (continuous_rootRecovery α hα).comp_aestronglyMeasurable
      hPower.aestronglyMeasurable
  apply hRoot.congr
  filter_upwards [hW] with a ha
  exact rootRecovery_rpow α (w a) hα ha

private theorem sum_rpow_le_product_seed_scale
    (α : ℝ)
    (a : ℝ)
    (b : ℝ)
    (hα : 0 < α)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
  Real.rpow (a + b) α ≤ Real.rpow 2 α * (Real.rpow a α + Real.rpow b α) := by
  rcases le_total a b with hab | hba
  · calc
      Real.rpow (a + b) α ≤ Real.rpow (2 * b) α :=
        Real.rpow_le_rpow (add_nonneg ha hb) (by linarith) (le_of_lt hα)
      _ = Real.rpow 2 α * Real.rpow b α := by
        exact Real.mul_rpow (x := 2) (y := b) (z := α) (by norm_num) hb
      _ ≤ Real.rpow 2 α * (Real.rpow a α + Real.rpow b α) :=
        mul_le_mul_of_nonneg_left
          (by
            have hNonneg : 0 ≤ Real.rpow a α := Real.rpow_nonneg ha α
            linarith only [hNonneg])
          (Real.rpow_nonneg (x := 2) (by norm_num) α)
  · calc
      Real.rpow (a + b) α ≤ Real.rpow (2 * a) α :=
        Real.rpow_le_rpow (add_nonneg ha hb) (by linarith) (le_of_lt hα)
      _ = Real.rpow 2 α * Real.rpow a α := by
        exact Real.mul_rpow (x := 2) (y := a) (z := α) (by norm_num) ha
      _ ≤ Real.rpow 2 α * (Real.rpow a α + Real.rpow b α) :=
        mul_le_mul_of_nonneg_left
          (by
            have hNonneg : 0 ≤ Real.rpow b α := Real.rpow_nonneg hb α
            linarith only [hNonneg])
          (Real.rpow_nonneg (x := 2) (by norm_num) α)

private theorem pair_exponential_domination
    (α : ℝ)
    (τ : ℝ)
    (a : ℝ)
    (b : ℝ)
    (hα : 0 < α)
    (hτ : 0 < τ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
  Real.exp ((τ / Real.rpow 2 α) * Real.rpow ((a + b) ^ 2) (α / 2)) ≤ Real.exp (τ * Real.rpow a α) * Real.exp (τ * Real.rpow b α) := by
  have hTwo : 0 < Real.rpow 2 α :=
    Real.rpow_pos_of_pos (x := 2) (by norm_num) α
  have hPower :
      Real.rpow ((a + b) ^ 2) (α / 2) = Real.rpow (a + b) α := by
    have hSquare : Real.rpow (a + b) (2 : ℝ) = (a + b) ^ 2 :=
      Real.rpow_two (a + b)
    have hMul :
        Real.rpow (a + b) ((2 : ℝ) * (α / 2)) =
          Real.rpow (Real.rpow (a + b) (2 : ℝ)) (α / 2) :=
      Real.rpow_mul (add_nonneg ha hb) 2 (α / 2)
    rw [← hSquare, ← hMul]
    congr 1
    ring
  calc
    Real.exp ((τ / Real.rpow 2 α) * Real.rpow ((a + b) ^ 2) (α / 2)) ≤
        Real.exp (τ * Real.rpow a α + τ * Real.rpow b α) := by
      apply Real.exp_le_exp.mpr
      rw [hPower]
      calc
        (τ / Real.rpow 2 α) * Real.rpow (a + b) α ≤
            (τ / Real.rpow 2 α) *
              (Real.rpow 2 α * (Real.rpow a α + Real.rpow b α)) :=
          mul_le_mul_of_nonneg_left (sum_rpow_le_product_seed_scale α a b hα ha hb)
            (by positivity)
        _ = τ * Real.rpow a α + τ * Real.rpow b α := by
          field_simp [ne_of_gt hTwo] <;> ring
    _ = Real.exp (τ * Real.rpow a α) * Real.exp (τ * Real.rpow b α) :=
      Real.exp_add _ _

private theorem paired_seed_exponential_moment
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (v : Ω → ℝ)
    (α : ℝ)
    (τ : ℝ)
    (M : ℝ)
    (hα : 0 < α)
    (hτ : 0 < τ)
    (hM : 1 ≤ M)
    (hv : Measurable v)
    (hv0 : ∀ᵐ a : Ω ∂ν, 0 ≤ v a)
    (hvExp : Integrable (fun a : Ω => Real.exp (τ * Real.rpow (v a) α)) ν)
    (hvBound : (∫ a : Ω, Real.exp (τ * Real.rpow (v a) α) ∂ν) ≤ M) :
  Integrable (fun p : Ω × Ω => Real.exp ((τ / Real.rpow 2 α) * Real.rpow (pairSquare v p) (α / 2))) (ν.prod ν) ∧
  (∫ p : Ω × Ω, Real.exp ((τ / Real.rpow 2 α) * Real.rpow (pairSquare v p) (α / 2)) ∂ν.prod ν) ≤ M ^ 2 := by
  letI instPairProbability : IsProbabilityMeasure (ν.prod ν) := inferInstanceAs (IsProbabilityMeasure (ν.prod ν))
  let E : Ω → ℝ := fun a : Ω => Real.exp (τ * Real.rpow (v a) α)
  let Y : Ω × Ω → ℝ := pairSquare v
  let G : Ω × Ω → ℝ := fun p : Ω × Ω => Real.exp ((τ / Real.rpow 2 α) * Real.rpow (Y p) (α / 2))
  let B : Ω × Ω → ℝ := fun p : Ω × Ω => E p.1 * E p.2
  let firstProjection : Ω × Ω → Ω := Prod.fst
  let secondProjection : Ω × Ω → Ω := Prod.snd
  have hE : Integrable E ν := hvExp
  have hY : Measurable Y := by
    change Measurable (fun p : Ω × Ω => (v p.1 + v p.2) ^ 2)
    fun_prop
  have hG : Measurable G := by
    dsimp [G]
    fun_prop
  have hB : Integrable B (ν.prod ν) := hE.mul_prod hE
  have hFirst : MeasurePreserving firstProjection (ν.prod ν) ν :=
    measurePreserving_fst (μ := ν) (ν := ν)
  have hSecond : MeasurePreserving secondProjection (ν.prod ν) ν :=
    measurePreserving_snd (μ := ν) (ν := ν)
  have hGood : ∀ᵐ p : Ω × Ω ∂ν.prod ν, 0 ≤ v p.1 ∧ 0 ≤ v p.2 := by
    exact (hFirst.quasiMeasurePreserving.ae hv0).and
      (hSecond.quasiMeasurePreserving.ae hv0)
  have hDom : ∀ᵐ p : Ω × Ω ∂ν.prod ν, G p ≤ B p := by
    filter_upwards [hGood] with p hp
    exact pair_exponential_domination α τ (v p.1) (v p.2) hα hτ hp.1 hp.2
  have hGInt : Integrable G (ν.prod ν) := by
    apply hB.mono' hG.aestronglyMeasurable
    filter_upwards [hDom] with p hp
    simpa only [Real.norm_eq_abs, G, abs_of_pos (Real.exp_pos _)] using hp
  have hENonneg : 0 ≤ ∫ a : Ω, E a ∂ν := by
    apply integral_nonneg_of_ae
    exact ae_of_all ν (fun a => le_of_lt (Real.exp_pos _))
  have hEBound : (∫ a : Ω, E a ∂ν) ≤ M := hvBound
  have hProductBound : (∫ a : Ω, E a ∂ν) * (∫ a : Ω, E a ∂ν) ≤ M ^ 2 := by
    have hMNonneg : 0 ≤ M := by linarith
    have hProduct :=
      mul_nonneg (sub_nonneg.mpr hEBound) (add_nonneg hMNonneg hENonneg)
    nlinarith
  refine ⟨hGInt, ?_⟩
  calc
    (∫ p : Ω × Ω, G p ∂ν.prod ν) ≤ ∫ p : Ω × Ω, B p ∂ν.prod ν :=
      integral_mono_ae hGInt hB hDom
    _ = (∫ a : Ω, E a ∂ν) * (∫ a : Ω, E a ∂ν) := integral_prod_mul E E
    _ ≤ M ^ 2 := hProductBound

private theorem paired_energy_representative_ae
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (w : Ω → ℝ)
    (v : Ω → ℝ)
    (hwv : w =ᵐ[ν] v) :
  pairedEnergy n w =ᵐ[pairedLaw n ν] coordinateSum (fun _ : Fin n => pairSquare v) := by
  letI instPairProbability : IsProbabilityMeasure (ν.prod ν) := inferInstanceAs (IsProbabilityMeasure (ν.prod ν))
  letI instPairedProbability : IsProbabilityMeasure (pairedLaw n ν) := inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => ν.prod ν)))
  let pairEval : Fin n → (Fin n → Ω × Ω) → Ω × Ω := fun (i : Fin n) (z : Fin n → Ω × Ω) => z i
  let firstEval : Fin n → (Fin n → Ω × Ω) → Ω := fun (i : Fin n) (z : Fin n → Ω × Ω) => (z i).1
  let secondEval : Fin n → (Fin n → Ω × Ω) → Ω := fun (i : Fin n) (z : Fin n → Ω × Ω) => (z i).2
  have hEval (i : Fin n) :
      MeasurePreserving (pairEval i) (pairedLaw n ν) (ν.prod ν) := by
    simpa only [pairEval, pairedLaw] using
      (measurePreserving_eval (fun _ : Fin n => ν.prod ν) i)
  have hFirst (i : Fin n) :
      MeasurePreserving (firstEval i) (pairedLaw n ν) ν := by
    exact (measurePreserving_fst (μ := ν) (ν := ν)).comp (hEval i)
  have hSecond (i : Fin n) :
      MeasurePreserving (secondEval i) (pairedLaw n ν) ν := by
    exact (measurePreserving_snd (μ := ν) (ν := ν)).comp (hEval i)
  have hAll : ∀ᵐ z : Fin n → Ω × Ω ∂pairedLaw n ν,
      ∀ i : Fin n, w (z i).1 = v (z i).1 ∧ w (z i).2 = v (z i).2 := by
    apply ae_all_iff.mpr
    intro i
    exact ((hFirst i).quasiMeasurePreserving.ae hwv).and
      ((hSecond i).quasiMeasurePreserving.ae hwv)
  filter_upwards [hAll] with z hz
  unfold pairedEnergy Shao.OQ6.FiniteMatrixSignEnergy.weightEnergy ghostWeight
    coordinateSum pairSquare
  apply Finset.sum_congr rfl
  intro i hi
  rw [(hz i).1, (hz i).2]

theorem envelope_scales_pos
    (α : ℝ)
    (τ : ℝ)
    (M : ℝ)
    (hα : 0 < α)
    (hτ : 0 < τ)
    (hM : 1 ≤ M) :
  0 < envelopeMomentScale α τ M ∧
  0 < commonMomentScale α τ M ∧
  0 < scalarTailScale α τ M ∧
  0 < rowTailScale α τ M ∧
  0 < tailScale α τ M := by
  have hMPos : 0 < M := by linarith
  have hTwoPow : 0 < Real.rpow 2 α :=
    Real.rpow_pos_of_pos (x := 2) (by norm_num) α
  have hBeta : 0 < α / 2 := by positivity
  have hPairTau : 0 < τ / Real.rpow 2 α := div_pos hτ hTwoPow
  have hScalarMoment :
      0 < scalarMomentScale (α / 2) (τ / Real.rpow 2 α) (M ^ 2) := by
    change 0 < M ^ 2 *
      Real.rpow ((τ / Real.rpow 2 α) * (α / 2)) (-(1 / (α / 2)))
    exact mul_pos (by positivity)
      (Real.rpow_pos_of_pos (mul_pos hPairTau hBeta) _)
  have hC : 0 < envelopeMomentScale α τ M := by
    change 0 < 2 * Real.rpow 2 (1 / (α / 2)) *
      scalarMomentScale (α / 2) (τ / Real.rpow 2 α) (M ^ 2)
    exact mul_pos
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos (x := 2) (by norm_num) _))
      hScalarMoment
  have hCommon : 0 < commonMomentScale α τ M := by
    apply lt_of_lt_of_le (show 0 < 8 * envelopeMomentScale α τ M by positivity)
    exact le_max_left _ _
  have hScalar : 0 < scalarTailScale α τ M := by
    unfold scalarTailScale
    positivity
  have hRow : 0 < rowTailScale α τ M := by
    unfold rowTailScale
    positivity
  have hTail : 0 < tailScale α τ M := by
    exact lt_of_lt_of_le hScalar (le_max_left _ _)
  exact ⟨hC, hCommon, hScalar, hRow, hTail⟩

theorem paired_energy_real_moment_from_exp
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (w : Ω → ℝ)
    (α : ℝ)
    (τ : ℝ)
    (M : ℝ)
    (p : ℝ)
    (hα : 0 < α)
    (hα2 : α ≤ 2)
    (hτ : 0 < τ)
    (hM : 1 ≤ M)
    (hp : 1 ≤ p)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hExp : Integrable (fun a : Ω => Real.exp (τ * Real.rpow (w a) α)) ν)
    (hExpBound : (∫ a : Ω, Real.exp (τ * Real.rpow (w a) α) ∂ν) ≤ M) :
  Integrable (fun z : Fin n → Ω × Ω => Real.rpow (pairedEnergy n w z) p) (pairedLaw n ν) ∧
  Real.rpow (∫ z : Fin n → Ω × Ω, Real.rpow (pairedEnergy n w z) p ∂pairedLaw n ν) (1 / p) ≤
    envelopeMomentScale α τ M * ((n : ℝ) + Real.rpow p (2 / α)) := by
  letI instPairProbability : IsProbabilityMeasure (ν.prod ν) := inferInstanceAs (IsProbabilityMeasure (ν.prod ν))
  letI instPairedProbability : IsProbabilityMeasure (pairedLaw n ν) := inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => ν.prod ν)))
  let hw : AEStronglyMeasurable w ν := aestronglyMeasurable_of_exp_moment ν w α τ hα hτ hW hExp
  let v : Ω → ℝ := hw.mk w
  let β : ℝ := α / 2
  let τPair : ℝ := τ / Real.rpow 2 α
  let MPair : ℝ := M ^ 2
  let μPair : Fin n → Measure (Ω × Ω) := fun _ : Fin n => ν.prod ν
  letI instCoordinateProbability : (i : Fin n) → IsProbabilityMeasure (μPair i) := fun _ : Fin n => inferInstanceAs (IsProbabilityMeasure (ν.prod ν))
  let YPair : Fin n → (Ω × Ω) → ℝ := fun _ : Fin n => pairSquare v
  have hv : Measurable v := hw.measurable_mk
  have hwv : w =ᵐ[ν] v := hw.ae_eq_mk
  have hv0 : ∀ᵐ a : Ω ∂ν, 0 ≤ v a := by
    filter_upwards [hW, hwv] with a ha hwa
    simpa only [← hwa] using ha
  have hvExp : Integrable (fun a : Ω => Real.exp (τ * Real.rpow (v a) α)) ν := by
    apply hExp.congr
    filter_upwards [hwv] with a ha
    rw [ha]
  have hvBound : (∫ a : Ω, Real.exp (τ * Real.rpow (v a) α) ∂ν) ≤ M := by
    calc
      (∫ a : Ω, Real.exp (τ * Real.rpow (v a) α) ∂ν) =
          ∫ a : Ω, Real.exp (τ * Real.rpow (w a) α) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hwv] with a ha
        rw [ha]
      _ ≤ M := hExpBound
  have hSeed := paired_seed_exponential_moment ν v α τ M hα hτ hM hv hv0 hvExp hvBound
  have hβ : 0 < β := by dsimp [β]; linarith
  have hβOne : β ≤ 1 := by dsimp [β]; linarith
  have hτPair : 0 < τPair := by
    dsimp [τPair]
    positivity
  have hMPair : 1 ≤ MPair := by
    dsimp [MPair]
    have hProduct := mul_nonneg (sub_nonneg.mpr hM) (show 0 ≤ M + 1 by linarith)
    nlinarith
  have hYMeasurable : ∀ i : Fin n, Measurable (YPair i) := by
    intro i
    change Measurable (fun p : Ω × Ω => (v p.1 + v p.2) ^ 2)
    fun_prop
  have hYNonneg : ∀ i : Fin n, ∀ᵐ a : Ω × Ω ∂μPair i, 0 ≤ YPair i a := by
    intro i
    exact ae_of_all (μPair i) (fun a => sq_nonneg _)
  have hYExpInt : ∀ i : Fin n,
      Integrable (fun a : Ω × Ω => Real.exp (τPair * Real.rpow (YPair i a) β)) (μPair i) := by
    intro i
    simpa only [τPair, β, YPair, μPair] using hSeed.1
  have hYExpBound : ∀ i : Fin n,
      (∫ a : Ω × Ω, Real.exp (τPair * Real.rpow (YPair i a) β) ∂μPair i) ≤ MPair := by
    intro i
    simpa only [τPair, β, YPair, μPair, MPair] using hSeed.2
  have hSum := sum_real_moment_from_exp β τPair MPair hβ hβOne hτPair hMPair n
    μPair instCoordinateProbability YPair hYMeasurable hYNonneg hYExpInt hYExpBound p hp
  have hEnergyAE :
      pairedEnergy n w =ᵐ[pairedLaw n ν] coordinateSum YPair := by
    simpa only [YPair] using paired_energy_representative_ae n ν w v hwv
  have hPowerAE :
      (fun z : Fin n → Ω × Ω => Real.rpow (coordinateSum YPair z) p) =ᵐ[pairedLaw n ν]
        (fun z : Fin n → Ω × Ω => Real.rpow (pairedEnergy n w z) p) := by
    filter_upwards [hEnergyAE] with z hz
    rw [hz]
  have hSumInt :
      Integrable (fun z : Fin n → Ω × Ω => Real.rpow (coordinateSum YPair z) p)
        (pairedLaw n ν) := by
    change Integrable (fun z : Fin n → Ω × Ω => coordinateSum YPair z ^ p)
      (Measure.pi μPair)
    exact hSum.1
  have hExponent : (1 : ℝ) / (α / 2) = 2 / α := by
    field_simp [ne_of_gt hα] <;> ring
  have hSumBound :
      Real.rpow
        (∫ z : Fin n → Ω × Ω, Real.rpow (coordinateSum YPair z) p ∂pairedLaw n ν)
        (1 / p) ≤ envelopeMomentScale α τ M * ((n : ℝ) + Real.rpow p (2 / α)) := by
    change (∫ z : Fin n → Ω × Ω, coordinateSum YPair z ^ p ∂Measure.pi μPair) ^
        (1 / p) ≤ sumMomentScale β τPair MPair * ((n : ℝ) + p ^ (2 / α))
    simpa only [β, hExponent] using hSum.2
  refine ⟨hSumInt.congr hPowerAE, ?_⟩
  rw [← integral_congr_ae hPowerAE]
  exact hSumBound

theorem canonical_row_product_envelope_moment
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (r : Ω → Ω → ℝ)
    (w : Ω → ℝ)
    (α : ℝ)
    (τ : ℝ)
    (M : ℝ)
    (q : ℝ)
    (hα : 0 < α)
    (hα2 : α ≤ 2)
    (hτ : 0 < τ)
    (hM : 1 ≤ M)
    (hr : Measurable (Function.uncurry r))
    (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
    (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
    (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hExp : Integrable (fun a : Ω => Real.exp (τ * Real.rpow (w a) α)) ν)
    (hExpBound : (∫ a : Ω, Real.exp (τ * Real.rpow (w a) α) ∂ν) ≤ M)
    (hR : ∀ᵐ p : Ω × Ω ∂ν.prod ν, |r p.1 p.2| ≤ w p.1 * w p.2)
    (hq : 2 ≤ q) :
  Integrable (fun x : Fin n → Ω => Real.rpow ‖originalRows n r x‖ q) (sampleLaw n ν) ∧
  Real.rpow (∫ x : Fin n → Ω, Real.rpow ‖originalRows n r x‖ q ∂sampleLaw n ν) (1 / q) ≤ 2 * Real.sqrt q * envelopeMomentScale α τ M * ((n : ℝ) + Real.rpow q (2 / α)) := by
  have hEnergy := paired_energy_real_moment_from_exp n ν w α τ M q
    hα hα2 hτ hM (by linarith) hW hExp hExpBound
  have hRow := canonical_row_qmoment_bound n ν r w q hr hr1 hcR hcL hq hW hR hEnergy.1
  refine ⟨hRow.1, hRow.2.trans ?_⟩
  calc
    2 * Real.sqrt q *
        Real.rpow (∫ z : Fin n → Ω × Ω, Real.rpow (pairedEnergy n w z) q ∂pairedLaw n ν)
          (1 / q) ≤
      2 * Real.sqrt q *
        (envelopeMomentScale α τ M * ((n : ℝ) + Real.rpow q (2 / α))) :=
      mul_le_mul_of_nonneg_left hEnergy.2 (by positivity)
    _ = 2 * Real.sqrt q * envelopeMomentScale α τ M *
        ((n : ℝ) + Real.rpow q (2 / α)) := by ring

theorem canonical_scalar_product_envelope_moment
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (r : Ω → Ω → ℝ)
    (w : Ω → ℝ)
    (α : ℝ)
    (τ : ℝ)
    (M : ℝ)
    (q : ℝ)
    (hα : 0 < α)
    (hα2 : α ≤ 2)
    (hτ : 0 < τ)
    (hM : 1 ≤ M)
    (hr : Measurable (Function.uncurry r))
    (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
    (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
    (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hExp : Integrable (fun a : Ω => Real.exp (τ * Real.rpow (w a) α)) ν)
    (hExpBound : (∫ a : Ω, Real.exp (τ * Real.rpow (w a) α) ∂ν) ≤ M)
    (hR : ∀ᵐ p : Ω × Ω ∂ν.prod ν, |r p.1 p.2| ≤ w p.1 * w p.2)
    (hq : 2 ≤ q)
    (hsym : ∀ a b : Ω, r a b = r b a) :
  Integrable (fun x : Fin n → Ω => Real.rpow |originalUpper n r x| q) (sampleLaw n ν) ∧
  Real.rpow (∫ x : Fin n → Ω, Real.rpow |originalUpper n r x| q ∂sampleLaw n ν) (1 / q) ≤ 8 * envelopeMomentScale α τ M * q * ((n : ℝ) + Real.rpow q (2 / α)) := by
  have hEnergy := paired_energy_real_moment_from_exp n ν w α τ M q
    hα hα2 hτ hM (by linarith) hW hExp hExpBound
  have hScalar := canonical_scalar_qmoment_bound n ν r w q hr hr1 hcR hcL hsym
    hq hW hR hEnergy.1
  refine ⟨hScalar.1, hScalar.2.trans ?_⟩
  calc
    8 * q *
        Real.rpow (∫ z : Fin n → Ω × Ω, Real.rpow (pairedEnergy n w z) q ∂pairedLaw n ν)
          (1 / q) ≤
      8 * q * (envelopeMomentScale α τ M * ((n : ℝ) + Real.rpow q (2 / α))) :=
      mul_le_mul_of_nonneg_left hEnergy.2 (by linarith)
    _ = 8 * envelopeMomentScale α τ M * q *
        ((n : ℝ) + Real.rpow q (2 / α)) := by ring

theorem canonical_product_envelope_moments
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (r : Ω → Ω → ℝ)
    (w : Ω → ℝ)
    (α : ℝ)
    (τ : ℝ)
    (M : ℝ)
    (q : ℝ)
    (hα : 0 < α)
    (hα2 : α ≤ 2)
    (hτ : 0 < τ)
    (hM : 1 ≤ M)
    (hr : Measurable (Function.uncurry r))
    (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
    (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
    (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hExp : Integrable (fun a : Ω => Real.exp (τ * Real.rpow (w a) α)) ν)
    (hExpBound : (∫ a : Ω, Real.exp (τ * Real.rpow (w a) α) ∂ν) ≤ M)
    (hR : ∀ᵐ p : Ω × Ω ∂ν.prod ν, |r p.1 p.2| ≤ w p.1 * w p.2)
    (hq : 2 ≤ q)
    (hsym : ∀ a b : Ω, r a b = r b a) :
  Integrable (fun x : Fin n → Ω => Real.rpow |originalUpper n r x| q) (sampleLaw n ν) ∧
  Integrable (fun x : Fin n → Ω => Real.rpow ‖originalRows n r x‖ (2 * q)) (sampleLaw n ν) ∧
  Real.rpow (∫ x : Fin n → Ω, Real.rpow |originalUpper n r x| q ∂sampleLaw n ν) (1 / q) ≤ commonMomentScale α τ M * q * ((n : ℝ) + Real.rpow q (2 / α)) ∧
  Real.rpow (∫ x : Fin n → Ω, Real.rpow ‖originalRows n r x‖ (2 * q) ∂sampleLaw n ν) (1 / (2 * q)) ≤ commonMomentScale α τ M * Real.sqrt q * ((n : ℝ) + Real.rpow q (2 / α)) := by
  let s : ℝ := 2 / α
  have hqNonneg : 0 ≤ q := by linarith
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hC : 0 < envelopeMomentScale α τ M :=
    (envelope_scales_pos α τ M hα hτ hM).1
  have hScalar := canonical_scalar_product_envelope_moment n ν r w α τ M q
    hα hα2 hτ hM hr hr1 hcR hcL hW hExp hExpBound hR hq hsym
  have hRow := canonical_row_product_envelope_moment n ν r w α τ M (2 * q)
    hα hα2 hτ hM hr hr1 hcR hcL hW hExp hExpBound hR (by linarith)
  have hTwo : 1 ≤ Real.rpow 2 s := by
    calc
      (1 : ℝ) = Real.rpow 2 0 := by simp
      _ ≤ Real.rpow 2 s :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
  have hPower :
      Real.rpow (2 * q) s = Real.rpow 2 s * Real.rpow q s :=
    Real.mul_rpow (x := 2) (y := q) (z := s) (by norm_num) hqNonneg
  have hGrowth :
      (n : ℝ) + Real.rpow (2 * q) s ≤
        Real.rpow 2 s * ((n : ℝ) + Real.rpow q s) := by
    rw [hPower]
    have hExtra := mul_nonneg (sub_nonneg.mpr hTwo) (Nat.cast_nonneg (α := ℝ) n)
    nlinarith
  have hSqrt :
      Real.sqrt (2 * q) = Real.sqrt 2 * Real.sqrt q := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by positivity)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr
    calc
      2 * q = (Real.sqrt 2) ^ 2 * (Real.sqrt q) ^ 2 := by
        rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt hqNonneg]
      _ = (Real.sqrt 2 * Real.sqrt q) * (Real.sqrt 2 * Real.sqrt q) := by ring
  have hScalarCoefficient :
      8 * envelopeMomentScale α τ M ≤ commonMomentScale α τ M :=
    le_max_left _ _
  have hRowCoefficient :
      2 * Real.sqrt 2 * Real.rpow 2 s * envelopeMomentScale α τ M ≤
        commonMomentScale α τ M := by
    exact le_max_right _ _
  refine ⟨hScalar.1, hRow.1, hScalar.2.trans ?_, hRow.2.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hScalarCoefficient hqNonneg)
      (add_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg hqNonneg _))
  · change 2 * Real.sqrt (2 * q) * envelopeMomentScale α τ M *
      ((n : ℝ) + Real.rpow (2 * q) s) ≤
        commonMomentScale α τ M * Real.sqrt q * ((n : ℝ) + Real.rpow q s)
    calc
      2 * Real.sqrt (2 * q) * envelopeMomentScale α τ M *
          ((n : ℝ) + Real.rpow (2 * q) s) ≤
        2 * Real.sqrt (2 * q) * envelopeMomentScale α τ M *
          (Real.rpow 2 s * ((n : ℝ) + Real.rpow q s)) :=
        mul_le_mul_of_nonneg_left hGrowth (by positivity)
      _ = (2 * Real.sqrt 2 * Real.rpow 2 s * envelopeMomentScale α τ M) *
          Real.sqrt q * ((n : ℝ) + Real.rpow q s) := by rw [hSqrt]; ring
      _ ≤ commonMomentScale α τ M * Real.sqrt q *
          ((n : ℝ) + Real.rpow q s) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hRowCoefficient (Real.sqrt_nonneg _))
          (add_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg hqNonneg _))

private theorem strict_moment_markov
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω)
    [hμ : IsFiniteMeasure μ]
    (X : Ω → ℝ)
    (p : ℝ)
    (K : ℝ)
    (hp : 0 < p)
    (hK : 0 < K)
    (hX : ∀ a : Ω, 0 ≤ X a)
    (hXp : Integrable (fun a : Ω => Real.rpow (X a) p) μ)
    (hMoment : Real.rpow (∫ a : Ω, Real.rpow (X a) p ∂μ) (1 / p) ≤ K) :
  μ.real {a : Ω | Real.exp 1 * K < X a} ≤ Real.exp (-p) := by
  let powerX : Ω → ℝ := fun a : Ω => Real.rpow (X a) p
  let momentIntegral : ℝ := ∫ a : Ω, Real.rpow (X a) p ∂μ
  let epsilon : ℝ := Real.rpow (Real.exp 1 * K) p
  let strictEvent : Set Ω := {a : Ω | Real.exp 1 * K < X a}
  let closedPowerEvent : Set Ω := {a : Ω | epsilon ≤ Real.rpow (X a) p}
  have hIntegralNonneg : 0 ≤ momentIntegral := by
    apply integral_nonneg_of_ae
    exact ae_of_all μ (fun a => Real.rpow_nonneg (hX a) p)
  have hIntegralBound : momentIntegral ≤ Real.rpow K p := by
    have hPower := Real.rpow_le_rpow
      (Real.rpow_nonneg hIntegralNonneg (1 / p)) hMoment (le_of_lt hp)
    have hInverse :
        Real.rpow (Real.rpow momentIntegral (1 / p)) p = momentIntegral := by
      simpa only [Real.rpow_eq_pow, one_div] using
        (Real.rpow_inv_rpow hIntegralNonneg (ne_of_gt hp))
    change Real.rpow (Real.rpow momentIntegral (1 / p)) p ≤ Real.rpow K p at hPower
    simpa only [hInverse] using hPower
  have hEpsilon : 0 < epsilon :=
    Real.rpow_pos_of_pos (mul_pos (Real.exp_pos 1) hK) p
  have hSubset : strictEvent ⊆ closedPowerEvent := by
    intro a ha
    exact Real.rpow_le_rpow (le_of_lt (mul_pos (Real.exp_pos 1) hK))
      (le_of_lt ha) (le_of_lt hp)
  have hMarkov : epsilon * μ.real closedPowerEvent ≤ momentIntegral := by
    exact mul_meas_ge_le_integral_of_nonneg
      (ae_of_all μ (fun a => Real.rpow_nonneg (hX a) p)) hXp epsilon
  have hScaledEvent : epsilon * μ.real strictEvent ≤ momentIntegral :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hSubset) (le_of_lt hEpsilon)).trans hMarkov
  have hCancel : epsilon * Real.exp (-p) = Real.rpow K p := by
    dsimp [epsilon]
    rw [Real.mul_rpow (le_of_lt (Real.exp_pos 1)) (le_of_lt hK), Real.exp_one_rpow]
    calc
      (Real.exp p * Real.rpow K p) * Real.exp (-p) =
          (Real.exp p * Real.exp (-p)) * Real.rpow K p := by ring
      _ = Real.rpow K p := by rw [← Real.exp_add]; simp
  have hScaledBound : epsilon * μ.real strictEvent ≤ epsilon * Real.exp (-p) := by
    calc
      epsilon * μ.real strictEvent ≤ momentIntegral := hScaledEvent
      _ ≤ Real.rpow K p := hIntegralBound
      _ = epsilon * Real.exp (-p) := hCancel.symm
  by_contra hNot
  have hPositiveGap : 0 < epsilon * (μ.real strictEvent - Real.exp (-p)) :=
    mul_pos hEpsilon (sub_pos.mpr (lt_of_not_ge hNot))
  nlinarith only [hScaledBound, hPositiveGap]

private theorem tail_window_power_bounds
    (n : ℕ)
    (α : ℝ)
    (q : ℝ)
    (hα : 0 < α)
    (hq : 2 ≤ q)
    (hWindow : 2 * q ≤ Real.rpow (n : ℝ) (α / 2)) :
  0 < n ∧ Real.rpow q (2 / α) ≤ (n : ℝ) ∧ Real.rpow (2 * q) (2 / α) ≤ (n : ℝ) := by
  have hqNonneg : 0 ≤ q := by linarith
  have hn : 0 < n := by
    by_contra hn
    have hnZero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hβ : (α / 2 : ℝ) ≠ 0 := by linarith
    have hZero : Real.rpow (0 : ℝ) (α / 2) = 0 := Real.zero_rpow hβ
    simp only [Nat.cast_zero] at hWindow
    rw [hZero] at hWindow
    linarith
  have hPairPower :
      Real.rpow (2 * q) (2 / α) ≤
        Real.rpow (Real.rpow (n : ℝ) (α / 2)) (2 / α) :=
    Real.rpow_le_rpow (by linarith) hWindow (by positivity)
  have hInverse :
      Real.rpow (Real.rpow (n : ℝ) (α / 2)) (2 / α) = (n : ℝ) := by
    change ((n : ℝ) ^ (α / 2)) ^ (2 / α) = (n : ℝ)
    rw [← Real.rpow_mul (Nat.cast_nonneg n)]
    have hExponent : (α / 2) * (2 / α) = (1 : ℝ) := by
      field_simp [ne_of_gt hα] <;> ring
    rw [hExponent, Real.rpow_one]
  have hPair : Real.rpow (2 * q) (2 / α) ≤ (n : ℝ) := by
    simpa only [hInverse] using hPairPower
  have hSingle : Real.rpow q (2 / α) ≤ Real.rpow (2 * q) (2 / α) :=
    Real.rpow_le_rpow hqNonneg (by linarith) (by positivity)
  exact ⟨hn, hSingle.trans hPair, hPair⟩

theorem canonical_scalar_product_envelope_tail
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (r : Ω → Ω → ℝ)
    (w : Ω → ℝ)
    (α : ℝ)
    (τ : ℝ)
    (M : ℝ)
    (q : ℝ)
    (hα : 0 < α)
    (hα2 : α ≤ 2)
    (hτ : 0 < τ)
    (hM : 1 ≤ M)
    (hr : Measurable (Function.uncurry r))
    (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
    (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
    (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hExp : Integrable (fun a : Ω => Real.exp (τ * Real.rpow (w a) α)) ν)
    (hExpBound : (∫ a : Ω, Real.exp (τ * Real.rpow (w a) α) ∂ν) ≤ M)
    (hR : ∀ᵐ p : Ω × Ω ∂ν.prod ν, |r p.1 p.2| ≤ w p.1 * w p.2)
    (hq : 2 ≤ q)
    (hsym : ∀ a b : Ω, r a b = r b a)
    (hWindow : 2 * q ≤ Real.rpow (n : ℝ) (α / 2)) :
  (sampleLaw n ν).real {x : Fin n → Ω | scalarTailScale α τ M * (n : ℝ) * q < |originalUpper n r x|} ≤ Real.exp (-q) := by
  letI instSampleProbability : IsProbabilityMeasure (sampleLaw n ν) := inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => ν)))
  letI instSampleFinite : IsFiniteMeasure (sampleLaw n ν) := inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Fin n => ν)))
  let C : ℝ := envelopeMomentScale α τ M
  let scalarAbs : (Fin n → Ω) → ℝ := fun x : Fin n → Ω => |originalUpper n r x|
  let KScalar : ℝ := 16 * C * (n : ℝ) * q
  have hC : 0 < C := (envelope_scales_pos α τ M hα hτ hM).1
  have hWindowBounds := tail_window_power_bounds n α q hα hq hWindow
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hWindowBounds.1
  have hqPos : 0 < q := by linarith
  have hMoment := canonical_scalar_product_envelope_moment n ν r w α τ M q
    hα hα2 hτ hM hr hr1 hcR hcL hW hExp hExpBound hR hq hsym
  have hK : 0 < KScalar := by dsimp [KScalar]; positivity
  have hSmall :
      Real.rpow (∫ x : Fin n → Ω, Real.rpow (scalarAbs x) q ∂sampleLaw n ν)
        (1 / q) ≤ KScalar := by
    calc
      Real.rpow (∫ x : Fin n → Ω, Real.rpow (scalarAbs x) q ∂sampleLaw n ν)
          (1 / q) ≤ 8 * C * q * ((n : ℝ) + Real.rpow q (2 / α)) := hMoment.2
      _ ≤ 8 * C * q * ((n : ℝ) + (n : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (by linarith only [hWindowBounds.2.1]) (by positivity)
      _ = KScalar := by dsimp [KScalar]; ring
  have hTail := strict_moment_markov (sampleLaw n ν) scalarAbs q KScalar hqPos hK
    (fun x => abs_nonneg _) hMoment.1 hSmall
  simpa only [scalarAbs, KScalar, C, scalarTailScale, mul_assoc, mul_left_comm, mul_comm]
    using hTail

theorem canonical_row_product_envelope_tail
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (r : Ω → Ω → ℝ)
    (w : Ω → ℝ)
    (α : ℝ)
    (τ : ℝ)
    (M : ℝ)
    (q : ℝ)
    (hα : 0 < α)
    (hα2 : α ≤ 2)
    (hτ : 0 < τ)
    (hM : 1 ≤ M)
    (hr : Measurable (Function.uncurry r))
    (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
    (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
    (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hExp : Integrable (fun a : Ω => Real.exp (τ * Real.rpow (w a) α)) ν)
    (hExpBound : (∫ a : Ω, Real.exp (τ * Real.rpow (w a) α) ∂ν) ≤ M)
    (hR : ∀ᵐ p : Ω × Ω ∂ν.prod ν, |r p.1 p.2| ≤ w p.1 * w p.2)
    (hq : 2 ≤ q)
    (hWindow : 2 * q ≤ Real.rpow (n : ℝ) (α / 2)) :
  (sampleLaw n ν).real {x : Fin n → Ω | rowTailScale α τ M * (n : ℝ) ^ 2 * q < ‖originalRows n r x‖ ^ 2} ≤ Real.exp (-(2 * q)) := by
  letI instSampleProbability : IsProbabilityMeasure (sampleLaw n ν) := inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => ν)))
  letI instSampleFinite : IsFiniteMeasure (sampleLaw n ν) := inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Fin n => ν)))
  let C : ℝ := envelopeMomentScale α τ M
  let rowNorm : (Fin n → Ω) → ℝ := fun x : Fin n → Ω => ‖originalRows n r x‖
  let KRow : ℝ := 4 * Real.sqrt (2 * q) * C * (n : ℝ)
  have hC : 0 < C := (envelope_scales_pos α τ M hα hτ hM).1
  have hWindowBounds := tail_window_power_bounds n α q hα hq hWindow
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hWindowBounds.1
  have hqPos : 0 < q := by linarith
  have hSqrtPos : 0 < Real.sqrt (2 * q) := Real.sqrt_pos_of_pos (by linarith)
  have hMoment := canonical_row_product_envelope_moment n ν r w α τ M (2 * q)
    hα hα2 hτ hM hr hr1 hcR hcL hW hExp hExpBound hR (by linarith)
  have hK : 0 < KRow := by dsimp [KRow]; positivity
  have hSmall :
      Real.rpow (∫ x : Fin n → Ω, Real.rpow (rowNorm x) (2 * q) ∂sampleLaw n ν)
        (1 / (2 * q)) ≤ KRow := by
    calc
      Real.rpow (∫ x : Fin n → Ω, Real.rpow (rowNorm x) (2 * q) ∂sampleLaw n ν)
          (1 / (2 * q)) ≤
        2 * Real.sqrt (2 * q) * C * ((n : ℝ) + Real.rpow (2 * q) (2 / α)) := hMoment.2
      _ ≤ 2 * Real.sqrt (2 * q) * C * ((n : ℝ) + (n : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (by linarith only [hWindowBounds.2.2]) (by positivity)
      _ = KRow := by dsimp [KRow]; ring
  have hTail := strict_moment_markov (sampleLaw n ν) rowNorm (2 * q) KRow
    (by linarith) hK (fun x => norm_nonneg _) hMoment.1 hSmall
  have hSquare :
      (Real.exp 1 * KRow) ^ 2 = rowTailScale α τ M * (n : ℝ) ^ 2 * q := by
    dsimp [KRow, C, rowTailScale]
    rw [mul_pow, mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt (show 0 ≤ 2 * q by linarith)]
    ring
  have hSubset :
      {x : Fin n → Ω | rowTailScale α τ M * (n : ℝ) ^ 2 * q < (rowNorm x) ^ 2} ⊆
        {x : Fin n → Ω | Real.exp 1 * KRow < rowNorm x} := by
    intro x hx
    by_contra hNot
    have hLe : rowNorm x ≤ Real.exp 1 * KRow := le_of_not_gt hNot
    have hNorm : 0 ≤ rowNorm x := norm_nonneg _
    have hExpK : 0 ≤ Real.exp 1 * KRow := le_of_lt (mul_pos (Real.exp_pos 1) hK)
    have hDiff := mul_nonneg (sub_nonneg.mpr hLe) (add_nonneg hExpK hNorm)
    have hLeSq : (rowNorm x) ^ 2 ≤ (Real.exp 1 * KRow) ^ 2 := by nlinarith
    rw [hSquare] at hLeSq
    exact (not_lt_of_ge hLeSq) hx
  exact (measureReal_mono hSubset).trans hTail

theorem canonical_product_envelope_tails
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (r : Ω → Ω → ℝ)
    (w : Ω → ℝ)
    (α : ℝ)
    (τ : ℝ)
    (M : ℝ)
    (q : ℝ)
    (hα : 0 < α)
    (hα2 : α ≤ 2)
    (hτ : 0 < τ)
    (hM : 1 ≤ M)
    (hr : Measurable (Function.uncurry r))
    (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
    (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
    (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hExp : Integrable (fun a : Ω => Real.exp (τ * Real.rpow (w a) α)) ν)
    (hExpBound : (∫ a : Ω, Real.exp (τ * Real.rpow (w a) α) ∂ν) ≤ M)
    (hR : ∀ᵐ p : Ω × Ω ∂ν.prod ν, |r p.1 p.2| ≤ w p.1 * w p.2)
    (hq : 2 ≤ q)
    (hsym : ∀ a b : Ω, r a b = r b a)
    (hWindow : 2 * q ≤ Real.rpow (n : ℝ) (α / 2)) :
  (sampleLaw n ν).real {x : Fin n → Ω | tailScale α τ M * (n : ℝ) * q < |originalUpper n r x|} ≤ Real.exp (-q) ∧
  (sampleLaw n ν).real {x : Fin n → Ω | tailScale α τ M * (n : ℝ) ^ 2 * q < ‖originalRows n r x‖ ^ 2} ≤ Real.exp (-(2 * q)) ∧
  (sampleLaw n ν).real {x : Fin n → Ω | tailScale α τ M * (n : ℝ) * q < |originalUpper n r x|} + (sampleLaw n ν).real {x : Fin n → Ω | tailScale α τ M * (n : ℝ) ^ 2 * q < ‖originalRows n r x‖ ^ 2} ≤ 2 * Real.exp (-q) := by
  letI instSampleProbability : IsProbabilityMeasure (sampleLaw n ν) := inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => ν)))
  letI instSampleFinite : IsFiniteMeasure (sampleLaw n ν) := inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Fin n => ν)))
  let FEvent : Set (Fin n → Ω) := {x : Fin n → Ω | tailScale α τ M * (n : ℝ) * q < |originalUpper n r x|}
  let LEvent : Set (Fin n → Ω) := {x : Fin n → Ω | tailScale α τ M * (n : ℝ) ^ 2 * q < ‖originalRows n r x‖ ^ 2}
  have hqNonneg : 0 ≤ q := by linarith
  have hScalar := canonical_scalar_product_envelope_tail n ν r w α τ M q
    hα hα2 hτ hM hr hr1 hcR hcL hW hExp hExpBound hR hq hsym hWindow
  have hRow := canonical_row_product_envelope_tail n ν r w α τ M q
    hα hα2 hτ hM hr hr1 hcR hcL hW hExp hExpBound hR hq hWindow
  have hScalarScale : scalarTailScale α τ M ≤ tailScale α τ M :=
    le_max_left _ _
  have hRowScale : rowTailScale α τ M ≤ tailScale α τ M :=
    le_max_right _ _
  have hSubsetF : FEvent ⊆
      {x : Fin n → Ω | scalarTailScale α τ M * (n : ℝ) * q < |originalUpper n r x|} := by
    intro x hx
    change tailScale α τ M * (n : ℝ) * q < |originalUpper n r x| at hx
    change scalarTailScale α τ M * (n : ℝ) * q < |originalUpper n r x|
    apply lt_of_le_of_lt _ hx
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hScalarScale (Nat.cast_nonneg n)) hqNonneg
  have hSubsetL : LEvent ⊆
      {x : Fin n → Ω | rowTailScale α τ M * (n : ℝ) ^ 2 * q < ‖originalRows n r x‖ ^ 2} := by
    intro x hx
    change tailScale α τ M * (n : ℝ) ^ 2 * q < ‖originalRows n r x‖ ^ 2 at hx
    change rowTailScale α τ M * (n : ℝ) ^ 2 * q < ‖originalRows n r x‖ ^ 2
    apply lt_of_le_of_lt _ hx
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hRowScale (sq_nonneg (n : ℝ))) hqNonneg
  have hF : (sampleLaw n ν).real FEvent ≤ Real.exp (-q) :=
    (measureReal_mono hSubsetF).trans hScalar
  have hL : (sampleLaw n ν).real LEvent ≤ Real.exp (-(2 * q)) :=
    (measureReal_mono hSubsetL).trans hRow
  refine ⟨hF, hL, ?_⟩
  have hExp : Real.exp (-(2 * q)) ≤ Real.exp (-q) :=
    Real.exp_le_exp.mpr (by linarith)
  have hSum := add_le_add hF hL
  nlinarith

theorem canonical_product_envelope_two_thirds_tails
    (n : ℕ)
    {Ω : Type u}
    [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω)
    [hν : IsProbabilityMeasure ν]
    (r : Ω → Ω → ℝ)
    (w : Ω → ℝ)
    (τ : ℝ)
    (M : ℝ)
    (q : ℝ)
    (hτ : 0 < τ)
    (hM : 1 ≤ M)
    (hr : Measurable (Function.uncurry r))
    (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
    (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
    (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hR : ∀ᵐ p : Ω × Ω ∂ν.prod ν, |r p.1 p.2| ≤ w p.1 * w p.2)
    (hq : 2 ≤ q)
    (hExp : Integrable (fun a : Ω => Real.exp (τ * Real.rpow (w a) (2 / 3 : ℝ))) ν)
    (hExpBound : (∫ a : Ω, Real.exp (τ * Real.rpow (w a) (2 / 3 : ℝ)) ∂ν) ≤ M)
    (hsym : ∀ a b : Ω, r a b = r b a)
    (hWindow : q ≤ Real.rpow (n : ℝ) (1 / 3 : ℝ) / 2) :
  (sampleLaw n ν).real {x : Fin n → Ω | tailScale (2 / 3 : ℝ) τ M * (n : ℝ) * q < |originalUpper n r x|} ≤ Real.exp (-q) ∧
  (sampleLaw n ν).real {x : Fin n → Ω | tailScale (2 / 3 : ℝ) τ M * (n : ℝ) ^ 2 * q < ‖originalRows n r x‖ ^ 2} ≤ Real.exp (-(2 * q)) ∧
  (sampleLaw n ν).real {x : Fin n → Ω | tailScale (2 / 3 : ℝ) τ M * (n : ℝ) * q < |originalUpper n r x|} + (sampleLaw n ν).real {x : Fin n → Ω | tailScale (2 / 3 : ℝ) τ M * (n : ℝ) ^ 2 * q < ‖originalRows n r x‖ ^ 2} ≤ 2 * Real.exp (-q) := by
  have hWindowThird :
      2 * q ≤ Real.rpow (n : ℝ) ((2 / 3 : ℝ) / 2) := by
    have hExponent : (2 / 3 : ℝ) / 2 = (1 / 3 : ℝ) := by norm_num
    rw [hExponent]
    linarith
  exact canonical_product_envelope_tails n ν r w (2 / 3 : ℝ) τ M q
    (by norm_num) (by norm_num) hτ hM hr hr1 hcR hcL hW hExp hExpBound
    hR hq hsym hWindowThird

end
end Shao.OQ6.CanonicalProductEnvelopeTails
