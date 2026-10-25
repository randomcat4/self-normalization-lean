import Shao.OQ6.StretchedExponentialSumMoments
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

set_option autoImplicit false
universe u
namespace Shao.OQ6.BoundedMeanSumMoments
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ6.StretchedExponentialSumMoments (coordinateSum)

-- D01: exact frozen declaration; source-only proof.
private theorem bounded_nat_power_integrable
    {Ω : Type u} [instΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [instFinite : IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C)
    (hfBounds : ∀ᵐ ω ∂μ, 0 ≤ f ω ∧ f ω ≤ C)
    (k : ℕ) :
    Integrable (fun ω : Ω => (f ω) ^ k) μ := by
  refine (integrable_const (C ^ k)).mono' (hf.pow_const k).aestronglyMeasurable ?_
  filter_upwards [hfBounds] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hω.1 k)]
  have hLower : 0 ≤ f ω := hω.1
  have hUpper : f ω ≤ C := hω.2
  gcongr

-- D02: exact frozen declaration; source-only proof.
private theorem coordinate_sum_measurable_bounds
    {Ω : Type u} [instΩ : MeasurableSpace Ω]
    (n : ℕ) (μ : Fin n → Measure Ω)
    (hμ : ∀ i : Fin n, IsProbabilityMeasure (μ i))
    (Y : Fin n → Ω → ℝ)
    (hY : ∀ i : Fin n, Measurable (Y i))
    (B : ℝ) (hB : 0 ≤ B)
    (hYnonneg : ∀ i : Fin n, ∀ᵐ ω ∂(μ i), 0 ≤ Y i ω)
    (hYle : ∀ i : Fin n, ∀ᵐ ω ∂(μ i), Y i ω ≤ B) :
    Measurable (coordinateSum Y) ∧
      (∀ᵐ x : Fin n → Ω ∂(Measure.pi μ),
        0 ≤ coordinateSum Y x ∧ coordinateSum Y x ≤ (n : ℝ) * B) := by
  -- frozen D02/body/instCoordinateProbability
  letI instCoordinateProbability : ∀ i : Fin n, IsProbabilityMeasure (μ i) := hμ
  -- frozen D02/body/instCoordinateSigmaFinite
  letI instCoordinateSigmaFinite : ∀ i : Fin n, SigmaFinite (μ i) := fun i : Fin n => inferInstance
  -- frozen D02/body/instProductProbability
  letI instProductProbability : IsProbabilityMeasure (Measure.pi μ) := inferInstance
  constructor
  · exact Finset.measurable_sum Finset.univ
      (fun i _ => (hY i).comp (measurable_pi_apply i))
  · have hCoordinates : ∀ᵐ x : Fin n → Ω ∂(Measure.pi μ),
        ∀ i : Fin n, 0 ≤ Y i (x i) ∧ Y i (x i) ≤ B := by
      rw [ae_all_iff]
      intro i
      exact (Measure.tendsto_eval_ae_ae (μ := μ) (i := i)).eventually
        ((hYnonneg i).and (hYle i))
    filter_upwards [hCoordinates] with x hx
    constructor
    · exact Finset.sum_nonneg (fun i _ => (hx i).1)
    · calc
        coordinateSum Y x ≤ ∑ _i : Fin n, B :=
          Finset.sum_le_sum (fun i _ => (hx i).2)
        _ = (n : ℝ) * B := by simp

-- D03: exact frozen declaration; source-only proof.
private theorem coordinate_sum_split
    {Ω : Type u} (n : ℕ) (Y : Fin (n + 1) → Ω → ℝ)
    (i : Fin (n + 1)) (x : Fin (n + 1) → Ω) :
    coordinateSum Y x = Y i (x i) +
      coordinateSum (fun j : Fin n => Y (i.succAbove j))
        (fun j : Fin n => x (i.succAbove j)) := by
  simpa only [coordinateSum] using
    (Fin.sum_univ_succAbove (fun j : Fin (n + 1) => Y j (x j)) i)

-- D04: exact frozen declaration; source-only proof.
private theorem shifted_nat_moment_le
    {Ω : Type u} [instΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [instProbability : IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f)
    (hfnn : ∀ᵐ ω ∂μ, 0 ≤ f ω)
    (a B c : ℝ) (ha : 0 ≤ a) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (k : ℕ)
    (hInt : ∀ j : ℕ, j ≤ k → Integrable (fun ω : Ω => (f ω) ^ j) μ)
    (hMoment : ∀ j : ℕ, j ≤ k →
      (∫ ω : Ω, (f ω) ^ j ∂μ) ≤ (a + (j : ℝ) * B) ^ j) :
    Integrable (fun ω : Ω => (f ω + c) ^ k) μ ∧
      (∫ ω : Ω, (f ω + c) ^ k ∂μ) ≤ (a + (k : ℝ) * B + c) ^ k := by
  -- frozen D04/body/momentIndexSet
  let momentIndexSet : Finset ℕ := Finset.range (k + 1)
  -- frozen D04/body/binomialCoefficient
  let binomialCoefficient : ℕ → ℝ := fun j : ℕ => (Nat.choose k j : ℝ) * c ^ (k - j)
  -- frozen D04/body/binomialTerm
  let binomialTerm : ℕ → Ω → ℝ := fun (j : ℕ) (ω : Ω) => binomialCoefficient j * (f ω) ^ j
  -- frozen D04/body/commonBase
  let commonBase : ℝ := a + (k : ℝ) * B
  -- frozen D04/body/upperTerm
  let upperTerm : ℕ → ℝ := fun j : ℕ => binomialCoefficient j * commonBase ^ j
  have hCoefficientNonneg : ∀ j : ℕ, 0 ≤ binomialCoefficient j := by
    intro j
    dsimp only [binomialCoefficient]
    positivity
  have hTermInt : ∀ j : ℕ, j ∈ momentIndexSet → Integrable (binomialTerm j) μ := by
    intro j hj
    have hjle : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    exact (hInt j hjle).const_mul (binomialCoefficient j)
  have hExpansion : ∀ ω : Ω,
      (f ω + c) ^ k = ∑ j ∈ momentIndexSet, binomialTerm j ω := by
    intro ω
    rw [_root_.add_pow]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [binomialTerm, binomialCoefficient]
    ring
  have hFiniteInt : Integrable (fun ω : Ω => ∑ j ∈ momentIndexSet, binomialTerm j ω) μ :=
    integrable_finsetSum momentIndexSet hTermInt
  have hShiftedInt : Integrable (fun ω : Ω => (f ω + c) ^ k) μ :=
    hFiniteInt.congr (Filter.Eventually.of_forall (fun ω => (hExpansion ω).symm))
  have hCommonNonneg : 0 ≤ commonBase := by dsimp only [commonBase]; positivity
  have hTermBound : ∀ j : ℕ, j ∈ momentIndexSet →
      (∫ ω : Ω, binomialTerm j ω ∂μ) ≤ upperTerm j := by
    intro j hj
    have hjle : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hBaseNonneg : 0 ≤ a + (j : ℝ) * B := by positivity
    have hBaseLe : a + (j : ℝ) * B ≤ commonBase := by
      dsimp only [commonBase]
      have hCast : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjle
      nlinarith [mul_le_mul_of_nonneg_right hCast hB]
    have hPowerLe : (a + (j : ℝ) * B) ^ j ≤ commonBase ^ j := by gcongr
    change (∫ ω : Ω, binomialCoefficient j * (f ω) ^ j ∂μ) ≤
      binomialCoefficient j * commonBase ^ j
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left (hMoment j hjle) (hCoefficientNonneg j)).trans
      (mul_le_mul_of_nonneg_left hPowerLe (hCoefficientNonneg j))
  have hUpperExpansion : (∑ j ∈ momentIndexSet, upperTerm j) = (commonBase + c) ^ k := by
    conv_rhs => rw [_root_.add_pow]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [upperTerm, binomialCoefficient]
    ring
  refine ⟨hShiftedInt, ?_⟩
  calc
    (∫ ω : Ω, (f ω + c) ^ k ∂μ) =
        ∑ j ∈ momentIndexSet, ∫ ω : Ω, binomialTerm j ω ∂μ := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hExpansion),
        integral_finsetSum momentIndexSet hTermInt]
    _ ≤ ∑ j ∈ momentIndexSet, upperTerm j := Finset.sum_le_sum hTermBound
    _ = (a + (k : ℝ) * B + c) ^ k := hUpperExpansion

-- D05: exact frozen declaration; source-only proof.
private theorem coordinate_delete_integral_factor
    {Ω : Type u} [instΩ : MeasurableSpace Ω]
    (n : ℕ) (μ : Fin (n + 1) → Measure Ω)
    (hμ : ∀ i : Fin (n + 1), IsProbabilityMeasure (μ i))
    (Y : Fin (n + 1) → Ω → ℝ)
    (hY : ∀ i : Fin (n + 1), Measurable (Y i))
    (B : ℝ) (hB : 0 ≤ B)
    (hYnonneg : ∀ i : Fin (n + 1), ∀ᵐ ω ∂(μ i), 0 ≤ Y i ω)
    (hYle : ∀ i : Fin (n + 1), ∀ᵐ ω ∂(μ i), Y i ω ≤ B)
    (i : Fin (n + 1)) (k : ℕ) :
    Integrable
      (fun x : Fin (n + 1) → Ω =>
        Y i (x i) * (coordinateSum Y x - Y i (x i) + B) ^ k)
      (Measure.pi μ) ∧
      (∫ x : Fin (n + 1) → Ω,
        Y i (x i) * (coordinateSum Y x - Y i (x i) + B) ^ k ∂(Measure.pi μ)) =
        (∫ ω : Ω, Y i ω ∂(μ i)) *
          (∫ z : Fin n → Ω,
            (coordinateSum (fun j : Fin n => Y (i.succAbove j)) z + B) ^ k
              ∂(Measure.pi (fun j : Fin n => μ (i.succAbove j)))) := by
  -- frozen D05/body/instCoordinateProbability
  letI instCoordinateProbability : ∀ i : Fin (n + 1), IsProbabilityMeasure (μ i) := hμ
  -- frozen D05/body/instCoordinateSigmaFinite
  letI instCoordinateSigmaFinite : ∀ i : Fin (n + 1), SigmaFinite (μ i) := fun i : Fin (n + 1) => inferInstance
  -- frozen D05/body/deletedMeasure
  let deletedMeasure : Fin n → Measure Ω := fun j : Fin n => μ (i.succAbove j)
  -- frozen D05/body/deletedSeed
  let deletedSeed : Fin n → Ω → ℝ := fun j : Fin n => Y (i.succAbove j)
  -- frozen D05/body/instDeletedProbability
  letI instDeletedProbability : ∀ j : Fin n, IsProbabilityMeasure (deletedMeasure j) := fun j : Fin n => hμ (i.succAbove j)
  -- frozen D05/body/deletedSum
  let deletedSum : (Fin n → Ω) → ℝ := coordinateSum deletedSeed
  -- frozen D05/body/shiftedPower
  let shiftedPower : (Fin n → Ω) → ℝ := fun z : Fin n → Ω => (deletedSum z + B) ^ k
  -- frozen D05/body/shiftedPowerBound
  let shiftedPowerBound : ℝ := ((n : ℝ) * B + B) ^ k
  -- frozen D05/body/splitEquiv
  let splitEquiv : (Fin (n + 1) → Ω) ≃ᵐ Ω × (Fin n → Ω) := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) i
  -- frozen D05/body/productKernel
  let productKernel : Ω × (Fin n → Ω) → ℝ := fun z : Ω × (Fin n → Ω) => Y i z.1 * shiftedPower z.2
  -- frozen D05/body/originalKernel
  let originalKernel : (Fin (n + 1) → Ω) → ℝ := fun x : Fin (n + 1) → Ω => Y i (x i) * (coordinateSum Y x - Y i (x i) + B) ^ k
  have hDeleted : Measurable deletedSum ∧
      (∀ᵐ z : Fin n → Ω ∂(Measure.pi deletedMeasure),
        0 ≤ deletedSum z ∧ deletedSum z ≤ (n : ℝ) * B) :=
    coordinate_sum_measurable_bounds n deletedMeasure
      (fun j => hμ (i.succAbove j)) deletedSeed
      (fun j => hY (i.succAbove j)) B hB
      (fun j => hYnonneg (i.succAbove j)) (fun j => hYle (i.succAbove j))
  have hScalarInt : Integrable (Y i) (μ i) := by
    simpa only [pow_one] using bounded_nat_power_integrable (μ i) (Y i) (hY i) B hB
      ((hYnonneg i).and (hYle i)) 1
  have hShiftedInt : Integrable shiftedPower (Measure.pi deletedMeasure) := by
    refine (integrable_const shiftedPowerBound).mono' ?_ ?_
    · exact ((hDeleted.1.add measurable_const).pow_const k).aestronglyMeasurable
    · filter_upwards [hDeleted.2] with z hz
      dsimp only [shiftedPower, shiftedPowerBound]
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (add_nonneg hz.1 hB) k)]
      have hLower : 0 ≤ deletedSum z + B := add_nonneg hz.1 hB
      have hUpper : deletedSum z + B ≤ (n : ℝ) * B + B := by
        linarith [hz.2]
      gcongr
  have hProductInt : Integrable productKernel ((μ i).prod (Measure.pi deletedMeasure)) :=
    hScalarInt.mul_prod hShiftedInt
  have hSplitMP : MeasurePreserving splitEquiv (Measure.pi μ)
      ((μ i).prod (Measure.pi deletedMeasure)) := by
    exact measurePreserving_piFinSuccAbove μ i
  have hKernelEq : productKernel ∘ splitEquiv = originalKernel := by
    funext x
    change Y i (x i) *
        (coordinateSum (fun j : Fin n => Y (i.succAbove j))
          (fun j : Fin n => x (i.succAbove j)) + B) ^ k =
      Y i (x i) * (coordinateSum Y x - Y i (x i) + B) ^ k
    rw [coordinate_sum_split n Y i x]
    congr 2 <;> ring
  have hOriginalInt : Integrable originalKernel (Measure.pi μ) := by
    rw [← hKernelEq]
    exact hSplitMP.integrable_comp_of_integrable hProductInt
  have hFactor : (∫ x : Fin (n + 1) → Ω, originalKernel x ∂(Measure.pi μ)) =
      (∫ ω : Ω, Y i ω ∂(μ i)) *
        (∫ z : Fin n → Ω, shiftedPower z ∂(Measure.pi deletedMeasure)) := by
    calc
      (∫ x : Fin (n + 1) → Ω, originalKernel x ∂(Measure.pi μ)) =
          ∫ x : Fin (n + 1) → Ω, productKernel (splitEquiv x) ∂(Measure.pi μ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => congrFun hKernelEq.symm x)
      _ = ∫ z : Ω × (Fin n → Ω), productKernel z
          ∂((μ i).prod (Measure.pi deletedMeasure)) := hSplitMP.integral_comp' productKernel
      _ = _ := integral_prod_mul (Y i) shiftedPower
  exact ⟨hOriginalInt, hFactor⟩

-- D06: exact frozen declaration; source-only proof.
private theorem nonneg_real_moment_mono
    {Ω : Type u} [instΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [instProbability : IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f)
    (hfnn : ∀ᵐ ω ∂μ, 0 ≤ f ω)
    (p r : ℝ) (hp : 0 < p) (hpr : p ≤ r)
    (hrInt : Integrable (fun ω : Ω => (f ω) ^ r) μ) :
    Integrable (fun ω : Ω => (f ω) ^ p) μ ∧
      (∫ ω : Ω, (f ω) ^ p ∂μ) ^ (1 / p) ≤
        (∫ ω : Ω, (f ω) ^ r ∂μ) ^ (1 / r) := by
  have hr : 0 < r := hp.trans_le hpr
  have hp0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hr0 : ENNReal.ofReal r ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hr)
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hrTop : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
  have hrNorm : Integrable (fun ω : Ω => ‖f ω‖ ^ r) μ := by
    refine hrInt.congr ?_
    filter_upwards [hfnn] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω]
  have hMemr : MemLp f (ENNReal.ofReal r) μ := by
    apply (integrable_norm_rpow_iff hf.aestronglyMeasurable hr0 hrTop).mp
    simpa only [ENNReal.toReal_ofReal hr.le] using hrNorm
  have hMemp : MemLp f (ENNReal.ofReal p) μ :=
    hMemr.mono_exponent (ENNReal.ofReal_le_ofReal hpr)
  have hpNorm : Integrable (fun ω : Ω => ‖f ω‖ ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp.le] using hMemp.integrable_norm_rpow hp0 hpTop
  have hpInt : Integrable (fun ω : Ω => (f ω) ^ p) μ := by
    refine hpNorm.congr ?_
    filter_upwards [hfnn] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω]
  refine ⟨hpInt, ?_⟩
  have hIntegralP : (∫ ω : Ω, ‖f ω‖ ^ p ∂μ) = ∫ ω : Ω, (f ω) ^ p ∂μ := by
    apply integral_congr_ae
    filter_upwards [hfnn] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω]
  have hIntegralR : (∫ ω : Ω, ‖f ω‖ ^ r ∂μ) = ∫ ω : Ω, (f ω) ^ r ∂μ := by
    apply integral_congr_ae
    filter_upwards [hfnn] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω]
  have hCompare : eLpNorm f (ENNReal.ofReal p) μ ≤ eLpNorm f (ENNReal.ofReal r) μ :=
    eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpr)
  rw [MemLp.eLpNorm_eq_integral_rpow_norm hp0 hpTop hMemp,
    MemLp.eLpNorm_eq_integral_rpow_norm hr0 hrTop hMemr,
    ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hr.le,
    hIntegralP, hIntegralR] at hCompare
  have hRNonneg : 0 ≤ (∫ ω : Ω, (f ω) ^ r ∂μ) := by
    apply integral_nonneg_of_ae
    filter_upwards [hfnn] with ω hω
    exact Real.rpow_nonneg hω r
  have hRRootNonneg : 0 ≤ (∫ ω : Ω, (f ω) ^ r ∂μ) ^ r⁻¹ :=
    Real.rpow_nonneg hRNonneg _
  simpa only [one_div] using (ENNReal.ofReal_le_ofReal_iff hRRootNonneg).mp hCompare

-- D07: exact frozen declaration; source-only proof.
private theorem ceil_nat_bounds
    (q : ℝ) (hq : 1 ≤ q) :
    1 ≤ Nat.ceil q ∧ q ≤ (Nat.ceil q : ℝ) ∧ (Nat.ceil q : ℝ) ≤ 2 * q := by
  refine ⟨Nat.ceil_pos.mpr (lt_of_lt_of_le zero_lt_one hq), Nat.le_ceil q, ?_⟩
  have hceil : (Nat.ceil q : ℝ) < q + 1 := Nat.ceil_lt_add_one (le_trans zero_le_one hq)
  linarith

-- D08: exact frozen declaration; source-only proof.
theorem sum_nat_moment_from_bound
    (m B : ℝ) (hm : 0 ≤ m) (hB : 0 ≤ B)
    {Ω : Type u} [instΩ : MeasurableSpace Ω]
    (n : ℕ) (μ : Fin n → Measure Ω)
    (hμ : ∀ i : Fin n, IsProbabilityMeasure (μ i))
    (Y : Fin n → Ω → ℝ)
    (hY : ∀ i : Fin n, Measurable (Y i))
    (hYnonneg : ∀ i : Fin n, ∀ᵐ ω ∂(μ i), 0 ≤ Y i ω)
    (hYle : ∀ i : Fin n, ∀ᵐ ω ∂(μ i), Y i ω ≤ B)
    (hYmean : ∀ i : Fin n, (∫ ω : Ω, Y i ω ∂(μ i)) ≤ m)
    (k : ℕ) :
    Integrable (fun x : Fin n → Ω => (coordinateSum Y x) ^ k) (Measure.pi μ) ∧
      (∫ x : Fin n → Ω, (coordinateSum Y x) ^ k ∂(Measure.pi μ)) ≤
        ((n : ℝ) * m + (k : ℝ) * B) ^ k := by
  -- frozen D08/body/momentProperty
  let momentProperty : ℕ → Prop :=
    fun r : ℕ => ∀ (N : ℕ) (ν : Fin N → Measure Ω)
      (hν : ∀ i : Fin N, IsProbabilityMeasure (ν i))
      (Z : Fin N → Ω → ℝ)
      (hZ : ∀ i : Fin N, Measurable (Z i))
      (hZnonneg : ∀ i : Fin N, ∀ᵐ ω ∂(ν i), 0 ≤ Z i ω)
      (hZle : ∀ i : Fin N, ∀ᵐ ω ∂(ν i), Z i ω ≤ B)
      (hZmean : ∀ i : Fin N, (∫ ω : Ω, Z i ω ∂(ν i)) ≤ m),
      Integrable (fun x : Fin N → Ω => (coordinateSum Z x) ^ r) (Measure.pi ν) ∧
        (∫ x : Fin N → Ω, (coordinateSum Z x) ^ r ∂(Measure.pi ν)) ≤
          ((N : ℝ) * m + (r : ℝ) * B) ^ r
  have hAll : ∀ r : ℕ, momentProperty r := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro N ν hν Z hZ hZnonneg hZle hZmean
      -- frozen D08/strong-induction-step/instStepCoordinateProbability
      letI instStepCoordinateProbability : ∀ i : Fin N, IsProbabilityMeasure (ν i) := hν
      -- frozen D08/strong-induction-step/instStepProductProbability
      letI instStepProductProbability : IsProbabilityMeasure (Measure.pi ν) := inferInstance
      -- frozen D08/strong-induction-step/stepMeasure
      let stepMeasure : Measure (Fin N → Ω) := Measure.pi ν
      -- frozen D08/strong-induction-step/stepSum
      let stepSum : (Fin N → Ω) → ℝ := coordinateSum Z
      have hSum : Measurable stepSum ∧
          (∀ᵐ x : Fin N → Ω ∂stepMeasure,
            0 ≤ stepSum x ∧ stepSum x ≤ (N : ℝ) * B) :=
        coordinate_sum_measurable_bounds N ν hν Z hZ B hB hZnonneg hZle
      have hPowerInt : Integrable (fun x : Fin N → Ω => (stepSum x) ^ r) stepMeasure :=
        bounded_nat_power_integrable stepMeasure stepSum hSum.1 ((N : ℝ) * B)
          (mul_nonneg (Nat.cast_nonneg N) hB) hSum.2 r
      cases r with
      | zero =>
        refine ⟨hPowerInt, ?_⟩
        simp [stepMeasure]
      | succ t =>
        cases N with
        | zero =>
          refine ⟨hPowerInt, ?_⟩
          have hNonneg : 0 ≤ ((0 : ℝ) * m + ((t + 1 : ℕ) : ℝ) * B) ^ (t + 1) := by
            positivity
          simpa [stepSum, coordinateSum] using hNonneg
        | succ d =>
          -- frozen D08/r=t+1,N=d+1-positive-branches/minorBase
          let minorBase : ℝ := (d : ℝ) * m + ((t + 1 : ℕ) : ℝ) * B
          -- frozen D08/r=t+1,N=d+1-positive-branches/targetBase
          let targetBase : ℝ := ((d + 1 : ℕ) : ℝ) * m + ((t + 1 : ℕ) : ℝ) * B
          -- frozen D08/r=t+1,N=d+1-positive-branches/weightedKernel
          let weightedKernel : Fin (d + 1) → (Fin (d + 1) → Ω) → ℝ := fun (i : Fin (d + 1)) (x : Fin (d + 1) → Ω) => Z i (x i) * (coordinateSum Z x - Z i (x i) + B) ^ t
          -- frozen D08/r=t+1,N=d+1-positive-branches/totalWeightedKernel
          let totalWeightedKernel : (Fin (d + 1) → Ω) → ℝ := fun x : Fin (d + 1) → Ω => ∑ i : Fin (d + 1), weightedKernel i x
          -- frozen D08/r=t+1,N=d+1-positive-branches/coordinateMean
          let coordinateMean : Fin (d + 1) → ℝ := fun i : Fin (d + 1) => ∫ ω : Ω, Z i ω ∂(ν i)
          -- frozen D08/r=t+1,N=d+1-positive-branches/deletedShiftMoment
          let deletedShiftMoment : Fin (d + 1) → ℝ := fun i : Fin (d + 1) => ∫ z : Fin d → Ω, (coordinateSum (fun j : Fin d => Z (i.succAbove j)) z + B) ^ t ∂(Measure.pi (fun j : Fin d => ν (i.succAbove j)))
          -- frozen D08/r=t+1,N=d+1-positive-branches/factorizedSummand
          let factorizedSummand : Fin (d + 1) → ℝ := fun i : Fin (d + 1) => coordinateMean i * deletedShiftMoment i
          -- frozen D08/r=t+1,N=d+1-positive-branches/uniformSummand
          let uniformSummand : Fin (d + 1) → ℝ := fun _ : Fin (d + 1) => m * minorBase ^ t
          have hFactor : ∀ i : Fin (d + 1),
              Integrable (weightedKernel i) stepMeasure ∧
                (∫ x : Fin (d + 1) → Ω, weightedKernel i x ∂stepMeasure) =
                  factorizedSummand i := by
            intro i
            exact coordinate_delete_integral_factor d ν hν Z hZ B hB hZnonneg hZle i t
          have hTotalInt : Integrable totalWeightedKernel stepMeasure :=
            integrable_finsetSum Finset.univ (fun i _ => (hFactor i).1)
          have hCoordinates : ∀ᵐ x : Fin (d + 1) → Ω ∂stepMeasure,
              ∀ i : Fin (d + 1), 0 ≤ Z i (x i) ∧ Z i (x i) ≤ B := by
            rw [ae_all_iff]
            intro i
            exact (@Measure.tendsto_eval_ae_ae _ _ _ _ ν (fun j => inferInstance) i).eventually
              ((hZnonneg i).and (hZle i))
          have hDomination : ∀ᵐ x : Fin (d + 1) → Ω ∂stepMeasure,
              (stepSum x) ^ (t + 1) ≤ totalWeightedKernel x := by
            filter_upwards [hCoordinates, hSum.2] with x hx hs
            calc
              (stepSum x) ^ (t + 1) =
                  ∑ i : Fin (d + 1), Z i (x i) * (stepSum x) ^ t := by
                rw [← Finset.sum_mul]
                exact pow_succ' (stepSum x) t
              _ ≤ totalWeightedKernel x := by
                apply Finset.sum_le_sum
                intro i hi
                dsimp only [weightedKernel]
                apply mul_le_mul_of_nonneg_left _ (hx i).1
                have hBaseLe : stepSum x ≤ coordinateSum Z x - Z i (x i) + B := by
                  change coordinateSum Z x ≤ coordinateSum Z x - Z i (x i) + B
                  linarith [(hx i).2]
                have hStepNonneg : 0 ≤ stepSum x := hs.1
                gcongr
          have hShiftBounds : ∀ i : Fin (d + 1),
              0 ≤ deletedShiftMoment i ∧ deletedShiftMoment i ≤ minorBase ^ t := by
            intro i
            -- frozen D08/per-deletion-i/deletedMeasure
            let deletedMeasure : Fin d → Measure Ω := fun j : Fin d => ν (i.succAbove j)
            -- frozen D08/per-deletion-i/deletedSeed
            let deletedSeed : Fin d → Ω → ℝ := fun j : Fin d => Z (i.succAbove j)
            -- frozen D08/per-deletion-i/deletedSum
            let deletedSum : (Fin d → Ω) → ℝ := coordinateSum deletedSeed
            -- frozen D08/per-deletion-i/shiftMomentBase
            let shiftMomentBase : ℝ := (d : ℝ) * m
            have hLow : ∀ j : ℕ, j ≤ t →
                Integrable (fun z : Fin d → Ω => (deletedSum z) ^ j)
                  (Measure.pi deletedMeasure) ∧
                  (∫ z : Fin d → Ω, (deletedSum z) ^ j ∂(Measure.pi deletedMeasure)) ≤
                    (shiftMomentBase + (j : ℝ) * B) ^ j := by
              intro j hj
              have hjlt : j < t + 1 := Nat.lt_succ_of_le hj
              exact ih j hjlt d deletedMeasure (fun l => hν (i.succAbove l))
                deletedSeed (fun l => hZ (i.succAbove l))
                (fun l => hZnonneg (i.succAbove l)) (fun l => hZle (i.succAbove l))
                (fun l => hZmean (i.succAbove l))
            have hDeleted : Measurable deletedSum ∧
                (∀ᵐ z : Fin d → Ω ∂(Measure.pi deletedMeasure),
                  0 ≤ deletedSum z ∧ deletedSum z ≤ (d : ℝ) * B) :=
              coordinate_sum_measurable_bounds d deletedMeasure
                (fun j => hν (i.succAbove j)) deletedSeed
                (fun j => hZ (i.succAbove j)) B hB
                (fun j => hZnonneg (i.succAbove j)) (fun j => hZle (i.succAbove j))
            have hDeletedProductProbability : IsProbabilityMeasure (Measure.pi deletedMeasure) :=
              @Measure.pi.instIsProbabilityMeasure _ _ _ _ deletedMeasure
                (fun j : Fin d => hν (i.succAbove j))
            have hShifted : Integrable (fun z : Fin d → Ω => (deletedSum z + B) ^ t)
                (Measure.pi deletedMeasure) ∧
                (∫ z : Fin d → Ω, (deletedSum z + B) ^ t ∂(Measure.pi deletedMeasure)) ≤
                  (shiftMomentBase + (t : ℝ) * B + B) ^ t :=
              shifted_nat_moment_le (instProbability := hDeletedProductProbability)
                (Measure.pi deletedMeasure) deletedSum hDeleted.1
                (hDeleted.2.mono (fun z hz => hz.1)) shiftMomentBase B B
                (mul_nonneg (Nat.cast_nonneg d) hm) hB hB t
                (fun j hj => (hLow j hj).1) (fun j hj => (hLow j hj).2)
            have hShiftBase : shiftMomentBase + (t : ℝ) * B + B = minorBase := by
              dsimp only [shiftMomentBase, minorBase]
              push_cast
              ring
            constructor
            · apply integral_nonneg_of_ae
              filter_upwards [hDeleted.2] with z hz
              exact pow_nonneg (add_nonneg hz.1 hB) t
            · simpa only [hShiftBase] using hShifted.2
          have hTermBound : ∀ i : Fin (d + 1), factorizedSummand i ≤ uniformSummand i := by
            intro i
            change coordinateMean i * deletedShiftMoment i ≤ m * minorBase ^ t
            exact (mul_le_mul_of_nonneg_right (hZmean i) (hShiftBounds i).1).trans
              (mul_le_mul_of_nonneg_left (hShiftBounds i).2 hm)
          have hMinorNonneg : 0 ≤ minorBase := by dsimp only [minorBase]; positivity
          have hTargetNonneg : 0 ≤ targetBase := by dsimp only [targetBase]; positivity
          have hMinorLe : minorBase ≤ targetBase := by
            dsimp only [minorBase, targetBase]
            push_cast
            nlinarith
          have hMeanLe : ((d + 1 : ℕ) : ℝ) * m ≤ targetBase := by
            dsimp only [targetBase]
            exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg (t + 1)) hB)
          have hPowerLe : minorBase ^ t ≤ targetBase ^ t := by gcongr
          refine ⟨hPowerInt, ?_⟩
          change (∫ x : Fin (d + 1) → Ω, (stepSum x) ^ (t + 1) ∂stepMeasure) ≤
            targetBase ^ (t + 1)
          calc
            (∫ x : Fin (d + 1) → Ω, (stepSum x) ^ (t + 1) ∂stepMeasure) ≤
                ∫ x : Fin (d + 1) → Ω, totalWeightedKernel x ∂stepMeasure :=
              integral_mono_ae hPowerInt hTotalInt hDomination
            _ = ∑ i : Fin (d + 1), factorizedSummand i := by
              change (∫ x : Fin (d + 1) → Ω,
                ∑ i : Fin (d + 1), weightedKernel i x ∂stepMeasure) = _
              rw [integral_finsetSum Finset.univ (fun i _ => (hFactor i).1)]
              exact Finset.sum_congr rfl (fun i _ => (hFactor i).2)
            _ ≤ ∑ i : Fin (d + 1), uniformSummand i :=
              Finset.sum_le_sum (fun i _ => hTermBound i)
            _ = ((d + 1 : ℕ) : ℝ) * m * minorBase ^ t := by
              simp [uniformSummand, mul_assoc]
            _ ≤ targetBase * targetBase ^ t :=
              mul_le_mul hMeanLe hPowerLe (pow_nonneg hMinorNonneg t) hTargetNonneg
            _ = targetBase ^ (t + 1) := (pow_succ' targetBase t).symm
  exact hAll k n μ hμ Y hY hYnonneg hYle hYmean

-- D09: exact frozen declaration; source-only proof.
theorem sum_real_moment_from_bound
    (m B : ℝ) (hm : 0 ≤ m) (hB : 0 ≤ B)
    {Ω : Type u} [instΩ : MeasurableSpace Ω]
    (n : ℕ) (μ : Fin n → Measure Ω)
    (hμ : ∀ i : Fin n, IsProbabilityMeasure (μ i))
    (Y : Fin n → Ω → ℝ)
    (hY : ∀ i : Fin n, Measurable (Y i))
    (hYnonneg : ∀ i : Fin n, ∀ᵐ ω ∂(μ i), 0 ≤ Y i ω)
    (hYle : ∀ i : Fin n, ∀ᵐ ω ∂(μ i), Y i ω ≤ B)
    (hYmean : ∀ i : Fin n, (∫ ω : Ω, Y i ω ∂(μ i)) ≤ m)
    (q : ℝ) (hq : 1 ≤ q) :
    Integrable (fun x : Fin n → Ω => (coordinateSum Y x) ^ q) (Measure.pi μ) ∧
      (∫ x : Fin n → Ω, (coordinateSum Y x) ^ q ∂(Measure.pi μ)) ^ (1 / q) ≤
        (n : ℝ) * m + 2 * B * q := by
  -- frozen D09/body/instCoordinateProbability
  letI instCoordinateProbability : ∀ i : Fin n, IsProbabilityMeasure (μ i) := hμ
  -- frozen D09/body/instCoordinateSigmaFinite
  letI instCoordinateSigmaFinite : ∀ i : Fin n, SigmaFinite (μ i) := fun i : Fin n => inferInstance
  -- frozen D09/body/instProductProbability
  letI instProductProbability : IsProbabilityMeasure (Measure.pi μ) := inferInstance
  -- frozen D09/body/sampleMeasure
  let sampleMeasure : Measure (Fin n → Ω) := Measure.pi μ
  -- frozen D09/body/sampleSum
  let sampleSum : (Fin n → Ω) → ℝ := coordinateSum Y
  -- frozen D09/body/roundedExponent
  let roundedExponent : ℕ := Nat.ceil q
  -- frozen D09/body/integerRootBase
  let integerRootBase : ℝ := (n : ℝ) * m + (roundedExponent : ℝ) * B
  have hRounded : 1 ≤ roundedExponent ∧ q ≤ (roundedExponent : ℝ) ∧
      (roundedExponent : ℝ) ≤ 2 * q := ceil_nat_bounds q hq
  have hQ : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hRoundedPositive : 0 < (roundedExponent : ℝ) := Nat.cast_pos.mpr hRounded.1
  have hSum : Measurable sampleSum ∧
      (∀ᵐ x : Fin n → Ω ∂sampleMeasure,
        0 ≤ sampleSum x ∧ sampleSum x ≤ (n : ℝ) * B) :=
    coordinate_sum_measurable_bounds n μ hμ Y hY B hB hYnonneg hYle
  have hIntegerMoment : Integrable (fun x : Fin n → Ω => (sampleSum x) ^ roundedExponent)
      sampleMeasure ∧
      (∫ x : Fin n → Ω, (sampleSum x) ^ roundedExponent ∂sampleMeasure) ≤
        integerRootBase ^ roundedExponent :=
    sum_nat_moment_from_bound m B hm hB n μ hμ Y hY hYnonneg hYle hYmean roundedExponent
  have hRoundedIntegrable :
      Integrable (fun x : Fin n → Ω => (sampleSum x) ^ (roundedExponent : ℝ)) sampleMeasure := by
    simpa only [Real.rpow_natCast] using hIntegerMoment.1
  have hRealMoment : Integrable (fun x : Fin n → Ω => (sampleSum x) ^ q) sampleMeasure ∧
      (∫ x : Fin n → Ω, (sampleSum x) ^ q ∂sampleMeasure) ^ (1 / q) ≤
        (∫ x : Fin n → Ω, (sampleSum x) ^ (roundedExponent : ℝ) ∂sampleMeasure) ^
          (1 / (roundedExponent : ℝ)) :=
    nonneg_real_moment_mono sampleMeasure sampleSum hSum.1
      (hSum.2.mono (fun x hx => hx.1)) q (roundedExponent : ℝ)
      hQ hRounded.2.1 hRoundedIntegrable
  have hIntegerIntegralNonneg :
      0 ≤ (∫ x : Fin n → Ω, (sampleSum x) ^ roundedExponent ∂sampleMeasure) := by
    apply integral_nonneg_of_ae
    filter_upwards [hSum.2] with x hx
    exact pow_nonneg hx.1 roundedExponent
  have hBaseNonneg : 0 ≤ integerRootBase := by dsimp only [integerRootBase]; positivity
  have hIntegerRoot :
      (∫ x : Fin n → Ω, (sampleSum x) ^ roundedExponent ∂sampleMeasure) ^
          (1 / (roundedExponent : ℝ)) ≤ integerRootBase := by
    calc
      _ ≤ (integerRootBase ^ roundedExponent) ^ (1 / (roundedExponent : ℝ)) :=
        Real.rpow_le_rpow hIntegerIntegralNonneg hIntegerMoment.2 (by positivity)
      _ = _ := by
        simpa only [one_div] using
          Real.pow_rpow_inv_natCast hBaseNonneg (Nat.ne_of_gt hRounded.1)
  refine ⟨hRealMoment.1, ?_⟩
  calc
    _ ≤ (∫ x : Fin n → Ω, (sampleSum x) ^ roundedExponent ∂sampleMeasure) ^
        (1 / (roundedExponent : ℝ)) := by
      simpa only [Real.rpow_natCast] using hRealMoment.2
    _ ≤ integerRootBase := hIntegerRoot
    _ ≤ (n : ℝ) * m + 2 * B * q := by
      dsimp only [integerRootBase]
      nlinarith [mul_le_mul_of_nonneg_right hRounded.2.2 hB]

end
end Shao.OQ6.BoundedMeanSumMoments
