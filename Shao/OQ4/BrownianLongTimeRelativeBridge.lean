-- Complete LOCAL implementation of the exact parent freeze.
-- All 10 frozen heads, zero new values, and all 6 imports are preserved.
-- No Lean/import/object/toolchain/build command is authorized in this phase.
import Shao.OQ4.KilledBlockBounds
import Shao.OQ4.BrownianFixedTimeNormalization
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Order.Filter.AtTopBot.Tendsto

noncomputable section
namespace Shao.OQ4.BrownianLongTimeRelativeBridge
open MeasureTheory Filter
open scoped Topology

private theorem lower_moments_integrable
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν) :
    Integrable (fun x : ℝ => x) ν ∧ Integrable (fun x : ℝ => x ^ 2) ν := by
  have hdom : Integrable (fun x : ℝ => 1 + |x| ^ 3) ν :=
    (integrable_const (1 : ℝ)).add h3
  have hsmall (r : ℝ) (hr : 0 ≤ r) : r ≤ 1 + r ^ 3 ∧ r ^ 2 ≤ 1 + r ^ 3 := by
    by_cases hr1 : r ≤ 1
    · have hp := mul_nonneg hr (sub_nonneg.mpr hr1)
      have hr3 : 0 ≤ r ^ 3 := pow_nonneg hr 3
      constructor <;> nlinarith
    · have hlarge : 1 ≤ r := (lt_of_not_ge hr1).le
      have hp := mul_nonneg hr (sub_nonneg.mpr hlarge)
      have hq := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hlarge)
      constructor <;> nlinarith
  have hid : AEStronglyMeasurable (fun x : ℝ => x) ν :=
    measurable_id.aestronglyMeasurable
  have hsq : AEStronglyMeasurable (fun x : ℝ => x ^ 2) ν :=
    (by fun_prop : Measurable (fun x : ℝ => x ^ 2)).aestronglyMeasurable
  refine ⟨hdom.mono' hid ?_, hdom.mono' hsq ?_⟩
  · exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using (hsmall |x| (abs_nonneg x)).1
  · exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x), sq_abs] using
        (hsmall |x| (abs_nonneg x)).2

private theorem third_moment_nonneg (ν : Measure ℝ) :
    0 ≤ ∫ x : ℝ, |x| ^ 3 ∂ν := by
  exact integral_nonneg fun x => pow_nonneg (abs_nonneg x) 3

private theorem bridge_constants_nonnegative
    (M Cq Cs : ℝ) (hM : 0 ≤ M) (hCq : 0 ≤ Cq) (hCs : 0 ≤ Cs) :
    0 ≤ killedResidualConstant M Cq Cs ∧
      0 < 2 * (1 + (2 * Cs) * Real.exp (Real.pi ^ 2)) * Real.exp (Real.pi ^ 2) := by
  constructor
  · unfold killedResidualConstant killedLayerConstant
    positivity
  · positivity

private theorem large_parameters_eventually
    (M : ℝ) (hSeq : ℕ → ℝ) (hinfty : Tendsto hSeq atTop atTop) :
    ∀ᶠ j in atTop, 3 ≤ hSeq j ∧ Real.pi * (1 + M) ≤ hSeq j := by
  exact (hinfty.eventually (eventually_ge_atTop 3)).and
    (hinfty.eventually (eventually_ge_atTop (Real.pi * (1 + M))))

private theorem floor_le_horizon_eventually
    (hSeq : ℕ → ℝ) (NSeq : ℕ → ℕ) (hpos : ∀ j, 0 < hSeq j)
    (hlong : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 2) atTop atTop) :
    ∀ᶠ j in atTop, ⌊hSeq j ^ 2⌋₊ ≤ NSeq j := by
  filter_upwards [hlong.eventually (eventually_ge_atTop (1 : ℝ))] with j hj
  have hh2 : 0 < hSeq j ^ 2 := sq_pos_of_pos (hpos j)
  have hN : hSeq j ^ 2 ≤ (NSeq j : ℝ) := by
    simpa only [one_mul] using (le_div_iff₀ hh2).mp hj
  have hf : (⌊hSeq j ^ 2⌋₊ : ℝ) ≤ (NSeq j : ℝ) :=
    (Nat.floor_le (sq_nonneg (hSeq j))).trans hN
  exact_mod_cast hf

private theorem absorption_coefficient_tendsto_zero
    (M Cq Cs : ℝ) (hSeq : ℕ → ℝ) (NSeq : ℕ → ℕ)
    (hinfty : Tendsto hSeq atTop atTop)
    (hshort : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 3)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j => ((2 * Cs) * Real.exp (Real.pi ^ 2)) *
        (killedResidualConstant M Cq Cs * Real.exp (Real.pi ^ 2) / hSeq j ^ 3) *
          (NSeq j : ℝ) +
        (2 * Cs * M) * Real.exp (Real.pi ^ 2) / hSeq j)
      atTop (𝓝 (0 : ℝ)) := by
  let A : ℝ := ((2 * Cs) * Real.exp (Real.pi ^ 2)) *
    (killedResidualConstant M Cq Cs * Real.exp (Real.pi ^ 2))
  let B : ℝ := (2 * Cs * M) * Real.exp (Real.pi ^ 2)
  have hfirst : Tendsto (fun j => A * ((NSeq j : ℝ) / hSeq j ^ 3))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hshort.const_mul A
  have hsecond : Tendsto (fun j => B * (hSeq j)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hinfty).const_mul B
  have hs : Tendsto (fun j => A * ((NSeq j : ℝ) / hSeq j ^ 3) + B * (hSeq j)⁻¹)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [add_zero] using hfirst.add hsecond
  have heq (j : ℕ) :
      ((2 * Cs) * Real.exp (Real.pi ^ 2)) *
          (killedResidualConstant M Cq Cs * Real.exp (Real.pi ^ 2) / hSeq j ^ 3) *
            (NSeq j : ℝ) +
          (2 * Cs * M) * Real.exp (Real.pi ^ 2) / hSeq j =
        A * ((NSeq j : ℝ) / hSeq j ^ 3) + B * (hSeq j)⁻¹ := by
    dsimp only [A, B]
    simp only [div_eq_mul_inv]
    ring
  exact Filter.Tendsto.congr' (Eventually.of_forall fun j => (heq j).symm) hs

-- The actual finite theorem is called with M equal to the actual third moment.
-- The all-time primitive probabilities remain explicit inputs.
private theorem finite_absorption_eventually
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (Cq Cs : ℝ) (hCq : 0 ≤ Cq) (hCs : 0 ≤ Cs)
    (hAC : iidIntervalConcentration ν (∫ x : ℝ, |x| ^ 3 ∂ν) Cq)
    (hS : iidOneSidedSurvival ν (∫ x : ℝ, |x| ^ 3 ∂ν) Cs)
    (hSeq : ℕ → ℝ) (NSeq : ℕ → ℕ) (hpos : ∀ j, 0 < hSeq j)
    (hinfty : Tendsto hSeq atTop atTop)
    (hlong : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 3)
      atTop (𝓝 (0 : ℝ))) :
    let R : ℝ := Real.exp (Real.pi ^ 2)
    let H : ℝ := 2 * (1 + (2 * Cs) * R) * R
    ∀ᶠ j in atTop,
      (∀ k : ℕ, k ≤ NSeq j →
        0 ≤ normalizedKernelMass ν (hSeq j) k 0 ∧
          normalizedKernelMass ν (hSeq j) k 0 ≤ H) ∧
      (∀ k : ℕ, ⌊hSeq j ^ 2⌋₊ ≤ k → k ≤ NSeq j →
        |normalizedKernelCosine ν (hSeq j) k 0 -
          normalizedKernelCosine ν (hSeq j) ⌊hSeq j ^ 2⌋₊ 0| ≤
            (killedResidualConstant (∫ x : ℝ, |x| ^ 3 ∂ν) Cq Cs * R * H) *
              ((NSeq j : ℝ) / hSeq j ^ 3)) := by
  dsimp only
  let β : ℝ := ∫ x : ℝ, |x| ^ 3 ∂ν
  let R : ℝ := Real.exp (Real.pi ^ 2)
  let H : ℝ := 2 * (1 + (2 * Cs) * R) * R
  rcases lower_moments_integrable ν h3 with ⟨hId, hSq⟩
  have hβ : 0 ≤ β := third_moment_nonneg ν
  have hconstants := bridge_constants_nonnegative β Cq Cs hβ hCq hCs
  have hE : 0 ≤ killedResidualConstant β Cq Cs := hconstants.1
  have hR : 0 < R := Real.exp_pos _
  have hH : 0 ≤ H := hconstants.2.le
  have hsmallLimit := absorption_coefficient_tendsto_zero β Cq Cs hSeq NSeq hinfty hshort
  have hsmall : ∀ᶠ j in atTop,
      ((2 * Cs) * R) * (killedResidualConstant β Cq Cs * R / hSeq j ^ 3) *
          (NSeq j : ℝ) + (2 * Cs * β) * R / hSeq j ≤ (1 / 2 : ℝ) := by
    obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp hsmallLimit) (1 / 2) (by norm_num)
    filter_upwards [eventually_ge_atTop J] with j hj
    have hab :
        |((2 * Cs) * R) * (killedResidualConstant β Cq Cs * R / hSeq j ^ 3) *
            (NSeq j : ℝ) + (2 * Cs * β) * R / hSeq j| < (1 / 2 : ℝ) := by
      simpa only [Real.dist_eq, sub_zero] using hJ j hj
    exact (le_abs_self _).trans hab.le
  filter_upwards [large_parameters_eventually β hSeq hinfty,
    floor_le_horizon_eventually hSeq NSeq hpos hlong, hsmall] with j hj hmN hsj
  have hz : |(0 : ℝ)| ≤ hSeq j := by simpa only [abs_zero] using (hpos j).le
  have hs := killed_block_finite_absorption ν β (hSeq j) Cq Cs hj.1
    hId hSq h3 hmean hsecond hβ le_rfl hCq hCs hAC hS hj.2
    (NSeq j) hmN hsj 0 hz
  dsimp only at hs
  refine ⟨hs.1, ?_⟩
  intro k hmk hkN
  have hh : 0 < hSeq j := hpos j
  have hsub : ((k - ⌊hSeq j ^ 2⌋₊ : ℕ) : ℝ) ≤ (NSeq j : ℝ) := by
    have hsubNat : k - ⌊hSeq j ^ (2 : ℕ)⌋₊ ≤ NSeq j := (Nat.sub_le _ _).trans hkN
    exact Nat.cast_le.mpr hsubNat
  have hER : 0 ≤ killedResidualConstant β Cq Cs * R / hSeq j ^ 3 := by positivity
  calc
    _ ≤ (killedResidualConstant β Cq Cs * R / hSeq j ^ 3) *
        ((k - ⌊hSeq j ^ 2⌋₊ : ℕ) : ℝ) * H := hs.2 k hmk hkN
    _ ≤ (killedResidualConstant β Cq Cs * R / hSeq j ^ 3) * (NSeq j : ℝ) * H :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsub hER) hH
    _ = (killedResidualConstant β Cq Cs * R * H) * ((NSeq j : ℝ) / hSeq j ^ 3) := by
      simp only [div_eq_mul_inv]
      ring

-- Definitional rewriting and composition of the actual148 B1 producer.
-- No supplied Brownian data, desired normalization, or limit premise.
private theorem fixed_time_normalization_along
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (hSeq : ℕ → ℝ) (hinfty : Tendsto hSeq atTop atTop) :
    Tendsto (fun j => normalizedKernelCosine ν (hSeq j) ⌊hSeq j ^ 2⌋₊ 0)
      atTop (𝓝 (1 : ℝ)) := by
  have ht := (Shao.OQ4.BrownianFixedTimeNormalization.fixed_time_normalization
    ν h3 hmean hsecond).comp hinfty
  change Tendsto (fun j =>
    (cosineCoefficient ν (Real.pi / (2 * hSeq j)) ^ ⌊hSeq j ^ 2⌋₊)⁻¹ *
      killedAction ν (hSeq j) ⌊hSeq j ^ 2⌋₊
        (fun w => Real.cos ((Real.pi / (2 * hSeq j)) * w)) 0) atTop (𝓝 (1 : ℝ))
  simpa only [Function.comp_def] using ht

private theorem drift_error_tendsto_zero
    (ν : Measure ℝ) (Cq Cs : ℝ) (hSeq : ℕ → ℝ) (NSeq : ℕ → ℕ)
    (hshort : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 3)
      atTop (𝓝 (0 : ℝ))) :
    let R : ℝ := Real.exp (Real.pi ^ 2)
    let H : ℝ := 2 * (1 + (2 * Cs) * R) * R
    Tendsto (fun j =>
      (killedResidualConstant (∫ x : ℝ, |x| ^ 3 ∂ν) Cq Cs * R * H) *
        ((NSeq j : ℝ) / hSeq j ^ 3)) atTop (𝓝 (0 : ℝ)) := by
  dsimp only
  simpa only [mul_zero] using hshort.const_mul
    (killedResidualConstant (∫ x : ℝ, |x| ^ 3 ∂ν) Cq Cs * Real.exp (Real.pi ^ 2) *
      (2 * (1 + (2 * Cs) * Real.exp (Real.pi ^ 2)) * Real.exp (Real.pi ^ 2)))

-- PUBLIC fixed-law actual D8 bridge, explicitly conditional on actual S/AC.
-- H is positive and independent of every future terminal Brownian block time T.
-- This is not a theorem closing S/AC, K, Kv or general OQ4.
theorem long_time_relative_bridge
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (Cq Cs : ℝ) (hCq : 0 ≤ Cq) (hCs : 0 ≤ Cs)
    (hAC : iidIntervalConcentration ν (∫ x : ℝ, |x| ^ 3 ∂ν) Cq)
    (hS : iidOneSidedSurvival ν (∫ x : ℝ, |x| ^ 3 ∂ν) Cs)
    (hSeq : ℕ → ℝ) (NSeq : ℕ → ℕ) (hpos : ∀ j, 0 < hSeq j)
    (hinfty : Tendsto hSeq atTop atTop)
    (hlong : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 3)
      atTop (𝓝 (0 : ℝ))) :
    let R : ℝ := Real.exp (Real.pi ^ 2)
    let H : ℝ := 2 * (1 + (2 * Cs) * R) * R
    0 < H ∧
      (∀ᶠ j in atTop, ∀ k : ℕ, k ≤ NSeq j →
        0 ≤ normalizedKernelMass ν (hSeq j) k 0 ∧
          normalizedKernelMass ν (hSeq j) k 0 ≤ H) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
        ∀ k : ℕ, ⌊hSeq j ^ 2⌋₊ ≤ k → k ≤ NSeq j →
          |normalizedKernelCosine ν (hSeq j) k 0 - 1| < ε) := by
  let R : ℝ := Real.exp (Real.pi ^ 2)
  let H : ℝ := 2 * (1 + (2 * Cs) * R) * R
  have hH : 0 < H :=
    (bridge_constants_nonnegative (∫ x : ℝ, |x| ^ 3 ∂ν) Cq Cs
      (third_moment_nonneg ν) hCq hCs).2
  have hfinite := finite_absorption_eventually ν h3 hmean hsecond Cq Cs hCq hCs hAC hS
    hSeq NSeq hpos hinfty hlong hshort
  have hbase := fixed_time_normalization_along ν h3 hmean hsecond hSeq hinfty
  have herr := drift_error_tendsto_zero ν Cq Cs hSeq NSeq hshort
  refine ⟨hH, hfinite.mono (fun _ hj => hj.1), ?_⟩
  intro ε hε
  obtain ⟨J₁, hJ₁⟩ := (Metric.tendsto_atTop.mp hbase) (ε / 2) (by linarith)
  obtain ⟨J₂, hJ₂⟩ := (Metric.tendsto_atTop.mp herr) (ε / 2) (by linarith)
  filter_upwards [hfinite, eventually_ge_atTop J₁, eventually_ge_atTop J₂] with j hfj hj₁ hj₂
  intro k hmk hkN
  have hB : |normalizedKernelCosine ν (hSeq j) ⌊hSeq j ^ 2⌋₊ 0 - 1| < ε / 2 := by
    simpa only [Real.dist_eq] using hJ₁ j hj₁
  have hD : (killedResidualConstant (∫ x : ℝ, |x| ^ 3 ∂ν) Cq Cs * R * H) *
      ((NSeq j : ℝ) / hSeq j ^ 3) < ε / 2 := by
    have hab : |(killedResidualConstant (∫ x : ℝ, |x| ^ 3 ∂ν) Cq Cs * R * H) *
        ((NSeq j : ℝ) / hSeq j ^ 3)| < ε / 2 := by
      simpa only [Real.dist_eq, sub_zero] using hJ₂ j hj₂
    exact lt_of_le_of_lt (le_abs_self _) hab
  calc
    |normalizedKernelCosine ν (hSeq j) k 0 - 1| =
        |(normalizedKernelCosine ν (hSeq j) k 0 -
          normalizedKernelCosine ν (hSeq j) ⌊hSeq j ^ 2⌋₊ 0) +
          (normalizedKernelCosine ν (hSeq j) ⌊hSeq j ^ 2⌋₊ 0 - 1)| := by
      congr 1
      ring
    _ ≤ |normalizedKernelCosine ν (hSeq j) k 0 -
          normalizedKernelCosine ν (hSeq j) ⌊hSeq j ^ 2⌋₊ 0| +
        |normalizedKernelCosine ν (hSeq j) ⌊hSeq j ^ 2⌋₊ 0 - 1| := abs_add_le _ _
    _ ≤ (killedResidualConstant (∫ x : ℝ, |x| ^ 3 ∂ν) Cq Cs * R * H) *
          ((NSeq j : ℝ) / hSeq j ^ 3) +
        |normalizedKernelCosine ν (hSeq j) ⌊hSeq j ^ 2⌋₊ 0 - 1| :=
      add_le_add (hfj.2 k hmk hkN) le_rfl
    _ < ε / 2 + ε / 2 := add_lt_add hD hB
    _ = ε := by ring

-- V2 separately frozen additions: original common-M varying-row scope.
-- Combined LOCAL file: 13 theorem heads, zero new values, the same 6 imports.
private theorem varying_row_finite_absorption_eventually
    (νSeq : ℕ → Measure ℝ) (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (Cq Cs : ℝ) (hCq : 0 ≤ Cq) (hCs : 0 ≤ Cs)
    (hAC : ∀ j, iidIntervalConcentration (νSeq j) (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) Cq)
    (hS : ∀ j, iidOneSidedSurvival (νSeq j) (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) Cs)
    (hSeq : ℕ → ℝ) (NSeq : ℕ → ℕ) (hpos : ∀ j, 0 < hSeq j)
    (hinfty : Tendsto hSeq atTop atTop)
    (hlong : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 3)
      atTop (𝓝 (0 : ℝ))) :
    let R : ℝ := Real.exp (Real.pi ^ 2)
    let H : ℝ := 2 * (1 + (2 * Cs) * R) * R
    ∀ᶠ j in atTop,
      (∀ k : ℕ, k ≤ NSeq j →
        0 ≤ @normalizedKernelMass (νSeq j) (hprob j) (hSeq j) k 0 ∧
          @normalizedKernelMass (νSeq j) (hprob j) (hSeq j) k 0 ≤ H) ∧
      (∀ k : ℕ, ⌊hSeq j ^ 2⌋₊ ≤ k → k ≤ NSeq j →
        |@normalizedKernelCosine (νSeq j) (hprob j) (hSeq j) k 0 -
          @normalizedKernelCosine (νSeq j) (hprob j) (hSeq j) ⌊hSeq j ^ 2⌋₊ 0| ≤
            (killedResidualConstant M Cq Cs * R * H) * ((NSeq j : ℝ) / hSeq j ^ 3)) := by
  dsimp only
  let R : ℝ := Real.exp (Real.pi ^ 2)
  let H : ℝ := 2 * (1 + (2 * Cs) * R) * R
  have hM0 : 0 ≤ M := (third_moment_nonneg (νSeq 0)).trans (hM 0)
  have hconstants := bridge_constants_nonnegative M Cq Cs hM0 hCq hCs
  have hE : 0 ≤ killedResidualConstant M Cq Cs := hconstants.1
  have hR : 0 < R := Real.exp_pos _
  have hH : 0 ≤ H := hconstants.2.le
  have hsmallLimit := absorption_coefficient_tendsto_zero M Cq Cs hSeq NSeq hinfty hshort
  have hsmall : ∀ᶠ j in atTop,
      ((2 * Cs) * R) * (killedResidualConstant M Cq Cs * R / hSeq j ^ 3) *
          (NSeq j : ℝ) + (2 * Cs * M) * R / hSeq j ≤ (1 / 2 : ℝ) := by
    obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp hsmallLimit) (1 / 2) (by norm_num)
    filter_upwards [eventually_ge_atTop J] with j hj
    have hab :
        |((2 * Cs) * R) * (killedResidualConstant M Cq Cs * R / hSeq j ^ 3) *
            (NSeq j : ℝ) + (2 * Cs * M) * R / hSeq j| < (1 / 2 : ℝ) := by
      simpa only [Real.dist_eq, sub_zero] using hJ j hj
    exact (le_abs_self _).trans hab.le
  filter_upwards [large_parameters_eventually M hSeq hinfty,
    floor_le_horizon_eventually hSeq NSeq hpos hlong, hsmall] with j hj hmN hsj
  letI : IsProbabilityMeasure (νSeq j) := hprob j
  rcases lower_moments_integrable (νSeq j) (h3 j) with ⟨hId, hSq⟩
  have hz : |(0 : ℝ)| ≤ hSeq j := by simpa only [abs_zero] using (hpos j).le
  have hs := killed_block_finite_absorption (νSeq j) M (hSeq j) Cq Cs hj.1
    hId hSq (h3 j) (hmean j) (hsecond j) hM0 (hM j) hCq hCs (hAC j) (hS j) hj.2
    (NSeq j) hmN hsj 0 hz
  dsimp only at hs
  refine ⟨hs.1, ?_⟩
  intro k hmk hkN
  have hh : 0 < hSeq j := hpos j
  have hsub : ((k - ⌊hSeq j ^ 2⌋₊ : ℕ) : ℝ) ≤ (NSeq j : ℝ) := by
    have hsubNat : k - ⌊hSeq j ^ (2 : ℕ)⌋₊ ≤ NSeq j := (Nat.sub_le _ _).trans hkN
    exact Nat.cast_le.mpr hsubNat
  have hER : 0 ≤ killedResidualConstant M Cq Cs * R / hSeq j ^ 3 := by positivity
  calc
    _ ≤ (killedResidualConstant M Cq Cs * R / hSeq j ^ 3) *
        ((k - ⌊hSeq j ^ 2⌋₊ : ℕ) : ℝ) * H := hs.2 k hmk hkN
    _ ≤ (killedResidualConstant M Cq Cs * R / hSeq j ^ 3) * (NSeq j : ℝ) * H :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsub hER) hH
    _ = (killedResidualConstant M Cq Cs * R * H) * ((NSeq j : ℝ) / hSeq j ^ 3) := by
      simp only [div_eq_mul_inv]
      ring

-- Uses actual148.varying_row_fixed_time_limits third conjunct.
-- Does not use fixed-law B1 composition with a changing law.
private theorem varying_row_fixed_time_normalization_along
    (νSeq : ℕ → Measure ℝ) (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (hpos : ∀ j, 0 < hSeq j)
    (hinfty : Tendsto hSeq atTop atTop) :
    Tendsto (fun j =>
      @normalizedKernelCosine (νSeq j) (hprob j) (hSeq j) ⌊hSeq j ^ 2⌋₊ 0)
      atTop (𝓝 (1 : ℝ)) := by
  have ht := Shao.OQ4.BrownianFixedTimeNormalization.varying_row_fixed_time_limits
    νSeq hprob h3 hmean hsecond M hM hSeq hpos hinfty
  change Tendsto (fun j =>
    (cosineCoefficient (νSeq j) (Real.pi / (2 * hSeq j)) ^ ⌊hSeq j ^ 2⌋₊)⁻¹ *
      @killedAction (νSeq j) (hprob j) (hSeq j) ⌊hSeq j ^ 2⌋₊
        (fun w => Real.cos ((Real.pi / (2 * hSeq j)) * w)) 0) atTop (𝓝 (1 : ℝ))
  exact ht.2.2

-- PUBLIC common-M varying-row D8 consumer; primitive S/AC remain explicit.
-- M>=0 is derived using row0, not added as a public hypothesis.
-- All normalized outputs use the literal per-row hprob j instance.
theorem varying_row_long_time_relative_bridge
    (νSeq : ℕ → Measure ℝ) (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (Cq Cs : ℝ) (hCq : 0 ≤ Cq) (hCs : 0 ≤ Cs)
    (hAC : ∀ j, iidIntervalConcentration (νSeq j) (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) Cq)
    (hS : ∀ j, iidOneSidedSurvival (νSeq j) (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) Cs)
    (hSeq : ℕ → ℝ) (NSeq : ℕ → ℕ) (hpos : ∀ j, 0 < hSeq j)
    (hinfty : Tendsto hSeq atTop atTop)
    (hlong : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 3)
      atTop (𝓝 (0 : ℝ))) :
    let R : ℝ := Real.exp (Real.pi ^ 2)
    let H : ℝ := 2 * (1 + (2 * Cs) * R) * R
    0 < H ∧
      (∀ᶠ j in atTop, ∀ k : ℕ, k ≤ NSeq j →
        0 ≤ @normalizedKernelMass (νSeq j) (hprob j) (hSeq j) k 0 ∧
          @normalizedKernelMass (νSeq j) (hprob j) (hSeq j) k 0 ≤ H) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
        ∀ k : ℕ, ⌊hSeq j ^ 2⌋₊ ≤ k → k ≤ NSeq j →
          |@normalizedKernelCosine (νSeq j) (hprob j) (hSeq j) k 0 - 1| < ε) := by
  let R : ℝ := Real.exp (Real.pi ^ 2)
  let H : ℝ := 2 * (1 + (2 * Cs) * R) * R
  have hM0 : 0 ≤ M := (third_moment_nonneg (νSeq 0)).trans (hM 0)
  have hH : 0 < H := (bridge_constants_nonnegative M Cq Cs hM0 hCq hCs).2
  have hfinite := varying_row_finite_absorption_eventually νSeq hprob h3 hmean hsecond
    M hM Cq Cs hCq hCs hAC hS hSeq NSeq hpos hinfty hlong hshort
  have hbase := varying_row_fixed_time_normalization_along νSeq hprob h3 hmean hsecond
    M hM hSeq hpos hinfty
  have herr : Tendsto (fun j => (killedResidualConstant M Cq Cs * R * H) *
      ((NSeq j : ℝ) / hSeq j ^ 3)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hshort.const_mul (killedResidualConstant M Cq Cs * R * H)
  refine ⟨hH, hfinite.mono (fun _ hj => hj.1), ?_⟩
  intro ε hε
  obtain ⟨J₁, hJ₁⟩ := (Metric.tendsto_atTop.mp hbase) (ε / 2) (by linarith)
  obtain ⟨J₂, hJ₂⟩ := (Metric.tendsto_atTop.mp herr) (ε / 2) (by linarith)
  filter_upwards [hfinite, eventually_ge_atTop J₁, eventually_ge_atTop J₂] with j hfj hj₁ hj₂
  intro k hmk hkN
  have hB : |@normalizedKernelCosine (νSeq j) (hprob j) (hSeq j) ⌊hSeq j ^ 2⌋₊ 0 - 1| <
      ε / 2 := by
    simpa only [Real.dist_eq] using hJ₁ j hj₁
  have hD : (killedResidualConstant M Cq Cs * R * H) *
      ((NSeq j : ℝ) / hSeq j ^ 3) < ε / 2 := by
    have hab : |(killedResidualConstant M Cq Cs * R * H) *
        ((NSeq j : ℝ) / hSeq j ^ 3)| < ε / 2 := by
      simpa only [Real.dist_eq, sub_zero] using hJ₂ j hj₂
    exact lt_of_le_of_lt (le_abs_self _) hab
  calc
    |@normalizedKernelCosine (νSeq j) (hprob j) (hSeq j) k 0 - 1| =
        |(@normalizedKernelCosine (νSeq j) (hprob j) (hSeq j) k 0 -
          @normalizedKernelCosine (νSeq j) (hprob j) (hSeq j) ⌊hSeq j ^ 2⌋₊ 0) +
          (@normalizedKernelCosine (νSeq j) (hprob j) (hSeq j) ⌊hSeq j ^ 2⌋₊ 0 - 1)| := by
      congr 1
      ring
    _ ≤ |@normalizedKernelCosine (νSeq j) (hprob j) (hSeq j) k 0 -
          @normalizedKernelCosine (νSeq j) (hprob j) (hSeq j) ⌊hSeq j ^ 2⌋₊ 0| +
        |@normalizedKernelCosine (νSeq j) (hprob j) (hSeq j) ⌊hSeq j ^ 2⌋₊ 0 - 1| :=
      abs_add_le _ _
    _ ≤ (killedResidualConstant M Cq Cs * R * H) * ((NSeq j : ℝ) / hSeq j ^ 3) +
        |@normalizedKernelCosine (νSeq j) (hprob j) (hSeq j) ⌊hSeq j ^ 2⌋₊ 0 - 1| :=
      add_le_add (hfj.2 k hmk hkN) le_rfl
    _ < ε / 2 + ε / 2 := add_lt_add hD hB
    _ = ε := by ring

end Shao.OQ4.BrownianLongTimeRelativeBridge
end
