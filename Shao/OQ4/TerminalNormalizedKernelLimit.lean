-- Complete LOCAL implementation of the parent-frozen13 heads.
-- Formal freeze SHA256 bf1a80104cb1ee7812932127d7a54c274a0db7d8a3d900cc71a092b4f781fd6d.
-- All11 imports and zero new top-level values are preserved.
-- Unchecked: upstream qualification, server kernel/axioms and fresh complete review pending.
import Shao.OQ4.CosinePowers
import Shao.OQ4.KernelRecurrence
import Shao.OQ4.KilledPathLaw
import Shao.OQ4.BrownianLongTimeRelativeBridge
import Shao.OQ4.BrownianTerminalKernelBlock
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto

set_option autoImplicit false
noncomputable section
namespace Shao.OQ4.TerminalNormalizedKernelLimit
open MeasureTheory Filter Set
open RademacherScalarBounds (lambda)
open scoped NNReal Topology

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

private theorem common_moment_bound_nonneg
    (νSeq : ℕ → Measure ℝ) (M : ℝ)
    (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M) :
    0 ≤ M := by
  have hβ : 0 ≤ ∫ x : ℝ, |x| ^ 3 ∂(νSeq 0) :=
    integral_nonneg fun x => pow_nonneg (abs_nonneg x) 3
  exact hβ.trans (hM 0)

private theorem large_rate_bounds_eventually
    (νSeq : ℕ → Measure ℝ) (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (hinfty : Tendsto hSeq atTop atTop) :
    ∀ᶠ j in atTop,
      1 ≤ hSeq j ∧ Real.pi * (1 + M) ≤ hSeq j ∧
        (3 : ℝ) / 4 ≤ principalRate (νSeq j) (hSeq j) ∧
          principalRate (νSeq j) (hSeq j) < 1 := by
  have hM0 : 0 ≤ M := common_moment_bound_nonneg νSeq M hM
  filter_upwards [hinfty.eventually (eventually_ge_atTop (1 : ℝ)),
    hinfty.eventually (eventually_ge_atTop (Real.pi * (1 + M)))] with j hh1 hlarge
  letI : IsProbabilityMeasure (νSeq j) := hprob j
  rcases lower_moments_integrable (νSeq j) (h3 j) with ⟨hId, hSq⟩
  have hb := cosineCoefficient_large_h_bounds (νSeq j) M (hSeq j)
    hId hSq (h3 j) (hmean j) (hsecond j) hM0 (hM j) hh1 hlarge
  exact ⟨hh1, hlarge, hb.2.2.1, hb.2.2.2⟩

-- PUBLIC free coefficient conclusion; no S/AC or N/h^2->infinity premise.
theorem varying_row_free_cosine_rate_compensation
    (νSeq : ℕ → Measure ℝ) (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (NSeq : ℕ → ℕ) (hpos : ∀ j, 0 < hSeq j)
    (hinfty : Tendsto hSeq atTop atTop)
    (hshort : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 3)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j => principalRate (νSeq j) (hSeq j) ^ NSeq j *
      Real.exp (lambda * (NSeq j : ℝ) / hSeq j ^ 2)) atTop (𝓝 (1 : ℝ)) := by
  let D : ℝ := Real.pi ^ 3 * M / 48 + Real.pi ^ 4 / 8
  have hM0 : 0 ≤ M := common_moment_bound_nonneg νSeq M hM
  have hlarge := large_rate_bounds_eventually νSeq hprob h3 hmean hsecond M hM hSeq hinfty
  have hb : Tendsto (fun j => D * ((NSeq j : ℝ) / hSeq j ^ 3))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hshort.const_mul D
  have herror : ∀ᶠ j in atTop,
      |(NSeq j : ℝ) * Real.log (principalRate (νSeq j) (hSeq j)) +
        lambda * (NSeq j : ℝ) / hSeq j ^ 2| ≤ D * ((NSeq j : ℝ) / hSeq j ^ 3) := by
    filter_upwards [hlarge] with j hj
    letI : IsProbabilityMeasure (νSeq j) := hprob j
    rcases lower_moments_integrable (νSeq j) (h3 j) with ⟨hId, hSq⟩
    have he := cosineCoefficient_log_error_mul (νSeq j) M (hSeq j)
      hId hSq (h3 j) (hmean j) (hsecond j) hM0 (hM j) hj.1 hj.2.1 (NSeq j)
    have heq : Real.pi ^ 2 * (NSeq j : ℝ) / (8 * hSeq j ^ 2) =
        lambda * (NSeq j : ℝ) / hSeq j ^ 2 := by
      unfold lambda
      field_simp [ne_of_gt (hpos j)] <;> ring
    rw [heq] at he
    simpa only [D, principalRate, mul_div_assoc] using he
  have habs : Tendsto (fun j =>
      |(NSeq j : ℝ) * Real.log (principalRate (νSeq j) (hSeq j)) +
        lambda * (NSeq j : ℝ) / hSeq j ^ 2|) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) herror hb
  have hsum : Tendsto (fun j =>
      (NSeq j : ℝ) * Real.log (principalRate (νSeq j) (hSeq j)) +
        lambda * (NSeq j : ℝ) / hSeq j ^ 2) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq, sub_zero] using habs
  have hexp : Tendsto (fun j => Real.exp
      ((NSeq j : ℝ) * Real.log (principalRate (νSeq j) (hSeq j)) +
        lambda * (NSeq j : ℝ) / hSeq j ^ 2)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.tendsto (0 : ℝ)).comp hsum
  have heq : ∀ᶠ j in atTop,
      Real.exp ((NSeq j : ℝ) * Real.log (principalRate (νSeq j) (hSeq j)) +
        lambda * (NSeq j : ℝ) / hSeq j ^ 2) =
      principalRate (νSeq j) (hSeq j) ^ NSeq j *
        Real.exp (lambda * (NSeq j : ℝ) / hSeq j ^ 2) := by
    filter_upwards [hlarge] with j hj
    have hρ : 0 < principalRate (νSeq j) (hSeq j) := by linarith [hj.2.2.1]
    rw [Real.exp_add, ← Real.log_pow, Real.exp_log (pow_pos hρ _)]
  exact Filter.Tendsto.congr' heq hexp

private theorem floor_horizon_ratio_tendsto
    (T : ℝ≥0) (hSeq : ℕ → ℝ) (hpos : ∀ j, 0 < hSeq j)
    (hinfty : Tendsto hSeq atTop atTop) :
    Tendsto (fun j =>
      (PolygonalKilledFunctionalLimit.floorHorizon T (hSeq j) : ℝ) / hSeq j ^ 2)
      atTop (𝓝 (T : ℝ)) := by
  have hbound (j : ℕ) :
      0 ≤ (T : ℝ) -
        (PolygonalKilledFunctionalLimit.floorHorizon T (hSeq j) : ℝ) / hSeq j ^ 2 ∧
      (T : ℝ) -
        (PolygonalKilledFunctionalLimit.floorHorizon T (hSeq j) : ℝ) / hSeq j ^ 2 <
          1 / hSeq j ^ 2 := by
    dsimp only [PolygonalKilledFunctionalLimit.floorHorizon]
    have hh2 : 0 < hSeq j ^ 2 := sq_pos_of_pos (hpos j)
    have hf : (⌊(T : ℝ) * hSeq j ^ 2⌋₊ : ℝ) ≤ (T : ℝ) * hSeq j ^ 2 :=
      Nat.floor_le (mul_nonneg T.2 (sq_nonneg _))
    have hlt : (T : ℝ) * hSeq j ^ 2 <
        (⌊(T : ℝ) * hSeq j ^ 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hr : (⌊(T : ℝ) * hSeq j ^ 2⌋₊ : ℝ) / hSeq j ^ 2 ≤ (T : ℝ) :=
      (div_le_iff₀ hh2).mpr hf
    refine ⟨sub_nonneg.mpr hr, ?_⟩
    apply (lt_div_iff₀ hh2).mpr
    have heq :
        ((T : ℝ) - (⌊(T : ℝ) * hSeq j ^ 2⌋₊ : ℝ) / hSeq j ^ 2) * hSeq j ^ 2 =
          (T : ℝ) * hSeq j ^ 2 - (⌊(T : ℝ) * hSeq j ^ 2⌋₊ : ℝ) := by
      rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hh2)]
    rw [heq]
    linarith
  have hi : Tendsto (fun j => (hSeq j)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hinfty
  have hb : Tendsto (fun j => 1 / hSeq j ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div, inv_pow] using hi.pow 2
  have hz : Tendsto (fun j => (T : ℝ) -
      (PolygonalKilledFunctionalLimit.floorHorizon T (hSeq j) : ℝ) / hSeq j ^ 2)
      atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun j => (hbound j).1) (fun j => (hbound j).2.le) hb
  have ht := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (T : ℝ)) atTop (𝓝 (T : ℝ))).sub hz
  simpa only [sub_sub_cancel, sub_zero] using ht

private theorem terminal_horizon_decomposition_eventually
    (T : ℝ≥0) (hSeq : ℕ → ℝ) (NSeq : ℕ → ℕ)
    (hpos : ∀ j, 0 < hSeq j)
    (hlong : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 2) atTop atTop) :
    ∀ᶠ j in atTop,
      let L : ℕ := PolygonalKilledFunctionalLimit.floorHorizon T (hSeq j)
      L + ⌊hSeq j ^ 2⌋₊ ≤ NSeq j ∧ L ≤ NSeq j ∧
        ⌊hSeq j ^ 2⌋₊ ≤ NSeq j - L ∧ NSeq j - L ≤ NSeq j ∧
          (NSeq j - L) + L = NSeq j := by
  filter_upwards [hlong.eventually (eventually_ge_atTop ((T : ℝ) + 2))] with j hj
  let L : ℕ := PolygonalKilledFunctionalLimit.floorHorizon T (hSeq j)
  have hh2 : 0 < hSeq j ^ 2 := sq_pos_of_pos (hpos j)
  have hN : ((T : ℝ) + 2) * hSeq j ^ 2 ≤ (NSeq j : ℝ) :=
    (le_div_iff₀ hh2).mp hj
  have hLreal : (L : ℝ) ≤ (T : ℝ) * hSeq j ^ 2 :=
    Nat.floor_le (mul_nonneg T.2 (sq_nonneg _))
  have hmreal : (⌊hSeq j ^ 2⌋₊ : ℝ) ≤ hSeq j ^ 2 :=
    Nat.floor_le (sq_nonneg _)
  have hsumreal : ((L + ⌊hSeq j ^ 2⌋₊ : ℕ) : ℝ) ≤ (NSeq j : ℝ) := by
    push_cast
    nlinarith [sq_nonneg (hSeq j)]
  have hsum : L + ⌊hSeq j ^ 2⌋₊ ≤ NSeq j := by exact_mod_cast hsumreal
  have hL : L ≤ NSeq j := by omega
  change L + ⌊hSeq j ^ 2⌋₊ ≤ NSeq j ∧ L ≤ NSeq j ∧
    ⌊hSeq j ^ 2⌋₊ ≤ NSeq j - L ∧ NSeq j - L ≤ NSeq j ∧
      (NSeq j - L) + L = NSeq j
  refine ⟨hsum, hL, ?_, Nat.sub_le _ _, Nat.sub_add_cancel hL⟩
  omega

private theorem fixed_time_inverse_rate_tendsto
    (νSeq : ℕ → Measure ℝ) (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (T : ℝ≥0) (hSeq : ℕ → ℝ) (hpos : ∀ j, 0 < hSeq j)
    (hinfty : Tendsto hSeq atTop atTop) :
    Tendsto (fun j =>
      (principalRate (νSeq j) (hSeq j) ^
        PolygonalKilledFunctionalLimit.floorHorizon T (hSeq j))⁻¹)
      atTop (𝓝 (Real.exp (lambda * (T : ℝ)))) := by
  let L : ℕ → ℕ := fun j => PolygonalKilledFunctionalLimit.floorHorizon T (hSeq j)
  have hupper : Tendsto (fun j => (T : ℝ) / hSeq j) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp hinfty).const_mul (T : ℝ)
  have hshort : Tendsto (fun j => (L j : ℝ) / hSeq j ^ 3)
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero
      (fun j => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (hpos j).le 3)) ?_ hupper
    intro j
    have hf : (L j : ℝ) ≤ (T : ℝ) * hSeq j ^ 2 :=
      Nat.floor_le (mul_nonneg T.2 (sq_nonneg _))
    calc
      (L j : ℝ) / hSeq j ^ 3 ≤ ((T : ℝ) * hSeq j ^ 2) / hSeq j ^ 3 :=
        div_le_div_of_nonneg_right hf (pow_nonneg (hpos j).le 3)
      _ = (T : ℝ) / hSeq j := by field_simp [ne_of_gt (hpos j)] <;> ring
  have hcomp := varying_row_free_cosine_rate_compensation
    νSeq hprob h3 hmean hsecond M hM hSeq L hpos hinfty hshort
  have hscale : Tendsto (fun j => lambda * (L j : ℝ) / hSeq j ^ 2)
      atTop (𝓝 (lambda * (T : ℝ))) := by
    simpa only [L, mul_div_assoc] using
      (floor_horizon_ratio_tendsto T hSeq hpos hinfty).const_mul lambda
  have hexp := (Real.continuous_exp.tendsto (lambda * (T : ℝ))).comp hscale
  have hresult : Tendsto (fun j =>
      Real.exp (lambda * (L j : ℝ) / hSeq j ^ 2) *
        (principalRate (νSeq j) (hSeq j) ^ L j *
          Real.exp (lambda * (L j : ℝ) / hSeq j ^ 2))⁻¹)
      atTop (𝓝 (Real.exp (lambda * (T : ℝ)))) := by
    simpa only [Function.comp_apply, inv_one, mul_one] using
      hexp.mul (hcomp.inv₀ (by norm_num : (1 : ℝ) ≠ 0))
  have heq : ∀ᶠ j in atTop,
      Real.exp (lambda * (L j : ℝ) / hSeq j ^ 2) *
        (principalRate (νSeq j) (hSeq j) ^ L j *
          Real.exp (lambda * (L j : ℝ) / hSeq j ^ 2))⁻¹ =
      (principalRate (νSeq j) (hSeq j) ^ L j)⁻¹ := by
    filter_upwards [large_rate_bounds_eventually
      νSeq hprob h3 hmean hsecond M hM hSeq hinfty] with j hj
    have hρ : 0 < principalRate (νSeq j) (hSeq j) := by linarith [hj.2.2.1]
    have hp : principalRate (νSeq j) (hSeq j) ^ L j ≠ 0 :=
      ne_of_gt (pow_pos hρ _)
    have he : Real.exp (lambda * (L j : ℝ) / hSeq j ^ 2) ≠ 0 :=
      ne_of_gt (Real.exp_pos _)
    field_simp [hp, he] <;> ring
  exact Filter.Tendsto.congr' heq hresult

private theorem source_survival_error_bounds_of_forall
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ≥0)
    (h : ℝ) (hh : 0 ≤ h) (ε : ℝ)
    (hbound : ∀ z : ℝ, |z| ≤ h →
      |killedMass ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) z -
        BrownianUniformSurvival.brownianSurvival CanonicalBrownian.B
          CanonicalBrownian.law T (z / h)| ≤ ε) :
    0 ≤ BrownianTerminalKernelBlock.sourceSurvivalError ν T h ∧
      BrownianTerminalKernelBlock.sourceSurvivalError ν T h ≤ ε := by
  let e : ℝ → ℝ := fun z =>
    |killedMass ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) z -
      BrownianUniformSurvival.brownianSurvival CanonicalBrownian.B
        CanonicalBrownian.law T (z / h)|
  have hz0 : (0 : ℝ) ∈ Icc (-h) h := ⟨neg_nonpos.mpr hh, hh⟩
  have hne : (e '' Icc (-h) h).Nonempty := ⟨e 0, ⟨0, hz0, rfl⟩⟩
  have hb : BddAbove (e '' Icc (-h) h) := by
    refine ⟨ε, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hbound z (abs_le.mpr hz)
  change 0 ≤ sSup (e '' Icc (-h) h) ∧ sSup (e '' Icc (-h) h) ≤ ε
  constructor
  · have he0 : 0 ≤ e 0 := abs_nonneg _
    exact he0.trans (le_csSup hb ⟨0, hz0, rfl⟩)
  · apply csSup_le hne
    rintro _ ⟨z, hz, rfl⟩
    exact hbound z (abs_le.mpr hz)

private theorem varying_row_source_survival_error_tendsto
    (νSeq : ℕ → Measure ℝ) (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (T : ℝ≥0) (hT : 0 < T)
    (hSeq : ℕ → ℝ) (hpos : ∀ j, 0 < hSeq j)
    (hinfty : Tendsto hSeq atTop atTop) :
    Tendsto (fun j => @BrownianTerminalKernelBlock.sourceSurvivalError
      (νSeq j) (hprob j) T (hSeq j)) atTop (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨A, hA, hbound⟩ :=
    BrownianUniformSurvival.uniform_brownian_survival_momentClass
      CanonicalBrownian.B CanonicalBrownian.law CanonicalBrownian.isBrownianReal
      T hT M (ε / 2) (half_pos hε)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp
    (hinfty.eventually (eventually_ge_atTop A))
  refine ⟨J, ?_⟩
  intro j hj
  letI : IsProbabilityMeasure (νSeq j) := hprob j
  have hb := source_survival_error_bounds_of_forall (νSeq j) T
    (hSeq j) (hpos j).le (ε / 2)
    (fun z hz => (hbound (hSeq j) (hJ j hj) (νSeq j) (hprob j)
      (h3 j) (hmean j) (hsecond j) (hM j) z hz).le)
  have hs : BrownianTerminalKernelBlock.sourceSurvivalError (νSeq j) T (hSeq j) < ε :=
    hb.2.trans_lt (half_lt_self hε)
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hb.1] using hs

-- PUBLIC original finite normalized P2, with all n>=0 and actual error/rate.
theorem normalized_terminal_kernel_block
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ≥0) (hT : 1 ≤ T)
    (h : ℝ) (hh : 0 < h) (hρ : 0 < principalRate ν h) (n : ℕ) :
    |normalizedKernelMass ν h (n + PolygonalKilledFunctionalLimit.floorHorizon T h) 0 -
      (4 / Real.pi) * Real.exp (-lambda * (T : ℝ)) *
        (principalRate ν h ^ PolygonalKilledFunctionalLimit.floorHorizon T h)⁻¹ *
          normalizedKernelCosine ν h n 0| ≤
      (BrownianTerminalKernelBlock.sourceSurvivalError ν T h +
        BrownianTerminalSpectral.remainderC * Real.exp (-9 * lambda * (T : ℝ))) *
          (principalRate ν h ^ PolygonalKilledFunctionalLimit.floorHorizon T h)⁻¹ *
            normalizedKernelMass ν h n 0 := by
  let L : ℕ := PolygonalKilledFunctionalLimit.floorHorizon T h
  let ρ : ℝ := principalRate ν h
  let a : ℝ := (4 / Real.pi) * Real.exp (-lambda * (T : ℝ))
  let E : ℝ := BrownianTerminalKernelBlock.sourceSurvivalError ν T h +
    BrownianTerminalSpectral.remainderC * Real.exp (-9 * lambda * (T : ℝ))
  have hcos : (fun w : ℝ => Real.cos (Real.pi * w / (2 * h))) = principalCosine h := by
    funext w
    unfold principalCosine
    congr 1
    ring
  have hp := BrownianTerminalKernelBlock.terminal_kernel_block ν T hT h hh n
  rw [hcos] at hp
  change |killedMass ν h (n + L) 0 - a * kernelCosine ν h n 0| ≤
    E * killedMass ν h n 0 at hp
  have hρ0 : 0 < ρ := hρ
  have hq : 0 ≤ (ρ ^ (n + L))⁻¹ := (inv_pos.mpr (pow_pos hρ0 _)).le
  have hpow : (ρ ^ (n + L))⁻¹ = (ρ ^ L)⁻¹ * (ρ ^ n)⁻¹ := by
    rw [pow_add]
    field_simp [pow_ne_zero n (ne_of_gt hρ0), pow_ne_zero L (ne_of_gt hρ0)] <;> ring
  change |(ρ ^ (n + L))⁻¹ * killedMass ν h (n + L) 0 -
      a * (ρ ^ L)⁻¹ * ((ρ ^ n)⁻¹ * kernelCosine ν h n 0)| ≤
    E * (ρ ^ L)⁻¹ * ((ρ ^ n)⁻¹ * killedMass ν h n 0)
  calc
    _ = |(ρ ^ (n + L))⁻¹ *
        (killedMass ν h (n + L) 0 - a * kernelCosine ν h n 0)| := by
      congr 1
      rw [hpow]
      ring
    _ = (ρ ^ (n + L))⁻¹ *
        |killedMass ν h (n + L) 0 - a * kernelCosine ν h n 0| := by
      rw [abs_mul, abs_of_nonneg hq]
    _ ≤ (ρ ^ (n + L))⁻¹ * (E * killedMass ν h n 0) :=
      mul_le_mul_of_nonneg_left hp hq
    _ = _ := by rw [hpow]; ring

private theorem terminal_tail_small
    (H ε : ℝ) (hH : 0 < H) (hε : 0 < ε) :
    ∃ T : ℝ≥0, 1 ≤ T ∧
      2 * H * BrownianTerminalSpectral.remainderC *
        Real.exp (-8 * lambda * (T : ℝ)) < ε / 3 := by
  let C : ℝ := BrownianTerminalSpectral.remainderC
  have hC : 0 < C := BrownianTerminalSpectral.remainderC_pos
  have hLambda : 0 < lambda := by unfold lambda; positivity
  let D : ℝ := 6 * H * C / ε
  have hD : 0 < D := by dsimp only [D]; positivity
  let t : ℝ := max 1 (Real.log D / (8 * lambda) + 1)
  have ht1 : 1 ≤ t := le_max_left _ _
  have hqt : Real.log D / (8 * lambda) < t := by
    have hm : Real.log D / (8 * lambda) + 1 ≤ t := le_max_right _ _
    linarith
  let T : ℝ≥0 := ⟨t, (by linarith : 0 ≤ t)⟩
  refine ⟨T, ?_, ?_⟩
  · exact_mod_cast ht1
  · have hden : 0 < 8 * lambda := by positivity
    have hmul : Real.log D < t * (8 * lambda) := (div_lt_iff₀ hden).mp hqt
    have hx : -8 * lambda * t < -Real.log D := by nlinarith
    have he : Real.exp (-8 * lambda * t) < D⁻¹ := by
      calc
        _ < Real.exp (-Real.log D) := Real.exp_lt_exp.mpr hx
        _ = D⁻¹ := by rw [Real.exp_neg, Real.exp_log hD]
    have hf : 2 * H * C * Real.exp (-8 * lambda * t) < 2 * H * C * D⁻¹ :=
      mul_lt_mul_of_pos_left he (by positivity)
    have hid : 2 * H * C * D⁻¹ = ε / 3 := by
      dsimp only [D]
      field_simp [ne_of_gt hε, ne_of_gt hH, ne_of_gt hC] <;> ring
    change 2 * H * C * Real.exp (-8 * lambda * t) < ε / 3
    exact hf.trans_eq hid

-- PUBLIC full common-M varying-row normalized limit; actual S/AC stay explicit.
theorem varying_row_normalized_kernel_mass_tendsto
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
    Tendsto (fun j => @normalizedKernelMass (νSeq j) (hprob j) (hSeq j) (NSeq j) 0)
      atTop (𝓝 (4 / Real.pi)) := by
  let R : ℝ := Real.exp (Real.pi ^ 2)
  let H : ℝ := 2 * (1 + (2 * Cs) * R) * R
  have hbridge := BrownianLongTimeRelativeBridge.varying_row_long_time_relative_bridge
    νSeq hprob h3 hmean hsecond M hM Cq Cs hCq hCs hAC hS
    hSeq NSeq hpos hinfty hlong hshort
  change 0 < H ∧
    (∀ᶠ j in atTop, ∀ k : ℕ, k ≤ NSeq j →
      0 ≤ @normalizedKernelMass (νSeq j) (hprob j) (hSeq j) k 0 ∧
        @normalizedKernelMass (νSeq j) (hprob j) (hSeq j) k 0 ≤ H) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      ∀ k : ℕ, ⌊hSeq j ^ 2⌋₊ ≤ k → k ≤ NSeq j →
        |@normalizedKernelCosine (νSeq j) (hprob j) (hSeq j) k 0 - 1| < ε) at hbridge
  rcases hbridge with ⟨hH, hmass, hcos⟩
  have hlarge := large_rate_bounds_eventually νSeq hprob h3 hmean hsecond M hM hSeq hinfty
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨T, hT, htail⟩ := terminal_tail_small H ε hH hε
  let L : ℕ → ℕ := fun j => PolygonalKilledFunctionalLimit.floorHorizon T (hSeq j)
  let n : ℕ → ℕ := fun j => NSeq j - L j
  let r : ℕ → ℝ := fun j => (principalRate (νSeq j) (hSeq j) ^ L j)⁻¹
  let E : ℕ → ℝ := fun j =>
    @BrownianTerminalKernelBlock.sourceSurvivalError (νSeq j) (hprob j) T (hSeq j)
  let f : ℕ → ℝ := fun j =>
    @normalizedKernelCosine (νSeq j) (hprob j) (hSeq j) (n j) 0
  let g : ℕ → ℝ := fun j =>
    @normalizedKernelMass (νSeq j) (hprob j) (hSeq j) (n j) 0
  let a : ℝ := (4 / Real.pi) * Real.exp (-lambda * (T : ℝ))
  let b : ℝ := Real.exp (lambda * (T : ℝ))
  let C : ℝ := BrownianTerminalSpectral.remainderC
  have hb : 0 < b := Real.exp_pos _
  have hC : 0 < C := BrownianTerminalSpectral.remainderC_pos
  have hrange : ∀ᶠ j in atTop,
      ⌊hSeq j ^ 2⌋₊ ≤ n j ∧ n j ≤ NSeq j ∧ n j + L j = NSeq j := by
    filter_upwards [terminal_horizon_decomposition_eventually T hSeq NSeq hpos hlong] with j hj
    change L j + ⌊hSeq j ^ 2⌋₊ ≤ NSeq j ∧ L j ≤ NSeq j ∧
      ⌊hSeq j ^ 2⌋₊ ≤ n j ∧ n j ≤ NSeq j ∧ n j + L j = NSeq j at hj
    exact ⟨hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2⟩
  have hf : Tendsto f atTop (𝓝 (1 : ℝ)) := by
    apply Metric.tendsto_atTop.mpr
    intro δ hδ
    have hev : ∀ᶠ j in atTop, |f j - 1| < δ := by
      filter_upwards [hrange, hcos δ hδ] with j hj hcj
      exact hcj (n j) hj.1 hj.2.1
    obtain ⟨J, hJ⟩ := eventually_atTop.mp hev
    refine ⟨J, ?_⟩
    intro j hj
    simpa only [Real.dist_eq] using hJ j hj
  have hr : Tendsto r atTop (𝓝 b) :=
    fixed_time_inverse_rate_tendsto νSeq hprob h3 hmean hsecond M hM T hSeq hpos hinfty
  have hElimit : Tendsto E atTop (𝓝 (0 : ℝ)) :=
    varying_row_source_survival_error_tendsto νSeq hprob h3 hmean hsecond M hM
      T (lt_of_lt_of_le zero_lt_one hT) hSeq hpos hinfty
  have hE0 (j : ℕ) : 0 ≤ E j := by
    letI : IsProbabilityMeasure (νSeq j) := hprob j
    apply (source_survival_error_bounds_of_forall (νSeq j) T (hSeq j) (hpos j).le 1 ?_).1
    intro z _hz
    have hk0 := killedMass_nonneg (νSeq j) (hSeq j)
      (PolygonalKilledFunctionalLimit.floorHorizon T (hSeq j)) z
    have hk1 := killedMass_le_one (νSeq j) (hSeq j)
      (PolygonalKilledFunctionalLimit.floorHorizon T (hSeq j)) z
    have hg0 : 0 ≤ BrownianUniformSurvival.brownianSurvival CanonicalBrownian.B
        CanonicalBrownian.law T (z / hSeq j) := measureReal_nonneg
    have hg1 : BrownianUniformSurvival.brownianSurvival CanonicalBrownian.B
        CanonicalBrownian.law T (z / hSeq j) ≤ 1 := measureReal_le_one
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hab : a * b = 4 / Real.pi := by
    have hex : Real.exp (-lambda * (T : ℝ)) * Real.exp (lambda * (T : ℝ)) = 1 := by
      rw [← Real.exp_add]
      have hz : -lambda * (T : ℝ) + lambda * (T : ℝ) = 0 := by ring
      rw [hz, Real.exp_zero]
    dsimp only [a, b]
    rw [mul_assoc, hex, mul_one]
  have hp : Tendsto (fun j => a * r j * f j) atTop (𝓝 (4 / Real.pi)) := by
    simpa only [hab, mul_one] using (hr.const_mul a).mul hf
  have hrsmall : ∀ᶠ j in atTop, r j < 2 * b :=
    hr.eventually (Iio_mem_nhds (by linarith : b < 2 * b))
  let δ : ℝ := ε / (6 * H * b)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hEsmall : ∀ᶠ j in atTop, E j < δ :=
    hElimit.eventually (Iio_mem_nhds hδ)
  obtain ⟨Jp, hJp⟩ := (Metric.tendsto_atTop.mp hp) (ε / 3) (by positivity)
  have hpSmall : ∀ᶠ j in atTop, |a * r j * f j - 4 / Real.pi| < ε / 3 := by
    filter_upwards [eventually_ge_atTop Jp] with j hj
    simpa only [Real.dist_eq] using hJp j hj
  have hgmass : ∀ᶠ j in atTop, 0 ≤ g j ∧ g j ≤ H := by
    filter_upwards [hmass, hrange] with j hj hrj
    exact hj (n j) hrj.2.1
  have hfinal : ∀ᶠ j in atTop,
      |@normalizedKernelMass (νSeq j) (hprob j) (hSeq j) (NSeq j) 0 - 4 / Real.pi| < ε := by
    filter_upwards [hlarge, hrange, hrsmall, hEsmall, hpSmall, hgmass]
      with j hlj hnj hrj hEj hpj hgj
    letI : IsProbabilityMeasure (νSeq j) := hprob j
    have hρ : 0 < principalRate (νSeq j) (hSeq j) := by linarith [hlj.2.2.1]
    have hP2 := normalized_terminal_kernel_block
      (νSeq j) T hT (hSeq j) (hpos j) hρ (n j)
    change |@normalizedKernelMass (νSeq j) (hprob j) (hSeq j) (n j + L j) 0 -
        a * r j * f j| ≤
      (E j + C * Real.exp (-9 * lambda * (T : ℝ))) * r j * g j at hP2
    rw [hnj.2.2] at hP2
    have hrg : r j * g j ≤ 2 * b * H := by
      calc
        _ ≤ (2 * b) * g j := mul_le_mul_of_nonneg_right hrj.le hgj.1
        _ ≤ (2 * b) * H := mul_le_mul_of_nonneg_left hgj.2 (by positivity)
    have hsmallE : E j * r j * g j < ε / 3 := by
      calc
        _ = E j * (r j * g j) := by ring
        _ ≤ E j * (2 * b * H) := mul_le_mul_of_nonneg_left hrg (hE0 j)
        _ < δ * (2 * b * H) := mul_lt_mul_of_pos_right hEj (by positivity)
        _ = ε / 3 := by
          dsimp only [δ]
          field_simp [ne_of_gt hH, ne_of_gt hb] <;> ring
    have hsmallTail : (C * Real.exp (-9 * lambda * (T : ℝ))) * r j * g j < ε / 3 := by
      calc
        _ = (C * Real.exp (-9 * lambda * (T : ℝ))) * (r j * g j) := by ring
        _ ≤ (C * Real.exp (-9 * lambda * (T : ℝ))) * (2 * b * H) :=
          mul_le_mul_of_nonneg_left hrg (by positivity)
        _ = 2 * H * C *
            (Real.exp (-9 * lambda * (T : ℝ)) * Real.exp (lambda * (T : ℝ))) := by
          dsimp only [b]
          ring
        _ = 2 * H * C * Real.exp (-8 * lambda * (T : ℝ)) := by
          rw [← Real.exp_add]
          have hx : -9 * lambda * (T : ℝ) + lambda * (T : ℝ) =
              -8 * lambda * (T : ℝ) := by ring
          rw [hx]
        _ < ε / 3 := htail
    calc
      |@normalizedKernelMass (νSeq j) (hprob j) (hSeq j) (NSeq j) 0 - 4 / Real.pi| =
          |(@normalizedKernelMass (νSeq j) (hprob j) (hSeq j) (NSeq j) 0 -
            a * r j * f j) + (a * r j * f j - 4 / Real.pi)| := by
        congr 1
        ring
      _ ≤ |@normalizedKernelMass (νSeq j) (hprob j) (hSeq j) (NSeq j) 0 -
            a * r j * f j| + |a * r j * f j - 4 / Real.pi| := abs_add_le _ _
      _ ≤ (E j + C * Real.exp (-9 * lambda * (T : ℝ))) * r j * g j +
          |a * r j * f j - 4 / Real.pi| := add_le_add hP2 (le_refl _)
      _ = E j * r j * g j + (C * Real.exp (-9 * lambda * (T : ℝ))) * r j * g j +
          |a * r j * f j - 4 / Real.pi| := by ring
      _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add hsmallE hsmallTail) hpj
      _ = ε := by ring
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hfinal
  refine ⟨J, ?_⟩
  intro j hj
  simpa only [Real.dist_eq] using hJ j hj

-- PUBLIC actual finite-product closed-strip probability version of conditional K.
-- Every primitive assumption is repeated literally; no supplied normalized limit.
theorem varying_row_closedStrip_relative_asymptotic
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
    Tendsto (fun j =>
      (Measure.pi (fun _ : Fin (NSeq j) => νSeq j)).real
        (@Shao.closedStrip (NSeq j) (hSeq j)) /
          ((4 / Real.pi) * Real.exp (-lambda * (NSeq j : ℝ) / hSeq j ^ 2)))
      atTop (𝓝 (1 : ℝ)) := by
  have hnorm := varying_row_normalized_kernel_mass_tendsto
    νSeq hprob h3 hmean hsecond M hM Cq Cs hCq hCs hAC hS
    hSeq NSeq hpos hinfty hlong hshort
  have hcomp := varying_row_free_cosine_rate_compensation
    νSeq hprob h3 hmean hsecond M hM hSeq NSeq hpos hinfty hshort
  have ha : (4 / Real.pi : ℝ) ≠ 0 := ne_of_gt (div_pos (by norm_num) Real.pi_pos)
  have hlim : Tendsto (fun j =>
      @normalizedKernelMass (νSeq j) (hprob j) (hSeq j) (NSeq j) 0 *
        (principalRate (νSeq j) (hSeq j) ^ NSeq j *
          Real.exp (lambda * (NSeq j : ℝ) / hSeq j ^ 2)) / (4 / Real.pi))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_one, div_self ha] using
      (hnorm.mul hcomp).div_const (4 / Real.pi : ℝ)
  have heq : ∀ᶠ j in atTop,
      @normalizedKernelMass (νSeq j) (hprob j) (hSeq j) (NSeq j) 0 *
        (principalRate (νSeq j) (hSeq j) ^ NSeq j *
          Real.exp (lambda * (NSeq j : ℝ) / hSeq j ^ 2)) / (4 / Real.pi) =
      (Measure.pi (fun _ : Fin (NSeq j) => νSeq j)).real
        (@Shao.closedStrip (NSeq j) (hSeq j)) /
          ((4 / Real.pi) * Real.exp (-lambda * (NSeq j : ℝ) / hSeq j ^ 2)) := by
    filter_upwards [large_rate_bounds_eventually
      νSeq hprob h3 hmean hsecond M hM hSeq hinfty] with j hj
    letI : IsProbabilityMeasure (νSeq j) := hprob j
    have hρ : 0 < principalRate (νSeq j) (hSeq j) := by linarith [hj.2.2.1]
    have hp : principalRate (νSeq j) (hSeq j) ^ NSeq j ≠ 0 :=
      ne_of_gt (pow_pos hρ _)
    have he : Real.exp (lambda * (NSeq j : ℝ) / hSeq j ^ 2) ≠ 0 :=
      ne_of_gt (Real.exp_pos _)
    have hpath := killedMass_eq_closedStrip_probability
      (νSeq j) (NSeq j) (hSeq j) (hpos j).le
    rw [← hpath]
    unfold normalizedKernelMass
    have hneg : -lambda * (NSeq j : ℝ) / hSeq j ^ 2 =
        -(lambda * (NSeq j : ℝ) / hSeq j ^ 2) := by ring
    rw [hneg, Real.exp_neg]
    field_simp [hp, ha, he] <;> ring
  exact Filter.Tendsto.congr' heq hlim

end Shao.OQ4.TerminalNormalizedKernelLimit
end
