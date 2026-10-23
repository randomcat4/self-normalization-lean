-- AUTHOR175 LOCAL IMPLEMENTATION ONLY: parent-frozen, NOT Lean/kernel checked.
-- Proposed production file: Shao/OQ4/UniformConditionalEnergy.lean
-- Proposed module: Shao.OQ4.UniformConditionalEnergy
-- EXHAUSTIVE source inventory: 8 imports; 1 option; 1 transparent def;
-- 9 private theorem heads; 5 public theorem heads.
-- ZERO additional abbrev/opaque/structure/class/instance/notation/macro/axiom.
-- No new universe variables. All instance binders below use existing instances.
-- All unlisted helpers must remain proof-local or be submitted for a new freeze.

import Shao.OQ4.EnergyJointTransport
import Shao.OQ4.UnconditionalKernelAsymptotic
import Shao.OQ4.ConditionalEnergyConcentration
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
noncomputable section
namespace Shao.OQ4.UniformConditionalEnergy

open MeasureTheory Filter Set
open RademacherScalarBounds (lambda)
open scoped Topology

-- VALUE 1, FULL transparent value. This is the actual finite-product integral.
-- The exp-pair is exactly cosh(y)-1; no abstract conditional value is substituted.
noncomputable def energyCoshExcessIntegral
    (ν : Measure ℝ) (n : ℕ) (b h s : ℝ) : ℝ := by
  classical
  exact ∫ a : Shao.Path n,
    (if a ∈ (@Shao.closedStrip n b) then
      (Real.exp (s * (Shao.energy a - (n : ℝ)) / h ^ 2) +
        Real.exp (-(s * (Shao.energy a - (n : ℝ)) / h ^ 2))) / 2 - 1
    else 0) ∂Measure.pi (fun _ : Fin n => ν)

-- PRIVATE 1: pays nonnegativity, evenness and monotonicity for negative y too.
private theorem exp_pair_mono_abs
    (u v : ℝ) (huv : |u| ≤ |v|) :
    0 ≤ (Real.exp u + Real.exp (-u)) / 2 - 1 ∧
      (Real.exp u + Real.exp (-u)) / 2 - 1 ≤
        (Real.exp v + Real.exp (-v)) / 2 - 1 := by
  have hnonneg (x : ℝ) : 0 ≤ (Real.exp x + Real.exp (-x)) / 2 - 1 := by
    nlinarith [Real.add_one_le_exp x, Real.add_one_le_exp (-x)]
  have heven (x : ℝ) :
      Real.exp x + Real.exp (-x) = Real.exp |x| + Real.exp (-|x|) := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, neg_neg]
      ring
  refine ⟨hnonneg u, ?_⟩
  rw [heven u, heven v]
  let a : ℝ := Real.exp (|v| - |u|)
  have ha : 1 ≤ a := by
    dsimp only [a]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (sub_nonneg.mpr huv)
  have hright : 0 ≤ Real.exp |u| - Real.exp (-|v|) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    linarith [abs_nonneg u, abs_nonneg v]
  have hv : Real.exp |v| = Real.exp |u| * a := by
    dsimp only [a]
    rw [← Real.exp_add]
    congr 1
    ring
  have hu : Real.exp (-|u|) = Real.exp (-|v|) * a := by
    dsimp only [a]
    rw [← Real.exp_add]
    congr 1
    ring
  have hp := mul_nonneg (sub_nonneg.mpr ha) hright
  rw [hv, hu]
  nlinarith

-- PRIVATE 2: the strictly positive finite Markov denominator.
private theorem exp_pair_strict_pos
    (u : ℝ) (hu : 0 < u) :
    0 < (Real.exp u + Real.exp (-u)) / 2 - 1 := by
  have hp : u + 1 < Real.exp u := Real.add_one_lt_exp (ne_of_gt hu)
  nlinarith [Real.add_one_le_exp (-u)]

-- PRIVATE 3: extends the old finite integrability head from 1≤b to 0<b.
-- This finite fact uses strip coordinate bounds, no moments or exponential MGF.
private theorem energyPathIntegrand_integrable_pos
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (b u : ℝ) (hb : 0 < b) :
    Integrable (energyPathIntegrand (n := n) b u)
      (Measure.pi (fun _ : Fin n => ν)) := by
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  let B : ℝ := |u| * (4 * (n : ℝ) + (n : ℝ) / b ^ 2)
  have hbound (a : Shao.Path n) :
      ‖energyPathIntegrand b u a‖ ≤ Real.exp B := by
    rw [Real.norm_eq_abs]
    by_cases ha : a ∈ Shao.closedStrip b
    · have hQ : Shao.energy a ≤ 4 * (n : ℝ) * b ^ 2 := by
        calc
          _ ≤ Finset.sum Finset.univ (fun _i : Fin n => 4 * b ^ 2) := by
            apply Finset.sum_le_sum
            intro i _
            have hi := Shao.abs_coordinate_le_two_mul_of_mem_closedStrip a b ha i
            have hi2 := pow_le_pow_left₀ (abs_nonneg (a i)) hi 2
            nlinarith [sq_abs (a i)]
          _ = _ := by simp; ring
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hQabs : |Shao.energy a - (n : ℝ)| ≤ 4 * (n : ℝ) * b ^ 2 + (n : ℝ) := by
        apply abs_le.mpr
        constructor
        · nlinarith [Shao.energy_nonneg a, sq_nonneg b]
        · linarith
      have harg : u * (Shao.energy a - (n : ℝ)) / b ^ 2 ≤ B := by
        calc
          _ ≤ |u * (Shao.energy a - (n : ℝ)) / b ^ 2| := le_abs_self _
          _ = |u| * (|Shao.energy a - (n : ℝ)| / b ^ 2) := by
            rw [abs_div, abs_mul, abs_of_pos hb2]
            ring
          _ ≤ |u| * ((4 * (n : ℝ) * b ^ 2 + (n : ℝ)) / b ^ 2) :=
            mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right hQabs hb2.le) (abs_nonneg u)
          _ = B := by
            dsimp only [B]
            field_simp [hb.ne']
            <;> ring
      rw [energyPathIntegrand, if_pos ha, Real.abs_exp]
      exact Real.exp_le_exp.mpr harg
    · simp only [energyPathIntegrand, if_neg ha, abs_zero]
      exact Real.exp_nonneg B
  exact (integrable_const (Real.exp B)).mono'
    (energyPathIntegrand_measurable b u hb.le).aestronglyMeasurable
    (Eventually.of_forall hbound)

-- PRIVATE 4: literal cancellation and integral linearity after integrability.
open scoped Classical in
private theorem energyCoshExcess_integrable_identity
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (b h s : ℝ) (hb : 0 < b) (hh : 0 < h) :
    Integrable (fun a : Shao.Path n =>
      if a ∈ (@Shao.closedStrip n b) then
        (Real.exp (s * (Shao.energy a - (n : ℝ)) / h ^ 2) +
          Real.exp (-(s * (Shao.energy a - (n : ℝ)) / h ^ 2))) / 2 - 1
      else 0) (Measure.pi (fun _ : Fin n => ν)) ∧
      energyCoshExcessIntegral ν n b h s =
        (energyJointIntegral ν n b (s * (b / h) ^ 2) +
          energyJointIntegral ν n b (-(s * (b / h) ^ 2))) / 2 -
          (Measure.pi (fun _ : Fin n => ν)).real (@Shao.closedStrip n b) := by
  classical
  let μ : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ν)
  let A : Set (Shao.Path n) := Shao.closedStrip b
  let IA : Shao.Path n → ℝ := A.indicator (fun _ => 1)
  let u : ℝ := s * (b / h) ^ 2
  let f : Shao.Path n → ℝ := fun a =>
    if a ∈ A then
      (Real.exp (s * (Shao.energy a - (n : ℝ)) / h ^ 2) +
        Real.exp (-(s * (Shao.energy a - (n : ℝ)) / h ^ 2))) / 2 - 1
    else 0
  have hA : MeasurableSet A := by
    dsimp only [A]
    rw [← shiftedClosedSurvival_eq_closedStrip n b hb.le]
    exact measurableSet_shiftedClosedSurvival n b 0
  have hiA : Integrable IA μ := (integrable_const (1 : ℝ)).indicator hA
  have hiP : Integrable (energyPathIntegrand (n := n) b u) μ :=
    energyPathIntegrand_integrable_pos ν n b u hb
  have hiM : Integrable (energyPathIntegrand (n := n) b (-u)) μ :=
    energyPathIntegrand_integrable_pos ν n b (-u) hb
  have hscale (q : ℝ) : u * q / b ^ 2 = s * q / h ^ 2 := by
    dsimp only [u]
    field_simp [hb.ne', hh.ne']
    <;> ring
  have hscaleNeg (q : ℝ) : (-u) * q / b ^ 2 = -(s * q / h ^ 2) := by
    rw [neg_mul, neg_div, hscale]
  have hpoint (a : Shao.Path n) :
      f a = (energyPathIntegrand b u a + energyPathIntegrand b (-u) a) / 2 - IA a := by
    by_cases ha : a ∈ A
    · have ha' : a ∈ Shao.closedStrip b := ha
      simp only [f, if_pos ha, energyPathIntegrand, if_pos ha',
        hscale, hscaleNeg, IA, Set.indicator_of_mem ha]
    · have ha' : a ∉ Shao.closedStrip b := ha
      simp [f, ha, energyPathIntegrand, ha', IA]
  have hif : Integrable f μ :=
    (((hiP.add hiM).div_const 2).sub hiA).congr
      (Eventually.of_forall fun a => (hpoint a).symm)
  have hIA : (∫ a, IA a ∂μ) = μ.real A := by
    simpa only [IA, measureReal_def, show (1 : Shao.Path n → ℝ) = (fun _ => 1) from rfl] using
      (integral_indicator_one (μ := μ) hA)
  refine ⟨hif, ?_⟩
  have hJ : energyCoshExcessIntegral ν n b h s =
      ∫ a, (energyPathIntegrand b u a + energyPathIntegrand b (-u) a) / 2 - IA a ∂μ := by
    change (∫ a, f a ∂μ) = _
    exact integral_congr_ae (Eventually.of_forall hpoint)
  have hiSum : Integrable (fun a => energyPathIntegrand b u a +
      energyPathIntegrand b (-u) a) μ := hiP.add hiM
  have hiDiv : Integrable (fun a => (energyPathIntegrand b u a +
      energyPathIntegrand b (-u) a) / 2) μ := hiSum.div_const 2
  have hdiv : (fun a : Shao.Path n =>
      (energyPathIntegrand b u a + energyPathIntegrand b (-u) a) / 2) =
      (fun a => (2 : ℝ)⁻¹ * (energyPathIntegrand b u a + energyPathIntegrand b (-u) a)) := by
    funext a
    ring
  rw [hJ, integral_sub hiDiv hiA, hdiv, integral_const_mul, integral_add hiP hiM, hIA]
  dsimp only [u, energyJointIntegral, μ, A]
  ring

-- PUBLIC 1: nonnegativity is valid even at early zero/nonpositive heights.
theorem energyCoshExcessIntegral_nonneg
    (ν : Measure ℝ) (n : ℕ) (b h s : ℝ) :
    0 ≤ energyCoshExcessIntegral ν n b h s := by
  unfold energyCoshExcessIntegral
  apply integral_nonneg
  intro a
  dsimp only [Pi.zero_apply]
  split_ifs
  · exact (exp_pair_mono_abs
      (s * (Shao.energy a - (n : ℝ)) / h ^ 2)
      (s * (Shao.energy a - (n : ℝ)) / h ^ 2) le_rfl).1
  · exact le_rfl

-- PRIVATE 5: two FIXED Laplace parameters ±s*C² dominate every moving radius.
private theorem energyCoshExcess_le_fixed
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (b h s C : ℝ)
    (hb : 0 < b) (hh : 0 < h) (hs : 0 < s)
    (hC : 1 ≤ C) (hbh : b ≤ C * h) :
    energyCoshExcessIntegral ν n b h s ≤
      (energyJointIntegral ν n b (s * C ^ 2) +
        energyJointIntegral ν n b (-(s * C ^ 2))) / 2 -
        (Measure.pi (fun _ : Fin n => ν)).real (@Shao.closedStrip n b) := by
  classical
  obtain ⟨hiL, _⟩ := energyCoshExcess_integrable_identity ν n b h s hb hh
  obtain ⟨hiR, hR⟩ := energyCoshExcess_integrable_identity ν n b b (s * C ^ 2) hb hb
  have hbc0 : 0 ≤ b / h := div_nonneg hb.le hh.le
  have hbc : b / h ≤ C := (div_le_iff₀ hh).mpr hbh
  have hbc2 : (b / h) ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ hbc0 hbc 2
  have hpoint (a : Shao.Path n) :
      (if a ∈ (@Shao.closedStrip n b) then
        (Real.exp (s * (Shao.energy a - (n : ℝ)) / h ^ 2) +
          Real.exp (-(s * (Shao.energy a - (n : ℝ)) / h ^ 2))) / 2 - 1 else 0) ≤
      (if a ∈ (@Shao.closedStrip n b) then
        (Real.exp ((s * C ^ 2) * (Shao.energy a - (n : ℝ)) / b ^ 2) +
          Real.exp (-((s * C ^ 2) * (Shao.energy a - (n : ℝ)) / b ^ 2))) / 2 - 1 else 0) := by
    by_cases ha : a ∈ (@Shao.closedStrip n b)
    · simp only [if_pos ha]
      apply (exp_pair_mono_abs _ _ ?_).2
      have hscale : s * (Shao.energy a - (n : ℝ)) / h ^ 2 =
          (s * (b / h) ^ 2) * ((Shao.energy a - (n : ℝ)) / b ^ 2) := by
        field_simp [hb.ne', hh.ne']
        <;> ring
      rw [hscale]
      have hright : (s * C ^ 2) * (Shao.energy a - (n : ℝ)) / b ^ 2 =
          (s * C ^ 2) * ((Shao.energy a - (n : ℝ)) / b ^ 2) := by ring
      rw [hright]
      simpa only [abs_mul, abs_of_nonneg hs.le,
        abs_of_nonneg (sq_nonneg (b / h)), abs_of_nonneg (sq_nonneg C)] using
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbc2 hs.le)
          (abs_nonneg ((Shao.energy a - (n : ℝ)) / b ^ 2))
    · simp only [if_neg ha, le_refl]
  have hJ : energyCoshExcessIntegral ν n b h s ≤
      energyCoshExcessIntegral ν n b b (s * C ^ 2) := integral_mono hiL hiR hpoint
  have hR' : energyCoshExcessIntegral ν n b b (s * C ^ 2) =
      (energyJointIntegral ν n b (s * C ^ 2) +
        energyJointIntegral ν n b (-(s * C ^ 2))) / 2 -
        (Measure.pi (fun _ : Fin n => ν)).real (@Shao.closedStrip n b) := by
    simpa only [div_self hb.ne', one_pow, mul_one] using hR
  exact hJ.trans_eq hR'

-- PUBLIC 2: finite literal strict-deviation/closed-wall Markov inequality.
-- No positive-survival premise and no moment premise are introduced.
theorem energy_deviation_finite_bound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (b h s ε : ℝ)
    (hb : 0 < b) (hh : 0 < h) (hs : 0 < s) (hε : 0 < ε) :
    0 < (Real.exp (s * ε) + Real.exp (-(s * ε))) / 2 - 1 ∧
      ((Real.exp (s * ε) + Real.exp (-(s * ε))) / 2 - 1) *
        (Measure.pi (fun _ : Fin n => ν)).real
          ((@Shao.closedStrip n b) ∩
            {a : Shao.Path n | ε * h ^ 2 < |Shao.energy a - (n : ℝ)|}) ≤
        energyCoshExcessIntegral ν n b h s := by
  classical
  let μ : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ν)
  let A : Set (Shao.Path n) := Shao.closedStrip b
  let B : Set (Shao.Path n) :=
    A ∩ {a | ε * h ^ 2 < |Shao.energy a - (n : ℝ)|}
  let IB : Shao.Path n → ℝ := B.indicator (fun _ => 1)
  let D : ℝ := (Real.exp (s * ε) + Real.exp (-(s * ε))) / 2 - 1
  have hD : 0 < D := exp_pair_strict_pos (s * ε) (mul_pos hs hε)
  have hA : MeasurableSet A := by
    dsimp only [A]
    rw [← shiftedClosedSurvival_eq_closedStrip n b hb.le]
    exact measurableSet_shiftedClosedSurvival n b 0
  have hE : Measurable (fun a : Shao.Path n => Shao.energy a - (n : ℝ)) :=
    Shao.measurable_energy.sub_const (n : ℝ)
  have hEabs : Measurable (fun a : Shao.Path n => |Shao.energy a - (n : ℝ)|) := by
    fun_prop
  have hB : MeasurableSet B :=
    hA.inter (measurableSet_lt measurable_const hEabs)
  have hiB : Integrable IB μ := (integrable_const (1 : ℝ)).indicator hB
  have hIB : (∫ a, IB a ∂μ) = μ.real B := by
    simpa only [IB, measureReal_def, show (1 : Shao.Path n → ℝ) = (fun _ => 1) from rfl] using
      (integral_indicator_one (μ := μ) hB)
  have hiJ := (energyCoshExcess_integrable_identity ν n b h s hb hh).1
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
  have hpoint (a : Shao.Path n) : D * IB a ≤
      (if a ∈ (@Shao.closedStrip n b) then
        (Real.exp (s * (Shao.energy a - (n : ℝ)) / h ^ 2) +
          Real.exp (-(s * (Shao.energy a - (n : ℝ)) / h ^ 2))) / 2 - 1
      else 0) := by
    by_cases haB : a ∈ B
    · have ha : a ∈ (@Shao.closedStrip n b) := haB.1
      have hdev : ε * h ^ 2 < |Shao.energy a - (n : ℝ)| := haB.2
      have harg : s * ε ≤ |s * (Shao.energy a - (n : ℝ)) / h ^ 2| := by
        rw [abs_div, abs_mul, abs_of_pos hs, abs_of_pos hh2]
        apply (le_div_iff₀ hh2).mpr
        have hm := mul_le_mul_of_nonneg_left hdev.le hs.le
        nlinarith
      have hm := (exp_pair_mono_abs (s * ε)
        (s * (Shao.energy a - (n : ℝ)) / h ^ 2)
        (by simpa only [abs_of_pos (mul_pos hs hε)] using harg)).2
      simpa only [IB, Set.indicator_of_mem haB, mul_one, if_pos ha, D] using hm
    · have hIB0 : IB a = 0 := by simp only [IB, Set.indicator_of_notMem haB]
      rw [hIB0, mul_zero]
      split_ifs
      · exact (exp_pair_mono_abs
          (s * (Shao.energy a - (n : ℝ)) / h ^ 2)
          (s * (Shao.energy a - (n : ℝ)) / h ^ 2) le_rfl).1
      · exact le_rfl
  have hm := integral_mono (hiB.const_mul D) hiJ hpoint
  rw [integral_const_mul, hIB] at hm
  refine ⟨hD, ?_⟩
  simpa only [D, B, A, μ, energyCoshExcessIntegral] using hm

-- PRIVATE 6: original tail scales survive every eventually selected radius.
private theorem selected_radius_scales
    (h : ℕ → ℝ) (n : ℕ → ℕ) (b : ℕ → ℝ)
    (C : ℝ) (hC : 1 ≤ C)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 (0 : ℝ)))
    (hb : ∀ᶠ j in atTop, h j / 2 ≤ b j ∧ b j ≤ C * h j) :
    Tendsto b atTop atTop ∧
      Tendsto (fun j => (n j : ℝ) / b j ^ 2) atTop atTop ∧
      Tendsto (fun j => (n j : ℝ) / b j ^ 3) atTop (𝓝 (0 : ℝ)) := by
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hpos : ∀ᶠ j in atTop, 0 < h j := hinfty.eventually_gt_atTop 0
  have hhalf : Tendsto (fun j => h j / 2) atTop atTop :=
    (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr hinfty
  have hbInf : Tendsto b atTop atTop :=
    tendsto_atTop_mono' atTop (hb.mono fun _ hj => hj.1) hhalf
  have hlongLower : Tendsto (fun j => ((n j : ℝ) / h j ^ 2) / C ^ 2) atTop atTop :=
    (tendsto_div_const_atTop_of_pos (sq_pos_of_pos hCpos)).mpr hlong
  have hlongBound : ∀ᶠ j in atTop,
      ((n j : ℝ) / h j ^ 2) / C ^ 2 ≤ (n j : ℝ) / b j ^ 2 := by
    filter_upwards [hb, hpos] with j hj hh
    have hbj : 0 < b j := lt_of_lt_of_le (half_pos hh) hj.1
    have hden : b j ^ 2 ≤ C ^ 2 * h j ^ 2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ hbj.le hj.2 2
    calc
      _ = (n j : ℝ) / (C ^ 2 * h j ^ 2) := by
        rw [div_div]
        congr 1
        ring
      _ ≤ (n j : ℝ) / b j ^ 2 := by
        apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hCpos) (sq_pos_of_pos hh))
          (sq_pos_of_pos hbj)).mpr
        exact mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg _)
  have hbLong : Tendsto (fun j => (n j : ℝ) / b j ^ 2) atTop atTop :=
    tendsto_atTop_mono' atTop hlongBound hlongLower
  have hnonneg : ∀ᶠ j in atTop, 0 ≤ (n j : ℝ) / b j ^ 3 := by
    filter_upwards [hb, hpos] with j hj hh
    have hbj : 0 < b j := lt_of_lt_of_le (half_pos hh) hj.1
    exact div_nonneg (Nat.cast_nonneg _) (pow_pos hbj 3).le
  have hupper : ∀ᶠ j in atTop,
      (n j : ℝ) / b j ^ 3 ≤ 8 * ((n j : ℝ) / h j ^ 3) := by
    filter_upwards [hb, hpos] with j hj hh
    have hbj : 0 < b j := lt_of_lt_of_le (half_pos hh) hj.1
    have hcube : h j ^ 3 ≤ 8 * b j ^ 3 := by
      have hp := pow_le_pow_left₀ (half_pos hh).le hj.1 3
      nlinarith
    calc
      _ ≤ (8 * (n j : ℝ)) / h j ^ 3 := by
        apply (div_le_div_iff₀ (pow_pos hbj 3) (pow_pos hh 3)).mpr
        have hm := mul_le_mul_of_nonneg_left hcube (Nat.cast_nonneg (n j) : (0 : ℝ) ≤ n j)
        nlinarith
      _ = 8 * ((n j : ℝ) / h j ^ 3) := by ring
  have hzero : Tendsto (fun j => 8 * ((n j : ℝ) / h j ^ 3)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (8 : ℝ)) atTop (𝓝 8)).mul hshort
  exact ⟨hbInf, hbLong, squeeze_zero' hnonneg hupper hzero⟩

-- PRIVATE 7: all-index positive-height K is consumed through a finite-prefix repair.
-- The actual unconditional K producer is called internally, never assumed.
private theorem fixed_law_closedStrip_relative_asymptotic
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j =>
      (Measure.pi (fun _ : Fin (n j) => ν)).real
        (@Shao.closedStrip (n j) (h j)) /
          ((4 / Real.pi) * Real.exp (-lambda * (n j : ℝ) / h j ^ 2)))
      atTop (𝓝 (1 : ℝ)) := by
  classical
  let h' : ℕ → ℝ := fun j => if 0 < h j then h j else 1
  have hpos : ∀ᶠ j in atTop, 0 < h j := hinfty.eventually_gt_atTop 0
  have hpos' (j : ℕ) : 0 < h' j := by
    dsimp only [h']
    split_ifs with hj
    · exact hj
    · norm_num
  have hh' : Tendsto h' atTop atTop := by
    apply hinfty.congr'
    filter_upwards [hpos] with j hj
    simp only [h', if_pos hj]
  have hl' : Tendsto (fun j => (n j : ℝ) / h' j ^ 2) atTop atTop := by
    apply hlong.congr'
    filter_upwards [hpos] with j hj
    simp only [h', if_pos hj]
  have hs' : Tendsto (fun j => (n j : ℝ) / h' j ^ 3) atTop (𝓝 (0 : ℝ)) := by
    apply hshort.congr'
    filter_upwards [hpos] with j hj
    simp only [h', if_pos hj]
  have hk := UnconditionalKernelAsymptotic.varying_row_closedStrip_relative_asymptotic
    (fun _ : ℕ => ν) (fun _ => inferInstance) (fun _ => h3)
    (fun _ => hmean) (fun _ => hsecond)
    (∫ x : ℝ, |x| ^ 3 ∂ν) (fun _ => le_rfl)
    h' n hpos' hh' hl' hs'
  apply hk.congr'
  filter_upwards [hpos] with j hj
  simp only [h', if_pos hj]

-- PRIVATE 8: selected-radius excess uses only the two fixed-parameter E4 heads.
private theorem selected_radius_energy_ratio_tendsto
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 (0 : ℝ)))
    (b : ℕ → ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hb : ∀ᶠ j in atTop, h j / 2 ≤ b j ∧ b j ≤ C * h j)
    (s : ℝ) (hs : 0 < s) :
    Tendsto (fun j => energyCoshExcessIntegral ν (n j) (b j) (h j) s /
      (Measure.pi (fun _ : Fin (n j) => ν)).real
        (@Shao.closedStrip (n j) (b j)))
      atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨hbInf, hbLong, hbShort⟩ := selected_radius_scales h n b C hC hinfty hlong hshort hb
  let G : ℕ → ℝ := fun j =>
    (Measure.pi (fun _ : Fin (n j) => ν)).real (@Shao.closedStrip (n j) (b j))
  let p : ℝ := s * C ^ 2
  let U : ℕ → ℝ := fun j =>
    (energyJointIntegral ν (n j) (b j) p / G j +
      energyJointIntegral ν (n j) (b j) (-p) / G j) / 2 - 1
  have hp := ConditionalEnergyConcentration.energy_laplace_ratio_tendsto
    ν h3 hmean hsecond b n hbInf hbLong hbShort p
  have hm := ConditionalEnergyConcentration.energy_laplace_ratio_tendsto
    ν h3 hmean hsecond b n hbInf hbLong hbShort (-p)
  have hU : Tendsto U atTop (𝓝 (0 : ℝ)) := by
    simpa only [U, G, show ((1 : ℝ) + 1) / 2 - 1 = 0 by norm_num] using
      ((hp.add hm).div_const 2).sub_const 1
  have hGpos : ∀ᶠ j in atTop, 0 < G j :=
    ConditionalEnergyConcentration.closedStrip_probability_eventually_pos
      ν h3 hmean hsecond b n hbInf hbLong hbShort
  have hlower : ∀ᶠ j in atTop,
      0 ≤ energyCoshExcessIntegral ν (n j) (b j) (h j) s / G j := by
    filter_upwards [hGpos] with j hj
    exact div_nonneg (energyCoshExcessIntegral_nonneg ν (n j) (b j) (h j) s) hj.le
  have hupper : ∀ᶠ j in atTop,
      energyCoshExcessIntegral ν (n j) (b j) (h j) s / G j ≤ U j := by
    filter_upwards [hGpos, hb, hinfty.eventually_gt_atTop 0] with j hj hbj hh
    have hbpos : 0 < b j := lt_of_lt_of_le (half_pos hh) hbj.1
    have hfinite := energyCoshExcess_le_fixed ν (n j) (b j) (h j) s C
      hbpos hh hs hC hbj.2
    calc
      _ ≤ ((energyJointIntegral ν (n j) (b j) p +
          energyJointIntegral ν (n j) (b j) (-p)) / 2 - G j) / G j :=
        div_le_div_of_nonneg_right hfinite hj.le
      _ = U j := by
        dsimp only [U]
        field_simp [hj.ne']
        <;> ring
  simpa only [G] using squeeze_zero' hlower hupper hU

-- PRIVATE 9: choice at every bad index; no invalid negation of eventuality.
-- This is a generic logical principle, not a public desired-limit premise.
private theorem eventually_forall_radius_of_selected
    (h : ℕ → ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hpos : ∀ᶠ j in atTop, 0 < h j)
    (P : ℕ → ℝ → Prop)
    (hselected : ∀ b : ℕ → ℝ,
      (∀ᶠ j in atTop, h j / 2 ≤ b j ∧ b j ≤ C * h j) →
        ∀ᶠ j in atTop, P j (b j)) :
    ∀ᶠ j in atTop, ∀ b : ℝ,
      h j / 2 ≤ b → b ≤ C * h j → P j b := by
  classical
  let Bad : ℕ → Prop := fun j => ∃ b : ℝ, h j / 2 ≤ b ∧ b ≤ C * h j ∧ ¬P j b
  let β : ℕ → ℝ := fun j => if hj : Bad j then Classical.choose hj else h j
  have hβ : ∀ᶠ j in atTop, h j / 2 ≤ β j ∧ β j ≤ C * h j := by
    filter_upwards [hpos] with j hj
    by_cases hbad : Bad j
    · have hc := Classical.choose_spec hbad
      simpa only [β, dif_pos hbad] using And.intro hc.1 hc.2.1
    · simp only [β, dif_neg hbad]
      constructor
      · linarith
      · simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hj.le
  have hP : ∀ᶠ j in atTop, P j (β j) := hselected β hβ
  filter_upwards [hP] with j hj b hb0 hb1
  by_contra hnot
  have hbad : Bad j := ⟨b, hb0, hb1, hnot⟩
  have hβbad : ¬P j (β j) := by
    simpa only [β, dif_pos hbad] using (Classical.choose_spec hbad).2.2
  exact hβbad hj

-- PUBLIC 3: the source (3) and uniform K relative error, with literal actual objects.
-- Only original law/moment/tail-scale hypotheses; no desired K/E4 limit premise.
theorem uniform_closedStrip_energy_controls
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 (0 : ℝ)))
    (C : ℝ) (hC : 1 ≤ C) (s : ℝ) (hs : 0 < s)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ j in atTop, ∀ b : ℝ, h j / 2 ≤ b → b ≤ C * h j →
      0 < (Measure.pi (fun _ : Fin (n j) => ν)).real
        (@Shao.closedStrip (n j) b) ∧
      |(Measure.pi (fun _ : Fin (n j) => ν)).real
          (@Shao.closedStrip (n j) b) /
            ((4 / Real.pi) * Real.exp (-lambda * (n j : ℝ) / b ^ 2)) - 1| < δ ∧
      0 ≤ energyCoshExcessIntegral ν (n j) b (h j) s /
        (Measure.pi (fun _ : Fin (n j) => ν)).real
          (@Shao.closedStrip (n j) b) ∧
      energyCoshExcessIntegral ν (n j) b (h j) s /
        (Measure.pi (fun _ : Fin (n j) => ν)).real
          (@Shao.closedStrip (n j) b) < δ := by
  apply eventually_forall_radius_of_selected h C hC (hinfty.eventually_gt_atTop 0)
  intro b hb
  obtain ⟨hbInf, hbLong, hbShort⟩ := selected_radius_scales h n b C hC hinfty hlong hshort hb
  have hK := fixed_law_closedStrip_relative_asymptotic
    ν h3 hmean hsecond b n hbInf hbLong hbShort
  have hKzero : Tendsto (fun j =>
      |(Measure.pi (fun _ : Fin (n j) => ν)).real
        (@Shao.closedStrip (n j) (b j)) /
          ((4 / Real.pi) * Real.exp (-lambda * (n j : ℝ) / b j ^ 2)) - 1|)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, abs_zero] using (hK.sub_const 1).abs
  have hGpos := ConditionalEnergyConcentration.closedStrip_probability_eventually_pos
    ν h3 hmean hsecond b n hbInf hbLong hbShort
  have hJ := selected_radius_energy_ratio_tendsto
    ν h3 hmean hsecond h n hinfty hlong hshort b C hC hb s hs
  filter_upwards [hGpos, hKzero.eventually (gt_mem_nhds hδ),
    hJ.eventually (gt_mem_nhds hδ)] with j hj hk hsmall
  exact ⟨hj, hk, div_nonneg
    (energyCoshExcessIntegral_nonneg ν (n j) (b j) (h j) s) hj.le, hsmall⟩

-- PUBLIC 4: the one-tail boundary-ratio bound needed by all middle layers.
theorem uniform_closedStrip_boundary_ratio_bound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 (0 : ℝ)))
    (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ j in atTop,
      0 < (Measure.pi (fun _ : Fin (n j) => ν)).real
        (@Shao.closedStrip (n j) (h j)) ∧
      ∀ b : ℝ, h j / 2 ≤ b → b ≤ C * h j →
        0 < (Measure.pi (fun _ : Fin (n j) => ν)).real
          (@Shao.closedStrip (n j) b) ∧
        (Measure.pi (fun _ : Fin (n j) => ν)).real
            (@Shao.closedStrip (n j) b) /
          (Measure.pi (fun _ : Fin (n j) => ν)).real
            (@Shao.closedStrip (n j) (h j)) ≤
          4 * Real.exp (lambda * ((n j : ℝ) / h j ^ 2 - (n j : ℝ) / b ^ 2)) := by
  have hcontrols := uniform_closedStrip_energy_controls ν h3 hmean hsecond h n
    hinfty hlong hshort C hC 1 (by norm_num) (1 / 2) (by norm_num)
  filter_upwards [hcontrols, hinfty.eventually_gt_atTop 0] with j hj hh
  have hhlo : h j / 2 ≤ h j := by linarith
  have hhhi : h j ≤ C * h j := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hh.le
  have hself := hj (h j) hhlo hhhi
  refine ⟨hself.1, ?_⟩
  intro b hb0 hb1
  have hB := hj b hb0 hb1
  refine ⟨hB.1, ?_⟩
  let Gb : ℝ := (Measure.pi (fun _ : Fin (n j) => ν)).real (@Shao.closedStrip (n j) b)
  let Gh : ℝ := (Measure.pi (fun _ : Fin (n j) => ν)).real (@Shao.closedStrip (n j) (h j))
  let mb : ℝ := (4 / Real.pi) * Real.exp (-lambda * (n j : ℝ) / b ^ 2)
  let mh : ℝ := (4 / Real.pi) * Real.exp (-lambda * (n j : ℝ) / h j ^ 2)
  let E : ℝ := Real.exp (lambda * ((n j : ℝ) / h j ^ 2 - (n j : ℝ) / b ^ 2))
  have hmb : 0 < mb := mul_pos (div_pos (by norm_num) Real.pi_pos) (Real.exp_pos _)
  have hmh : 0 < mh := mul_pos (div_pos (by norm_num) Real.pi_pos) (Real.exp_pos _)
  have hGh : 0 < Gh := hself.1
  have hqb : Gb / mb ≤ 2 := by
    have hu := (abs_lt.mp hB.2.1).2
    change Gb / mb - 1 < (1 / 2 : ℝ) at hu
    linarith
  have hqh : (1 / 2 : ℝ) ≤ Gh / mh := by
    have hl := (abs_lt.mp hself.2.1).1
    change -(1 / 2 : ℝ) < Gh / mh - 1 at hl
    linarith
  have hGb : Gb ≤ 2 * mb := (div_le_iff₀ hmb).mp hqb
  have hGhMain : mh ≤ 2 * Gh := by
    have hm := (le_div_iff₀ hmh).mp hqh
    linarith
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hexp : Real.exp (-lambda * (n j : ℝ) / b ^ 2) =
      E * Real.exp (-lambda * (n j : ℝ) / h j ^ 2) := by
    dsimp only [E]
    rw [← Real.exp_add]
    congr 1
    ring
  have hmain : mb = E * mh := by
    dsimp only [mb, mh]
    rw [hexp]
    ring
  change Gb / Gh ≤ 4 * E
  apply (div_le_iff₀ hGh).mpr
  calc
    Gb ≤ 2 * mb := hGb
    _ ≤ 4 * E * Gh := by
      rw [hmain]
      have hm := mul_le_mul_of_nonneg_left hGhMain (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hE)
      nlinarith

-- PUBLIC 5: actual joint-energy concentration on the ORIGINAL h² scale.
theorem uniform_energy_concentration
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 (0 : ℝ)))
    (C : ℝ) (hC : 1 ≤ C)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ j in atTop, ∀ b : ℝ, h j / 2 ≤ b → b ≤ C * h j →
      0 < (Measure.pi (fun _ : Fin (n j) => ν)).real
        (@Shao.closedStrip (n j) b) ∧
      0 ≤ (Measure.pi (fun _ : Fin (n j) => ν)).real
          ((@Shao.closedStrip (n j) b) ∩
            {a : Shao.Path (n j) |
              ε * h j ^ 2 < |Shao.energy a - (n j : ℝ)|}) /
        (Measure.pi (fun _ : Fin (n j) => ν)).real
          (@Shao.closedStrip (n j) b) ∧
      (Measure.pi (fun _ : Fin (n j) => ν)).real
          ((@Shao.closedStrip (n j) b) ∩
            {a : Shao.Path (n j) |
              ε * h j ^ 2 < |Shao.energy a - (n j : ℝ)|}) /
        (Measure.pi (fun _ : Fin (n j) => ν)).real
          (@Shao.closedStrip (n j) b) < δ := by
  let D : ℝ := (Real.exp ε + Real.exp (-ε)) / 2 - 1
  have hD : 0 < D := exp_pair_strict_pos ε hε
  have hcontrols := uniform_closedStrip_energy_controls ν h3 hmean hsecond h n
    hinfty hlong hshort C hC 1 (by norm_num) (δ * D) (mul_pos hδ hD)
  filter_upwards [hcontrols, hinfty.eventually_gt_atTop 0] with j hj hh b hb0 hb1
  have hB := hj b hb0 hb1
  have hbpos : 0 < b := lt_of_lt_of_le (half_pos hh) hb0
  have hfinite := (energy_deviation_finite_bound ν (n j) b (h j) 1 ε
    hbpos hh (by norm_num) hε).2
  let G : ℝ := (Measure.pi (fun _ : Fin (n j) => ν)).real (@Shao.closedStrip (n j) b)
  let R : ℝ := (Measure.pi (fun _ : Fin (n j) => ν)).real
    ((@Shao.closedStrip (n j) b) ∩
      {a : Shao.Path (n j) | ε * h j ^ 2 < |Shao.energy a - (n j : ℝ)|})
  have hG : 0 < G := hB.1
  have hf : D * R ≤ energyCoshExcessIntegral ν (n j) b (h j) 1 := by
    simpa only [one_mul, D, R] using hfinite
  have hR : 0 ≤ R / G := div_nonneg ENNReal.toReal_nonneg hG.le
  refine ⟨hB.1, hR, ?_⟩
  change R / G < δ
  have hprod : (R / G) * D < δ * D := by
    calc
      _ = (D * R) / G := by ring
      _ ≤ energyCoshExcessIntegral ν (n j) b (h j) 1 / G :=
        div_le_div_of_nonneg_right hf hG.le
      _ < δ * D := hB.2.2.2
  nlinarith [hprod]

end Shao.OQ4.UniformConditionalEnergy
end
