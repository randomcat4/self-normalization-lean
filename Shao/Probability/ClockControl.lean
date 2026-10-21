import Shao.Probability.FiniteIID
import Shao.Probability.GaussianTail
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

namespace Shao.Probability

private theorem bounded_power_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) (p : ℕ) :
    Integrable (fun a : ℝ => a ^ p) ν := by
  apply Integrable.of_bound (by fun_prop) (h ^ p)
  filter_upwards [hs] with a ha
  simpa only [Real.norm_eq_abs, abs_pow] using
    pow_le_pow_left₀ (abs_nonneg a) ha p

private theorem square_mean_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    0 ≤ (∫ a : ℝ, a ^ 2 ∂ν) ∧ (∫ a : ℝ, a ^ 2 ∂ν) ≤ h ^ 2 := by
  refine ⟨integral_nonneg (fun a => sq_nonneg a), ?_⟩
  have hm := integral_mono_ae (bounded_power_integrable ν h hs 2)
    (integrable_const (h ^ 2)) ?_
  · simpa using hm
  · filter_upwards [hs] with a ha
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) ha 2

private theorem centered_square_support (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    ∀ᵐ a : ℝ ∂ν, |a ^ 2 - (∫ z : ℝ, z ^ 2 ∂ν)| ≤ h ^ 2 := by
  obtain ⟨hm0, hmh⟩ := square_mean_bounds ν h hs
  filter_upwards [hs] with a ha
  have ha2 : a ^ 2 ≤ h ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) ha 2
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg a], by linarith⟩

private theorem centered_square_moments (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    Integrable (fun a : ℝ => (a ^ 2 - m2) ^ 2) ν ∧
      (∫ a : ℝ, a ^ 2 - m2 ∂ν) = 0 ∧
      (∫ a : ℝ, (a ^ 2 - m2) ^ 2 ∂ν) ≤ ∫ a : ℝ, a ^ 4 ∂ν := by
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
  have h2 := bounded_power_integrable ν h hs 2
  have h4 := bounded_power_integrable ν h hs 4
  have hpoly (a : ℝ) : (a ^ 2 - m2) ^ 2 = a ^ 4 - (2 * m2) * a ^ 2 + m2 ^ 2 := by ring
  have hi : Integrable (fun a : ℝ => (a ^ 2 - m2) ^ 2) ν := by
    apply ((h4.sub (h2.const_mul (2 * m2))).add (integrable_const (m2 ^ 2))).congr
    exact ae_of_all ν (fun a => (hpoly a).symm)
  refine ⟨hi, ?_, ?_⟩
  · rw [integral_sub h2 (integrable_const m2)]
    simp [m2]
  · have heq : (∫ a : ℝ, (a ^ 2 - m2) ^ 2 ∂ν) =
        (∫ a : ℝ, a ^ 4 ∂ν) - m2 ^ 2 := by
      simp_rw [hpoly]
      rw [integral_add (f := fun a : ℝ => a ^ 4 - (2 * m2) * a ^ 2)
          (g := fun _a : ℝ => m2 ^ 2)
          (h4.sub (h2.const_mul (2 * m2))) (integrable_const (m2 ^ 2)),
        integral_sub (f := fun a : ℝ => a ^ 4) (g := fun a : ℝ => (2 * m2) * a ^ 2)
          h4 (h2.const_mul (2 * m2)), integral_const_mul]
      simp [m2]
      ring
    rw [heq]
    linarith [sq_nonneg m2]

private theorem one_clock_exp_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (θ : ℝ) (hθ : |θ| * h ^ 2 ≤ 1) :
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    Integrable (fun a : ℝ => Real.exp (θ * (a ^ 2 - m2))) ν ∧
      (∫ a : ℝ, Real.exp (θ * (a ^ 2 - m2)) ∂ν) ≤
        Real.exp (2 * θ ^ 2 * (∫ a : ℝ, a ^ 4 ∂ν)) := by
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
  have hB := centered_square_support ν h hs
  obtain ⟨hBi, hBm, hB2⟩ := centered_square_moments ν h hs
  change Integrable (fun a : ℝ => (a ^ 2 - m2) ^ 2) ν at hBi
  change (∫ a : ℝ, a ^ 2 - m2 ∂ν) = 0 at hBm
  have hθB : ∀ᵐ a : ℝ ∂ν, |θ * (a ^ 2 - m2)| ≤ 1 := by
    filter_upwards [hB] with a ha
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left ha (abs_nonneg θ)).trans hθ
  have hi : Integrable (fun a : ℝ => Real.exp (θ * (a ^ 2 - m2))) ν := by
    apply Integrable.of_bound (by fun_prop) (Real.exp 1)
    filter_upwards [hθB] with a ha
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans ha)
  have hBint := (bounded_power_integrable ν h hs 2).sub (integrable_const m2)
  have hpoint : ∀ᵐ a : ℝ ∂ν,
      Real.exp (θ * (a ^ 2 - m2)) ≤
        1 + θ * (a ^ 2 - m2) + 2 * θ ^ 2 * (a ^ 2 - m2) ^ 2 := by
    filter_upwards [hθB] with a ha
    have hp := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le ha)).2
    nlinarith [sq_nonneg (θ * (a ^ 2 - m2))]
  have hb := integral_mono_ae hi
    (((integrable_const 1).add (hBint.const_mul θ)).add (hBi.const_mul (2 * θ ^ 2))) hpoint
  change (∫ a : ℝ, Real.exp (θ * (a ^ 2 - m2)) ∂ν) ≤
    ∫ a : ℝ, 1 + θ * (a ^ 2 - m2) + 2 * θ ^ 2 * (a ^ 2 - m2) ^ 2 ∂ν at hb
  have hlin : (∫ a : ℝ, Real.exp (θ * (a ^ 2 - m2)) ∂ν) ≤
      1 + 2 * θ ^ 2 * (∫ a : ℝ, (a ^ 2 - m2) ^ 2 ∂ν) := by
    rw [integral_add (f := fun a : ℝ => 1 + θ * (a ^ 2 - m2))
        (g := fun a : ℝ => 2 * θ ^ 2 * (a ^ 2 - m2) ^ 2)
        ((integrable_const 1).add (hBint.const_mul θ)) (hBi.const_mul (2 * θ ^ 2)),
      integral_add (f := fun _a : ℝ => (1 : ℝ)) (g := fun a : ℝ => θ * (a ^ 2 - m2))
        (integrable_const 1) (hBint.const_mul θ), integral_const_mul,
      integral_const_mul, hBm] at hb
    simpa using hb
  refine ⟨hi, hlin.trans ?_⟩
  calc
    _ ≤ 1 + 2 * θ ^ 2 * (∫ a : ℝ, a ^ 4 ∂ν) := by
      gcongr
    _ ≤ Real.exp (2 * θ ^ 2 * (∫ a : ℝ, a ^ 4 ∂ν)) := by
      simpa only [add_comm] using Real.add_one_le_exp (2 * θ ^ 2 * (∫ a : ℝ, a ^ 4 ∂ν))

private theorem prefixSquares_sum_castLE {n : ℕ} (a : Shao.Path n)
    (k : ℕ) (hk : k ≤ n) :
    Shao.prefixSquares a k = ∑ i : Fin k, (a (i.castLE hk)) ^ 2 := by
  classical
  unfold Shao.prefixSquares
  symm
  refine Finset.sum_bij (fun i _ => i.castLE hk) ?_ ?_ ?_ ?_
  · intro i _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castLE]
    exact i.is_lt
  · intro i _ j _ he
    exact Fin.castLE_injective hk he
  · intro j hj
    refine ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext rfl
  · intro i _
    rfl

theorem iid_bounded_clock_exp_integral
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (h : ℝ) (hh : 0 ≤ h) (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (k : ℕ) (hk : k ≤ n) (θ : ℝ) (hθ : |θ| * h ^ 2 ≤ 1) :
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m4 : ℝ := ∫ a : ℝ, a ^ 4 ∂ν
    let D : Ω → ℝ := fun ω =>
      Shao.prefixSquares (samplePath X ω) k - (k : ℝ) * m2
    Integrable (fun ω => Real.exp (θ * D ω)) μ ∧
      (∫ ω, Real.exp (θ * D ω) ∂μ) ≤
        Real.exp (2 * θ ^ 2 * (k : ℝ) * m4) := by
  classical
  have _ := hh
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
  let m4 : ℝ := ∫ a : ℝ, a ^ 4 ∂ν
  let Y : Fin k → Ω → ℝ := fun i => X (i.castLE hk)
  let B : ℝ → ℝ := fun a => a ^ 2 - m2
  let D : Ω → ℝ := fun ω =>
    Shao.prefixSquares (samplePath X ω) k - (k : ℝ) * m2
  have hD : D = fun ω => ∑ i : Fin k, B (Y i ω) := by
    funext ω
    dsimp only [D]
    rw [prefixSquares_sum_castLE _ k hk]
    simp [B, Y, samplePath, Finset.sum_sub_distrib]
  have hcoord (i : Fin k) : ∀ᵐ ω ∂μ, |B (Y i ω)| ≤ h ^ 2 := by
    have hB := centered_square_support ν h hsupport
    exact (hLaw (i.castLE hk)).symm.ae_snd
      (p := fun a : ℝ => |a ^ 2 - m2| ≤ h ^ 2)
      (measurableSet_le (continuous_abs.measurable.comp ((measurable_id.pow_const 2).sub_const m2))
        measurable_const) hB
  have hi : Integrable (fun ω => Real.exp (θ * D ω)) μ := by
    apply Integrable.of_bound (by dsimp [D, samplePath, Shao.prefixSquares]; fun_prop)
      (Real.exp (|θ| * ((k : ℝ) * h ^ 2)))
    filter_upwards [(ae_all_iff.2 hcoord)] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hsum : |D ω| ≤ (k : ℝ) * h ^ 2 := by
      rw [hD]
      apply abs_le.mpr
      constructor
      · have hl := Finset.sum_le_sum (s := Finset.univ)
          (fun i _ => (abs_le.mp (hω i)).1)
        simpa using hl
      · have hu := Finset.sum_le_sum (s := Finset.univ)
          (fun i _ => (abs_le.mp (hω i)).2)
        simpa using hu
    calc
      θ * D ω ≤ |θ * D ω| := le_abs_self _
      _ = |θ| * |D ω| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (abs_nonneg θ)
  have hYi : iIndepFun Y μ := hIndep.precomp (Fin.castLE_injective hk)
  have hYm (i : Fin k) : Measurable (Y i) := hX (i.castLE hk)
  have hf : Measurable (fun a : ℝ => Real.exp (θ * B a)) := by dsimp [B]; fun_prop
  have hfac := hYi.integral_fun_prod_comp (fun i => (hYm i).aemeasurable)
    (f := fun _ a => Real.exp (θ * B a)) (fun _ => hf.aestronglyMeasurable)
  have hmarg (i : Fin k) : (∫ ω, Real.exp (θ * B (Y i ω)) ∂μ) =
      ∫ a : ℝ, Real.exp (θ * B a) ∂ν := (hLaw (i.castLE hk)).comp hf |>.integral_eq
  have hex : (fun ω => Real.exp (θ * D ω)) =
      (fun ω => ∏ i : Fin k, Real.exp (θ * B (Y i ω))) := by
    funext ω
    rw [hD, Finset.mul_sum, Real.exp_sum]
  have heq : (∫ ω, Real.exp (θ * D ω) ∂μ) =
      (∫ a : ℝ, Real.exp (θ * B a) ∂ν) ^ k := by
    rw [hex, hfac]
    simp only [hmarg, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  obtain ⟨_, hbound⟩ := one_clock_exp_bound ν h hsupport θ hθ
  refine ⟨hi, ?_⟩
  rw [heq]
  calc
    _ ≤ (Real.exp (2 * θ ^ 2 * m4)) ^ k :=
      pow_le_pow_left₀ (integral_nonneg fun a => (Real.exp_pos _).le) hbound k
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem iid_bounded_clock_deviation_le
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (h : ℝ) (hh : 0 ≤ h) (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (k : ℕ) (hk : k ≤ n)
    (δ θ : ℝ) (hδ : 0 < δ) (hθ : 0 < θ) (hstep : θ * h ^ 2 ≤ 1) :
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m4 : ℝ := ∫ a : ℝ, a ^ 4 ∂ν
    let D : Ω → ℝ := fun ω =>
      Shao.prefixSquares (samplePath X ω) k - (k : ℝ) * m2
    μ.real {ω | δ ≤ |D ω|} ≤
      (Real.exp (2 * θ ^ 2 * (k : ℝ) * m4) - 1) /
        (Real.cosh (θ * δ) - 1) := by
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
  let m4 : ℝ := ∫ a : ℝ, a ^ 4 ∂ν
  let D : Ω → ℝ := fun ω =>
    Shao.prefixSquares (samplePath X ω) k - (k : ℝ) * m2
  obtain ⟨hpi, hp⟩ := iid_bounded_clock_exp_integral hX hIndep hLaw h hh hsupport k hk θ
    (by simpa only [abs_of_pos hθ] using hstep)
  obtain ⟨hni, hn⟩ := iid_bounded_clock_exp_integral hX hIndep hLaw h hh hsupport k hk (-θ)
    (by simpa only [abs_neg, abs_of_pos hθ] using hstep)
  change Integrable (fun ω => Real.exp (θ * D ω)) μ at hpi
  change Integrable (fun ω => Real.exp ((-θ) * D ω)) μ at hni
  change (∫ ω, Real.exp (θ * D ω) ∂μ) ≤ Real.exp (2 * θ ^ 2 * (k : ℝ) * m4) at hp
  change (∫ ω, Real.exp ((-θ) * D ω) ∂μ) ≤ Real.exp (2 * (-θ) ^ 2 * (k : ℝ) * m4) at hn
  simp only [neg_sq] at hn
  let f : Ω → ℝ := fun ω => Real.cosh (θ * D ω) - 1
  have hf : f = fun ω =>
      (Real.exp (θ * D ω) + Real.exp ((-θ) * D ω)) / 2 - 1 := by
    funext ω
    simp only [f, Real.cosh_eq, neg_mul]
  have hfi : Integrable f μ := by
    rw [hf]
    exact ((hpi.add hni).div_const 2).sub (integrable_const 1)
  have hIf : (∫ ω, f ω ∂μ) =
      ((∫ ω, Real.exp (θ * D ω) ∂μ) + (∫ ω, Real.exp ((-θ) * D ω) ∂μ)) / 2 - 1 := by
    rw [hf]
    change (∫ ω, (Real.exp (θ * D ω) + Real.exp ((-θ) * D ω)) / 2 - 1 ∂μ) = _
    rw [integral_sub (f := fun ω => (Real.exp (θ * D ω) + Real.exp ((-θ) * D ω)) / 2)
        (g := fun _ω => (1 : ℝ)) ((hpi.add hni).div_const 2) (integrable_const 1),
      integral_div,
      integral_add (f := fun ω => Real.exp (θ * D ω)) (g := fun ω => Real.exp ((-θ) * D ω))
        hpi hni]
    simp
  have hI : (∫ ω, f ω ∂μ) ≤ Real.exp (2 * θ ^ 2 * (k : ℝ) * m4) - 1 := by
    rw [hIf]
    linarith
  let c : ℝ := Real.cosh (θ * δ) - 1
  have hc : 0 < c := by
    dsimp only [c]
    have hlt := Real.one_lt_cosh.mpr (mul_pos hθ hδ).ne'
    linarith
  have hsub : {ω | δ ≤ |D ω|} ⊆ {ω | c ≤ f ω} := by
    intro ω hω
    apply sub_le_sub_right (Real.cosh_le_cosh.mpr ?_) 1
    simpa only [abs_mul, abs_of_pos hθ, abs_of_pos hδ] using
      mul_le_mul_of_nonneg_left hω hθ.le
  have hm : μ.real {ω | δ ≤ |D ω|} ≤ μ.real {ω | c ≤ f ω} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun ω => sub_nonneg.mpr (Real.one_le_cosh (θ * D ω)))) hfi c
  change μ.real {ω | δ ≤ |D ω|} ≤
    (Real.exp (2 * θ ^ 2 * (k : ℝ) * m4) - 1) / c
  apply (le_div_iff₀ hc).2
  calc
    _ ≤ μ.real {ω | c ≤ f ω} * c := mul_le_mul_of_nonneg_right hm hc.le
    _ ≤ ∫ ω, f ω ∂μ := by simpa only [mul_comm] using hmark
    _ ≤ _ := hI

private theorem fourth_le_bound_mul_cube (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    (∫ a : ℝ, a ^ 4 ∂ν) ≤ h * (∫ a : ℝ, |a| ^ 3 ∂ν) := by
  have h3 : Integrable (fun a : ℝ => |a| ^ 3) ν := by
    simpa only [Real.norm_eq_abs, abs_pow] using (bounded_power_integrable ν h hs 3).norm
  have hm := integral_mono_ae (bounded_power_integrable ν h hs 4) (h3.const_mul h) ?_
  · simpa only [integral_const_mul] using hm
  · filter_upwards [hs] with a ha
    calc
      a ^ 4 = (|a| ^ 2) ^ 2 := by rw [sq_abs]; ring
      _ = |a| * |a| ^ 3 := by ring
      _ ≤ h * |a| ^ 3 := mul_le_mul_of_nonneg_right ha (pow_nonneg (abs_nonneg a) 3)

private theorem clock_exp_le_normal_tail (y : ℝ) (hy : 0 ≤ y) :
    Real.exp (-(1 + y) ^ 2) ≤ Real.sqrt (2 * Real.pi) * Shao.standardNormalTail y := by
  let c : ℝ := Real.sqrt (2 * Real.pi)
  have hc : 0 < c := Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
  have ha : 0 < 1 + y := by linarith
  have hφ : Shao.standardNormalDensity y = c⁻¹ * Real.exp (-y ^ 2 / 2) := by
    simp [Shao.standardNormalDensity, ProbabilityTheory.gaussianPDFReal, c]
  have hm := (div_le_iff₀ ha).1 (Shao.standardNormal_mills_bounds y hy).1
  have hmul := mul_le_mul_of_nonneg_left hm hc.le
  rw [hφ, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at hmul
  have hex : (1 + y) * Real.exp (-(1 + y) ^ 2) ≤ Real.exp (-y ^ 2 / 2) := by
    calc
      _ ≤ Real.exp y * Real.exp (-(1 + y) ^ 2) := by
        exact mul_le_mul_of_nonneg_right (by simpa only [add_comm] using Real.add_one_le_exp y)
          (Real.exp_pos _).le
      _ = Real.exp (y - (1 + y) ^ 2) := by rw [← Real.exp_add]; congr 1
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg y])
  have hp : Real.exp (-(1 + y) ^ 2) * (1 + y) ≤
      (c * Shao.standardNormalTail y) * (1 + y) := by
    calc
      _ ≤ Real.exp (-y ^ 2 / 2) := by simpa only [mul_comm] using hex
      _ ≤ _ := by simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul
  by_contra! hn
  have hpos := mul_pos (sub_pos.mpr hn) ha
  nlinarith

theorem iid_bounded_clock_bad_probability_le
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (h y : ℝ) (hh : 0 ≤ h) (hy : 2 ≤ y)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (hlower : (3 / 4 : ℝ) ≤ (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν))
    (hupper : (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν) ≤ (4 / 3 : ℝ))
    (hscale : (1 + y) * h ≤ 1)
    (hstep : 8 * (1 + y) ^ 2 * h ^ 2 ≤ 1)
    (hbudget : (8 * (1 + y) ^ 2) ^ 2 * (n : ℝ) *
      (∫ a : ℝ, a ^ 4 ∂ν) ≤ (1 / 2 : ℝ)) :
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    μ.real {ω | Shao.prefixSquares (samplePath X ω) (n / 2) < (1 / 16 : ℝ)} +
      μ.real {ω | Shao.energy (samplePath X ω) ∉ Set.Icc (1 / 4 : ℝ) 2} ≤
        2048 * Real.sqrt (2 * Real.pi) *
          ((1 + y) ^ 3 * (n : ℝ) * m3) * Shao.standardNormalTail y := by
  let a : ℝ := 1 + y
  let θ : ℝ := 8 * a ^ 2
  let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂ν
  let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂ν
  let m4 : ℝ := ∫ z : ℝ, z ^ 4 ∂ν
  let Q : ℕ → Ω → ℝ := fun j ω => Shao.prefixSquares (samplePath X ω) j
  have ha : 3 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have hθ0 : 0 < θ := by dsimp [θ]; positivity
  have hm20 : 0 ≤ m2 := (square_mean_bounds ν h hsupport).1
  have hm2h : m2 ≤ h ^ 2 := (square_mean_bounds ν h hsupport).2
  have hm30 : 0 ≤ m3 := integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  have hm40 : 0 ≤ m4 := integral_nonneg (fun z => by positivity)
  have hhthird : h ≤ (1 / 3 : ℝ) := by
    have hprod := mul_nonneg (show 0 ≤ a - 3 by linarith) hh
    change a * h ≤ 1 at hscale
    nlinarith
  have hm2nine : m2 ≤ (1 / 9 : ℝ) := by nlinarith
  have hn7 : 7 ≤ n := by
    by_contra! hn
    have hn6 : (n : ℝ) ≤ 6 := by exact_mod_cast (show n ≤ 6 by omega)
    have hb := mul_le_mul_of_nonneg_left hm2nine (Nat.cast_nonneg n)
    change (3 / 4 : ℝ) ≤ (n : ℝ) * m2 at hlower
    nlinarith
  have hk : n / 2 ≤ n := Nat.div_le_self n 2
  have hk3 : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 3 * (n / 2) by omega)
  have hkm : (1 / 4 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) * m2 := by
    have hp := mul_le_mul_of_nonneg_right hk3 hm20
    change (3 / 4 : ℝ) ≤ (n : ℝ) * m2 at hlower
    nlinarith
  have hden : Real.exp (a ^ 2) / 4 ≤ Real.cosh (a ^ 2) - 1 := by
    have hexp4 : 4 ≤ Real.exp (a ^ 2) := by
      nlinarith [Real.add_one_le_exp (a ^ 2), sq_nonneg (a - 3)]
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-a ^ 2)]
  have hden0 : 0 < Real.cosh (a ^ 2) - 1 :=
    lt_of_lt_of_le (div_pos (Real.exp_pos _) (by norm_num)) hden
  have hdev (j : ℕ) (hj : j ≤ n) :
      μ.real {ω | (1 / 8 : ℝ) ≤ |Q j ω - (j : ℝ) * m2|} ≤
        16 * θ ^ 2 * (n : ℝ) * m4 * Real.exp (-a ^ 2) := by
    have hjr : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
    have hpay : θ ^ 2 * (j : ℝ) * m4 ≤ θ ^ 2 * (n : ℝ) * m4 := by
      gcongr
    have hu0 : 0 ≤ 2 * θ ^ 2 * (j : ℝ) * m4 := by positivity
    have hu1 : 2 * θ ^ 2 * (j : ℝ) * m4 ≤ 1 := by
      change θ ^ 2 * (n : ℝ) * m4 ≤ (1 / 2 : ℝ) at hbudget
      nlinarith
    have hexc : Real.exp (2 * θ ^ 2 * (j : ℝ) * m4) - 1 ≤
        4 * θ ^ 2 * (n : ℝ) * m4 := by
      have ht := Real.abs_exp_sub_one_le (x := 2 * θ ^ 2 * (j : ℝ) * m4)
        (by rw [abs_of_nonneg hu0]; exact hu1)
      rw [abs_of_nonneg hu0] at ht
      have hs := le_abs_self (Real.exp (2 * θ ^ 2 * (j : ℝ) * m4) - 1)
      nlinarith
    have hd := iid_bounded_clock_deviation_le hX hIndep hLaw h hh hsupport j hj
      (1 / 8) θ (by norm_num) hθ0 hstep
    change μ.real {ω | (1 / 8 : ℝ) ≤ |Q j ω - (j : ℝ) * m2|} ≤
      (Real.exp (2 * θ ^ 2 * (j : ℝ) * m4) - 1) / (Real.cosh (θ * (1 / 8)) - 1) at hd
    have hθδ : θ * (1 / 8 : ℝ) = a ^ 2 := by dsimp [θ]; ring
    rw [hθδ] at hd
    apply hd.trans
    apply (div_le_iff₀ hden0).2
    have hp : 0 ≤ 16 * θ ^ 2 * (n : ℝ) * m4 * Real.exp (-a ^ 2) := by positivity
    calc
      _ ≤ 4 * θ ^ 2 * (n : ℝ) * m4 := hexc
      _ = (16 * θ ^ 2 * (n : ℝ) * m4 * Real.exp (-a ^ 2)) *
          (Real.exp (a ^ 2) / 4) := by
        rw [Real.exp_neg]
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hden hp
  have hsub1 : {ω | Q (n / 2) ω < (1 / 16 : ℝ)} ⊆
      {ω | (1 / 8 : ℝ) ≤ |Q (n / 2) ω - ((n / 2 : ℕ) : ℝ) * m2|} := by
    intro ω hω
    have ht := neg_le_abs (Q (n / 2) ω - ((n / 2 : ℕ) : ℝ) * m2)
    change Q (n / 2) ω < (1 / 16 : ℝ) at hω
    change (1 / 8 : ℝ) ≤ _
    linarith
  have hsub2 : {ω | Shao.energy (samplePath X ω) ∉ Set.Icc (1 / 4 : ℝ) 2} ⊆
      {ω | (1 / 8 : ℝ) ≤ |Q n ω - (n : ℝ) * m2|} := by
    intro ω hω
    have hQ : Q n ω = Shao.energy (samplePath X ω) := Shao.prefixSquares_length _
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, not_and_or, not_le] at hω
    change (1 / 8 : ℝ) ≤ _
    rw [hQ]
    change (3 / 4 : ℝ) ≤ (n : ℝ) * m2 at hlower
    change (n : ℝ) * m2 ≤ (4 / 3 : ℝ) at hupper
    rcases hω with hω | hω
    · have ht := neg_le_abs (Q n ω - (n : ℝ) * m2)
      rw [hQ] at ht
      linarith
    · have ht := le_abs_self (Q n ω - (n : ℝ) * m2)
      rw [hQ] at ht
      linarith
  have hb1 := (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub1)).trans (hdev _ hk)
  have hb2 := (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub2)).trans (hdev n le_rfl)
  change μ.real {ω | Q (n / 2) ω < (1 / 16 : ℝ)} ≤
    16 * θ ^ 2 * (n : ℝ) * m4 * Real.exp (-a ^ 2) at hb1
  change μ.real {ω | Shao.energy (samplePath X ω) ∉ Set.Icc (1 / 4 : ℝ) 2} ≤
    16 * θ ^ 2 * (n : ℝ) * m4 * Real.exp (-a ^ 2) at hb2
  have hcube : a * m4 ≤ m3 := by
    have hm4 := fourth_le_bound_mul_cube ν h hsupport
    change m4 ≤ h * m3 at hm4
    have hm := mul_le_mul_of_nonneg_left hm4 ha0.le
    have hs := mul_le_mul_of_nonneg_right hscale hm30
    nlinarith
  have hnormal := clock_exp_le_normal_tail y (by linarith)
  change Real.exp (-a ^ 2) ≤ Real.sqrt (2 * Real.pi) * Shao.standardNormalTail y at hnormal
  change μ.real {ω | Q (n / 2) ω < (1 / 16 : ℝ)} +
    μ.real {ω | Shao.energy (samplePath X ω) ∉ Set.Icc (1 / 4 : ℝ) 2} ≤ _
  calc
    _ ≤ 32 * θ ^ 2 * (n : ℝ) * m4 * Real.exp (-a ^ 2) := by linarith
    _ = (2048 * a ^ 3 * (n : ℝ) * Real.exp (-a ^ 2)) * (a * m4) := by dsimp [θ]; ring
    _ ≤ (2048 * a ^ 3 * (n : ℝ) * Real.exp (-a ^ 2)) * m3 := by
      exact mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = (2048 * a ^ 3 * (n : ℝ) * m3) * Real.exp (-a ^ 2) := by ring
    _ ≤ (2048 * a ^ 3 * (n : ℝ) * m3) *
        (Real.sqrt (2 * Real.pi) * Shao.standardNormalTail y) := by
      exact mul_le_mul_of_nonneg_left hnormal (by positivity)
    _ = _ := by dsimp [a]; ring

end Shao.Probability
