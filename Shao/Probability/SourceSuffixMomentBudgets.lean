/- Raw finite-variance Gaussian damping and the actual suffix moment budgets. -/
import Shao.Probability.FiniteIID
import Shao.Probability.SpitzerFinite
import Shao.Probability.TruncationRegularity
import Shao.Probability.TruncationSampleSize
import Shao.Probability.SourceMarkedSuffixAveraging
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Shao.Probability
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Classical

private theorem smb_exp_remainder (v : ℝ) :
    Real.exp v ≤ 1 + v + v ^ 2 * Real.exp |v| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (v : ℂ) 2
  have h' : ‖Complex.exp (v : ℂ) - (1 + (v : ℂ))‖ ≤ v ^ 2 * Real.exp |v| := by
    simpa [Finset.sum_range_succ, Real.norm_eq_abs, sq_abs] using h
  have hc : Complex.exp (v : ℂ) - (1 + (v : ℂ)) = ((Real.exp v - (1 + v) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_exp]
  rw [hc, Complex.norm_real, Real.norm_eq_abs] at h'
  have hh := (le_abs_self (Real.exp v - (1 + v))).trans h'
  linarith only [hh]

private theorem smb_gaussian_linear (u : ℝ) :
    u * Real.exp (-(u ^ 2) / 2) ≤ 1 := by
  have hu : u ≤ Real.exp (u ^ 2 / 2) := by
    nlinarith [Real.add_one_le_exp (u ^ 2 / 2), sq_nonneg (u - 1)]
  calc
    _ ≤ Real.exp (u ^ 2 / 2) * Real.exp (-(u ^ 2) / 2) :=
      mul_le_mul_of_nonneg_right hu (Real.exp_pos _).le
    _ = 1 := by
      rw [← Real.exp_add, show u ^ 2 / 2 + -(u ^ 2) / 2 = 0 by ring, Real.exp_zero]

private theorem smb_completed_square
    (s lambda epsilon x : ℝ) (hs : 0 < s)
    (he : epsilon = 1 ∨ epsilon = -1) :
    Real.exp (-s * x ^ 2 + epsilon * lambda * Real.sqrt s * x) ≤
        Real.exp (lambda ^ 2 / 4) ∧
      Real.exp (-s * x ^ 2 + epsilon * lambda * Real.sqrt s * x) ≤
        Real.exp (lambda ^ 2 / 2) * Real.exp (-(s / 2) * x ^ 2) := by
  have hsq : (Real.sqrt s * x) ^ 2 = s * x ^ 2 := by rw [mul_pow, Real.sq_sqrt hs.le]
  constructor
  · apply Real.exp_le_exp.2
    rcases he with rfl | rfl <;>
      nlinarith only [sq_nonneg (Real.sqrt s * x - lambda / 2),
        sq_nonneg (Real.sqrt s * x + lambda / 2), hsq]
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    rcases he with rfl | rfl <;>
      nlinarith only [sq_nonneg (Real.sqrt s * x - lambda),
        sq_nonneg (Real.sqrt s * x + lambda), hsq]

private theorem smb_damped_mark_integrable
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (s : ℝ) (hs : 0 < s) :
    Integrable (fun z : ℝ => |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2)) nu := by
  have hroot : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  apply (h2.div_const (Real.sqrt s)).mono' (by fun_prop)
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hh := smb_gaussian_linear (Real.sqrt s * |z|)
    have he : -((Real.sqrt s * |z|) ^ 2) / 2 = -(s / 2) * z ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hs.le, sq_abs]; ring
    rw [he] at hh
    apply (le_div_iff₀ hroot).2
    have hp := mul_le_mul_of_nonneg_left hh (sq_nonneg z)
    convert hp using 1 <;> rw [← sq_abs z] <;> ring

private theorem smb_gaussian_factors_integrable
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (s lambda epsilon : ℝ) (hs : 0 < s)
    (he : epsilon = 1 ∨ epsilon = -1) :
    Integrable (fun z : ℝ =>
        Real.exp (-s * z ^ 2 + epsilon * lambda * Real.sqrt s * z)) nu ∧
      Integrable (fun z : ℝ => |z| ^ 3 *
        Real.exp (-s * z ^ 2 + epsilon * lambda * Real.sqrt s * z)) nu := by
  constructor
  · apply (integrable_const (Real.exp (lambda ^ 2 / 4))).mono' (by fun_prop)
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (smb_completed_square s lambda epsilon z hs he).1
  · apply ((smb_damped_mark_integrable nu h2 s hs).const_mul (Real.exp (lambda ^ 2 / 2))).mono'
      (by fun_prop)
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      convert mul_le_mul_of_nonneg_left (smb_completed_square s lambda epsilon z hs he).2
        (pow_nonneg (abs_nonneg z) 3) using 1 <;> ring

private theorem smb_exp_loss_square (u : ℝ) :
    0 ≤ 1 - Real.exp (-(u ^ 2)) ∧ 1 - Real.exp (-(u ^ 2)) ≤ |u| := by
  have hh : Real.exp (-(u ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (sq_nonneg u))
  refine ⟨sub_nonneg.2 hh, ?_⟩
  by_cases hu : |u| ≤ 1
  · have he := Real.one_sub_le_exp_neg (u ^ 2)
    have hs : u ^ 2 ≤ |u| := by nlinarith [sq_abs u, abs_nonneg u]
    linarith only [he, hs]
  · have hp := (Real.exp_pos (-(u ^ 2))).le
    have hu' : 1 ≤ |u| := le_of_not_ge hu
    linarith only [hp, hu']

private theorem smb_centered_damped_first
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0) (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (s : ℝ) (hs : 0 < s) :
    Integrable (fun z : ℝ => z * Real.exp (-s * z ^ 2)) nu ∧
      |∫ z : ℝ, z * Real.exp (-s * z ^ 2) ∂nu| ≤ Real.sqrt s := by
  have h1 : Integrable (fun z : ℝ => z) nu := by
    apply (h2.add (integrable_const 1)).mono' measurable_id.aestronglyMeasurable
    exact ae_of_all _ fun z => by
      change |z| ≤ z ^ 2 + 1
      nlinarith [sq_nonneg (|z| - 1), sq_abs z]
  have hi : Integrable (fun z : ℝ => z * Real.exp (-s * z ^ 2)) nu := by
    apply h1.abs.mono' (by fun_prop)
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg z]))
        (abs_nonneg z)).trans_eq (mul_one _)
  have hp (z : ℝ) : |z * Real.exp (-s * z ^ 2) - z| ≤ Real.sqrt s * z ^ 2 := by
    have he : -((Real.sqrt s * z) ^ 2) = -s * z ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hs.le]; ring
    have hl := smb_exp_loss_square (Real.sqrt s * z)
    rw [he] at hl
    calc
      _ = |z| * (1 - Real.exp (-s * z ^ 2)) := by
        rw [show z * Real.exp (-s * z ^ 2) - z = -z * (1 - Real.exp (-s * z ^ 2)) by ring,
          abs_mul, abs_neg, abs_of_nonneg hl.1]
      _ ≤ |z| * |Real.sqrt s * z| := mul_le_mul_of_nonneg_left hl.2 (abs_nonneg z)
      _ = _ := by rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg s), ← sq_abs z]; ring
  refine ⟨hi, ?_⟩
  have heq : (∫ z : ℝ, z * Real.exp (-s * z ^ 2) - z ∂nu) =
      ∫ z : ℝ, z * Real.exp (-s * z ^ 2) ∂nu := by rw [integral_sub hi h1, hmean, sub_zero]
  rw [← heq]
  calc
    _ ≤ ∫ z : ℝ, |z * Real.exp (-s * z ^ 2) - z| ∂nu := abs_integral_le_integral_abs
    _ ≤ ∫ z : ℝ, Real.sqrt s * z ^ 2 ∂nu :=
      integral_mono (hi.sub h1).abs (h2.const_mul _) hp
    _ = _ := by rw [integral_const_mul, hnorm, mul_one]

private theorem smb_cutoff_scalar_gap (u : ℝ) (hu : 0 ≤ u) (hu2 : u ≤ 2) :
    (2 / 5 : ℝ) * u ≤ 1 - Real.exp (-u) := by
  have hp : 1 + u + u ^ 2 / 2 ≤ Real.exp u := by
    have hh := Real.sum_le_exp_of_nonneg hu 3
    norm_num [Finset.sum_range_succ, Nat.factorial] at hh
    convert hh using 1 <;> ring
  have hfac : 0 ≤ u * (2 - u) * (2 * u + 3) := by positivity
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1 - (2 / 5 : ℝ) * u by linarith only [hu2])
  have hmul : 1 ≤ (1 - (2 / 5 : ℝ) * u) * Real.exp u := by nlinarith only [hm, hfac]
  have he : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  have hcalc : Real.exp u * Real.exp (-u) ≤ Real.exp u * (1 - (2 / 5 : ℝ) * u) := by
    calc
      Real.exp u * Real.exp (-u) = 1 := by rw [mul_comm]; exact he
      1 ≤ Real.exp u * (1 - (2 / 5 : ℝ) * u) := by simpa only [mul_comm] using hmul
  have hh : Real.exp (-u) ≤ 1 - (2 / 5 : ℝ) * u :=
    (mul_le_mul_iff_right₀ (Real.exp_pos u)).1 hcalc
  linarith only [hh]

private theorem smb_cutoff_laplace_gap
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (b s : ℝ) (hb : 0 < b) (hs : 0 < s) (hsb : s ≤ 2 / b)
    (hret : (1 / 2 : ℝ) ≤ ∫ z : ℝ, if z ^ 2 ≤ b then z ^ 2 else 0 ∂nu) :
    Integrable (fun z : ℝ => Real.exp (-s * z ^ 2)) nu ∧
      s / 5 ≤ 1 - ∫ z : ℝ, Real.exp (-s * z ^ 2) ∂nu := by
  have hi : Integrable (fun z : ℝ => Real.exp (-s * z ^ 2)) nu := by
    apply (integrable_const 1).mono' (by fun_prop)
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg z])
  have hri : Integrable (fun z : ℝ => if z ^ 2 ≤ b then z ^ 2 else 0) nu := by
    apply h2.mono' ((Measurable.ite (measurableSet_le (measurable_id.pow_const 2) measurable_const)
      (measurable_id.pow_const 2) measurable_const).aestronglyMeasurable)
    exact ae_of_all _ fun z => by split_ifs <;> simp [Real.norm_eq_abs, sq_nonneg]
  have hp (z : ℝ) : (2 / 5 : ℝ) * s * (if z ^ 2 ≤ b then z ^ 2 else 0) ≤
      1 - Real.exp (-s * z ^ 2) := by
    split_ifs with hz
    · have hsb' : s * b ≤ 2 := (le_div_iff₀ hb).1 hsb
      have hh := smb_cutoff_scalar_gap (s * z ^ 2) (mul_nonneg hs.le (sq_nonneg z))
        ((mul_le_mul_of_nonneg_left hz hs.le).trans hsb')
      simpa only [mul_assoc, neg_mul] using hh
    · simp only [mul_zero]
      exact sub_nonneg.2 (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg z]))
  have hh := integral_mono (hri.const_mul ((2 / 5 : ℝ) * s))
    ((integrable_const 1).sub hi) hp
  rw [integral_const_mul] at hh
  change (2 / 5 : ℝ) * s * (∫ z : ℝ, if z ^ 2 ≤ b then z ^ 2 else 0 ∂nu) ≤
    ∫ z : ℝ, 1 - Real.exp (-s * z ^ 2) ∂nu at hh
  rw [integral_sub (integrable_const 1) hi, integral_const, probReal_univ, one_smul] at hh
  refine ⟨hi, ?_⟩
  nlinarith only [hh, mul_le_mul_of_nonneg_left hret hs.le]

private theorem smb_gaussian_taylor
    (s lambda epsilon z : ℝ) (hs : 0 < s)
    (hl : 0 ≤ lambda) (hl1 : lambda ≤ 1 / 16)
    (he : epsilon = 1 ∨ epsilon = -1) :
    Real.exp (-s * z ^ 2 + epsilon * lambda * Real.sqrt s * z) ≤
      Real.exp (-s * z ^ 2) +
        (epsilon * lambda * Real.sqrt s) * (z * Real.exp (-s * z ^ 2)) +
          (2 * lambda ^ 2 * s) * z ^ 2 := by
  let v : ℝ := epsilon * lambda * Real.sqrt s * z
  have ht := mul_le_mul_of_nonneg_left (smb_exp_remainder v) (Real.exp_pos (-s * z ^ 2)).le
  have hvsq : v ^ 2 = lambda ^ 2 * s * z ^ 2 := by
    dsimp [v]
    rcases he with rfl | rfl <;> simp only [mul_pow, Real.sq_sqrt hs.le] <;> ring
  have hvabs : |v| = lambda * Real.sqrt s * |z| := by
    dsimp [v]
    rcases he with rfl | rfl <;>
      simp [abs_mul, abs_of_nonneg hl, abs_of_nonneg (Real.sqrt_nonneg s)]
  have hc : Real.exp (-s * z ^ 2 + |v|) ≤ 2 := by
    have hh := (smb_completed_square s lambda 1 |z| hs (Or.inl rfl)).1
    simp only [one_mul, sq_abs] at hh
    rw [hvabs]
    apply hh.trans
    calc
      _ ≤ Real.exp (1 / 4 : ℝ) := Real.exp_le_exp.2 (by nlinarith only [hl, hl1])
      _ ≤ 2 := by
        have h := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
        norm_num at h
        linarith only [h]
  have hr : Real.exp (-s * z ^ 2) * (v ^ 2 * Real.exp |v|) ≤ (2 * lambda ^ 2 * s) * z ^ 2 := by
    calc
      _ = (lambda ^ 2 * s * z ^ 2) * Real.exp (-s * z ^ 2 + |v|) := by rw [Real.exp_add, hvsq]; ring
      _ ≤ (lambda ^ 2 * s * z ^ 2) * 2 := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring
  rw [← Real.exp_add] at ht
  dsimp only [v] at ht
  nlinarith only [ht, hr]

theorem raw_gaussian_damped_coordinate_factors :
    let lambda : ℝ := (1 - Real.exp (-2)) / 16
    let c : ℝ := (1 - Real.exp (-2)) / 8
    0 < lambda ∧ 0 < c ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ (b s : ℝ), 0 < b → 0 < s → s ≤ 2 / b →
          let retained : ℝ := ∫ z : ℝ, if z ^ 2 ≤ b then z ^ 2 else 0 ∂nu
          let gamma : ℝ := if (1 / 2 : ℝ) ≤ retained then -c else 1
          let a3 : ℝ → ℝ := fun u => ∫ z : ℝ, |z| ^ 3 * Real.exp (-u * z ^ 2) ∂nu
          Integrable (fun z : ℝ => |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2)) nu ∧
            ∀ epsilon : ℝ, (epsilon = 1 ∨ epsilon = -1) →
              let weight : ℝ → ℝ := fun z =>
                Real.exp (-s * z ^ 2 + epsilon * lambda * Real.sqrt s * z)
              Integrable weight nu ∧ Integrable (fun z => |z| ^ 3 * weight z) nu ∧
                (∫ z : ℝ, weight z ∂nu) ≤ Real.exp (gamma * s) ∧
                (∫ z : ℝ, |z| ^ 3 * weight z ∂nu) ≤
                  Real.exp (lambda ^ 2 / 2) * a3 (s / 2) := by
  intro lambda c
  have he2 : Real.exp (-2 : ℝ) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hl : 0 < lambda := by dsimp [lambda]; linarith only [he2]
  have hl1 : lambda ≤ 1 / 16 := by dsimp [lambda]; linarith only [Real.exp_pos (-2 : ℝ)]
  have hc : c = 2 * lambda := by dsimp [c, lambda]; ring
  refine ⟨hl, by rw [hc]; positivity, ?_⟩
  intro nu hnu h2 hmean hnorm b s hb hs hsb retained gamma a3
  letI : IsProbabilityMeasure nu := hnu
  have h3 := smb_damped_mark_integrable nu h2 s hs
  refine ⟨h3, ?_⟩
  intro epsilon he weight
  have hwi := smb_gaussian_factors_integrable nu h2 s lambda epsilon hs he
  have hLi : Integrable (fun z : ℝ => Real.exp (-s * z ^ 2)) nu := by
    simpa only [mul_zero, zero_mul, add_zero] using
      (smb_gaussian_factors_integrable nu h2 s 0 1 hs (Or.inl rfl)).1
  have hgi := smb_centered_damped_first nu h2 hmean hnorm s hs
  let m1 : ℝ := ∫ z : ℝ, z * Real.exp (-s * z ^ 2) ∂nu
  have hEm : epsilon * m1 ≤ |m1| := by
    rcases he with rfl | rfl
    · simpa only [one_mul] using le_abs_self m1
    · simpa only [neg_one_mul] using neg_le_abs m1
  have hm : (epsilon * lambda * Real.sqrt s) * m1 ≤ lambda * s := by
    calc
      _ = (lambda * Real.sqrt s) * (epsilon * m1) := by ring
      _ ≤ (lambda * Real.sqrt s) * |m1| := mul_le_mul_of_nonneg_left hEm (by positivity)
      _ ≤ (lambda * Real.sqrt s) * Real.sqrt s :=
        mul_le_mul_of_nonneg_left hgi.2 (by positivity)
      _ = _ := by rw [mul_assoc, ← pow_two, Real.sq_sqrt hs.le]
  have hFi : Integrable (fun z : ℝ => Real.exp (-s * z ^ 2) +
      (epsilon * lambda * Real.sqrt s) * (z * Real.exp (-s * z ^ 2)) +
      (2 * lambda ^ 2 * s) * z ^ 2) nu :=
    (hLi.add (hgi.1.const_mul _)).add (h2.const_mul _)
  have hbnd := integral_mono hwi.1 hFi (smb_gaussian_taylor s lambda epsilon · hs hl.le hl1 he)
  rw [integral_add (f := fun z : ℝ => Real.exp (-s * z ^ 2) +
      (epsilon * lambda * Real.sqrt s) * (z * Real.exp (-s * z ^ 2)))
      (g := fun z : ℝ => (2 * lambda ^ 2 * s) * z ^ 2)
      (hLi.add (hgi.1.const_mul _)) (h2.const_mul _),
    integral_add (f := fun z : ℝ => Real.exp (-s * z ^ 2))
      (g := fun z : ℝ => (epsilon * lambda * Real.sqrt s) * (z * Real.exp (-s * z ^ 2)))
      hLi (hgi.1.const_mul _), integral_const_mul, integral_const_mul, hnorm, mul_one] at hbnd
  have hlin : (∫ z : ℝ, weight z ∂nu) ≤
      (∫ z : ℝ, Real.exp (-s * z ^ 2) ∂nu) + (lambda + 2 * lambda ^ 2) * s := by
    change (∫ z : ℝ, weight z ∂nu) ≤ _ at hbnd
    nlinarith only [hbnd, hm]
  refine ⟨hwi.1, hwi.2, ?_, ?_⟩
  · by_cases hret : (1 / 2 : ℝ) ≤ retained
    · have hg := (smb_cutoff_laplace_gap nu h2 b s hb hs hsb hret).2
      have hconst : lambda + 2 * lambda ^ 2 + c ≤ 1 / 5 := by
        rw [hc]
        nlinarith only [hl.le, hl1, mul_nonneg hl.le (sub_nonneg.2 hl1)]
      have hp : (∫ z : ℝ, weight z ∂nu) ≤ 1 - c * s := by
        nlinarith only [hlin, hg, mul_le_mul_of_nonneg_right hconst hs.le]
      change _ ≤ Real.exp ((if (1 / 2 : ℝ) ≤ retained then -c else 1) * s)
      rw [if_pos hret]
      exact hp.trans (by simpa only [neg_mul] using Real.one_sub_le_exp_neg (c * s))
    · have hL : (∫ z : ℝ, Real.exp (-s * z ^ 2) ∂nu) ≤ 1 := by
        have hh := integral_mono hLi (integrable_const 1) (fun z : ℝ =>
          Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg z]))
        simpa only [integral_const, probReal_univ, one_smul] using hh
      have hconst : lambda + 2 * lambda ^ 2 ≤ 1 := by
        nlinarith only [hl.le, hl1, mul_nonneg hl.le (sub_nonneg.2 hl1)]
      have hp : (∫ z : ℝ, weight z ∂nu) ≤ 1 + s := by
        nlinarith only [hlin, hL, mul_le_mul_of_nonneg_right hconst hs.le]
      change _ ≤ Real.exp ((if (1 / 2 : ℝ) ≤ retained then -c else 1) * s)
      rw [if_neg hret, one_mul]
      exact hp.trans (by linarith only [Real.add_one_le_exp s])
  · calc
      _ ≤ ∫ z : ℝ, Real.exp (lambda ^ 2 / 2) *
          (|z| ^ 3 * Real.exp (-(s / 2) * z ^ 2)) ∂nu := by
        apply integral_mono hwi.2 (h3.const_mul _)
        intro z
        convert mul_le_mul_of_nonneg_left (smb_completed_square s lambda epsilon z hs he).2
          (pow_nonneg (abs_nonneg z) 3) using 1 <;> ring
      _ = _ := integral_const_mul _ _

private theorem smb_raw_normalization
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂nu) :
    let scale : ℝ := Real.sqrt ((n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu))
    let eta : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
    0 < scale ∧ IsProbabilityMeasure eta ∧
      Integrable (fun z : ℝ => z ^ 2) eta ∧
      (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) = 1 ∧
      Integrable (fun z : ℝ => Shao.truncationF (z / scale)) nu ∧
      Shao.truncationBudget eta n 0 =
        (n : ℝ) * (∫ z : ℝ, Shao.truncationF (z / scale) ∂nu) := by
  intro scale eta
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < scale := Real.sqrt_pos.2 (mul_pos hN hsecond)
  have hs2 : scale ^ 2 = (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) := Real.sq_sqrt (by positivity)
  have hm : Measurable (fun z : ℝ => z / scale) := measurable_id.div_const scale
  have hp : IsProbabilityMeasure eta := by dsimp [eta]; infer_instance
  letI : IsProbabilityMeasure eta := hp
  have hi2 : Integrable (fun z : ℝ => z ^ 2) eta := by
    apply (integrable_map_measure (by fun_prop) hm.aemeasurable).2
    simpa only [Function.comp_def, div_pow] using h2.div_const (scale ^ 2)
  have he2 : (∫ z : ℝ, z ^ 2 ∂eta) = (∫ z : ℝ, z ^ 2 ∂nu) / scale ^ 2 := by
    rw [show eta = Measure.map (fun z : ℝ => z / scale) nu from rfl,
      integral_map hm.aemeasurable (by fun_prop)]
    simp_rw [div_pow]
    exact integral_div _ _
  have hF : Integrable (fun z : ℝ => Shao.truncationF (z / scale)) nu := by
    convert Shao.integrable_truncationF_mul nu h2 (1 / scale) using 1
    funext z
    congr 1
    ring
  refine ⟨hs, hp, hi2, ?_, hF, ?_⟩
  · rw [he2, hs2]; field_simp
  · unfold Shao.truncationBudget
    simp only [add_zero, one_mul]
    rw [show eta = Measure.map (fun z : ℝ => z / scale) nu from rfl,
      integral_map hm.aemeasurable Shao.continuous_truncationF.aestronglyMeasurable]

private theorem smb_budget_tangent (z b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    b * z ^ 2 ≤ Shao.truncationF z + b ^ 3 := by
  by_cases hz : b ≤ |z|
  · have hh : b ≤ min |z| 1 := le_min hz hb1
    have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg z)
    have hb3 : 0 ≤ b ^ 3 := pow_nonneg hb 3
    dsimp [Shao.truncationF]
    nlinarith only [hm, hb3]
  · have hsq : z ^ 2 ≤ b ^ 2 := by
      have hh : |z| ≤ b := le_of_not_ge hz
      nlinarith [sq_abs z, abs_nonneg z]
    have hm := mul_le_mul_of_nonneg_left hsq hb
    have hF := Shao.truncationF_nonneg z
    nlinarith only [hm, hF]

private theorem smb_normalized_budget_bounds
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1) :
    let R : ℝ := Shao.truncationBudget nu n 0
    0 < R ∧ R ≤ 1 ∧ 1 / (2 * Real.sqrt (2 * (n : ℝ))) ≤ R ∧
      (1 / 2 : ℝ) ≤ 4 * (n : ℝ) * R ^ 2 := by
  intro R
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let b : ℝ := 1 / Real.sqrt (2 * (n : ℝ))
  have ht : 0 < Real.sqrt (2 * (n : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have ht2 : Real.sqrt (2 * (n : ℝ)) ^ 2 = 2 * (n : ℝ) := Real.sq_sqrt (by positivity)
  have ht1 : 1 ≤ Real.sqrt (2 * (n : ℝ)) := by nlinarith only [ht2, ht.le, hN1]
  have hb : 0 < b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by dsimp [b]; exact (div_le_iff₀ ht).2 (by simpa using ht1)
  have hb2 : (n : ℝ) * b ^ 2 = 1 / 2 := by
    dsimp [b]
    rw [div_pow, ht2]
    field_simp
  have hb3 : (n : ℝ) * b ^ 3 = b / 2 := by
    calc
      _ = ((n : ℝ) * b ^ 2) * b := by ring
      _ = b / 2 := by rw [hb2]; ring
  have hFi : Integrable Shao.truncationF nu := by
    simpa only [one_mul] using Shao.integrable_truncationF_mul nu h2 1
  have hRf : R = (n : ℝ) * (∫ z : ℝ, Shao.truncationF z ∂nu) := by
    simp only [R, Shao.truncationBudget, add_zero, one_mul]
  have hi := integral_mono (h2.const_mul b) (hFi.add (integrable_const (b ^ 3)))
    (fun z => smb_budget_tangent z b hb.le hb1)
  rw [integral_const_mul] at hi
  change b * (∫ z : ℝ, z ^ 2 ∂nu) ≤ ∫ z : ℝ, Shao.truncationF z + b ^ 3 ∂nu at hi
  rw [integral_add (f := Shao.truncationF) (g := fun _ : ℝ => b ^ 3) hFi (integrable_const _),
    integral_const, probReal_univ, one_smul] at hi
  have hlow : b / 2 ≤ R := by
    have hh := mul_le_mul_of_nonneg_left hi hN.le
    have hh' : b ≤ R + b / 2 := by
      calc
        b = (n : ℝ) * (b * (∫ z : ℝ, z ^ 2 ∂nu)) := by rw [mul_left_comm, hnorm, mul_one]
        _ ≤ (n : ℝ) * ((∫ z : ℝ, Shao.truncationF z ∂nu) + b ^ 3) := hh
        _ = _ := by rw [mul_add, ← hRf, hb3]
    linarith only [hh']
  have hRpos : 0 < R := (half_pos hb).trans_le hlow
  have hupper : R ≤ 1 := by
    have hh := integral_mono hFi h2 Shao.truncationF_le_sq
    have hmul := mul_le_mul_of_nonneg_left hh hN.le
    rwa [← hRf, hnorm] at hmul
  refine ⟨hRpos, hupper, ?_, ?_⟩
  · convert hlow using 1 <;> dsimp [b] <;> ring
  · have hh := (sq_le_sq₀ (half_pos hb).le hRpos.le).2 hlow
    have hm := mul_le_mul_of_nonneg_left hh hN.le
    nlinarith only [hm, hb2]

private theorem smb_normalized_retained_energy
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (H : ℝ) (hR : Shao.truncationBudget nu n 0 ≤ 1 / 2)
    (hH : 4 * Shao.truncationBudget nu n 0 ^ 2 ≤ H) :
    Integrable (fun z : ℝ => if z ^ 2 ≤ H then z ^ 2 else 0) nu ∧
      (1 / 2 : ℝ) ≤ (n : ℝ) * (∫ z : ℝ, if z ^ 2 ≤ H then z ^ 2 else 0 ∂nu) := by
  let R : ℝ := Shao.truncationBudget nu n 0
  have hRp : 0 < R := (smb_normalized_budget_bounds nu n hn h2 hnorm).1
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  let tail : ℝ → ℝ := fun z => if H < z ^ 2 then z ^ 2 else 0
  let ret : ℝ → ℝ := fun z => if z ^ 2 ≤ H then z ^ 2 else 0
  have hti : Integrable tail nu := by
    apply h2.mono' ((Measurable.ite
      (measurableSet_lt measurable_const (measurable_id.pow_const 2))
      (measurable_id.pow_const 2) measurable_const).aestronglyMeasurable)
    exact ae_of_all _ fun z => by dsimp [tail]; split_ifs <;> simp [Real.norm_eq_abs, sq_nonneg]
  have hri : Integrable ret nu := by
    apply h2.mono' ((Measurable.ite
      (measurableSet_le (measurable_id.pow_const 2) measurable_const)
      (measurable_id.pow_const 2) measurable_const).aestronglyMeasurable)
    exact ae_of_all _ fun z => by dsimp [ret]; split_ifs <;> simp [Real.norm_eq_abs, sq_nonneg]
  have hp (z : ℝ) : (2 * R) * tail z ≤ Shao.truncationF z := by
    dsimp [tail]
    split_ifs with hz
    · have ha : 2 * R ≤ |z| := by nlinarith only [hz, hH, hRp, abs_nonneg z, sq_abs z]
      have hm : 2 * R ≤ min |z| 1 := le_min ha (by change R ≤ 1 / 2 at hR; linarith only [hR])
      unfold Shao.truncationF
      nlinarith only [mul_le_mul_of_nonneg_left hm (sq_nonneg z)]
    · simpa only [mul_zero] using Shao.truncationF_nonneg z
  have hFi : Integrable Shao.truncationF nu := by
    simpa only [one_mul] using Shao.integrable_truncationF_mul nu h2 1
  have hh := integral_mono (hti.const_mul (2 * R)) hFi hp
  rw [integral_const_mul] at hh
  have hRf : R = (n : ℝ) * (∫ z : ℝ, Shao.truncationF z ∂nu) := by
    simp only [R, Shao.truncationBudget, add_zero, one_mul]
  have htp : (n : ℝ) * (∫ z : ℝ, tail z ∂nu) ≤ 1 / 2 := by
    have hm := mul_le_mul_of_nonneg_left hh hN.le
    nlinarith only [hm, hRf, hRp]
  have hsum : (∫ z : ℝ, ret z ∂nu) + (∫ z : ℝ, tail z ∂nu) = ∫ z : ℝ, z ^ 2 ∂nu := by
    rw [← integral_add hri hti]
    apply integral_congr_ae
    exact ae_of_all _ fun z => by dsimp [ret, tail]; split_ifs <;> simp_all <;> linarith
  refine ⟨hri, ?_⟩
  change (1 / 2 : ℝ) ≤ (n : ℝ) * (∫ z : ℝ, ret z ∂nu)
  nlinarith only [hsum, hnorm, htp]

private theorem smb_raw_budget_comparison
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n r : ℕ)
    (hn : 0 < n) (hr : 0 < r) (hrn : r ≤ n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂nu) :
    let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂nu
    let etaN : Measure ℝ := Measure.map (fun z : ℝ => z / Real.sqrt ((n : ℝ) * sigmaSq)) nu
    let etaR : Measure ℝ := Measure.map (fun z : ℝ => z / Real.sqrt ((r : ℝ) * sigmaSq)) nu
    Shao.truncationBudget etaR r 0 ≤
      Real.sqrt ((n : ℝ) / (r : ℝ)) * Shao.truncationBudget etaN n 0 := by
  intro sigmaSq etaN etaR
  let sn : ℝ := Real.sqrt ((n : ℝ) * sigmaSq)
  let sr : ℝ := Real.sqrt ((r : ℝ) * sigmaSq)
  let c : ℝ := sn / sr
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnr : (r : ℝ) ≤ n := by exact_mod_cast hrn
  have hSigma : 0 < sigmaSq := hsecond
  have hsn : 0 < sn := Real.sqrt_pos.2 (mul_pos hN hsecond)
  have hsr : 0 < sr := Real.sqrt_pos.2 (mul_pos hrr hsecond)
  have hsn2 : sn ^ 2 = (n : ℝ) * sigmaSq := Real.sq_sqrt (by positivity)
  have hsr2 : sr ^ 2 = (r : ℝ) * sigmaSq := Real.sq_sqrt (by positivity)
  have hle : sr ≤ sn := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hnr hsecond.le)
  have hc : 1 ≤ c := (le_div_iff₀ hsr).2 (by simpa only [one_mul] using hle)
  have hc2 : c ^ 2 = (n : ℝ) / (r : ℝ) := by
    dsimp [c]
    rw [div_pow, hsn2, hsr2]
    field_simp [hSigma.ne']
  have hcn : (r : ℝ) * c ^ 2 = (n : ℝ) := by rw [hc2]; field_simp
  have hcroot : c = Real.sqrt ((n : ℝ) / (r : ℝ)) := by
    have hh := Real.sq_sqrt (div_nonneg hN.le hrr.le)
    nlinarith only [hc2, hh, Real.sqrt_nonneg ((n : ℝ) / (r : ℝ)), hc]
  have dn := smb_raw_normalization nu n hn h2 hsecond
  have dr := smb_raw_normalization nu r hr h2 hsecond
  have hf (z : ℝ) : Shao.truncationF (z / sr) ≤ c ^ 3 * Shao.truncationF (z / sn) := by
    have he : c * (z / sn) = z / sr := by dsimp [c]; field_simp
    simpa only [he] using (Shao.truncationF_scale_one_le c (z / sn) hc).2
  have hi := integral_mono dr.2.2.2.2.1 (dn.2.2.2.2.1.const_mul (c ^ 3)) hf
  rw [integral_const_mul] at hi
  calc
    _ = (r : ℝ) * (∫ z : ℝ, Shao.truncationF (z / sr) ∂nu) := dr.2.2.2.2.2
    _ ≤ (r : ℝ) * (c ^ 3 * (∫ z : ℝ, Shao.truncationF (z / sn) ∂nu)) :=
      mul_le_mul_of_nonneg_left hi hrr.le
    _ = c * ((n : ℝ) * (∫ z : ℝ, Shao.truncationF (z / sn) ∂nu)) := by
      calc
        _ = ((r : ℝ) * c ^ 2) * c * (∫ z : ℝ, Shao.truncationF (z / sn) ∂nu) := by ring
        _ = _ := by rw [hcn]; ring
    _ = _ := by rw [hcroot, ← dn.2.2.2.2.2]

theorem raw_truncation_budget_suffix_geometry
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂nu) :
    let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂nu
    let scale : ℝ := Real.sqrt ((n : ℝ) * sigmaSq)
    let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
    let R : ℝ := Shao.truncationBudget normalizedLaw n 0
    let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
    let Rprefix : ℕ → ℝ := fun r =>
      Shao.truncationBudget
        (Measure.map (fun z : ℝ => z / Real.sqrt ((r : ℝ) * sigmaSq)) nu) r 0
    0 < R ∧ R ≤ 1 ∧ 1 / (2 * Real.sqrt (2 * (n : ℝ))) ≤ R ∧
      0 < h ∧ sigmaSq / 2 ≤ h ∧
      (∀ r : ℕ, 0 < r → r ≤ n →
        Rprefix r ≤ Real.sqrt ((n : ℝ) / (r : ℝ)) * R) ∧
      (R ≤ 1 / 2 → sigmaSq / 2 ≤
        ∫ z : ℝ, if z ^ 2 ≤ h then z ^ 2 else 0 ∂nu) := by
  intro sigmaSq scale normalizedLaw R h Rprefix
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hd := smb_raw_normalization nu n hn h2 hsecond
  letI : IsProbabilityMeasure normalizedLaw := hd.2.1
  have hs : 0 < scale := hd.1
  have hs2 : scale ^ 2 = (n : ℝ) * sigmaSq := Real.sq_sqrt (by positivity)
  have hnb := smb_normalized_budget_bounds normalizedLaw n hn hd.2.2.1 hd.2.2.2.1
  have hRp : 0 < R := hnb.1
  have hSigma : 0 < sigmaSq := hsecond
  have hhalf : sigmaSq / 2 ≤ h := by
    dsimp only [h]
    nlinarith only [mul_le_mul_of_nonneg_left hnb.2.2.2 hsecond.le]
  refine ⟨hnb.1, hnb.2.1, hnb.2.2.1, by dsimp [h]; positivity, hhalf, ?_, ?_⟩
  · intro r hr hrn
    exact smb_raw_budget_comparison nu n r hn hr hrn h2 hsecond
  · intro hR
    have hret := (smb_normalized_retained_energy normalizedLaw n hn hd.2.2.1 hd.2.2.2.1
      (4 * R ^ 2) hR le_rfl).2
    have hm : Measurable (fun z : ℝ => z / scale) := measurable_id.div_const scale
    have hretm : Measurable (fun z : ℝ => if z ^ 2 ≤ 4 * R ^ 2 then z ^ 2 else 0) :=
      Measurable.ite (measurableSet_le (measurable_id.pow_const 2) measurable_const)
        (measurable_id.pow_const 2) measurable_const
    have he : (∫ z : ℝ, if z ^ 2 ≤ 4 * R ^ 2 then z ^ 2 else 0 ∂normalizedLaw) =
        (∫ z : ℝ, if z ^ 2 ≤ h then z ^ 2 else 0 ∂nu) / scale ^ 2 := by
      rw [show normalizedLaw = Measure.map (fun z : ℝ => z / scale) nu from rfl,
        integral_map hm.aemeasurable hretm.aestronglyMeasurable, ← integral_div]
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        have hc : (z / scale) ^ 2 ≤ 4 * R ^ 2 ↔ z ^ 2 ≤ h := by
          rw [div_pow, div_le_iff₀ (pow_pos hs 2), hs2]
          dsimp [h]
          constructor <;> intro hh <;> nlinarith only [hh]
        have hc' : z ^ 2 / scale ^ 2 ≤ 4 * R ^ 2 ↔ z ^ 2 ≤ h := by simpa only [div_pow] using hc
        by_cases hz : z ^ 2 ≤ h <;> simp only [div_pow, hc', hz, ite_true, ite_false, zero_div]
    rw [he] at hret
    have hid : (n : ℝ) *
        ((∫ z : ℝ, if z ^ 2 ≤ h then z ^ 2 else 0 ∂nu) / scale ^ 2) =
        (∫ z : ℝ, if z ^ 2 ≤ h then z ^ 2 else 0 ∂nu) / sigmaSq := by
      rw [hs2]
      field_simp [hN.ne', hSigma.ne']
    rw [hid] at hret
    have hh := (le_div_iff₀ hsecond).1 hret
    linarith only [hh]

private theorem smb_marked_exponential_product
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (m : ℕ) (s lambda epsilon : ℝ) (hs : 0 < s)
    (he : epsilon = 1 ∨ epsilon = -1) :
    let w : ℝ → ℝ := fun z => Real.exp (-s * z ^ 2 + epsilon * lambda * Real.sqrt s * z)
    let f : Shao.Path (m + 1) → ℝ := fun v => |v 0| ^ 3 *
      Real.exp (-s * Shao.energy v + epsilon * lambda * Real.sqrt s * Shao.prefixSum v (m + 1))
    Integrable f (Measure.pi (fun _ : Fin (m + 1) => nu)) ∧
      (∫ v, f v ∂Measure.pi (fun _ : Fin (m + 1) => nu)) =
        (∫ z : ℝ, |z| ^ 3 * w z ∂nu) * (∫ z : ℝ, w z ∂nu) ^ m := by
  intro w f
  let g : Fin (m + 1) → ℝ → ℝ := fun i z => if i = 0 then |z| ^ 3 * w z else w z
  have hi := smb_gaussian_factors_integrable nu h2 s lambda epsilon hs he
  have hgi (i : Fin (m + 1)) : Integrable (g i) nu := by
    dsimp [g]
    split_ifs
    · exact hi.2
    · exact hi.1
  have hprod (v : Shao.Path (m + 1)) : (∏ i : Fin (m + 1), g i (v i)) = f v := by
    calc
      _ = |v 0| ^ 3 * (∏ i : Fin (m + 1), w (v i)) := by
        rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
        simp only [g, ite_true, Fin.succ_ne_zero, ite_false]
        ring
      _ = _ := by
        dsimp [f, w]
        congr 1
        rw [← Real.exp_sum]
        congr 1
        simp only [Shao.energy, Shao.prefixSum_length, Finset.mul_sum, Finset.sum_add_distrib]
  have hp : Integrable (fun v : Shao.Path (m + 1) => ∏ i : Fin (m + 1), g i (v i))
      (Measure.pi (fun _ : Fin (m + 1) => nu)) := Integrable.fintype_prod hgi
  refine ⟨hp.congr (ae_of_all _ hprod), ?_⟩
  calc
    _ = ∫ v : Shao.Path (m + 1), ∏ i : Fin (m + 1), g i (v i)
        ∂Measure.pi (fun _ : Fin (m + 1) => nu) := by
      exact integral_congr_ae (ae_of_all _ fun v => (hprod v).symm)
    _ = ∏ i : Fin (m + 1), ∫ z : ℝ, g i z ∂nu := integral_fintype_prod_eq_prod g
    _ = _ := by
      rw [Fin.prod_univ_succ]
      simp only [g, ite_true, Fin.succ_ne_zero, ite_false, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem smb_polynomial_two_exponentials
    (p : ℕ) (lambda u : ℝ) (hl : 0 < lambda) :
    |u| ^ p ≤ ((p.factorial : ℝ) / lambda ^ p) *
      (Real.exp (lambda * u) + Real.exp (-lambda * u)) := by
  have hfac : 0 < (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos p
  have hh := (div_le_iff₀ hfac).1 (Real.pow_div_factorial_le_exp (lambda * |u|)
    (mul_nonneg hl.le (abs_nonneg u)) p)
  have he : Real.exp (lambda * |u|) ≤ Real.exp (lambda * u) + Real.exp (-lambda * u) := by
    by_cases hu : 0 ≤ u
    · rw [abs_of_nonneg hu]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_nonpos (le_of_not_ge hu)]
      have heq : lambda * -u = -lambda * u := by ring
      rw [heq]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  calc
    _ ≤ (Real.exp (lambda * |u|) * (p.factorial : ℝ)) / lambda ^ p := by
      apply (le_div_iff₀ (pow_pos hl p)).2
      simpa only [mul_pow, mul_comm] using hh
    _ = ((p.factorial : ℝ) / lambda ^ p) * Real.exp (lambda * |u|) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

private theorem smb_sqrt_pow_inverse
    (s : ℝ) (hs : 0 < s) (p : ℕ) :
    1 / (Real.sqrt s) ^ p = Real.rpow s (-(p : ℝ) / 2) := by
  rw [Real.rpow_eq_pow, Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hs.le, one_div]
  rw [show -(p : ℝ) / 2 = -((1 / 2 : ℝ) * (p : ℝ)) by ring, Real.rpow_neg hs.le]

private theorem smb_scaled_polynomial_exponentials
    (p : ℕ) (lambda s d : ℝ) (hl : 0 < lambda) (hs : 0 < s) :
    |d| ^ p ≤ ((p.factorial : ℝ) / lambda ^ p) * Real.rpow s (-(p : ℝ) / 2) *
      (Real.exp (lambda * Real.sqrt s * d) + Real.exp (-lambda * Real.sqrt s * d)) := by
  have hh := smb_polynomial_two_exponentials p lambda (Real.sqrt s * d) hl
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg s), mul_pow] at hh
  have hroot : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  calc
    _ ≤ (((p.factorial : ℝ) / lambda ^ p) *
        (Real.exp (lambda * Real.sqrt s * d) + Real.exp (-lambda * Real.sqrt s * d))) /
        (Real.sqrt s) ^ p := by
      apply (le_div_iff₀ (pow_pos hroot p)).2
      simpa only [mul_assoc, mul_comm (Real.sqrt s ^ p)] using hh
    _ = _ := by rw [← smb_sqrt_pow_inverse s hs p]; ring

theorem iid_marked_gaussian_damped_moments :
    let c : ℝ := (1 - Real.exp (-2)) / 8
    ∀ p : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ (m : ℕ) (b s : ℝ), 0 < b → 0 < s → s ≤ 2 / b →
          let P : Measure (Shao.Path (m + 1)) := Measure.pi (fun _ : Fin (m + 1) => nu)
          let T : Shao.Path (m + 1) → ℝ := Shao.energy
          let d : Shao.Path (m + 1) → ℝ := fun v => Shao.prefixSum v (m + 1)
          let M : Shao.Path (m + 1) → ℝ := fun v => |v 0| ^ 3
          let a3 : ℝ → ℝ := fun u => ∫ z : ℝ, |z| ^ 3 * Real.exp (-u * z ^ 2) ∂nu
          let retained : ℝ := ∫ z : ℝ, if z ^ 2 ≤ b then z ^ 2 else 0 ∂nu
          let gamma : ℝ := if (1 / 2 : ℝ) ≤ retained then -c else 1
          Integrable (fun v => M v * |d v| ^ p * Real.exp (-s * T v)) P ∧
            (∫ v, M v * |d v| ^ p * Real.exp (-s * T v) ∂P) ≤
              C * Real.rpow s (-(p : ℝ) / 2) * a3 (s / 2) *
                Real.exp (gamma * s * (m : ℝ)) := by
  intro c p
  let lambda : ℝ := (1 - Real.exp (-2)) / 16
  have hl : 0 < lambda := raw_gaussian_damped_coordinate_factors.1
  have hfac : 0 < (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos p
  let C : ℝ := 2 * ((p.factorial : ℝ) / lambda ^ p) * Real.exp (lambda ^ 2 / 2)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro nu hnu h2 hmean hnorm m b s hb hs hsb P T d M a3 retained gamma
  letI : IsProbabilityMeasure nu := hnu
  let J : ℝ → Shao.Path (m + 1) → ℝ := fun epsilon v =>
    M v * Real.exp (-s * T v + epsilon * lambda * Real.sqrt s * d v)
  let A : ℝ := ((p.factorial : ℝ) / lambda ^ p) * Real.rpow s (-(p : ℝ) / 2)
  let B : ℝ := Real.exp (lambda ^ 2 / 2) * a3 (s / 2) * Real.exp (gamma * s * (m : ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hJ (epsilon : ℝ) (he : epsilon = 1 ∨ epsilon = -1) : Integrable (J epsilon) P :=
    (smb_marked_exponential_product nu h2 m s lambda epsilon hs he).1
  have hpoint (v : Shao.Path (m + 1)) :
      M v * |d v| ^ p * Real.exp (-s * T v) ≤ A * (J 1 v + J (-1) v) := by
    have hh := smb_scaled_polynomial_exponentials p lambda s (d v) hl hs
    calc
      _ = (M v * Real.exp (-s * T v)) * |d v| ^ p := by ring
      _ ≤ (M v * Real.exp (-s * T v)) * (A *
          (Real.exp (lambda * Real.sqrt s * d v) + Real.exp (-lambda * Real.sqrt s * d v))) :=
        mul_le_mul_of_nonneg_left hh (by dsimp [M]; positivity)
      _ = _ := by dsimp [J]; simp only [one_mul, neg_one_mul, Real.exp_add]; ring
  have hboundI : Integrable (fun v => A * (J 1 v + J (-1) v)) P :=
    ((hJ 1 (Or.inl rfl)).add (hJ (-1) (Or.inr rfl))).const_mul A
  have hfmeas : Measurable (fun v : Shao.Path (m + 1) => M v * |d v| ^ p * Real.exp (-s * T v)) :=
    (((continuous_abs.measurable.comp (measurable_pi_apply (X := fun _ : Fin (m + 1) => ℝ) 0)).pow_const 3).mul
      ((continuous_abs.measurable.comp (Shao.measurable_prefixSum (m + 1))).pow_const p)).mul
        ((measurable_const.mul Shao.measurable_energy).exp)
  have hfi : Integrable (fun v => M v * |d v| ^ p * Real.exp (-s * T v)) P := by
    apply hboundI.mono' hfmeas.aestronglyMeasurable
    exact ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [M]; positivity)]
      exact hpoint v
  have hraw := raw_gaussian_damped_coordinate_factors.2.2 nu h2 hmean hnorm b s hb hs hsb
  have hJbound (epsilon : ℝ) (he : epsilon = 1 ∨ epsilon = -1) : (∫ v, J epsilon v ∂P) ≤ B := by
    have hd := hraw.2 epsilon he
    have hz : 0 ≤ ∫ z : ℝ, Real.exp (-s * z ^ 2 + epsilon * lambda * Real.sqrt s * z) ∂nu :=
      integral_nonneg fun _ => (Real.exp_pos _).le
    have ha : 0 ≤ a3 (s / 2) := integral_nonneg fun z => by positivity
    have hp := pow_le_pow_left₀ hz hd.2.2.1 m
    have hexp : (Real.exp (gamma * s)) ^ m = Real.exp (gamma * s * (m : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc
      _ = (∫ z : ℝ, |z| ^ 3 * Real.exp (-s * z ^ 2 + epsilon * lambda * Real.sqrt s * z) ∂nu) *
          (∫ z : ℝ, Real.exp (-s * z ^ 2 + epsilon * lambda * Real.sqrt s * z) ∂nu) ^ m :=
        (smb_marked_exponential_product nu h2 m s lambda epsilon hs he).2
      _ ≤ (Real.exp (lambda ^ 2 / 2) * a3 (s / 2)) * (Real.exp (gamma * s)) ^ m :=
        mul_le_mul hd.2.2.2 hp (pow_nonneg hz m) (mul_nonneg (Real.exp_pos _).le ha)
      _ = _ := by rw [hexp]
  refine ⟨hfi, ?_⟩
  have hi := integral_mono hfi hboundI hpoint
  rw [integral_const_mul, integral_add (hJ 1 (Or.inl rfl)) (hJ (-1) (Or.inr rfl))] at hi
  calc
    _ ≤ A * ((∫ v, J 1 v ∂P) + (∫ v, J (-1) v ∂P)) := hi
    _ ≤ A * (B + B) := mul_le_mul_of_nonneg_left
      (add_le_add (hJbound 1 (Or.inl rfl)) (hJbound (-1) (Or.inr rfl))) hA
    _ = _ := by dsimp [A, B, C]; ring

private theorem smb_gamma_kernel (alpha rate : ℝ) (ha : 0 < alpha) (hr : 0 < rate) :
    IntegrableOn (fun s : ℝ => Real.rpow s (alpha - 1) * Real.exp (-rate * s)) (Set.Ioi 0) ∧
      (∫ s : ℝ in Set.Ioi 0, Real.rpow s (alpha - 1) * Real.exp (-rate * s)) =
        Real.rpow (1 / rate) alpha * Real.Gamma alpha := by
  simp only [Real.rpow_eq_pow]
  constructor
  · simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := alpha - 1) (b := rate)
        (by linarith only [ha]) (by norm_num) hr
  · simpa only [neg_mul] using Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr

private theorem smb_gamma_half (rate : ℝ) (hr : 0 < rate) :
    IntegrableOn (fun s : ℝ => Real.rpow s (-1 / 2 : ℝ) * Real.exp (-rate * s)) (Set.Ioi 0) ∧
      (∫ s : ℝ in Set.Ioi 0, Real.rpow s (-1 / 2 : ℝ) * Real.exp (-rate * s)) =
        Real.Gamma (1 / 2) / Real.sqrt rate := by
  have hh := smb_gamma_kernel (1 / 2) rate (by norm_num) hr
  simp only [neg_div] at *
  norm_num only [show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num] at hh
  refine ⟨hh.1, ?_⟩
  rw [hh.2, Real.rpow_eq_pow, ← Real.sqrt_eq_rpow,
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  ring

private theorem smb_gamma_three_halves (rate : ℝ) (hr : 0 < rate) :
    IntegrableOn (fun s : ℝ => Real.rpow s (1 / 2 : ℝ) * Real.exp (-rate * s)) (Set.Ioi 0) ∧
      (∫ s : ℝ in Set.Ioi 0, Real.rpow s (1 / 2 : ℝ) * Real.exp (-rate * s)) =
        Real.Gamma (3 / 2) / (rate * Real.sqrt rate) := by
  have hh := smb_gamma_kernel (3 / 2) rate (by norm_num) hr
  norm_num only [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] at hh
  refine ⟨hh.1, ?_⟩
  rw [hh.2, Real.rpow_eq_pow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add (by positivity), Real.rpow_one, ← Real.sqrt_eq_rpow,
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  ring

private theorem smb_half_power_small (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => Real.rpow s (-1 / 2 : ℝ)) (Set.Ioo 0 a) ∧
      (∫ s : ℝ in Set.Ioo 0 a, Real.rpow s (-1 / 2 : ℝ)) = 2 * Real.sqrt a := by
  simp only [Real.rpow_eq_pow]
  have hi : IntervalIntegrable (fun s : ℝ => s ^ (-1 / 2 : ℝ)) volume 0 a :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hio : IntegrableOn (fun s : ℝ => s ^ (-1 / 2 : ℝ)) (Set.Ioc 0 a) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).1 hi
  refine ⟨hio.mono_set Set.Ioo_subset_Ioc_self, ?_⟩
  have he := integral_rpow (a := 0) (b := a) (r := (-1 / 2 : ℝ)) (Or.inl (by norm_num))
  rw [intervalIntegral.integral_of_le ha.le, integral_Ioc_eq_integral_Ioo] at he
  convert he using 1 <;> norm_num [Real.sqrt_eq_rpow] <;> ring

private theorem smb_scaled_budget_integrand (N z : ℝ) (hN : 0 < N) :
    N * Shao.truncationF (z / Real.sqrt N) =
      z ^ 2 * min (|z| / Real.sqrt N) 1 := by
  have ht : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  unfold Shao.truncationF
  rw [div_pow, Real.sq_sqrt hN.le, abs_div, abs_of_pos ht]
  field_simp

private theorem smb_marked_half_kernel (z : ℝ) (hz : z ≠ 0) :
    IntegrableOn (fun s : ℝ => Real.rpow s (-1 / 2 : ℝ) * |z| ^ 3 *
      Real.exp (-(s / 2) * z ^ 2)) (Set.Ioi 0) ∧
      (∫ s : ℝ in Set.Ioi 0, Real.rpow s (-1 / 2 : ℝ) * |z| ^ 3 *
        Real.exp (-(s / 2) * z ^ 2)) =
        Real.sqrt 2 * Real.Gamma (1 / 2) * z ^ 2 := by
  have hp : 0 < z ^ 2 / 2 := div_pos (sq_pos_of_ne_zero hz) (by norm_num)
  have hg := smb_gamma_half (z ^ 2 / 2) hp
  have he (s : ℝ) : Real.rpow s (-1 / 2 : ℝ) * |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2) =
      |z| ^ 3 * (Real.rpow s (-1 / 2 : ℝ) * Real.exp (-(z ^ 2 / 2) * s)) := by
    rw [show -(s / 2) * z ^ 2 = -(z ^ 2 / 2) * s by ring]
    ring
  have hf : (fun s : ℝ => Real.rpow s (-1 / 2 : ℝ) * |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2)) =
      fun s => |z| ^ 3 * (Real.rpow s (-1 / 2 : ℝ) * Real.exp (-(z ^ 2 / 2) * s)) := funext he
  rw [hf]
  refine ⟨hg.1.const_mul _, ?_⟩
  rw [integral_const_mul, hg.2, Real.sqrt_div (sq_nonneg z), Real.sqrt_sq_eq_abs]
  have ha : |z| ≠ 0 := abs_ne_zero.2 hz
  field_simp [ha]
  rw [← sq_abs z]

private theorem smb_low_scalar_kernel :
    ∃ C : ℝ, 0 < C ∧ ∀ (N z : ℝ), 0 < N →
      IntegrableOn (fun s : ℝ => Real.rpow s (-1 / 2 : ℝ) * |z| ^ 3 *
        Real.exp (-(s / 2) * z ^ 2)) (Set.Ioo 0 (1 / N)) ∧
        (∫ s : ℝ in Set.Ioo 0 (1 / N), Real.rpow s (-1 / 2 : ℝ) * |z| ^ 3 *
          Real.exp (-(s / 2) * z ^ 2)) ≤ C * (N * Shao.truncationF (z / Real.sqrt N)) := by
  let C : ℝ := 2 + 2 * Real.Gamma (1 / 2)
  have hG : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N z hN
  have ht : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  let k : ℝ → ℝ := fun s => Real.rpow s (-1 / 2 : ℝ) * |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2)
  have hp := smb_half_power_small (1 / N) (by positivity)
  have hk : IntegrableOn k (Set.Ioo 0 (1 / N)) := by
    apply (hp.1.mul_const (|z| ^ 3)).mono' (by dsimp [k]; fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hs0 : 0 ≤ s := hs.1.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [k]; positivity)]
    have he : Real.exp (-(s / 2) * z ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg z])
    have hfac : 0 ≤ Real.rpow s (-1 / 2 : ℝ) * |z| ^ 3 :=
      mul_nonneg (Real.rpow_nonneg hs0 _) (pow_nonneg (abs_nonneg z) 3)
    exact (mul_le_mul_of_nonneg_left he hfac).trans_eq (mul_one _)
  refine ⟨hk, ?_⟩
  change (∫ s : ℝ in Set.Ioo 0 (1 / N), k s) ≤ _
  rw [smb_scaled_budget_integrand N z hN]
  by_cases hz : |z| ≤ Real.sqrt N
  · have hmin : min (|z| / Real.sqrt N) 1 = |z| / Real.sqrt N :=
      min_eq_left ((div_le_one₀ ht).2 hz)
    rw [hmin]
    have hi : (∫ s : ℝ in Set.Ioo 0 (1 / N), k s) ≤
        (∫ s : ℝ in Set.Ioo 0 (1 / N), Real.rpow s (-1 / 2 : ℝ) * |z| ^ 3) := by
      apply integral_mono_ae hk (hp.1.mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      have hs0 : 0 ≤ s := hs.1.le
      have he : Real.exp (-(s / 2) * z ^ 2) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg z])
      have hfac : 0 ≤ Real.rpow s (-1 / 2 : ℝ) * |z| ^ 3 :=
        mul_nonneg (Real.rpow_nonneg hs0 _) (pow_nonneg (abs_nonneg z) 3)
      exact (mul_le_mul_of_nonneg_left he hfac).trans_eq (mul_one _)
    calc
      _ ≤ (2 * Real.sqrt (1 / N)) * |z| ^ 3 := by
        simpa only [integral_mul_const, hp.2] using hi
      _ = 2 * (z ^ 2 * (|z| / Real.sqrt N)) := by
        rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one, ← sq_abs z]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith only [hG]) (by positivity)
  · have hlarge : Real.sqrt N ≤ |z| := le_of_not_ge hz
    rw [min_eq_right ((le_div_iff₀ ht).2 (by simpa only [one_mul] using hlarge)), mul_one]
    have hzne : z ≠ 0 := by intro he; simp only [he, abs_zero] at hlarge; linarith only [ht, hlarge]
    have hg := smb_marked_half_kernel z hzne
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] k := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : 0 ≤ s := hs.le
      dsimp [k]; positivity
    calc
      _ ≤ ∫ s : ℝ in Set.Ioi 0, k s := setIntegral_mono_set hg.1 hnn
        (ae_of_all _ fun (s : ℝ) (hs : s ∈ Set.Ioo 0 (1 / N)) => hs.1)
      _ = Real.sqrt 2 * Real.Gamma (1 / 2) * z ^ 2 := hg.2
      _ ≤ (2 * Real.Gamma (1 / 2)) * z ^ 2 := by
        have hs2 : Real.sqrt 2 ≤ 2 := by
          nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs2 hG.le) (sq_nonneg z)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (sq_nonneg z)

private theorem smb_low_raw_kernel_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ), 0 < n →
        Integrable (fun z : ℝ => z ^ 2) nu →
        let eta : Measure ℝ := Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) nu
        let R : ℝ := Shao.truncationBudget eta n 0
        let a3 : ℝ → ℝ := fun u => ∫ z : ℝ, |z| ^ 3 * Real.exp (-u * z ^ 2) ∂nu
        IntegrableOn (fun s : ℝ => Real.rpow s (-1 / 2 : ℝ) * a3 (s / 2))
          (Set.Ioo 0 (1 / (n : ℝ))) ∧
          (∫ s : ℝ in Set.Ioo 0 (1 / (n : ℝ)), Real.rpow s (-1 / 2 : ℝ) * a3 (s / 2)) ≤ C * R := by
  obtain ⟨C, hC, hscalar⟩ := smb_low_scalar_kernel
  refine ⟨C, hC, ?_⟩
  intro nu hnu n hn h2 eta R a3
  letI : IsProbabilityMeasure nu := hnu
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  let S : Set ℝ := Set.Ioo 0 (1 / (n : ℝ))
  let K : ℝ × ℝ → ℝ := fun p =>
    Real.rpow p.2 (-1 / 2 : ℝ) * |p.1| ^ 3 * Real.exp (-(p.2 / 2) * p.1 ^ 2)
  have hKm : Measurable K := by dsimp [K]; fun_prop
  have hsections (z : ℝ) : Integrable (fun s => K (z, s)) (volume.restrict S) :=
    (hscalar (n : ℝ) z hN).1
  have hFi : Integrable (fun z : ℝ => Shao.truncationF (z / Real.sqrt (n : ℝ))) nu := by
    convert Shao.integrable_truncationF_mul nu h2 (1 / Real.sqrt (n : ℝ)) using 1
    funext z
    congr 1
    ring
  have houterm : AEStronglyMeasurable (fun z => ∫ s : ℝ, ‖K (z, s)‖ ∂volume.restrict S) nu :=
    hKm.aestronglyMeasurable.norm.integral_prod_right'
  have hnormeq (z : ℝ) : (∫ s : ℝ, ‖K (z, s)‖ ∂volume.restrict S) =
      ∫ s : ℝ, K (z, s) ∂volume.restrict S := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hs0 : 0 ≤ s := hs.1.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [K]; positivity)]
  have hnormi : Integrable (fun z => ∫ s : ℝ, ‖K (z, s)‖ ∂volume.restrict S) nu := by
    apply (hFi.const_mul (C * (n : ℝ))).mono' houterm
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), hnormeq]
      convert (hscalar (n : ℝ) z hN).2 using 1 <;> ring
  have hKi : Integrable K (nu.prod (volume.restrict S)) :=
    (integrable_prod_iff hKm.aestronglyMeasurable).2 ⟨ae_of_all _ hsections, hnormi⟩
  have hright (s : ℝ) : (∫ z : ℝ, K (z, s) ∂nu) = Real.rpow s (-1 / 2 : ℝ) * a3 (s / 2) := by
    dsimp [K, a3]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun z => by ring
  have hright' : (fun s => ∫ z : ℝ, K (z, s) ∂nu) =
      fun s => Real.rpow s (-1 / 2 : ℝ) * a3 (s / 2) := funext hright
  refine ⟨hright' ▸ hKi.integral_prod_right, ?_⟩
  change (∫ s : ℝ, Real.rpow s (-1 / 2 : ℝ) * a3 (s / 2) ∂volume.restrict S) ≤ _
  rw [← hright']
  calc
    _ = ∫ z : ℝ, ∫ s : ℝ, K (z, s) ∂volume.restrict S ∂nu :=
      (integral_integral_swap hKi).symm
    _ ≤ ∫ z : ℝ, (C * (n : ℝ)) * Shao.truncationF (z / Real.sqrt (n : ℝ)) ∂nu := by
      apply integral_mono hKi.integral_prod_left (hFi.const_mul _)
      intro z
      convert (hscalar (n : ℝ) z hN).2 using 1 <;> ring
    _ = C * R := by
      rw [integral_const_mul]
      have hRf : R = (n : ℝ) * (∫ z : ℝ, Shao.truncationF (z / Real.sqrt (n : ℝ)) ∂nu) := by
        unfold R Shao.truncationBudget
        simp only [add_zero, one_mul]
        rw [show eta = Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) nu from rfl,
          integral_map (μ := nu) (φ := fun z : ℝ => z / Real.sqrt (n : ℝ))
            (measurable_id.div_const _).aemeasurable
            Shao.continuous_truncationF.aestronglyMeasurable]
      rw [hRf]
      ring

private theorem smb_damped_mark_budget_point
    (N z s : ℝ) (hN : 0 < N) (hs : 1 / N ≤ s) :
    |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2) ≤
      Real.sqrt N * (N * Shao.truncationF (z / Real.sqrt N)) := by
  have ht : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hs0 : 0 < s := (one_div_pos.2 hN).trans_le hs
  rw [smb_scaled_budget_integrand N z hN]
  by_cases hz : |z| ≤ Real.sqrt N
  · rw [min_eq_left ((div_le_one₀ ht).2 hz)]
    have he : Real.exp (-(s / 2) * z ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg z])
    calc
      _ ≤ |z| ^ 3 := (mul_le_mul_of_nonneg_left he (pow_nonneg (abs_nonneg z) 3)).trans_eq (mul_one _)
      _ = _ := by rw [← sq_abs z]; field_simp
  · have hlarge : Real.sqrt N ≤ |z| := le_of_not_ge hz
    rw [min_eq_right ((le_div_iff₀ ht).2 (by simpa only [one_mul] using hlarge)), mul_one]
    have hh := smb_gaussian_linear (|z| / Real.sqrt N)
    have heq : -((|z| / Real.sqrt N) ^ 2) / 2 = -((1 / N) / 2) * z ^ 2 := by
      rw [div_pow, Real.sq_sqrt hN.le, sq_abs]
      ring
    rw [heq] at hh
    have hmul := mul_le_mul_of_nonneg_left hh ht.le
    have hbase : |z| * Real.exp (-((1 / N) / 2) * z ^ 2) ≤ Real.sqrt N := by
      convert hmul using 1 <;> field_simp
    calc
      _ ≤ |z| ^ 3 * Real.exp (-((1 / N) / 2) * z ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by
          have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg z)
          nlinarith only [hm])) (pow_nonneg (abs_nonneg z) 3)
      _ = z ^ 2 * (|z| * Real.exp (-((1 / N) / 2) * z ^ 2)) := by rw [← sq_abs z]; ring
      _ ≤ z ^ 2 * Real.sqrt N := mul_le_mul_of_nonneg_left hbase (sq_nonneg z)
      _ = _ := by ring

private theorem smb_early_scalar_kernel :
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧ ∀ (N z : ℝ), 0 < N →
      IntegrableOn (fun s : ℝ => Real.rpow s (1 / 2 : ℝ) * |z| ^ 3 *
        Real.exp (-(s / 2) * z ^ 2) * Real.exp (-c * N * s)) (Set.Ioi 0) ∧
        N * (∫ s : ℝ in Set.Ioi 0, Real.rpow s (1 / 2 : ℝ) * |z| ^ 3 *
          Real.exp (-(s / 2) * z ^ 2) * Real.exp (-c * N * s)) ≤
            C * (N * Shao.truncationF (z / Real.sqrt N)) := by
  intro c hc
  let G : ℝ := Real.Gamma (3 / 2)
  let C : ℝ := G / (c * Real.sqrt c) + 4 * G
  have hG : 0 < G := Real.Gamma_pos_of_pos (by norm_num)
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N z hN
  let rate : ℝ := z ^ 2 / 2 + c * N
  have hr : 0 < rate := by dsimp [rate]; positivity
  have hrN : c * N ≤ rate := by dsimp [rate]; nlinarith only [sq_nonneg z]
  have hrA : z ^ 2 / 2 ≤ rate := by dsimp [rate]; linarith only [mul_pos hc hN]
  have ht : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hsrate : 0 < Real.sqrt rate := Real.sqrt_pos.2 hr
  have hg := smb_gamma_three_halves rate hr
  have hf : (fun s : ℝ => Real.rpow s (1 / 2 : ℝ) * |z| ^ 3 *
      Real.exp (-(s / 2) * z ^ 2) * Real.exp (-c * N * s)) =
      fun s => |z| ^ 3 * (Real.rpow s (1 / 2 : ℝ) * Real.exp (-rate * s)) := by
    funext s
    rw [show -rate * s = -(s / 2) * z ^ 2 + -c * N * s by dsimp [rate]; ring, Real.exp_add]
    ring
  rw [hf]
  refine ⟨hg.1.const_mul _, ?_⟩
  rw [integral_const_mul, hg.2, smb_scaled_budget_integrand N z hN]
  by_cases hz : |z| ≤ Real.sqrt N
  · rw [min_eq_left ((div_le_one₀ ht).2 hz)]
    have hden : (c * Real.sqrt c) * N * Real.sqrt N ≤ rate * Real.sqrt rate := by
      have hh := mul_le_mul hrN (Real.sqrt_le_sqrt hrN) (Real.sqrt_nonneg (c * N)) hr.le
      rw [Real.sqrt_mul hc.le] at hh
      convert hh using 1 <;> ring
    calc
      _ = (N * |z| ^ 3 * G) / (rate * Real.sqrt rate) := by dsimp [G]; ring
      _ ≤ (N * |z| ^ 3 * G) / ((c * Real.sqrt c) * N * Real.sqrt N) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = (G / (c * Real.sqrt c)) * (z ^ 2 * (|z| / Real.sqrt N)) := by
        rw [← sq_abs z]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith only [hG]) (by positivity)
  · have hlarge : Real.sqrt N ≤ |z| := le_of_not_ge hz
    rw [min_eq_right ((le_div_iff₀ ht).2 (by simpa only [one_mul] using hlarge)), mul_one]
    have hsroot : |z| / 2 ≤ Real.sqrt rate := by
      apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg rate)).1
      rw [div_pow, sq_abs, Real.sq_sqrt hr.le]
      nlinarith only [hrA, sq_nonneg z]
    have hden : |z| ^ 3 ≤ 4 * (rate * Real.sqrt rate) := by
      have hh := mul_le_mul hrA hsroot (by positivity : (0 : ℝ) ≤ |z| / 2) hr.le
      rw [← sq_abs z] at hh
      nlinarith only [hh]
    have hNA : N ≤ z ^ 2 := by
      have hh := (sq_le_sq₀ ht.le (abs_nonneg z)).2 hlarge
      rwa [Real.sq_sqrt hN.le, sq_abs] at hh
    calc
      _ = (N * |z| ^ 3 * G) / (rate * Real.sqrt rate) := by dsimp [G]; ring
      _ ≤ 4 * G * N := by
        apply (div_le_iff₀ (mul_pos hr hsrate)).2
        have hh := mul_le_mul_of_nonneg_left hden (show 0 ≤ N * G by positivity)
        nlinarith only [hh]
      _ ≤ 4 * G * z ^ 2 := mul_le_mul_of_nonneg_left hNA (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by dsimp [C]; linarith only [div_nonneg hG.le (mul_pos hc hsc).le]) (sq_nonneg z)

private theorem smb_scaled_budget_map (nu : Measure ℝ) (n : ℕ) :
    Shao.truncationBudget (Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) nu) n 0 =
      (n : ℝ) * (∫ z : ℝ, Shao.truncationF (z / Real.sqrt (n : ℝ)) ∂nu) := by
  unfold Shao.truncationBudget
  simp only [add_zero, one_mul]
  rw [integral_map (μ := nu) (φ := fun z : ℝ => z / Real.sqrt (n : ℝ))
    (measurable_id.div_const _).aemeasurable Shao.continuous_truncationF.aestronglyMeasurable]

private theorem smb_early_raw_kernel_bound :
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ), 0 < n →
        Integrable (fun z : ℝ => z ^ 2) nu →
        let eta : Measure ℝ := Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) nu
        let R : ℝ := Shao.truncationBudget eta n 0
        let a3 : ℝ → ℝ := fun u => ∫ z : ℝ, |z| ^ 3 * Real.exp (-u * z ^ 2) ∂nu
        IntegrableOn (fun s : ℝ => Real.rpow s (1 / 2 : ℝ) * a3 (s / 2) *
          Real.exp (-c * (n : ℝ) * s)) (Set.Ioi 0) ∧
          (n : ℝ) * (∫ s : ℝ in Set.Ioi 0, Real.rpow s (1 / 2 : ℝ) * a3 (s / 2) *
            Real.exp (-c * (n : ℝ) * s)) ≤ C * R := by
  intro c hc
  obtain ⟨C, hC, hscalar⟩ := smb_early_scalar_kernel c hc
  refine ⟨C, hC, ?_⟩
  intro nu hnu n hn h2 eta R a3
  letI : IsProbabilityMeasure nu := hnu
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  let S : Set ℝ := Set.Ioi 0
  let K : ℝ × ℝ → ℝ := fun p =>
    Real.rpow p.2 (1 / 2 : ℝ) * |p.1| ^ 3 * Real.exp (-(p.2 / 2) * p.1 ^ 2) *
      Real.exp (-c * (n : ℝ) * p.2)
  have hKm : Measurable K := by dsimp [K]; fun_prop
  have hsections (z : ℝ) : Integrable (fun s => K (z, s)) (volume.restrict S) :=
    (hscalar (n : ℝ) z hN).1
  have hFi : Integrable (fun z : ℝ => Shao.truncationF (z / Real.sqrt (n : ℝ))) nu := by
    convert Shao.integrable_truncationF_mul nu h2 (1 / Real.sqrt (n : ℝ)) using 1
    funext z
    congr 1
    ring
  have hsectionbound (z : ℝ) :
      (∫ s : ℝ, K (z, s) ∂volume.restrict S) ≤ C * Shao.truncationF (z / Real.sqrt (n : ℝ)) := by
    apply (mul_le_mul_iff_right₀ hN).1
    convert (hscalar (n : ℝ) z hN).2 using 1 <;> ring
  have hnormeq (z : ℝ) : (∫ s : ℝ, ‖K (z, s)‖ ∂volume.restrict S) =
      ∫ s : ℝ, K (z, s) ∂volume.restrict S := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 ≤ s := hs.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [K]; positivity)]
  have hnormi : Integrable (fun z => ∫ s : ℝ, ‖K (z, s)‖ ∂volume.restrict S) nu := by
    apply (hFi.const_mul C).mono' hKm.aestronglyMeasurable.norm.integral_prod_right'
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), hnormeq]
      exact hsectionbound z
  have hKi : Integrable K (nu.prod (volume.restrict S)) :=
    (integrable_prod_iff hKm.aestronglyMeasurable).2 ⟨ae_of_all _ hsections, hnormi⟩
  have hright (s : ℝ) : (∫ z : ℝ, K (z, s) ∂nu) =
      Real.rpow s (1 / 2 : ℝ) * a3 (s / 2) * Real.exp (-c * (n : ℝ) * s) := by
    dsimp [K, a3]
    rw [integral_mul_const]
    congr 1
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun z => by ring
  have hright' : (fun s => ∫ z : ℝ, K (z, s) ∂nu) =
      fun s => Real.rpow s (1 / 2 : ℝ) * a3 (s / 2) * Real.exp (-c * (n : ℝ) * s) := funext hright
  refine ⟨hright' ▸ hKi.integral_prod_right, ?_⟩
  change (n : ℝ) * (∫ s : ℝ,
    Real.rpow s (1 / 2 : ℝ) * a3 (s / 2) * Real.exp (-c * (n : ℝ) * s) ∂volume.restrict S) ≤ _
  rw [← hright', ← integral_integral_swap hKi]
  calc
    _ ≤ (n : ℝ) * (∫ z : ℝ, C * Shao.truncationF (z / Real.sqrt (n : ℝ)) ∂nu) :=
      mul_le_mul_of_nonneg_left
        (integral_mono hKi.integral_prod_left (hFi.const_mul _) hsectionbound) hN.le
    _ = C * R := by
      rw [integral_const_mul, show R = (n : ℝ) *
        (∫ z : ℝ, Shao.truncationF (z / Real.sqrt (n : ℝ)) ∂nu) from smb_scaled_budget_map nu n]
      ring

private theorem smb_raw_mark_budget_point
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu) (s : ℝ) (hs : 1 / (n : ℝ) ≤ s) :
    (∫ z : ℝ, |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2) ∂nu) ≤
      Real.sqrt (n : ℝ) *
        Shao.truncationBudget (Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) nu) n 0 := by
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs0 : 0 < s := (one_div_pos.2 hN).trans_le hs
  have hFi : Integrable (fun z : ℝ => Shao.truncationF (z / Real.sqrt (n : ℝ))) nu := by
    convert Shao.integrable_truncationF_mul nu h2 (1 / Real.sqrt (n : ℝ)) using 1
    funext z
    congr 1
    ring
  calc
    _ ≤ ∫ z : ℝ, (Real.sqrt (n : ℝ) * (n : ℝ)) *
        Shao.truncationF (z / Real.sqrt (n : ℝ)) ∂nu := by
      apply integral_mono (smb_damped_mark_integrable nu h2 s hs0) (hFi.const_mul _)
      intro z
      convert smb_damped_mark_budget_point (n : ℝ) z s hN hs using 1 <;> ring
    _ = _ := by rw [integral_const_mul, smb_scaled_budget_map]; ring

theorem raw_gaussian_scalar_budget_integrals :
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ), 0 < n →
        Integrable (fun z : ℝ => z ^ 2) nu → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) nu
        let R : ℝ := Shao.truncationBudget normalizedLaw n 0
        let rho : ℝ := Real.sqrt (n : ℝ) * R
        let a3 : ℝ → ℝ := fun s => ∫ z : ℝ, |z| ^ 3 * Real.exp (-s * z ^ 2) ∂nu
        let lowKernel : ℝ → ℝ := fun s => Real.rpow s (-1 / 2 : ℝ) * a3 (s / 2)
        let earlyKernel : ℝ → ℝ := fun s =>
          Real.rpow s (1 / 2 : ℝ) * a3 (s / 2) * Real.exp (-c * (n : ℝ) * s)
        IntegrableOn lowKernel (Set.Ioo 0 (1 / (n : ℝ))) ∧
          (∫ s : ℝ in Set.Ioo 0 (1 / (n : ℝ)), lowKernel s) ≤ C * R ∧
          (∀ s : ℝ, 1 / (n : ℝ) ≤ s → a3 (s / 2) ≤ C * rho) ∧
          IntegrableOn earlyKernel (Set.Ioi 0) ∧
          (n : ℝ) * (∫ s : ℝ in Set.Ioi 0, earlyKernel s) ≤ C * R := by
  intro c hc
  obtain ⟨Cl, hCl, hl⟩ := smb_low_raw_kernel_bound
  obtain ⟨Ce, hCe, he⟩ := smb_early_raw_kernel_bound c hc
  let C : ℝ := Cl + Ce + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro nu hnu n hn h2 hsecond normalizedLaw R rho a3 lowKernel earlyKernel
  letI : IsProbabilityMeasure nu := hnu
  have hl' := hl nu n hn h2
  have he' := he nu n hn h2
  have hR : 0 ≤ R := by
    rw [show R = (n : ℝ) * (∫ z : ℝ, Shao.truncationF (z / Real.sqrt (n : ℝ)) ∂nu)
      from smb_scaled_budget_map nu n]
    exact mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun z => Shao.truncationF_nonneg _)
  refine ⟨hl'.1, hl'.2.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hR), ?_,
    he'.1, he'.2.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hR)⟩
  intro s hs
  apply (smb_raw_mark_budget_point nu n hn h2 s hs).trans
  simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith : (1 : ℝ) ≤ C)
      (show 0 ≤ rho by dsimp [rho]; positivity))

private theorem smb_positive_power_integral (a B : ℝ) (ha : 0 < a) (hB : 0 < B) :
    IntegrableOn (fun s : ℝ => Real.rpow s (a - 1)) (Set.Ioo 0 B) ∧
      (∫ s : ℝ in Set.Ioo 0 B, Real.rpow s (a - 1)) = Real.rpow B a / a := by
  have hi := intervalIntegral.intervalIntegrable_rpow'
    (a := (0 : ℝ)) (b := B) (by linarith : -1 < a - 1)
  have he := integral_rpow (a := (0 : ℝ)) (b := B) (r := a - 1) (Or.inl (by linarith))
  have hs := hi.1
  refine ⟨hs.mono_set Set.Ioo_subset_Ioc_self, ?_⟩
  rw [intervalIntegral.integral_of_le hB.le, integral_Ioc_eq_integral_Ioo] at he
  simpa only [sub_add_cancel, Real.zero_rpow ha.ne', sub_zero, Real.rpow_eq_pow] using he

private theorem smb_inverse_laplace (a T b : ℝ) (ha : 0 < a) (hb : 0 < b) (hT : b ≤ T) :
    Real.rpow T (-a) ≤ Real.exp 1 * a *
      (∫ s : ℝ in Set.Ioo 0 (1 / b), Real.rpow s (a - 1) * Real.exp (-s * T)) := by
  have hTp : 0 < T := hb.trans_le hT
  have hsmall : Set.Ioo (0 : ℝ) (1 / T) ⊆ Set.Ioo 0 (1 / b) := by
    intro s hs
    exact ⟨hs.1, hs.2.trans_le (one_div_le_one_div_of_le hb hT)⟩
  have hg := smb_gamma_kernel a T ha hTp
  have hf : (fun s : ℝ => Real.rpow s (a - 1) * Real.exp (-T * s)) =
      fun s => Real.rpow s (a - 1) * Real.exp (-s * T) := by
    funext s
    congr 1
    congr 1
    ring
  have hg' := hf ▸ hg.1
  have hi := hg'.mono_set (show Set.Ioo (0 : ℝ) (1 / b) ⊆ Set.Ioi 0 from fun _ hs => hs.1)
  have hp := smb_positive_power_integral a (1 / T) ha (one_div_pos.2 hTp)
  have hlo : Real.exp (-1) * (Real.rpow (1 / T) a / a) ≤
      ∫ s : ℝ in Set.Ioo 0 (1 / T), Real.rpow s (a - 1) * Real.exp (-s * T) := by
    rw [← hp.2, ← integral_const_mul]
    apply integral_mono_ae (hp.1.const_mul _) (hg'.mono_set fun _ hs => hs.1)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hs0 : 0 ≤ s := hs.1.le
    have hsT : s * T ≤ 1 := (le_div_iff₀ hTp).1 hs.2.le
    calc
      _ = Real.rpow s (a - 1) * Real.exp (-1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (Real.rpow_nonneg hs0 _)
  have hmono : (∫ s : ℝ in Set.Ioo 0 (1 / T), Real.rpow s (a - 1) * Real.exp (-s * T)) ≤
      ∫ s : ℝ in Set.Ioo 0 (1 / b), Real.rpow s (a - 1) * Real.exp (-s * T) := by
    apply setIntegral_mono_set hi _ (ae_of_all _ fun _ hs => hsmall hs)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact mul_nonneg (Real.rpow_nonneg hs.1.le _) (Real.exp_pos _).le
  have he : Real.exp 1 * a * (Real.exp (-1) * (Real.rpow (1 / T) a / a)) = Real.rpow T (-a) := by
    have hpow : Real.rpow (1 / T) a = Real.rpow T (-a) := by
      simp only [Real.rpow_eq_pow, one_div, Real.inv_rpow hTp.le, Real.rpow_neg hTp.le]
    rw [hpow]
    calc
      _ = (Real.exp 1 * Real.exp (-1)) * Real.rpow T (-a) := by field_simp <;> ring
      _ = _ := by rw [← Real.exp_add]; norm_num
  calc
    _ = _ := he.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hlo.trans hmono) (mul_pos (Real.exp_pos _) ha).le

private theorem smb_small_half_raw_integrable
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu) (B : ℝ) (hB : 0 < B) :
    IntegrableOn (fun s : ℝ => Real.rpow s (-1 / 2 : ℝ) *
      (∫ z : ℝ, |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2) ∂nu)) (Set.Ioo 0 B) := by
  obtain ⟨C, hC, hscalar⟩ := smb_low_scalar_kernel
  let N : ℝ := 1 / B
  have hN : 0 < N := one_div_pos.2 hB
  have hinv : 1 / N = B := by dsimp [N]; field_simp
  let S : Set ℝ := Set.Ioo 0 B
  let K : ℝ × ℝ → ℝ := fun p =>
    Real.rpow p.2 (-1 / 2 : ℝ) * |p.1| ^ 3 * Real.exp (-(p.2 / 2) * p.1 ^ 2)
  have hKm : Measurable K := by dsimp [K]; fun_prop
  have hsections (z : ℝ) : Integrable (fun s => K (z, s)) (volume.restrict S) := by
    change IntegrableOn (fun s : ℝ => Real.rpow s (-1 / 2 : ℝ) * |z| ^ 3 *
      Real.exp (-(s / 2) * z ^ 2)) (Set.Ioo 0 B)
    rw [← hinv]
    exact (hscalar N z hN).1
  have hFi : Integrable (fun z : ℝ => Shao.truncationF (z / Real.sqrt N)) nu := by
    convert Shao.integrable_truncationF_mul nu h2 (1 / Real.sqrt N) using 1
    funext z
    congr 1
    ring
  have hnormeq (z : ℝ) : (∫ s : ℝ, ‖K (z, s)‖ ∂volume.restrict S) =
      ∫ s : ℝ, K (z, s) ∂volume.restrict S := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [Real.norm_eq_abs]
    exact abs_of_nonneg (show 0 ≤ K (z, s) by
      dsimp [K]
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.1.le _)
        (pow_nonneg (abs_nonneg _) _)) (Real.exp_pos _).le)
  have hnormi : Integrable (fun z => ∫ s : ℝ, ‖K (z, s)‖ ∂volume.restrict S) nu := by
    apply (hFi.const_mul (C * N)).mono' hKm.aestronglyMeasurable.norm.integral_prod_right'
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), hnormeq]
      have hh := (hscalar N z hN).2
      rw [hinv] at hh
      convert hh using 1 <;> ring
  have hKi : Integrable K (nu.prod (volume.restrict S)) :=
    (integrable_prod_iff hKm.aestronglyMeasurable).2 ⟨ae_of_all _ hsections, hnormi⟩
  have heq : (fun s => ∫ z : ℝ, K (z, s) ∂nu) = fun s : ℝ =>
      Real.rpow s (-1 / 2 : ℝ) * (∫ z : ℝ, |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2) ∂nu) := by
    funext s
    dsimp [K]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun z => by ring
  exact heq ▸ hKi.integral_prod_right

private theorem smb_cutoff_moment_kernel_integrable
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (m q : ℕ) (hq : q = 1 ∨ q = 3) (b gamma : ℝ) (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => Real.rpow s ((q : ℝ) / 2 - 1) *
      (∫ z : ℝ, |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2) ∂nu) *
      Real.exp (gamma * s * (m : ℝ))) (Set.Ioo 0 (1 / b)) := by
  let a3 : ℝ → ℝ := fun s => ∫ z : ℝ, |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2) ∂nu
  let L : ℝ → ℝ := fun s => Real.rpow s (-1 / 2 : ℝ) * a3 s
  have hL : IntegrableOn L (Set.Ioo 0 (1 / b)) :=
    smb_small_half_raw_integrable nu h2 (1 / b) (one_div_pos.2 hb)
  have ha (s : ℝ) : 0 ≤ a3 s := integral_nonneg fun z => by positivity
  have ham : AEStronglyMeasurable a3 (volume.restrict (Set.Ioo 0 (1 / b))) := by
    have hm : Measurable (fun p : ℝ × ℝ => |p.1| ^ 3 * Real.exp (-(p.2 / 2) * p.1 ^ 2)) := by fun_prop
    exact hm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
  let E : ℝ := Real.exp (|gamma| * (m : ℝ) / b)
  apply (hL.const_mul ((1 + 1 / b) * E)).mono'
    (((by simp only [Real.rpow_eq_pow]; fun_prop :
      Measurable (fun s : ℝ => Real.rpow s ((q : ℝ) / 2 - 1))).aestronglyMeasurable.mul ham).mul
      (by fun_prop))
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hs0 : 0 ≤ s := hs.1.le
  have he : Real.exp (gamma * s * (m : ℝ)) ≤ E := by
    apply Real.exp_le_exp.2
    calc
      _ ≤ |gamma| * s * (m : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self gamma) hs0)
          (Nat.cast_nonneg _)
      _ ≤ |gamma| * (1 / b) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs.2.le (abs_nonneg _))
          (Nat.cast_nonneg _)
      _ = _ := by ring
  have hfac : Real.rpow s ((q : ℝ) / 2 - 1) ≤
      (1 + 1 / b) * Real.rpow s (-1 / 2 : ℝ) := by
    rcases hq with rfl | rfl
    · norm_num only [Nat.cast_one, one_div, sub_eq_add_neg] at *
      have hr : 0 ≤ Real.rpow s (-1 / 2 : ℝ) := Real.rpow_nonneg hs0 _
      have hh : (1 : ℝ) ≤ 1 + 1 / b := by linarith only [one_div_pos.2 hb]
      convert mul_le_mul_of_nonneg_right hh hr using 1 <;> norm_num <;> ring
    · norm_num only [Nat.cast_ofNat, show (3 : ℝ) / 2 - 1 = 1 / 2 by norm_num]
      rw [show (1 / 2 : ℝ) = -1 / 2 + 1 by norm_num, Real.rpow_eq_pow,
        Real.rpow_add hs.1, Real.rpow_one]
      have hr : 0 ≤ Real.rpow s (-1 / 2 : ℝ) := Real.rpow_nonneg hs0 _
      have hh : s ≤ 1 + 1 / b := by linarith only [hs.2]
      convert mul_le_mul_of_nonneg_left hh hr using 1 <;> simp only [Real.rpow_eq_pow] <;> ring
  change ‖Real.rpow s ((q : ℝ) / 2 - 1) * a3 s * Real.exp (gamma * s * (m : ℝ))‖ ≤ _
  have hnonneg : 0 ≤ Real.rpow s ((q : ℝ) / 2 - 1) * a3 s * Real.exp (gamma * s * (m : ℝ)) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0 _) (ha s)) (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    _ ≤ ((1 + 1 / b) * Real.rpow s (-1 / 2 : ℝ)) * a3 s * E :=
      mul_le_mul (mul_le_mul_of_nonneg_right hfac (ha s)) he (Real.exp_pos _).le
        (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hs0 _)) (ha s))
    _ = _ := by dsimp [L]; ring

private theorem smb_marked_cutoff_polynomial_inverse :
    let c : ℝ := (1 - Real.exp (-2)) / 8
    ∀ j q : ℕ, (q = 1 ∨ q = 3) → ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ (m : ℕ) (b : ℝ), 0 < b →
          let P : Measure (Shao.Path (m + 1)) := Measure.pi (fun _ : Fin (m + 1) => nu)
          let T : Shao.Path (m + 1) → ℝ := Shao.energy
          let d : Shao.Path (m + 1) → ℝ := fun v => Shao.prefixSum v (m + 1)
          let M : Shao.Path (m + 1) → ℝ := fun v => |v 0| ^ 3
          let a3 : ℝ → ℝ := fun u => ∫ z : ℝ, |z| ^ 3 * Real.exp (-u * z ^ 2) ∂nu
          let retained : ℝ := ∫ z : ℝ, if z ^ 2 ≤ b then z ^ 2 else 0 ∂nu
          let gamma : ℝ := if (1 / 2 : ℝ) ≤ retained then -c else 1
          let selected : Shao.Path (m + 1) → ℝ := fun v =>
            if 0 < T v ∧ b ≤ T v then M v * |d v| ^ j / (Real.sqrt (T v)) ^ (j + q) else 0
          let kernel : ℝ → ℝ := fun s =>
            Real.rpow s ((q : ℝ) / 2 - 1) * a3 (s / 2) * Real.exp (gamma * s * (m : ℝ))
          Integrable selected P ∧
            (∫ v, selected v ∂P) ≤ C * ∫ s : ℝ in Set.Ioo 0 (1 / b), kernel s := by
  intro c j q hq
  obtain ⟨Cj, hCj, hmoment⟩ := iid_marked_gaussian_damped_moments j
  let alpha : ℝ := ((j + q : ℕ) : ℝ) / 2
  have hqpos : 0 < q := by rcases hq with rfl | rfl <;> norm_num
  have halpha : 0 < alpha := by dsimp [alpha]; exact div_pos (by exact_mod_cast (Nat.add_pos_right j hqpos)) (by norm_num)
  let A : ℝ := Real.exp 1 * alpha
  have hA : 0 < A := mul_pos (Real.exp_pos _) halpha
  refine ⟨A * Cj, mul_pos hA hCj, ?_⟩
  intro nu hnu h2 hmean hnorm m b hb P T d M a3 retained gamma selected kernel
  letI : IsProbabilityMeasure nu := hnu
  let S : Set ℝ := Set.Ioo 0 (1 / b)
  let K : ℝ × Shao.Path (m + 1) → ℝ := fun x =>
    Real.rpow x.1 (alpha - 1) * (M x.2 * |d x.2| ^ j * Real.exp (-x.1 * T x.2))
  have hMm : Measurable M :=
    (continuous_abs.measurable.comp (measurable_pi_apply (X := fun _ : Fin (m + 1) => ℝ) 0)).pow_const 3
  have hTm : Measurable T := Shao.measurable_energy
  have hdm : Measurable d := Shao.measurable_prefixSum (m + 1)
  have hKm : Measurable K := by
    dsimp [K]
    fun_prop
  have hknn (s : ℝ) (hs : 0 ≤ s) (v : Shao.Path (m + 1)) : 0 ≤ K (s, v) :=
    mul_nonneg (Real.rpow_nonneg hs _)
      (mul_nonneg (mul_nonneg (pow_nonneg (abs_nonneg _) _) (pow_nonneg (abs_nonneg _) _)) (Real.exp_pos _).le)
  have hki : IntegrableOn kernel S := smb_cutoff_moment_kernel_integrable nu h2 m q hq b gamma hb
  have hsexp (s : ℝ) (hs : 0 < s) :
      Real.rpow s (alpha - 1) * Real.rpow s (-(j : ℝ) / 2) =
        Real.rpow s ((q : ℝ) / 2 - 1) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hs]
    congr 1
    dsimp [alpha]
    push_cast
    ring
  have hsb (s : ℝ) (hs : s ∈ S) : s ≤ 2 / b := by
    calc
      s ≤ 1 / b := hs.2.le
      _ ≤ 1 / b + 1 / b := le_add_of_nonneg_right (one_div_pos.2 hb).le
      _ = _ := by ring
  have hsections : ∀ᵐ s ∂volume.restrict S, Integrable (fun v => K (s, v)) P := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact ((hmoment nu h2 hmean hnorm m b s hb hs.1 (hsb s hs)).1).const_mul
      (Real.rpow s (alpha - 1))
  have hupper (s : ℝ) (hs : s ∈ S) :
      (∫ v, K (s, v) ∂P) ≤ Cj * kernel s := by
    change (∫ v, Real.rpow s (alpha - 1) * (M v * |d v| ^ j * Real.exp (-s * T v)) ∂P) ≤ _
    rw [integral_const_mul]
    calc
        _ ≤ Real.rpow s (alpha - 1) *
            (Cj * Real.rpow s (-(j : ℝ) / 2) * a3 (s / 2) * Real.exp (gamma * s * (m : ℝ))) :=
          mul_le_mul_of_nonneg_left (hmoment nu h2 hmean hnorm m b s hb hs.1 (hsb s hs)).2
            (Real.rpow_nonneg hs.1.le _)
        _ = _ := by
          dsimp [kernel]
          calc
            _ = Cj * (Real.rpow s (alpha - 1) * Real.rpow s (-(j : ℝ) / 2)) *
                a3 (s / 2) * Real.exp (gamma * s * (m : ℝ)) := by simp only [Real.rpow_eq_pow]; ring
            _ = _ := by rw [hsexp s hs.1]; simp only [Real.rpow_eq_pow]; ring
  have hnormi : Integrable (fun s => ∫ v, ‖K (s, v)‖ ∂P) (volume.restrict S) := by
    apply (hki.const_mul Cj).mono' hKm.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have he : (∫ v, ‖K (s, v)‖ ∂P) = ∫ v, K (s, v) ∂P := by
      apply integral_congr_ae
      exact ae_of_all _ fun v => Real.norm_of_nonneg (hknn s hs.1.le v)
    rw [he]
    exact hupper s hs
  have hKi : Integrable K ((volume.restrict S).prod P) :=
    (integrable_prod_iff hKm.aestronglyMeasurable).2 ⟨hsections, hnormi⟩
  have hselm : Measurable selected := by
    apply Measurable.ite
      ((measurableSet_lt measurable_const hTm).inter (measurableSet_le measurable_const hTm))
    · exact (hMm.mul ((continuous_abs.measurable.comp hdm).pow_const j)).div
        (hTm.sqrt.pow_const (j + q))
    · exact measurable_const
  have hselnn (v : Shao.Path (m + 1)) : 0 ≤ selected v := by
    dsimp [selected, M]
    split_ifs <;> positivity
  have hpoint (v : Shao.Path (m + 1)) : selected v ≤ A * ∫ s : ℝ, K (s, v) ∂volume.restrict S := by
    by_cases hv : 0 < T v ∧ b ≤ T v
    · rw [show selected v = M v * |d v| ^ j / (Real.sqrt (T v)) ^ (j + q) from if_pos hv]
      have hi := smb_inverse_laplace alpha (T v) b halpha hb hv.2
      have hp : Real.rpow (T v) (-alpha) = 1 / (Real.sqrt (T v)) ^ (j + q) := by
        convert (smb_sqrt_pow_inverse (T v) hv.1 (j + q)).symm using 1
        congr 1
        dsimp [alpha]
        push_cast
        ring
      calc
        _ = (M v * |d v| ^ j) * Real.rpow (T v) (-alpha) := by
          rw [hp]
          ring
        _ ≤ (M v * |d v| ^ j) * (A * ∫ s : ℝ in Set.Ioo 0 (1 / b),
            Real.rpow s (alpha - 1) * Real.exp (-s * T v)) :=
          mul_le_mul_of_nonneg_left hi (mul_nonneg (pow_nonneg (abs_nonneg _) _) (pow_nonneg (abs_nonneg _) _))
        _ = _ := by
          calc
            _ = A * ((M v * |d v| ^ j) * (∫ s : ℝ in Set.Ioo 0 (1 / b),
                Real.rpow s (alpha - 1) * Real.exp (-s * T v))) := by ring
            _ = _ := by
              rw [← integral_const_mul]
              congr 1
              apply integral_congr_ae
              exact ae_of_all _ fun s => by dsimp [K]; ring
    · rw [show selected v = 0 from if_neg hv]
      exact mul_nonneg hA.le (integral_nonneg_of_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact hknn s hs.1.le v))
  have hseli : Integrable selected P := by
    apply (hKi.integral_prod_right.const_mul A).mono' hselm.aestronglyMeasurable
    exact ae_of_all _ fun v => by rw [Real.norm_eq_abs, abs_of_nonneg (hselnn v)]; exact hpoint v
  refine ⟨hseli, ?_⟩
  calc
    _ ≤ ∫ v, A * (∫ s : ℝ, K (s, v) ∂volume.restrict S) ∂P :=
      integral_mono hseli (hKi.integral_prod_right.const_mul A) hpoint
    _ = A * ∫ s : ℝ, ∫ v, K (s, v) ∂P ∂volume.restrict S := by
      rw [integral_const_mul, ← integral_integral_swap hKi]
    _ ≤ A * ∫ s : ℝ, Cj * kernel s ∂volume.restrict S := by
      apply mul_le_mul_of_nonneg_left _ hA.le
      apply integral_mono_ae hKi.integral_prod_left (hki.const_mul Cj)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hupper s hs
    _ = _ := by rw [integral_const_mul]; ring

private theorem smb_one_add_pow_bound (u : ℝ) (hu : 0 ≤ u) (p : ℕ) :
    (1 + u) ^ p ≤ (2 : ℝ) ^ p * (1 + u ^ p) := by
  calc
    _ ≤ (2 : ℝ) ^ (p - 1) * ((1 : ℝ) ^ p + u ^ p) := add_pow_le (by norm_num) hu p
    _ ≤ _ := by
      rw [one_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le _ _))
        (by positivity)

theorem iid_marked_cutoff_inverse_moments :
    let c : ℝ := (1 - Real.exp (-2)) / 8
    ∀ p q : ℕ, (q = 1 ∨ q = 3) → ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ (m : ℕ) (b : ℝ), 0 < b →
          let P : Measure (Shao.Path (m + 1)) := Measure.pi (fun _ : Fin (m + 1) => nu)
          let T : Shao.Path (m + 1) → ℝ := Shao.energy
          let d : Shao.Path (m + 1) → ℝ := fun v => Shao.prefixSum v (m + 1)
          let M : Shao.Path (m + 1) → ℝ := fun v => |v 0| ^ 3
          let a3 : ℝ → ℝ := fun u => ∫ z : ℝ, |z| ^ 3 * Real.exp (-u * z ^ 2) ∂nu
          let retained : ℝ := ∫ z : ℝ, if z ^ 2 ≤ b then z ^ 2 else 0 ∂nu
          let gamma : ℝ := if (1 / 2 : ℝ) ≤ retained then -c else 1
          let selected : Shao.Path (m + 1) → ℝ := fun v =>
            if 0 < T v ∧ b ≤ T v then
              M v / (Real.sqrt (T v)) ^ q * (1 + |d v| / Real.sqrt (T v)) ^ p
            else 0
          let kernel : ℝ → ℝ := fun s =>
            Real.rpow s ((q : ℝ) / 2 - 1) * a3 (s / 2) *
              Real.exp (gamma * s * (m : ℝ))
          Integrable selected P ∧ IntegrableOn kernel (Set.Ioo 0 (1 / b)) ∧
            (∫ v, selected v ∂P) ≤ C * ∫ s : ℝ in Set.Ioo 0 (1 / b), kernel s := by
  intro c p q hq
  obtain ⟨C0, hC0, hm0⟩ := smb_marked_cutoff_polynomial_inverse 0 q hq
  obtain ⟨Cp, hCp, hmp⟩ := smb_marked_cutoff_polynomial_inverse p q hq
  refine ⟨(2 : ℝ) ^ p * (C0 + Cp), by positivity, ?_⟩
  intro nu hnu h2 hmean hnorm m b hb P T d M a3 retained gamma selected kernel
  letI : IsProbabilityMeasure nu := hnu
  let U : Shao.Path (m + 1) → ℝ := fun v =>
    if 0 < T v ∧ b ≤ T v then M v / (Real.sqrt (T v)) ^ q else 0
  let V : Shao.Path (m + 1) → ℝ := fun v =>
    if 0 < T v ∧ b ≤ T v then M v * |d v| ^ p / (Real.sqrt (T v)) ^ (p + q) else 0
  have h0 : Integrable U P ∧
      (∫ v, U v ∂P) ≤ C0 * ∫ s : ℝ in Set.Ioo 0 (1 / b), kernel s := by
    simpa only [pow_zero, mul_one, zero_add] using hm0 nu h2 hmean hnorm m b hb
  have hp : Integrable V P ∧
      (∫ v, V v ∂P) ≤ Cp * ∫ s : ℝ in Set.Ioo 0 (1 / b), kernel s :=
    hmp nu h2 hmean hnorm m b hb
  have hMm : Measurable M :=
    (continuous_abs.measurable.comp (measurable_pi_apply (X := fun _ : Fin (m + 1) => ℝ) 0)).pow_const 3
  have hTm : Measurable T := Shao.measurable_energy
  have hdm : Measurable d := Shao.measurable_prefixSum (m + 1)
  have hselm : Measurable selected := by
    apply Measurable.ite
      ((measurableSet_lt measurable_const hTm).inter (measurableSet_le measurable_const hTm))
    · exact (hMm.div (hTm.sqrt.pow_const q)).mul
        ((measurable_const.add ((continuous_abs.measurable.comp hdm).div hTm.sqrt)).pow_const p)
    · exact measurable_const
  have hnn (v : Shao.Path (m + 1)) : 0 ≤ selected v := by
    dsimp [selected, M]
    split_ifs <;> positivity
  have hpoint (v : Shao.Path (m + 1)) : selected v ≤ (2 : ℝ) ^ p * (U v + V v) := by
    by_cases hv : 0 < T v ∧ b ≤ T v
    · dsimp [selected, U, V]
      rw [if_pos hv, if_pos hv, if_pos hv]
      have ht : 0 < Real.sqrt (T v) := Real.sqrt_pos.2 hv.1
      have hh := smb_one_add_pow_bound (|d v| / Real.sqrt (T v)) (by positivity) p
      calc
        _ ≤ (M v / (Real.sqrt (T v)) ^ q) * ((2 : ℝ) ^ p *
            (1 + (|d v| / Real.sqrt (T v)) ^ p)) :=
          mul_le_mul_of_nonneg_left hh (by dsimp [M]; positivity)
        _ = _ := by
          rw [div_pow, pow_add]
          field_simp
          <;> ring
    · simp only [selected, U, V, if_neg hv, add_zero, mul_zero]
      exact le_rfl
  have hsi : Integrable selected P := by
    apply ((h0.1.add hp.1).const_mul ((2 : ℝ) ^ p)).mono' hselm.aestronglyMeasurable
    exact ae_of_all _ fun v => by rw [Real.norm_eq_abs, abs_of_nonneg (hnn v)]; exact hpoint v
  refine ⟨hsi, smb_cutoff_moment_kernel_integrable nu h2 m q hq b gamma hb, ?_⟩
  calc
    _ ≤ ∫ v, (2 : ℝ) ^ p * (U v + V v) ∂P :=
      integral_mono hsi ((h0.1.add hp.1).const_mul _) hpoint
    _ = (2 : ℝ) ^ p * ((∫ v, U v ∂P) + ∫ v, V v ∂P) := by
      rw [integral_const_mul, integral_add h0.1 hp.1]
    _ ≤ (2 : ℝ) ^ p * (C0 * (∫ s : ℝ in Set.Ioo 0 (1 / b), kernel s) +
        Cp * (∫ s : ℝ in Set.Ioo 0 (1 / b), kernel s)) :=
      mul_le_mul_of_nonneg_left (add_le_add h0.2 hp.2) (by positivity)
    _ = _ := by ring

private theorem smb_early_marked_block :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ (m : ℕ) (b : ℝ), 0 < b →
          let P : Measure (Shao.Path (m + 1)) := Measure.pi (fun _ : Fin (m + 1) => nu)
          let c : ℝ := (1 - Real.exp (-2)) / 8
          let retained : ℝ := ∫ z : ℝ, if z ^ 2 ≤ b then z ^ 2 else 0 ∂nu
          let gamma : ℝ := if (1 / 2 : ℝ) ≤ retained then -c else 1
          let a3 : ℝ → ℝ := fun u => ∫ z : ℝ, |z| ^ 3 * Real.exp (-u * z ^ 2) ∂nu
          let early : Shao.Path (m + 1) → ℝ := fun v =>
            if 0 < Shao.energy v ∧ b ≤ Shao.energy v then
              |v 0| ^ 3 / (Shao.energy v * Real.sqrt (Shao.energy v)) *
                (1 + |Shao.prefixSum v (m + 1)| ^ 3 /
                  (Shao.energy v * Real.sqrt (Shao.energy v)))
            else 0
          Integrable early P ∧
            (∫ v, early v ∂P) ≤ C * ∫ s : ℝ in Set.Ioo 0 (1 / b),
              Real.rpow s (1 / 2 : ℝ) * a3 (s / 2) * Real.exp (gamma * s * (m : ℝ)) ∧
            (∀ v, 0 ≤ early v ∧ early v ≤ (1 + Real.sqrt ((m + 1 : ℕ) : ℝ)) ^ 3) := by
  obtain ⟨C, hC, hm⟩ := iid_marked_cutoff_inverse_moments 3 3 (Or.inr rfl)
  refine ⟨C, hC, ?_⟩
  intro nu hnu h2 hmean hnorm m b hb P c retained gamma a3 early
  letI : IsProbabilityMeasure nu := hnu
  let J : Shao.Path (m + 1) → ℝ := fun v =>
    if 0 < Shao.energy v ∧ b ≤ Shao.energy v then
      |v 0| ^ 3 / Real.sqrt (Shao.energy v) ^ 3 *
        (1 + |Shao.prefixSum v (m + 1)| / Real.sqrt (Shao.energy v)) ^ 3 else 0
  have hJ := hm nu h2 hmean hnorm m b hb
  have hpoint (v : Shao.Path (m + 1)) : early v ≤ J v := by
    dsimp [early, J]
    split_ifs with hv
    · have hs : 0 < Real.sqrt (Shao.energy v) := Real.sqrt_pos.2 hv.1
      have hs3 : Real.sqrt (Shao.energy v) ^ 3 =
          Shao.energy v * Real.sqrt (Shao.energy v) := by
        rw [pow_succ, Real.sq_sqrt hv.1.le]
      rw [← hs3]
      have hu : 0 ≤ |Shao.prefixSum v (m + 1)| / Real.sqrt (Shao.energy v) := by positivity
      have hh : 1 + (|Shao.prefixSum v (m + 1)| / Real.sqrt (Shao.energy v)) ^ 3 ≤
          (1 + |Shao.prefixSum v (m + 1)| / Real.sqrt (Shao.energy v)) ^ 3 := by
        nlinarith only [hu, sq_nonneg (|Shao.prefixSum v (m + 1)| / Real.sqrt (Shao.energy v))]
      rw [div_pow] at hh
      exact mul_le_mul_of_nonneg_left hh (by positivity)
    · exact le_rfl
  have hnn (v : Shao.Path (m + 1)) : 0 ≤ early v := by
    have hE := Shao.energy_nonneg v
    dsimp [early]
    split_ifs <;> positivity
  have hem : Measurable early := by
    have hT : Measurable (Shao.energy : Shao.Path (m + 1) → ℝ) := Shao.measurable_energy
    have hd : Measurable (fun v : Shao.Path (m + 1) => Shao.prefixSum v (m + 1)) :=
      Shao.measurable_prefixSum (m + 1)
    apply Measurable.ite
      ((measurableSet_lt measurable_const hT).inter (measurableSet_le measurable_const hT))
    · exact (((continuous_abs.measurable.comp (measurable_pi_apply (X := fun _ : Fin (m + 1) => ℝ) 0)).pow_const 3).div
        (hT.mul hT.sqrt)).mul
          (measurable_const.add (((continuous_abs.measurable.comp hd).pow_const 3).div (hT.mul hT.sqrt)))
    · exact measurable_const
  have hei : Integrable early P := by
    apply hJ.1.mono' hem.aestronglyMeasurable
    exact ae_of_all _ fun v => by rw [Real.norm_eq_abs, abs_of_nonneg (hnn v)]; exact hpoint v
  refine ⟨hei, (integral_mono hei hJ.1 hpoint).trans ?_, ?_⟩
  · simpa only [Nat.cast_ofNat, show (3 : ℝ) / 2 - 1 = 1 / 2 by norm_num] using hJ.2.2
  · intro v
    refine ⟨hnn v, (hpoint v).trans ?_⟩
    have hg := SourceMarkedSuffixAveraging.suffix_normalized_geometry v
    by_cases hv : 0 < Shao.energy v ∧ b ≤ Shao.energy v
    · dsimp [J]
      rw [if_pos hv]
      have hs3 : Real.sqrt (Shao.energy v) ^ 3 =
          Shao.energy v * Real.sqrt (Shao.energy v) := by rw [pow_succ, Real.sq_sqrt hv.1.le]
      rw [hs3]
      have hmark := (hg.2.2.2.1 (0 : Fin (m + 1))).2
      have hD := hg.2.2.2.2.2.1.2
      rw [SourceMarkedSuffixAveraging.normalizedCubicMark, if_pos hv.1] at hmark
      rw [SourceMarkedSuffixAveraging.suffixD, if_pos hv.1] at hD
      calc
        _ ≤ (1 + |Shao.prefixSum v (m + 1)| / Real.sqrt (Shao.energy v)) ^ 3 := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hmark (by positivity)
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hD 3
    · simp only [J, if_neg hv]
      positivity

private theorem smb_early_unit_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) nu
        let R : ℝ := Shao.truncationBudget normalizedLaw n 0
        let h : ℝ := 4 * (n : ℝ) * R ^ 2
        let P : (t : ℕ) → Measure (Shao.Path t) := fun t => Measure.pi (fun _ : Fin t => nu)
        let firstCube : (t : ℕ) → Shao.Path t → ℝ := fun t v =>
          if ht : 0 < t then |v ⟨0, ht⟩| ^ 3 else 0
        let early : (t : ℕ) → Shao.Path t → ℝ := fun t v =>
          if 0 < Shao.energy v ∧ h ≤ Shao.energy v then
            firstCube t v / (Shao.energy v * Real.sqrt (Shao.energy v)) *
              (1 + |Shao.prefixSum v t| ^ 3 /
                (Shao.energy v * Real.sqrt (Shao.energy v)))
          else 0
        (∀ t ∈ Finset.Icc ((n + 1) / 2) n, Integrable (early t) (P t)) ∧
          (∑ t ∈ Finset.Icc ((n + 1) / 2) n, ∫ v, early t v ∂P t) ≤ C * R := by
  let c : ℝ := (1 - Real.exp (-2)) / 8
  have hc : 0 < c := raw_gaussian_damped_coordinate_factors.2.1
  obtain ⟨Cb, hCb, hblock⟩ := smb_early_marked_block
  obtain ⟨Cs, hCs, hscalar⟩ := raw_gaussian_scalar_budget_integrals (c / 4) (by positivity)
  let C : ℝ := 1152 + Cb * Cs + Real.exp 1 * Cb * Cs
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro nu hnu n hn h2 hmean hnorm normalizedLaw R h P firstCube early
  letI : IsProbabilityMeasure nu := hnu
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hg := raw_truncation_budget_suffix_geometry nu n hn h2 (by rw [hnorm]; norm_num)
  simp only [hnorm, mul_one] at hg
  rcases hg with ⟨hRpos, hRone, hRlower, hhpos, hhhalf, hprefix, hret⟩
  have hs := hscalar nu n hn h2 hnorm
  let a3 : ℝ → ℝ := fun u => ∫ z : ℝ, |z| ^ 3 * Real.exp (-u * z ^ 2) ∂nu
  let gamma : ℝ := if (1 / 2 : ℝ) ≤ (∫ z : ℝ, if z ^ 2 ≤ h then z ^ 2 else 0 ∂nu) then -c else 1
  let K : ℕ → ℝ → ℝ := fun t s =>
    Real.rpow s (1 / 2 : ℝ) * a3 (s / 2) * Real.exp (gamma * s * ((t - 1 : ℕ) : ℝ))
  let L : ℝ → ℝ := fun s => Real.rpow s (-1 / 2 : ℝ) * a3 (s / 2)
  let E : ℝ → ℝ := fun s => Real.rpow s (1 / 2 : ℝ) * a3 (s / 2) * Real.exp (-(c / 4) * (n : ℝ) * s)
  let A : Finset ℕ := Finset.Icc ((n + 1) / 2) n
  have hpos (t : ℕ) (ht : t ∈ A) : 0 < t := by
    have ht' := Finset.mem_Icc.1 ht
    omega
  have htle (t : ℕ) (ht : t ∈ A) : t ≤ n := (Finset.mem_Icc.1 ht).2
  have hcard : (A.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show A.card ≤ n by dsimp [A]; rw [Nat.card_Icc]; omega)
  have hblk (t : ℕ) (ht : 0 < t) :
      Integrable (early t) (P t) ∧
        (∫ v, early t v ∂P t) ≤ Cb * ∫ s : ℝ in Set.Ioo 0 (1 / h), K t s ∧
        (∀ v, 0 ≤ early t v ∧ early t v ≤ (1 + Real.sqrt (t : ℝ)) ^ 3) := by
    cases t with
    | zero => omega
    | succ m =>
      have hz : (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) = 0 := by apply Fin.ext; simp
      simpa only [early, P, K, a3, gamma, c, firstCube, Nat.succ_pos, dite_true, Nat.succ_eq_add_one, Nat.add_sub_cancel, hz]
        using hblock nu h2 hmean hnorm m h hhpos
  have hKi (t : ℕ) : IntegrableOn (K t) (Set.Ioo 0 (1 / h)) := by
    simpa only [Nat.cast_ofNat, show (3 : ℝ) / 2 - 1 = 1 / 2 by norm_num] using
      smb_cutoff_moment_kernel_integrable nu h2 (t - 1) 3 (Or.inr rfl) h gamma hhpos
  have ha (s : ℝ) : 0 ≤ a3 (s / 2) := integral_nonneg fun z => by positivity
  have hLnn (s : ℝ) (hs0 : 0 ≤ s) : 0 ≤ L s :=
    mul_nonneg (Real.rpow_nonneg hs0 _) (ha s)
  have hEnn (s : ℝ) (hs0 : 0 ≤ s) : 0 ≤ E s :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0 _) (ha s)) (Real.exp_pos _).le
  have hL : IntegrableOn L (Set.Ioo 0 (1 / (n : ℝ))) := hs.1
  have hE : IntegrableOn E (Set.Ioi 0) := hs.2.2.2.1
  have hI0 : 0 ≤ ∫ s : ℝ in Set.Ioo 0 (1 / (n : ℝ)), L s := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact hLnn s hs.1.le
  have hIE : 0 ≤ ∫ s : ℝ in Set.Ioi 0, E s := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hEnn s hs.le
  refine ⟨fun t ht => (hblk t (hpos t ht)).1, ?_⟩
  change (∑ t ∈ A, ∫ v, early t v ∂P t) ≤ C * R
  by_cases hnsmall : n ≤ 3
  · have hEach (t : ℕ) (ht : t ∈ A) : (∫ v, early t v ∂P t) ≤ 64 := by
      have ht3 : (t : ℝ) ≤ 3 := by exact_mod_cast (htle t ht).trans hnsmall
      have hroot : Real.sqrt (t : ℝ) ≤ 3 := by
        nlinarith only [Real.sq_sqrt (Nat.cast_nonneg t), Real.sqrt_nonneg (t : ℝ), ht3]
      have hi := (hblk t (hpos t ht)).1
      have hb (v : Shao.Path t) : early t v ≤ 64 := by
        calc
          _ ≤ (1 + Real.sqrt (t : ℝ)) ^ 3 := (hblk t (hpos t ht)).2.2 v |>.2
          _ ≤ (4 : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
          _ = 64 := by norm_num
      simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
        integral_mono hi (integrable_const (64 : ℝ)) hb
    have hR6 : (1 / 6 : ℝ) ≤ R := by
      have hn3 : (n : ℝ) ≤ 3 := by exact_mod_cast hnsmall
      have hroot : Real.sqrt (2 * (n : ℝ)) ≤ 3 := by
        nlinarith only [Real.sq_sqrt (by positivity : 0 ≤ 2 * (n : ℝ)), Real.sqrt_nonneg (2 * (n : ℝ)), hn3]
      exact (one_div_le_one_div_of_le (by positivity : 0 < 2 * Real.sqrt (2 * (n : ℝ)))
        (by linarith : 2 * Real.sqrt (2 * (n : ℝ)) ≤ 6)).trans hRlower
    calc
      _ ≤ ∑ t ∈ A, (64 : ℝ) := Finset.sum_le_sum hEach
      _ = (A.card : ℝ) * 64 := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) * 64 := mul_le_mul_of_nonneg_right hcard (by norm_num)
      _ ≤ 192 := by
        have hn3 : (n : ℝ) ≤ 3 := by exact_mod_cast hnsmall
        linarith only [hn3]
      _ ≤ 1152 * R := by linarith only [hR6]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by dsimp [C]; linarith only [mul_pos hCb hCs, mul_pos (mul_pos (Real.exp_pos 1) hCb) hCs]) hRpos.le
  · have hn4 : 4 ≤ n := by omega
    by_cases hRsmall : R ≤ 1 / 2
    · have hgamma : gamma = -c := if_pos (hret hRsmall)
      have hEach (t : ℕ) (ht : t ∈ A) :
          (∫ v, early t v ∂P t) ≤ Cb * ∫ s : ℝ in Set.Ioi 0, E s := by
        apply (hblk t (hpos t ht)).2.1.trans
        apply mul_le_mul_of_nonneg_left _ hCb.le
        have hsub : Set.Ioo (0 : ℝ) (1 / h) ⊆ Set.Ioi 0 := fun _ hs => hs.1
        calc
          _ ≤ ∫ s : ℝ in Set.Ioo 0 (1 / h), E s := by
            apply integral_mono_ae (hKi t) (hE.mono_set hsub)
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs0
            have h4 : n ≤ 4 * (t - 1) := by
              have ht' := (Finset.mem_Icc.1 ht).1
              omega
            have hm : (n : ℝ) / 4 ≤ ((t - 1 : ℕ) : ℝ) := by
              have hh : (n : ℝ) ≤ 4 * ((t - 1 : ℕ) : ℝ) := by exact_mod_cast h4
              linarith only [hh]
            have hexp : Real.exp (gamma * s * ((t - 1 : ℕ) : ℝ)) ≤
                Real.exp (-(c / 4) * (n : ℝ) * s) := by
              rw [hgamma]
              apply Real.exp_le_exp.2
              have hh := mul_le_mul_of_nonneg_left hm (mul_nonneg hc.le hs0.1.le)
              nlinarith only [hh]
            exact mul_le_mul_of_nonneg_left hexp
              (mul_nonneg (Real.rpow_nonneg hs0.1.le _) (ha s))
          _ ≤ _ := setIntegral_mono_set hE
            (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs0; exact hEnn s hs0.le)
            (ae_of_all _ fun _ hs0 => hsub hs0)
      calc
        _ ≤ ∑ t ∈ A, (Cb * ∫ s : ℝ in Set.Ioi 0, E s) := Finset.sum_le_sum hEach
        _ = (A.card : ℝ) * (Cb * ∫ s : ℝ in Set.Ioi 0, E s) := by simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (n : ℝ) * (Cb * ∫ s : ℝ in Set.Ioi 0, E s) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg hCb.le hIE)
        _ = Cb * ((n : ℝ) * ∫ s : ℝ in Set.Ioi 0, E s) := by ring
        _ ≤ Cb * (Cs * R) := mul_le_mul_of_nonneg_left hs.2.2.2.2 hCb.le
        _ = (Cb * Cs) * R := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (by dsimp [C]; linarith only [mul_pos (mul_pos (Real.exp_pos 1) hCb) hCs]) hRpos.le
    · have hnle : (n : ℝ) ≤ h := by
        have hsq : 1 ≤ 4 * R ^ 2 := by nlinarith only [lt_of_not_ge hRsmall, sq_nonneg (R - 1 / 2)]
        have hh := mul_le_mul_of_nonneg_left hsq hN.le
        dsimp [h]
        nlinarith only [hh]
      have hsub : Set.Ioo (0 : ℝ) (1 / h) ⊆ Set.Ioo 0 (1 / (n : ℝ)) :=
        fun _ hs0 => ⟨hs0.1, hs0.2.trans_le (one_div_le_one_div_of_le hN hnle)⟩
      have hg1 : gamma ≤ 1 := by dsimp [gamma]; split_ifs <;> linarith only [hc]
      have hEach (t : ℕ) (ht : t ∈ A) :
          (∫ v, early t v ∂P t) ≤ Cb * ((Real.exp 1 / (n : ℝ)) *
            ∫ s : ℝ in Set.Ioo 0 (1 / (n : ℝ)), L s) := by
        apply (hblk t (hpos t ht)).2.1.trans
        apply mul_le_mul_of_nonneg_left _ hCb.le
        calc
          _ ≤ (Real.exp 1 / (n : ℝ)) * ∫ s : ℝ in Set.Ioo 0 (1 / h), L s := by
            rw [← integral_const_mul]
            apply integral_mono_ae (hKi t) ((hL.mono_set hsub).const_mul _)
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs0
            have hsn : s ≤ 1 / (n : ℝ) := (hsub hs0).2.le
            have hmt : ((t - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast ((Nat.sub_le t 1).trans (htle t ht))
            have he : Real.exp (gamma * s * ((t - 1 : ℕ) : ℝ)) ≤ Real.exp 1 := by
              apply Real.exp_le_exp.2
              calc
                _ ≤ s * ((t - 1 : ℕ) : ℝ) := by
                  simpa only [one_mul] using mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hg1 hs0.1.le) (Nat.cast_nonneg (t - 1))
                _ ≤ s * (n : ℝ) := mul_le_mul_of_nonneg_left hmt hs0.1.le
                _ ≤ 1 := (le_div_iff₀ hN).1 hsn
            have hpw : Real.rpow s (1 / 2 : ℝ) = Real.rpow s (-1 / 2 : ℝ) * s := by
              simp only [Real.rpow_eq_pow]
              rw [show (1 / 2 : ℝ) = -1 / 2 + 1 by norm_num, Real.rpow_add hs0.1, Real.rpow_one]
            change Real.rpow s (1 / 2 : ℝ) * a3 (s / 2) *
              Real.exp (gamma * s * ((t - 1 : ℕ) : ℝ)) ≤ _
            rw [hpw]
            have hh : s * Real.exp (gamma * s * ((t - 1 : ℕ) : ℝ)) ≤ Real.exp 1 / (n : ℝ) := by
              calc
                _ ≤ (1 / (n : ℝ)) * Real.exp 1 := mul_le_mul hsn he (Real.exp_pos _).le (one_div_pos.2 hN).le
                _ = _ := by ring
            convert mul_le_mul_of_nonneg_left hh (hLnn s hs0.1.le) using 1 <;> dsimp [L] <;> ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (setIntegral_mono_set hL
              (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs0; exact hLnn s hs0.1.le)
              (ae_of_all _ fun _ hs0 => hsub hs0)) (by positivity)
      calc
        _ ≤ ∑ t ∈ A, Cb * ((Real.exp 1 / (n : ℝ)) *
            ∫ s : ℝ in Set.Ioo 0 (1 / (n : ℝ)), L s) := Finset.sum_le_sum hEach
        _ = (A.card : ℝ) * (Cb * ((Real.exp 1 / (n : ℝ)) *
            ∫ s : ℝ in Set.Ioo 0 (1 / (n : ℝ)), L s)) := by simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (n : ℝ) * (Cb * ((Real.exp 1 / (n : ℝ)) *
            ∫ s : ℝ in Set.Ioo 0 (1 / (n : ℝ)), L s)) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg hCb.le (mul_nonneg (by positivity) hI0))
        _ = (Real.exp 1 * Cb) * (∫ s : ℝ in Set.Ioo 0 (1 / (n : ℝ)), L s) := by field_simp <;> ring
        _ ≤ (Real.exp 1 * Cb) * (Cs * R) := mul_le_mul_of_nonneg_left hs.2.1 (by positivity)
        _ = (Real.exp 1 * Cb * Cs) * R := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (by dsimp [C]; linarith only [mul_pos hCb hCs]) hRpos.le

private theorem smb_variance_normalization
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0) (hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂nu) :
    let sigma : ℝ := Real.sqrt (∫ z : ℝ, z ^ 2 ∂nu)
    let eta : Measure ℝ := Measure.map (fun z : ℝ => z / sigma) nu
    0 < sigma ∧ IsProbabilityMeasure eta ∧ Integrable (fun z : ℝ => z ^ 2) eta ∧
      (∫ z : ℝ, z ∂eta) = 0 ∧ (∫ z : ℝ, z ^ 2 ∂eta) = 1 ∧
      (∀ n : ℕ, Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) eta =
        Measure.map (fun z : ℝ => z / Real.sqrt ((n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu))) nu) ∧
      (∀ t : ℕ, Measure.map (fun v : Shao.Path t => fun i => v i / sigma)
        (Measure.pi (fun _ : Fin t => nu)) = Measure.pi (fun _ : Fin t => eta)) := by
  intro sigma eta
  have hs : 0 < sigma := Real.sqrt_pos.2 hsecond
  have hs2 : sigma ^ 2 = ∫ z : ℝ, z ^ 2 ∂nu := Real.sq_sqrt hsecond.le
  have hm : Measurable (fun z : ℝ => z / sigma) := measurable_id.div_const _
  have hp : IsProbabilityMeasure eta := by dsimp [eta]; infer_instance
  letI : IsProbabilityMeasure eta := hp
  have hi2 : Integrable (fun z : ℝ => z ^ 2) eta := by
    apply (integrable_map_measure (by fun_prop) hm.aemeasurable).2
    simpa only [Function.comp_def, div_pow] using h2.div_const (sigma ^ 2)
  have hme : (∫ z : ℝ, z ∂eta) = 0 := by
    rw [show eta = Measure.map (fun z : ℝ => z / sigma) nu from rfl,
      integral_map hm.aemeasurable (f := fun z : ℝ => z) (by fun_prop), integral_div, hmean, zero_div]
  have hnorm : (∫ z : ℝ, z ^ 2 ∂eta) = 1 := by
    rw [show eta = Measure.map (fun z : ℝ => z / sigma) nu from rfl,
      integral_map hm.aemeasurable (by fun_prop)]
    simp_rw [div_pow]
    rw [integral_div, hs2, div_self hsecond.ne']
  refine ⟨hs, hp, hi2, hme, hnorm, ?_, fun t => Measure.pi_map_pi (fun _ : Fin t => hm.aemeasurable)⟩
  intro n
  rw [show eta = Measure.map (fun z : ℝ => z / sigma) nu from rfl,
    Measure.map_map (f := fun z : ℝ => z / sigma)
      (g := fun z : ℝ => z / Real.sqrt (n : ℝ)) (measurable_id.div_const _) hm]
  congr 1
  funext z
  simp only [Function.comp_def, Real.sqrt_mul (Nat.cast_nonneg n)]
  dsimp [sigma]
  ring

private theorem smb_early_scale_invariance (t : ℕ) (v : Shao.Path t) (sigma b : ℝ) (hsigma : 0 < sigma) :
    let w : Shao.Path t := fun i => v i / sigma
    let firstCube : Shao.Path t → ℝ := fun a => if ht : 0 < t then |a ⟨0, ht⟩| ^ 3 else 0
    (if 0 < Shao.energy v ∧ sigma ^ 2 * b ≤ Shao.energy v then
      firstCube v / (Shao.energy v * Real.sqrt (Shao.energy v)) *
        (1 + |Shao.prefixSum v t| ^ 3 / (Shao.energy v * Real.sqrt (Shao.energy v))) else 0) =
    (if 0 < Shao.energy w ∧ b ≤ Shao.energy w then
      firstCube w / (Shao.energy w * Real.sqrt (Shao.energy w)) *
        (1 + |Shao.prefixSum w t| ^ 3 / (Shao.energy w * Real.sqrt (Shao.energy w))) else 0) := by
  intro w firstCube
  have he : Shao.energy w = Shao.energy v / sigma ^ 2 := by
    dsimp [Shao.energy, w]
    simp only [div_pow, Finset.sum_div]
  have hd : Shao.prefixSum w t = Shao.prefixSum v t / sigma := by
    dsimp [Shao.prefixSum, w]
    rw [Finset.sum_div]
  have hs : Real.sqrt (Shao.energy w) = Real.sqrt (Shao.energy v) / sigma := by
    rw [he, Real.sqrt_div (Shao.energy_nonneg v), Real.sqrt_sq hsigma.le]
  have hM : firstCube w = firstCube v / sigma ^ 3 := by
    dsimp [firstCube, w]
    split_ifs <;> simp only [abs_div, abs_of_pos hsigma, div_pow, zero_div]
  have hsigmasq : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
  have hguard : (0 < Shao.energy w ∧ b ≤ Shao.energy w) ↔
      (0 < Shao.energy v ∧ sigma ^ 2 * b ≤ Shao.energy v) := by
    rw [he, show (0 < Shao.energy v / sigma ^ 2) ↔ 0 < Shao.energy v by
      simpa only [zero_mul] using (lt_div_iff₀ hsigmasq :
        (0 : ℝ) < Shao.energy v / sigma ^ 2 ↔ 0 * sigma ^ 2 < Shao.energy v),
      le_div_iff₀ hsigmasq, mul_comm b]
  by_cases hv : 0 < Shao.energy v ∧ sigma ^ 2 * b ≤ Shao.energy v
  · rw [if_pos hv, if_pos (hguard.2 hv), hs, he, hd, hM]
    simp only [abs_div, abs_of_pos hsigma, div_pow]
    field_simp
    <;> ring
  · rw [if_neg hv, if_neg (fun hw => hv (hguard.1 hw))]

theorem iid_early_cubic_suffix_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → 0 < (∫ z : ℝ, z ^ 2 ∂nu) →
        let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂nu
        let scale : ℝ := Real.sqrt ((n : ℝ) * sigmaSq)
        let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
        let R : ℝ := Shao.truncationBudget normalizedLaw n 0
        let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
        let P : (t : ℕ) → Measure (Shao.Path t) := fun t => Measure.pi (fun _ : Fin t => nu)
        let firstCube : (t : ℕ) → Shao.Path t → ℝ := fun t v =>
          if ht : 0 < t then |v ⟨0, ht⟩| ^ 3 else 0
        let early : (t : ℕ) → Shao.Path t → ℝ := fun t v =>
          if 0 < Shao.energy v ∧ h ≤ Shao.energy v then
            firstCube t v / (Shao.energy v * Real.sqrt (Shao.energy v)) *
              (1 + |Shao.prefixSum v t| ^ 3 /
                (Shao.energy v * Real.sqrt (Shao.energy v)))
          else 0
        (∀ t ∈ Finset.Icc ((n + 1) / 2) n, Integrable (early t) (P t)) ∧
          (∑ t ∈ Finset.Icc ((n + 1) / 2) n, ∫ v, early t v ∂P t) ≤ C * R := by
  obtain ⟨C, hC, hu⟩ := smb_early_unit_budget
  refine ⟨C, hC, ?_⟩
  intro nu hnu n hn h2 hmean hsecond sigmaSq scale normalizedLaw R h P firstCube early
  letI : IsProbabilityMeasure nu := hnu
  let sigma : ℝ := Real.sqrt sigmaSq
  let eta : Measure ℝ := Measure.map (fun z : ℝ => z / sigma) nu
  have hd := smb_variance_normalization nu h2 hmean hsecond
  rcases hd with ⟨hsigma, hpeta, h2eta, hmeta, hneta, hmaps, hpis⟩
  letI : IsProbabilityMeasure eta := hpeta
  have hsigma2 : sigma ^ 2 = sigmaSq := Real.sq_sqrt hsecond.le
  let b : ℝ := 4 * (n : ℝ) * R ^ 2
  let E : (t : ℕ) → Shao.Path t → ℝ := fun t v =>
    if 0 < Shao.energy v ∧ b ≤ Shao.energy v then
      firstCube t v / (Shao.energy v * Real.sqrt (Shao.energy v)) *
        (1 + |Shao.prefixSum v t| ^ 3 / (Shao.energy v * Real.sqrt (Shao.energy v))) else 0
  let Pe : (t : ℕ) → Measure (Shao.Path t) := fun t => Measure.pi (fun _ : Fin t => eta)
  have hRmap : Shao.truncationBudget
      (Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) eta) n 0 = R := by
    rw [hmaps n]
  have hunit := hu eta n hn h2eta hmeta hneta
  dsimp only at hunit
  rw [hRmap] at hunit
  change (∀ t ∈ Finset.Icc ((n + 1) / 2) n, Integrable (E t) (Pe t)) ∧
    (∑ t ∈ Finset.Icc ((n + 1) / 2) n, ∫ v, E t v ∂Pe t) ≤ C * R at hunit
  have hh : h = sigma ^ 2 * b := by rw [hsigma2]; dsimp [h, b]; ring
  have hpoint (t : ℕ) (v : Shao.Path t) :
      early t v = E t (fun i => v i / sigma) := by
    dsimp only [early, E]
    rw [hh]
    exact smb_early_scale_invariance t v sigma b hsigma
  have hmp (t : ℕ) : MeasurePreserving (fun v : Shao.Path t => fun i => v i / sigma) (P t) (Pe t) :=
    ⟨Measurable.of_eval (fun i => (measurable_pi_apply i).div_const _), hpis t⟩
  have hi (t : ℕ) (ht : t ∈ Finset.Icc ((n + 1) / 2) n) : Integrable (early t) (P t) := by
    have hh := (hmp t).integrable_comp_of_integrable (hunit.1 t ht)
    exact hh.congr (ae_of_all _ fun v => (hpoint t v).symm)
  have heq (t : ℕ) (ht : t ∈ Finset.Icc ((n + 1) / 2) n) :
      (∫ v, early t v ∂P t) = ∫ v, E t v ∂Pe t := by
    calc
      _ = ∫ v, E t (fun i => v i / sigma) ∂P t := integral_congr_ae (ae_of_all _ (hpoint t))
      _ = _ := by
        rw [← (hmp t).map_eq]
        exact (integral_map (hmp t).measurable.aemeasurable
          (by rw [(hmp t).map_eq]; exact (hunit.1 t ht).aestronglyMeasurable)).symm
  refine ⟨hi, ?_⟩
  calc
    _ = ∑ t ∈ Finset.Icc ((n + 1) / 2) n, ∫ v, E t v ∂Pe t :=
      Finset.sum_congr rfl heq
    _ ≤ _ := hunit.2

private theorem smb_exponential_rank_sum (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (s : ℝ), 0 < s → s ≤ 2 →
      (∑ t ∈ Finset.Icc 1 N, Real.exp (-c * s * ((t - 1 : ℕ) : ℝ))) ≤ (N : ℝ) ∧
      (∑ t ∈ Finset.Icc 1 N, Real.exp (-c * s * ((t - 1 : ℕ) : ℝ))) ≤ C / s := by
  refine ⟨Real.exp (2 * c) / c, by positivity, ?_⟩
  intro N s hs hs2
  let q : ℝ := Real.exp (-c * s)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by nlinarith only [mul_pos hc hs])
  have he (t : ℕ) : Real.exp (-c * s * ((t - 1 : ℕ) : ℝ)) = q ^ (t - 1) := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsum : (∑ t ∈ Finset.Icc 1 N, q ^ (t - 1)) = ∑ i ∈ Finset.range N, q ^ i := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
      simp only [Nat.add_sub_cancel]
  simp_rw [he]
  rw [hsum]
  refine ⟨?_, ?_⟩
  · calc
      _ ≤ ∑ i ∈ Finset.range N, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
        pow_le_one₀ hq0 hq1.le
      _ = _ := by simp
  · have hden : 0 < 1 - q := sub_pos.2 hq1
    have hgeom : (∑ i ∈ Finset.range N, q ^ i) ≤ 1 / (1 - q) := by
      apply (le_div_iff₀ hden).2
      have hh := geom_sum_mul q N
      nlinarith only [hh, pow_nonneg hq0 N]
    have hu : 0 < c * s := mul_pos hc hs
    have hgap : c * s * Real.exp (-c * s) ≤ 1 - q := by
      have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (c * s)) (Real.exp_pos (-c * s)).le
      have heq : Real.exp (c * s) * Real.exp (-c * s) = 1 := by
        rw [← Real.exp_add, show c * s + -c * s = 0 by ring, Real.exp_zero]
      rw [heq] at hh
      dsimp [q]
      nlinarith only [hh]
    have hge : Real.exp (-(2 * c)) ≤ Real.exp (-c * s) := Real.exp_le_exp.2 (by nlinarith only [hs2, hc])
    have hlower : c * s * Real.exp (-(2 * c)) ≤ 1 - q :=
      (mul_le_mul_of_nonneg_left hge hu.le).trans hgap
    calc
      _ ≤ 1 / (1 - q) := hgeom
      _ ≤ 1 / (c * s * Real.exp (-(2 * c))) :=
        one_div_le_one_div_of_le (by positivity) hlower
      _ = _ := by
        rw [Real.exp_neg]
        field_simp
        <;> ring

private theorem smb_high_half_power (N : ℝ) (hN : 0 < N) :
    IntegrableOn (fun s : ℝ => Real.rpow s (-3 / 2 : ℝ)) (Set.Ioi (1 / N)) ∧
      (∫ s : ℝ in Set.Ioi (1 / N), Real.rpow s (-3 / 2 : ℝ)) = 2 * Real.sqrt N := by
  have hp : 0 < 1 / N := one_div_pos.2 hN
  refine ⟨integrableOn_Ioi_rpow_of_lt (by norm_num) hp, ?_⟩
  have hh := integral_Ioi_rpow_of_lt (a := (-3 / 2 : ℝ)) (by norm_num) hp
  convert hh using 1
  norm_num
  rw [Real.rpow_neg (inv_nonneg.mpr hN.le), ← Real.sqrt_eq_rpow, Real.sqrt_inv, inv_inv]
  ring

private theorem smb_suffix_product_map
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n r : ℕ) (hr : r ≤ n) :
    Measurable (fun v : Shao.Path n => Spitzer.tail v r hr) ∧
      Measure.map (fun v : Shao.Path n => Spitzer.tail v r hr)
        (Measure.pi (fun _ : Fin n => nu)) = Measure.pi (fun _ : Fin (n - r) => nu) := by
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let f : Fin (n - r) → Fin n := fun i => ⟨r + i.val, by omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hh := congrArg Fin.val hij
    dsimp [f] at hh
    omega
  let X : Fin n → Shao.Path n → ℝ := fun i v => v i
  have hX (i : Fin n) : Measurable (X i) := measurable_pi_apply i
  have hIndep : iIndepFun X P := iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P nu := by
    refine ⟨(hX i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id] using
      (measurePreserving_eval (μ := fun _ : Fin n => nu) i).map_eq
  exact ⟨measurable_samplePath (fun i => hX (f i)),
    iid_samplePath_map_eq_pi (fun i => hX (f i)) (hIndep.precomp hf) (fun i => hLaw (f i))⟩

private theorem smb_late_scale_invariance
    {t : ℕ} (v : Shao.Path t) (sigma H V R : ℝ) (hsigma : 0 < sigma) :
    SourceMarkedSuffixAveraging.lateAveragedWeight (sigma ^ 2 * H) (sigma ^ 2 * V) R v =
      SourceMarkedSuffixAveraging.lateAveragedWeight H V R (fun i => v i / sigma) := by
  let w : Shao.Path t := fun i => v i / sigma
  have he : Shao.energy w = Shao.energy v / sigma ^ 2 := by
    dsimp [Shao.energy, w]
    simp only [div_pow, Finset.sum_div]
  have hd : Shao.prefixSum w t = Shao.prefixSum v t / sigma := by
    dsimp [Shao.prefixSum, w]
    rw [Finset.sum_div]
  have hs : Real.sqrt (Shao.energy w) = Real.sqrt (Shao.energy v) / sigma := by
    rw [he, Real.sqrt_div (Shao.energy_nonneg v), Real.sqrt_sq hsigma.le]
  have hmass : SourceMarkedSuffixAveraging.cubicMass w =
      SourceMarkedSuffixAveraging.cubicMass v / sigma ^ 3 := by
    dsimp [SourceMarkedSuffixAveraging.cubicMass, w]
    simp only [abs_div, abs_of_pos hsigma, div_pow, Finset.sum_div]
  have hsigmasq : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
  have hpos : (0 < Shao.energy w) ↔ 0 < Shao.energy v := by
    rw [he]
    simpa only [zero_mul] using (lt_div_iff₀ hsigmasq :
      (0 : ℝ) < Shao.energy v / sigma ^ 2 ↔ 0 * sigma ^ 2 < Shao.energy v)
  have hguard : (H ≤ Shao.energy w) ↔ sigma ^ 2 * H ≤ Shao.energy v := by
    rw [he, le_div_iff₀ hsigmasq, mul_comm H]
  have hbeta : SourceMarkedSuffixAveraging.suffixBeta w = SourceMarkedSuffixAveraging.suffixBeta v := by
    unfold SourceMarkedSuffixAveraging.suffixBeta
    by_cases hv : 0 < Shao.energy v
    · rw [if_pos hv, if_pos (hpos.2 hv), hmass, hs, he]
      field_simp
    · rw [if_neg hv, if_neg (fun hw => hv (hpos.1 hw))]
  have hD : SourceMarkedSuffixAveraging.suffixD w = SourceMarkedSuffixAveraging.suffixD v := by
    unfold SourceMarkedSuffixAveraging.suffixD
    by_cases hv : 0 < Shao.energy v
    · rw [if_pos hv, if_pos (hpos.2 hv), hd, hs, abs_div, abs_of_pos hsigma]
      field_simp
    · rw [if_neg hv, if_neg (fun hw => hv (hpos.1 hw))]
  change _ = SourceMarkedSuffixAveraging.lateAveragedWeight H V R w
  unfold SourceMarkedSuffixAveraging.lateAveragedWeight
  by_cases hv : sigma ^ 2 * H ≤ Shao.energy v
  · rw [if_pos hv, if_pos (hguard.2 hv), hbeta, hD, he]
    field_simp
    <;> ring
  · rw [if_neg hv, if_neg (fun hw => hv (hguard.1 hw))]

private theorem smb_late_scalar_rank_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        let R : ℝ := Shao.truncationBudget (Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) nu) n 0
        let b : ℝ := 4 * (n : ℝ) * R ^ 2
        let c : ℝ := (1 - Real.exp (-2)) / 8
        let gamma : ℝ := if (1 / 2 : ℝ) ≤ (∫ z : ℝ, if z ^ 2 ≤ b then z ^ 2 else 0 ∂nu) then -c else 1
        let a3 : ℝ → ℝ := fun u => ∫ z : ℝ, |z| ^ 3 * Real.exp (-u * z ^ 2) ∂nu
        let K : ℕ → ℝ → ℝ := fun t s =>
          Real.rpow s (-1 / 2 : ℝ) * a3 (s / 2) * Real.exp (gamma * s * ((t - 1 : ℕ) : ℝ))
        (∑ t ∈ Finset.Icc 1 (n / 2), ∫ s : ℝ in Set.Ioo 0 (1 / b), K t s) ≤ C * (n : ℝ) * R := by
  let c : ℝ := (1 - Real.exp (-2)) / 8
  have hc : 0 < c := raw_gaussian_damped_coordinate_factors.2.1
  obtain ⟨Cg, hCg, hgeom⟩ := smb_exponential_rank_sum c hc
  obtain ⟨Cs, hCs, hscalar⟩ := raw_gaussian_scalar_budget_integrals 1 (by norm_num)
  let C : ℝ := Cs + 4 * Cg + Real.exp 1 * Cs
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro nu hnu n hn h2 hnorm R b c' gamma a3 K
  letI : IsProbabilityMeasure nu := hnu
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hg := raw_truncation_budget_suffix_geometry nu n hn h2 (by rw [hnorm]; norm_num)
  simp only [hnorm, mul_one] at hg
  rcases hg with ⟨hRpos, hRone, hRlower, hbpos, hbhalf, hprefix, hret⟩
  have hscl := hscalar nu n hn h2 hnorm
  let rho : ℝ := Real.sqrt (n : ℝ) * R
  let S : Set ℝ := Set.Ioo 0 (1 / b)
  let A : Finset ℕ := Finset.Icc 1 (n / 2)
  let L : ℝ → ℝ := fun s => Real.rpow s (-1 / 2 : ℝ) * a3 (s / 2)
  let F : ℝ → ℝ := fun s => ∑ t ∈ A, K t s
  have hL : IntegrableOn L (Set.Ioo 0 (1 / (n : ℝ))) := hscl.1
  have ha (s : ℝ) : 0 ≤ a3 (s / 2) := integral_nonneg fun z => by positivity
  have hLnn (s : ℝ) (hs : 0 ≤ s) : 0 ≤ L s := mul_nonneg (Real.rpow_nonneg hs _) (ha s)
  have hKt (t : ℕ) : IntegrableOn (K t) S := by
    simpa only [Nat.cast_one, show (1 : ℝ) / 2 - 1 = -1 / 2 by norm_num] using
      smb_cutoff_moment_kernel_integrable nu h2 (t - 1) 1 (Or.inl rfl) b gamma hbpos
  have hFi : IntegrableOn F S := integrable_finsetSum A (fun t _ => hKt t)
  have hsum : (∑ t ∈ A, ∫ s : ℝ in S, K t s) = ∫ s : ℝ in S, F s :=
    (integral_finsetSum A (fun t _ => hKt t)).symm
  have hfactor (s : ℝ) : F s = L s * ∑ t ∈ A, Real.exp (gamma * s * ((t - 1 : ℕ) : ℝ)) := by
    dsimp [F, K, L]
    rw [Finset.mul_sum]
  have hcard : (A.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show A.card ≤ n by dsimp [A]; rw [Nat.card_Icc]; omega)
  change (∑ t ∈ A, ∫ s : ℝ in S, K t s) ≤ C * (n : ℝ) * R
  rw [hsum]
  by_cases hRsmall : R ≤ 1 / 2
  · have hgamma : gamma = -c := if_pos (hret hRsmall)
    let B : Set ℝ := Set.Ioo 0 (1 / (n : ℝ))
    let J : ℝ → ℝ := fun s => Real.rpow s (-3 / 2 : ℝ)
    let H : Set ℝ := Set.Ioi (1 / (2 * (n : ℝ)))
    have hhigh := smb_high_half_power (2 * (n : ℝ)) (by positivity)
    have hLi : Integrable (B.indicator L) volume := (integrable_indicator_iff measurableSet_Ioo).2 hL
    have hJi : Integrable (H.indicator J) volume := (integrable_indicator_iff measurableSet_Ioi).2 hhigh.1
    let U : ℝ → ℝ := fun s => (n : ℝ) * B.indicator L s + (Cg * rho) * H.indicator J s
    have hUi : Integrable U volume := (hLi.const_mul _).add (hJi.const_mul _)
    have hBnn (s : ℝ) : 0 ≤ B.indicator L s := by
      by_cases hs : s ∈ B
      · rw [Set.indicator_of_mem hs]; exact hLnn s hs.1.le
      · rw [Set.indicator_of_notMem hs]
    have hHnn (s : ℝ) : 0 ≤ H.indicator J s := by
      by_cases hs : s ∈ H
      · rw [Set.indicator_of_mem hs]
        exact Real.rpow_nonneg ((one_div_pos.2 (by positivity : 0 < 2 * (n : ℝ))).le.trans hs.le) _
      · rw [Set.indicator_of_notMem hs]
    have hUnn (s : ℝ) : 0 ≤ U s :=
      add_nonneg (mul_nonneg hN.le (hBnn s)) (mul_nonneg (by dsimp [rho]; positivity) (hHnn s))
    have hpoint (s : ℝ) (hs : s ∈ S) : F s ≤ U s := by
      have hs0 : 0 < s := hs.1
      have hs2 : s ≤ 2 := hs.2.le.trans ((div_le_iff₀ hbpos).2 (by linarith only [hbhalf]))
      have hg' := hgeom (n / 2) s hs0 hs2
      rw [hfactor, hgamma]
      by_cases hslow : s < 1 / (n : ℝ)
      · have hmem : s ∈ B := ⟨hs0, hslow⟩
        calc
          _ ≤ L s * ((n / 2 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hg'.1 (hLnn s hs0.le)
          _ ≤ L s * (n : ℝ) := mul_le_mul_of_nonneg_left
            (by exact_mod_cast (Nat.div_le_self n 2)) (hLnn s hs0.le)
          _ = (n : ℝ) * B.indicator L s := by rw [Set.indicator_of_mem hmem]; ring
          _ ≤ U s := le_add_of_nonneg_right (mul_nonneg (by dsimp [rho]; positivity) (hHnn s))
      · have hsn : 1 / (n : ℝ) ≤ s := le_of_not_gt hslow
        have hmem : s ∈ H := by
          have hh : 1 / (2 * (n : ℝ)) < 1 / (n : ℝ) :=
            one_div_lt_one_div_of_lt hN (by linarith only [hN])
          exact hh.trans_le hsn
        have hmark : a3 (s / 2) ≤ rho := smb_raw_mark_budget_point nu n hn h2 s hsn
        have hpw : Real.rpow s (-1 / 2 : ℝ) / s = Real.rpow s (-3 / 2 : ℝ) := by
          simp only [Real.rpow_eq_pow]
          rw [show (-1 / 2 : ℝ) = -3 / 2 + 1 by norm_num, Real.rpow_add hs0, Real.rpow_one]
          field_simp
        calc
          _ ≤ L s * (Cg / s) := mul_le_mul_of_nonneg_left hg'.2 (hLnn s hs0.le)
          _ = (Cg * a3 (s / 2)) * J s := by
            dsimp [L, J]
            simp only [Real.rpow_eq_pow] at hpw
            rw [← hpw]
            ring
          _ ≤ (Cg * rho) * J s := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmark hCg.le) (Real.rpow_nonneg hs0.le _)
          _ = (Cg * rho) * H.indicator J s := by rw [Set.indicator_of_mem hmem]
          _ ≤ U s := le_add_of_nonneg_left (mul_nonneg hN.le (hBnn s))
    have htail : 2 * Real.sqrt (2 * (n : ℝ)) ≤ 4 * Real.sqrt (n : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hs2 : Real.sqrt 2 ≤ 2 := by nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      have hh := mul_le_mul_of_nonneg_right hs2 (Real.sqrt_nonneg (n : ℝ))
      linarith only [hh]
    calc
      _ ≤ ∫ s : ℝ in S, U s := by
        apply integral_mono_ae hFi hUi.integrableOn
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact hpoint s hs
      _ ≤ ∫ s : ℝ, U s := setIntegral_le_integral hUi (ae_of_all _ hUnn)
      _ = (n : ℝ) * (∫ s : ℝ in B, L s) + (Cg * rho) * (2 * Real.sqrt (2 * (n : ℝ))) := by
        rw [show U = fun s => (n : ℝ) * B.indicator L s + (Cg * rho) * H.indicator J s from rfl,
          integral_add (hLi.const_mul _) (hJi.const_mul _), integral_const_mul, integral_const_mul,
          integral_indicator measurableSet_Ioo, integral_indicator measurableSet_Ioi, hhigh.2]
      _ ≤ (n : ℝ) * (Cs * R) + (Cg * rho) * (4 * Real.sqrt (n : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hscl.2.1 hN.le)
          (mul_le_mul_of_nonneg_left htail (by dsimp [rho]; positivity))
      _ = (Cs + 4 * Cg) * (n : ℝ) * R := by
        dsimp [rho]
        calc
          _ = Cs * (n : ℝ) * R + (4 * Cg * R) * Real.sqrt (n : ℝ) ^ 2 := by ring
          _ = _ := by rw [Real.sq_sqrt hN.le]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith only [mul_pos (Real.exp_pos 1) hCs]) hN.le) hRpos.le
  · have hnle : (n : ℝ) ≤ b := by
      have hsq : 1 ≤ 4 * R ^ 2 := by nlinarith only [lt_of_not_ge hRsmall, sq_nonneg (R - 1 / 2)]
      have hh := mul_le_mul_of_nonneg_left hsq hN.le
      dsimp [b]
      nlinarith only [hh]
    have hsub : S ⊆ Set.Ioo 0 (1 / (n : ℝ)) :=
      fun _ hs => ⟨hs.1, hs.2.trans_le (one_div_le_one_div_of_le hN hnle)⟩
    have hg1 : gamma ≤ 1 := by
      dsimp only [gamma]
      split_ifs
      · change -c ≤ 1
        linarith only [hc]
      · exact le_rfl
    have hpoint (s : ℝ) (hs : s ∈ S) : F s ≤ ((n : ℝ) * Real.exp 1) * L s := by
      have hsn : s ≤ 1 / (n : ℝ) := (hsub hs).2.le
      have he (t : ℕ) (ht : t ∈ A) : Real.exp (gamma * s * ((t - 1 : ℕ) : ℝ)) ≤ Real.exp 1 := by
        have htN : ((t - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast ((Nat.sub_le t 1).trans ((Finset.mem_Icc.1 ht).2.trans (Nat.div_le_self n 2)))
        apply Real.exp_le_exp.2
        calc
          _ ≤ s * ((t - 1 : ℕ) : ℝ) := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hg1 hs.1.le) (Nat.cast_nonneg (t - 1))
          _ ≤ s * (n : ℝ) := mul_le_mul_of_nonneg_left htN hs.1.le
          _ ≤ 1 := (le_div_iff₀ hN).1 hsn
      rw [hfactor]
      calc
        _ ≤ L s * (∑ t ∈ A, Real.exp 1) := mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum he) (hLnn s hs.1.le)
        _ = L s * ((A.card : ℝ) * Real.exp 1) := by simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ L s * ((n : ℝ) * Real.exp 1) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le) (hLnn s hs.1.le)
        _ = _ := by ring
    calc
      _ ≤ ((n : ℝ) * Real.exp 1) * ∫ s : ℝ in S, L s := by
        rw [← integral_const_mul]
        apply integral_mono_ae hFi ((hL.mono_set hsub).const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact hpoint s hs
      _ ≤ ((n : ℝ) * Real.exp 1) * ∫ s : ℝ in Set.Ioo 0 (1 / (n : ℝ)), L s :=
        mul_le_mul_of_nonneg_left
          (setIntegral_mono_set hL
            (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs; exact hLnn s hs.1.le)
            (ae_of_all _ fun _ hs => hsub hs)) (by positivity)
      _ ≤ ((n : ℝ) * Real.exp 1) * (Cs * R) := mul_le_mul_of_nonneg_left hscl.2.1 (by positivity)
      _ = (Real.exp 1 * Cs) * (n : ℝ) * R := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith only [hCs, hCg]) hN.le) hRpos.le

private theorem smb_late_unit_product_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        let R : ℝ := Shao.truncationBudget (Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) nu) n 0
        let h : ℝ := 4 * (n : ℝ) * R ^ 2
        let Rprefix : ℕ → ℝ := fun t =>
          Shao.truncationBudget (Measure.map (fun z : ℝ => z / Real.sqrt ((n - t : ℕ) : ℝ)) nu) (n - t) 0
        let P : (t : ℕ) → Measure (Shao.Path t) := fun t => Measure.pi (fun _ : Fin t => nu)
        let late : (t : ℕ) → Shao.Path t → ℝ := fun t =>
          SourceMarkedSuffixAveraging.lateAveragedWeight h ((n - t : ℕ) : ℝ) (Rprefix t)
        (∀ t ∈ Finset.Icc 1 (n / 2), Integrable (late t) (P t)) ∧
          (∑ t ∈ Finset.Icc 1 (n / 2), ∫ v, late t v ∂P t) ≤ C * R := by
  obtain ⟨Ci, hCi, hinverse⟩ := iid_marked_cutoff_inverse_moments 5 1 (Or.inl rfl)
  obtain ⟨Cs, hCs, hscalar⟩ := smb_late_scalar_rank_budget
  refine ⟨(5 / 2 : ℝ) * Ci * Cs, by positivity, ?_⟩
  intro nu hnu n hn h2 hmean hnorm R h Rprefix P late
  letI : IsProbabilityMeasure nu := hnu
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hg := raw_truncation_budget_suffix_geometry nu n hn h2 (by rw [hnorm]; norm_num)
  simp only [hnorm, mul_one] at hg
  rcases hg with ⟨hRpos, hRone, hRlower, hhpos, hhhalf, hpref, hret⟩
  let c : ℝ := (1 - Real.exp (-2)) / 8
  let gamma : ℝ := if (1 / 2 : ℝ) ≤ (∫ z : ℝ, if z ^ 2 ≤ h then z ^ 2 else 0 ∂nu) then -c else 1
  let a3 : ℝ → ℝ := fun u => ∫ z : ℝ, |z| ^ 3 * Real.exp (-u * z ^ 2) ∂nu
  let K : ℕ → ℝ → ℝ := fun t s =>
    Real.rpow s (-1 / 2 : ℝ) * a3 (s / 2) * Real.exp (gamma * s * ((t - 1 : ℕ) : ℝ))
  have hr (t : ℕ) (ht : t ∈ Finset.Icc 1 (n / 2)) : 0 < n - t := by
    have ht' := Finset.mem_Icc.1 ht
    omega
  have hbracket (t : ℕ) (ht : t ∈ Finset.Icc 1 (n / 2)) (T : ℝ) (hT : h ≤ T) :
      T / ((n - t : ℕ) : ℝ) + Rprefix t ^ 2 ≤ (5 / (2 * (n : ℝ))) * T := by
    have hrp : 0 < ((n - t : ℕ) : ℝ) := by exact_mod_cast hr t ht
    have hrN : n - t ≤ n := Nat.sub_le _ _
    have hnr : (n : ℝ) ≤ 2 * ((n - t : ℕ) : ℝ) := by
      exact_mod_cast (show n ≤ 2 * (n - t) by have ht' := Finset.mem_Icc.1 ht; omega)
    have hRatio : (n : ℝ) / ((n - t : ℕ) : ℝ) ≤ 2 := (div_le_iff₀ hrp).2 (by linarith only [hnr])
    have hRp0 : 0 ≤ Rprefix t := by
      dsimp [Rprefix, Shao.truncationBudget]
      exact mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun z => Shao.truncationF_nonneg _)
    have hRp := hpref (n - t) (hr t ht) hrN
    have hRp2 : Rprefix t ^ 2 ≤ 2 * R ^ 2 := by
      have hh := mul_self_le_mul_self hRp0 hRp
      rw [← pow_two, ← pow_two, mul_pow, Real.sq_sqrt (div_nonneg hN.le hrp.le)] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right hRatio (sq_nonneg R))
    have hTp : 0 ≤ T := hhpos.le.trans hT
    have hTr : T / ((n - t : ℕ) : ℝ) ≤ 2 * T / (n : ℝ) := by
      apply (div_le_iff₀ hrp).2
      calc
        T = (T * (n : ℝ)) / (n : ℝ) := by field_simp
        _ ≤ (T * (2 * ((n - t : ℕ) : ℝ))) / (n : ℝ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnr hTp) hN.le
        _ = _ := by ring
    have hRbound : 2 * R ^ 2 ≤ T / (2 * (n : ℝ)) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * (n : ℝ))).2
      convert hT using 1 <;> dsimp [h] <;> ring
    calc
      _ ≤ 2 * T / (n : ℝ) + T / (2 * (n : ℝ)) := add_le_add hTr (hRp2.trans hRbound)
      _ = _ := by ring
  have hEach (t : ℕ) (ht : t ∈ Finset.Icc 1 (n / 2)) :
      Integrable (late t) (P t) ∧ (∫ v, late t v ∂P t) ≤
        ((5 / (2 * (n : ℝ))) * Ci) * ∫ s : ℝ in Set.Ioo 0 (1 / h), K t s := by
    have htp : 0 < t := (Finset.mem_Icc.1 ht).1
    have hrp : 0 < ((n - t : ℕ) : ℝ) := by exact_mod_cast hr t ht
    cases t with
    | zero => omega
    | succ m =>
      have hav := SourceMarkedSuffixAveraging.iid_product_late_marked_integral_eq_average
        (Nat.succ_pos m) nu h2 h ((n - (m + 1) : ℕ) : ℝ) (Rprefix (m + 1)) hhpos hrp (0 : Fin (m + 1))
      have hi := hinverse nu h2 hmean hnorm m h hhpos
      let J : Shao.Path (m + 1) → ℝ := fun v =>
        if 0 < Shao.energy v ∧ h ≤ Shao.energy v then
          |v 0| ^ 3 / Real.sqrt (Shao.energy v) *
            (1 + |Shao.prefixSum v (m + 1)| / Real.sqrt (Shao.energy v)) ^ 5 else 0
      have hJi : Integrable J (P (m + 1)) := by simpa only [pow_one] using hi.1
      have hpoint (v : Shao.Path (m + 1)) :
          SourceMarkedSuffixAveraging.lateMarkedWeight h ((n - (m + 1) : ℕ) : ℝ) (Rprefix (m + 1)) v 0 ≤
            (5 / (2 * (n : ℝ))) * J v := by
        by_cases hv : h ≤ Shao.energy v
        · have hvp : 0 < Shao.energy v := hhpos.trans_le hv
          have hnn : 0 ≤ |v 0| ^ 3 / (Shao.energy v * Real.sqrt (Shao.energy v)) *
              (1 + |Shao.prefixSum v (m + 1)| / Real.sqrt (Shao.energy v)) ^ 5 := by positivity
          dsimp [SourceMarkedSuffixAveraging.lateMarkedWeight, SourceMarkedSuffixAveraging.normalizedCubicMark,
            SourceMarkedSuffixAveraging.suffixD, J]
          rw [if_pos hv, if_pos hvp, if_pos hvp, if_pos ⟨hvp, hv⟩]
          calc
            _ ≤ (|v 0| ^ 3 / (Shao.energy v * Real.sqrt (Shao.energy v)) *
                (1 + |Shao.prefixSum v (m + 1)| / Real.sqrt (Shao.energy v)) ^ 5) *
                  ((5 / (2 * (n : ℝ))) * Shao.energy v) :=
              mul_le_mul_of_nonneg_left (hbracket (m + 1) ht _ hv) hnn
            _ = _ := by field_simp <;> ring
        · have hj : ¬ (0 < Shao.energy v ∧ h ≤ Shao.energy v) := fun hh => hv hh.2
          simp only [SourceMarkedSuffixAveraging.lateMarkedWeight, if_neg hv, J, if_neg hj, mul_zero]
          exact le_rfl
      refine ⟨hav.2.1, ?_⟩
      calc
        _ = ∫ v, SourceMarkedSuffixAveraging.lateMarkedWeight h ((n - (m + 1) : ℕ) : ℝ)
            (Rprefix (m + 1)) v 0 ∂P (m + 1) := hav.2.2.symm
        _ ≤ (5 / (2 * (n : ℝ))) * ∫ v, J v ∂P (m + 1) := by
          rw [← integral_const_mul]
          exact integral_mono hav.1 (hJi.const_mul _) hpoint
        _ ≤ (5 / (2 * (n : ℝ))) * (Ci * ∫ s : ℝ in Set.Ioo 0 (1 / h), K (m + 1) s) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa only [J, P, K, a3, gamma, c, pow_one, Nat.add_sub_cancel, Nat.cast_one,
            show (1 : ℝ) / 2 - 1 = -1 / 2 by norm_num] using hi.2.2
        _ = _ := by ring
  refine ⟨fun t ht => (hEach t ht).1, ?_⟩
  calc
    _ ≤ ∑ t ∈ Finset.Icc 1 (n / 2),
        ((5 / (2 * (n : ℝ))) * Ci) * ∫ s : ℝ in Set.Ioo 0 (1 / h), K t s :=
      Finset.sum_le_sum fun t ht => (hEach t ht).2
    _ = ((5 / (2 * (n : ℝ))) * Ci) *
        (∑ t ∈ Finset.Icc 1 (n / 2), ∫ s : ℝ in Set.Ioo 0 (1 / h), K t s) := (Finset.mul_sum _ _ _).symm
    _ ≤ ((5 / (2 * (n : ℝ))) * Ci) * (Cs * (n : ℝ) * R) :=
      mul_le_mul_of_nonneg_left (hscalar nu n hn h2 hnorm) (by positivity)
    _ = _ := by field_simp <;> ring

private theorem smb_late_raw_product_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → 0 < (∫ z : ℝ, z ^ 2 ∂nu) →
        let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂nu
        let R : ℝ := Shao.truncationBudget
          (Measure.map (fun z : ℝ => z / Real.sqrt ((n : ℝ) * sigmaSq)) nu) n 0
        let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
        let Rprefix : ℕ → ℝ := fun t =>
          Shao.truncationBudget
            (Measure.map (fun z : ℝ => z / Real.sqrt (((n - t : ℕ) : ℝ) * sigmaSq)) nu) (n - t) 0
        let P : (t : ℕ) → Measure (Shao.Path t) := fun t => Measure.pi (fun _ : Fin t => nu)
        let late : (t : ℕ) → Shao.Path t → ℝ := fun t =>
          SourceMarkedSuffixAveraging.lateAveragedWeight h (((n - t : ℕ) : ℝ) * sigmaSq) (Rprefix t)
        (∀ t ∈ Finset.Icc 1 (n / 2), Integrable (late t) (P t)) ∧
          (∑ t ∈ Finset.Icc 1 (n / 2), ∫ v, late t v ∂P t) ≤ C * R := by
  obtain ⟨C, hC, hu⟩ := smb_late_unit_product_budget
  refine ⟨C, hC, ?_⟩
  intro nu hnu n hn h2 hmean hsecond sigmaSq R h Rprefix P late
  letI : IsProbabilityMeasure nu := hnu
  let sigma : ℝ := Real.sqrt sigmaSq
  let eta : Measure ℝ := Measure.map (fun z : ℝ => z / sigma) nu
  have hd := smb_variance_normalization nu h2 hmean hsecond
  rcases hd with ⟨hsigma, hpeta, h2eta, hmeta, hneta, hmaps, hpis⟩
  letI : IsProbabilityMeasure eta := hpeta
  have hsigma2 : sigma ^ 2 = sigmaSq := Real.sq_sqrt hsecond.le
  let b : ℝ := 4 * (n : ℝ) * R ^ 2
  let E : (t : ℕ) → Shao.Path t → ℝ := fun t =>
    SourceMarkedSuffixAveraging.lateAveragedWeight b ((n - t : ℕ) : ℝ) (Rprefix t)
  let Pe : (t : ℕ) → Measure (Shao.Path t) := fun t => Measure.pi (fun _ : Fin t => eta)
  have hRmap : Shao.truncationBudget
      (Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) eta) n 0 = R := by rw [hmaps n]
  have hRpmap (t : ℕ) : Shao.truncationBudget
      (Measure.map (fun z : ℝ => z / Real.sqrt ((n - t : ℕ) : ℝ)) eta) (n - t) 0 = Rprefix t := by
    rw [hmaps (n - t)]
  have hunit := hu eta n hn h2eta hmeta hneta
  dsimp only at hunit
  rw [hRmap] at hunit
  simp_rw [hRpmap] at hunit
  change (∀ t ∈ Finset.Icc 1 (n / 2), Integrable (E t) (Pe t)) ∧
    (∑ t ∈ Finset.Icc 1 (n / 2), ∫ v, E t v ∂Pe t) ≤ C * R at hunit
  have hh : h = sigma ^ 2 * b := by rw [hsigma2]; dsimp [h, b]; ring
  have hpoint (t : ℕ) (v : Shao.Path t) : late t v = E t (fun i => v i / sigma) := by
    change SourceMarkedSuffixAveraging.lateAveragedWeight h (((n - t : ℕ) : ℝ) * sigmaSq) (Rprefix t) v = _
    have hV : ((n - t : ℕ) : ℝ) * sigmaSq = sigma ^ 2 * ((n - t : ℕ) : ℝ) := by rw [hsigma2]; ring
    rw [hh, hV]
    exact smb_late_scale_invariance v sigma b ((n - t : ℕ) : ℝ) (Rprefix t) hsigma
  have hmp (t : ℕ) : MeasurePreserving (fun v : Shao.Path t => fun i => v i / sigma) (P t) (Pe t) :=
    ⟨Measurable.of_eval (fun i => (measurable_pi_apply i).div_const _), hpis t⟩
  have hi (t : ℕ) (ht : t ∈ Finset.Icc 1 (n / 2)) : Integrable (late t) (P t) :=
    ((hmp t).integrable_comp_of_integrable (hunit.1 t ht)).congr (ae_of_all _ fun v => (hpoint t v).symm)
  have heq (t : ℕ) (ht : t ∈ Finset.Icc 1 (n / 2)) :
      (∫ v, late t v ∂P t) = ∫ v, E t v ∂Pe t := by
    calc
      _ = ∫ v, E t (fun i => v i / sigma) ∂P t := integral_congr_ae (ae_of_all _ (hpoint t))
      _ = _ := by
        rw [← (hmp t).map_eq]
        exact (integral_map (hmp t).measurable.aemeasurable
          (by rw [(hmp t).map_eq]; exact (hunit.1 t ht).aestronglyMeasurable)).symm
  refine ⟨hi, ?_⟩
  calc
    _ = ∑ t ∈ Finset.Icc 1 (n / 2), ∫ v, E t v ∂Pe t := Finset.sum_congr rfl heq
    _ ≤ _ := hunit.2

theorem iid_late_fifth_and_cubic_suffix_budgets :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → 0 < (∫ z : ℝ, z ^ 2 ∂nu) →
        let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂nu
        let scale : ℝ := Real.sqrt ((n : ℝ) * sigmaSq)
        let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
        let R : ℝ := Shao.truncationBudget normalizedLaw n 0
        let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
        let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
        let suffix : (t : ℕ) → Shao.Path n → Shao.Path (n - (n - t)) := fun t v =>
          Spitzer.tail v (n - t) (Nat.sub_le n t)
        let T : ℕ → Shao.Path n → ℝ := fun t v => Shao.energy (suffix t v)
        let d : ℕ → Shao.Path n → ℝ := fun t v =>
          Shao.prefixSum (suffix t v) (n - (n - t))
        let beta : ℕ → Shao.Path n → ℝ := fun t v =>
          if 0 < T t v then
            (∑ i : Fin (n - (n - t)), |suffix t v i| ^ 3) /
              (T t v * Real.sqrt (T t v))
          else 0
        let D : ℕ → Shao.Path n → ℝ := fun t v =>
          if 0 < T t v then 1 + |d t v| / Real.sqrt (T t v) else 1
        let Rprefix : ℕ → ℝ := fun t =>
          Shao.truncationBudget
            (Measure.map (fun z : ℝ => z /
              Real.sqrt (((n - t : ℕ) : ℝ) * sigmaSq)) nu) (n - t) 0
        let late : ℕ → ℕ → Shao.Path n → ℝ := fun p t v =>
          if 0 < T t v ∧ h ≤ T t v then
            (beta t v / (t : ℝ)) * D t v ^ p *
              (T t v / (((n - t : ℕ) : ℝ) * sigmaSq) + Rprefix t ^ 2)
          else 0
        ∀ p : ℕ, (p = 3 ∨ p = 5) →
          (∀ t ∈ Finset.Icc 1 (n / 2), Integrable (late p t) P) ∧
            (∑ t ∈ Finset.Icc 1 (n / 2), ∫ v, late p t v ∂P) ≤ C * R := by
  obtain ⟨C, hC, hraw⟩ := smb_late_raw_product_budget
  refine ⟨C, hC, ?_⟩
  intro nu hnu n hn h2 hmean hsecond sigmaSq scale normalizedLaw R h P suffix T d beta D Rprefix late
  letI : IsProbabilityMeasure nu := hnu
  have hg := raw_truncation_budget_suffix_geometry nu n hn h2 hsecond
  have hhpos : 0 < h := hg.2.2.2.1
  have hprod := hraw nu n hn h2 hmean hsecond
  let Q : (t : ℕ) → Measure (Shao.Path t) := fun t => Measure.pi (fun _ : Fin t => nu)
  let W : (t : ℕ) → Shao.Path t → ℝ := fun t =>
    SourceMarkedSuffixAveraging.lateAveragedWeight h (((n - t : ℕ) : ℝ) * sigmaSq) (Rprefix t)
  let A : ℕ → Shao.Path n → ℝ := fun t v =>
    SourceMarkedSuffixAveraging.lateAveragedWeight h (((n - t : ℕ) : ℝ) * sigmaSq) (Rprefix t) (suffix t v)
  have hsp (t : ℕ) : Measurable (suffix t) ∧
      Measure.map (suffix t) P = Measure.pi (fun _ : Fin (n - (n - t)) => nu) :=
    smb_suffix_product_map nu n (n - t) (Nat.sub_le n t)
  have hActual (t : ℕ) (ht : t ∈ Finset.Icc 1 (n / 2)) :
      Integrable (A t) P ∧ (∫ v, A t v ∂P) = ∫ v, W t v ∂Q t := by
    have htn : t ≤ n := (Finset.mem_Icc.1 ht).2.trans (Nat.div_le_self n 2)
    have hlen : n - (n - t) = t := Nat.sub_sub_self htn
    have hId : IdentDistrib (suffix t) (id : Shao.Path (n - (n - t)) → Shao.Path (n - (n - t)))
        P (Measure.pi (fun _ : Fin (n - (n - t)) => nu)) :=
      ⟨(hsp t).1.aemeasurable, measurable_id.aemeasurable, by rw [Measure.map_id]; exact (hsp t).2⟩
    have hObs := hId.comp
      (SourceMarkedSuffixAveraging.late_weights_measurable_and_covariant
        (t := n - (n - t)) h (((n - t : ℕ) : ℝ) * sigmaSq) (Rprefix t)).2.1
    have hi : Integrable
        (SourceMarkedSuffixAveraging.lateAveragedWeight h (((n - t : ℕ) : ℝ) * sigmaSq) (Rprefix t) :
          Shao.Path (n - (n - t)) → ℝ)
        (Measure.pi (fun _ : Fin (n - (n - t)) => nu)) := by
      rw [hlen]
      exact hprod.1 t ht
    refine ⟨hObs.symm.integrable_snd hi, ?_⟩
    calc
      _ = ∫ v : Shao.Path (n - (n - t)),
          SourceMarkedSuffixAveraging.lateAveragedWeight h (((n - t : ℕ) : ℝ) * sigmaSq)
            (Rprefix t) v ∂Measure.pi (fun _ : Fin (n - (n - t)) => nu) := hObs.integral_eq
      _ = _ := by rw [hlen]
  intro p hp
  have hp5 : p ≤ 5 := by rcases hp with rfl | rfl <;> norm_num
  have hpoint (t : ℕ) (ht : t ∈ Finset.Icc 1 (n / 2)) (v : Shao.Path n) :
      0 ≤ late p t v ∧ late p t v ≤ A t v := by
    have htp : 0 < (t : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 ht).1
    have hr : 0 < n - t := by have ht' := Finset.mem_Icc.1 ht; omega
    have hV : 0 < ((n - t : ℕ) : ℝ) * sigmaSq := mul_pos (by exact_mod_cast hr) hsecond
    have hgeometry := SourceMarkedSuffixAveraging.suffix_normalized_geometry (suffix t v)
    have hbeta : 0 ≤ beta t v := hgeometry.2.2.2.2.1.1
    have hD : 1 ≤ D t v := hgeometry.2.2.2.2.2.1.1
    have hbr : 0 ≤ T t v / (((n - t : ℕ) : ℝ) * sigmaSq) + Rprefix t ^ 2 :=
      add_nonneg (div_nonneg (Shao.energy_nonneg _) hV.le) (sq_nonneg _)
    by_cases hv : 0 < T t v ∧ h ≤ T t v
    · have hA : A t v = (beta t v / (t : ℝ)) * D t v ^ 5 *
          (T t v / (((n - t : ℕ) : ℝ) * sigmaSq) + Rprefix t ^ 2) := by
        change (if h ≤ T t v then _ else 0) = _
        rw [if_pos hv.2]
        have hlen : ((n - (n - t) : ℕ) : ℝ) = (t : ℝ) := by
          exact_mod_cast Nat.sub_sub_self ((Finset.mem_Icc.1 ht).2.trans (Nat.div_le_self n 2))
        rw [hlen]
        rfl
      dsimp only [late]
      rw [if_pos hv, hA]
      refine ⟨mul_nonneg (mul_nonneg (div_nonneg hbeta htp.le) (pow_nonneg (by linarith only [hD]) _)) hbr, ?_⟩
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hp5) (div_nonneg hbeta htp.le)) hbr
    · have hAH : ¬ h ≤ T t v := fun hh => hv ⟨hhpos.trans_le hh, hh⟩
      dsimp only [late]
      rw [if_neg hv]
      refine ⟨le_rfl, ?_⟩
      change 0 ≤ (if h ≤ T t v then _ else 0)
      rw [if_neg hAH]
  have hm (t : ℕ) : Measurable (late p t) := by
    have hTm : Measurable (T t) := Shao.measurable_energy.comp (hsp t).1
    have hdm : Measurable (d t) := (Shao.measurable_prefixSum (n - (n - t))).comp (hsp t).1
    have hcm : Measurable (fun v : Shao.Path n => ∑ i : Fin (n - (n - t)), |suffix t v i| ^ 3) :=
      Finset.measurable_sum _ (fun i _ =>
        (continuous_abs.measurable.comp ((measurable_pi_apply i).comp (hsp t).1)).pow_const 3)
    have hbm : Measurable (beta t) := Measurable.ite (measurableSet_lt measurable_const hTm)
      (hcm.div (hTm.mul hTm.sqrt)) measurable_const
    have hDm : Measurable (D t) := Measurable.ite (measurableSet_lt measurable_const hTm)
      (measurable_const.add ((continuous_abs.measurable.comp hdm).div hTm.sqrt)) measurable_const
    exact Measurable.ite
      ((measurableSet_lt measurable_const hTm).inter (measurableSet_le measurable_const hTm))
      (((hbm.div_const (t : ℝ)).mul (hDm.pow_const p)).mul
        ((hTm.div_const (((n - t : ℕ) : ℝ) * sigmaSq)).add measurable_const)) measurable_const
  have hi (t : ℕ) (ht : t ∈ Finset.Icc 1 (n / 2)) : Integrable (late p t) P := by
    apply (hActual t ht).1.mono' (hm t).aestronglyMeasurable
    exact ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpoint t ht v).1]
      exact (hpoint t ht v).2
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∑ t ∈ Finset.Icc 1 (n / 2), ∫ v, A t v ∂P :=
      Finset.sum_le_sum fun t ht =>
        integral_mono (hi t ht) (hActual t ht).1 (fun v => (hpoint t ht v).2)
    _ = ∑ t ∈ Finset.Icc 1 (n / 2), ∫ v, W t v ∂Q t :=
      Finset.sum_congr rfl (fun t ht => (hActual t ht).2)
    _ ≤ _ := hprod.2

end Shao.Probability
