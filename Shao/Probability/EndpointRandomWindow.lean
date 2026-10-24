import Shao.Probability.SourceTruncationBridge
import Shao.Probability.BoundedQuadraticTilt
import Shao.Probability.BerryEsseen
import Shao.Probability.GaussianTail
import Shao.Probability.TruncationSampleSize
import Shao.Probability.SourceClockBridge
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.Variance

/-!
Random energy windows for the original self-normalized endpoint.
The original moderate-deviation results remain attributed to Shao--Zhou (2016).
The randomized concentration, finite-product covariance, and true quadratic-tilt
moment estimates below are proved here, with no external concentration axiom.
The actual uncentered energy, its zero paths, and closed boundary atoms are retained.
-/

set_option autoImplicit false
set_option Elab.async false
namespace Shao.Probability
open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem ep_clip_lipschitz (u v : ℝ) :
    |min (u ^ 2) (abs u) - min (v ^ 2) (abs v)| ≤ 2 * |u - v| := by
  have hscalar (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) :
      0 ≤ min (y ^ 2) y - min (x ^ 2) x ∧
        min (y ^ 2) y - min (x ^ 2) x ≤ 2 * (y - x) := by
    by_cases hy1 : y ≤ 1
    · have hx1 : x ≤ 1 := hxy.trans hy1
      have hxx : x ^ 2 ≤ x := by nlinarith
      have hyy : y ^ 2 ≤ y := by nlinarith
      rw [min_eq_left hyy, min_eq_left hxx]
      constructor
      · nlinarith
      · nlinarith [mul_nonneg (sub_nonneg.mpr hxy)
          (show 0 ≤ 2 - x - y by linarith)]
    · have hy1' : 1 ≤ y := le_of_lt (lt_of_not_ge hy1)
      have hyy : y ≤ y ^ 2 := by nlinarith
      rw [min_eq_right hyy]
      by_cases hx1 : x ≤ 1
      · have hxx : x ^ 2 ≤ x := by nlinarith
        rw [min_eq_left hxx]
        constructor <;> nlinarith [sq_nonneg (x - 1)]
      · have hx1' : 1 ≤ x := le_of_lt (lt_of_not_ge hx1)
        have hxx : x ≤ x ^ 2 := by nlinarith
        rw [min_eq_right hxx]
        constructor <;> linarith
  have ha := abs_abs_sub_abs_le_abs_sub u v
  rw [← sq_abs u, ← sq_abs v]
  rcases le_total |u| |v| with huv | hvu
  · obtain ⟨h0, h2⟩ := hscalar |u| |v| (abs_nonneg u) (abs_nonneg v) huv
    rw [abs_of_nonpos (by linarith : min (|u| ^ 2) |u| - min (|v| ^ 2) |v| ≤ 0)]
    rw [abs_of_nonpos (sub_nonpos.mpr huv)] at ha
    linarith
  · obtain ⟨h0, h2⟩ := hscalar |v| |u| (abs_nonneg v) (abs_nonneg u) hvu
    rw [abs_of_nonneg h0]
    rw [abs_of_nonneg (sub_nonneg.mpr hvu)] at ha
    linarith

private theorem ep_sqrt_clip (Q : ℝ) (hQ : 0 ≤ Q) :
    (Real.sqrt Q - 1) ^ 2 ≤ min ((Q - 1) ^ 2) |Q - 1| := by
  have hs : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg Q
  have hs2 : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ
  apply le_min
  · have hp := mul_nonneg (sq_nonneg (Real.sqrt Q - 1))
      (show 0 ≤ (Real.sqrt Q + 1) ^ 2 - 1 by nlinarith)
    nlinarith only [hp, hs2]
  · rcases le_total 1 Q with h1 | h1
    · rw [abs_of_nonneg (sub_nonneg.mpr h1)]
      have hr : 1 ≤ Real.sqrt Q := by nlinarith
      nlinarith
    · rw [abs_of_nonpos (sub_nonpos.mpr h1)]
      have hr : Real.sqrt Q ≤ 1 := by nlinarith
      nlinarith

private theorem ep_width_delete (t Q a : ℝ) (ht : 0 ≤ t) :
    |t / 2 * min ((Q - 1) ^ 2) (abs (Q - 1)) -
      t / 2 * min ((Q - a ^ 2 - 1) ^ 2) (abs (Q - a ^ 2 - 1))| ≤ t * a ^ 2 := by
  rw [← mul_sub, abs_mul, abs_of_nonneg (div_nonneg ht (by norm_num))]
  have h := mul_le_mul_of_nonneg_left (ep_clip_lipschitz (Q - 1) (Q - a ^ 2 - 1))
    (show 0 ≤ t / 2 by positivity)
  have he : Q - 1 - (Q - a ^ 2 - 1) = a ^ 2 := by ring
  rw [he, abs_of_nonneg (sq_nonneg a)] at h
  nlinarith only [h]

private theorem ep_integrable_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (f : Ω → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ᵐ a : Ω ∂ν, |f a| ≤ C) :
    Integrable f ν := by
  exact (integrable_const C).mono' hf.aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs] using hC)

private theorem ep_bounded_power (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hh : 0 ≤ h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) (k : ℕ) :
    Integrable (fun a : ℝ => a ^ k) ν ∧
      Integrable (fun a : ℝ => |a| ^ k) ν ∧
      (∫ a : ℝ, |a| ^ k ∂ν) ≤ h ^ k := by
  have hp : ∀ᵐ a : ℝ ∂ν, |a| ^ k ≤ h ^ k := by
    filter_upwards [hs] with a ha
    exact pow_le_pow_left₀ (abs_nonneg a) ha k
  have hi : Integrable (fun a : ℝ => |a| ^ k) ν :=
    ep_integrable_bound ν _ (by fun_prop) _ (by
      filter_upwards [hp] with a ha
      simpa only [abs_of_nonneg (pow_nonneg (abs_nonneg a) k)] using ha)
  refine ⟨?_, hi, ?_⟩
  · exact ep_integrable_bound ν _ (by fun_prop) _ (by simpa only [abs_pow] using hp)
  · simpa only [integral_const, probReal_univ, one_smul] using
      integral_mono_ae hi (integrable_const (h ^ k)) hp

private theorem ep_pi_support (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (h : ℝ) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    ∀ᵐ v : Shao.Path n ∂Measure.pi (fun _ : Fin n => ν), ∀ i : Fin n, |v i| ≤ h := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (fun _ : Fin n => ν) i).quasiMeasurePreserving.ae hs

private theorem ep_energy_bound (n : ℕ) (h : ℝ) (hh : 0 ≤ h)
    (v : Shao.Path n) (hv : ∀ i : Fin n, |v i| ≤ h) :
    0 ≤ Shao.energy v ∧ Shao.energy v ≤ (n : ℝ) * h ^ 2 := by
  constructor
  · exact Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  · calc
      Shao.energy v ≤ ∑ _i : Fin n, h ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (v i)) (hv i) 2
      _ = _ := by simp

private theorem ep_energy_exp_integrable
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (h s : ℝ) (hh : 0 ≤ h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    Integrable (fun v : Shao.Path n => Real.exp (s * (Shao.energy v - 1)))
      (Measure.pi (fun _ : Fin n => ν)) := by
  apply ep_integrable_bound _ _
    ((Shao.measurable_energy.sub_const 1).const_mul s).exp
    (Real.exp (|s| * ((n : ℝ) * h ^ 2 + 1)))
  filter_upwards [ep_pi_support ν n h hs] with v hv
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hQ := ep_energy_bound n h hh v hv
  have hq : |Shao.energy v - 1| ≤ (n : ℝ) * h ^ 2 + 1 := by
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hQ.1, abs_one]; linarith)
  calc
    s * (Shao.energy v - 1) ≤ |s * (Shao.energy v - 1)| := le_abs_self _
    _ = |s| * |Shao.energy v - 1| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hq (abs_nonneg s)

private theorem ep_abs_first_second_le_third
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν)
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) :
    (∫ a : ℝ, |a| ∂ν) * (∫ a : ℝ, a ^ 2 ∂ν) ≤
      (∫ a : ℝ, |a| ^ 3 ∂ν) := by
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
  let m1 : ℝ := ∫ a : ℝ, |a| ∂ν
  let r : ℝ := Real.sqrt m2
  have hm2 : 0 ≤ m2 := integral_nonneg fun a => sq_nonneg a
  have hm1 : 0 ≤ m1 := integral_nonneg fun a => abs_nonneg a
  have hr : 0 ≤ r := Real.sqrt_nonneg m2
  have hr2 : r ^ 2 = m2 := Real.sq_sqrt hm2
  have hpoint (a : ℝ) : (3 * r) * a ^ 2 ≤ 2 * |a| ^ 3 + r ^ 3 := by
    have hf := mul_nonneg (sq_nonneg (|a| - r))
      (show 0 ≤ 2 * |a| + r by positivity)
    rw [← sq_abs a]
    nlinarith only [hf]
  have hi := integral_mono (h2.const_mul (3 * r))
    ((h3.const_mul 2).add (integrable_const (r ^ 3))) hpoint
  change (∫ a : ℝ, (3 * r) * a ^ 2 ∂ν) ≤
    ∫ a : ℝ, 2 * |a| ^ 3 + r ^ 3 ∂ν at hi
  rw [integral_const_mul, integral_add (h3.const_mul 2) (integrable_const (r ^ 3)),
    integral_const_mul] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  have hr3 : r ^ 3 = r * m2 := by rw [pow_succ, hr2]; ring
  have hlyap : r * m2 ≤ ∫ a : ℝ, |a| ^ 3 ∂ν := by
    change 3 * r * m2 ≤ 2 * (∫ a : ℝ, |a| ^ 3 ∂ν) + r ^ 3 at hi
    linarith only [hi, hr3]
  have hLp : MemLp (fun a : ℝ => |a|) 2 ν := by
    apply (memLp_two_iff_integrable_sq continuous_abs.aestronglyMeasurable).2
    simpa only [sq_abs] using h2
  have hvar := variance_nonneg (fun a : ℝ => |a|) ν
  rw [variance_eq_sub hLp] at hvar
  simp only [Pi.pow_apply, sq_abs] at hvar
  have hm12 : m1 ^ 2 ≤ m2 := by dsimp [m1, m2]; linarith
  have hm1r : m1 ≤ r := by nlinarith
  exact (mul_le_mul_of_nonneg_right hm1r hm2).trans hlyap

private theorem ep_energy_exp_product
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) (s : ℝ) :
    (∫ v : Shao.Path n, Real.exp (s * (Shao.energy v - 1))
      ∂Measure.pi (fun _ : Fin n => ν)) =
      Real.exp (-s) * (∫ a : ℝ, Real.exp (s * a ^ 2) ∂ν) ^ n := by
  have he (v : Shao.Path n) : Real.exp (s * (Shao.energy v - 1)) =
      Real.exp (-s) * ∏ i : Fin n, Real.exp (s * (v i) ^ 2) := by
    rw [← Real.exp_sum, ← Real.exp_add]
    congr 1
    simp only [Shao.energy, ← Finset.mul_sum]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  have hp := integral_fintype_prod_eq_pow (ι := Fin n) (μ := ν)
    (fun a : ℝ => Real.exp (s * a ^ 2))
  simpa only [Fintype.card_fin] using congrArg (fun r : ℝ => Real.exp (-s) * r) hp

private theorem ep_bounded_energy_mgf
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (h s : ℝ) (hh : 0 ≤ h)
    (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) (hsmall : |s| * h ^ 2 ≤ 1) :
    (∫ v : Shao.Path n, Real.exp (s * (Shao.energy v - 1))
      ∂Measure.pi (fun _ : Fin n => ν)) ≤
      Real.exp (|s| * |(n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν) - 1| +
        (n : ℝ) * s ^ 2 * (∫ a : ℝ, a ^ 4 ∂ν)) := by
  let b : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
  let b4 : ℝ := ∫ a : ℝ, a ^ 4 ∂ν
  let X : ℝ → ℝ := fun a => s * (a ^ 2 - b)
  have hp := ep_bounded_power ν h hh hs
  have hb : 0 ≤ b := integral_nonneg fun a => sq_nonneg a
  have hbh : b ≤ h ^ 2 := by simpa only [sq_abs] using (hp 2).2.2
  have hX : Integrable X ν := ((hp 2).1.sub (integrable_const b)).const_mul s
  have hXmean : (∫ a : ℝ, X a ∂ν) = 0 := by
    dsimp [X]
    rw [integral_const_mul, integral_sub (hp 2).1 (integrable_const b)]
    simp [b]
  have hXb : ∀ᵐ a : ℝ ∂ν, |X a| ≤ 1 := by
    filter_upwards [hs] with a ha
    have ha2 : a ^ 2 ≤ h ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) ha 2
    have hd : |a ^ 2 - b| ≤ h ^ 2 := abs_le.mpr ⟨by nlinarith [sq_nonneg a], by nlinarith⟩
    dsimp [X]
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hd (abs_nonneg s)).trans hsmall
  have hX2 : Integrable (fun a : ℝ => X a ^ 2) ν :=
    ep_integrable_bound ν _ (by dsimp [X]; fun_prop) 1 (by
      filter_upwards [hXb] with a ha
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_abs (X a), abs_nonneg (X a)])
  have hX2val : (∫ a : ℝ, X a ^ 2 ∂ν) = s ^ 2 * (b4 - b ^ 2) := by
    have he (a : ℝ) : X a ^ 2 = s ^ 2 * (a ^ 4 - (2 * b) * a ^ 2 + b ^ 2) := by
      dsimp [X]
      ring
    simp_rw [he]
    rw [integral_const_mul,
      integral_add (f := fun a : ℝ => a ^ 4 - (2 * b) * a ^ 2)
        (g := fun _ : ℝ => b ^ 2)
        ((hp 4).1.sub ((hp 2).1.const_mul (2 * b))) (integrable_const (b ^ 2)),
      integral_sub (f := fun a : ℝ => a ^ 4) (g := fun a : ℝ => (2 * b) * a ^ 2)
        (hp 4).1 ((hp 2).1.const_mul (2 * b)), integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    dsimp [b4, b]
    ring
  have heX : Integrable (fun a : ℝ => Real.exp (X a)) ν :=
    ep_integrable_bound ν _ (by dsimp [X]; fun_prop) (Real.exp 1) (by
      filter_upwards [hXb] with a ha
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans ha))
  have heXle : (∫ a : ℝ, Real.exp (X a) ∂ν) ≤ Real.exp (s ^ 2 * b4) := by
    have hi := integral_mono_ae heX (((integrable_const (1 : ℝ)).add hX).add hX2) (by
      filter_upwards [hXb] with a ha
      have hh := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le ha)).2
      change Real.exp (X a) ≤ 1 + X a + X a ^ 2
      linarith only [hh])
    change (∫ a : ℝ, Real.exp (X a) ∂ν) ≤ ∫ a : ℝ, 1 + X a + X a ^ 2 ∂ν at hi
    rw [integral_add (f := fun a : ℝ => 1 + X a) (g := fun a : ℝ => X a ^ 2)
        ((integrable_const (1 : ℝ)).add hX) hX2,
      integral_add (f := fun _ : ℝ => 1) (g := X)
        (integrable_const (1 : ℝ)) hX, hXmean, hX2val] at hi
    simp only [integral_const, probReal_univ, one_smul, add_zero] at hi
    have hpoly : s ^ 2 * (b4 - b ^ 2) ≤ s ^ 2 * b4 := by
      nlinarith [mul_nonneg (sq_nonneg s) (sq_nonneg b)]
    exact hi.trans ((by linarith : 1 + s ^ 2 * (b4 - b ^ 2) ≤ 1 + s ^ 2 * b4).trans
      (by linarith [Real.add_one_le_exp (s ^ 2 * b4)]))
  have heone : (∫ a : ℝ, Real.exp (s * a ^ 2) ∂ν) ≤
      Real.exp (s * b + s ^ 2 * b4) := by
    have he (a : ℝ) : Real.exp (s * a ^ 2) = Real.exp (s * b) * Real.exp (X a) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [X]
      ring
    simp_rw [he]
    rw [integral_const_mul, Real.exp_add]
    exact mul_le_mul_of_nonneg_left heXle (Real.exp_pos _).le
  rw [ep_energy_exp_product]
  calc
    Real.exp (-s) * (∫ a : ℝ, Real.exp (s * a ^ 2) ∂ν) ^ n ≤
        Real.exp (-s) * Real.exp (s * b + s ^ 2 * b4) ^ n := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact pow_le_pow_left₀ (integral_nonneg fun a => (Real.exp_pos _).le) heone n
    _ = Real.exp (s * ((n : ℝ) * b - 1) + (n : ℝ) * s ^ 2 * b4) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hi := le_abs_self (s * ((n : ℝ) * b - 1))
      rw [abs_mul] at hi
      dsimp [b, b4] at hi ⊢
      linarith only [hi]

private theorem ep_abs_integral
    (ν : Measure ℝ) (F G : ℝ → ℝ)
    (hF : Integrable F ν) (hG : Integrable G ν)
    (hbound : ∀ᵐ a : ℝ ∂ν, |F a| ≤ G a) :
    |∫ a : ℝ, F a ∂ν| ≤ ∫ a : ℝ, G a ∂ν := by
  have hi := integral_mono_ae hF.norm hG (by
    filter_upwards [hbound] with a ha
    simpa only [Real.norm_eq_abs] using ha)
  have hn : |∫ a : ℝ, F a ∂ν| ≤ ∫ a : ℝ, ‖F a‖ ∂ν := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm F
  exact hn.trans hi

private theorem ep_tilt_moment_budget
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (h t c : ℝ) (hh : 0 < h) (ht : 0 < t)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hsupport : ∀ᵐ a : ℝ ∂η, |a| ≤ h) (hthin : t * h ≤ 1 / 800) :
    let ρ : Measure ℝ := η.tilted (fun a : ℝ => t * a - c * t ^ 2 * a ^ 2)
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂η
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂η
    IsProbabilityMeasure ρ ∧
      (∀ᵐ a : ℝ ∂ρ, |a| ≤ h) ∧
      Integrable (fun a : ℝ => a ^ 2) ρ ∧
      Integrable (fun a : ℝ => a ^ 4) ρ ∧
      (∫ a : ℝ, |a| ^ 3 ∂ρ) ≤ 2 * m3 ∧
      (∫ a : ℝ, a ^ 4 ∂ρ) ≤ 2 * h * m3 ∧
      |(∫ a : ℝ, a ^ 2 ∂ρ) - m2| ≤ 12 * t * m3 := by
  dsimp only
  let f : ℝ → ℝ := fun a => t * a - c * t ^ 2 * a ^ 2
  let ρ : Measure ℝ := η.tilted f
  let Z : ℝ := ∫ a : ℝ, Real.exp (f a) ∂η
  let w : ℝ → ℝ := fun a => Real.exp (f a) / Z
  let m1 : ℝ := ∫ a : ℝ, |a| ∂η
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂η
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂η
  let S : ℝ := t * h + c * t ^ 2 * h ^ 2
  have hk : 0 ≤ t * h := mul_nonneg ht.le hh.le
  have hk2 := pow_le_pow_left₀ hk hthin 2
  norm_num at hk2
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hS : S ≤ 1 / 400 := by
    have hc := mul_le_mul_of_nonneg_right hc1 (show 0 ≤ t ^ 2 * h ^ 2 by positivity)
    dsimp [S]
    nlinarith [hc]
  obtain ⟨hW, hZ, hZL, _, _, _, hprob, _, _, hsρ, hd, hL1, hident,
      hcompare, hp, _⟩ := boundedQuadraticTilt_density_moments η h t (c * t ^ 2)
        hh (by positivity) hsupport
  rw [abs_of_pos ht] at hZL hd hcompare
  change 0 < Z at hZ
  change IsProbabilityMeasure ρ at hprob
  change ∀ᵐ a : ℝ ∂ρ, |a| ≤ h at hsρ
  letI : IsProbabilityMeasure ρ := hprob
  have hZh : 1 / 2 ≤ Z := by
    have he := Real.add_one_le_exp (-S)
    change Real.exp (-S) ≤ Z at hZL
    linarith
  have he2 : Real.exp (2 * S) ≤ 2 := by
    have hu := Real.exp_bound_div_one_sub_of_interval
      (show 0 ≤ 2 * S by positivity) (show 2 * S < 1 by linarith)
    have hden : 0 < 1 - 2 * S := by linarith
    apply hu.trans
    apply (div_le_iff₀ hden).2
    linarith
  have h2η : Integrable (fun a : ℝ => a ^ 2) η := (hp 2).1
  have h3η : Integrable (fun a : ℝ => |a| ^ 3) η := (hp 3).2.2.1
  have h1η : Integrable (fun a : ℝ => |a|) η := by simpa using (hp 1).2.2.1
  have hm2 : 0 ≤ m2 := integral_nonneg fun a => sq_nonneg a
  have hm3 : 0 ≤ m3 := integral_nonneg fun a => pow_nonneg (abs_nonneg a) 3
  have h3ρ : (∫ a : ℝ, |a| ^ 3 ∂ρ) ≤ 2 * m3 := by
    have hu := (hcompare (fun a : ℝ => |a| ^ 3) h3η
      (Filter.Eventually.of_forall fun a => pow_nonneg (abs_nonneg a) 3)).2
    change (∫ a : ℝ, |a| ^ 3 ∂ρ) ≤ Real.exp (2 * S) * m3 at hu
    exact hu.trans (mul_le_mul_of_nonneg_right he2 hm3)
  have h4ρ : (∫ a : ℝ, a ^ 4 ∂ρ) ≤ 2 * h * m3 := by
    have hi := integral_mono_ae (hp 4).2.1 ((hp 3).2.2.2.1.const_mul h) (by
      filter_upwards [hsρ] with a ha
      change a ^ 4 ≤ h * |a| ^ 3
      have hu := mul_le_mul_of_nonneg_right ha (pow_nonneg (abs_nonneg a) 3)
      have ha4 : |a| ^ 4 = a ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
      simpa only [← pow_succ', ha4] using hu)
    rw [integral_const_mul] at hi
    exact hi.trans (by nlinarith [mul_le_mul_of_nonneg_left h3ρ hh.le])
  have hpoint : ∀ᵐ a : ℝ ∂η, |Real.exp (f a) - 1| ≤ 3 * t * |a| := by
    filter_upwards [hsupport] with a ha
    have hta : 0 ≤ t * |a| := by positivity
    have htah : t * |a| ≤ t * h := mul_le_mul_of_nonneg_left ha ht.le
    have hca := mul_le_mul_of_nonneg_right hc1 (show 0 ≤ t ^ 2 * a ^ 2 by positivity)
    have hfa : |f a| ≤ t * |a| + c * t ^ 2 * a ^ 2 := by
      have hu := abs_sub (t * a) (c * t ^ 2 * a ^ 2)
      simpa only [abs_mul, abs_of_nonneg ht.le,
        abs_of_nonneg (mul_nonneg (mul_nonneg hc0 (sq_nonneg t)) (sq_nonneg a))] using hu
    have hsqa : t ^ 2 * a ^ 2 = (t * |a|) ^ 2 := by rw [mul_pow, sq_abs]
    have hlin : |f a| ≤ (3 / 2) * (t * |a|) := by nlinarith
    have hfone : |f a| ≤ 1 := by linarith
    exact (Real.abs_exp_sub_one_le hfone).trans (by linarith)
  have hZdiff : |Z - 1| ≤ 3 * t * m1 := by
    have hi := ep_abs_integral η (fun a : ℝ => Real.exp (f a) - 1)
      (fun a : ℝ => (3 * t) * |a|) (hW.sub (integrable_const 1))
      (h1η.const_mul (3 * t)) hpoint
    rw [integral_sub hW (integrable_const 1), integral_const_mul] at hi
    simpa only [integral_const, probReal_univ, one_smul] using hi
  have hwdiff : ∀ᵐ a : ℝ ∂η, |w a - 1| ≤ 6 * t * (|a| + m1) := by
    filter_upwards [hpoint] with a ha
    have he : w a - 1 = (Real.exp (f a) - Z) / Z := by dsimp [w]; field_simp <;> ring
    rw [he, abs_div, abs_of_pos hZ]
    apply (div_le_iff₀ hZ).2
    have hu := abs_sub_le (Real.exp (f a)) 1 Z
    have h1 : |Real.exp (f a) - Z| ≤ 3 * t * (|a| + m1) := by
      rw [abs_sub_comm 1 Z] at hu
      nlinarith only [hu, ha, hZdiff]
    have hnon : 0 ≤ 3 * t * (|a| + m1) := by
      dsimp [m1]
      positivity
    nlinarith [mul_nonneg hnon (show 0 ≤ 2 * Z - 1 by linarith)]
  have hw2 : Integrable (fun a : ℝ => w a * a ^ 2) η := by
    exact h2η.bdd_mul (by dsimp [w, f]; fun_prop) (c := Real.exp (2 * S)) (by
      filter_upwards [hd] with a ha
      change |w a| ≤ Real.exp (2 * S)
      rw [abs_of_nonneg (div_nonneg (Real.exp_pos _).le hZ.le)]
      exact ha.2)
  have hd2 : Integrable (fun a : ℝ => (w a - 1) * a ^ 2) η := by
    exact (hw2.sub h2η).congr (Filter.Eventually.of_forall fun a => by
      simp only [Pi.sub_apply]
      ring)
  have hdrift : |(∫ a : ℝ, a ^ 2 ∂ρ) - m2| ≤ 12 * t * m3 := by
    have hi := ep_abs_integral η (fun a : ℝ => (w a - 1) * a ^ 2)
      (fun a : ℝ => (6 * t) * (|a| ^ 3 + m1 * a ^ 2)) hd2
      ((h3η.add (h2η.const_mul m1)).const_mul (6 * t)) (by
        filter_upwards [hwdiff] with a ha
        rw [abs_mul, abs_of_nonneg (sq_nonneg a)]
        have hu := mul_le_mul_of_nonneg_right ha (sq_nonneg a)
        convert hu using 1 <;> rw [← sq_abs a] <;> ring)
    have hid : (∫ a : ℝ, (w a - 1) * a ^ 2 ∂η) = (∫ a : ℝ, a ^ 2 ∂ρ) - m2 := by
      have he (a : ℝ) : (w a - 1) * a ^ 2 = w a * a ^ 2 - a ^ 2 := by ring
      simp_rw [he]
      rw [integral_sub hw2 h2η]
      have hident2 := hident (fun a : ℝ => a ^ 2) h2η
      change (∫ a : ℝ, a ^ 2 ∂ρ) = ∫ a : ℝ, w a * a ^ 2 ∂η at hident2
      rw [← hident2]
    rw [hid, integral_const_mul,
      integral_add (f := fun a : ℝ => |a| ^ 3) (g := fun a : ℝ => m1 * a ^ 2)
        h3η (h2η.const_mul m1), integral_const_mul] at hi
    have hlyap := ep_abs_first_second_le_third η h2η h3η
    change m1 * m2 ≤ m3 at hlyap
    change |(∫ a : ℝ, a ^ 2 ∂ρ) - m2| ≤ 6 * t * (m3 + m1 * m2) at hi
    nlinarith [mul_le_mul_of_nonneg_left hlyap ht.le]
  exact ⟨hprob, hsρ, (hp 2).2.1, (hp 4).2.1, h3ρ, h4ρ, hdrift⟩

theorem boundedEndpoint_quadraticTilt_energy_exponential_moment
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (n : ℕ) (hn : 1 ≤ n) (h t : ℝ) (hh : 0 < h) (ht : 0 < t)
    (hsupport : ∀ᵐ a : ℝ ∂eta, |a| ≤ h)
    (hthin : t * h ≤ 1 / 800)
    (hsmall :
      (1 + t) * ((n : ℝ) * |∫ a : ℝ, a ∂eta|) +
      (1 + t) ^ 2 * |(n : ℝ) * (∫ a : ℝ, a ^ 2 ∂eta) - 1| +
      (1 + t) ^ 3 * ((n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂eta)) ≤ 1 / 1000)
    (s : ℝ) (hs : |s| ≤ t ^ 2 / 2) :
    let etaT : Measure ℝ :=
      eta.tilted (fun a : ℝ => t * a - t ^ 2 * a ^ 2 / 2)
    let T : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => etaT)
    Integrable (fun v : Shao.Path n => Real.exp (s * (Shao.energy v - 1))) T ∧
      (∫ v : Shao.Path n, Real.exp (s * (Shao.energy v - 1)) ∂T) ≤ 2 := by
  dsimp only
  let etaT : Measure ℝ := eta.tilted (fun a : ℝ => t * a - t ^ 2 * a ^ 2 / 2)
  let q : ℝ := (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂eta)
  let beta : ℝ := (n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂eta)
  let d : ℝ := |q - 1|
  have hd : 0 ≤ d := abs_nonneg _
  have hb : 0 ≤ beta := mul_nonneg (Nat.cast_nonneg n)
    (integral_nonneg fun a => pow_nonneg (abs_nonneg a) 3)
  have hbud := ep_tilt_moment_budget eta h t (1 / 2) hh ht
    (by norm_num) (by norm_num) hsupport hthin
  have hf : (fun a : ℝ => t * a - (1 / 2) * t ^ 2 * a ^ 2) =
      (fun a : ℝ => t * a - t ^ 2 * a ^ 2 / 2) := by funext a; ring
  dsimp only at hbud
  rw [hf] at hbud
  obtain ⟨hprob, hsT, _, _, _, h4, hq⟩ := hbud
  change IsProbabilityMeasure etaT at hprob
  change ∀ᵐ a : ℝ ∂etaT, |a| ≤ h at hsT
  letI : IsProbabilityMeasure etaT := hprob
  have hk2 := pow_le_pow_left₀ (mul_nonneg ht.le hh.le) hthin 2
  norm_num at hk2
  have hssh : |s| * h ^ 2 ≤ 1 := by
    have hu := mul_le_mul_of_nonneg_right hs (sq_nonneg h)
    nlinarith only [hu, hk2]
  refine ⟨ep_energy_exp_integrable etaT n h s hh.le hsT, ?_⟩
  have hQ : |(n : ℝ) * (∫ a : ℝ, a ^ 2 ∂etaT) - 1| ≤ d + 12 * t * beta := by
    have hqN := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg n)
    have he : (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂etaT) - 1 =
        (n : ℝ) * ((∫ a : ℝ, a ^ 2 ∂etaT) - (∫ a : ℝ, a ^ 2 ∂eta)) + (q - 1) := by
      dsimp [q]
      ring
    rw [he]
    have hu := abs_add_le ((n : ℝ) *
      ((∫ a : ℝ, a ^ 2 ∂etaT) - (∫ a : ℝ, a ^ 2 ∂eta))) (q - 1)
    simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))] at hu
    dsimp [d, beta]
    dsimp [etaT] at hu ⊢
    nlinarith only [hu, hqN]
  have hB4 : (n : ℝ) * (∫ a : ℝ, a ^ 4 ∂etaT) ≤ 2 * h * beta := by
    have hu := mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg n)
    dsimp [beta, etaT]
    nlinarith only [hu]
  have hs2 : s ^ 2 ≤ t ^ 4 / 4 := by
    have hu := pow_le_pow_left₀ (abs_nonneg s) hs 2
    rw [sq_abs] at hu
    nlinarith only [hu]
  have hB4non : 0 ≤ (n : ℝ) * (∫ a : ℝ, a ^ 4 ∂etaT) := by
    apply mul_nonneg (Nat.cast_nonneg n)
    exact integral_nonneg fun a => by positivity
  have hfirst := mul_le_mul hs hQ (abs_nonneg _) (by positivity : 0 ≤ t ^ 2 / 2)
  have hsecond := mul_le_mul hs2 hB4 hB4non (by positivity : 0 ≤ t ^ 4 / 4)
  have hthb := mul_le_mul_of_nonneg_right hthin (show 0 ≤ t ^ 3 * beta by positivity)
  have hbudget : (1 + t) ^ 2 * d + (1 + t) ^ 3 * beta ≤ 1 / 1000 := by
    have hmu : 0 ≤ (1 + t) * ((n : ℝ) * |∫ a : ℝ, a ∂eta|) := by positivity
    change (1 + t) * ((n : ℝ) * |∫ a : ℝ, a ∂eta|) +
      (1 + t) ^ 2 * d + (1 + t) ^ 3 * beta ≤ 1 / 1000 at hsmall
    linarith only [hsmall, hmu]
  have hd2 := mul_le_mul_of_nonneg_right
    (show t ^ 2 ≤ (1 + t) ^ 2 by nlinarith only [ht]) hd
  have hb3 := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ ht.le (show t ≤ 1 + t by linarith) 3) hb
  have hE : |s| * |(n : ℝ) * (∫ a : ℝ, a ^ 2 ∂etaT) - 1| +
      (n : ℝ) * s ^ 2 * (∫ a : ℝ, a ^ 4 ∂etaT) ≤ 7 / 1000 := by
    have hpos : 0 ≤ (1 + t) ^ 2 * d := by positivity
    nlinarith only [hfirst, hsecond, hthb, hd2, hb3, hbudget, hpos]
  have hexp : Real.exp (7 / 1000 : ℝ) ≤ 2 := by
    exact (Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)).trans
      (by norm_num)
  exact (ep_bounded_energy_mgf etaT n h s hh.le hsT hssh).trans
    ((Real.exp_le_exp.mpr hE).trans hexp)

private theorem ep_clip_test_bounds (a δ r w : ℝ) (hδ : 0 ≤ δ) (hr : 0 ≤ r) :
    let F : ℝ → ℝ → ℝ := fun r w =>
      r / 2 + δ - min (max (a + δ - w) 0) (r + 2 * δ)
    |F r w| ≤ r / 2 + δ := by
  dsimp only
  have h0 : 0 ≤ min (max (a + δ - w) 0) (r + 2 * δ) :=
    le_min (le_max_right _ _) (by linarith)
  have hu := min_le_right (max (a + δ - w) 0) (r + 2 * δ)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem ep_clip_test_radius (a δ r r' w : ℝ) :
    let F : ℝ → ℝ → ℝ := fun r w =>
      r / 2 + δ - min (max (a + δ - w) 0) (r + 2 * δ)
    |F r w - F r' w| ≤ |r - r'| / 2 := by
  dsimp only
  let U : ℝ := max (a + δ - w) 0
  have hstep (x y : ℝ) (hxy : x ≤ y) :
      |(y / 2 + δ - min U (y + 2 * δ)) -
        (x / 2 + δ - min U (x + 2 * δ))| ≤ (y - x) / 2 := by
    have hm := min_le_min_left U (show x + 2 * δ ≤ y + 2 * δ by linarith)
    have hd : min U (y + 2 * δ) - min U (x + 2 * δ) ≤ y - x := by
      by_cases hu : U ≤ x + 2 * δ
      · rw [min_eq_left hu, min_eq_left (show U ≤ y + 2 * δ by linarith)]
        linarith
      · rw [min_eq_right (le_of_not_ge hu)]
        linarith [min_le_right U (y + 2 * δ)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rcases le_total r r' with hrr | hrr
  · rw [abs_of_nonpos (sub_nonpos.mpr hrr), abs_sub_comm]
    convert hstep r r' hrr using 1 <;> ring
  · rw [abs_of_nonneg (sub_nonneg.mpr hrr)]
    exact hstep r' r hrr

private theorem ep_clip_test_monotone (a δ r w v : ℝ) (hvw : v ≤ w) :
    let F : ℝ → ℝ → ℝ := fun r w =>
      r / 2 + δ - min (max (a + δ - w) 0) (r + 2 * δ)
    F r v ≤ F r w := by
  dsimp only
  have hu := min_le_min_right (r + 2 * δ)
    (max_le_max_right (0 : ℝ) (show a + δ - w ≤ a + δ - v by linarith))
  linarith only [hu]

private theorem ep_clip_test_nonneg (a δ r w x : ℝ) :
    let F : ℝ → ℝ → ℝ := fun r w =>
      r / 2 + δ - min (max (a + δ - w) 0) (r + 2 * δ)
    0 ≤ x * (F r w - F r (w - x)) := by
  dsimp only
  rcases le_total 0 x with hx | hx
  · exact mul_nonneg hx (sub_nonneg.mpr
      (ep_clip_test_monotone a δ r w (w - x) (by linarith)))
  · exact mul_nonneg_of_nonpos_of_nonpos hx (sub_nonpos.mpr
      (ep_clip_test_monotone a δ r (w - x) w (by linarith)))

private theorem ep_clip_test_linear (a δ r w x : ℝ)
    (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hlo : a - r ≤ w) (hhi : w ≤ a)
    (hx : |x| ≤ δ) :
    let F : ℝ → ℝ → ℝ := fun r w =>
      r / 2 + δ - min (max (a + δ - w) 0) (r + 2 * δ)
    x * (F r w - F r (w - x)) = x ^ 2 := by
  dsimp only
  have hx' := abs_le.mp hx
  have hline (v : ℝ) (hv0 : a - r - δ ≤ v) (hv1 : v ≤ a + δ) :
      r / 2 + δ - min (max (a + δ - v) 0) (r + 2 * δ) = v - a + r / 2 := by
    rw [max_eq_left (by linarith), min_eq_left (by linarith)]
    ring
  rw [hline w (by linarith) (by linarith), hline (w - x) (by linarith) (by linarith)]
  ring

private theorem ep_random_clip_interval
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (hX3 : ∀ i, Integrable (fun ω => |X i ω| ^ 3) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hsecond : (∑ i : Fin n, ∫ ω, X i ω ^ 2 ∂μ) = 1)
    (hind : iIndepFun X μ)
    (r : Ω → ℝ) (ri : Fin n → Ω → ℝ)
    (hrm : Measurable r) (hrim : ∀ i, Measurable (ri i))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᵐ ω ∂μ,
      0 ≤ r ω ∧ r ω ≤ C ∧ ∀ i, 0 ≤ ri i ω ∧ ri i ω ≤ C)
    (hdel : ∀ i, IndepFun (X i)
      (fun ω => ((∑ j : Fin n, X j ω) - X i ω, ri i ω)) μ)
    (a : ℝ) :
    let V : Ω → ℝ := fun ω => ∑ i : Fin n, X i ω
    let B : ℝ := ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂μ
    μ.real {ω | a - r ω ≤ V ω ∧ V ω ≤ a} ≤
      16 * B + 2 * (∫ ω, |V ω| * r ω ∂μ) +
        2 * (∑ i : Fin n, ∫ ω, |X i ω| * |r ω - ri i ω| ∂μ) := by
  classical
  dsimp only
  let V : Ω → ℝ := fun ω => ∑ i : Fin n, X i ω
  let B : ℝ := ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂μ
  let E : Set Ω := {ω | a - r ω ≤ V ω ∧ V ω ≤ a}
  let L : ℝ := ∑ i : Fin n, ∫ ω, |X i ω| * |r ω - ri i ω| ∂μ
  have hV2 : MemLp V 2 μ := memLp_finsetSum Finset.univ (fun i _ => hX2 i)
  have hVm : Measurable V := by dsimp [V]; fun_prop
  have hV1 := hV2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have habV : Integrable (fun ω => |V ω|) μ := by simpa only [Real.norm_eq_abs] using hV1.norm
  have hX1 (i : Fin n) := (hX2 i).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hBnon : 0 ≤ B := Finset.sum_nonneg fun i _ =>
    integral_nonneg fun ω => pow_nonneg (abs_nonneg (X i ω)) 3
  have hLnon : 0 ≤ L := Finset.sum_nonneg fun i _ => integral_nonneg fun ω => by positivity
  have hArnon : 0 ≤ ∫ ω, |V ω| * r ω ∂μ := integral_nonneg_of_ae
    (hbound.mono fun ω hω => mul_nonneg (abs_nonneg _) hω.1)
  by_cases hBbig : 1 ≤ B
  · exact (measureReal_le_one (μ := μ) (s := E)).trans (by
      change 1 ≤ 16 * B + 2 * (∫ ω, |V ω| * r ω ∂μ) + 2 * L
      linarith)
  have hBlt : B < 1 := lt_of_not_ge hBbig
  have hBpos : 0 < B := by
    by_contra hnot
    have hBzero : B = 0 := le_antisymm (le_of_not_gt hnot) hBnon
    have hzero (i : Fin n) : ∫ ω, |X i ω| ^ 3 ∂μ = 0 := by
      have hu := Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
        (f := fun j : Fin n => ∫ ω, |X j ω| ^ 3 ∂μ)
        (fun j _ => integral_nonneg fun ω => pow_nonneg (abs_nonneg (X j ω)) 3)
        (Finset.mem_univ i)
      change (∫ ω, |X i ω| ^ 3 ∂μ) ≤ B at hu
      exact le_antisymm (by simpa only [hBzero] using hu)
        (integral_nonneg fun ω => pow_nonneg (abs_nonneg _) 3)
    have hzero2 (i : Fin n) : ∫ ω, X i ω ^ 2 ∂μ = 0 := by
      have hz := (integral_eq_zero_iff_of_nonneg
        (fun ω => pow_nonneg (abs_nonneg (X i ω)) 3) (hX3 i)).1 (hzero i)
      calc
        _ = ∫ _ω : Ω, (0 : ℝ) ∂μ := integral_congr_ae (by
          filter_upwards [hz] with ω hω
          have hi : |X i ω| = 0 := (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hω
          rw [abs_eq_zero.mp hi]
          norm_num)
        _ = 0 := by simp
    simp only [hzero2, Finset.sum_const_zero] at hsecond
    norm_num at hsecond
  let δ : ℝ := 2 * B
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hVmean : (∫ ω, V ω ∂μ) = 0 := by
    dsimp [V]
    rw [integral_finsetSum _ (fun i _ => hX1 i)]
    simp only [hmean, Finset.sum_const_zero]
  have hVsq : (∫ ω, V ω ^ 2 ∂μ) = 1 := by
    have hv := IndepFun.variance_sum (s := (Finset.univ : Finset (Fin n)))
      (fun i _ => hX2 i) (fun i _ j _ hij => hind.indepFun hij)
    have he : (∑ i : Fin n, X i) = V := by ext ω; simp only [V, Finset.sum_apply]
    rw [he, variance_eq_sub hV2, hVmean] at hv
    simp only [Pi.pow_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] at hv
    have hvi (i : Fin n) : variance (X i) μ = ∫ ω, X i ω ^ 2 ∂μ := by
      rw [variance_eq_sub (hX2 i), hmean i]
      simp
    simpa only [hvi, hsecond] using hv
  have hVabs : (∫ ω, |V ω| ∂μ) ≤ 1 := by
    have hi := integral_mono habV ((hV2.integrable_sq.add (integrable_const 1)).div_const 2)
      (fun ω => by
        change |V ω| ≤ (V ω ^ 2 + 1) / 2
        nlinarith [sq_nonneg (|V ω| - 1), sq_abs (V ω)])
    change (∫ ω, |V ω| ∂μ) ≤ ∫ ω, (V ω ^ 2 + 1) / 2 ∂μ at hi
    rw [integral_div, integral_add hV2.integrable_sq (integrable_const 1), hVsq] at hi
    norm_num only [integral_const, probReal_univ, one_smul] at hi
    exact hi
  let Ui : Fin n → Ω → ℝ := fun i ω => if |X i ω| ≤ δ then X i ω ^ 2 else 0
  let U : Ω → ℝ := fun ω => ∑ i : Fin n, Ui i ω
  have hUim (i : Fin n) : Measurable (Ui i) := by
    exact Measurable.ite (measurableSet_le (continuous_abs.measurable.comp (hXm i)) measurable_const)
      ((hXm i).pow_const 2) measurable_const
  have hUib (i : Fin n) (ω : Ω) : 0 ≤ Ui i ω ∧ Ui i ω ≤ δ ^ 2 := by
    dsimp [Ui]
    split_ifs with hi
    · exact ⟨sq_nonneg _, by nlinarith [sq_abs (X i ω), abs_nonneg (X i ω)]⟩
    · constructor <;> positivity
  have hUi1 (i : Fin n) : Integrable (Ui i) μ :=
    ep_integrable_bound μ _ (hUim i) (δ ^ 2) (Filter.Eventually.of_forall fun ω => by
      rw [abs_of_nonneg (hUib i ω).1]
      exact (hUib i ω).2)
  have hUi2 (i : Fin n) : MemLp (Ui i) 2 μ := by
    apply (memLp_two_iff_integrable_sq (hUim i).aestronglyMeasurable).2
    apply ep_integrable_bound μ _ ((hUim i).pow_const 2) (δ ^ 4)
    exact Filter.Eventually.of_forall fun ω => by
      rw [abs_of_nonneg (sq_nonneg _)]
      have hh := pow_le_pow_left₀ (hUib i ω).1 (hUib i ω).2 2
      nlinarith only [hh]
  have hU2 : MemLp U 2 μ := memLp_finsetSum Finset.univ (fun i _ => hUi2 i)
  have hU1 := hU2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hUm : Measurable U := by dsimp [U]; fun_prop
  have hUint : (∫ ω, U ω ∂μ) = ∑ i : Fin n, ∫ ω, Ui i ω ∂μ :=
    integral_finsetSum _ (fun i _ => hUi1 i)
  have hUmean : 1 / 2 ≤ ∫ ω, U ω ∂μ := by
    have htail (i : Fin n) :
        δ * (∫ ω, X i ω ^ 2 ∂μ) - (∫ ω, |X i ω| ^ 3 ∂μ) ≤
          δ * (∫ ω, Ui i ω ∂μ) := by
      have hi := integral_mono (((hX2 i).integrable_sq.const_mul δ).sub (hX3 i))
        ((hUi1 i).const_mul δ) (fun ω => by
          change δ * X i ω ^ 2 - |X i ω| ^ 3 ≤ δ * Ui i ω
          dsimp [Ui]
          split_ifs with hsmall
          · nlinarith [pow_nonneg (abs_nonneg (X i ω)) 3]
          · have hu := mul_le_mul_of_nonneg_right (le_of_not_ge hsmall) (sq_nonneg (X i ω))
            rw [← sq_abs (X i ω)] at hu
            rw [← sq_abs (X i ω)]
            nlinarith only [hu])
      change (∫ ω, δ * X i ω ^ 2 - |X i ω| ^ 3 ∂μ) ≤ ∫ ω, δ * Ui i ω ∂μ at hi
      rw [integral_sub ((hX2 i).integrable_sq.const_mul δ) (hX3 i),
        integral_const_mul, integral_const_mul] at hi
      exact hi
    have hi := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => htail i)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsecond, ← hUint] at hi
    change δ * 1 - B ≤ δ * (∫ ω, U ω ∂μ) at hi
    dsimp [δ] at hi
    nlinarith only [hi, hBpos]
  have hvarU : variance U μ ≤ 2 * B ^ 2 := by
    have hindU : iIndepFun Ui μ := by
      change iIndepFun (fun i ω => if |X i ω| ≤ δ then X i ω ^ 2 else 0) μ
      exact hind.comp (fun _ : Fin n => fun x : ℝ => if |x| ≤ δ then x ^ 2 else 0)
        (fun _ => Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
          (measurable_id.pow_const 2) measurable_const)
    have hv := IndepFun.variance_sum (s := (Finset.univ : Finset (Fin n)))
      (fun i _ => hUi2 i) (fun i _ j _ hij => hindU.indepFun hij)
    have he : (∑ i : Fin n, Ui i) = U := by ext ω; simp only [U, Finset.sum_apply]
    rw [he] at hv
    have hvi (i : Fin n) : variance (Ui i) μ ≤ δ * (∫ ω, |X i ω| ^ 3 ∂μ) := by
      have hi := integral_mono (hUi2 i).integrable_sq ((hX3 i).const_mul δ) (fun ω => by
        change Ui i ω ^ 2 ≤ δ * |X i ω| ^ 3
        dsimp [Ui]
        split_ifs with hsmall
        · have hu := mul_le_mul_of_nonneg_right hsmall (pow_nonneg (abs_nonneg (X i ω)) 3)
          have hab4 : |X i ω| ^ 4 = X i ω ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
          nlinarith only [hu, hab4]
        · simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
          positivity)
      change (∫ ω, Ui i ω ^ 2 ∂μ) ≤ ∫ ω, δ * |X i ω| ^ 3 ∂μ at hi
      rw [integral_const_mul] at hi
      rw [variance_eq_sub (hUi2 i)]
      simp only [Pi.pow_apply]
      linarith [sq_nonneg (∫ ω, Ui i ω ∂μ)]
    rw [hv]
    have hi := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hvi i)
    rw [← Finset.mul_sum] at hi
    change _ ≤ δ * B at hi
    dsimp [δ] at hi
    nlinarith only [hi]
  let F : ℝ → ℝ → ℝ := fun r w => r / 2 + δ - min (max (a + δ - w) 0) (r + 2 * δ)
  let Fr : Ω → ℝ := fun ω => F (r ω) (V ω)
  let Fprev : Fin n → Ω → ℝ := fun i ω => F (r ω) (V ω - X i ω)
  let Fri : Fin n → Ω → ℝ := fun i ω => F (ri i ω) (V ω - X i ω)
  have hFrm : Measurable Fr := by dsimp [Fr, F]; fun_prop
  have hFprevm (i : Fin n) : Measurable (Fprev i) := by dsimp [Fprev, F]; fun_prop
  have hFrim (i : Fin n) : Measurable (Fri i) := by dsimp [Fri, F]; fun_prop
  have hFrb : ∀ᵐ ω ∂μ, |Fr ω| ≤ C / 2 + δ := by
    filter_upwards [hbound] with ω hω
    exact (ep_clip_test_bounds a δ (r ω) (V ω) hδ.le hω.1).trans (by linarith [hω.2.1])
  have hFprevb (i : Fin n) : ∀ᵐ ω ∂μ, |Fprev i ω| ≤ C / 2 + δ := by
    filter_upwards [hbound] with ω hω
    exact (ep_clip_test_bounds a δ (r ω) (V ω - X i ω) hδ.le hω.1).trans (by linarith [hω.2.1])
  have hFrib (i : Fin n) : ∀ᵐ ω ∂μ, |Fri i ω| ≤ C / 2 + δ := by
    filter_upwards [hbound] with ω hω
    exact (ep_clip_test_bounds a δ (ri i ω) (V ω - X i ω) hδ.le (hω.2.2 i).1).trans
      (by linarith [(hω.2.2 i).2])
  have hXF (i : Fin n) : Integrable (fun ω => X i ω * Fr ω) μ :=
    (hX1 i).mul_bdd hFrm.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hFrb)
  have hXFprev (i : Fin n) : Integrable (fun ω => X i ω * Fprev i ω) μ :=
    (hX1 i).mul_bdd (hFprevm i).aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hFprevb i)
  have hXFri (i : Fin n) : Integrable (fun ω => X i ω * Fri i ω) μ :=
    (hX1 i).mul_bdd (hFrim i).aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hFrib i)
  have hHpart (i : Fin n) : Integrable (fun ω => X i ω * (Fr ω - Fprev i ω)) μ := by
    exact ((hXF i).sub (hXFprev i)).congr
      (Filter.Eventually.of_forall fun ω => by simp only [Pi.sub_apply]; ring)
  let H : ℝ := ∑ i : Fin n, ∫ ω, X i ω * (Fr ω - Fprev i ω) ∂μ
  have hE : MeasurableSet E :=
    (measurableSet_le (measurable_const.sub hrm) hVm).inter (measurableSet_le hVm measurable_const)
  let I : Ω → ℝ := E.indicator (fun _ => 1)
  have hIm : Measurable I := measurable_const.indicator hE
  have hI1 : Integrable I μ := (integrable_const (1 : ℝ)).indicator hE
  have hIval : (∫ ω, I ω ∂μ) = μ.real E := integral_indicator_one hE
  have hIU : Integrable (fun ω => I ω * U ω) μ := hU1.bdd_mul hIm.aestronglyMeasurable
    (c := 1) (Filter.Eventually.of_forall fun ω => by
      dsimp [I]
      by_cases hω : ω ∈ E <;> simp [hω])
  have hHl : (∫ ω, I ω * U ω ∂μ) ≤ H := by
    have hi := integral_mono hIU (integrable_finsetSum Finset.univ (fun i _ => hHpart i)) (fun ω => by
      change I ω * U ω ≤ ∑ i : Fin n, X i ω * (Fr ω - Fprev i ω)
      by_cases hω : ω ∈ E
      · have hwall : a - r ω ≤ V ω ∧ V ω ≤ a := hω
        simp only [I, Set.indicator_of_mem hω, one_mul]
        apply Finset.sum_le_sum
        intro i _
        change Ui i ω ≤ X i ω * (F (r ω) (V ω) - F (r ω) (V ω - X i ω))
        dsimp [Ui]
        split_ifs with hsmall
        · rw [ep_clip_test_linear a δ (r ω) (V ω) (X i ω) hδ.le
            (by linarith [hwall.1, hwall.2]) hwall.1 hwall.2 hsmall]
        · exact ep_clip_test_nonneg a δ (r ω) (V ω) (X i ω)
      · simp only [I, Set.indicator_of_notMem hω, zero_mul]
        exact Finset.sum_nonneg fun i _ => ep_clip_test_nonneg a δ (r ω) (V ω) (X i ω))
    rw [integral_finsetSum _ (fun i _ => hHpart i)] at hi
    exact hi
  have hHlower : μ.real E / 4 - 2 * B ^ 2 ≤ H := by
    let mU : ℝ := ∫ ω, U ω ∂μ
    have hcen2 : Integrable (fun ω => (U ω - mU) ^ 2) μ :=
      (hU2.sub (memLp_const mU)).integrable_sq
    have hi := integral_mono
      ((hI1.mul_const (mU - 1 / 4)).sub hcen2) hIU (fun ω => by
        change I ω * (mU - 1 / 4) - (U ω - mU) ^ 2 ≤ I ω * U ω
        by_cases hω : ω ∈ E
        · simp only [I, Set.indicator_of_mem hω, one_mul]
          nlinarith [sq_nonneg (U ω - mU + 1 / 2)]
        · simp only [I, Set.indicator_of_notMem hω, zero_mul]
          nlinarith [sq_nonneg (U ω - mU)])
    change (∫ ω, I ω * (mU - 1 / 4) - (U ω - mU) ^ 2 ∂μ) ≤
      (∫ ω, I ω * U ω ∂μ) at hi
    rw [integral_sub (hI1.mul_const (mU - 1 / 4)) hcen2, integral_mul_const, hIval] at hi
    have hv : (∫ ω, (U ω - mU) ^ 2 ∂μ) = variance U μ :=
      (variance_eq_integral hUm.aemeasurable).symm
    rw [hv] at hi
    have hb0 : 0 ≤ μ.real E := measureReal_nonneg
    have hm := mul_le_mul_of_nonneg_left (show 1 / 4 ≤ mU - 1 / 4 by
      dsimp [mU]; linarith only [hUmean]) hb0
    nlinarith only [hi, hvarU, hm, hHl]
  have hLi (i : Fin n) : Integrable (fun ω => |X i ω| * |r ω - ri i ω|) μ := by
    have hXiabs : Integrable (fun ω => |X i ω|) μ := by
      simpa only [Real.norm_eq_abs] using (hX1 i).norm
    apply hXiabs.mul_bdd
      (continuous_abs.measurable.comp (hrm.sub (hrim i))).aestronglyMeasurable (c := 2 * C)
    filter_upwards [hbound] with ω hω
    change ‖|r ω - ri i ω|‖ ≤ 2 * C
    rw [Real.norm_eq_abs, abs_abs]
    have hu := abs_sub (r ω) (ri i ω)
    rw [abs_of_nonneg hω.1, abs_of_nonneg (hω.2.2 i).1] at hu
    linarith [hω.2.1, (hω.2.2 i).2]
  have hindzero (i : Fin n) : (∫ ω, X i ω * Fri i ω ∂μ) = 0 := by
    have hi := (hdel i).comp measurable_id
      (show Measurable (fun p : ℝ × ℝ => F p.2 p.1) by dsimp [F]; fun_prop)
    have he := hi.integral_fun_mul_eq_mul_integral (hXm i).aestronglyMeasurable
      (hFrim i).aestronglyMeasurable
    simpa only [Function.comp_def, id_eq, hmean, zero_mul] using he
  have hHup : H ≤ (∫ ω, V ω * Fr ω ∂μ) + L / 2 := by
    have hi (i : Fin n) : (∫ ω, X i ω * (Fr ω - Fprev i ω) ∂μ) ≤
        (∫ ω, X i ω * Fr ω ∂μ) +
          (∫ ω, |X i ω| * |r ω - ri i ω| ∂μ) / 2 := by
      have hi := integral_mono (hHpart i)
        (((hXF i).add ((hLi i).div_const 2)).sub (hXFri i)) (fun ω => by
          change X i ω * (Fr ω - Fprev i ω) ≤
            X i ω * Fr ω + |X i ω| * |r ω - ri i ω| / 2 - X i ω * Fri i ω
          have hu := ep_clip_test_radius a δ (r ω) (ri i ω) (V ω - X i ω)
          change |Fprev i ω - Fri i ω| ≤ |r ω - ri i ω| / 2 at hu
          have hm := mul_le_mul_of_nonneg_left hu (abs_nonneg (X i ω))
          have ha := neg_le_abs (X i ω * (Fprev i ω - Fri i ω))
          rw [abs_mul] at ha
          nlinarith only [hm, ha])
      change _ ≤ ∫ ω, X i ω * Fr ω + |X i ω| * |r ω - ri i ω| / 2 - X i ω * Fri i ω ∂μ at hi
      rw [integral_sub
          (f := fun ω => X i ω * Fr ω + |X i ω| * |r ω - ri i ω| / 2)
          (g := fun ω => X i ω * Fri i ω)
          ((hXF i).add ((hLi i).div_const 2)) (hXFri i),
        integral_add (f := fun ω => X i ω * Fr ω)
          (g := fun ω => |X i ω| * |r ω - ri i ω| / 2)
          (hXF i) ((hLi i).div_const 2), integral_div, hindzero i] at hi
      simpa only [sub_zero] using hi
    have hi := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hi i)
    rw [Finset.sum_add_distrib, ← Finset.sum_div] at hi
    have he : (∑ i : Fin n, ∫ ω, X i ω * Fr ω ∂μ) = ∫ ω, V ω * Fr ω ∂μ := by
      rw [← integral_finsetSum _ (fun i _ => hXF i)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by dsimp [V]; rw [Finset.sum_mul]
    rw [he] at hi
    exact hi
  have hVr : Integrable (fun ω => |V ω| * r ω) μ := habV.mul_bdd hrm.aestronglyMeasurable
    (c := C) (by
      filter_upwards [hbound] with ω hω
      simpa only [Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2.1)
  have hVF : Integrable (fun ω => V ω * Fr ω) μ := hV1.mul_bdd hFrm.aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs] using hFrb)
  have hVFup : (∫ ω, V ω * Fr ω ∂μ) ≤ (∫ ω, |V ω| * r ω ∂μ) / 2 + δ := by
    have hi := integral_mono_ae hVF ((hVr.div_const 2).add (habV.const_mul δ)) (by
      filter_upwards [hbound] with ω hω
      change V ω * Fr ω ≤ |V ω| * r ω / 2 + δ * |V ω|
      have hu := mul_le_mul_of_nonneg_left
        (ep_clip_test_bounds a δ (r ω) (V ω) hδ.le hω.1) (abs_nonneg (V ω))
      have ha := le_abs_self (V ω * Fr ω)
      rw [abs_mul] at ha
      nlinarith only [hu, ha])
    change _ ≤ ∫ ω, |V ω| * r ω / 2 + δ * |V ω| ∂μ at hi
    rw [integral_add (hVr.div_const 2) (habV.const_mul δ), integral_div, integral_const_mul] at hi
    have hm := mul_le_mul_of_nonneg_left hVabs hδ.le
    linarith only [hi, hm]
  change μ.real E ≤ 16 * B + 2 * (∫ ω, |V ω| * r ω ∂μ) + 2 * L
  have hBsq : B ^ 2 ≤ B := by nlinarith only [hBnon, hBlt]
  dsimp [δ] at hVFup
  linarith only [hHlower, hHup, hVFup, hBsq]

private theorem ep_product_covariance_anchor
    (η : Measure ℝ) [IsProbabilityMeasure η] (n : ℕ)
    (h : ℝ) (hh : 0 ≤ h) (hsupport : ∀ᵐ a : ℝ ∂η, |a| ≤ h)
    (F G : Shao.Path n → ℝ) (hFm : Measurable F) (hGm : Measurable G)
    (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (hFb : ∀ v : Shao.Path n, (∀ i : Fin n, |v i| ≤ h) → |F v| ≤ CF)
    (hGb : ∀ v : Shao.Path n, (∀ i : Fin n, |v i| ≤ h) → |G v| ≤ CG) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => η)
    let R : Measure (Fin n → ℝ × ℝ) := Measure.pi (fun _ : Fin n => η.prod η)
    let A : (Fin n → ℝ × ℝ) → Shao.Path n := fun z j => (z j).1
    let H : ℕ → (Fin n → ℝ × ℝ) → Shao.Path n :=
      fun k z j => if j.val < k then (z j).2 else (z j).1
    let A0 : Fin n → (Fin n → ℝ × ℝ) → Shao.Path n :=
      fun i z j => if j = i then 0 else (z j).1
    (∫ v : Shao.Path n, F v * G v ∂P) -
      (∫ v : Shao.Path n, F v ∂P) * (∫ v : Shao.Path n, G v ∂P) =
      ∑ i : Fin n, ∫ z : Fin n → ℝ × ℝ,
        (F (A z) - F (A0 i z)) *
          (G (H i.val z) - G (H (i.val + 1) z)) ∂R := by
  classical
  dsimp only
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => η)
  let R : Measure (Fin n → ℝ × ℝ) := Measure.pi (fun _ : Fin n => η.prod η)
  let A : (Fin n → ℝ × ℝ) → Shao.Path n := fun z j => (z j).1
  let B : (Fin n → ℝ × ℝ) → Shao.Path n := fun z j => (z j).2
  let H : ℕ → (Fin n → ℝ × ℝ) → Shao.Path n :=
    fun k z j => if j.val < k then (z j).2 else (z j).1
  let A0 : Fin n → (Fin n → ℝ × ℝ) → Shao.Path n :=
    fun i z j => if j = i then 0 else (z j).1
  have hAm : Measurable A := by dsimp [A]; fun_prop
  have hBm : Measurable B := by dsimp [B]; fun_prop
  have hHm (k : ℕ) : Measurable (H k) := by dsimp [H]; fun_prop
  have hA0m (i : Fin n) : Measurable (A0 i) := by dsimp [A0]; fun_prop
  have hsPair : ∀ᵐ p : ℝ × ℝ ∂η.prod η, |p.1| ≤ h ∧ |p.2| ≤ h := by
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hsupport,
      measurePreserving_snd.quasiMeasurePreserving.ae hsupport] with p hp hq
    exact ⟨hp, hq⟩
  have hsR : ∀ᵐ z : Fin n → ℝ × ℝ ∂R,
      ∀ i : Fin n, |(z i).1| ≤ h ∧ |(z i).2| ≤ h := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun _ : Fin n => η.prod η) i).quasiMeasurePreserving.ae hsPair
  have hAs (z : Fin n → ℝ × ℝ) (hz : ∀ i : Fin n, |(z i).1| ≤ h ∧ |(z i).2| ≤ h) :
      ∀ j : Fin n, |A z j| ≤ h := fun j => (hz j).1
  have hBs (z : Fin n → ℝ × ℝ) (hz : ∀ i : Fin n, |(z i).1| ≤ h ∧ |(z i).2| ≤ h) :
      ∀ j : Fin n, |B z j| ≤ h := fun j => (hz j).2
  have hHs (k : ℕ) (z : Fin n → ℝ × ℝ)
      (hz : ∀ i : Fin n, |(z i).1| ≤ h ∧ |(z i).2| ≤ h) :
      ∀ j : Fin n, |H k z j| ≤ h := by
    intro j
    dsimp [H]
    split_ifs
    · exact (hz j).2
    · exact (hz j).1
  have hA0s (i : Fin n) (z : Fin n → ℝ × ℝ)
      (hz : ∀ j : Fin n, |(z j).1| ≤ h ∧ |(z j).2| ≤ h) :
      ∀ j : Fin n, |A0 i z j| ≤ h := by
    intro j
    dsimp [A0]
    split_ifs
    · simpa only [abs_zero] using hh
    · exact (hz j).1
  have hIntAA : Integrable (fun z => F (A z) * G (A z)) R :=
    ep_integrable_bound R _ ((hFm.comp hAm).mul (hGm.comp hAm)) (CF * CG) (by
      filter_upwards [hsR] with z hz
      rw [abs_mul]
      exact mul_le_mul (hFb _ (hAs z hz)) (hGb _ (hAs z hz)) (abs_nonneg _) hCF)
  have hIntAB : Integrable (fun z => F (A z) * G (B z)) R :=
    ep_integrable_bound R _ ((hFm.comp hAm).mul (hGm.comp hBm)) (CF * CG) (by
      filter_upwards [hsR] with z hz
      rw [abs_mul]
      exact mul_le_mul (hFb _ (hAs z hz)) (hGb _ (hBs z hz)) (abs_nonneg _) hCF)
  have hIntAH (k : ℕ) : Integrable (fun z => F (A z) * G (H k z)) R :=
    ep_integrable_bound R _ ((hFm.comp hAm).mul (hGm.comp (hHm k))) (CF * CG) (by
      filter_upwards [hsR] with z hz
      rw [abs_mul]
      exact mul_le_mul (hFb _ (hAs z hz)) (hGb _ (hHs k z hz)) (abs_nonneg _) hCF)
  have hIntA0H (i : Fin n) (k : ℕ) : Integrable (fun z => F (A0 i z) * G (H k z)) R :=
    ep_integrable_bound R _ ((hFm.comp (hA0m i)).mul (hGm.comp (hHm k))) (CF * CG) (by
      filter_upwards [hsR] with z hz
      rw [abs_mul]
      exact mul_le_mul (hFb _ (hA0s i z hz)) (hGb _ (hHs k z hz)) (abs_nonneg _) hCF)
  have hzero (i : Fin n) : (∫ z, F (A0 i z) * (G (H i.val z) - G (H (i.val + 1) z)) ∂R) = 0 := by
    let sw : (Fin n → ℝ × ℝ) → (Fin n → ℝ × ℝ) :=
      fun z j => if j = i then (z j).swap else z j
    have hsw : MeasurePreserving sw R R := by
      change MeasurePreserving (fun z j => if j = i then (z j).swap else z j)
        (Measure.pi (fun _ : Fin n => η.prod η)) (Measure.pi (fun _ : Fin n => η.prod η))
      apply measurePreserving_pi (fun _ : Fin n => η.prod η) (fun _ : Fin n => η.prod η)
        (f := fun j p => if j = i then p.swap else p)
      intro j
      by_cases hji : j = i
      · simp only [hji, if_pos rfl]
        exact Measure.measurePreserving_swap
      · simp only [hji, if_false]
        exact MeasurePreserving.id _
    have hA0sw (z : Fin n → ℝ × ℝ) : A0 i (sw z) = A0 i z := by
      ext j
      by_cases hji : j = i <;> simp [A0, sw, hji]
    have hHsw (z : Fin n → ℝ × ℝ) : H i.val (sw z) = H (i.val + 1) z := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [H, sw]
      · have hne : j.val ≠ i.val := fun hval => hji (Fin.ext hval)
        by_cases hlt : j.val < i.val
        · simp [H, sw, hji, hlt, show j.val < i.val + 1 by omega]
        · simp [H, sw, hji, hlt, show ¬j.val < i.val + 1 by omega]
    have he := integral_map hsw.aemeasurable
      (((hFm.comp (hA0m i)).mul (hGm.comp (hHm i.val))).aestronglyMeasurable)
    rw [hsw.map_eq] at he
    have hid : (∫ z, F (A0 i z) * G (H i.val z) ∂R) =
        ∫ z, F (A0 i z) * G (H (i.val + 1) z) ∂R := by
      simpa only [Function.comp_apply, Pi.mul_apply, hA0sw, hHsw] using he
    have heq (z : Fin n → ℝ × ℝ) :
        F (A0 i z) * (G (H i.val z) - G (H (i.val + 1) z)) =
          F (A0 i z) * G (H i.val z) - F (A0 i z) * G (H (i.val + 1) z) := by ring
    simp_rw [heq]
    rw [integral_sub (hIntA0H i i.val) (hIntA0H i (i.val + 1)), hid, sub_self]
  have hIntH (i : Fin n) : Integrable
      (fun z => F (A z) * (G (H i.val z) - G (H (i.val + 1) z))) R := by
    exact ((hIntAH i.val).sub (hIntAH (i.val + 1))).congr
      (Filter.Eventually.of_forall fun z => by simp only [Pi.sub_apply]; ring)
  have hIntA0D (i : Fin n) : Integrable
      (fun z => F (A0 i z) * (G (H i.val z) - G (H (i.val + 1) z))) R := by
    exact ((hIntA0H i i.val).sub (hIntA0H i (i.val + 1))).congr
      (Filter.Eventually.of_forall fun z => by simp only [Pi.sub_apply]; ring)
  have hterm (i : Fin n) :
      (∫ z, (F (A z) - F (A0 i z)) * (G (H i.val z) - G (H (i.val + 1) z)) ∂R) =
        ∫ z, F (A z) * (G (H i.val z) - G (H (i.val + 1) z)) ∂R := by
    have he (z : Fin n → ℝ × ℝ) :
        (F (A z) - F (A0 i z)) * (G (H i.val z) - G (H (i.val + 1) z)) =
          F (A z) * (G (H i.val z) - G (H (i.val + 1) z)) -
            F (A0 i z) * (G (H i.val z) - G (H (i.val + 1) z)) := by ring
    simp_rw [he]
    rw [integral_sub (hIntH i) (hIntA0D i), hzero i, sub_zero]
  have htel (z : Fin n → ℝ × ℝ) :
      ∑ i : Fin n, (G (H i.val z) - G (H (i.val + 1) z)) = G (A z) - G (B z) := by
    have hsum (m : ℕ) : ∑ k ∈ Finset.range m, (G (H k z) - G (H (k + 1) z)) =
        G (H 0 z) - G (H m z) := by
      induction m with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, ih]; ring
    have h0 : H 0 z = A z := by ext j; simp [H, A]
    have hn : H n z = B z := by ext j; simp [H, B, j.is_lt]
    have hfin : (∑ i : Fin n, (G (H i.val z) - G (H (i.val + 1) z))) =
        ∑ k ∈ Finset.range n, (G (H k z) - G (H (k + 1) z)) :=
      Fin.sum_univ_eq_sum_range (fun k : ℕ => G (H k z) - G (H (k + 1) z)) n
    rw [hfin, hsum, h0, hn]
  have hAP : MeasurePreserving A R P :=
    measurePreserving_pi (fun _ : Fin n => η.prod η) (fun _ : Fin n => η)
      (fun _ => measurePreserving_fst)
  have hAA : (∫ z, F (A z) * G (A z) ∂R) = ∫ v : Shao.Path n, F v * G v ∂P := by
    have he := integral_map hAP.aemeasurable (hFm.mul hGm).aestronglyMeasurable
    rw [hAP.map_eq] at he
    exact he.symm
  have hAB : (∫ z, F (A z) * G (B z) ∂R) =
      (∫ v : Shao.Path n, F v ∂P) * (∫ v : Shao.Path n, G v ∂P) := by
    have hsplit := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
      (fun _ => η) (fun _ => η)
    have he := integral_map hsplit.aemeasurable
      ((hFm.comp measurable_fst).mul (hGm.comp measurable_snd)).aestronglyMeasurable
    rw [hsplit.map_eq] at he
    change (∫ p : Shao.Path n × Shao.Path n, F p.1 * G p.2 ∂P.prod P) =
      ∫ z : Fin n → ℝ × ℝ, F (A z) * G (B z) ∂R at he
    rw [integral_prod_mul] at he
    exact he.symm
  change (∫ v : Shao.Path n, F v * G v ∂P) -
    (∫ v : Shao.Path n, F v ∂P) * (∫ v : Shao.Path n, G v ∂P) =
      ∑ i : Fin n, ∫ z : Fin n → ℝ × ℝ, (F (A z) - F (A0 i z)) *
        (G (H i.val z) - G (H (i.val + 1) z)) ∂R
  rw [← hAA, ← hAB]
  symm
  simp_rw [hterm]
  rw [← integral_finsetSum _ (fun i _ => hIntH i)]
  have he (z : Fin n → ℝ × ℝ) :
      (∑ i : Fin n, F (A z) * (G (H i.val z) - G (H (i.val + 1) z))) =
        F (A z) * G (A z) - F (A z) * G (B z) := by
    rw [← Finset.mul_sum, htel]
    ring
  simp_rw [he]
  exact integral_sub hIntAA hIntAB

private theorem ep_square_shift
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (h2 : MemLp f 2 μ) (c : ℝ) :
    Integrable (fun ω => (f ω - c) ^ 2) μ ∧
      (∫ ω, (f ω - c) ^ 2 ∂μ) =
        variance f μ + ((∫ ω, f ω ∂μ) - c) ^ 2 := by
  have h1 := h2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hi : Integrable (fun ω => f ω ^ 2 - (2 * c) * f ω + c ^ 2) μ :=
    (h2.integrable_sq.sub (h1.const_mul (2 * c))).add (integrable_const _)
  have he : (fun ω => (f ω - c) ^ 2) = (fun ω => f ω ^ 2 - (2 * c) * f ω + c ^ 2) := by
    funext ω
    ring
  refine ⟨by rw [he]; exact hi, ?_⟩
  rw [he,
    integral_add (f := fun ω => f ω ^ 2 - (2 * c) * f ω) (g := fun _ => c ^ 2)
      (h2.integrable_sq.sub (h1.const_mul (2 * c))) (integrable_const (c ^ 2)),
    integral_sub (f := fun ω => f ω ^ 2) (g := fun ω => (2 * c) * f ω)
      h2.integrable_sq (h1.const_mul (2 * c)), integral_const_mul,
    integral_const, probReal_univ, one_smul, variance_eq_sub h2]
  simp only [Pi.pow_apply]
  ring

private theorem ep_energy_square_cost
    (η : Measure ℝ) [IsProbabilityMeasure η] (n : ℕ)
    (h4 : Integrable (fun a : ℝ => a ^ 4) η) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => η)
    Integrable (fun v : Shao.Path n => (Shao.energy v - 1) ^ 2) P ∧
      (∫ v : Shao.Path n, (Shao.energy v - 1) ^ 2 ∂P) ≤
        (n : ℝ) * (∫ a : ℝ, a ^ 4 ∂η) +
          ((n : ℝ) * (∫ a : ℝ, a ^ 2 ∂η) - 1) ^ 2 := by
  dsimp only
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => η)
  have hLp : MemLp (fun a : ℝ => a ^ 2) 2 η := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    simpa only [← pow_mul] using h4
  have hcoord (i : Fin n) : MemLp (fun v : Shao.Path n => (v i) ^ 2) 2 P :=
    hLp.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => η) i)
  have hQ2 : MemLp (Shao.energy : Shao.Path n → ℝ) 2 P :=
    memLp_finsetSum Finset.univ (fun i _ => hcoord i)
  have hQmean : (∫ v : Shao.Path n, Shao.energy v ∂P) =
      (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂η) := by
    change (∫ v : Shao.Path n, ∑ i : Fin n, (v i) ^ 2 ∂P) = _
    rw [integral_finsetSum _ (fun i _ => (hcoord i).integrable (by norm_num))]
    have hi (i : Fin n) : (∫ v : Shao.Path n, (v i) ^ 2 ∂P) = ∫ a : ℝ, a ^ 2 ∂η := by
      have he := integral_map (measurePreserving_eval (fun _ : Fin n => η) i).aemeasurable
        (show Measurable (fun a : ℝ => a ^ 2) by fun_prop).aestronglyMeasurable
      rw [(measurePreserving_eval (fun _ : Fin n => η) i).map_eq] at he
      exact he.symm
    simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hQvar : variance (Shao.energy : Shao.Path n → ℝ) P =
      (n : ℝ) * variance (fun a : ℝ => a ^ 2) η := by
    have hv := variance_sum_pi (μ := fun _ : Fin n => η) (X := fun _ => fun a : ℝ => a ^ 2)
      (fun _ => hLp)
    have he : (∑ i : Fin n, fun v : Shao.Path n => v i ^ 2) = Shao.energy := by
      ext v
      simp only [Shao.energy, Finset.sum_apply]
    rw [he] at hv
    simpa only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using hv
  obtain ⟨hi, he⟩ := ep_square_shift P Shao.energy hQ2 1
  refine ⟨hi, ?_⟩
  rw [he, hQmean, hQvar, variance_eq_sub hLp]
  simp only [Pi.pow_apply, ← pow_mul]
  have hu := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg (∫ a : ℝ, a ^ 2 ∂η))
  nlinarith only [hu]

private theorem ep_g_abs (h t a : ℝ) (hh : 0 ≤ h) (ht : 0 ≤ t)
    (hthin : t * h ≤ 1 / 800) (ha : |a| ≤ h) :
    |a - t * a ^ 2 / 2| ≤ 2 * |a| := by
  have hta := mul_le_mul_of_nonneg_left ha ht
  have hp := mul_le_mul_of_nonneg_right (hta.trans hthin) (abs_nonneg a)
  have hi := abs_sub a (t * a ^ 2 / 2)
  rw [abs_of_nonneg (by positivity : 0 ≤ t * a ^ 2 / 2)] at hi
  rw [← sq_abs a] at hi ⊢
  nlinarith only [hi, hp, abs_nonneg a]

private theorem ep_pair_mixed_cost
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (h : ℝ) (hh : 0 ≤ h) (hsupport : ∀ᵐ a : ℝ ∂η, |a| ≤ h) :
    Integrable (fun p : ℝ × ℝ => |p.1| * (p.1 ^ 2 + p.2 ^ 2)) (η.prod η) ∧
      (∫ p : ℝ × ℝ, |p.1| * (p.1 ^ 2 + p.2 ^ 2) ∂η.prod η) ≤
        2 * (∫ a : ℝ, |a| ^ 3 ∂η) := by
  have hp := ep_bounded_power η h hh hsupport
  have h1 : Integrable (fun a : ℝ => |a|) η := by simpa only [pow_one] using (hp 1).2.1
  have hsPair : ∀ᵐ p : ℝ × ℝ ∂η.prod η, |p.1| ≤ h ∧ |p.2| ≤ h := by
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hsupport,
      measurePreserving_snd.quasiMeasurePreserving.ae hsupport] with p hp hq
    exact ⟨hp, hq⟩
  have hiA : Integrable (fun p : ℝ × ℝ => |p.1| ^ 3) (η.prod η) :=
    measurePreserving_fst.integrable_comp_of_integrable (hp 3).2.1
  have hiB : Integrable (fun p : ℝ × ℝ => |p.1| * p.2 ^ 2) (η.prod η) := by
    exact h1.mul_prod (hp 2).1
  have he (p : ℝ × ℝ) : |p.1| * (p.1 ^ 2 + p.2 ^ 2) = |p.1| ^ 3 + |p.1| * p.2 ^ 2 := by
    rw [← sq_abs p.1]
    ring
  have hi : Integrable (fun p : ℝ × ℝ => |p.1| * (p.1 ^ 2 + p.2 ^ 2)) (η.prod η) := by
    simp_rw [he]
    exact hiA.add hiB
  refine ⟨hi, ?_⟩
  simp_rw [he]
  rw [integral_add hiA hiB]
  have hA : (∫ p : ℝ × ℝ, |p.1| ^ 3 ∂η.prod η) = ∫ a : ℝ, |a| ^ 3 ∂η := by
    have hm := integral_map (μ := η.prod η) (φ := Prod.fst) measurePreserving_fst.aemeasurable
      (show Measurable (fun a : ℝ => |a| ^ 3) by fun_prop).aestronglyMeasurable
    rw [measurePreserving_fst.map_eq] at hm
    exact hm.symm
  have hB : (∫ p : ℝ × ℝ, |p.1| * p.2 ^ 2 ∂η.prod η) =
      (∫ a : ℝ, |a| ∂η) * (∫ a : ℝ, a ^ 2 ∂η) :=
    integral_prod_mul (fun a : ℝ => |a|) (fun a : ℝ => a ^ 2)
  rw [hA, hB]
  linarith only [ep_abs_first_second_le_third η (hp 2).1 (hp 3).2.1]

private theorem ep_energy_clip_covariance
    (η : Measure ℝ) [IsProbabilityMeasure η] (n : ℕ)
    (h t : ℝ) (hh : 0 < h) (ht : 0 < t)
    (hsupport : ∀ᵐ a : ℝ ∂η, |a| ≤ h) (hthin : t * h ≤ 1 / 800) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => η)
    let g : ℝ → ℝ := fun a => a - t * a ^ 2 / 2
    let m : ℝ := ∫ a : ℝ, g a ∂η
    let Y : Shao.Path n → ℝ := fun v =>
      Shao.prefixSum (fun i : Fin n => g (v i)) n - (n : ℝ) * m
    let R : Shao.Path n → ℝ := fun v =>
      t / 2 * min ((Shao.energy v - 1) ^ 2) |Shao.energy v - 1|
    |(∫ v : Shao.Path n, |Y v| * R v ∂P) -
      (∫ v : Shao.Path n, |Y v| ∂P) * (∫ v : Shao.Path n, R v ∂P)| ≤
        4 * t * (n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂η) := by
  classical
  dsimp only
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => η)
  let g : ℝ → ℝ := fun a => a - t * a ^ 2 / 2
  let m : ℝ := ∫ a : ℝ, g a ∂η
  let Y : Shao.Path n → ℝ := fun v => Shao.prefixSum (fun i : Fin n => g (v i)) n - (n : ℝ) * m
  let F : Shao.Path n → ℝ := fun v => |Y v|
  let G : Shao.Path n → ℝ := fun v => t / 2 * min ((Shao.energy v - 1) ^ 2) |Shao.energy v - 1|
  let CF : ℝ := (n : ℝ) * (2 * h + |m|)
  let CG : ℝ := t / 2 * ((n : ℝ) * h ^ 2 + 1)
  have hFm : Measurable F := by dsimp [F, Y]; simp only [Shao.prefixSum_length]; fun_prop
  have hGm : Measurable G := by
    exact (((Shao.measurable_energy.sub_const 1).pow_const 2).min
      (continuous_abs.measurable.comp (Shao.measurable_energy.sub_const 1))).const_mul (t / 2)
  have hFb (v : Shao.Path n) (hv : ∀ i : Fin n, |v i| ≤ h) : |F v| ≤ CF := by
    have hsum : |Shao.prefixSum (fun i : Fin n => g (v i)) n| ≤ (n : ℝ) * (2 * h) := by
      rw [Shao.prefixSum_length]
      calc
        _ ≤ ∑ i : Fin n, |g (v i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, 2 * h := Finset.sum_le_sum fun i _ =>
          (ep_g_abs h t (v i) hh.le ht.le hthin (hv i)).trans (by linarith [hv i])
        _ = _ := by simp
    have hu := abs_sub (Shao.prefixSum (fun i : Fin n => g (v i)) n) ((n : ℝ) * m)
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))] at hu
    change abs (abs (Shao.prefixSum (fun i : Fin n => g (v i)) n - (n : ℝ) * m)) ≤ CF
    rw [abs_abs]
    dsimp [CF]
    nlinarith only [hsum, hu]
  have hGb (v : Shao.Path n) (hv : ∀ i : Fin n, |v i| ≤ h) : |G v| ≤ CG := by
    have hQ := ep_energy_bound n h hh.le v hv
    have ha : |Shao.energy v - 1| ≤ (n : ℝ) * h ^ 2 + 1 := by
      have hu := abs_sub (Shao.energy v) 1
      rw [abs_of_nonneg hQ.1, abs_one] at hu
      linarith only [hu, hQ.2]
    have hg0 : 0 ≤ G v := mul_nonneg (by positivity)
      (le_min (sq_nonneg _) (abs_nonneg _))
    rw [abs_of_nonneg hg0]
    exact mul_le_mul_of_nonneg_left
      ((min_le_right ((Shao.energy v - 1) ^ 2) |Shao.energy v - 1|).trans ha) (by positivity)
  have hcov := ep_product_covariance_anchor η n h hh.le hsupport F G hFm hGm CF CG
    (by dsimp [CF]; positivity) (by dsimp [CG]; positivity) hFb hGb
  let T : Measure (Fin n → ℝ × ℝ) := Measure.pi (fun _ : Fin n => η.prod η)
  let A : (Fin n → ℝ × ℝ) → Shao.Path n := fun z j => (z j).1
  let H : ℕ → (Fin n → ℝ × ℝ) → Shao.Path n :=
    fun k z j => if j.val < k then (z j).2 else (z j).1
  let A0 : Fin n → (Fin n → ℝ × ℝ) → Shao.Path n :=
    fun i z j => if j = i then 0 else (z j).1
  dsimp only at hcov
  change (∫ v : Shao.Path n, F v * G v ∂P) -
      (∫ v : Shao.Path n, F v ∂P) * (∫ v : Shao.Path n, G v ∂P) =
      ∑ i : Fin n, ∫ z : Fin n → ℝ × ℝ,
        (F (A z) - F (A0 i z)) * (G (H i.val z) - G (H (i.val + 1) z)) ∂T at hcov
  have hsPair : ∀ᵐ p : ℝ × ℝ ∂η.prod η, |p.1| ≤ h ∧ |p.2| ≤ h := by
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hsupport,
      measurePreserving_snd.quasiMeasurePreserving.ae hsupport] with p hp hq
    exact ⟨hp, hq⟩
  have hsT : ∀ᵐ z : Fin n → ℝ × ℝ ∂T,
      ∀ i : Fin n, |(z i).1| ≤ h ∧ |(z i).2| ≤ h := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun _ : Fin n => η.prod η) i).quasiMeasurePreserving.ae hsPair
  obtain ⟨hpairI, hpairB⟩ := ep_pair_mixed_cost η h hh.le hsupport
  have hterm (i : Fin n) :
      |∫ z : Fin n → ℝ × ℝ, (F (A z) - F (A0 i z)) *
        (G (H i.val z) - G (H (i.val + 1) z)) ∂T| ≤
          4 * t * (∫ a : ℝ, |a| ^ 3 ∂η) := by
    have hpoint : ∀ᵐ z : Fin n → ℝ × ℝ ∂T,
        |(F (A z) - F (A0 i z)) * (G (H i.val z) - G (H (i.val + 1) z))| ≤
          (2 * t) * (|(z i).1| * ((z i).1 ^ 2 + (z i).2 ^ 2)) := by
      filter_upwards [hsT] with z hz
      have hy : Y (A z) - Y (A0 i z) = g ((z i).1) := by
        have hdiff (j : Fin n) : g (A z j) - g (A0 i z j) = if j = i then g ((z i).1) else 0 := by
          by_cases hji : j = i <;> simp [A, A0, g, hji]
        calc
          _ = ∑ j : Fin n, (g (A z j) - g (A0 i z j)) := by
            dsimp [Y]
            simp only [Shao.prefixSum_length, Finset.sum_sub_distrib]
            ring
          _ = _ := by simp_rw [hdiff]; simp
      have hf : |F (A z) - F (A0 i z)| ≤ 2 * |(z i).1| := by
        exact ((abs_abs_sub_abs_le_abs_sub (Y (A z)) (Y (A0 i z))).trans_eq (by rw [hy])).trans
          (ep_g_abs h t ((z i).1) hh.le ht.le hthin (hz i).1)
      have he : Shao.energy (H i.val z) - Shao.energy (H (i.val + 1) z) =
          (z i).1 ^ 2 - (z i).2 ^ 2 := by
        have hdiff (j : Fin n) : H i.val z j ^ 2 - H (i.val + 1) z j ^ 2 =
            if j = i then (z i).1 ^ 2 - (z i).2 ^ 2 else 0 := by
          by_cases hji : j = i
          · subst j
            simp [H]
          · have hne : j.val ≠ i.val := fun he => hji (Fin.ext he)
            by_cases hj : j.val < i.val
            · simp [H, hji, hj, show j.val < i.val + 1 by omega]
            · simp [H, hji, hj, show ¬j.val < i.val + 1 by omega]
        dsimp [Shao.energy]
        rw [← Finset.sum_sub_distrib]
        simp_rw [hdiff]
        simp
      have hg : |G (H i.val z) - G (H (i.val + 1) z)| ≤
          t * ((z i).1 ^ 2 + (z i).2 ^ 2) := by
        calc
          _ = t / 2 * |min ((Shao.energy (H i.val z) - 1) ^ 2) (abs (Shao.energy (H i.val z) - 1)) -
              min ((Shao.energy (H (i.val + 1) z) - 1) ^ 2) (abs (Shao.energy (H (i.val + 1) z) - 1))| := by
            dsimp [G]
            rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ t / 2)]
          _ ≤ t / 2 * (2 * |(Shao.energy (H i.val z) - 1) - (Shao.energy (H (i.val + 1) z) - 1)|) :=
            mul_le_mul_of_nonneg_left (ep_clip_lipschitz _ _) (by positivity)
          _ = t * |(z i).1 ^ 2 - (z i).2 ^ 2| := by
            rw [show (Shao.energy (H i.val z) - 1) - (Shao.energy (H (i.val + 1) z) - 1) =
              (z i).1 ^ 2 - (z i).2 ^ 2 by linarith only [he]]
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            ((abs_sub ((z i).1 ^ 2) ((z i).2 ^ 2)).trans_eq (by
              rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)])) ht.le
      rw [abs_mul]
      exact (mul_le_mul hf hg (abs_nonneg _) (by positivity)).trans_eq (by ring)
    have hmajI : Integrable
        (fun z : Fin n → ℝ × ℝ => (2 * t) * (|(z i).1| * ((z i).1 ^ 2 + (z i).2 ^ 2))) T :=
      ((measurePreserving_eval (fun _ : Fin n => η.prod η) i).integrable_comp_of_integrable hpairI).const_mul (2 * t)
    have hfunm : Measurable (fun z : Fin n → ℝ × ℝ =>
        (F (A z) - F (A0 i z)) * (G (H i.val z) - G (H (i.val + 1) z))) := by
      apply Measurable.mul
      · apply Measurable.sub
        · exact hFm.comp (by dsimp [A]; fun_prop)
        · exact hFm.comp (by dsimp [A0]; fun_prop)
      · apply Measurable.sub
        · exact hGm.comp (by dsimp [H]; fun_prop)
        · exact hGm.comp (by dsimp [H]; fun_prop)
    have hfunI : Integrable (fun z : Fin n → ℝ × ℝ =>
        (F (A z) - F (A0 i z)) * (G (H i.val z) - G (H (i.val + 1) z))) T :=
      hmajI.mono' hfunm.aestronglyMeasurable (by
        filter_upwards [hpoint] with z hz
        simpa only [Real.norm_eq_abs] using hz)
    have hi := integral_mono_ae hfunI.norm hmajI (by
      filter_upwards [hpoint] with z hz
      simpa only [Real.norm_eq_abs] using hz)
    have hn := norm_integral_le_integral_norm (μ := T)
      (fun z : Fin n → ℝ × ℝ => (F (A z) - F (A0 i z)) * (G (H i.val z) - G (H (i.val + 1) z)))
    rw [integral_const_mul] at hi
    have hval : (∫ z : Fin n → ℝ × ℝ, |(z i).1| * ((z i).1 ^ 2 + (z i).2 ^ 2) ∂T) =
        ∫ p : ℝ × ℝ, |p.1| * (p.1 ^ 2 + p.2 ^ 2) ∂η.prod η := by
      have hm := integral_map (measurePreserving_eval (fun _ : Fin n => η.prod η) i).aemeasurable
        (show Measurable (fun p : ℝ × ℝ => |p.1| * (p.1 ^ 2 + p.2 ^ 2)) by fun_prop).aestronglyMeasurable
      rw [(measurePreserving_eval (fun _ : Fin n => η.prod η) i).map_eq] at hm
      exact hm.symm
    rw [hval] at hi
    simp only [Real.norm_eq_abs] at hi hn
    have hb := mul_le_mul_of_nonneg_left hpairB (show 0 ≤ 2 * t by positivity)
    nlinarith only [hi, hn, hb]
  change |(∫ v : Shao.Path n, F v * G v ∂P) -
    (∫ v : Shao.Path n, F v ∂P) * (∫ v : Shao.Path n, G v ∂P)| ≤ _
  rw [hcov]
  calc
    _ ≤ ∑ i : Fin n, |∫ z : Fin n → ℝ × ℝ,
        (F (A z) - F (A0 i z)) * (G (H i.val z) - G (H (i.val + 1) z)) ∂T| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, 4 * t * (∫ a : ℝ, |a| ^ 3 ∂η) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by simp; ring

private theorem ep_centered_third
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hh : 0 ≤ h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    Integrable (fun a : ℝ => |a - ∫ z : ℝ, z ∂ν| ^ 3) ν ∧
      (∫ a : ℝ, |a - ∫ z : ℝ, z ∂ν| ^ 3 ∂ν) ≤
        8 * (∫ a : ℝ, |a| ^ 3 ∂ν) := by
  let m : ℝ := ∫ a : ℝ, a ∂ν
  have hp := ep_bounded_power ν h hh hs
  have h1 : Integrable (fun a : ℝ => a) ν := by simpa only [pow_one] using (hp 1).1
  have hm1 : |m| ≤ ∫ a : ℝ, |a| ∂ν := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun a : ℝ => a)
  have hLp : MemLp (id : ℝ → ℝ) 2 ν :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 (hp 2).1
  have hm2 : m ^ 2 ≤ ∫ a : ℝ, a ^ 2 ∂ν := by
    have hv := variance_nonneg (id : ℝ → ℝ) ν
    rw [variance_eq_sub hLp] at hv
    simp only [Pi.pow_apply, id_eq] at hv
    dsimp [m]
    linarith
  have hm3 : |m| ^ 3 ≤ ∫ a : ℝ, |a| ^ 3 ∂ν := by
    have hp1 := mul_le_mul hm1 hm2 (sq_nonneg m)
      (integral_nonneg fun a : ℝ => abs_nonneg a)
    have hl := ep_abs_first_second_le_third ν (hp 2).1 (hp 3).2.1
    have he : |m| ^ 3 = |m| * m ^ 2 := by rw [pow_succ, sq_abs]; ring
    rw [he]
    exact hp1.trans hl
  have hc : Integrable (fun a : ℝ => |a - m| ^ 3) ν :=
    ep_integrable_bound ν _ (by fun_prop) ((h + |m|) ^ 3) (by
      filter_upwards [hs] with a ha
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub a m).trans (by linarith)) 3)
  have hpoint (a : ℝ) : |a - m| ^ 3 ≤ 4 * (|a| ^ 3 + |m| ^ 3) := by
    have htri := pow_le_pow_left₀ (abs_nonneg (a - m)) (abs_sub a m) 3
    have hf := mul_nonneg (sq_nonneg (|a| - |m|))
      (add_nonneg (abs_nonneg a) (abs_nonneg m))
    nlinarith only [htri, hf]
  have hi := integral_mono hc (((hp 3).2.1.add (integrable_const (|m| ^ 3))).const_mul 4) hpoint
  change (∫ a : ℝ, |a - m| ^ 3 ∂ν) ≤ ∫ a : ℝ, 4 * (|a| ^ 3 + |m| ^ 3) ∂ν at hi
  rw [integral_const_mul, integral_add (hp 3).2.1 (integrable_const (|m| ^ 3))] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  exact ⟨hc, by linarith only [hi, hm3]⟩

private theorem ep_g_centered_third
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (h t : ℝ) (hh : 0 < h) (ht : 0 < t)
    (hsupport : ∀ᵐ a : ℝ ∂η, |a| ≤ h) (hthin : t * h ≤ 1 / 800) :
    let g : ℝ → ℝ := fun a => a - t * a ^ 2 / 2
    let m : ℝ := ∫ a : ℝ, g a ∂η
    MemLp g 2 η ∧
      Integrable (fun a : ℝ => |g a - m| ^ 3) η ∧
      (∫ a : ℝ, |g a - m| ^ 3 ∂η) ≤
        64 * (∫ a : ℝ, |a| ^ 3 ∂η) := by
  dsimp only
  let g : ℝ → ℝ := fun a => a - t * a ^ 2 / 2
  let ζ : Measure ℝ := η.map g
  have hgm : Measurable g := by dsimp [g]; fun_prop
  have hprob : IsProbabilityMeasure ζ := by
    constructor
    change η.map g Set.univ = 1
    rw [Measure.map_apply hgm MeasurableSet.univ]
    simp
  letI : IsProbabilityMeasure ζ := hprob
  have hgb : ∀ᵐ a : ℝ ∂η, |g a| ≤ 2 * h := by
    filter_upwards [hsupport] with a ha
    exact (ep_g_abs h t a hh.le ht.le hthin ha).trans (by linarith)
  have hsζ : ∀ᵐ z : ℝ ∂ζ, |z| ≤ 2 * h := by
    exact (ae_map_iff hgm.aemeasurable
      (measurableSet_le continuous_abs.measurable measurable_const)).2 hgb
  have hLp : MemLp g 2 η := by
    apply (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2
    apply ep_integrable_bound η _ (hgm.pow_const 2) ((2 * h) ^ 2)
    filter_upwards [hgb] with a ha
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (g a), abs_nonneg (g a)]
  obtain ⟨hcζ, hbζ⟩ := ep_centered_third ζ (2 * h) (by positivity) hsζ
  have hmζ : (∫ z : ℝ, z ∂ζ) = ∫ a : ℝ, g a ∂η := by
    exact integral_map hgm.aemeasurable measurable_id.aestronglyMeasurable
  rw [hmζ] at hcζ hbζ
  have hc : Integrable (fun a : ℝ => |g a - ∫ z : ℝ, g z ∂η| ^ 3) η :=
    (integrable_map_measure (by fun_prop) hgm.aemeasurable).1 hcζ
  have hcube : (∫ z : ℝ, |z - ∫ a : ℝ, g a ∂η| ^ 3 ∂ζ) =
      ∫ a : ℝ, |g a - ∫ z : ℝ, g z ∂η| ^ 3 ∂η :=
    integral_map hgm.aemeasurable (by fun_prop)
  have hraw : (∫ z : ℝ, |z| ^ 3 ∂ζ) ≤ 8 * (∫ a : ℝ, |a| ^ 3 ∂η) := by
    rw [show (∫ z : ℝ, |z| ^ 3 ∂ζ) = ∫ a : ℝ, |g a| ^ 3 ∂η from
      integral_map hgm.aemeasurable (by fun_prop)]
    have hi3 : Integrable (fun a : ℝ => |g a| ^ 3) η :=
      ep_integrable_bound η _ (by dsimp [g]; fun_prop) ((2 * h) ^ 3) (by
        filter_upwards [hgb] with a ha
        rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
        exact pow_le_pow_left₀ (abs_nonneg _) ha 3)
    have hi := integral_mono_ae hi3 ((ep_bounded_power η h hh.le hsupport 3).2.1.const_mul 8) (by
      filter_upwards [hsupport] with a ha
      have hu := pow_le_pow_left₀ (abs_nonneg (g a)) (ep_g_abs h t a hh.le ht.le hthin ha) 3
      nlinarith only [hu])
    rw [integral_const_mul] at hi
    exact hi
  rw [hcube] at hbζ
  exact ⟨hLp, hc, by linarith only [hbζ, hraw]⟩

private theorem ep_pi_delete_independence
    (η : Measure ℝ) [IsProbabilityMeasure η] (n : ℕ) (i : Fin n)
    (φ : ℝ → ℝ) (hφ : Measurable φ)
    (ψ : Shao.Path n → ℝ × ℝ) (hψ : Measurable ψ)
    (hinv : ∀ (v : Shao.Path n) (a : ℝ), ψ (Function.update v i a) = ψ v) :
    IndepFun (fun v : Shao.Path n => φ (v i)) ψ (Measure.pi (fun _ : Fin n => η)) := by
  classical
  let S : Finset (Fin n) := Finset.univ.erase i
  let fill : (S → ℝ) → Shao.Path n := fun y j => if hj : j ∈ S then y ⟨j, hj⟩ else 0
  have hfillm : Measurable fill := by
    apply Measurable.of_eval
    intro j
    by_cases hj : j ∈ S
    · simpa only [fill, dif_pos hj] using (measurable_pi_apply (⟨j, hj⟩ : S))
    · simpa only [fill, dif_neg hj] using (measurable_const : Measurable (fun _ : S → ℝ => (0 : ℝ)))
  have hfill (v : Shao.Path n) : fill (fun j : S => v j) = Function.update v i 0 := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [fill, S]
    · simp [fill, S, hji]
  have hid : iIndepFun (fun j : Fin n => fun v : Shao.Path n => v j)
      (Measure.pi (fun _ : Fin n => η)) := iIndepFun_pi (fun _ => aemeasurable_id)
  have hraw := hid.indepFun_finset ({i} : Finset (Fin n)) S (by simp [S])
    (fun j => measurable_pi_apply j)
  have hc := hraw.comp
    (hφ.comp (measurable_pi_apply (⟨i, by simp⟩ : ({i} : Finset (Fin n)))))
    (hψ.comp hfillm)
  convert hc using 1
  · funext v
    rfl
  · funext v
    simpa only [Function.comp_apply, hfill] using (hinv v 0).symm

private theorem ep_unit_sum_abs
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (X : Fin n → Ω → ℝ) (hX2 : ∀ i, MemLp (X i) 2 μ)
    (hind : iIndepFun X μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hsecond : (∑ i : Fin n, ∫ ω, X i ω ^ 2 ∂μ) = 1) :
    (∫ ω, |∑ i : Fin n, X i ω| ∂μ) ≤ 1 := by
  let V : Ω → ℝ := fun ω => ∑ i : Fin n, X i ω
  have hV2 : MemLp V 2 μ := memLp_finsetSum Finset.univ (fun i _ => hX2 i)
  have hV1 := hV2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have habV : Integrable (fun ω => |V ω|) μ := by simpa only [Real.norm_eq_abs] using hV1.norm
  have hm : (∫ ω, V ω ∂μ) = 0 := by
    dsimp [V]
    rw [integral_finsetSum _ (fun i _ => (hX2 i).integrable (by norm_num))]
    simp only [hmean, Finset.sum_const_zero]
  have hVsq : (∫ ω, V ω ^ 2 ∂μ) = 1 := by
    have hv := IndepFun.variance_sum (s := (Finset.univ : Finset (Fin n)))
      (fun i _ => hX2 i) (fun i _ j _ hij => hind.indepFun hij)
    have he : (∑ i : Fin n, X i) = V := by ext ω; simp only [V, Finset.sum_apply]
    rw [he, variance_eq_sub hV2, hm] at hv
    simp only [Pi.pow_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] at hv
    have hvi (i : Fin n) : variance (X i) μ = ∫ ω, X i ω ^ 2 ∂μ := by
      rw [variance_eq_sub (hX2 i), hmean i]
      simp
    simpa only [hvi, hsecond] using hv
  have hi := integral_mono habV ((hV2.integrable_sq.add (integrable_const 1)).div_const 2)
    (fun ω => by
      change |V ω| ≤ (V ω ^ 2 + 1) / 2
      nlinarith [sq_nonneg (|V ω| - 1), sq_abs (V ω)])
  change (∫ ω, |V ω| ∂μ) ≤ ∫ ω, (V ω ^ 2 + 1) / 2 ∂μ at hi
  rw [integral_div, integral_add hV2.integrable_sq (integrable_const 1), hVsq] at hi
  norm_num only [integral_const, probReal_univ, one_smul] at hi
  exact hi

private theorem ep_g_mixed_centered
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (h t : ℝ) (hh : 0 < h) (ht : 0 < t)
    (hsupport : ∀ᵐ a : ℝ ∂η, |a| ≤ h) (hthin : t * h ≤ 1 / 800) :
    let g : ℝ → ℝ := fun a => a - t * a ^ 2 / 2
    let m : ℝ := ∫ a : ℝ, g a ∂η
    Integrable (fun a : ℝ => |g a - m| * a ^ 2) η ∧
      (∫ a : ℝ, |g a - m| * a ^ 2 ∂η) ≤
        4 * (∫ a : ℝ, |a| ^ 3 ∂η) := by
  dsimp only
  let g : ℝ → ℝ := fun a => a - t * a ^ 2 / 2
  let m : ℝ := ∫ a : ℝ, g a ∂η
  have hp := ep_bounded_power η h hh.le hsupport
  have hgi := (ep_g_centered_third η h t hh ht hsupport hthin).1.integrable (by norm_num)
  have hgb : ∀ᵐ a : ℝ ∂η, |g a| ≤ 2 * |a| :=
    hsupport.mono fun a ha => ep_g_abs h t a hh.le ht.le hthin ha
  have hga : Integrable (fun a : ℝ => |g a|) η := by
    simpa only [Real.norm_eq_abs] using hgi.norm
  have h1 : Integrable (fun a : ℝ => |a|) η := by simpa only [pow_one] using (hp 1).2.1
  have hm : |m| ≤ 2 * (∫ a : ℝ, |a| ∂η) := by
    have hi := integral_mono_ae hga (h1.const_mul 2) hgb
    rw [integral_const_mul] at hi
    have hn : |m| ≤ ∫ a : ℝ, |g a| ∂η := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (g : ℝ → ℝ)
    linarith only [hi, hn]
  have hmajor : Integrable (fun a : ℝ => 2 * |a| ^ 3 + |m| * a ^ 2) η :=
    ((hp 3).2.1.const_mul 2).add ((hp 2).1.const_mul |m|)
  have hpoint : ∀ᵐ a : ℝ ∂η, |g a - m| * a ^ 2 ≤ 2 * |a| ^ 3 + |m| * a ^ 2 := by
    filter_upwards [hgb] with a ha
    have hu := mul_le_mul_of_nonneg_right ((abs_sub (g a) m).trans
      (show |g a| + |m| ≤ 2 * |a| + |m| by linarith only [ha]))
      (sq_nonneg a)
    rw [← sq_abs a] at hu ⊢
    nlinarith only [hu]
  have hi : Integrable (fun a : ℝ => |g a - m| * a ^ 2) η :=
    hmajor.mono' (by dsimp [g]; fun_prop) (by
      filter_upwards [hpoint] with a ha
      simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg a))] using ha)
  have hbound := integral_mono_ae hi hmajor hpoint
  rw [integral_add ((hp 3).2.1.const_mul 2) ((hp 2).1.const_mul |m|),
    integral_const_mul, integral_const_mul] at hbound
  have hm2 := mul_le_mul_of_nonneg_right hm (integral_nonneg (μ := η) fun a : ℝ => sq_nonneg a)
  have hly := ep_abs_first_second_le_third η (hp 2).1 (hp 3).2.1
  exact ⟨hi, by nlinarith only [hbound, hm2, hly]⟩

theorem boundedEndpoint_energy_clip_random_interval
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (n : ℕ) (hn : 1 ≤ n) (h t : ℝ) (hh : 0 < h) (ht : 0 < t)
    (hsupport : ∀ᵐ u : ℝ ∂eta, |u| ≤ h)
    (hthin : t * h ≤ 1 / 800)
    (hvariance : 0 < variance (fun u : ℝ => u - t * u ^ 2 / 2) eta)
    (a : ℝ) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => eta)
    let g : ℝ → ℝ := fun u => u - t * u ^ 2 / 2
    let m : ℝ := ∫ u : ℝ, g u ∂eta
    let sigma : ℝ := Real.sqrt ((n : ℝ) * variance g eta)
    let q : ℝ := (n : ℝ) * (∫ u : ℝ, u ^ 2 ∂eta)
    let beta : ℝ := (n : ℝ) * (∫ u : ℝ, |u| ^ 3 ∂eta)
    let b4 : ℝ := (n : ℝ) * (∫ u : ℝ, u ^ 4 ∂eta)
    let Y : Shao.Path n → ℝ := fun v =>
      Shao.prefixSum (fun i : Fin n => g (v i)) n - (n : ℝ) * m
    let R : Shao.Path n → ℝ := fun v =>
      t / 2 * min ((Shao.energy v - 1) ^ 2) |Shao.energy v - 1|
    P.real {v : Shao.Path n | a - R v ≤ Y v ∧ Y v ≤ a} ≤
      1024 * beta / sigma ^ 3 +
        t / sigma * (b4 + (q - 1) ^ 2) + 16 * t * beta / sigma ^ 2 := by
  classical
  dsimp only
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => eta)
  let g : ℝ → ℝ := fun u => u - t * u ^ 2 / 2
  let m : ℝ := ∫ u : ℝ, g u ∂eta
  let sigma : ℝ := Real.sqrt ((n : ℝ) * variance g eta)
  let q : ℝ := (n : ℝ) * (∫ u : ℝ, u ^ 2 ∂eta)
  let beta : ℝ := (n : ℝ) * (∫ u : ℝ, |u| ^ 3 ∂eta)
  let b4 : ℝ := (n : ℝ) * (∫ u : ℝ, u ^ 4 ∂eta)
  let Y : Shao.Path n → ℝ := fun v =>
    Shao.prefixSum (fun i : Fin n => g (v i)) n - (n : ℝ) * m
  let R : Shao.Path n → ℝ := fun v =>
    t / 2 * min ((Shao.energy v - 1) ^ 2) |Shao.energy v - 1|
  let ξ : ℝ → ℝ := fun u => (g u - m) / sigma
  let X : Fin n → Shao.Path n → ℝ := fun i v => ξ (v i)
  let V : Shao.Path n → ℝ := fun v => Y v / sigma
  let r : Shao.Path n → ℝ := fun v => R v / sigma
  let ri : Fin n → Shao.Path n → ℝ := fun i v =>
    (t / 2 * min ((Shao.energy v - (v i) ^ 2 - 1) ^ 2)
      |Shao.energy v - (v i) ^ 2 - 1|) / sigma
  let C : ℝ := (t / 2 * ((n : ℝ) * h ^ 2 + 1)) / sigma
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsigma : 0 < sigma := Real.sqrt_pos.2 (mul_pos hnp hvariance)
  have hsigma2 : sigma ^ 2 = (n : ℝ) * variance g eta :=
    Real.sq_sqrt (mul_nonneg hnp.le hvariance.le)
  have hgm : Measurable g := by dsimp [g]; fun_prop
  have hξm : Measurable ξ := by dsimp [ξ]; fun_prop
  obtain ⟨hg2, hgc3, hgcB⟩ := ep_g_centered_third eta h t hh ht hsupport hthin
  change MemLp g 2 eta at hg2
  have hg1 := hg2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hξ2 : MemLp ξ 2 eta := by
    convert (hg2.sub (memLp_const m)).const_mul sigma⁻¹ using 1
    ext u
    simp only [ξ, Pi.sub_apply, div_eq_mul_inv, mul_comm]
  have hξ3 : Integrable (fun u : ℝ => |ξ u| ^ 3) eta := by
    have he (u : ℝ) : |ξ u| ^ 3 = |g u - m| ^ 3 / sigma ^ 3 := by
      dsimp [ξ]
      rw [abs_div, abs_of_pos hsigma, div_pow]
    simp_rw [he]
    exact hgc3.div_const (sigma ^ 3)
  have hξmean : (∫ u : ℝ, ξ u ∂eta) = 0 := by
    dsimp [ξ]
    rw [integral_div, integral_sub hg1 (integrable_const m)]
    simp [m]
  have hξsq : (∫ u : ℝ, ξ u ^ 2 ∂eta) = variance g eta / sigma ^ 2 := by
    have he (u : ℝ) : ξ u ^ 2 = (g u - m) ^ 2 / sigma ^ 2 := by dsimp [ξ]; rw [div_pow]
    simp_rw [he]
    rw [integral_div]
    have hv : (∫ u : ℝ, (g u - m) ^ 2 ∂eta) = variance g eta :=
      (variance_eq_integral hgm.aemeasurable).symm
    rw [hv]
  have hξcube : (∫ u : ℝ, |ξ u| ^ 3 ∂eta) ≤
      64 * (∫ u : ℝ, |u| ^ 3 ∂eta) / sigma ^ 3 := by
    have he (u : ℝ) : |ξ u| ^ 3 = |g u - m| ^ 3 / sigma ^ 3 := by
      dsimp [ξ]
      rw [abs_div, abs_of_pos hsigma, div_pow]
    simp_rw [he]
    rw [integral_div]
    exact div_le_div_of_nonneg_right hgcB (by positivity)
  have hpull (f : ℝ → ℝ) (hf : Measurable f) (i : Fin n) :
      (∫ v : Shao.Path n, f (v i) ∂P) = ∫ u : ℝ, f u ∂eta := by
    have he := integral_map (measurePreserving_eval (fun _ : Fin n => eta) i).aemeasurable
      hf.aestronglyMeasurable
    rw [(measurePreserving_eval (fun _ : Fin n => eta) i).map_eq] at he
    exact he.symm
  have hXm (i : Fin n) : Measurable (X i) := hξm.comp (measurable_pi_apply i)
  have hX2 (i : Fin n) : MemLp (X i) 2 P :=
    hξ2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => eta) i)
  have hX3 (i : Fin n) : Integrable (fun v => |X i v| ^ 3) P :=
    (measurePreserving_eval (fun _ : Fin n => eta) i).integrable_comp_of_integrable hξ3
  have hXmean (i : Fin n) : (∫ v : Shao.Path n, X i v ∂P) = 0 := by
    exact (hpull ξ hξm i).trans hξmean
  have hXsecond : (∑ i : Fin n, ∫ v : Shao.Path n, X i v ^ 2 ∂P) = 1 := by
    have hi (i : Fin n) : (∫ v : Shao.Path n, X i v ^ 2 ∂P) = variance g eta / sigma ^ 2 :=
      (hpull (fun u : ℝ => ξ u ^ 2) (hξm.pow_const 2) i).trans hξsq
    simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_div_assoc, ← hsigma2, div_self (by positivity : sigma ^ 2 ≠ 0)]
  have hind : iIndepFun X P := iIndepFun_pi (fun _ => hξm.aemeasurable)
  have hVsum (v : Shao.Path n) : (∑ i : Fin n, X i v) = V v := by
    dsimp [X, ξ, V, Y]
    rw [Shao.prefixSum_length, ← Finset.sum_div, Finset.sum_sub_distrib]
    simp
  have hVm : Measurable V := by dsimp [V, Y]; simp only [Shao.prefixSum_length]; fun_prop
  have hrm : Measurable r := by
    exact ((((Shao.measurable_energy.sub_const 1).pow_const 2).min
      (continuous_abs.measurable.comp (Shao.measurable_energy.sub_const 1))).const_mul (t / 2)).div_const sigma
  have hrim (i : Fin n) : Measurable (ri i) := by
    have hQ := Shao.measurable_energy.sub ((measurable_pi_apply i).pow_const 2)
    exact ((((hQ.sub_const 1).pow_const 2).min
      (continuous_abs.measurable.comp (hQ.sub_const 1))).const_mul (t / 2)).div_const sigma
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hwidth (Q : ℝ) (hQ0 : 0 ≤ Q) (hQh : Q ≤ (n : ℝ) * h ^ 2) :
      0 ≤ (t / 2 * min ((Q - 1) ^ 2) |Q - 1|) / sigma ∧
        (t / 2 * min ((Q - 1) ^ 2) |Q - 1|) / sigma ≤ C := by
    refine ⟨div_nonneg (mul_nonneg (by positivity) (le_min (sq_nonneg _) (abs_nonneg _))) hsigma.le, ?_⟩
    apply div_le_div_of_nonneg_right _ hsigma.le
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ t / 2)
    have hu := abs_sub Q 1
    rw [abs_of_nonneg hQ0, abs_one] at hu
    exact (min_le_right _ _).trans (by linarith only [hu, hQh])
  have hbound : ∀ᵐ v : Shao.Path n ∂P,
      0 ≤ r v ∧ r v ≤ C ∧ ∀ i : Fin n, 0 ≤ ri i v ∧ ri i v ≤ C := by
    filter_upwards [ep_pi_support eta n h hsupport] with v hv
    have hQ := ep_energy_bound n h hh.le v hv
    obtain ⟨hr0, hrC⟩ := hwidth (Shao.energy v) hQ.1 hQ.2
    refine ⟨hr0, hrC, fun i => ?_⟩
    have hi : (v i) ^ 2 ≤ Shao.energy v :=
      Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
    exact hwidth (Shao.energy v - (v i) ^ 2) (by linarith) (by nlinarith [sq_nonneg (v i)])
  have hdel (i : Fin n) : IndepFun (X i)
      (fun v : Shao.Path n => ((∑ j : Fin n, X j v) - X i v, ri i v)) P := by
    apply ep_pi_delete_independence eta n i ξ hξm _
      ((show Measurable (fun v : Shao.Path n => (∑ j : Fin n, X j v) - X i v) by fun_prop).prodMk (hrim i))
    intro v u
    have hsum (f : ℝ → ℝ) :
        (∑ j : Fin n, f (Function.update v i u j)) - f u =
          (∑ j : Fin n, f (v j)) - f (v i) := by
      have hj (j : Fin n) : f (Function.update v i u j) - f (v j) =
          if j = i then f u - f (v i) else 0 := by
        by_cases hji : j = i <;> simp [hji]
      have he : (∑ j : Fin n, f (Function.update v i u j)) - (∑ j : Fin n, f (v j)) =
          f u - f (v i) := by
        rw [← Finset.sum_sub_distrib]
        simp_rw [hj]
        simp
      linarith only [he]
    apply Prod.ext
    · simpa [X] using hsum ξ
    · have he := hsum (fun u : ℝ => u ^ 2)
      change Shao.energy (Function.update v i u) - u ^ 2 = Shao.energy v - (v i) ^ 2 at he
      dsimp [ri]
      have hvi : Function.update v i u i = u := by simp
      rw [hvi]
      rw [he]
  have hbase := ep_random_clip_interval P n X hXm hX2 hX3 hXmean hXsecond hind
    r ri hrm hrim C hC hbound hdel (a / sigma)
  dsimp only at hbase
  simp_rw [hVsum] at hbase
  have hEvent : {v : Shao.Path n | a / sigma - r v ≤ V v ∧ V v ≤ a / sigma} =
      {v : Shao.Path n | a - R v ≤ Y v ∧ Y v ≤ a} := by
    ext v
    dsimp [V, r]
    rw [← sub_div, div_le_div_iff_of_pos_right hsigma, div_le_div_iff_of_pos_right hsigma]
  rw [hEvent] at hbase
  have hB : (∑ i : Fin n, ∫ v : Shao.Path n, |X i v| ^ 3 ∂P) ≤ 64 * beta / sigma ^ 3 := by
    have hi (i : Fin n) : (∫ v : Shao.Path n, |X i v| ^ 3 ∂P) ≤
        64 * (∫ u : ℝ, |u| ^ 3 ∂eta) / sigma ^ 3 := by
      rw [hpull (fun u : ℝ => |ξ u| ^ 3) (by fun_prop) i]
      exact hξcube
    have hi := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hi i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hi
    exact hi.trans_eq (by dsimp [beta]; ring)
  obtain ⟨hmixI, hmixB⟩ := ep_g_mixed_centered eta h t hh ht hsupport hthin
  change Integrable (fun u : ℝ => |g u - m| * u ^ 2) eta at hmixI
  change (∫ u : ℝ, |g u - m| * u ^ 2 ∂eta) ≤ 4 * (∫ u : ℝ, |u| ^ 3 ∂eta) at hmixB
  have hL : (∑ i : Fin n, ∫ v : Shao.Path n, |X i v| * |r v - ri i v| ∂P) ≤
      4 * t * beta / sigma ^ 2 := by
    have hi (i : Fin n) : (∫ v : Shao.Path n, |X i v| * |r v - ri i v| ∂P) ≤
        4 * t * (∫ u : ℝ, |u| ^ 3 ∂eta) / sigma ^ 2 := by
      have hpt (v : Shao.Path n) : |X i v| * |r v - ri i v| ≤
          (t / sigma ^ 2) * (|g (v i) - m| * (v i) ^ 2) := by
        have hw := div_le_div_of_nonneg_right (ep_width_delete t (Shao.energy v) (v i) ht.le) hsigma.le
        have he : |r v - ri i v| ≤ t * (v i) ^ 2 / sigma := by
          simpa only [r, R, ri, ← sub_div, abs_div, abs_of_pos hsigma] using hw
        have hu := mul_le_mul_of_nonneg_left he (abs_nonneg (X i v))
        have hxe : |X i v| = |g (v i) - m| / sigma := by
          dsimp [X, ξ]
          rw [abs_div, abs_of_pos hsigma]
        rw [hxe] at hu
        rw [hxe]
        convert hu using 1 <;> field_simp <;> ring
      have hmajor : Integrable
          (fun v : Shao.Path n => (t / sigma ^ 2) * (|g (v i) - m| * (v i) ^ 2)) P := by
        simpa only [Function.comp_apply] using
          ((measurePreserving_eval (fun _ : Fin n => eta) i).integrable_comp_of_integrable hmixI).const_mul (t / sigma ^ 2)
      have hleft : Integrable (fun v : Shao.Path n => |X i v| * |r v - ri i v|) P :=
        hmajor.mono' (by fun_prop) (Filter.Eventually.of_forall fun v => by
          simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ |X i v| * |r v - ri i v|)] using hpt v)
      have hu := integral_mono hleft hmajor hpt
      change (∫ v : Shao.Path n, |X i v| * |r v - ri i v| ∂P) ≤
        ∫ v : Shao.Path n, (t / sigma ^ 2) * (|g (v i) - m| * (v i) ^ 2) ∂P at hu
      rw [integral_const_mul, hpull (fun u : ℝ => |g u - m| * u ^ 2) (by dsimp [g]; fun_prop) i] at hu
      have hb := mul_le_mul_of_nonneg_left hmixB (show 0 ≤ t / sigma ^ 2 by positivity)
      exact (hu.trans hb).trans_eq (by ring)
    have hi := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hi i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hi
    exact hi.trans_eq (by dsimp [beta]; ring)
  have hrI : Integrable r P := ep_integrable_bound P r hrm C (by
    filter_upwards [hbound] with v hv
    simpa only [abs_of_nonneg hv.1] using hv.2.1)
  have hErnon : 0 ≤ ∫ v : Shao.Path n, r v ∂P := integral_nonneg_of_ae (hbound.mono fun _ hv => hv.1)
  have hEr : (∫ v : Shao.Path n, r v ∂P) ≤ t / (2 * sigma) * (b4 + (q - 1) ^ 2) := by
    obtain ⟨hi, hb⟩ := ep_energy_square_cost eta n (ep_bounded_power eta h hh.le hsupport 4).1
    have hu := integral_mono hrI (hi.const_mul (t / (2 * sigma))) (fun v => by
      change (t / 2 * min ((Shao.energy v - 1) ^ 2) |Shao.energy v - 1|) / sigma ≤
        (t / (2 * sigma)) * (Shao.energy v - 1) ^ 2
      have hh := mul_le_mul_of_nonneg_left (min_le_left ((Shao.energy v - 1) ^ 2) |Shao.energy v - 1|)
        (show 0 ≤ t / (2 * sigma) by positivity)
      convert hh using 1 <;> field_simp <;> ring)
    rw [integral_const_mul] at hu
    have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ t / (2 * sigma) by positivity)
    exact hu.trans hh
  have hVabs := ep_unit_sum_abs P n X hX2 hind hXmean hXsecond
  simp_rw [hVsum] at hVabs
  have hCov := ep_energy_clip_covariance eta n h t hh ht hsupport hthin
  dsimp only at hCov
  change |(∫ v : Shao.Path n, |Y v| * R v ∂P) -
    (∫ v : Shao.Path n, |Y v| ∂P) * (∫ v : Shao.Path n, R v ∂P)| ≤
      4 * t * (n : ℝ) * (∫ u : ℝ, |u| ^ 3 ∂eta) at hCov
  have hAeq : (∫ v : Shao.Path n, |V v| * r v ∂P) =
      (∫ v : Shao.Path n, |Y v| * R v ∂P) / sigma ^ 2 := by
    have he (v : Shao.Path n) : |V v| * r v = |Y v| * R v / sigma ^ 2 := by
      dsimp [V, r]
      rw [abs_div, abs_of_pos hsigma]
      field_simp <;> ring
    simp_rw [he]
    exact integral_div _ _
  have hVeq : (∫ v : Shao.Path n, |V v| ∂P) = (∫ v : Shao.Path n, |Y v| ∂P) / sigma := by
    simp only [V, abs_div, abs_of_pos hsigma]
    exact integral_div _ _
  have hreq : (∫ v : Shao.Path n, r v ∂P) = (∫ v : Shao.Path n, R v ∂P) / sigma := integral_div _ _
  have hcovN : |(∫ v : Shao.Path n, |V v| * r v ∂P) -
      (∫ v : Shao.Path n, |V v| ∂P) * (∫ v : Shao.Path n, r v ∂P)| ≤
        4 * t * beta / sigma ^ 2 := by
    rw [hAeq, hVeq, hreq]
    have he (u v w : ℝ) : |u / sigma ^ 2 - (v / sigma) * (w / sigma)| =
        |u - v * w| / sigma ^ 2 := by
      calc
        _ = |(u - v * w) / sigma ^ 2| := by congr 1; field_simp <;> ring
        _ = _ := by rw [abs_div, abs_of_pos (sq_pos_of_pos hsigma)]
    rw [he]
    convert div_le_div_of_nonneg_right hCov (show 0 ≤ sigma ^ 2 by positivity) using 1 <;>
      dsimp [beta] <;> ring
  have hA : (∫ v : Shao.Path n, |V v| * r v ∂P) ≤
      (∫ v : Shao.Path n, r v ∂P) + 4 * t * beta / sigma ^ 2 := by
    have hu := (le_abs_self ((∫ v : Shao.Path n, |V v| * r v ∂P) -
      (∫ v : Shao.Path n, |V v| ∂P) * (∫ v : Shao.Path n, r v ∂P))).trans hcovN
    have hp := mul_le_mul_of_nonneg_right hVabs hErnon
    linarith only [hu, hp]
  change P.real {v : Shao.Path n | a - R v ≤ Y v ∧ Y v ≤ a} ≤
    1024 * beta / sigma ^ 3 + t / sigma * (b4 + (q - 1) ^ 2) + 16 * t * beta / sigma ^ 2
  calc
    _ ≤ 16 * (64 * beta / sigma ^ 3) +
        2 * (t / (2 * sigma) * (b4 + (q - 1) ^ 2) + 4 * t * beta / sigma ^ 2) +
        2 * (4 * t * beta / sigma ^ 2) := by linarith only [hbase, hB, hL, hA, hEr]
    _ = _ := by ring

private theorem ep_pi_tilted
    (η : Measure ℝ) [IsProbabilityMeasure η] (n : ℕ)
    (f : ℝ → ℝ) (hfm : Measurable f)
    (hfi : Integrable (fun a : ℝ => Real.exp (f a)) η) :
    Measure.pi (fun _ : Fin n => η.tilted f) =
      (Measure.pi (fun _ : Fin n => η)).tilted
        (fun v : Shao.Path n => ∑ i : Fin n, f (v i)) := by
  classical
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => η)
  let Z : ℝ := ∫ a : ℝ, Real.exp (f a) ∂η
  let w : ℝ → ℝ := fun a => Real.exp (f a) / Z
  let F : Shao.Path n → ℝ := fun v => ∑ i : Fin n, f (v i)
  have hZ : 0 < Z := integral_exp_pos hfi
  letI : IsProbabilityMeasure (η.tilted f) := isProbabilityMeasure_tilted hfi
  have hN : (∫ v : Shao.Path n, Real.exp (F v) ∂P) = Z ^ n := by
    dsimp [F, P]
    simp_rw [Real.exp_sum]
    simpa only [Fintype.card_fin] using
      (integral_fintype_prod_eq_pow (ι := Fin n) (μ := η) (fun a : ℝ => Real.exp (f a)))
  have hd (v : Shao.Path n) : Real.exp (F v) / Z ^ n = ∏ i : Fin n, w (v i) := by
    dsimp [F, w]
    rw [Real.exp_sum, Finset.prod_div_distrib]
    simp
  apply Measure.pi_eq
  intro s hs
  have hbox : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi hs
  rw [tilted_apply_eq_ofReal_integral' _ hbox, hN]
  change ENNReal.ofReal (∫ v : Shao.Path n in Set.pi Set.univ s, Real.exp (F v) / Z ^ n ∂P) =
    ∏ i : Fin n, (η.tilted f) (s i)
  simp_rw [hd]
  rw [← integral_indicator hbox]
  have hind (v : Shao.Path n) :
      (Set.pi Set.univ s).indicator (fun v : Shao.Path n => ∏ i : Fin n, w (v i)) v =
        ∏ i : Fin n, (s i).indicator w (v i) := by
    by_cases hv : ∀ i : Fin n, v i ∈ s i
    · have hvset : v ∈ Set.pi Set.univ s := by simpa using hv
      rw [Set.indicator_of_mem hvset]
      exact Finset.prod_congr rfl (fun i _ => (Set.indicator_of_mem (hv i) w).symm)
    · have hvset : v ∉ Set.pi Set.univ s := by simpa using hv
      rw [Set.indicator_of_notMem hvset]
      obtain ⟨i, hi⟩ := not_forall.mp hv
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi w)).symm
  simp_rw [hind]
  have hwNon (a : ℝ) : 0 ≤ w a := div_nonneg (Real.exp_pos _).le hZ.le
  have hsiNon (i : Fin n) : 0 ≤ ∫ a : ℝ, (s i).indicator w a ∂η :=
    integral_nonneg (fun a => Set.indicator_nonneg (fun u _ => hwNon u) a)
  rw [integral_fintype_prod_eq_prod (fun i : Fin n => (s i).indicator w),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => hsiNon i)]
  apply Finset.prod_congr rfl
  intro i _
  rw [tilted_apply_eq_ofReal_integral' f (hs i), ← integral_indicator (hs i)]

private theorem ep_variance_pair
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (f : ℝ → ℝ) (h2 : MemLp f 2 ν) :
    (∫ p : ℝ × ℝ, (f p.1 - f p.2) ^ 2 ∂ν.prod ν) = 2 * variance f ν := by
  have h1 := h2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hcross := h1.mul_prod h1
  have hA := h2.integrable_sq.comp_fst ν
  have hB := h2.integrable_sq.comp_snd ν
  have he (p : ℝ × ℝ) : (f p.1 - f p.2) ^ 2 =
      f p.1 ^ 2 + f p.2 ^ 2 - 2 * (f p.1 * f p.2) := by ring
  have hAf : (∫ p : ℝ × ℝ, f p.1 ^ 2 ∂ν.prod ν) = ∫ a : ℝ, f a ^ 2 ∂ν := by
    simpa only [probReal_univ, one_smul] using
      (integral_fun_fst (μ := ν) (ν := ν) (fun a : ℝ => f a ^ 2))
  have hBf : (∫ p : ℝ × ℝ, f p.2 ^ 2 ∂ν.prod ν) = ∫ a : ℝ, f a ^ 2 ∂ν := by
    simpa only [probReal_univ, one_smul] using
      (integral_fun_snd (μ := ν) (ν := ν) (fun a : ℝ => f a ^ 2))
  simp_rw [he]
  rw [integral_sub (f := fun p : ℝ × ℝ => f p.1 ^ 2 + f p.2 ^ 2)
      (g := fun p : ℝ × ℝ => 2 * (f p.1 * f p.2)) (hA.add hB) (hcross.const_mul 2),
    integral_add (f := fun p : ℝ × ℝ => f p.1 ^ 2) (g := fun p : ℝ × ℝ => f p.2 ^ 2)
      hA hB, integral_const_mul, hAf, hBf,
    integral_prod_mul f f, variance_eq_sub h2]
  simp only [Pi.pow_apply]
  ring

private theorem ep_g_variance_lower
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h t : ℝ) (hh : 0 < h) (ht : 0 < t)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) (hthin : t * h ≤ 1 / 800) :
    (3 / 4) * variance (id : ℝ → ℝ) ν ≤
      variance (fun a : ℝ => a - t * a ^ 2 / 2) ν := by
  let g : ℝ → ℝ := fun a => a - t * a ^ 2 / 2
  have hg2 := (ep_g_centered_third ν h t hh ht hsupport hthin).1
  have h2 : MemLp (id : ℝ → ℝ) 2 ν :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2
      (ep_bounded_power ν h hh.le hsupport 2).1
  have hprodg : MemLp (fun p : ℝ × ℝ => g p.1 - g p.2) 2 (ν.prod ν) :=
    (hg2.comp_measurePreserving measurePreserving_fst).sub
      (hg2.comp_measurePreserving measurePreserving_snd)
  have hprod : MemLp (fun p : ℝ × ℝ => p.1 - p.2) 2 (ν.prod ν) :=
    (h2.comp_measurePreserving measurePreserving_fst).sub
      (h2.comp_measurePreserving measurePreserving_snd)
  have hsPair : ∀ᵐ p : ℝ × ℝ ∂ν.prod ν, |p.1| ≤ h ∧ |p.2| ≤ h := by
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hsupport,
      measurePreserving_snd.quasiMeasurePreserving.ae hsupport] with p hp hq
    exact ⟨hp, hq⟩
  have hi := integral_mono_ae (hprod.integrable_sq.const_mul (3 / 4)) hprodg.integrable_sq (by
    filter_upwards [hsPair] with p hp
    change (3 / 4) * (p.1 - p.2) ^ 2 ≤ (g p.1 - g p.2) ^ 2
    have hsum := abs_add_le p.1 p.2
    have hlow : 7 / 8 ≤ 1 - t * (p.1 + p.2) / 2 := by
      have hu : p.1 + p.2 ≤ 2 * h :=
        (le_abs_self (p.1 + p.2)).trans (hsum.trans (by linarith [hp.1, hp.2]))
      have htu := mul_le_mul_of_nonneg_left hu ht.le
      nlinarith only [htu, hthin]
    have hsq : (3 / 4 : ℝ) ≤ (1 - t * (p.1 + p.2) / 2) ^ 2 := by nlinarith only [hlow]
    have hmul := mul_nonneg (sq_nonneg (p.1 - p.2)) (sub_nonneg.mpr hsq)
    have he : (g p.1 - g p.2) ^ 2 = (p.1 - p.2) ^ 2 * (1 - t * (p.1 + p.2) / 2) ^ 2 := by
      dsimp [g]
      ring
    rw [he]
    nlinarith only [hmul])
  change (∫ p : ℝ × ℝ, (3 / 4) * (p.1 - p.2) ^ 2 ∂ν.prod ν) ≤
    ∫ p : ℝ × ℝ, (g p.1 - g p.2) ^ 2 ∂ν.prod ν at hi
  have hpairId := ep_variance_pair ν id h2
  simp only [id_eq] at hpairId
  rw [integral_const_mul, hpairId, ep_variance_pair ν g hg2] at hi
  linarith only [hi]

private theorem ep_tilt_variance_lower
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (n : ℕ) (hn : 1 ≤ n) (h t c : ℝ) (hh : 0 < h) (ht : 0 < t)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hsupport : ∀ᵐ a : ℝ ∂η, |a| ≤ h) (hthin : t * h ≤ 1 / 800)
    (hsmall :
      (1 + t) * ((n : ℝ) * |∫ a : ℝ, a ∂η|) +
      (1 + t) ^ 2 * |(n : ℝ) * (∫ a : ℝ, a ^ 2 ∂η) - 1| +
      (1 + t) ^ 3 * ((n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂η)) ≤ 1 / 1000) :
    let ρ : Measure ℝ := η.tilted (fun a : ℝ => t * a - c * t ^ 2 * a ^ 2)
    (1 / 4 : ℝ) ≤ (n : ℝ) * variance (fun a : ℝ => a - t * a ^ 2 / 2) ρ := by
  dsimp only
  let ρ : Measure ℝ := η.tilted (fun a : ℝ => t * a - c * t ^ 2 * a ^ 2)
  let mu : ℝ := ∫ a : ℝ, a ∂η
  let q : ℝ := (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂η)
  let beta : ℝ := (n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂η)
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : 0 ≤ beta := by dsimp [beta]; positivity
  have hmn : 0 ≤ (n : ℝ) * |mu| := by positivity
  have hterms : 0 ≤ (1 + t) ^ 3 * beta := by positivity
  have hmuN : (n : ℝ) * |mu| ≤ 1 / 1000 := by
    have hfirst : (n : ℝ) * |mu| ≤ (1 + t) * ((n : ℝ) * |mu|) := by nlinarith only [ht, hmn]
    change (1 + t) * ((n : ℝ) * |mu|) + (1 + t) ^ 2 * |q - 1| +
      (1 + t) ^ 3 * beta ≤ 1 / 1000 at hsmall
    linarith [mul_nonneg (sq_nonneg (1 + t)) (abs_nonneg (q - 1))]
  have hqD : |q - 1| ≤ 1 / 1000 := by
    have hfirst : |q - 1| ≤ (1 + t) ^ 2 * |q - 1| := by
      have hu := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (1 + t) ^ 2 by nlinarith) (abs_nonneg (q - 1))
      simpa only [one_mul] using hu
    have hm0 : 0 ≤ (1 + t) * ((n : ℝ) * |mu|) := by positivity
    change (1 + t) * ((n : ℝ) * |mu|) + (1 + t) ^ 2 * |q - 1| +
      (1 + t) ^ 3 * beta ≤ 1 / 1000 at hsmall
    linarith only [hsmall, hfirst, hm0, hterms]
  obtain ⟨_, _, _, _, _, _, hprob, _, _, hsρ, _, _, _, _, hp, _, _, hV, _, hVL, _, _⟩ :=
    boundedQuadraticTilt_density_moments η h t (c * t ^ 2) hh (by positivity) hsupport
  change IsProbabilityMeasure ρ at hprob
  change ∀ᵐ a : ℝ ∂ρ, |a| ≤ h at hsρ
  letI : IsProbabilityMeasure ρ := hprob
  have hVn : (3 / 4 : ℝ) ≤ (n : ℝ) * variance (id : ℝ → ℝ) η := by
    rw [hV]
    change (3 / 4 : ℝ) ≤ (n : ℝ) * ((∫ a : ℝ, a ^ 2 ∂η) - mu ^ 2)
    have hmuSq := pow_le_pow_left₀ hmn hmuN 2
    have hnmu : (n : ℝ) * mu ^ 2 ≤ ((n : ℝ) * |mu|) ^ 2 := by
      have hu := mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hN)) (sq_nonneg mu)
      rw [mul_pow, sq_abs]
      nlinarith only [hu]
    have hql := (neg_le_abs (q - 1)).trans hqD
    dsimp [q] at hql
    nlinarith only [hmuSq, hnmu, hql]
  let S : ℝ := t * h + c * t ^ 2 * h ^ 2
  have hk2 := pow_le_pow_left₀ (mul_nonneg ht.le hh.le) hthin 2
  norm_num at hk2
  have hS : S ≤ 1 / 400 := by
    have hu := mul_le_mul_of_nonneg_right hc1 (show 0 ≤ t ^ 2 * h ^ 2 by positivity)
    dsimp [S]
    nlinarith only [hu, hthin, hk2]
  rw [abs_of_pos ht] at hVL
  change Real.exp (-(2 * S)) * variance (id : ℝ → ℝ) η ≤ variance (id : ℝ → ℝ) ρ at hVL
  have he : 1 / 2 ≤ Real.exp (-(2 * S)) := by linarith [Real.add_one_le_exp (-(2 * S))]
  have hVr : (1 / 2) * variance (id : ℝ → ℝ) η ≤ variance (id : ℝ → ℝ) ρ :=
    (mul_le_mul_of_nonneg_right he (variance_nonneg _ _)).trans hVL
  have hg := ep_g_variance_lower ρ h t hh ht hsρ hthin
  have hVrN := mul_le_mul_of_nonneg_left hVr (Nat.cast_nonneg n)
  have hgN := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg n)
  nlinarith only [hVn, hVrN, hgN]

private theorem ep_tilt_random_interval_bound
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (n : ℕ) (hn : 1 ≤ n) (h t c : ℝ) (hh : 0 < h) (ht : 0 < t)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hsupport : ∀ᵐ a : ℝ ∂η, |a| ≤ h) (hthin : t * h ≤ 1 / 800)
    (hsmall :
      (1 + t) * ((n : ℝ) * |∫ a : ℝ, a ∂η|) +
      (1 + t) ^ 2 * |(n : ℝ) * (∫ a : ℝ, a ^ 2 ∂η) - 1| +
      (1 + t) ^ 3 * ((n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂η)) ≤ 1 / 1000) :
    let mu : ℝ := ∫ a : ℝ, a ∂η
    let q : ℝ := (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂η)
    let beta : ℝ := (n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂η)
    let z : ℝ := (1 + t) * ((n : ℝ) * |mu|) +
      (1 + t) ^ 2 * |q - 1| + (1 + t) ^ 3 * beta
    let ρ : Measure ℝ := η.tilted (fun a : ℝ => t * a - c * t ^ 2 * a ^ 2)
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ρ)
    let W : Shao.Path n → ℝ := fun v =>
      Shao.prefixSum v n - t * Shao.energy v / 2 - t / 2
    let R : Shao.Path n → ℝ := fun v =>
      t / 2 * min ((Shao.energy v - 1) ^ 2) |Shao.energy v - 1|
    P.real {v : Shao.Path n | -R v ≤ W v ∧ W v ≤ 0} ≤
      (2 : ℝ) ^ 15 * z / (1 + t) := by
  classical
  dsimp only
  let p : ℝ := 1 + t
  let mu : ℝ := ∫ a : ℝ, a ∂η
  let q : ℝ := (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂η)
  let beta : ℝ := (n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂η)
  let d : ℝ := |q - 1|
  let z : ℝ := p * ((n : ℝ) * |mu|) + p ^ 2 * d + p ^ 3 * beta
  let ρ : Measure ℝ := η.tilted (fun a : ℝ => t * a - c * t ^ 2 * a ^ 2)
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ρ)
  let g : ℝ → ℝ := fun a => a - t * a ^ 2 / 2
  let m : ℝ := ∫ a : ℝ, g a ∂ρ
  let sigma : ℝ := Real.sqrt ((n : ℝ) * variance g ρ)
  let qc : ℝ := (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ρ)
  let B3 : ℝ := (n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂ρ)
  let B4 : ℝ := (n : ℝ) * (∫ a : ℝ, a ^ 4 ∂ρ)
  let W : Shao.Path n → ℝ := fun v => Shao.prefixSum v n - t * Shao.energy v / 2 - t / 2
  let R : Shao.Path n → ℝ := fun v => t / 2 * min ((Shao.energy v - 1) ^ 2) |Shao.energy v - 1|
  have hp : 0 < p := by dsimp [p]; linarith
  have hd : 0 ≤ d := abs_nonneg _
  have hb : 0 ≤ beta := by dsimp [beta]; positivity
  have hpd : 0 ≤ p * d + beta := by positivity
  obtain ⟨hprob, hsρ, _, _, h3c, h4c, hqc⟩ := ep_tilt_moment_budget η h t c hh ht hc0 hc1 hsupport hthin
  change IsProbabilityMeasure ρ at hprob
  change ∀ᵐ a : ℝ ∂ρ, |a| ≤ h at hsρ
  letI : IsProbabilityMeasure ρ := hprob
  have hNV := ep_tilt_variance_lower η n hn h t c hh ht hc0 hc1 hsupport hthin hsmall
  change (1 / 4 : ℝ) ≤ (n : ℝ) * variance g ρ at hNV
  have hV : 0 < variance g ρ := by
    by_contra hnot
    have hu := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (le_of_not_gt hnot)
    linarith only [hu, hNV]
  have hsigma : 1 / 2 ≤ sigma := by
    have hs := Real.sq_sqrt (show 0 ≤ (n : ℝ) * variance g ρ by positivity)
    have hn := Real.sqrt_nonneg ((n : ℝ) * variance g ρ)
    dsimp [sigma]
    nlinarith only [hs, hn, hNV]
  have hsp : 0 < sigma := by linarith only [hsigma]
  have hB3 : B3 ≤ 2 * beta := by
    have hu := mul_le_mul_of_nonneg_left h3c (Nat.cast_nonneg n)
    change (n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂ρ) ≤ (n : ℝ) * (2 * ∫ a : ℝ, |a| ^ 3 ∂η) at hu
    dsimp [B3, beta]
    nlinarith only [hu]
  have hB4 : B4 ≤ 2 * h * beta := by
    have hu := mul_le_mul_of_nonneg_left h4c (Nat.cast_nonneg n)
    change (n : ℝ) * (∫ a : ℝ, a ^ 4 ∂ρ) ≤ (n : ℝ) * (2 * h * ∫ a : ℝ, |a| ^ 3 ∂η) at hu
    dsimp [B4, beta]
    nlinarith only [hu]
  have hQc : |qc - 1| ≤ d + 12 * t * beta := by
    have hu := mul_le_mul_of_nonneg_left hqc (Nat.cast_nonneg n)
    have he : qc - 1 = (n : ℝ) * ((∫ a : ℝ, a ^ 2 ∂ρ) - (∫ a : ℝ, a ^ 2 ∂η)) + (q - 1) := by
      dsimp [qc, q]
      ring
    rw [he]
    have hi := abs_add_le ((n : ℝ) * ((∫ a : ℝ, a ^ 2 ∂ρ) - (∫ a : ℝ, a ^ 2 ∂η))) (q - 1)
    simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))] at hi
    dsimp [d, beta]
    nlinarith only [hu, hi]
  have hz : z ≤ 1 / 1000 := hsmall
  have hparts : p ^ 2 * d + p ^ 3 * beta ≤ 1 / 1000 := by
    have hm : 0 ≤ p * ((n : ℝ) * |mu|) := by positivity
    dsimp [z] at hz
    linarith only [hz, hm]
  have htd : t * d ≤ 1 / 1000 := by
    have hu := mul_le_mul_of_nonneg_right (show t ≤ p ^ 2 by dsimp [p]; nlinarith only [ht]) hd
    linarith [show 0 ≤ p ^ 3 * beta by positivity]
  have htb : t ^ 3 * beta ≤ 1 / 1000 := by
    have hu := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ ht.le (show t ≤ p by dsimp [p]; linarith) 3) hb
    linarith [show 0 ≤ p ^ 2 * d by positivity]
  have hwidth : t / 2 * (B4 + (qc - 1) ^ 2) ≤ p * d + beta := by
    have hs := pow_le_pow_left₀ (abs_nonneg (qc - 1)) hQc 2
    rw [sq_abs] at hs
    have hsq : (qc - 1) ^ 2 ≤ 2 * d ^ 2 + 288 * t ^ 2 * beta ^ 2 := by
      nlinarith [sq_nonneg (d - 12 * t * beta)]
    have hsqT := mul_le_mul_of_nonneg_left hsq ht.le
    have h4T := mul_le_mul_of_nonneg_left hB4 ht.le
    have hthinB := mul_le_mul_of_nonneg_right hthin hb
    have htdD := mul_le_mul_of_nonneg_right htd hd
    have htbB := mul_le_mul_of_nonneg_right htb hb
    dsimp [p]
    nlinarith only [hsqT, h4T, hthinB, htdD, htbB, hd, hb, mul_nonneg ht.le hd]
  have hbase := boundedEndpoint_energy_clip_random_interval ρ n hn h t hh ht hsρ hthin hV
    (t / 2 - (n : ℝ) * m)
  dsimp only at hbase
  have hY (v : Shao.Path n) :
      Shao.prefixSum (fun i : Fin n => g (v i)) n - (n : ℝ) * m =
        W v + t / 2 - (n : ℝ) * m := by
    dsimp [g, W]
    simp only [Shao.prefixSum_length, Finset.sum_sub_distrib,
      ← Finset.sum_div, ← Finset.mul_sum, Shao.energy]
    ring
  change P.real {v : Shao.Path n |
    (t / 2 - (n : ℝ) * m) - R v ≤ Shao.prefixSum (fun i : Fin n => g (v i)) n - (n : ℝ) * m ∧
      Shao.prefixSum (fun i : Fin n => g (v i)) n - (n : ℝ) * m ≤ (t / 2 - (n : ℝ) * m)} ≤
      1024 * B3 / sigma ^ 3 + t / sigma * (B4 + (qc - 1) ^ 2) + 16 * t * B3 / sigma ^ 2 at hbase
  have hevent : {v : Shao.Path n |
    (t / 2 - (n : ℝ) * m) - R v ≤ Shao.prefixSum (fun i : Fin n => g (v i)) n - (n : ℝ) * m ∧
      Shao.prefixSum (fun i : Fin n => g (v i)) n - (n : ℝ) * m ≤ (t / 2 - (n : ℝ) * m)} =
        {v : Shao.Path n | -R v ≤ W v ∧ W v ≤ 0} := by
    ext v
    simp only [Set.mem_setOf_eq]
    rw [hY]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hevent] at hbase
  have hfirst : 1024 * B3 / sigma ^ 3 ≤ 16384 * beta := by
    apply (div_le_iff₀ (pow_pos hsp 3)).2
    have hu := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hsigma 3) (show 0 ≤ 16384 * beta by positivity)
    norm_num at hu
    nlinarith only [hu, hB3]
  have hthird : 16 * t * B3 / sigma ^ 2 ≤ 128 * t * beta := by
    apply (div_le_iff₀ (sq_pos_of_pos hsp)).2
    have hu := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hsigma 2) (show 0 ≤ 128 * t * beta by positivity)
    have hbT := mul_le_mul_of_nonneg_left hB3 ht.le
    norm_num at hu
    nlinarith only [hu, hbT]
  have hmiddle : t / sigma * (B4 + (qc - 1) ^ 2) ≤ 4 * (p * d + beta) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hsp).2
    have hu := mul_le_mul_of_nonneg_left hsigma hpd
    nlinarith only [hu, hwidth]
  have hratio : p * d + p ^ 2 * beta ≤ z / p := by
    apply (le_div_iff₀ hp).2
    dsimp [z]
    have hm : 0 ≤ p * ((n : ℝ) * |mu|) := by positivity
    nlinarith only [hm]
  change P.real {v : Shao.Path n | -R v ≤ W v ∧ W v ≤ 0} ≤ (2 : ℝ) ^ 15 * z / p
  calc
    _ ≤ 16384 * beta + 4 * (p * d + beta) + 128 * t * beta := by
      linarith only [hbase, hfirst, hmiddle, hthird]
    _ ≤ 32768 * (p * d + p ^ 2 * beta) := by
      dsimp [p]
      nlinarith [mul_nonneg (sq_nonneg t) hb, mul_nonneg ht.le hb, mul_nonneg ht.le hd]
    _ ≤ 32768 * (z / p) := mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ = _ := by norm_num; ring

private theorem ep_tilted_sub_const
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hfi : Integrable (fun ω => Real.exp (f ω)) μ) (c : ℝ) :
    μ.tilted (fun ω => f ω - c) = μ.tilted f := by
  letI : IsProbabilityMeasure (μ.tilted f) := isProbabilityMeasure_tilted hfi
  have he := tilted_tilted hfi (fun _ : Ω => -c)
  rw [tilted_const] at he
  have hf : (fun ω => f ω - c) = f + (fun _ : Ω => -c) := by
    funext ω
    simp only [Pi.add_apply, sub_eq_add_neg]
  rw [hf]
  exact he.symm

private theorem ep_weighted_tilt_event
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hfi : Integrable (fun ω => Real.exp (f ω)) μ)
    (E : Set Ω) (hE : MeasurableSet E) :
    (∫ ω, E.indicator (fun ω => Real.exp (f ω)) ω ∂μ) =
      (∫ ω, Real.exp (f ω) ∂μ) * (μ.tilted f).real E := by
  let Z : ℝ := ∫ ω, Real.exp (f ω) ∂μ
  have hZ : 0 < Z := integral_exp_pos hfi
  have he := integral_tilted (μ := μ) f (E.indicator (fun _ : Ω => (1 : ℝ)))
  have hconst : (∫ ω, E.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ.tilted f) = (μ.tilted f).real E :=
    integral_indicator_one hE
  rw [hconst] at he
  have hpoint (ω : Ω) : (Real.exp (f ω) / Z) * E.indicator (fun _ : Ω => (1 : ℝ)) ω =
      E.indicator (fun ω => Real.exp (f ω)) ω / Z := by
    by_cases hω : ω ∈ E <;> simp [hω]
  simp only [smul_eq_mul] at he
  change (μ.tilted f).real E = ∫ ω, (Real.exp (f ω) / Z) * E.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ at he
  simp_rw [hpoint] at he
  rw [integral_div] at he
  change (∫ ω, E.indicator (fun ω => Real.exp (f ω)) ω ∂μ) = Z * (μ.tilted f).real E
  rw [he]
  field_simp [hZ.ne']

private theorem ep_energy_retilt
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (n : ℕ) (h t c : ℝ) (hh : 0 < h) (ht : 0 < t)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hsupport : ∀ᵐ a : ℝ ∂η, |a| ≤ h) (hthin : t * h ≤ 1 / 800) :
    let ηT : Measure ℝ := η.tilted (fun a : ℝ => t * a - t ^ 2 * a ^ 2 / 2)
    let T : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ηT)
    let s : ℝ := (1 / 2 - c) * t ^ 2
    T.tilted (fun v : Shao.Path n => s * (Shao.energy v - 1)) =
      Measure.pi (fun _ : Fin n => η.tilted (fun a : ℝ => t * a - c * t ^ 2 * a ^ 2)) := by
  dsimp only
  let f : ℝ → ℝ := fun a => t * a - t ^ 2 * a ^ 2 / 2
  let ηT : Measure ℝ := η.tilted f
  let T : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ηT)
  let s : ℝ := (1 / 2 - c) * t ^ 2
  have hfi : Integrable (fun a : ℝ => Real.exp (f a)) η := by
    convert (boundedQuadraticTilt_density_moments η h t (t ^ 2 / 2) hh (by positivity) hsupport).1 using 1
    funext a
    congr 1
    dsimp [f]
    ring
  letI : IsProbabilityMeasure ηT := isProbabilityMeasure_tilted hfi
  have hsT : ∀ᵐ a : ℝ ∂ηT, |a| ≤ h := (tilted_absolutelyContinuous η f).ae_le hsupport
  have henergyI : Integrable (fun a : ℝ => Real.exp (s * a ^ 2)) ηT :=
    ep_integrable_bound ηT _ (by fun_prop) (Real.exp (|s| * h ^ 2)) (by
      filter_upwards [hsT] with a ha
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have ha2 : a ^ 2 ≤ h ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) ha 2
      have hu := mul_le_mul_of_nonneg_left ha2 (abs_nonneg s)
      have hl := mul_le_mul_of_nonneg_right (le_abs_self s) (sq_nonneg a)
      linarith only [hu, hl])
  have hmarg : ηT.tilted (fun a : ℝ => s * a ^ 2) =
      η.tilted (fun a : ℝ => t * a - c * t ^ 2 * a ^ 2) := by
    rw [tilted_tilted hfi]
    congr 1
    ext a
    dsimp [f, s]
    ring
  have hp := ep_pi_tilted ηT n (fun a : ℝ => s * a ^ 2) (by fun_prop) henergyI
  rw [hmarg] at hp
  have hsum : (fun v : Shao.Path n => ∑ i : Fin n, s * (v i) ^ 2) =
      (fun v : Shao.Path n => s * Shao.energy v) := by
    ext v
    exact (Finset.mul_sum _ _ _).symm
  rw [hsum] at hp
  have hprodI : Integrable (fun v : Shao.Path n => Real.exp (s * Shao.energy v)) T := by
    have he (v : Shao.Path n) : Real.exp (s * Shao.energy v) =
        Real.exp s * Real.exp (s * (Shao.energy v - 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp_rw [he]
    exact (ep_energy_exp_integrable ηT n h s hh.le hsT).const_mul (Real.exp s)
  have hconst := ep_tilted_sub_const T (fun v : Shao.Path n => s * Shao.energy v) hprodI s
  have hf : (fun v : Shao.Path n => s * Shao.energy v - s) =
      (fun v : Shao.Path n => s * (Shao.energy v - 1)) := by ext v; ring
  rw [hf] at hconst
  exact hconst.trans hp.symm

theorem boundedEndpoint_quadraticTilt_random_window_explicit
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (n : ℕ) (hn : 1 ≤ n) (h t : ℝ) (hh : 0 < h) (ht : 0 < t)
    (hsupport : ∀ᵐ a : ℝ ∂eta, |a| ≤ h)
    (hthin : t * h ≤ 1 / 800)
    (hsmall :
      (1 + t) * ((n : ℝ) * |∫ a : ℝ, a ∂eta|) +
      (1 + t) ^ 2 * |(n : ℝ) * (∫ a : ℝ, a ^ 2 ∂eta) - 1| +
      (1 + t) ^ 3 * ((n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂eta)) ≤ 1 / 1000) :
    let mu : ℝ := ∫ a : ℝ, a ∂eta
    let q : ℝ := (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂eta)
    let beta : ℝ := (n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂eta)
    let z : ℝ := (1 + t) * ((n : ℝ) * |mu|) +
      (1 + t) ^ 2 * |q - 1| + (1 + t) ^ 3 * beta
    let etaT : Measure ℝ := eta.tilted (fun a : ℝ => t * a - t ^ 2 * a ^ 2 / 2)
    let T : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => etaT)
    let W : Shao.Path n → ℝ := fun v =>
      Shao.prefixSum v n - t * Shao.energy v / 2 - t / 2
    let J : Shao.Path n → ℝ := fun v =>
      if -(t * (Real.sqrt (Shao.energy v) - 1) ^ 2 / 2) ≤ W v ∧ W v < 0
      then Real.exp (-t * W v) else 0
    (∫ v : Shao.Path n, J v ∂T) ≤ (2 : ℝ) ^ 17 * z / (1 + t) := by
  classical
  dsimp only
  let etaT : Measure ℝ := eta.tilted (fun a : ℝ => t * a - t ^ 2 * a ^ 2 / 2)
  let T : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => etaT)
  let P0 : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => eta.tilted (fun a : ℝ => t * a))
  let P1 : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => eta.tilted (fun a : ℝ => t * a - t ^ 2 * a ^ 2))
  let mu : ℝ := ∫ a : ℝ, a ∂eta
  let q : ℝ := (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂eta)
  let beta : ℝ := (n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂eta)
  let z : ℝ := (1 + t) * ((n : ℝ) * |mu|) + (1 + t) ^ 2 * |q - 1| + (1 + t) ^ 3 * beta
  let s : ℝ := t ^ 2 / 2
  let W : Shao.Path n → ℝ := fun v => Shao.prefixSum v n - t * Shao.energy v / 2 - t / 2
  let R : Shao.Path n → ℝ := fun v => t / 2 * min ((Shao.energy v - 1) ^ 2) |Shao.energy v - 1|
  let E : Set (Shao.Path n) := {v | -R v ≤ W v ∧ W v ≤ 0}
  let J : Shao.Path n → ℝ := fun v =>
    if -(t * (Real.sqrt (Shao.energy v) - 1) ^ 2 / 2) ≤ W v ∧ W v < 0
    then Real.exp (-t * W v) else 0
  let Uplus : Shao.Path n → ℝ := fun v => Real.exp (s * (Shao.energy v - 1))
  let Uminus : Shao.Path n → ℝ := fun v => Real.exp ((-s) * (Shao.energy v - 1))
  have hhalf := ep_tilt_moment_budget eta h t (1 / 2) hh ht (by norm_num) (by norm_num) hsupport hthin
  have hfhalf : (fun a : ℝ => t * a - (1 / 2) * t ^ 2 * a ^ 2) =
      (fun a : ℝ => t * a - t ^ 2 * a ^ 2 / 2) := by ext a; ring
  dsimp only at hhalf
  rw [hfhalf] at hhalf
  have hprob : IsProbabilityMeasure etaT := hhalf.1
  letI : IsProbabilityMeasure etaT := hprob
  have hsnon : 0 ≤ s := by dsimp [s]; positivity
  have hMplus := boundedEndpoint_quadraticTilt_energy_exponential_moment eta n hn h t hh ht hsupport hthin hsmall
    s (by dsimp [s]; rw [abs_of_nonneg (by positivity : 0 ≤ t ^ 2 / 2)])
  have hMminus := boundedEndpoint_quadraticTilt_energy_exponential_moment eta n hn h t hh ht hsupport hthin hsmall
    (-s) (by rw [abs_neg, abs_of_nonneg hsnon])
  change Integrable Uplus T ∧ (∫ v : Shao.Path n, Uplus v ∂T) ≤ 2 at hMplus
  change Integrable Uminus T ∧ (∫ v : Shao.Path n, Uminus v ∂T) ≤ 2 at hMminus
  have hWm : Measurable W := by
    exact ((Shao.measurable_prefixSum n).sub ((Shao.measurable_energy.const_mul t).div_const 2)).sub_const (t / 2)
  have hRm : Measurable R :=
    (((Shao.measurable_energy.sub_const 1).pow_const 2).min
      (continuous_abs.measurable.comp (Shao.measurable_energy.sub_const 1))).const_mul (t / 2)
  have hE : MeasurableSet E :=
    (measurableSet_le hRm.neg hWm).inter (measurableSet_le hWm measurable_const)
  have hDm : Measurable (fun v : Shao.Path n => t * (Real.sqrt (Shao.energy v) - 1) ^ 2 / 2) :=
    ((((Real.continuous_sqrt.measurable.comp Shao.measurable_energy).sub_const 1).pow_const 2).const_mul t).div_const 2
  have hJm : Measurable J := Measurable.ite
    ((measurableSet_le hDm.neg hWm).inter (measurableSet_lt hWm measurable_const))
    ((hWm.const_mul (-t)).exp) measurable_const
  have hJnon (v : Shao.Path n) : 0 ≤ J v := by dsimp [J]; split_ifs <;> positivity
  have hpoint (v : Shao.Path n) : J v ≤ E.indicator Uplus v + E.indicator Uminus v := by
    by_cases hband : -(t * (Real.sqrt (Shao.energy v) - 1) ^ 2 / 2) ≤ W v ∧ W v < 0
    · have hclip := ep_sqrt_clip (Shao.energy v) (Shao.energy_nonneg v)
      have hDR : t * (Real.sqrt (Shao.energy v) - 1) ^ 2 / 2 ≤ R v := by
        have hu := mul_le_mul_of_nonneg_left hclip (show 0 ≤ t / 2 by positivity)
        convert hu using 1 <;> (try dsimp [R]) <;> ring
      have hER : v ∈ E := ⟨by linarith only [hband.1, hDR], hband.2.le⟩
      simp only [J, if_pos hband, Set.indicator_of_mem hER]
      have hDabs : (Real.sqrt (Shao.energy v) - 1) ^ 2 ≤ |Shao.energy v - 1| :=
        hclip.trans (min_le_right _ _)
      have hupper : -t * W v ≤ s * |Shao.energy v - 1| := by
        have hu := mul_le_mul_of_nonneg_left hDabs (show 0 ≤ t ^ 2 / 2 by positivity)
        have hw := mul_le_mul_of_nonneg_left hband.1 ht.le
        dsimp [s]
        nlinarith only [hu, hw]
      apply (Real.exp_le_exp.mpr hupper).trans
      dsimp [Uplus, Uminus]
      rcases le_total 0 (Shao.energy v - 1) with hQ | hQ
      · rw [abs_of_nonneg hQ]
        linarith [Real.exp_pos ((-s) * (Shao.energy v - 1))]
      · rw [abs_of_nonpos hQ]
        have he : s * -(Shao.energy v - 1) = (-s) * (Shao.energy v - 1) := by ring
        rw [he]
        linarith [Real.exp_pos (s * (Shao.energy v - 1))]
    · simp only [J, if_neg hband]
      exact add_nonneg
        (Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) v)
        (Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) v)
  have hmajor : Integrable (fun v : Shao.Path n => E.indicator Uplus v + E.indicator Uminus v) T :=
    (hMplus.1.indicator hE).add (hMminus.1.indicator hE)
  have hJI : Integrable J T := hmajor.mono' hJm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hJnon v)] using hpoint v)
  have hInt := integral_mono hJI hmajor hpoint
  change (∫ v : Shao.Path n, J v ∂T) ≤ ∫ v : Shao.Path n, E.indicator Uplus v + E.indicator Uminus v ∂T at hInt
  rw [integral_add (hMplus.1.indicator hE) (hMminus.1.indicator hE)] at hInt
  have htilt0 := ep_energy_retilt eta n h t 0 hh ht (by norm_num) (by norm_num) hsupport hthin
  have hs0 : (1 / 2 - (0 : ℝ)) * t ^ 2 = s := by dsimp [s]; ring
  dsimp only at htilt0
  rw [hs0] at htilt0
  simp only [zero_mul, sub_zero] at htilt0
  change T.tilted (fun v : Shao.Path n => s * (Shao.energy v - 1)) = P0 at htilt0
  have htilt1 := ep_energy_retilt eta n h t 1 hh ht (by norm_num) (by norm_num) hsupport hthin
  have hs1 : (1 / 2 - (1 : ℝ)) * t ^ 2 = -s := by dsimp [s]; ring
  dsimp only at htilt1
  rw [hs1] at htilt1
  simp only [one_mul] at htilt1
  change T.tilted (fun v : Shao.Path n => (-s) * (Shao.energy v - 1)) = P1 at htilt1
  have hplus := ep_weighted_tilt_event T (fun v : Shao.Path n => s * (Shao.energy v - 1)) hMplus.1 E hE
  have hminus := ep_weighted_tilt_event T (fun v : Shao.Path n => (-s) * (Shao.energy v - 1)) hMminus.1 E hE
  rw [htilt0] at hplus
  rw [htilt1] at hminus
  change (∫ v : Shao.Path n, E.indicator Uplus v ∂T) = (∫ v : Shao.Path n, Uplus v ∂T) * P0.real E at hplus
  change (∫ v : Shao.Path n, E.indicator Uminus v ∂T) = (∫ v : Shao.Path n, Uminus v ∂T) * P1.real E at hminus
  have hP0 := ep_tilt_random_interval_bound eta n hn h t 0 hh ht (by norm_num) (by norm_num) hsupport hthin hsmall
  dsimp only at hP0
  simp only [zero_mul, sub_zero] at hP0
  change P0.real E ≤ (2 : ℝ) ^ 15 * z / (1 + t) at hP0
  have hP1 := ep_tilt_random_interval_bound eta n hn h t 1 hh ht (by norm_num) (by norm_num) hsupport hthin hsmall
  dsimp only at hP1
  simp only [one_mul] at hP1
  change P1.real E ≤ (2 : ℝ) ^ 15 * z / (1 + t) at hP1
  rw [hplus, hminus] at hInt
  have hp0 := mul_le_mul_of_nonneg_right hMplus.2 (measureReal_nonneg : 0 ≤ P0.real E)
  have hp1 := mul_le_mul_of_nonneg_right hMminus.2 (measureReal_nonneg : 0 ≤ P1.real E)
  change (∫ v : Shao.Path n, J v ∂T) ≤ (2 : ℝ) ^ 17 * z / (1 + t)
  calc
    _ ≤ 4 * ((2 : ℝ) ^ 15 * z / (1 + t)) := by linarith only [hInt, hp0, hp1, hP0, hP1]
    _ = _ := by norm_num; ring

theorem boundedEndpoint_quadraticTilt_random_window :
    ∃ Cw : ℝ, 0 ≤ Cw ∧
      ∀ (eta : Measure ℝ) [IsProbabilityMeasure eta]
        (n : ℕ) (hn : 1 ≤ n) (h t : ℝ), 0 < h → 0 < t →
        (∀ᵐ a : ℝ ∂eta, |a| ≤ h) → t * h ≤ 1 / 800 →
        (1 + t) * ((n : ℝ) * |∫ a : ℝ, a ∂eta|) +
        (1 + t) ^ 2 * |(n : ℝ) * (∫ a : ℝ, a ^ 2 ∂eta) - 1| +
        (1 + t) ^ 3 * ((n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂eta)) ≤ 1 / 1000 →
        let mu : ℝ := ∫ a : ℝ, a ∂eta
        let q : ℝ := (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂eta)
        let beta : ℝ := (n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂eta)
        let z : ℝ := (1 + t) * ((n : ℝ) * |mu|) +
          (1 + t) ^ 2 * |q - 1| + (1 + t) ^ 3 * beta
        let etaT : Measure ℝ := eta.tilted (fun a : ℝ => t * a - t ^ 2 * a ^ 2 / 2)
        let T : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => etaT)
        let W : Shao.Path n → ℝ := fun v =>
          Shao.prefixSum v n - t * Shao.energy v / 2 - t / 2
        let J : Shao.Path n → ℝ := fun v =>
          if -(t * (Real.sqrt (Shao.energy v) - 1) ^ 2 / 2) ≤ W v ∧ W v < 0
          then Real.exp (-t * W v) else 0
        (∫ v : Shao.Path n, J v ∂T) ≤ Cw * z / (1 + t) := by
  refine ⟨(2 : ℝ) ^ 17, by positivity, ?_⟩
  intro eta inst n hn h t hh ht hsupport hthin hsmall
  exact boundedEndpoint_quadraticTilt_random_window_explicit eta n hn h t hh ht hsupport hthin hsmall

end Shao.Probability
