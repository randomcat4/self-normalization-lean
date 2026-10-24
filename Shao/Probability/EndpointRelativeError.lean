import Shao.Probability.EndpointRandomWindow
import Shao.Probability.SourceTruncationBridge
import Shao.Probability.BoundedQuadraticTilt
import Shao.Probability.BerryEsseen
import Shao.Probability.GaussianTail
import Shao.Probability.TruncationSampleSize
import Shao.Probability.SourceClockBridge
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Layercake

/-!
The original fixed-cutoff self-normalized endpoint, retaining strict walls and
the actual zero-energy mass. The original endpoint moderate-deviation results
remain attributed to Shao--Zhou (2016); no external endpoint theorem is assumed.
-/

set_option autoImplicit false
set_option Elab.async false
namespace Shao.Probability
open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem er_pi_zero_energy
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.pi (fun _ : Fin n => ν)).real {v : Shao.Path n | Shao.energy v = 0} =
      (ν.real ({0} : Set ℝ)) ^ n := by
  have he : {v : Shao.Path n | Shao.energy v = 0} =
      Set.pi Set.univ (fun _ : Fin n => ({0} : Set ℝ)) := by
    ext v
    simp [Shao.energy_eq_zero_iff]
  rw [he, Measure.real_def, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
  rfl

private theorem er_nonzero_mass_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν)
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hm3 : 0 < ∫ a : ℝ, |a| ^ 3 ∂ν) :
    (∫ a : ℝ, a ^ 2 ∂ν) ^ 3 ≤
      (∫ a : ℝ, |a| ^ 3 ∂ν) ^ 2 * ν.real {a : ℝ | a ≠ 0} := by
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
  let C : ℝ := m2 / m3
  let E : Set ℝ := {a : ℝ | a ≠ 0}
  have hE : MeasurableSet E := (measurableSet_singleton (0 : ℝ)).compl
  have hC : 0 ≤ C := div_nonneg (integral_nonneg fun a => sq_nonneg a) hm3.le
  have hI : Integrable (E.indicator (fun _ : ℝ => (1 : ℝ))) ν :=
    (integrable_const (1 : ℝ)).indicator hE
  have hpoint (a : ℝ) : (3 * C ^ 2) * a ^ 2 ≤
      (2 * C ^ 3) * |a| ^ 3 + E.indicator (fun _ : ℝ => (1 : ℝ)) a := by
    by_cases ha : a = 0
    · simp [ha, E]
    · have hpoly := mul_nonneg (sq_nonneg (C * |a| - 1))
        (show 0 ≤ 2 * C * |a| + 1 by positivity)
      have hmem : a ∈ E := ha
      rw [Set.indicator_of_mem hmem]
      rw [← sq_abs a]
      nlinarith only [hpoly]
  have hi := integral_mono (h2.const_mul (3 * C ^ 2))
    ((h3.const_mul (2 * C ^ 3)).add hI) hpoint
  change (∫ a : ℝ, (3 * C ^ 2) * a ^ 2 ∂ν) ≤
    ∫ a : ℝ, (2 * C ^ 3) * |a| ^ 3 + E.indicator (fun _ : ℝ => (1 : ℝ)) a ∂ν at hi
  have hII : (∫ a : ℝ, E.indicator (fun _ : ℝ => (1 : ℝ)) a ∂ν) = ν.real E :=
    integral_indicator_one hE
  rw [integral_const_mul,
    integral_add (h3.const_mul (2 * C ^ 3)) hI, integral_const_mul, hII] at hi
  change 3 * C ^ 2 * m2 ≤ 2 * C ^ 3 * m3 + ν.real E at hi
  have hmid : m2 ^ 3 / m3 ^ 2 ≤ ν.real E := by
    dsimp [C] at hi
    have hidentity : 3 * (m2 / m3) ^ 2 * m2 - 2 * (m2 / m3) ^ 3 * m3 = m2 ^ 3 / m3 ^ 2 := by
      field_simp
      ring
    linarith only [hi, hidentity]
  have hfinal := (div_le_iff₀ (sq_pos_of_pos hm3)).1 hmid
  simpa only [mul_comm] using hfinal

private theorem er_zero_energy_exp_paid
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ)
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν)
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (a r : ℝ) (ha : 0 < a) (hr : 0 < r)
    (hsecond : (3 / 4 : ℝ) ≤ (n : ℝ) * (∫ u : ℝ, u ^ 2 ∂ν))
    (hthird : (n : ℝ) * (∫ u : ℝ, |u| ^ 3 ∂ν) ≤ 2 * r / a ^ 3) :
    (Measure.pi (fun _ : Fin n => ν)).real {v : Shao.Path n | Shao.energy v = 0} ≤
      Real.exp (-(a ^ 6 / (16 * r ^ 2))) := by
  let m2 : ℝ := ∫ u : ℝ, u ^ 2 ∂ν
  let m3 : ℝ := ∫ u : ℝ, |u| ^ 3 ∂ν
  let p : ℝ := ν.real {u : ℝ | u ≠ 0}
  let N : ℝ := n
  have hN : 0 ≤ N := Nat.cast_nonneg n
  have hm30 : 0 ≤ m3 := integral_nonneg fun u => pow_nonneg (abs_nonneg u) 3
  have hm3 : 0 < m3 := by
    by_contra h
    have hz : m3 = 0 := le_antisymm (le_of_not_gt h) hm30
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun u : ℝ => pow_nonneg (abs_nonneg u) 3) h3).1 hz
    have hm2 : m2 = 0 := by
      calc
        _ = ∫ _u : ℝ, (0 : ℝ) ∂ν := integral_congr_ae (by
          filter_upwards [hae] with u hu
          have hu0 : |u| = 0 := (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).1 hu
          simp [abs_eq_zero.1 hu0])
        _ = 0 := by simp
    change (3 / 4 : ℝ) ≤ N * m2 at hsecond
    rw [hm2, mul_zero] at hsecond
    norm_num at hsecond
  have hp : 0 ≤ p := measureReal_nonneg
  have hmom := er_nonzero_mass_moment ν h2 h3 hm3
  change m2 ^ 3 ≤ m3 ^ 2 * p at hmom
  have hscale : (N * m2) ^ 3 ≤ (N * m3) ^ 2 * (N * p) := by
    nlinarith only [mul_le_mul_of_nonneg_left hmom (pow_nonneg hN 3)]
  have hq : (1 / 4 : ℝ) ≤ (N * m2) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) hsecond 3
    norm_num at h
    linarith
  have hb : 0 ≤ N * m3 := mul_nonneg hN hm30
  have hbmul : N * m3 * a ^ 3 ≤ 2 * r := (le_div_iff₀ (pow_pos ha 3)).1 hthird
  have hb2 : (N * m3) ^ 2 * a ^ 6 ≤ 4 * r ^ 2 := by
    have h := pow_le_pow_left₀ (mul_nonneg hb (pow_nonneg ha.le 3)) hbmul 2
    nlinarith only [h]
  have hnp : a ^ 6 / (16 * r ^ 2) ≤ N * p := by
    apply (div_le_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hr))).2
    have h1 := mul_le_mul_of_nonneg_left (hq.trans hscale) (pow_nonneg ha.le 6)
    have h2 := mul_le_mul_of_nonneg_right hb2 (mul_nonneg hN hp)
    nlinarith only [h1, h2]
  have hp0 : ν.real ({0} : Set ℝ) = 1 - p := by
    have hc := measureReal_compl (μ := ν) (s := ({0} : Set ℝ)) (measurableSet_singleton (0 : ℝ))
    rw [probReal_univ] at hc
    have hset : ({0} : Set ℝ)ᶜ = {u : ℝ | u ≠ 0} := by ext u; simp
    rw [hset] at hc
    dsimp only [p]
    linarith
  rw [er_pi_zero_energy ν n, hp0]
  calc
    (1 - p) ^ n ≤ (Real.exp (-p)) ^ n := by
      apply pow_le_pow_left₀ (by rw [← hp0]; exact measureReal_nonneg)
      have h := Real.add_one_le_exp (-p)
      linarith only [h]
    _ = Real.exp (-(N * p)) := by rw [← Real.exp_nat_mul]; congr 1; dsimp [N]; ring
    _ ≤ Real.exp (-(a ^ 6 / (16 * r ^ 2))) := Real.exp_le_exp.2 (neg_le_neg hnp)

private theorem er_zero_energy_gaussian_numeric
    (x r : ℝ) (hx : 0 ≤ x) (hr : 0 < r) (hrsmall : r ≤ 1 / 32) :
    Real.exp (-((1 + x) ^ 6 / (16 * r ^ 2))) ≤
      Real.sqrt (2 * Real.pi) * r * Shao.standardNormalTail x := by
  let a : ℝ := 1 + x
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have ha6 : a ^ 2 ≤ a ^ 6 := by
    have h4 : 1 ≤ a ^ 4 := by simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) ha 4
    nlinarith only [mul_le_mul_of_nonneg_left h4 (sq_nonneg a)]
  have h32 : 32 * r ≤ a := by linarith
  have hr2 : r ^ 2 ≤ 1 / 16 := by nlinarith [sq_nonneg (r - 1 / 32)]
  have hexponent : x ^ 2 / 2 + a / r ≤ a ^ 6 / (16 * r ^ 2) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hr))).2
    have hmul : a / r * (16 * r ^ 2) = 16 * a * r := by field_simp
    rw [add_mul, hmul]
    have hx2 : x ^ 2 ≤ a ^ 2 := by dsimp [a]; nlinarith
    have hpart : 8 * x ^ 2 * r ^ 2 ≤ a ^ 2 / 2 := by
      have h := mul_le_mul_of_nonneg_left hr2 (sq_nonneg x)
      nlinarith only [h, hx2]
    have hpart2 : 16 * a * r ≤ a ^ 2 / 2 := by
      nlinarith only [mul_le_mul_of_nonneg_left h32 ha0.le]
    nlinarith only [hpart, hpart2, ha6]
  have hsmall : Real.exp (-(a / r)) ≤ r / a := by
    have h := Real.add_one_le_exp (a / r)
    have hd : a / r ≤ Real.exp (a / r) := by linarith only [h]
    have hmul := mul_le_mul_of_nonneg_right hd (Real.exp_pos (-(a / r))).le
    have hid : Real.exp (a / r) * Real.exp (-(a / r)) = 1 := by rw [← Real.exp_add]; simp
    rw [hid] at hmul
    apply (le_div_iff₀ ha0).2
    have hh := mul_le_mul_of_nonneg_right hmul hr.le
    have hi : (a / r * Real.exp (-(a / r))) * r = Real.exp (-(a / r)) * a := by field_simp
    rw [hi] at hh
    simpa only [one_mul] using hh
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hformula : Real.exp (-x ^ 2 / 2) = Real.sqrt (2 * Real.pi) * Shao.standardNormalDensity x := by
    simp only [Shao.standardNormalDensity, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
    field_simp
  have hM : Real.exp (-x ^ 2 / 2) / a ≤ Real.sqrt (2 * Real.pi) * Shao.standardNormalTail x := by
    rw [hformula, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (Shao.standardNormal_mills_bounds x hx).1 hsqrt.le
  calc
    _ ≤ Real.exp (-(x ^ 2 / 2 + a / r)) := Real.exp_le_exp.2 (neg_le_neg hexponent)
    _ = Real.exp (-x ^ 2 / 2) * Real.exp (-(a / r)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-x ^ 2 / 2) * (r / a) := mul_le_mul_of_nonneg_left hsmall (Real.exp_pos _).le
    _ = r * (Real.exp (-x ^ 2 / 2) / a) := by ring
    _ ≤ r * (Real.sqrt (2 * Real.pi) * Shao.standardNormalTail x) := mul_le_mul_of_nonneg_left hM hr.le
    _ = _ := by ring

theorem sourceTruncation_endpoint_zero_energy_gaussian_cost
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 800)
    (hR : Shao.truncationBudget nu n x ≤ epsilon ^ 3 / 8) :
    let r : ℝ := Shao.truncationBudget nu n x
    let rho : Measure ℝ :=
      ProbabilityTheory.cond nu {z : ℝ | |z| ≤ epsilon / (1 + x)}
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
    0 < r ∧ IsProbabilityMeasure rho ∧ IsProbabilityMeasure P ∧
      P.real {v : Shao.Path n | Shao.energy v = 0} ≤
        Real.exp (-((1 + x) ^ 6 / (16 * r ^ 2))) ∧
      P.real {v : Shao.Path n | Shao.energy v = 0} ≤
        Real.sqrt (2 * Real.pi) * r * Shao.standardNormalTail x := by
  let r : ℝ := Shao.truncationBudget nu n x
  let rho : Measure ℝ := ProbabilityTheory.cond nu {z : ℝ | |z| ≤ epsilon / (1 + x)}
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  have hn : 0 < n := by by_contra h; have hz := Nat.eq_zero_of_not_pos h; simp [hz] at hnorm
  have hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂nu := by
    by_contra h
    have hh := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (le_of_not_gt h)
    rw [hnorm] at hh
    norm_num at hh
  have hr : 0 < r := Shao.truncationBudget_pos nu n h2 hn hsecond x hx
  have heHalf : epsilon ≤ 1 / 2 := by linarith
  have hd := Shao.sourceTruncation_law_data nu n h2 hnorm x epsilon hx hepsilon heHalf hR
  haveI : IsProbabilityMeasure rho := hd.2.2.1
  haveI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hρ2 : Integrable (fun z : ℝ => z ^ 2) rho := hd.2.2.2.2.2.1
  have hρ3 : Integrable (fun z : ℝ => |z| ^ 3) rho := hd.2.2.2.2.2.2.1
  have hs := (Shao.sourceTruncation_variance_bounds nu n h2 hnorm hmean x epsilon hx hepsilon heHalf hR).1
  have hm := (Shao.sourceTruncation_paid_moments nu n h2 hnorm hmean x epsilon hx hepsilon heHalf hR).2.1
  have hzero := er_zero_energy_exp_paid rho n hρ2 hρ3 (1 + x) r (by positivity) hr hs hm
  have he3 := pow_le_pow_left₀ hepsilon.le hepsilonSmall 3
  have hrsmall : r ≤ 1 / 32 := by change Shao.truncationBudget nu n x ≤ 1 / 32; nlinarith only [hR, he3]
  exact ⟨hr, inferInstance, inferInstance, hzero, hzero.trans (er_zero_energy_gaussian_numeric x r hx hr hrsmall)⟩

private theorem er_quadratic_exp_taylor
    (v : ℝ) (hv : |v| ≤ 1 / 800) :
    let f : ℝ := v - v ^ 2 / 2
    let b : ℝ := Real.exp f
    |b - 1 - v| ≤ 2 * |v| ^ 3 ∧
      |f * b - v - v ^ 2 / 2| ≤ 4 * |v| ^ 3 ∧
      |f ^ 2 * b - v ^ 2| ≤ 4 * |v| ^ 3 := by
  let f : ℝ := v - v ^ 2 / 2
  let b : ℝ := Real.exp f
  let u : ℝ := |v|
  have hu0 : 0 ≤ u := abs_nonneg v
  have hu1 : u ≤ 1 := by dsimp [u]; linarith
  have hu4 : u ^ 4 ≤ u ^ 3 := by
    nlinarith only [mul_le_mul_of_nonneg_right hu1 (pow_nonneg hu0 3)]
  have hv2 : v ^ 2 = u ^ 2 := (sq_abs v).symm
  have huquarter : u ^ 2 ≤ u / 4 := by
    have h := mul_le_mul_of_nonneg_right (show u ≤ 1 / 4 by dsimp [u]; linarith) hu0
    nlinarith only [h]
  have hf : |f| ≤ (9 / 8 : ℝ) * u := by
    have h := abs_sub v (v ^ 2 / 2)
    rw [abs_div, abs_of_nonneg (sq_nonneg v)] at h
    norm_num at h
    dsimp only [f]
    change |v - v ^ 2 / 2| ≤ (9 / 8 : ℝ) * u
    change |v - v ^ 2 / 2| ≤ u + v ^ 2 / 2 at h
    nlinarith only [h, hv2, huquarter]
  have hf1 : |f| ≤ 1 := by dsimp [u] at hf; linarith
  have hr := Real.exp_bound (x := f) (n := 3) hf1 (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hr
  have hr' : |b - (1 + f + f ^ 2 / 2)| ≤ (1 / 2 : ℝ) * u ^ 3 := by
    have hc := pow_le_pow_left₀ (abs_nonneg f) hf 3
    have ht : |b - (1 + f + f ^ 2 / 2)| ≤ |f| ^ 3 * (2 / 9 : ℝ) := by
      convert hr using 1 <;> dsimp [b] <;> ring
    nlinarith only [ht, hc, pow_nonneg hu0 3]
  have hpoly : |f + f ^ 2 / 2 - v| ≤ (5 / 8 : ℝ) * u ^ 3 := by
    calc
      _ = |-(v ^ 3 / 2) + v ^ 4 / 8| := by congr 1; dsimp [f]; ring
      _ ≤ |-(v ^ 3 / 2)| + |v ^ 4 / 8| := abs_add_le _ _
      _ = u ^ 3 / 2 + u ^ 4 / 8 := by simp [u, abs_div, abs_pow]
      _ ≤ _ := by linarith only [hu4]
  have hfirst : |b - 1 - v| ≤ 2 * u ^ 3 := by
    calc
      _ = |(b - (1 + f + f ^ 2 / 2)) + (f + f ^ 2 / 2 - v)| := by congr 1; ring
      _ ≤ |b - (1 + f + f ^ 2 / 2)| + |f + f ^ 2 / 2 - v| := abs_add_le _ _
      _ ≤ _ := by nlinarith only [hr', hpoly, pow_nonneg hu0 3]
  have hsecond : |f * b - v - v ^ 2 / 2| ≤ 4 * u ^ 3 := by
    calc
      _ = |f * (b - 1 - v) - v ^ 3 / 2| := by congr 1; dsimp [f]; ring
      _ ≤ |f * (b - 1 - v)| + |v ^ 3 / 2| := abs_sub _ _
      _ = |f| * |b - 1 - v| + u ^ 3 / 2 := by
        have habs : |v ^ 3 / (2 : ℝ)| = u ^ 3 / 2 := by
          change |v ^ 3 / (2 : ℝ)| = |v| ^ 3 / 2
          rw [abs_div, abs_pow]
          norm_num
        rw [abs_mul]
        exact congrArg (fun q : ℝ => |f| * |b - 1 - v| + q) habs
      _ ≤ |f| * (2 * u ^ 3) + u ^ 3 / 2 := by gcongr
      _ ≤ 1 * (2 * u ^ 3) + u ^ 3 / 2 :=
        by
          have hm := mul_le_mul_of_nonneg_right hf1
            (show (0 : ℝ) ≤ 2 * u ^ 3 from mul_nonneg (by norm_num) (pow_nonneg hu0 3))
          linarith only [hm]
      _ ≤ _ := by nlinarith only [pow_nonneg hu0 3]
  have hb : |b - 1| ≤ (9 / 8 : ℝ) * u := by
    have ht : |b - 1| ≤ |b - 1 - v| + u := by
      simpa only [sub_add_cancel, u] using abs_add_le (b - 1 - v) v
    have hu2 : u ^ 2 ≤ (1 / 16 : ℝ) := by dsimp [u]; nlinarith [sq_nonneg (|v| - 1 / 800)]
    have hu3 := mul_le_mul_of_nonneg_right hu2 hu0
    nlinarith only [ht, hfirst, hu3]
  have hpoly2 : |f ^ 2 - v ^ 2| ≤ (5 / 4 : ℝ) * u ^ 3 := by
    calc
      _ = |-(v ^ 3) + v ^ 4 / 4| := by congr 1; dsimp [f]; ring
      _ ≤ |-(v ^ 3)| + |v ^ 4 / 4| := abs_add_le _ _
      _ = u ^ 3 + u ^ 4 / 4 := by simp [u, abs_div, abs_pow]
      _ ≤ _ := by linarith only [hu4]
  have hthird : |f ^ 2 * b - v ^ 2| ≤ 4 * u ^ 3 := by
    calc
      _ = |f ^ 2 * (b - 1) + (f ^ 2 - v ^ 2)| := by congr 1; ring
      _ ≤ |f ^ 2 * (b - 1)| + |f ^ 2 - v ^ 2| := abs_add_le _ _
      _ = f ^ 2 * |b - 1| + |f ^ 2 - v ^ 2| := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg f)]
      _ ≤ ((9 / 8 : ℝ) * u) ^ 2 * ((9 / 8 : ℝ) * u) + (5 / 4 : ℝ) * u ^ 3 := by
        have hfsq : f ^ 2 ≤ ((9 / 8 : ℝ) * u) ^ 2 := by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg f) hf 2
        exact add_le_add (mul_le_mul hfsq hb (abs_nonneg _) (by positivity)) hpoly2
      _ ≤ _ := by nlinarith only [pow_nonneg hu0 3]
  exact ⟨hfirst, hsecond, hthird⟩

private theorem er_integrable_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (f : Ω → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ᵐ a : Ω ∂ν, |f a| ≤ C) :
    Integrable f ν := by
  exact (integrable_const C).mono' hf.aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs] using hC)

private theorem er_pi_support (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (h : ℝ) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    ∀ᵐ v : Shao.Path n ∂Measure.pi (fun _ : Fin n => ν), ∀ i : Fin n, |v i| ≤ h := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (fun _ : Fin n => ν) i).quasiMeasurePreserving.ae hs

private theorem er_energy_bound (n : ℕ) (h : ℝ) (hh : 0 ≤ h)
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

private theorem er_pi_tilted
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

private theorem er_endpoint_exact_split
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (n : ℕ) (h t : ℝ) (hh : 0 < h) (ht : 0 < t)
    (hsupport : ∀ᵐ a : ℝ ∂eta, |a| ≤ h) :
    let f : ℝ → ℝ := fun a => t * a - t ^ 2 * a ^ 2 / 2
    let Z : ℝ := ∫ a : ℝ, Real.exp (f a) ∂eta
    let etaT : Measure ℝ := eta.tilted f
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => eta)
    let T : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => etaT)
    let W : Shao.Path n → ℝ := fun v =>
      Shao.prefixSum v n - t * Shao.energy v / 2 - t / 2
    let D : Shao.Path n → ℝ := fun v =>
      t * (Real.sqrt (Shao.energy v) - 1) ^ 2 / 2
    let H : Shao.Path n → ℝ := fun v =>
      if 0 ≤ W v then Real.exp (-t * W v) else 0
    let J : Shao.Path n → ℝ := fun v =>
      if -D v ≤ W v ∧ W v < 0 then Real.exp (-t * W v) else 0
    0 < Z ∧ IsProbabilityMeasure etaT ∧ IsProbabilityMeasure T ∧
      Integrable H T ∧ Integrable J T ∧
      P.real {v : Shao.Path n |
        t * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v n} =
        Z ^ n * Real.exp (-(t ^ 2 / 2)) *
          ((∫ v : Shao.Path n, H v ∂T) + (∫ v : Shao.Path n, J v ∂T)) := by
  classical
  let f : ℝ → ℝ := fun a => t * a - t ^ 2 * a ^ 2 / 2
  let Z : ℝ := ∫ a : ℝ, Real.exp (f a) ∂eta
  let etaT : Measure ℝ := eta.tilted f
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => eta)
  let T : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => etaT)
  let W : Shao.Path n → ℝ := fun v => Shao.prefixSum v n - t * Shao.energy v / 2 - t / 2
  let D : Shao.Path n → ℝ := fun v => t * (Real.sqrt (Shao.energy v) - 1) ^ 2 / 2
  let H : Shao.Path n → ℝ := fun v => if 0 ≤ W v then Real.exp (-t * W v) else 0
  let J : Shao.Path n → ℝ := fun v => if -D v ≤ W v ∧ W v < 0 then Real.exp (-t * W v) else 0
  let F : Shao.Path n → ℝ := fun v => ∑ i : Fin n, f (v i)
  let E : Set (Shao.Path n) := {v | t * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v n}
  have hfi : Integrable (fun a : ℝ => Real.exp (f a)) eta := by
    convert (boundedQuadraticTilt_density_moments eta h t (t ^ 2 / 2) hh (by positivity) hsupport).1 using 1
    funext a
    congr 1
    dsimp [f]
    ring
  have hZ : 0 < Z := integral_exp_pos hfi
  letI : IsProbabilityMeasure etaT := isProbabilityMeasure_tilted hfi
  haveI : IsProbabilityMeasure T := by dsimp [T]; infer_instance
  have hsT : ∀ᵐ a : ℝ ∂etaT, |a| ≤ h := (tilted_absolutelyContinuous eta f).ae_le hsupport
  have hWm : Measurable W :=
    ((Shao.measurable_prefixSum n).sub ((Shao.measurable_energy.const_mul t).div_const 2)).sub_const (t / 2)
  have hDm : Measurable D :=
    ((((Shao.measurable_energy.sqrt).sub_const 1).pow_const 2).const_mul t).div_const 2
  have hHm : Measurable H := (hWm.const_mul (-t)).exp.ite
    (measurableSet_le measurable_const hWm) measurable_const
  have hJm : Measurable J := (hWm.const_mul (-t)).exp.ite
    ((measurableSet_le hDm.neg hWm).inter (measurableSet_lt hWm measurable_const)) measurable_const
  have hQ (v : Shao.Path n) : 0 ≤ Shao.energy v := Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  have hDnon (v : Shao.Path n) : 0 ≤ D v := by dsimp [D]; positivity
  have hDle (v : Shao.Path n) : D v ≤ t / 2 * (Shao.energy v + 1) := by
    have hs : (Real.sqrt (Shao.energy v) - 1) ^ 2 ≤ Shao.energy v + 1 := by
      nlinarith only [Real.sq_sqrt (hQ v), Real.sqrt_nonneg (Shao.energy v)]
    have hi := mul_le_mul_of_nonneg_left hs (show 0 ≤ t / 2 by positivity)
    simpa only [div_mul_eq_mul_div] using hi
  have hH : Integrable H T := er_integrable_bound T H hHm 1 (Filter.Eventually.of_forall fun v => by
    dsimp only [H]
    split_ifs with hv
    · rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (by nlinarith only [mul_nonneg ht.le hv])
    · norm_num)
  have hJ : Integrable J T := er_integrable_bound T J hJm
      (Real.exp (t ^ 2 / 2 * ((n : ℝ) * h ^ 2 + 1))) (by
    filter_upwards [er_pi_support etaT n h hsT] with v hv
    dsimp only [J]
    split_ifs with hband
    · rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.2
      have hq := (er_energy_bound n h hh.le v hv).2
      have hd := (hDle v).trans (mul_le_mul_of_nonneg_left (show Shao.energy v + 1 ≤ (n : ℝ) * h ^ 2 + 1 by linarith only [hq])
        (show 0 ≤ t / 2 by positivity))
      have hi := mul_le_mul_of_nonneg_left (show -W v ≤ D v by linarith only [hband.1]) ht.le
      have hi2 := mul_le_mul_of_nonneg_left hd ht.le
      nlinarith only [hi, hi2]
    · simp only [abs_zero]; exact (Real.exp_pos _).le)
  have hwall (v : Shao.Path n) : v ∈ E ↔ -D v ≤ W v := by
    have heq : W v + D v = Shao.prefixSum v n - t * Real.sqrt (Shao.energy v) := by
      calc
        _ = Shao.prefixSum v n - t * Real.sqrt (Shao.energy v) +
            t / 2 * ((Real.sqrt (Shao.energy v)) ^ 2 - Shao.energy v) := by dsimp [W, D]; ring
        _ = _ := by rw [Real.sq_sqrt (hQ v)]; ring
    change t * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v n ↔ _
    constructor <;> intro hv <;> linarith only [heq, hv]
  have hHJ (v : Shao.Path n) : H v + J v = E.indicator (fun v => Real.exp (-t * W v)) v := by
    by_cases h0 : 0 ≤ W v
    · have hneg : ¬ W v < 0 := not_lt_of_ge h0
      have hmem : v ∈ E := (hwall v).2 (by linarith only [hDnon v, h0])
      simp [H, J, h0, hneg, Set.indicator_of_mem hmem]
    · have hneg : W v < 0 := lt_of_not_ge h0
      by_cases hd : -D v ≤ W v
      · have hmem : v ∈ E := (hwall v).2 hd
        simp [H, J, h0, hneg, hd, Set.indicator_of_mem hmem]
      · have hmem : v ∉ E := fun he => hd ((hwall v).1 he)
        simp [H, J, h0, hd, Set.indicator_of_notMem hmem]
  have hT : T = P.tilted F := er_pi_tilted eta n f (by dsimp [f]; fun_prop) hfi
  have hnormalizer : (∫ v : Shao.Path n, Real.exp (F v) ∂P) = Z ^ n := by
    dsimp [F, P]
    simp_rw [Real.exp_sum]
    simpa only [Fintype.card_fin] using
      (integral_fintype_prod_eq_pow (ι := Fin n) (μ := eta) (fun a : ℝ => Real.exp (f a)))
  have hF (v : Shao.Path n) : F v = t * W v + t ^ 2 / 2 := by
    have hs : F v = t * Shao.prefixSum v n - t ^ 2 * Shao.energy v / 2 := by
      simp only [F, f, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum,
        Shao.prefixSum_length, Shao.energy]
    rw [hs]
    dsimp [W]
    ring
  have hEm : MeasurableSet E := measurableSet_le
    (Shao.measurable_energy.sqrt.const_mul t) (Shao.measurable_prefixSum n)
  have hmain : (∫ v : Shao.Path n, H v ∂T) + (∫ v : Shao.Path n, J v ∂T) =
      (Real.exp (t ^ 2 / 2) / Z ^ n) * P.real E := by
    rw [← integral_add hH hJ, hT, integral_tilted, hnormalizer]
    simp only [smul_eq_mul]
    have hpoint (v : Shao.Path n) :
        Real.exp (F v) / Z ^ n * (H v + J v) =
          (Real.exp (t ^ 2 / 2) / Z ^ n) * E.indicator (fun _ => (1 : ℝ)) v := by
      rw [hHJ]
      by_cases hv : v ∈ E
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
        have he : Real.exp (F v) * Real.exp (-t * W v) = Real.exp (t ^ 2 / 2) := by
          rw [← Real.exp_add, hF]
          congr 1
          ring
        calc
          _ = (Real.exp (F v) * Real.exp (-t * W v)) / Z ^ n := by ring
          _ = _ := by rw [he]; ring
      · simp [Set.indicator_of_notMem hv]
    simp_rw [hpoint]
    rw [integral_const_mul]
    have hI : (∫ v : Shao.Path n, E.indicator (fun _ => (1 : ℝ)) v ∂P) = P.real E := integral_indicator_one hEm
    rw [hI]
  refine ⟨hZ, inferInstance, inferInstance, hH, hJ, ?_⟩
  change P.real E = Z ^ n * Real.exp (-(t ^ 2 / 2)) *
    ((∫ v : Shao.Path n, H v ∂T) + (∫ v : Shao.Path n, J v ∂T))
  rw [hmain]
  have he : Real.exp (-(t ^ 2 / 2)) * Real.exp (t ^ 2 / 2) = 1 := by rw [← Real.exp_add]; simp
  calc
    P.real E = P.real E * (Real.exp (-(t ^ 2 / 2)) * Real.exp (t ^ 2 / 2)) := by rw [he, mul_one]
    _ = _ := by field_simp [hZ.ne'] <;> ring

private theorem er_abs_integral
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

private theorem er_normalizer_expansion
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (h t : ℝ) (hh : 0 < h) (ht : 0 < t)
    (hsupport : ∀ᵐ a : ℝ ∂eta, |a| ≤ h) (hthin : t * h ≤ 1 / 800) :
    |(∫ a : ℝ, Real.exp (t * a - t ^ 2 * a ^ 2 / 2) ∂eta) - 1 -
      t * (∫ a : ℝ, a ∂eta)| ≤
        2 * t ^ 3 * (∫ a : ℝ, |a| ^ 3 ∂eta) := by
  obtain ⟨hW, _, _, _, _, _, _, _, _, _, _, _, _, _, hp, _⟩ :=
    boundedQuadraticTilt_density_moments eta h t (t ^ 2 / 2) hh (by positivity) hsupport
  have hi : Integrable (fun a : ℝ => Real.exp (t * a - t ^ 2 * a ^ 2 / 2)) eta := by
    convert hW using 1
    funext a
    congr 1
    ring
  have h1 : Integrable (fun a : ℝ => a) eta := by simpa only [pow_one] using (hp 1).1
  have h3 : Integrable (fun a : ℝ => |a| ^ 3) eta :=
    (hp 3).2.2.1
  have hF := (hi.sub (integrable_const (1 : ℝ))).sub (h1.const_mul t)
  have hb := er_abs_integral eta _ _ hF (h3.const_mul (2 * t ^ 3)) (by
    filter_upwards [hsupport] with a ha
    have hta : |t * a| ≤ 1 / 800 := by
      rw [abs_mul, abs_of_pos ht]
      exact (mul_le_mul_of_nonneg_left ha ht.le).trans hthin
    have hu := (er_quadratic_exp_taylor (t * a) hta).1
    have he : t * a - (t * a) ^ 2 / 2 = t * a - t ^ 2 * a ^ 2 / 2 := by ring
    rw [he, abs_mul, abs_of_pos ht, mul_pow] at hu
    convert hu using 1 <;> ring)
  change |∫ a : ℝ, Real.exp (t * a - t ^ 2 * a ^ 2 / 2) - 1 - t * a ∂eta| ≤
    ∫ a : ℝ, (2 * t ^ 3) * |a| ^ 3 ∂eta at hb
  rw [integral_sub (f := fun a : ℝ => Real.exp (t * a - t ^ 2 * a ^ 2 / 2) - 1)
      (g := fun a : ℝ => t * a) (hi.sub (integrable_const (1 : ℝ))) (h1.const_mul t),
    integral_sub hi (integrable_const (1 : ℝ)), integral_const_mul, integral_const_mul] at hb
  simpa only [integral_const, probReal_univ, one_smul] using hb

private theorem er_normalizer_power_budget
    (n : ℕ) (hn : 1 ≤ n) (Z z : ℝ)
    (hZ : 0 < Z) (hz : 0 ≤ z) (hzsmall : z ≤ 1 / 1000)
    (hbudget : (n : ℝ) * |Z - 1| ≤ 3 * z) :
    Z ^ n ≤ 2 ∧ |Z ^ n - 1| ≤ 8 * z := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδ : |Z - 1| ≤ 3 * z := by
    have hm := mul_le_mul_of_nonneg_right hN (abs_nonneg (Z - 1))
    nlinarith only [hm, hbudget]
  have hZ34 : (3 / 4 : ℝ) ≤ Z := by
    have h := (abs_le.1 hδ).1
    linarith only [h, hzsmall]
  have hlower : -(4 / 3 : ℝ) * |Z - 1| ≤ Real.log Z := by
    by_cases hl : 0 ≤ Real.log Z
    · nlinarith only [hl, abs_nonneg (Z - 1)]
    · have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hZ) hZ.le
      have he : Z * (1 - Z⁻¹) = Z - 1 := by field_simp
      rw [he] at h
      have hh := mul_le_mul_of_nonpos_right hZ34 (le_of_not_ge hl)
      have hd := neg_abs_le (Z - 1)
      nlinarith only [h, hh, hd]
  have hupper : Real.log Z ≤ (4 / 3 : ℝ) * |Z - 1| := by
    have h := (Real.log_le_sub_one_of_pos hZ).trans (le_abs_self (Z - 1))
    nlinarith only [h, abs_nonneg (Z - 1)]
  have hlog : |Real.log Z| ≤ (4 / 3 : ℝ) * |Z - 1| := abs_le.2 ⟨by linarith only [hlower], hupper⟩
  have hE : |(n : ℝ) * Real.log Z| ≤ 4 * z := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n)
    nlinarith only [h, hbudget]
  have hpow : Z ^ n = Real.exp ((n : ℝ) * Real.log Z) := by rw [Real.exp_nat_mul, Real.exp_log hZ]
  rw [hpow]
  constructor
  · apply (Real.exp_le_exp.2 ((le_abs_self _).trans hE)).trans
    have h := Real.exp_bound_div_one_sub_of_interval
      (show 0 ≤ 4 * z by positivity) (show 4 * z < 1 by linarith)
    apply h.trans
    apply (div_le_iff₀ (show 0 < 1 - 4 * z by linarith)).2
    linarith only [hzsmall]
  · exact (Real.abs_exp_sub_one_le (hE.trans (by linarith))).trans (by linarith only [hE])

private theorem er_linear_weight_taylor
    (t a : ℝ) (ht : 0 < t) (hta : |t * a| ≤ 1 / 800) :
    let g : ℝ := a - t * a ^ 2 / 2
    let b : ℝ := Real.exp (t * a - t ^ 2 * a ^ 2 / 2)
    |g * b - a - t * a ^ 2 / 2| ≤ 4 * t ^ 2 * |a| ^ 3 ∧
      |g ^ 2 * b - a ^ 2| ≤ 4 * t * |a| ^ 3 := by
  let g : ℝ := a - t * a ^ 2 / 2
  let b : ℝ := Real.exp (t * a - t ^ 2 * a ^ 2 / 2)
  obtain ⟨_, h1, h2⟩ := er_quadratic_exp_taylor (t * a) hta
  have he : t * a - (t * a) ^ 2 / 2 = t * a - t ^ 2 * a ^ 2 / 2 := by ring
  change |(t * a - (t * a) ^ 2 / 2) * Real.exp (t * a - (t * a) ^ 2 / 2) -
    t * a - (t * a) ^ 2 / 2| ≤ 4 * |t * a| ^ 3 at h1
  change |(t * a - (t * a) ^ 2 / 2) ^ 2 * Real.exp (t * a - (t * a) ^ 2 / 2) -
    (t * a) ^ 2| ≤ 4 * |t * a| ^ 3 at h2
  rw [he] at h1 h2
  simp only [abs_mul, abs_of_pos ht, mul_pow] at h1 h2
  change |(t * a - t ^ 2 * a ^ 2 / 2) * b - t * a - t ^ 2 * a ^ 2 / 2| ≤
    4 * (t ^ 3 * |a| ^ 3) at h1
  change |(t * a - t ^ 2 * a ^ 2 / 2) ^ 2 * b - t ^ 2 * a ^ 2| ≤
    4 * (t ^ 3 * |a| ^ 3) at h2
  constructor
  · have hi : (t * a - t ^ 2 * a ^ 2 / 2) * b - t * a - t ^ 2 * a ^ 2 / 2 =
        t * (g * b - a - t * a ^ 2 / 2) := by dsimp [g]; ring
    rw [hi, abs_mul, abs_of_pos ht] at h1
    apply (mul_le_mul_iff_right₀ ht).1
    exact h1.trans_eq (by ring)
  · have hi : (t * a - t ^ 2 * a ^ 2 / 2) ^ 2 * b - t ^ 2 * a ^ 2 =
        t ^ 2 * (g ^ 2 * b - a ^ 2) := by dsimp [g]; ring
    rw [hi, abs_mul, abs_of_pos (sq_pos_of_pos ht)] at h2
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos ht)).1
    exact h2.trans_eq (by ring)

private theorem er_tilted_integral_normalizer
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hfi : Integrable (fun a => Real.exp (f a)) ν) (g : Ω → ℝ) :
    (∫ a, Real.exp (f a) ∂ν) * (∫ a, g a ∂ν.tilted f) =
      ∫ a, Real.exp (f a) * g a ∂ν := by
  let Z : ℝ := ∫ a, Real.exp (f a) ∂ν
  have hZ : 0 < Z := integral_exp_pos hfi
  rw [integral_tilted]
  simp only [smul_eq_mul]
  have he (a : Ω) : (Real.exp (f a) / Z) * g a = (Real.exp (f a) * g a) / Z := by ring
  change Z * (∫ a, (Real.exp (f a) / Z) * g a ∂ν) = _
  simp_rw [he]
  rw [integral_div]
  field_simp [hZ.ne']

private theorem er_tilt_linear_expansions
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (h t : ℝ) (hh : 0 < h) (ht : 0 < t)
    (hsupport : ∀ᵐ a : ℝ ∂eta, |a| ≤ h) (hthin : t * h ≤ 1 / 800) :
    let f : ℝ → ℝ := fun a => t * a - t ^ 2 * a ^ 2 / 2
    let g : ℝ → ℝ := fun a => a - t * a ^ 2 / 2
    let Z : ℝ := ∫ a : ℝ, Real.exp (f a) ∂eta
    let rho : Measure ℝ := eta.tilted f
    let mu : ℝ := ∫ a : ℝ, a ∂eta
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂eta
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂eta
    0 < Z ∧ IsProbabilityMeasure rho ∧
      Integrable g rho ∧ Integrable (fun a : ℝ => g a ^ 2) rho ∧
      |Z * (∫ a : ℝ, g a ∂rho) - mu - t * m2 / 2| ≤ 4 * t ^ 2 * m3 ∧
      |Z * (∫ a : ℝ, g a ^ 2 ∂rho) - m2| ≤ 4 * t * m3 := by
  let f : ℝ → ℝ := fun a => t * a - t ^ 2 * a ^ 2 / 2
  let g : ℝ → ℝ := fun a => a - t * a ^ 2 / 2
  let Z : ℝ := ∫ a : ℝ, Real.exp (f a) ∂eta
  let rho : Measure ℝ := eta.tilted f
  obtain ⟨hW, _, _, _, _, _, _, _, _, _, _, hL1, _, _, hp, _⟩ :=
    boundedQuadraticTilt_density_moments eta h t (t ^ 2 / 2) hh (by positivity) hsupport
  have hf : (fun a : ℝ => t * a - (t ^ 2 / 2) * a ^ 2) = f := by funext a; dsimp [f]; ring
  rw [hf] at hL1
  have hfi : Integrable (fun a : ℝ => Real.exp (f a)) eta := by
    convert hW using 1
    funext a
    congr 1
    dsimp [f]
    ring
  have hZ : 0 < Z := integral_exp_pos hfi
  letI : IsProbabilityMeasure rho := isProbabilityMeasure_tilted hfi
  have h1 : Integrable (fun a : ℝ => a) eta := by simpa only [pow_one] using (hp 1).1
  have h2 : Integrable (fun a : ℝ => a ^ 2) eta := (hp 2).1
  have h3 : Integrable (fun a : ℝ => |a| ^ 3) eta := (hp 3).2.2.1
  have hgm : Measurable g := by dsimp [g]; fun_prop
  have hgb : ∀ᵐ a : ℝ ∂eta, |g a| ≤ 2 * h := by
    filter_upwards [hsupport] with a ha
    have hh2 : a ^ 2 ≤ h * |a| := by
      have hi := mul_le_mul_of_nonneg_right ha (abs_nonneg a)
      nlinarith only [hi, sq_abs a]
    have hab := abs_sub a (t * a ^ 2 / 2)
    rw [abs_div, abs_mul, abs_of_pos ht, abs_of_nonneg (sq_nonneg a)] at hab
    norm_num at hab
    dsimp only [g]
    nlinarith [mul_le_mul_of_nonneg_left hh2 ht.le,
      mul_le_mul_of_nonneg_right hthin (abs_nonneg a)]
  have hgi : Integrable g eta := er_integrable_bound eta g hgm (2 * h) hgb
  have hg2 : Integrable (fun a : ℝ => g a ^ 2) eta :=
    er_integrable_bound eta _ (hgm.pow_const 2) ((2 * h) ^ 2) (by
      filter_upwards [hgb] with a ha
      rw [abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ha 2)
  have hbd : ∀ᵐ a : ℝ ∂eta, ‖Real.exp (f a)‖ ≤ Real.exp (t * h) := by
    filter_upwards [hsupport] with a ha
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    dsimp [f]
    have hh := mul_le_mul_of_nonneg_left ((le_abs_self a).trans ha) ht.le
    nlinarith only [hh, mul_nonneg (sq_nonneg t) (sq_nonneg a)]
  have hig : Integrable (fun a : ℝ => Real.exp (f a) * g a) eta :=
    hgi.bdd_mul (by dsimp [f]; fun_prop) hbd
  have hig2 : Integrable (fun a : ℝ => Real.exp (f a) * g a ^ 2) eta :=
    hg2.bdd_mul (by dsimp [f]; fun_prop) hbd
  have hρg : Integrable g rho := by
    apply (hL1 g).2
    exact hgi
  have hρg2 : Integrable (fun a : ℝ => g a ^ 2) rho := by
    apply (hL1 (fun a : ℝ => g a ^ 2)).2
    exact hg2
  have hb1 := er_abs_integral eta _ _
    ((hig.sub h1).sub (h2.const_mul (t / 2))) (h3.const_mul (4 * t ^ 2)) (by
      filter_upwards [hsupport] with a ha
      have hta : |t * a| ≤ 1 / 800 := by
        rw [abs_mul, abs_of_pos ht]
        exact (mul_le_mul_of_nonneg_left ha ht.le).trans hthin
      have hu := (er_linear_weight_taylor t a ht hta).1
      convert hu using 1 <;> dsimp [f, g] <;> ring)
  have hb2 := er_abs_integral eta _ _ (hig2.sub h2) (h3.const_mul (4 * t)) (by
    filter_upwards [hsupport] with a ha
    have hta : |t * a| ≤ 1 / 800 := by
      rw [abs_mul, abs_of_pos ht]
      exact (mul_le_mul_of_nonneg_left ha ht.le).trans hthin
    have hu := (er_linear_weight_taylor t a ht hta).2
    convert hu using 1 <;> dsimp [f, g] <;> ring)
  have he1 := er_tilted_integral_normalizer eta f hfi g
  have he2 := er_tilted_integral_normalizer eta f hfi (fun a => g a ^ 2)
  change |∫ a : ℝ, Real.exp (f a) * g a - a - (t / 2) * a ^ 2 ∂eta| ≤
    ∫ a : ℝ, (4 * t ^ 2) * |a| ^ 3 ∂eta at hb1
  rw [integral_sub (f := fun a : ℝ => Real.exp (f a) * g a - a)
      (g := fun a : ℝ => (t / 2) * a ^ 2) (hig.sub h1) (h2.const_mul (t / 2)),
    integral_sub hig h1, integral_const_mul, integral_const_mul, ← he1] at hb1
  change |∫ a : ℝ, Real.exp (f a) * g a ^ 2 - a ^ 2 ∂eta| ≤
    ∫ a : ℝ, (4 * t) * |a| ^ 3 ∂eta at hb2
  rw [integral_sub hig2 h2, integral_const_mul, ← he2] at hb2
  refine ⟨hZ, inferInstance, hρg, hρg2, ?_, hb2⟩
  change |Z * (∫ a : ℝ, g a ∂rho) - (∫ a : ℝ, a ∂eta) -
      t * (∫ a : ℝ, a ^ 2 ∂eta) / 2| ≤ 4 * t ^ 2 * (∫ a : ℝ, |a| ^ 3 ∂eta)
  have he : t * (∫ a : ℝ, a ^ 2 ∂eta) / 2 = (t / 2) * (∫ a : ℝ, a ^ 2 ∂eta) := by ring
  rw [he]
  exact hb1

private theorem er_moment_lyapunov
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν)
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) :
    (∫ a : ℝ, a ^ 2 ∂ν) ^ 3 ≤ (∫ a : ℝ, |a| ^ 3 ∂ν) ^ 2 := by
  have hm30 : 0 ≤ ∫ a : ℝ, |a| ^ 3 ∂ν := integral_nonneg fun a => pow_nonneg (abs_nonneg a) 3
  by_cases hm3 : 0 < ∫ a : ℝ, |a| ^ 3 ∂ν
  · have h := mul_le_mul_of_nonneg_left
      (measureReal_le_one (μ := ν) (s := {a : ℝ | a ≠ 0}))
      (sq_nonneg (∫ a : ℝ, |a| ^ 3 ∂ν))
    have hs : (∫ a : ℝ, |a| ^ 3 ∂ν) ^ 2 * ν.real {a : ℝ | a ≠ 0} ≤
        (∫ a : ℝ, |a| ^ 3 ∂ν) ^ 2 := by simpa only [mul_one] using h
    exact (er_nonzero_mass_moment ν h2 h3 hm3).trans hs
  · have hz : (∫ a : ℝ, |a| ^ 3 ∂ν) = 0 := le_antisymm (le_of_not_gt hm3) hm30
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun a : ℝ => pow_nonneg (abs_nonneg a) 3) h3).1 hz
    have hm2 : (∫ a : ℝ, a ^ 2 ∂ν) = 0 := by
      calc
        _ = ∫ _a : ℝ, (0 : ℝ) ∂ν := integral_congr_ae (by
          filter_upwards [hae] with a ha
          have ha0 : |a| = 0 := (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).1 ha
          simp [abs_eq_zero.1 ha0])
        _ = 0 := by simp
    simp [hz, hm2]

private theorem er_linear_moment_arithmetic
    (N t z q beta u Z M R : ℝ)
    (hN : 1 ≤ N) (ht : 0 < t) (hz : 0 ≤ z) (hzsmall : z ≤ 1 / 1000)
    (hbeta : 0 ≤ beta)
    (hu : (1 + t) * |u| ≤ z)
    (hq : (1 + t) ^ 2 * |q - 1| ≤ z)
    (hb : (1 + t) ^ 3 * beta ≤ z)
    (hLy : q ^ 3 ≤ N * beta ^ 2)
    (hδ : N * |Z - 1| ≤ 3 * z)
    (hM : |Z * M - u - t * q / 2| ≤ 4 * t ^ 2 * beta)
    (hR : |Z * R - q| ≤ 4 * t * beta) :
    (1 / 2 : ℝ) ≤ Z ∧
      |M - t / 2| ≤ 16 * z / (1 + t) ∧
      |R - 1| ≤ 16 * z / (1 + t) ^ 2 ∧
      M ^ 2 / N ≤ 2 * z / (1 + t) ^ 2 ∧
      |R - M ^ 2 / N - 1| ≤ 32 * z / (1 + t) ^ 2 ∧
      (1 / 2 : ℝ) ≤ R - M ^ 2 / N ∧ R - M ^ 2 / N ≤ 2 := by
  let p : ℝ := 1 + t
  have hp : 1 ≤ p := by dsimp [p]; linarith only [ht]
  have hp0 : 0 < p := by linarith only [hp]
  have htP : t ≤ p := by dsimp [p]; linarith
  have hp2 : 1 ≤ p ^ 2 := by nlinarith only [hp]
  have hp6 : p ^ 2 ≤ p ^ 6 := by
    have h4 : 1 ≤ p ^ 4 := by simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hp 4
    nlinarith only [mul_le_mul_of_nonneg_left h4 (sq_nonneg p)]
  have hN0 : 0 < N := by linarith only [hN]
  have hz2 : z ^ 2 ≤ 1 / 6 := by nlinarith only [hzsmall, hz, sq_nonneg (z - 1 / 1000)]
  have hqabs : |q - 1| ≤ z := by
    have h := mul_le_mul_of_nonneg_right hp2 (abs_nonneg (q - 1))
    nlinarith only [h, hq]
  have hq9 : (9 / 10 : ℝ) ≤ q := by
    have h := (abs_le.1 hqabs).1
    linarith only [h, hzsmall]
  have hq3 : (1 / 2 : ℝ) ≤ q ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 10) hq9 3
    norm_num at h
    linarith only [h]
  have hcount : (1 : ℝ) ≤ 2 * N * beta ^ 2 := by linarith only [hLy, hq3]
  have hb2 : p ^ 6 * beta ^ 2 ≤ z ^ 2 := by
    have h := pow_le_pow_left₀ (mul_nonneg (pow_nonneg hp0.le 3) hbeta) hb 2
    nlinarith only [h]
  have hNinv : p ^ 6 ≤ 2 * N * z ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hcount (pow_nonneg hp0.le 6)
    have h2 := mul_le_mul_of_nonneg_left hb2 (show 0 ≤ 2 * N by positivity)
    nlinarith only [h1, h2]
  have hN3 : 3 * p ^ 2 ≤ N := by
    have h := mul_le_mul_of_nonneg_left hz2 hN0.le
    nlinarith only [h, hNinv, hp6]
  have hδp : p ^ 2 * |Z - 1| ≤ z := by
    have h := mul_le_mul_of_nonneg_right hN3 (abs_nonneg (Z - 1))
    nlinarith only [h, hδ]
  have hδabs : |Z - 1| ≤ z := by
    have h := mul_le_mul_of_nonneg_right hp2 (abs_nonneg (Z - 1))
    nlinarith only [h, hδp]
  have hZ : (1 / 2 : ℝ) ≤ Z := by
    have h := (abs_le.1 hδabs).1
    linarith only [h, hzsmall]
  have hZ0 : 0 ≤ Z := by linarith only [hZ]
  have hpT2 : p * t ^ 2 ≤ p ^ 3 := by
    have h := pow_le_pow_left₀ ht.le htP 2
    nlinarith only [mul_le_mul_of_nonneg_left h hp0.le]
  have htp2 : t * p ^ 2 ≤ p ^ 3 := by
    nlinarith only [mul_le_mul_of_nonneg_right htP (sq_nonneg p)]
  have hmb : p * |Z * M - u - t * q / 2| ≤ 4 * z := by
    have h1 := mul_le_mul_of_nonneg_left hM hp0.le
    have h2 := mul_le_mul_of_nonneg_right hpT2 hbeta
    nlinarith only [h1, h2, hb]
  have hqb : p * t * |q - 1| ≤ z := by
    have h := mul_le_mul_of_nonneg_right htP (mul_nonneg hp0.le (abs_nonneg (q - 1)))
    nlinarith only [h, hq]
  have hdb : p * t * |Z - 1| ≤ z := by
    have h := mul_le_mul_of_nonneg_right htP (mul_nonneg hp0.le (abs_nonneg (Z - 1)))
    nlinarith only [h, hδp]
  let A : ℝ := M - t / 2
  have hAeq : Z * A = (Z * M - u - t * q / 2) + u +
      (t / 2) * (q - 1) - (t / 2) * (Z - 1) := by dsimp [A]; ring
  have hAabs : |Z * A| ≤ |Z * M - u - t * q / 2| + |u| +
      (t / 2) * |q - 1| + (t / 2) * |Z - 1| := by
    rw [hAeq]
    calc
      _ ≤ |(Z * M - u - t * q / 2) + u + (t / 2) * (q - 1)| + |(t / 2) * (Z - 1)| := abs_sub _ _
      _ ≤ |(Z * M - u - t * q / 2) + u| + |(t / 2) * (q - 1)| + |(t / 2) * (Z - 1)| := by
        have h := abs_add_le ((Z * M - u - t * q / 2) + u) ((t / 2) * (q - 1))
        linarith only [h]
      _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ t / 2 by positivity)]
        have h := abs_add_le (Z * M - u - t * q / 2) u
        linarith only [h]
  have hApaid : p * |A| ≤ 16 * z := by
    have h1 := mul_le_mul_of_nonneg_left hAabs hp0.le
    rw [abs_mul, abs_of_nonneg hZ0] at h1
    have h2 := mul_le_mul_of_nonneg_right hZ (mul_nonneg hp0.le (abs_nonneg A))
    nlinarith only [h1, h2, hmb, hu, hqb, hdb, hz]
  have hRabs : |Z * (R - 1)| ≤ |Z * R - q| + |q - 1| + |Z - 1| := by
    have he : Z * (R - 1) = ((Z * R - q) + (q - 1)) - (Z - 1) := by ring
    rw [he]
    exact (abs_sub _ _).trans (by have h := abs_add_le (Z * R - q) (q - 1); linarith only [h])
  have hRpaid : p ^ 2 * |R - 1| ≤ 16 * z := by
    have h1 := mul_le_mul_of_nonneg_left hRabs (sq_nonneg p)
    rw [abs_mul, abs_of_nonneg hZ0] at h1
    have h2 := mul_le_mul_of_nonneg_left hR (sq_nonneg p)
    have h3 := mul_le_mul_of_nonneg_right htp2 hbeta
    have h4 := mul_le_mul_of_nonneg_right hZ (mul_nonneg (sq_nonneg p) (abs_nonneg (R - 1)))
    nlinarith only [h1, h2, h3, h4, hq, hb, hδp, hz]
  have hAsq : p ^ 2 * A ^ 2 ≤ 256 * z ^ 2 := by
    have h := pow_le_pow_left₀ (mul_nonneg hp0.le (abs_nonneg A)) hApaid 2
    rw [mul_pow, sq_abs] at h
    nlinarith only [h]
  have ht2p2 : t ^ 2 * p ^ 2 ≤ p ^ 6 := by
    have ht2 := pow_le_pow_left₀ ht.le htP 2
    have hp4 : p ^ 4 ≤ p ^ 6 := by
      nlinarith only [mul_le_mul_of_nonneg_left hp2 (pow_nonneg hp0.le 4)]
    have h := mul_le_mul_of_nonneg_right ht2 (sq_nonneg p)
    nlinarith only [h, hp4]
  have hMsq : p ^ 2 * M ^ 2 ≤ 2 * N * z := by
    have hyoung : M ^ 2 ≤ 2 * A ^ 2 + t ^ 2 / 2 := by dsimp [A]; nlinarith only [sq_nonneg (M - t)]
    have h1 := mul_le_mul_of_nonneg_left hyoung (sq_nonneg p)
    have h2 := mul_le_mul_of_nonneg_right hN (sq_nonneg z)
    have h3 : 513 * z ^ 2 ≤ 2 * z := by nlinarith only [hzsmall, hz]
    have h4 := mul_le_mul_of_nonneg_left h3 hN0.le
    nlinarith only [h1, hAsq, ht2p2, hNinv, h2, h4]
  have hMdiv : M ^ 2 / N ≤ 2 * z / p ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hp0)).2
    have he : M ^ 2 / N * p ^ 2 = (p ^ 2 * M ^ 2) / N := by ring
    rw [he]
    exact (div_le_iff₀ hN0).2 (by nlinarith only [hMsq])
  have hV : |R - M ^ 2 / N - 1| ≤ 32 * z / p ^ 2 := by
    have htri : |R - M ^ 2 / N - 1| ≤ |R - 1| + M ^ 2 / N := by
      have h := abs_sub (R - 1) (M ^ 2 / N)
      rw [abs_of_nonneg (div_nonneg (sq_nonneg M) hN0.le)] at h
      convert h using 1 <;> ring
    have hrdiv : |R - 1| ≤ 16 * z / p ^ 2 := (le_div_iff₀ (sq_pos_of_pos hp0)).2 (by nlinarith only [hRpaid])
    have hrel : 16 * z / p ^ 2 + 2 * z / p ^ 2 ≤ 32 * z / p ^ 2 := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (sq_nonneg p)
      linarith only [hz]
    exact (htri.trans (add_le_add hrdiv hMdiv)).trans hrel
  have hVsmall : 32 * z / p ^ 2 ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hp0)).2
    nlinarith only [hp2, hzsmall]
  refine ⟨hZ, (le_div_iff₀ hp0).2 (by nlinarith only [hApaid]),
    (le_div_iff₀ (sq_pos_of_pos hp0)).2 (by nlinarith only [hRpaid]), hMdiv, hV, ?_, ?_⟩
  · have h := (abs_le.1 (hV.trans hVsmall)).1
    linarith only [h]
  · have h := (abs_le.1 (hV.trans hVsmall)).2
    linarith only [h]

private theorem er_bounded_power (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hh : 0 ≤ h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) (k : ℕ) :
    Integrable (fun a : ℝ => a ^ k) ν ∧
      Integrable (fun a : ℝ => |a| ^ k) ν ∧
      (∫ a : ℝ, |a| ^ k ∂ν) ≤ h ^ k := by
  have hp : ∀ᵐ a : ℝ ∂ν, |a| ^ k ≤ h ^ k := by
    filter_upwards [hs] with a ha
    exact pow_le_pow_left₀ (abs_nonneg a) ha k
  have hi : Integrable (fun a : ℝ => |a| ^ k) ν :=
    er_integrable_bound ν _ (by fun_prop) _ (by
      filter_upwards [hp] with a ha
      simpa only [abs_of_nonneg (pow_nonneg (abs_nonneg a) k)] using ha)
  refine ⟨?_, hi, ?_⟩
  · exact er_integrable_bound ν _ (by fun_prop) _ (by simpa only [abs_pow] using hp)
  · simpa only [integral_const, probReal_univ, one_smul] using
      integral_mono_ae hi (integrable_const (h ^ k)) hp

private theorem er_abs_first_second_le_third
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

private theorem er_centered_third
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hh : 0 ≤ h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    Integrable (fun a : ℝ => |a - ∫ z : ℝ, z ∂ν| ^ 3) ν ∧
      (∫ a : ℝ, |a - ∫ z : ℝ, z ∂ν| ^ 3 ∂ν) ≤
        8 * (∫ a : ℝ, |a| ^ 3 ∂ν) := by
  let m : ℝ := ∫ a : ℝ, a ∂ν
  have hp := er_bounded_power ν h hh hs
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
    have hl := er_abs_first_second_le_third ν (hp 2).1 (hp 3).2.1
    have he : |m| ^ 3 = |m| * m ^ 2 := by rw [pow_succ, sq_abs]; ring
    rw [he]
    exact hp1.trans hl
  have hc : Integrable (fun a : ℝ => |a - m| ^ 3) ν :=
    er_integrable_bound ν _ (by fun_prop) ((h + |m|) ^ 3) (by
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

private theorem er_g_abs (h t a : ℝ) (hh : 0 ≤ h) (ht : 0 ≤ t)
    (hthin : t * h ≤ 1 / 800) (ha : |a| ≤ h) :
    |a - t * a ^ 2 / 2| ≤ 2 * |a| := by
  have hta := mul_le_mul_of_nonneg_left ha ht
  have hp := mul_le_mul_of_nonneg_right (hta.trans hthin) (abs_nonneg a)
  have hi := abs_sub a (t * a ^ 2 / 2)
  rw [abs_of_nonneg (by positivity : 0 ≤ t * a ^ 2 / 2)] at hi
  rw [← sq_abs a] at hi ⊢
  nlinarith only [hi, hp, abs_nonneg a]

private theorem er_g_centered_third
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
    exact (er_g_abs h t a hh.le ht.le hthin ha).trans (by linarith)
  have hsζ : ∀ᵐ z : ℝ ∂ζ, |z| ≤ 2 * h := by
    exact (ae_map_iff hgm.aemeasurable
      (measurableSet_le continuous_abs.measurable measurable_const)).2 hgb
  have hLp : MemLp g 2 η := by
    apply (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2
    apply er_integrable_bound η _ (hgm.pow_const 2) ((2 * h) ^ 2)
    filter_upwards [hgb] with a ha
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (g a), abs_nonneg (g a)]
  obtain ⟨hcζ, hbζ⟩ := er_centered_third ζ (2 * h) (by positivity) hsζ
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
      er_integrable_bound η _ (by dsimp [g]; fun_prop) ((2 * h) ^ 3) (by
        filter_upwards [hgb] with a ha
        rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
        exact pow_le_pow_left₀ (abs_nonneg _) ha 3)
    have hi := integral_mono_ae hi3 ((er_bounded_power η h hh.le hsupport 3).2.1.const_mul 8) (by
      filter_upwards [hsupport] with a ha
      have hu := pow_le_pow_left₀ (abs_nonneg (g a)) (er_g_abs h t a hh.le ht.le hthin ha) 3
      nlinarith only [hu])
    rw [integral_const_mul] at hi
    exact hi
  rw [hcube] at hbζ
  exact ⟨hLp, hc, by linarith only [hbζ, hraw]⟩

private theorem er_tilt_small_moment_budget
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
    let f : ℝ → ℝ := fun a => t * a - t ^ 2 * a ^ 2 / 2
    let g : ℝ → ℝ := fun a => a - t * a ^ 2 / 2
    let Z : ℝ := ∫ a : ℝ, Real.exp (f a) ∂eta
    let etaT : Measure ℝ := eta.tilted f
    let A : ℝ := (n : ℝ) * (∫ a : ℝ, g a ∂etaT) - t / 2
    let V : ℝ := (n : ℝ) * variance g etaT
    0 < Z ∧ IsProbabilityMeasure etaT ∧ MemLp g 2 etaT ∧
      Integrable (fun a : ℝ => |g a - ∫ b : ℝ, g b ∂etaT| ^ 3) etaT ∧
      Z ^ n ≤ 2 ∧ |Z ^ n - 1| ≤ 8 * z ∧
      |A| ≤ 16 * z / (1 + t) ∧ |V - 1| ≤ 32 * z / (1 + t) ^ 2 ∧
      (9 / 10 : ℝ) ≤ V ∧ V ≤ 2 ∧
      (n : ℝ) * (∫ a : ℝ, |g a - ∫ b : ℝ, g b ∂etaT| ^ 3 ∂etaT) ≤ 128 * beta := by
  let N : ℝ := n
  let p : ℝ := 1 + t
  let mu : ℝ := ∫ a : ℝ, a ∂eta
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂eta
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂eta
  let q : ℝ := N * m2
  let beta : ℝ := N * m3
  let z : ℝ := p * (N * |mu|) + p ^ 2 * |q - 1| + p ^ 3 * beta
  let f : ℝ → ℝ := fun a => t * a - t ^ 2 * a ^ 2 / 2
  let g : ℝ → ℝ := fun a => a - t * a ^ 2 / 2
  let Z : ℝ := ∫ a : ℝ, Real.exp (f a) ∂eta
  let rho : Measure ℝ := eta.tilted f
  let M : ℝ := N * (∫ a : ℝ, g a ∂rho)
  let R : ℝ := N * (∫ a : ℝ, g a ^ 2 ∂rho)
  let V : ℝ := N * variance g rho
  have hN : 1 ≤ N := by dsimp [N]; exact_mod_cast hn
  have hN0 : 0 < N := by linarith only [hN]
  have hp : 1 ≤ p := by dsimp [p]; linarith only [ht]
  have hp0 : 0 < p := by linarith only [hp]
  have htP : t ≤ p := by dsimp [p]; linarith
  have hm30 : 0 ≤ m3 := integral_nonneg fun a => pow_nonneg (abs_nonneg a) 3
  have hb0 : 0 ≤ beta := mul_nonneg hN0.le hm30
  have hz0 : 0 ≤ z := by dsimp only [z]; positivity
  have hzs : z ≤ 1 / 1000 := hsmall
  have hu : p * (N * |mu|) ≤ z := by
    dsimp only [z]
    have h1 : 0 ≤ p ^ 2 * |q - 1| := by positivity
    have h2 : 0 ≤ p ^ 3 * beta := mul_nonneg (pow_nonneg hp0.le 3) hb0
    linarith only [h1, h2]
  have hq : p ^ 2 * |q - 1| ≤ z := by
    dsimp only [z]
    have h1 : 0 ≤ p * (N * |mu|) := by positivity
    have h2 : 0 ≤ p ^ 3 * beta := mul_nonneg (pow_nonneg hp0.le 3) hb0
    linarith only [h1, h2]
  have hb : p ^ 3 * beta ≤ z := by
    dsimp only [z]
    have h1 : 0 ≤ p * (N * |mu|) := by positivity
    have h2 : 0 ≤ p ^ 2 * |q - 1| := by positivity
    linarith only [h1, h2]
  obtain ⟨hW, _, _, _, _, _, _, _, _, _, _, _, _, hcompare, hmom, _⟩ :=
    boundedQuadraticTilt_density_moments eta h t (t ^ 2 / 2) hh (by positivity) hsupport
  have hf : (fun a : ℝ => t * a - (t ^ 2 / 2) * a ^ 2) = f := by funext a; dsimp [f]; ring
  rw [hf] at hcompare
  have hfi : Integrable (fun a : ℝ => Real.exp (f a)) eta := by
    convert hW using 1
    funext a
    congr 1
    dsimp [f]
    ring
  have hZ : 0 < Z := integral_exp_pos hfi
  letI : IsProbabilityMeasure rho := isProbabilityMeasure_tilted hfi
  have hsρ : ∀ᵐ a : ℝ ∂rho, |a| ≤ h := (tilted_absolutelyContinuous eta f).ae_le hsupport
  have h2 : Integrable (fun a : ℝ => a ^ 2) eta := (hmom 2).1
  have h3 : Integrable (fun a : ℝ => |a| ^ 3) eta := (hmom 3).2.2.1
  have hLy0 := er_moment_lyapunov eta h2 h3
  have hLy : q ^ 3 ≤ N * beta ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hLy0 (pow_nonneg hN0.le 3)
    dsimp [q, beta, m2, m3]
    nlinarith only [h]
  have hδ0 := er_normalizer_expansion eta h t hh ht hsupport hthin
  change |Z - 1 - t * mu| ≤ 2 * t ^ 3 * m3 at hδ0
  have hδtri : |Z - 1| ≤ |Z - 1 - t * mu| + t * |mu| := by
    have h := abs_add_le (Z - 1 - t * mu) (t * mu)
    simpa only [sub_add_cancel, abs_mul, abs_of_pos ht] using h
  have hδ : N * |Z - 1| ≤ 3 * z := by
    have h1 := mul_le_mul_of_nonneg_left hδtri hN0.le
    have h2 := mul_le_mul_of_nonneg_left hδ0 hN0.le
    have ht3 := pow_le_pow_left₀ ht.le htP 3
    have h3 := mul_le_mul_of_nonneg_right ht3 hb0
    have h4 := mul_le_mul_of_nonneg_right htP (mul_nonneg hN0.le (abs_nonneg mu))
    dsimp [beta] at h3 hb
    nlinarith only [h1, h2, h3, h4, hu, hb]
  obtain ⟨_, _, hgi, hg2, hM0, hR0⟩ := er_tilt_linear_expansions eta h t hh ht hsupport hthin
  change Integrable g rho at hgi
  change Integrable (fun a : ℝ => g a ^ 2) rho at hg2
  change |Z * (∫ a : ℝ, g a ∂rho) - mu - t * m2 / 2| ≤ 4 * t ^ 2 * m3 at hM0
  change |Z * (∫ a : ℝ, g a ^ 2 ∂rho) - m2| ≤ 4 * t * m3 at hR0
  have hM : |Z * M - N * mu - t * q / 2| ≤ 4 * t ^ 2 * beta := by
    calc
      _ = N * |Z * (∫ a : ℝ, g a ∂rho) - mu - t * m2 / 2| := by
        have he : Z * M - N * mu - t * q / 2 =
            N * (Z * (∫ a : ℝ, g a ∂rho) - mu - t * m2 / 2) := by dsimp [M, q]; ring
        rw [he, abs_mul, abs_of_pos hN0]
      _ ≤ N * (4 * t ^ 2 * m3) := mul_le_mul_of_nonneg_left hM0 hN0.le
      _ = _ := by dsimp [beta]; ring
  have hR : |Z * R - q| ≤ 4 * t * beta := by
    calc
      _ = N * |Z * (∫ a : ℝ, g a ^ 2 ∂rho) - m2| := by
        have he : Z * R - q = N * (Z * (∫ a : ℝ, g a ^ 2 ∂rho) - m2) := by dsimp [R, q]; ring
        rw [he, abs_mul, abs_of_pos hN0]
      _ ≤ N * (4 * t * m3) := mul_le_mul_of_nonneg_left hR0 hN0.le
      _ = _ := by dsimp [beta]; ring
  have hu' : p * |N * mu| ≤ z := by rwa [abs_mul, abs_of_pos hN0]
  obtain ⟨_, hA, _, _, hV, _, hVhi⟩ :=
    er_linear_moment_arithmetic N t z q beta (N * mu) Z M R hN ht hz0 hzs hb0 hu' hq hb hLy hδ hM hR
  obtain ⟨hLp, hc3, hc3b⟩ := er_g_centered_third rho h t hh ht hsρ hthin
  change MemLp g 2 rho at hLp
  change Integrable (fun a : ℝ => |g a - ∫ b : ℝ, g b ∂rho| ^ 3) rho at hc3
  change (∫ a : ℝ, |g a - ∫ b : ℝ, g b ∂rho| ^ 3 ∂rho) ≤ 64 * (∫ a : ℝ, |a| ^ 3 ∂rho) at hc3b
  have hVeq : V = R - M ^ 2 / N := by
    have he := variance_eq_sub hLp
    simp only [Pi.pow_apply] at he
    dsimp [V]
    rw [he]
    dsimp [R, M]
    field_simp [hN0.ne'] <;> ring
  rw [← hVeq] at hV hVhi
  have hVlo : (9 / 10 : ℝ) ≤ V := by
    have hp2 : 1 ≤ p ^ 2 := by nlinarith only [hp]
    have hsmallV : 32 * z / p ^ 2 ≤ (1 / 10 : ℝ) := by
      apply (div_le_iff₀ (sq_pos_of_pos hp0)).2
      nlinarith only [hzs, hp2]
    have he := (abs_le.1 (hV.trans hsmallV)).1
    linarith only [he]
  have hS : 2 * (|t| * h + t ^ 2 / 2 * h ^ 2) ≤ (1 / 100 : ℝ) := by
    rw [abs_of_pos ht]
    have hk2 := pow_le_pow_left₀ (mul_nonneg ht.le hh.le) hthin 2
    nlinarith only [hthin, hk2]
  have hExp : Real.exp (2 * (|t| * h + t ^ 2 / 2 * h ^ 2)) ≤ 2 := by
    apply (Real.exp_le_exp.2 hS).trans
    have he := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num : (1 / 100 : ℝ) < 1)
    norm_num at he
    linarith only [he]
  have hρ3 : (∫ a : ℝ, |a| ^ 3 ∂rho) ≤ 2 * m3 := by
    have he := (hcompare (fun a : ℝ => |a| ^ 3) h3
      (Filter.Eventually.of_forall fun a => pow_nonneg (abs_nonneg a) 3)).2
    exact he.trans (mul_le_mul_of_nonneg_right hExp hm30)
  have hc3paid : N * (∫ a : ℝ, |g a - ∫ b : ℝ, g b ∂rho| ^ 3 ∂rho) ≤ 128 * beta := by
    have h1 := mul_le_mul_of_nonneg_left hc3b hN0.le
    have h2 := mul_le_mul_of_nonneg_left hρ3 hN0.le
    dsimp [beta]
    nlinarith only [h1, h2]
  have hZn := er_normalizer_power_budget n hn Z z hZ hz0 hzs hδ
  exact ⟨hZ, inferInstance, hLp, hc3, hZn.1, hZn.2, hA, hV, hVlo, hVhi, hc3paid⟩

private theorem er_standard_cdf_deriv (x : ℝ) :
    HasDerivAt Shao.OQ4.standardNormalCDF (Shao.standardNormalDensity x) x := by
  have heq : Shao.OQ4.standardNormalCDF = fun y : ℝ => 1 - Shao.standardNormalTail y := by
    funext y
    have h := (Shao.standardNormalTail_representation y).2.1
    change Shao.standardNormalTail y = 1 - Shao.OQ4.standardNormalCDF y at h
    linarith only [h]
  rw [heq]
  convert ((Shao.standardNormal_derivatives x).2.const_sub 1) using 1 <;> ring

private theorem er_density_weighted_abs_bound (y : ℝ) :
    |y| * Shao.standardNormalDensity y ≤ 1 := by
  have hroot : 1 ≤ Real.sqrt (2 * Real.pi) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt
      (show (1 : ℝ) ≤ 2 * Real.pi by linarith [Real.two_le_pi])
  have hinv : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hroot
  have hy : |y| ≤ Real.exp (y ^ 2 / 2) := by
    have h := Real.add_one_le_exp (y ^ 2 / 2)
    nlinarith only [h, sq_nonneg (|y| - 1), sq_abs y]
  have hp : |y| * Real.exp (-y ^ 2 / 2) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hy (Real.exp_pos (-y ^ 2 / 2)).le
    have he : Real.exp (y ^ 2 / 2) * Real.exp (-y ^ 2 / 2) = 1 := by
      rw [← Real.exp_add, show y ^ 2 / 2 + -y ^ 2 / 2 = 0 by ring, Real.exp_zero]
    rw [he] at h
    exact h
  have hf : Shao.standardNormalDensity y =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := by
    simp [Shao.standardNormalDensity, gaussianPDFReal]
  rw [hf]
  calc
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * (|y| * Real.exp (-y ^ 2 / 2)) := by ring
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hp (inv_nonneg.2 (Real.sqrt_nonneg _))
    _ ≤ 1 := by simpa only [mul_one] using hinv

private theorem er_standard_cdf_scale (y r : ℝ) (hr : (1 / 2 : ℝ) ≤ r) :
    |Shao.OQ4.standardNormalCDF (y / r) - Shao.OQ4.standardNormalCDF y| ≤ 2 * |r - 1| := by
  let F : ℝ → ℝ := fun s => Shao.OQ4.standardNormalCDF (y / s)
  have hD (s : ℝ) (hs : (1 / 2 : ℝ) ≤ s) :
      HasDerivAt F ((-y / s ^ 2) * Shao.standardNormalDensity (y / s)) s := by
    have hs0 : s ≠ 0 := ne_of_gt (by linarith only [hs])
    have hd := (hasDerivAt_const s y).div (hasDerivAt_id s) hs0
    have hc := (er_standard_cdf_deriv (y / s)).comp s hd
    convert hc using 1 <;> first | rfl | (simp only [id_eq, zero_mul, zero_sub, mul_one] <;> ring)
  have hbound (s : ℝ) (hs : (1 / 2 : ℝ) ≤ s) : ‖deriv F s‖ ≤ 2 := by
    have hs0 : 0 < s := by linarith only [hs]
    have hden : 0 < Shao.standardNormalDensity (y / s) := gaussianPDFReal_pos 0 1 (y / s) (by norm_num)
    rw [(hD s hs).deriv, Real.norm_eq_abs, abs_mul, abs_div, abs_neg,
      abs_of_nonneg (sq_nonneg s), abs_of_pos hden]
    have he : |y| / s ^ 2 * Shao.standardNormalDensity (y / s) =
        (|y / s| * Shao.standardNormalDensity (y / s)) / s := by
      rw [abs_div, abs_of_pos hs0]
      field_simp <;> ring
    rw [he]
    apply (div_le_iff₀ hs0).2
    have h := er_density_weighted_abs_bound (y / s)
    linarith only [h, hs]
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (C := (2 : ℝ))
    (fun s (hs : s ∈ Set.Ici (1 / 2 : ℝ)) => (hD s hs).differentiableAt)
    (fun s (hs : s ∈ Set.Ici (1 / 2 : ℝ)) => hbound s hs)
    (convex_Ici (1 / 2 : ℝ))
    (show (1 : ℝ) ∈ Set.Ici (1 / 2 : ℝ) by norm_num) hr
  simpa only [F, div_one, Real.norm_eq_abs] using hmv

private theorem er_gaussian_parameter_cdf
    (A V y : ℝ) (hV : (1 / 2 : ℝ) ≤ V) :
    |Shao.OQ4.standardNormalCDF ((y - A) / Real.sqrt V) -
      Shao.OQ4.standardNormalCDF y| ≤ 2 * |A| + 2 * |V - 1| := by
  let r : ℝ := Real.sqrt V
  have hV0 : 0 ≤ V := by linarith only [hV]
  have hr0 : 0 ≤ r := Real.sqrt_nonneg V
  have hrsq : r ^ 2 = V := Real.sq_sqrt hV0
  have hr : (1 / 2 : ℝ) ≤ r := by nlinarith only [hr0, hrsq, hV]
  have hrpos : 0 < r := by linarith only [hr]
  have hscale := er_standard_cdf_scale y r hr
  have hrerr : |r - 1| ≤ |V - 1| := by
    have he : V - 1 = (r - 1) * (r + 1) := by nlinarith only [hrsq]
    rw [he, abs_mul, abs_of_nonneg (show 0 ≤ r + 1 by linarith only [hr0])]
    nlinarith only [mul_nonneg hr0 (abs_nonneg (r - 1))]
  have hshift : |Shao.OQ4.standardNormalCDF ((y - A) / r) - Shao.OQ4.standardNormalCDF (y / r)| ≤ 2 * |A| := by
    have h := Shao.OQ4.standardNormalCDF_lipschitz ((y - A) / r) (y / r)
    have he : (y - A) / r - y / r = -A / r := by ring
    rw [he, abs_div, abs_neg, abs_of_pos hrpos] at h
    apply h.trans
    apply (div_le_iff₀ hrpos).2
    nlinarith only [mul_le_mul_of_nonneg_right hr (abs_nonneg A)]
  exact (abs_sub_le (Shao.OQ4.standardNormalCDF ((y - A) / r))
    (Shao.OQ4.standardNormalCDF (y / r)) (Shao.OQ4.standardNormalCDF y)).trans
      (by linarith only [hshift, hscale, hrerr])

private theorem er_standard_cdf_interval
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B : ℝ) (hB : 0 ≤ B)
    (hCDF : ∀ x : ℝ, |μ.real (Set.Iic x) - Shao.OQ4.standardNormalCDF x| ≤ B)
    (a b : ℝ) (hab : a ≤ b) :
    |μ.real (Set.Icc a b) - (gaussianReal 0 1).real (Set.Icc a b)| ≤ 2 * B := by
  let γ : Measure ℝ := gaussianReal 0 1
  letI : NullSingletonClass γ := nullSingletonClass_gaussianReal (by norm_num)
  have hγ : γ.real (Set.Icc a b) = Shao.OQ4.standardNormalCDF b - Shao.OQ4.standardNormalCDF a := by
    rw [← measureReal_congr (μ := γ) (Ioc_ae_eq_Icc (a := a) (b := b))]
    rw [Shao.OQ4.real_Ioc_eq_real_Iic_sub γ a b hab]
    simp only [γ, ← Shao.OQ4.standardNormalCDF_eq_real]
  have hlo : Shao.OQ4.standardNormalCDF b - Shao.OQ4.standardNormalCDF a - 2 * B ≤
      μ.real (Set.Icc a b) := by
    have h1 := (abs_le.1 (hCDF b)).1
    have h2 := (abs_le.1 (hCDF a)).2
    have hm : μ.real (Set.Ioc a b) ≤ μ.real (Set.Icc a b) := measureReal_mono Set.Ioc_subset_Icc_self
    rw [Shao.OQ4.real_Ioc_eq_real_Iic_sub μ a b hab] at hm
    linarith only [h1, h2, hm]
  have hhi : μ.real (Set.Icc a b) ≤ Shao.OQ4.standardNormalCDF b - Shao.OQ4.standardNormalCDF a + 2 * B := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hsub : Set.Icc a b ⊆ Set.Ioc (a - δ) b := fun y hy => ⟨by linarith only [hy.1, hδ], hy.2⟩
    have hm : μ.real (Set.Icc a b) ≤ μ.real (Set.Ioc (a - δ) b) := measureReal_mono hsub
    rw [Shao.OQ4.real_Ioc_eq_real_Iic_sub μ (a - δ) b (by linarith only [hab, hδ])] at hm
    have h1 := (abs_le.1 (hCDF b)).2
    have h2 := (abs_le.1 (hCDF (a - δ))).1
    have hG := Shao.OQ4.standardNormalCDF_lipschitz a (a - δ)
    have he : |a - (a - δ)| = δ := by rw [sub_sub_cancel, abs_of_pos hδ]
    rw [he] at hG
    have hG' := (abs_le.1 hG).2
    linarith only [hm, h1, h2, hG']
  change |μ.real (Set.Icc a b) - γ.real (Set.Icc a b)| ≤ _
  rw [hγ]
  exact abs_le.2 ⟨by linarith only [hlo], by linarith only [hhi]⟩

private theorem er_halfaxis_cdf_compare
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (t B : ℝ) (ht : 0 < t) (hB : 0 ≤ B)
    (hCDF : ∀ x : ℝ, |μ.real (Set.Iic x) - Shao.OQ4.standardNormalCDF x| ≤ B) :
    |(∫ y : ℝ, (if 0 ≤ y then Real.exp (-t * y) else 0) ∂μ) -
      (∫ y : ℝ, (if 0 ≤ y then Real.exp (-t * y) else 0) ∂gaussianReal 0 1)| ≤ 2 * B := by
  let H : ℝ → ℝ := fun y => if 0 ≤ y then Real.exp (-t * y) else 0
  let γ : Measure ℝ := gaussianReal 0 1
  let L : ℝ → ℝ := fun s => μ.real {y : ℝ | s ≤ H y}
  let K : ℝ → ℝ := fun s => γ.real {y : ℝ | s ≤ H y}
  have hHm : Measurable H := (measurable_id.const_mul (-t)).exp.ite
    (measurableSet_le measurable_const measurable_id) measurable_const
  have hH0 (y : ℝ) : 0 ≤ H y := by dsimp [H]; split_ifs <;> positivity
  have hH1 (y : ℝ) : H y ≤ 1 := by
    dsimp [H]
    split_ifs with hy
    · exact Real.exp_le_one_iff.2 (by nlinarith only [mul_nonneg ht.le hy])
    · norm_num
  have hI (ν : Measure ℝ) [IsProbabilityMeasure ν] : Integrable H ν :=
    er_integrable_bound ν H hHm 1 (Filter.Eventually.of_forall fun y => by
      rw [abs_of_nonneg (hH0 y)]; exact hH1 y)
  have hrepμ := (hI μ).integral_eq_integral_Ioc_meas_le
    (Filter.Eventually.of_forall hH0) (Filter.Eventually.of_forall hH1)
  have hrepγ := (hI γ).integral_eq_integral_Ioc_meas_le
    (Filter.Eventually.of_forall hH0) (Filter.Eventually.of_forall hH1)
  have hLanti : Antitone L := by
    intro a b hab
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono fun y hy => le_trans hab hy)
  have hKanti : Antitone K := by
    intro a b hab
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono fun y hy => le_trans hab hy)
  let mLevels : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  haveI : IsFiniteMeasure mLevels := by constructor; simp [mLevels]
  have hLI : Integrable L mLevels := er_integrable_bound mLevels L hLanti.measurable 1
    (Filter.Eventually.of_forall fun s => by rw [abs_of_nonneg (measureReal_nonneg)]; exact measureReal_le_one)
  have hKI : Integrable K mLevels := er_integrable_bound mLevels K hKanti.measurable 1
    (Filter.Eventually.of_forall fun s => by rw [abs_of_nonneg (measureReal_nonneg)]; exact measureReal_le_one)
  have hlevel (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
      {y : ℝ | s ≤ H y} = Set.Icc 0 (-Real.log s / t) := by
    ext y
    change (s ≤ H y) ↔ (0 ≤ y ∧ y ≤ -Real.log s / t)
    have hslog : Real.log s ≤ 0 := Real.log_nonpos hs.1.le hs.2
    have he : s ≤ Real.exp (-t * y) ↔ Real.log s ≤ -t * y := by
      simpa only [Real.exp_log hs.1] using
        (Real.exp_le_exp : Real.exp (Real.log s) ≤ Real.exp (-t * y) ↔ Real.log s ≤ -t * y)
    by_cases hy : 0 ≤ y
    · have hHy : H y = Real.exp (-t * y) := if_pos hy
      rw [hHy]
      simp only [hy, true_and]
      rw [he, le_div_iff₀ ht]
      constructor <;> intro hh <;> linarith only [hh]
    · have hHy : H y = 0 := if_neg hy
      rw [hHy]
      simp only [hy, false_and]
      constructor
      · intro hh
        exact (not_le_of_gt hs.1) hh
      · intro hh
        exact False.elim hh
  have hbnd : ∀ᵐ s : ℝ ∂mLevels, |L s - K s| ≤ 2 * B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hb : 0 ≤ -Real.log s / t := div_nonneg
      (neg_nonneg.2 (Real.log_nonpos hs.1.le hs.2)) ht.le
    dsimp only [L, K]
    rw [hlevel s hs]
    exact er_standard_cdf_interval μ B hB hCDF 0 (-Real.log s / t) hb
  change |(∫ y : ℝ, H y ∂μ) - (∫ y : ℝ, H y ∂γ)| ≤ _
  rw [hrepμ, hrepγ]
  change |(∫ s : ℝ, L s ∂mLevels) - (∫ s : ℝ, K s ∂mLevels)| ≤ _
  rw [← integral_sub hLI hKI]
  have hb := er_abs_integral mLevels (L - K) (fun _ => 2 * B) (hLI.sub hKI)
    (integrable_const (2 * B)) hbnd
  simpa [mLevels] using hb

private theorem er_standard_gaussian_halfaxis (t : ℝ) :
    (∫ y : ℝ, (if 0 ≤ y then Real.exp (-t * y) else 0) ∂gaussianReal 0 1) =
      Real.exp (t ^ 2 / 2) * Shao.standardNormalTail t := by
  classical
  have hformula (y : ℝ) : Shao.standardNormalDensity y =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := by
    simp [Shao.standardNormalDensity, gaussianPDFReal]
  have hsquare (y : ℝ) : Shao.standardNormalDensity y * Real.exp (-t * y) =
      Real.exp (t ^ 2 / 2) * Shao.standardNormalDensity (y + t) := by
    rw [hformula y, hformula (y + t)]
    calc
      _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2 + -t * y) := by rw [Real.exp_add]; ring
      _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (t ^ 2 / 2 + -(y + t) ^ 2 / 2) := by congr 2; ring
      _ = _ := by rw [Real.exp_add]; ring
  have hpoint (y : ℝ) : Shao.standardNormalDensity y *
      (if 0 ≤ y then Real.exp (-t * y) else 0) =
        Real.exp (t ^ 2 / 2) * (Set.Ici 0).indicator (fun y => Shao.standardNormalDensity (y + t)) y := by
    by_cases hy : 0 ≤ y
    · rw [if_pos hy, Set.indicator_of_mem hy]
      exact hsquare y
    · rw [if_neg hy, Set.indicator_of_notMem hy]
      ring
  have hshift : (∫ y : ℝ, (Set.Ici 0).indicator (fun y => Shao.standardNormalDensity (y + t)) y) =
      ∫ y : ℝ, (Set.Ici t).indicator Shao.standardNormalDensity y := by
    calc
      _ = ∫ y : ℝ, (Set.Ici t).indicator Shao.standardNormalDensity (y + t) := integral_congr_ae (Filter.Eventually.of_forall fun y => by
        change (Set.Ici 0).indicator (fun y => Shao.standardNormalDensity (y + t)) y =
          (Set.Ici t).indicator Shao.standardNormalDensity (y + t)
        by_cases hy : 0 ≤ y
        · have hyt : y + t ∈ Set.Ici t := by change t ≤ y + t; linarith only [hy]
          rw [Set.indicator_of_mem hy, Set.indicator_of_mem hyt]
        · have hyt : y + t ∉ Set.Ici t := by change ¬t ≤ y + t; linarith only [hy]
          rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hyt])
      _ = _ := integral_add_right_eq_self ((Set.Ici t).indicator Shao.standardNormalDensity) t
  have htail : (∫ y : ℝ, (Set.Ici t).indicator Shao.standardNormalDensity y) = Shao.standardNormalTail t := by
    rw [integral_indicator measurableSet_Ici]
    exact (setIntegral_congr_set (Ioi_ae_eq_Ici (a := t)).symm).trans
      (Shao.standardNormalTail_representation t).2.2.symm
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  change (∫ y : ℝ, Shao.standardNormalDensity y * (if 0 ≤ y then Real.exp (-t * y) else 0)) = _
  simp_rw [hpoint]
  rw [integral_const_mul, hshift, htail]

private theorem er_iid_mapped_berry_esseeen
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (g : ℝ → ℝ) (hgm : Measurable g)
    (h3 : Integrable (fun a : ℝ => |g a| ^ 3) ν)
    (hV : 0 < variance g ν)
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    let m : ℝ := ∫ a : ℝ, g a ∂ν
    let v : ℝ := variance g ν
    let m3c : ℝ := ∫ a : ℝ, |g a - m| ^ 3 ∂ν
    |(Measure.pi (fun _ : Fin n => ν)).real
        {a : Shao.Path n |
          ((∑ i : Fin n, g (a i)) - (n : ℝ) * m) /
            (Real.sqrt v * Real.sqrt (n : ℝ)) ≤ x} -
        Shao.OQ4.standardNormalCDF x| ≤
      (1024 : ℝ) * m3c / ((Real.sqrt v) ^ 3 * Real.sqrt (n : ℝ)) := by
  let ζ : Measure ℝ := ν.map g
  let G : Shao.Path n → Shao.Path n := fun a i => g (a i)
  have hG : Measurable G := Measurable.of_eval fun i => hgm.comp (measurable_pi_apply i)
  haveI : IsProbabilityMeasure ζ := by
    constructor
    change ν.map g Set.univ = 1
    rw [Measure.map_apply hgm MeasurableSet.univ]
    simp
  have hζ3 : Integrable (fun z : ℝ => |z| ^ 3) ζ :=
    (integrable_map_measure (by fun_prop) hgm.aemeasurable).2 h3
  have hmean : (∫ z : ℝ, z ∂ζ) = ∫ a : ℝ, g a ∂ν :=
    integral_map hgm.aemeasurable measurable_id.aestronglyMeasurable
  have hvar : variance (id : ℝ → ℝ) ζ = variance g ν := by
    simpa only [Function.comp_def, id_eq] using
      variance_map (X := (id : ℝ → ℝ)) measurable_id.aemeasurable hgm.aemeasurable
  have hζV : 0 < variance (id : ℝ → ℝ) ζ := by rw [hvar]; exact hV
  have hCDF := iid_centered_berryEsseen ζ hζ3 hζV n hn x
  have hmap : (Measure.pi (fun _ : Fin n => ν)).map G =
      Measure.pi (fun _ : Fin n => ζ) := Measure.pi_map_pi (fun _ : Fin n => hgm.aemeasurable)
  have hc3 : (∫ z : ℝ, |z - (∫ a : ℝ, g a ∂ν)| ^ 3 ∂ζ) =
      ∫ a : ℝ, |g a - (∫ b : ℝ, g b ∂ν)| ^ 3 ∂ν :=
    integral_map hgm.aemeasurable (by fun_prop)
  change |(Measure.pi (fun _ : Fin n => ζ)).real
      {a : Shao.Path n | (Shao.prefixSum a n - (n : ℝ) * (∫ z : ℝ, z ∂ζ)) /
        (Real.sqrt (variance (id : ℝ → ℝ) ζ) * Real.sqrt (n : ℝ)) ≤ x} -
      Shao.OQ4.standardNormalCDF x| ≤
    1024 * (∫ z : ℝ, |z - (∫ a : ℝ, a ∂ζ)| ^ 3 ∂ζ) /
      ((Real.sqrt (variance (id : ℝ → ℝ) ζ)) ^ 3 * Real.sqrt (n : ℝ)) at hCDF
  rw [hmean, hvar, hc3] at hCDF
  have hset : MeasurableSet {a : Shao.Path n |
      (Shao.prefixSum a n - (n : ℝ) * (∫ z : ℝ, g z ∂ν)) /
        (Real.sqrt (variance g ν) * Real.sqrt (n : ℝ)) ≤ x} :=
    measurableSet_le (((Shao.measurable_prefixSum n).sub_const _).div_const _) measurable_const
  have hactual : (Measure.pi (fun _ : Fin n => ζ)).real
      {a : Shao.Path n | (Shao.prefixSum a n - (n : ℝ) * (∫ z : ℝ, g z ∂ν)) /
        (Real.sqrt (variance g ν) * Real.sqrt (n : ℝ)) ≤ x} =
      (Measure.pi (fun _ : Fin n => ν)).real
      {a : Shao.Path n | ((∑ i : Fin n, g (a i)) - (n : ℝ) * (∫ z : ℝ, g z ∂ν)) /
        (Real.sqrt (variance g ν) * Real.sqrt (n : ℝ)) ≤ x} := by
    rw [← hmap, Measure.real_def, Measure.map_apply hG hset]
    congr 1
    congr 1
    ext a
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Shao.prefixSum_length, G]
  rw [hactual] at hCDF
  exact hCDF

private theorem er_endpoint_linear_cdf
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
    ∀ y : ℝ, |T.real {v : Shao.Path n | W v ≤ y} - Shao.OQ4.standardNormalCDF y| ≤
      196608 * beta + 32 * z / (1 + t) + 64 * z / (1 + t) ^ 2 := by
  dsimp only
  let N : ℝ := n
  let p : ℝ := 1 + t
  let beta : ℝ := N * (∫ a : ℝ, |a| ^ 3 ∂eta)
  let z : ℝ := p * (N * |∫ a : ℝ, a ∂eta|) +
    p ^ 2 * |N * (∫ a : ℝ, a ^ 2 ∂eta) - 1| + p ^ 3 * beta
  let rho : Measure ℝ := eta.tilted (fun a : ℝ => t * a - t ^ 2 * a ^ 2 / 2)
  let T : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  let g : ℝ → ℝ := fun a => a - t * a ^ 2 / 2
  let W : Shao.Path n → ℝ := fun v => Shao.prefixSum v n - t * Shao.energy v / 2 - t / 2
  let A : ℝ := N * (∫ a : ℝ, g a ∂rho) - t / 2
  let v : ℝ := variance g rho
  let V : ℝ := N * v
  have hN : 0 < N := by dsimp [N]; exact_mod_cast (show 0 < n by omega)
  have hp : 0 < p := by dsimp [p]; linarith only [ht]
  have hb : 0 ≤ beta := mul_nonneg hN.le (integral_nonneg fun a => pow_nonneg (abs_nonneg a) 3)
  obtain ⟨_, hprob, hLp, hc3, _, _, hA, hVerr, hVlo, _, hc3b⟩ :=
    er_tilt_small_moment_budget eta n hn h t hh ht hsupport hthin hsmall
  letI : IsProbabilityMeasure rho := hprob
  change |A| ≤ 16 * z / p at hA
  change |V - 1| ≤ 32 * z / p ^ 2 at hVerr
  change (9 / 10 : ℝ) ≤ V at hVlo
  change N * (∫ a : ℝ, |g a - ∫ b : ℝ, g b ∂rho| ^ 3 ∂rho) ≤ 128 * beta at hc3b
  have hv : 0 < v := by
    by_contra hh
    have h := mul_nonpos_of_nonneg_of_nonpos hN.le (le_of_not_gt hh)
    change V ≤ 0 at h
    linarith only [h, hVlo]
  have hV : 0 < V := by linarith only [hVlo]
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hsqrt : Real.sqrt V = Real.sqrt v * Real.sqrt N := by
    dsimp [V]
    rw [Real.sqrt_mul hN.le, mul_comm]
  have hden : N * ((Real.sqrt v) ^ 3 * Real.sqrt N) = (Real.sqrt V) ^ 3 := by
    rw [hsqrt, mul_pow]
    have he : (Real.sqrt N) ^ 3 = N * Real.sqrt N := by rw [pow_succ, Real.sq_sqrt hN.le]
    rw [he]
    ring
  have hsV9 : (9 / 10 : ℝ) ≤ Real.sqrt V := by nlinarith only [Real.sq_sqrt hV.le, hsV.le, hVlo]
  have hsV3 : (81 / 100 : ℝ) ≤ (Real.sqrt V) ^ 3 := by
    calc
      (81 / 100 : ℝ) = (9 / 10 : ℝ) * (9 / 10 : ℝ) := by norm_num
      _ ≤ V * Real.sqrt V := mul_le_mul hVlo hsV9 (by norm_num) hV.le
      _ = (Real.sqrt V) ^ 2 * Real.sqrt V :=
        congrArg (fun a : ℝ => a * Real.sqrt V) (Real.sq_sqrt hV.le).symm
      _ = _ := by ring
  have hbeBudget : 1024 * (∫ a : ℝ, |g a - ∫ b : ℝ, g b ∂rho| ^ 3 ∂rho) /
      ((Real.sqrt v) ^ 3 * Real.sqrt N) ≤ 196608 * beta := by
    apply (div_le_iff₀ (mul_pos (pow_pos hsv 3) hsN)).2
    apply (mul_le_mul_iff_right₀ hN).1
    have hh := mul_le_mul_of_nonneg_left hsV3 (show 0 ≤ 196608 * beta by positivity)
    rw [← hden] at hh
    nlinarith only [hh, hc3b, hb]
  have hgm : Measurable g := by dsimp [g]; fun_prop
  have hsρ : ∀ᵐ a : ℝ ∂rho, |a| ≤ h :=
    (tilted_absolutelyContinuous eta (fun a : ℝ => t * a - t ^ 2 * a ^ 2 / 2)).ae_le hsupport
  have hg3 : Integrable (fun a : ℝ => |g a| ^ 3) rho :=
    er_integrable_bound rho _ (by fun_prop) ((2 * h) ^ 3) (by
      filter_upwards [hsρ] with a ha
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
      apply pow_le_pow_left₀ (abs_nonneg _) _ 3
      exact (er_g_abs h t a hh.le ht.le hthin ha).trans (by linarith only [ha]))
  intro y
  change |T.real {a : Shao.Path n | W a ≤ y} - Shao.OQ4.standardNormalCDF y| ≤
    196608 * beta + 32 * z / p + 64 * z / p ^ 2
  have hBE := er_iid_mapped_berry_esseeen rho g hgm hg3 hv n hn ((y - A) / Real.sqrt V)
  have hsum (a : Shao.Path n) : (∑ i : Fin n, g (a i)) = Shao.prefixSum a n - t * Shao.energy a / 2 := by
    simp only [g, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum, Shao.prefixSum_length, Shao.energy]
  have hset : {a : Shao.Path n |
      ((∑ i : Fin n, g (a i)) - N * (∫ a : ℝ, g a ∂rho)) /
        (Real.sqrt v * Real.sqrt N) ≤ (y - A) / Real.sqrt V} =
      {a : Shao.Path n | W a ≤ y} := by
    ext a
    simp only [Set.mem_setOf_eq]
    rw [← hsqrt, div_le_div_iff_of_pos_right hsV, hsum]
    dsimp [A, W]
    constructor <;> intro hh <;> linarith only [hh]
  change |T.real {a : Shao.Path n |
      ((∑ i : Fin n, g (a i)) - N * (∫ a : ℝ, g a ∂rho)) /
        (Real.sqrt v * Real.sqrt N) ≤ (y - A) / Real.sqrt V} -
        Shao.OQ4.standardNormalCDF ((y - A) / Real.sqrt V)| ≤
      1024 * (∫ a : ℝ, |g a - ∫ b : ℝ, g b ∂rho| ^ 3 ∂rho) /
        ((Real.sqrt v) ^ 3 * Real.sqrt N) at hBE
  rw [hset] at hBE
  have hnormal := er_gaussian_parameter_cdf A V y (by linarith only [hVlo])
  have hpaid : |T.real {a : Shao.Path n | W a ≤ y} - Shao.OQ4.standardNormalCDF ((y - A) / Real.sqrt V)| +
      |Shao.OQ4.standardNormalCDF ((y - A) / Real.sqrt V) - Shao.OQ4.standardNormalCDF y| ≤
      196608 * beta + 2 * (16 * z / p) + 2 * (32 * z / p ^ 2) := by
    linarith only [hBE.trans hbeBudget, hnormal, hA, hVerr]
  have he : 196608 * beta + 2 * (16 * z / p) + 2 * (32 * z / p ^ 2) =
      196608 * beta + 32 * z / p + 64 * z / p ^ 2 := by ring
  exact (abs_sub_le (T.real {a : Shao.Path n | W a ≤ y})
    (Shao.OQ4.standardNormalCDF ((y - A) / Real.sqrt V)) (Shao.OQ4.standardNormalCDF y)).trans
      (hpaid.trans_eq he)

private theorem er_endpoint_halfaxis_budget
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
    let H : Shao.Path n → ℝ := fun v =>
      if 0 ≤ W v then Real.exp (-t * W v) else 0
    |(∫ v : Shao.Path n, H v ∂T) - Real.exp (t ^ 2 / 2) * Shao.standardNormalTail t| ≤
      393408 * z / (1 + t) := by
  dsimp only
  let p : ℝ := 1 + t
  let beta : ℝ := (n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂eta)
  let z : ℝ := p * ((n : ℝ) * |∫ a : ℝ, a ∂eta|) +
    p ^ 2 * |(n : ℝ) * (∫ a : ℝ, a ^ 2 ∂eta) - 1| + p ^ 3 * beta
  let rho : Measure ℝ := eta.tilted (fun a : ℝ => t * a - t ^ 2 * a ^ 2 / 2)
  let T : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  let W : Shao.Path n → ℝ := fun v => Shao.prefixSum v n - t * Shao.energy v / 2 - t / 2
  let μ : Measure ℝ := T.map W
  let B : ℝ := 196608 * beta + 32 * z / p + 64 * z / p ^ 2
  have hp : 1 ≤ p := by dsimp [p]; linarith only [ht]
  have hp0 : 0 < p := by linarith only [hp]
  have hb : 0 ≤ beta := mul_nonneg (Nat.cast_nonneg n) (integral_nonneg fun a => pow_nonneg (abs_nonneg a) 3)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hprob := (er_tilt_small_moment_budget eta n hn h t hh ht hsupport hthin hsmall).2.1
  letI : IsProbabilityMeasure rho := hprob
  have hWm : Measurable W :=
    ((Shao.measurable_prefixSum n).sub ((Shao.measurable_energy.const_mul t).div_const 2)).sub_const (t / 2)
  haveI : IsProbabilityMeasure μ := by
    constructor
    change T.map W Set.univ = 1
    rw [Measure.map_apply hWm MeasurableSet.univ]
    simp [T]
  have hCDF (y : ℝ) : |μ.real (Set.Iic y) - Shao.OQ4.standardNormalCDF y| ≤ B := by
    change |(T.map W (Set.Iic y)).toReal - Shao.OQ4.standardNormalCDF y| ≤ B
    rw [Measure.map_apply hWm measurableSet_Iic]
    exact er_endpoint_linear_cdf eta n hn h t hh ht hsupport hthin hsmall y
  have hcomp := er_halfaxis_cdf_compare μ t B ht hB hCDF
  have hsm : Measurable (fun y : ℝ => if 0 ≤ y then Real.exp (-t * y) else 0) :=
    (measurable_id.const_mul (-t)).exp.ite
      (measurableSet_le measurable_const measurable_id) measurable_const
  have hmap : (∫ y : ℝ, (if 0 ≤ y then Real.exp (-t * y) else 0) ∂μ) =
      ∫ v : Shao.Path n, (if 0 ≤ W v then Real.exp (-t * W v) else 0) ∂T :=
    integral_map hWm.aemeasurable hsm.aestronglyMeasurable
  rw [hmap, er_standard_gaussian_halfaxis t] at hcomp
  have hbcost : p ^ 3 * beta ≤ z := by
    dsimp only [z]
    have h1 : 0 ≤ p * ((n : ℝ) * |∫ a : ℝ, a ∂eta|) := by positivity
    have h2 : 0 ≤ p ^ 2 * |(n : ℝ) * (∫ a : ℝ, a ^ 2 ∂eta) - 1| := by positivity
    linarith only [h1, h2]
  have hbp : beta ≤ z / p := by
    apply (le_div_iff₀ hp0).2
    have hp3 : p ≤ p ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hp 2
      have h' := mul_le_mul_of_nonneg_right h hp0.le
      nlinarith only [h']
    have h := mul_le_mul_of_nonneg_right hp3 hb
    nlinarith only [h, hbcost]
  have hzdiv : z / p ^ 2 ≤ z / p := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hp0) hp0).2
    have hp2 : p ≤ p ^ 2 := by nlinarith only [hp]
    exact mul_le_mul_of_nonneg_left hp2 hz
  change |(∫ v : Shao.Path n, (if 0 ≤ W v then Real.exp (-t * W v) else 0) ∂T) -
    Real.exp (t ^ 2 / 2) * Shao.standardNormalTail t| ≤ 393408 * z / p
  apply hcomp.trans
  dsimp only [B]
  have hpaid : 2 * (196608 * beta + 32 * (z / p) + 64 * (z / p ^ 2)) ≤ 393408 * (z / p) := by
    linarith only [hbp, hzdiv]
  convert hpaid using 1 <;> ring

theorem boundedEndpoint_quadraticTilt_linear_halfspace
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
    let f : ℝ → ℝ := fun a => t * a - t ^ 2 * a ^ 2 / 2
    let Z : ℝ := ∫ a : ℝ, Real.exp (f a) ∂eta
    let etaT : Measure ℝ := eta.tilted f
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => eta)
    let T : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => etaT)
    let W : Shao.Path n → ℝ := fun v =>
      Shao.prefixSum v n - t * Shao.energy v / 2 - t / 2
    let D : Shao.Path n → ℝ := fun v =>
      t * (Real.sqrt (Shao.energy v) - 1) ^ 2 / 2
    let H : Shao.Path n → ℝ := fun v =>
      if 0 ≤ W v then Real.exp (-t * W v) else 0
    let J : Shao.Path n → ℝ := fun v =>
      if -D v ≤ W v ∧ W v < 0 then Real.exp (-t * W v) else 0
    0 < Z ∧ IsProbabilityMeasure etaT ∧ IsProbabilityMeasure T ∧
      Integrable H T ∧ Integrable J T ∧
      Z ^ n ≤ 2 ∧ |Z ^ n - 1| ≤ 8 * z ∧
      P.real {v : Shao.Path n |
        t * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v n} =
        Z ^ n * Real.exp (-(t ^ 2 / 2)) *
          ((∫ v : Shao.Path n, H v ∂T) + (∫ v : Shao.Path n, J v ∂T)) ∧
      |Z ^ n * Real.exp (-(t ^ 2 / 2)) * (∫ v : Shao.Path n, H v ∂T) -
        Shao.standardNormalTail t| ≤
        (2 : ℝ) ^ 20 * Real.sqrt (2 * Real.pi) * z * Shao.standardNormalTail t := by
  dsimp only
  let p : ℝ := 1 + t
  let z : ℝ := p * ((n : ℝ) * |∫ a : ℝ, a ∂eta|) +
    p ^ 2 * |(n : ℝ) * (∫ a : ℝ, a ^ 2 ∂eta) - 1| +
    p ^ 3 * ((n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂eta))
  let f : ℝ → ℝ := fun a => t * a - t ^ 2 * a ^ 2 / 2
  let Z : ℝ := ∫ a : ℝ, Real.exp (f a) ∂eta
  let rho : Measure ℝ := eta.tilted f
  let T : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  let W : Shao.Path n → ℝ := fun v => Shao.prefixSum v n - t * Shao.energy v / 2 - t / 2
  let H : Shao.Path n → ℝ := fun v => if 0 ≤ W v then Real.exp (-t * W v) else 0
  let E : ℝ := Real.exp (-(t ^ 2 / 2))
  let K : ℝ := Real.exp (t ^ 2 / 2) * Shao.standardNormalTail t
  obtain ⟨hZ, hprob, hprobT, hH, hJ, hidentity⟩ := er_endpoint_exact_split eta n h t hh ht hsupport
  obtain ⟨_, _, _, _, hZn, hZnerr, _⟩ := er_tilt_small_moment_budget eta n hn h t hh ht hsupport hthin hsmall
  have hHerror := er_endpoint_halfaxis_budget eta n hn h t hh ht hsupport hthin hsmall
  change |(∫ v : Shao.Path n, H v ∂T) - K| ≤ 393408 * z / p at hHerror
  change Z ^ n ≤ 2 at hZn
  change |Z ^ n - 1| ≤ 8 * z at hZnerr
  have hz : 0 ≤ z := by dsimp [z, p]; positivity
  have hp : 0 < p := by dsimp [p]; linarith only [ht]
  have htail : 0 < Shao.standardNormalTail t := (Shao.standardNormalTail_basic.2.2.1 t).1
  have hroot : 1 ≤ Real.sqrt (2 * Real.pi) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt
      (show (1 : ℝ) ≤ 2 * Real.pi by linarith [Real.two_le_pi])
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hZn0 : 0 ≤ Z ^ n := pow_nonneg (le_of_lt hZ) n
  have hEK : E * K = Shao.standardNormalTail t := by
    dsimp [E, K]
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have hfactor : Z ^ n * E * K = Z ^ n * Shao.standardNormalTail t := by rw [mul_assoc, hEK]
  have hdecomp : Z ^ n * E * (∫ v : Shao.Path n, H v ∂T) - Shao.standardNormalTail t =
      (Z ^ n * E) * ((∫ v : Shao.Path n, H v ∂T) - K) +
        (Z ^ n - 1) * Shao.standardNormalTail t := by nlinarith only [hfactor]
  have hmain : |Z ^ n * E * (∫ v : Shao.Path n, H v ∂T) - Shao.standardNormalTail t| ≤
      (2 * E) * (393408 * z / p) + 8 * z * Shao.standardNormalTail t := by
    rw [hdecomp]
    have htri := abs_add_le ((Z ^ n * E) * ((∫ v : Shao.Path n, H v ∂T) - K))
      ((Z ^ n - 1) * Shao.standardNormalTail t)
    simp only [abs_mul, abs_of_nonneg hZn0, abs_of_nonneg hE, abs_of_pos htail] at htri
    have h1 := mul_le_mul (mul_le_mul_of_nonneg_right hZn hE) hHerror
      (abs_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hE)
    have h2 := mul_le_mul_of_nonneg_right hZnerr htail.le
    linarith only [htri, h1, h2]
  have hformula : E = Real.sqrt (2 * Real.pi) * Shao.standardNormalDensity t := by
    dsimp [E]
    rw [show -(t ^ 2 / 2) = -t ^ 2 / 2 by ring]
    simp only [Shao.standardNormalDensity, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
    field_simp
  have hMills : E / p ≤ Real.sqrt (2 * Real.pi) * Shao.standardNormalTail t := by
    rw [hformula, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (Shao.standardNormal_mills_bounds t ht.le).1 (Real.sqrt_nonneg _)
  have hpaid := mul_le_mul_of_nonneg_left hMills (show 0 ≤ 786816 * z by positivity)
  have hsmall := mul_le_mul_of_nonneg_right hroot (mul_nonneg hz htail.le)
  have hcost : (2 * E) * (393408 * z / p) = 786816 * z * (E / p) := by ring
  rw [hcost] at hmain
  refine ⟨hZ, hprob, hprobT, hH, hJ, hZn, hZnerr, hidentity, ?_⟩
  change |Z ^ n * E * (∫ v : Shao.Path n, H v ∂T) - Shao.standardNormalTail t| ≤
    (2 : ℝ) ^ 20 * Real.sqrt (2 * Real.pi) * z * Shao.standardNormalTail t
  norm_num only [show (2 : ℝ) ^ 20 = 1048576 by norm_num]
  nlinarith only [hmain, hpaid, hsmall,
    mul_nonneg (Real.sqrt_nonneg (2 * Real.pi)) (mul_nonneg hz htail.le)]

private theorem er_bounded_weak_tail
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
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => eta)
    |P.real {v : Shao.Path n | t * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v n} -
      Shao.standardNormalTail t| ≤
      ((2 : ℝ) ^ 20 + (2 : ℝ) ^ 18) * Real.sqrt (2 * Real.pi) * z * Shao.standardNormalTail t := by
  dsimp only
  let p : ℝ := 1 + t
  let z : ℝ := p * ((n : ℝ) * |∫ a : ℝ, a ∂eta|) +
    p ^ 2 * |(n : ℝ) * (∫ a : ℝ, a ^ 2 ∂eta) - 1| +
    p ^ 3 * ((n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂eta))
  let f : ℝ → ℝ := fun a => t * a - t ^ 2 * a ^ 2 / 2
  let Z : ℝ := ∫ a : ℝ, Real.exp (f a) ∂eta
  let rho : Measure ℝ := eta.tilted f
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => eta)
  let T : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  let W : Shao.Path n → ℝ := fun v => Shao.prefixSum v n - t * Shao.energy v / 2 - t / 2
  let H : Shao.Path n → ℝ := fun v => if 0 ≤ W v then Real.exp (-t * W v) else 0
  let J : Shao.Path n → ℝ := fun v =>
    if -(t * (Real.sqrt (Shao.energy v) - 1) ^ 2 / 2) ≤ W v ∧ W v < 0 then Real.exp (-t * W v) else 0
  let E : ℝ := Real.exp (-(t ^ 2 / 2))
  obtain ⟨hZ, _, _, _, _, hZn, _, hidentity, hL⟩ :=
    boundedEndpoint_quadraticTilt_linear_halfspace eta n hn h t hh ht hsupport hthin hsmall
  have hRW := boundedEndpoint_quadraticTilt_random_window_explicit eta n hn h t hh ht hsupport hthin hsmall
  change Z ^ n ≤ 2 at hZn
  change (∫ v : Shao.Path n, J v ∂T) ≤ (2 : ℝ) ^ 17 * z / p at hRW
  change |Z ^ n * E * (∫ v : Shao.Path n, H v ∂T) - Shao.standardNormalTail t| ≤
    (2 : ℝ) ^ 20 * Real.sqrt (2 * Real.pi) * z * Shao.standardNormalTail t at hL
  change P.real {v : Shao.Path n | t * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v n} =
    Z ^ n * E * ((∫ v : Shao.Path n, H v ∂T) + (∫ v : Shao.Path n, J v ∂T)) at hidentity
  have hz : 0 ≤ z := by dsimp [z, p]; positivity
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hJ0 : 0 ≤ ∫ v : Shao.Path n, J v ∂T := integral_nonneg fun v => by dsimp [J]; split_ifs <;> positivity
  have hZn0 : 0 ≤ Z ^ n := pow_nonneg (le_of_lt hZ) n
  have hformula : E = Real.sqrt (2 * Real.pi) * Shao.standardNormalDensity t := by
    dsimp [E]
    rw [show -(t ^ 2 / 2) = -t ^ 2 / 2 by ring]
    simp only [Shao.standardNormalDensity, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
    field_simp
  have hMills : E / p ≤ Real.sqrt (2 * Real.pi) * Shao.standardNormalTail t := by
    rw [hformula, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (Shao.standardNormal_mills_bounds t ht.le).1 (Real.sqrt_nonneg _)
  have hWindow : Z ^ n * E * (∫ v : Shao.Path n, J v ∂T) ≤
      (2 : ℝ) ^ 18 * Real.sqrt (2 * Real.pi) * z * Shao.standardNormalTail t := by
    calc
      _ ≤ (2 * E) * ((2 : ℝ) ^ 17 * z / p) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hZn hE) hRW hJ0 (by positivity)
      _ = ((2 : ℝ) ^ 18 * z) * (E / p) := by norm_num; ring
      _ ≤ ((2 : ℝ) ^ 18 * z) * (Real.sqrt (2 * Real.pi) * Shao.standardNormalTail t) :=
        mul_le_mul_of_nonneg_left hMills (by positivity)
      _ = _ := by ring
  have htri : |P.real {v : Shao.Path n | t * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v n} - Shao.standardNormalTail t| ≤
      |Z ^ n * E * (∫ v : Shao.Path n, H v ∂T) - Shao.standardNormalTail t| +
        Z ^ n * E * (∫ v : Shao.Path n, J v ∂T) := by
    rw [hidentity]
    have he : Z ^ n * E * ((∫ v : Shao.Path n, H v ∂T) + (∫ v : Shao.Path n, J v ∂T)) - Shao.standardNormalTail t =
        (Z ^ n * E * (∫ v : Shao.Path n, H v ∂T) - Shao.standardNormalTail t) +
          Z ^ n * E * (∫ v : Shao.Path n, J v ∂T) := by ring
    rw [he]
    exact (abs_add_le _ _).trans_eq (by rw [abs_of_nonneg (mul_nonneg (mul_nonneg hZn0 hE) hJ0)])
  change |P.real {v : Shao.Path n | t * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v n} - Shao.standardNormalTail t| ≤
    ((2 : ℝ) ^ 20 + (2 : ℝ) ^ 18) * Real.sqrt (2 * Real.pi) * z * Shao.standardNormalTail t
  exact (htri.trans (add_le_add hL hWindow)).trans_eq (by ring)

private theorem er_reflected_weak_tail
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
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => eta)
    |P.real {v : Shao.Path n | t * Real.sqrt (Shao.energy v) ≤ -Shao.prefixSum v n} -
      Shao.standardNormalTail t| ≤
      ((2 : ℝ) ^ 20 + (2 : ℝ) ^ 18) * Real.sqrt (2 * Real.pi) * z * Shao.standardNormalTail t := by
  dsimp only
  let etaR : Measure ℝ := eta.map (fun a : ℝ => -a)
  let F : Shao.Path n → Shao.Path n := fun v i => -(v i)
  letI : IsProbabilityMeasure etaR := by
    constructor
    change eta.map (fun a : ℝ => -a) Set.univ = 1
    rw [Measure.map_apply measurable_neg MeasurableSet.univ]
    simp
  have hmean : (∫ a : ℝ, a ∂etaR) = -(∫ a : ℝ, a ∂eta) := by
    have hm : (∫ a : ℝ, a ∂etaR) = ∫ a : ℝ, -a ∂eta :=
      integral_map (μ := eta) (φ := fun a : ℝ => -a) (f := fun a : ℝ => a)
        measurable_neg.aemeasurable measurable_id.aestronglyMeasurable
    exact hm.trans (integral_neg (fun a : ℝ => a))
  have h2 : (∫ a : ℝ, a ^ 2 ∂etaR) = (∫ a : ℝ, a ^ 2 ∂eta) := by
    rw [integral_map measurable_neg.aemeasurable (by fun_prop)]
    simp only [neg_sq]
  have h3 : (∫ a : ℝ, |a| ^ 3 ∂etaR) = (∫ a : ℝ, |a| ^ 3 ∂eta) := by
    rw [integral_map measurable_neg.aemeasurable (by fun_prop)]
    simp only [abs_neg]
  have hsR : ∀ᵐ a : ℝ ∂etaR, |a| ≤ h :=
    (ae_map_iff measurable_neg.aemeasurable
      (measurableSet_le continuous_abs.measurable measurable_const)).2
      (by simpa only [abs_neg] using hsupport)
  have hsmallR :
      (1 + t) * ((n : ℝ) * |∫ a : ℝ, a ∂etaR|) +
      (1 + t) ^ 2 * |(n : ℝ) * (∫ a : ℝ, a ^ 2 ∂etaR) - 1| +
      (1 + t) ^ 3 * ((n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂etaR)) ≤ 1 / 1000 := by
    rw [hmean, h2, h3, abs_neg]
    exact hsmall
  have hR := er_bounded_weak_tail etaR n hn h t hh ht hsR hthin hsmallR
  dsimp only at hR
  rw [hmean, h2, h3, abs_neg] at hR
  have hFm : Measurable F := Measurable.of_eval fun i => (measurable_pi_apply i).neg
  have hmap : (Measure.pi (fun _ : Fin n => eta)).map F =
      Measure.pi (fun _ : Fin n => etaR) :=
    Measure.pi_map_pi (fun _ : Fin n => measurable_neg.aemeasurable)
  have hEm : MeasurableSet {v : Shao.Path n | t * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v n} :=
    measurableSet_le (Shao.measurable_energy.sqrt.const_mul t) (Shao.measurable_prefixSum n)
  rw [← hmap, Measure.real_def, Measure.map_apply hFm hEm] at hR
  have hset : F ⁻¹' {v : Shao.Path n | t * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v n} =
      {v : Shao.Path n | t * Real.sqrt (Shao.energy v) ≤ -Shao.prefixSum v n} := by
    ext v
    change (t * Real.sqrt (Shao.energy (-v)) ≤ Shao.prefixSum (-v) n) ↔ _
    rw [Shao.energy_neg, Shao.prefixSum_neg]
    rfl
  rw [hset] at hR
  exact hR

private theorem er_strict_endpoint_two_tail_identity
    (n : ℕ) (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (t : ℝ) (ht : 0 < t) :
    P.real {v : Shao.Path n | 0 < Shao.energy v ∧
      |Shao.prefixSum v n| < t * Real.sqrt (Shao.energy v)} =
      1 - P.real {v : Shao.Path n | t * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v n} -
        P.real {v : Shao.Path n | t * Real.sqrt (Shao.energy v) ≤ -Shao.prefixSum v n} +
        P.real {v : Shao.Path n | Shao.energy v = 0} := by
  let U : Set (Shao.Path n) := {v | t * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v n}
  let L : Set (Shao.Path n) := {v | t * Real.sqrt (Shao.energy v) ≤ -Shao.prefixSum v n}
  let A : Set (Shao.Path n) := {v | 0 < Shao.energy v ∧ |Shao.prefixSum v n| < t * Real.sqrt (Shao.energy v)}
  have hUm : MeasurableSet U := measurableSet_le
    (Shao.measurable_energy.sqrt.const_mul t) (Shao.measurable_prefixSum n)
  have hLm : MeasurableSet L := measurableSet_le
    (Shao.measurable_energy.sqrt.const_mul t) (Shao.measurable_prefixSum n).neg
  have hQ (v : Shao.Path n) : 0 ≤ Shao.energy v := Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  have hinter : U ∩ L = {v : Shao.Path n | Shao.energy v = 0} := by
    ext v
    change (t * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v n ∧
      t * Real.sqrt (Shao.energy v) ≤ -Shao.prefixSum v n) ↔ Shao.energy v = 0
    constructor
    · rintro ⟨h1, h2⟩
      have hh : t * Real.sqrt (Shao.energy v) ≤ 0 := by linarith only [h1, h2]
      have he : t * Real.sqrt (Shao.energy v) = 0 := le_antisymm hh (mul_nonneg ht.le (Real.sqrt_nonneg _))
      have hs : Real.sqrt (Shao.energy v) = 0 := (mul_eq_zero.1 he).resolve_left ht.ne'
      nlinarith only [Real.sq_sqrt (hQ v), hs]
    · intro hv
      have hs := Shao.prefixSum_eq_zero_of_energy_eq_zero v hv n
      rw [hv, hs]
      norm_num
  have hcompl : A = (U ∪ L)ᶜ := by
    ext v
    change (0 < Shao.energy v ∧ |Shao.prefixSum v n| < t * Real.sqrt (Shao.energy v)) ↔
      ¬(t * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v n ∨
        t * Real.sqrt (Shao.energy v) ≤ -Shao.prefixSum v n)
    constructor
    · intro hv hh
      have hb := abs_lt.1 hv.2
      rcases hh with hh | hh <;> linarith only [hb.1, hb.2, hh]
    · intro hh
      have h1 : Shao.prefixSum v n < t * Real.sqrt (Shao.energy v) := lt_of_not_ge (fun hu => hh (Or.inl hu))
      have h2 : -Shao.prefixSum v n < t * Real.sqrt (Shao.energy v) := lt_of_not_ge (fun hl => hh (Or.inr hl))
      have hpos : 0 < Shao.energy v := by
        by_contra h
        have he : Shao.energy v = 0 := le_antisymm (le_of_not_gt h) (hQ v)
        have hs := Shao.prefixSum_eq_zero_of_energy_eq_zero v he n
        rw [he, hs] at h1
        norm_num at h1
      exact ⟨hpos, abs_lt.2 ⟨by linarith only [h2], h1⟩⟩
  have hc := measureReal_compl (μ := P) (hUm.union hLm)
  rw [probReal_univ, ← hcompl] at hc
  have hu := measureReal_union_add_inter₀ (μ := P) (s := U) hLm.nullMeasurableSet
  rw [hinter] at hu
  change P.real A = 1 - P.real U - P.real L + P.real {v : Shao.Path n | Shao.energy v = 0}
  linarith only [hc, hu]

private theorem er_source_second_moment_error
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : Shao.truncationBudget nu n x ≤ epsilon ^ 3 / 8) :
    let rho : Measure ℝ := ProbabilityTheory.cond nu {z : ℝ | |z| ≤ epsilon / (1 + x)}
    |(n : ℝ) * (∫ z : ℝ, z ^ 2 ∂rho) - 1| ≤
      3 * Shao.truncationBudget nu n x / (epsilon * (1 + x) ^ 2) := by
  let a : ℝ := 1 + x
  let b : ℝ := a / epsilon
  let r : ℝ := Shao.truncationBudget nu n x
  let B : Set ℝ := {z | |z| ≤ epsilon / a}
  let rho : Measure ℝ := ProbabilityTheory.cond nu B
  let qB : ℝ := nu.real B
  let m : ℝ := nu.real Bᶜ
  let T2 : ℝ := (n : ℝ) * (∫ z : ℝ in Bᶜ, z ^ 2 ∂nu)
  have ha : 0 < a := by dsimp [a]; linarith only [hx]
  have hr : 0 ≤ r := Shao.truncationBudget_nonneg nu n h2 x
  have hB : MeasurableSet B := measurableSet_le continuous_abs.measurable measurable_const
  have hBc : Bᶜ = {z : ℝ | epsilon / a < |z|} := by ext z; simp [B]
  have hd := Shao.sourceTruncation_law_data nu n h2 hnorm x epsilon hx hepsilon hepsilonHalf hR
  have hqB34 : (3 / 4 : ℝ) ≤ qB := hd.1
  have hqB : 0 < qB := by linarith only [hqB34]
  have hp := Shao.sourceTruncation_reparameterization nu n h2 x epsilon hx hepsilon (by linarith only [hepsilonHalf])
  have hset : Shao.retainedCutoffSet b = B := hp.2.1
  have hlaw : Shao.retainedCutoffLaw nu b = rho := hp.2.2.1
  have hmass : Shao.retainedCutoffMass nu b = qB := by
    change nu.real (Shao.retainedCutoffSet b) = qB
    rw [hset]
  obtain ⟨hb2, hb6, _, _⟩ := Shao.sourceTruncation_sample_size nu n h2 hnorm x epsilon hx hepsilon hepsilonHalf hR
  change 2 ≤ b at hb2
  change b ^ 6 ≤ (n : ℝ) at hb6
  have hb4 : 1 ≤ b ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (show 1 ≤ b by linarith only [hb2]) 4
    simpa only [one_pow] using h
  have hb2N : b ^ 2 ≤ (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hb4 (sq_nonneg b)
    nlinarith only [h, hb6]
  have hNe2 : a ^ 2 ≤ (n : ℝ) * epsilon ^ 2 := by
    dsimp only [b] at hb2N
    rw [div_pow] at hb2N
    exact (div_le_iff₀ (sq_pos_of_pos hepsilon)).1 hb2N
  have hNe3 : epsilon * a ^ 2 ≤ (n : ℝ) * epsilon ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hNe2 hepsilon.le
    nlinarith only [h]
  have ht := Shao.sourceTruncation_tail_budget nu n h2 x epsilon hx hepsilon (by linarith only [hepsilonHalf])
  have hmN : (n : ℝ) * m ≤ r / epsilon ^ 3 := by
    dsimp only [m]
    rw [hBc]
    exact ht.1
  have hm0 : 0 ≤ m := measureReal_nonneg
  have hm : m ≤ r / (epsilon * a ^ 2) := by
    apply (le_div_iff₀ (mul_pos hepsilon (sq_pos_of_pos ha))).2
    have h1 := (le_div_iff₀ (pow_pos hepsilon 3)).1 hmN
    have h2 := mul_le_mul_of_nonneg_right hNe3 hm0
    nlinarith only [h1, h2]
  have htailInt : (∫ z : ℝ in Bᶜ, z ^ 2 ∂nu) =
      ∫ z : ℝ, (if epsilon / a < |z| then z ^ 2 else 0) ∂nu := by
    rw [hBc, ← integral_indicator (measurableSet_lt measurable_const continuous_abs.measurable)]
    rfl
  have hT2 : T2 ≤ r / (epsilon * a ^ 2) := by
    dsimp only [T2]
    rw [htailInt]
    exact ht.2.2
  have hT20 : 0 ≤ T2 := mul_nonneg (Nat.cast_nonneg n) (integral_nonneg fun z => sq_nonneg z)
  have hcond := Shao.integral_retainedCutoffLaw nu b (by rw [hmass]; exact hqB)
    (fun z : ℝ => z ^ 2) h2.restrict
  rw [hlaw, hset, hmass] at hcond
  have hsplit := integral_add_compl hB h2
  have hnormB : (n : ℝ) * (∫ z : ℝ in B, z ^ 2 ∂nu) = 1 - T2 := by
    have h := congrArg (fun y : ℝ => (n : ℝ) * y) hsplit
    dsimp only [T2]
    nlinarith only [h, hnorm]
  have hformula : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂rho) = (1 - T2) / qB := by
    rw [hcond]
    calc
      _ = ((n : ℝ) * (∫ z : ℝ in B, z ^ 2 ∂nu)) / qB := by ring
      _ = _ := by rw [hnormB]
  have hc : m = 1 - qB := by
    have h := measureReal_compl (μ := nu) hB
    rw [probReal_univ] at h
    exact h
  have he : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂rho) - 1 = (m - T2) / qB := by
    rw [hformula, hc]
    field_simp [hqB.ne'] <;> ring
  have habs : |m - T2| ≤ m + T2 := by
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg hm0, abs_of_nonneg hT20])
  have hnum : m + T2 ≤ 3 * qB * (r / (epsilon * a ^ 2)) := by
    calc
      _ ≤ 2 * (r / (epsilon * a ^ 2)) := by linarith only [hm, hT2]
      _ ≤ _ := mul_le_mul_of_nonneg_right (show 2 ≤ 3 * qB by linarith only [hqB34])
        (div_nonneg hr (mul_nonneg hepsilon.le (sq_nonneg a)))
  change |(n : ℝ) * (∫ z : ℝ, z ^ 2 ∂rho) - 1| ≤ 3 * r / (epsilon * a ^ 2)
  rw [he, abs_div, abs_of_pos hqB]
  calc
    _ ≤ (m + T2) / qB := div_le_div_of_nonneg_right habs hqB.le
    _ ≤ (3 * qB * (r / (epsilon * a ^ 2))) / qB := div_le_div_of_nonneg_right hnum hqB.le
    _ = _ := by field_simp [hqB.ne'] <;> ring

private theorem er_source_endpoint_inputs
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 800)
    (hR : Shao.truncationBudget nu n x ≤ epsilon ^ 3 / 8)
    (t : ℝ) (ht : 0 < t) (hnear : |t - x| ≤ 1 / (1 + x)) :
    let r : ℝ := Shao.truncationBudget nu n x
    let rho : Measure ℝ := ProbabilityTheory.cond nu {z : ℝ | |z| ≤ epsilon / (1 + x)}
    let h : ℝ := epsilon / (1 + x)
    let mu : ℝ := ∫ a : ℝ, a ∂rho
    let q : ℝ := (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂rho)
    let beta : ℝ := (n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂rho)
    let z : ℝ := (1 + t) * ((n : ℝ) * |mu|) +
      (1 + t) ^ 2 * |q - 1| + (1 + t) ^ 3 * beta
    let K : ℝ := 4 / epsilon ^ 2 + 12 / epsilon + 16
    IsProbabilityMeasure rho ∧ 1 ≤ n ∧ 0 < h ∧
      (∀ᵐ a : ℝ ∂rho, |a| ≤ h) ∧ t * h ≤ 1 / 800 ∧
      z ≤ 1 / 1000 ∧ z ≤ K * r := by
  let a : ℝ := 1 + x
  let p : ℝ := 1 + t
  let r : ℝ := Shao.truncationBudget nu n x
  let rho : Measure ℝ := ProbabilityTheory.cond nu {z : ℝ | |z| ≤ epsilon / a}
  let h : ℝ := epsilon / a
  let mu : ℝ := ∫ a : ℝ, a ∂rho
  let q : ℝ := (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂rho)
  let beta : ℝ := (n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂rho)
  let z : ℝ := p * ((n : ℝ) * |mu|) + p ^ 2 * |q - 1| + p ^ 3 * beta
  let K : ℝ := 4 / epsilon ^ 2 + 12 / epsilon + 16
  have ha1 : 1 ≤ a := by dsimp [a]; linarith only [hx]
  have ha : 0 < a := by linarith only [ha1]
  have hp : 0 < p := by dsimp [p]; linarith only [ht]
  have hr : 0 ≤ r := Shao.truncationBudget_nonneg nu n h2 x
  have heHalf : epsilon ≤ 1 / 2 := by linarith only [hepsilonSmall]
  obtain ⟨_, _, hprob, hs, _, _, _, _⟩ :=
    Shao.sourceTruncation_law_data nu n h2 hnorm x epsilon hx hepsilon heHalf hR
  obtain ⟨_, _, hn64, _⟩ := Shao.sourceTruncation_sample_size nu n h2 hnorm x epsilon hx hepsilon heHalf hR
  have hn : 1 ≤ n := by omega
  have hh : 0 < h := div_pos hepsilon ha
  have hpa : p ≤ 2 * a := by
    have htδ : t - x ≤ 1 / a := (le_abs_self _).trans hnear
    have h1a : 1 / a ≤ 1 := (div_le_iff₀ ha).2 (by simpa only [one_mul] using ha1)
    dsimp [p, a] at *
    linarith only [htδ, h1a, hx]
  have htA : t ≤ a := by
    have htδ : t - x ≤ 1 / a := (le_abs_self _).trans hnear
    have h1a : 1 / a ≤ 1 := (div_le_iff₀ ha).2 (by simpa only [one_mul] using ha1)
    dsimp only [a]
    linarith only [htδ, h1a]
  have hthin : t * h ≤ 1 / 800 := by
    have h1 : t * h ≤ epsilon := by
      dsimp only [h]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ ha).2
      have hm := mul_le_mul_of_nonneg_right htA hepsilon.le
      nlinarith only [hm]
    exact h1.trans hepsilonSmall
  have hpaid := Shao.sourceTruncation_paid_moments nu n h2 hnorm hmean x epsilon hx hepsilon heHalf hR
  have hm : (n : ℝ) * |mu| ≤ 2 * r / (epsilon ^ 2 * a) := hpaid.1
  have hb : beta ≤ 2 * r / a ^ 3 := hpaid.2.1
  have hq : |q - 1| ≤ 3 * r / (epsilon * a ^ 2) :=
    er_source_second_moment_error nu n h2 hnorm x epsilon hx hepsilon heHalf hR
  have hb0 : 0 ≤ beta := mul_nonneg (Nat.cast_nonneg n) (integral_nonneg fun a => pow_nonneg (abs_nonneg a) 3)
  have h1 : p * ((n : ℝ) * |mu|) ≤ 4 * r / epsilon ^ 2 := by
    calc
      _ ≤ (2 * a) * (2 * r / (epsilon ^ 2 * a)) :=
        mul_le_mul hpa hm (by positivity) (by positivity)
      _ = _ := by field_simp [ha.ne', hepsilon.ne'] <;> ring
  have h2q : p ^ 2 * |q - 1| ≤ 12 * r / epsilon := by
    calc
      _ ≤ (2 * a) ^ 2 * (3 * r / (epsilon * a ^ 2)) :=
        mul_le_mul (pow_le_pow_left₀ hp.le hpa 2) hq (abs_nonneg _) (by positivity)
      _ = _ := by field_simp [ha.ne', hepsilon.ne'] <;> ring
  have h3b : p ^ 3 * beta ≤ 16 * r := by
    calc
      _ ≤ (2 * a) ^ 3 * (2 * r / a ^ 3) :=
        mul_le_mul (pow_le_pow_left₀ hp.le hpa 3) hb hb0 (by positivity)
      _ = _ := by field_simp [ha.ne'] <;> ring
  have hzK : z ≤ K * r := by
    calc
      _ ≤ 4 * r / epsilon ^ 2 + 12 * r / epsilon + 16 * r := by dsimp only [z]; linarith only [h1, h2q, h3b]
      _ = _ := by dsimp [K]; ring
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsmallNum : K * r ≤ epsilon / 2 + (3 / 2 : ℝ) * epsilon ^ 2 + 2 * epsilon ^ 3 := by
    calc
      _ ≤ K * (epsilon ^ 3 / 8) := mul_le_mul_of_nonneg_left hR hK
      _ = _ := by dsimp [K]; field_simp [hepsilon.ne'] <;> ring
  have he2 := pow_le_pow_left₀ hepsilon.le hepsilonSmall 2
  have he3 := pow_le_pow_left₀ hepsilon.le hepsilonSmall 3
  have hzSmall : z ≤ 1 / 1000 := by
    have h := hzK.trans hsmallNum
    norm_num at he2 he3
    nlinarith only [h, hepsilonSmall, he2, he3]
  exact ⟨hprob, hn, hh, hs, hthin, hzSmall, hzK⟩

theorem sourceTruncation_endpoint_relative_error :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 / 800 →
      ∃ Ce : ℝ, 0 ≤ Ce ∧
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ),
          Integrable (fun z : ℝ => z ^ 2) nu →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
          (∫ z : ℝ, z ∂nu) = 0 →
          ∀ x : ℝ, 0 < x →
            Shao.truncationBudget nu n x ≤ epsilon ^ 3 / 8 →
            let rho : Measure ℝ := ProbabilityTheory.cond nu
              {z : ℝ | |z| ≤ epsilon / (1 + x)}
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            let G : ℝ → ℝ := fun t =>
              if 0 < t then 1 - 2 * Shao.standardNormalTail t else 0
            ∀ t : ℝ, |t - x| ≤ 1 / (1 + x) →
              |P.real {v : Shao.Path n |
                0 < Shao.energy v ∧
                  |Shao.prefixSum v n| < t * Real.sqrt (Shao.energy v)} - G t| ≤
                Ce * Shao.truncationBudget nu n x * Shao.standardNormalTail x := by
  intro epsilon hepsilon hepsilonSmall
  let K : ℝ := 4 / epsilon ^ 2 + 12 / epsilon + 16
  let Cs : ℝ := ((2 : ℝ) ^ 20 + (2 : ℝ) ^ 18) * Real.sqrt (2 * Real.pi)
  let Ce : ℝ := 2 * Cs * K * Real.exp 2 + Real.sqrt (2 * Real.pi)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  have hCe : 0 ≤ Ce := by dsimp [Ce]; positivity
  refine ⟨Ce, hCe, ?_⟩
  intro nu hnu n h2 hnorm hmean x hx hR
  letI : IsProbabilityMeasure nu := hnu
  dsimp only
  let r : ℝ := Shao.truncationBudget nu n x
  let rho : Measure ℝ := ProbabilityTheory.cond nu {z : ℝ | |z| ≤ epsilon / (1 + x)}
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  obtain ⟨hr, hprob, hprobP, _, hQ0⟩ := sourceTruncation_endpoint_zero_energy_gaussian_cost
    nu n h2 hnorm hmean x epsilon hx.le hepsilon hepsilonSmall hR
  change 0 < r at hr
  change IsProbabilityMeasure rho at hprob
  change IsProbabilityMeasure P at hprobP
  letI : IsProbabilityMeasure rho := hprob
  letI : IsProbabilityMeasure P := hprobP
  change P.real {v : Shao.Path n | Shao.energy v = 0} ≤
    Real.sqrt (2 * Real.pi) * r * Shao.standardNormalTail x at hQ0
  have htailx : 0 < Shao.standardNormalTail x := (Shao.standardNormalTail_basic.2.2.1 x).1
  intro t hnear
  change |P.real {v : Shao.Path n | 0 < Shao.energy v ∧
      |Shao.prefixSum v n| < t * Real.sqrt (Shao.energy v)} -
      (if 0 < t then 1 - 2 * Shao.standardNormalTail t else 0)| ≤ Ce * r * Shao.standardNormalTail x
  by_cases ht : 0 < t
  · rw [if_pos ht]
    let h : ℝ := epsilon / (1 + x)
    let z : ℝ := (1 + t) * ((n : ℝ) * |∫ a : ℝ, a ∂rho|) +
      (1 + t) ^ 2 * |(n : ℝ) * (∫ a : ℝ, a ^ 2 ∂rho) - 1| +
      (1 + t) ^ 3 * ((n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂rho))
    let U : Set (Shao.Path n) := {v | t * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v n}
    let L : Set (Shao.Path n) := {v | t * Real.sqrt (Shao.energy v) ≤ -Shao.prefixSum v n}
    let A : Set (Shao.Path n) := {v | 0 < Shao.energy v ∧ |Shao.prefixSum v n| < t * Real.sqrt (Shao.energy v)}
    let Q0 : Set (Shao.Path n) := {v | Shao.energy v = 0}
    obtain ⟨_, hn, hh, hs, hthin, hsmall, hzK⟩ :=
      er_source_endpoint_inputs nu n h2 hnorm hmean x epsilon hx.le hepsilon hepsilonSmall hR t ht hnear
    change 0 < h at hh
    change ∀ᵐ a : ℝ ∂rho, |a| ≤ h at hs
    change t * h ≤ 1 / 800 at hthin
    change z ≤ 1 / 1000 at hsmall
    change z ≤ K * r at hzK
    have hU := er_bounded_weak_tail rho n hn h t hh ht hs hthin hsmall
    have hL := er_reflected_weak_tail rho n hn h t hh ht hs hthin hsmall
    change |P.real U - Shao.standardNormalTail t| ≤ Cs * z * Shao.standardNormalTail t at hU
    change |P.real L - Shao.standardNormalTail t| ≤ Cs * z * Shao.standardNormalTail t at hL
    have htailt : 0 < Shao.standardNormalTail t := (Shao.standardNormalTail_basic.2.2.1 t).1
    have hratio := (Shao.standardNormalTail_local_comparison x t hx.le ht.le hnear).2
    have hPay : Cs * z * Shao.standardNormalTail t ≤ Cs * K * r * Real.exp 2 * Shao.standardNormalTail x := by
      have h := mul_le_mul (mul_le_mul_of_nonneg_left hzK hCs) hratio htailt.le
        (mul_nonneg hCs (mul_nonneg hK hr.le))
      exact h.trans_eq (by ring)
    have hU' := hU.trans hPay
    have hL' := hL.trans hPay
    have hid := er_strict_endpoint_two_tail_identity n P t ht
    change P.real A = 1 - P.real U - P.real L + P.real Q0 at hid
    have hdecomp : P.real A - (1 - 2 * Shao.standardNormalTail t) =
        (-(P.real U - Shao.standardNormalTail t) + -(P.real L - Shao.standardNormalTail t)) + P.real Q0 := by
      rw [hid]
      ring
    have hQ00 : 0 ≤ P.real Q0 := measureReal_nonneg
    have htri : |P.real A - (1 - 2 * Shao.standardNormalTail t)| ≤
        |P.real U - Shao.standardNormalTail t| + |P.real L - Shao.standardNormalTail t| + P.real Q0 := by
      rw [hdecomp]
      have h1 := abs_add_le
        (-(P.real U - Shao.standardNormalTail t) + -(P.real L - Shao.standardNormalTail t)) (P.real Q0)
      have h2 := abs_add_le (-(P.real U - Shao.standardNormalTail t)) (-(P.real L - Shao.standardNormalTail t))
      simp only [abs_neg, abs_of_nonneg hQ00] at h1 h2
      linarith only [h1, h2]
    change |P.real A - (1 - 2 * Shao.standardNormalTail t)| ≤ Ce * r * Shao.standardNormalTail x
    calc
      _ ≤ (Cs * K * r * Real.exp 2 * Shao.standardNormalTail x) +
          (Cs * K * r * Real.exp 2 * Shao.standardNormalTail x) +
          Real.sqrt (2 * Real.pi) * r * Shao.standardNormalTail x :=
        htri.trans (add_le_add (add_le_add hU' hL') hQ0)
      _ = _ := by dsimp only [Ce]; ring
  · have htnon : t ≤ 0 := le_of_not_gt ht
    have hempty : {v : Shao.Path n | 0 < Shao.energy v ∧
        |Shao.prefixSum v n| < t * Real.sqrt (Shao.energy v)} = ∅ := by
      ext v
      constructor
      · intro hv
        have hh := mul_nonpos_of_nonpos_of_nonneg htnon (Real.sqrt_nonneg (Shao.energy v))
        have h0 := abs_nonneg (Shao.prefixSum v n)
        exact False.elim (by linarith only [hv.2, hh, h0])
      · intro hv
        exact False.elim hv
    rw [hempty, measureReal_empty, if_neg ht]
    simpa only [sub_zero, abs_zero] using mul_nonneg (mul_nonneg hCe hr.le) htailx.le

end Shao.Probability
