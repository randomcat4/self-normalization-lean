import Shao.Probability.QuadraticCharacteristicPower
import Shao.Probability.LowFrequencyDamping
import Mathlib.Algebra.Ring.GeomSum

/-!
Real-frequency odd differences of powers of the actual quadratic characteristic
integral. The law is fixed and need not be centered. All power formulas are
polynomial, including at zero characteristic values and at small exponents.
-/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private lemma odd_moments {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) :
    Integrable (fun a : ℝ => a) ν ∧ Integrable (fun a : ℝ => a ^ 2) ν := by
  have hb := (integrable_const (1 : ℝ)).add h3
  have hp (a : ℝ) : |a| ≤ 1 + |a| ^ 3 ∧ a ^ 2 ≤ 1 + |a| ^ 3 := by
    have ha := abs_nonneg a
    have ha2 := sq_abs a
    by_cases h : |a| ≤ 1
    · constructor <;> nlinarith [sq_nonneg |a|, pow_nonneg ha 3]
    · have hh : 1 ≤ |a| := le_of_not_ge h
      constructor <;> nlinarith [sq_nonneg (|a| - 1),
        mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg |a|)]
  constructor
  · exact hb.mono' measurable_id.aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => by simpa using (hp a).1)
  · exact hb.mono' (by fun_prop) (Filter.Eventually.of_forall fun a => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)] using (hp a).2)

private lemma single_hasDerivAt (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (u v : ℝ) :
    HasDerivAt (fun r : ℝ => quadraticChar ν r v)
      (Complex.I * ∫ a : ℝ, (a : ℂ) *
        Complex.exp (((u * a + v * a ^ 2 : ℝ) : ℂ) * Complex.I) ∂ν) u := by
  have hi : iIndepFun (fun _ : Fin 1 => (id : ℝ → ℝ)) ν :=
    iIndepFun.of_subsingleton
  have hd := iid_quadraticChar_power_hasDerivAt
    (X := fun _ : Fin 1 => (id : ℝ → ℝ)) (fun _ => measurable_id) hi
    (fun _ => IdentDistrib.refl measurable_id.aemeasurable) h2 u v
  simpa [Shao.prefixSum, samplePath, Shao.energy] using hd

private lemma single_deriv_hasDerivAt (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (u v : ℝ) :
    HasDerivAt (fun r : ℝ => deriv (fun s : ℝ => quadraticChar ν s v) r)
      (deriv (fun r : ℝ => deriv (fun s : ℝ => quadraticChar ν s v) r) u) u := by
  have hi : iIndepFun (fun _ : Fin 1 => (id : ℝ → ℝ)) ν :=
    iIndepFun.of_subsingleton
  have hd := iid_quadraticChar_power_deriv_hasDerivAt
    (X := fun _ : Fin 1 => (id : ℝ → ℝ)) (fun _ => measurable_id) hi
    (fun _ => IdentDistrib.refl measurable_id.aemeasurable) h2 u v
  simpa only [pow_one] using hd.differentiableAt.hasDerivAt

private lemma full_weight_integrable {ν : Measure ℝ}
    (h1 : Integrable (fun a : ℝ => a) ν) (u v : ℝ) :
    Integrable (fun a : ℝ => (a : ℂ) *
      Complex.exp (((u * a + v * a ^ 2 : ℝ) : ℂ) * Complex.I)) ν := by
  refine h1.norm.mono' ((h1.ofReal (𝕜 := ℂ)).aestronglyMeasurable.mul
    (by fun_prop)) (Filter.Eventually.of_forall fun a => ?_)
  have hn (t : ℝ) : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 := by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, Real.exp_zero]
  rw [norm_mul, hn, mul_one, Complex.norm_real]

theorem quadraticChar_single_derivative_bounds (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) (u v : ℝ) :
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let f : ℝ → ℂ := fun r => quadraticChar ν r v
    ‖deriv f u - Complex.I * (μ : ℂ)‖ ≤ m2 * |u| + m3 * |v| ∧
      ‖deriv (fun r : ℝ => deriv f r) u‖ ≤ m2 := by
  dsimp only
  obtain ⟨h1, h2⟩ := odd_moments h3
  constructor
  · rw [(single_hasDerivAt ν h2 u v).deriv, ← mul_sub, norm_mul,
      Complex.norm_I, one_mul]
    have he : (∫ a : ℝ, (a : ℂ) *
        Complex.exp (((u * a + v * a ^ 2 : ℝ) : ℂ) * Complex.I) ∂ν) -
        ((∫ a : ℝ, a ∂ν : ℝ) : ℂ) =
        ∫ a : ℝ, (a : ℂ) *
          (Complex.exp (((u * a + v * a ^ 2 : ℝ) : ℂ) * Complex.I) - 1) ∂ν := by
      have hr : (∫ a : ℝ, (a : ℂ) ∂ν) = ((∫ a : ℝ, a ∂ν : ℝ) : ℂ) :=
        integral_ofReal
      rw [← hr]
      calc
        _ = ∫ a : ℝ, ((a : ℂ) *
            Complex.exp (((u * a + v * a ^ 2 : ℝ) : ℂ) * Complex.I) - (a : ℂ)) ∂ν :=
          (integral_sub (full_weight_integrable h1 u v) (h1.ofReal (𝕜 := ℂ))).symm
        _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun a => by ring)
    rw [he]
    calc
      _ ≤ ∫ a : ℝ, |u| * a ^ 2 + |v| * |a| ^ 3 ∂ν := by
        refine norm_integral_le_of_norm_le ((h2.const_mul _).add (h3.const_mul _))
          (Filter.Eventually.of_forall fun a => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hb : ‖Complex.exp (((u * a + v * a ^ 2 : ℝ) : ℂ) * Complex.I) - 1‖ ≤
            |u * a + v * a ^ 2| := by
          simpa only [mul_comm, Real.norm_eq_abs] using
            (Real.norm_exp_I_mul_ofReal_sub_one_le (x := u * a + v * a ^ 2))
        calc
          _ ≤ |a| * |u * a + v * a ^ 2| :=
            mul_le_mul_of_nonneg_left hb (abs_nonneg a)
          _ ≤ |a| * (|u * a| + |v * a ^ 2|) :=
            mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg a)
          _ = _ := by rw [abs_mul, abs_mul, abs_pow, ← sq_abs a]; ring
      _ = _ := by
        rw [integral_add (h2.const_mul _) (h3.const_mul _), integral_const_mul,
          integral_const_mul]
        ring
  · have hb := (quadraticChar_power_derivative_bounds ν h2 1 u v).2
    simpa only [pow_one, Nat.cast_one, one_mul, one_pow, sub_add_cancel] using hb

private lemma bounded_power_difference (x y : ℂ) (q a : ℝ)
    (hq : 0 ≤ q) (hx : ‖x‖ ≤ q) (hy : ‖y‖ ≤ q) (ha : ‖x - y‖ ≤ a)
    (k : ℕ) : ‖x ^ k - y ^ k‖ ≤ (k : ℝ) * a * q ^ (k - 1) := by
  have hs : ‖∑ i ∈ Finset.range k, x ^ i * y ^ (k - 1 - i)‖ ≤
      (k : ℝ) * q ^ (k - 1) := by
    calc
      _ ≤ ∑ i ∈ Finset.range k, ‖x ^ i * y ^ (k - 1 - i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range k, q ^ (k - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, norm_pow, norm_pow]
        have hex : i + (k - 1 - i) = k - 1 := by
          have := Finset.mem_range.mp hi
          omega
        calc
          _ ≤ q ^ i * q ^ (k - 1 - i) := by gcongr
          _ = _ := by rw [← pow_add, hex]
      _ = _ := by simp
  rw [← geom_sum₂_mul, norm_mul]
  calc
    _ ≤ ((k : ℝ) * q ^ (k - 1)) * a :=
      mul_le_mul hs ha (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq _))
    _ = _ := by ring

private lemma second_power_hasDerivAt (f : ℝ → ℂ)
    (hf : ∀ r, HasDerivAt f (deriv f r) r)
    (u : ℝ) (hff : HasDerivAt (fun r => deriv f r)
      (deriv (fun r => deriv f r) u) u) (k : ℕ) :
    HasDerivAt (fun r => deriv (fun s => f s ^ k) r)
      ((k : ℂ) * f u ^ (k - 1) * deriv (fun r => deriv f r) u +
      (k : ℂ) * ((k - 1 : ℕ) : ℂ) * f u ^ (k - 2) * (deriv f u) ^ 2) u := by
  have hfirst (r : ℝ) : deriv (fun s => f s ^ k) r =
      (k : ℂ) * f r ^ (k - 1) * deriv f r := (hf r |>.pow k).deriv
  have hd := (((hf u).pow (k - 1)).mul hff).const_mul (k : ℂ)
  have he : HasDerivAt (fun r => deriv (fun s => f s ^ k) r)
      ((k : ℂ) * (((k - 1 : ℕ) : ℂ) * f u ^ (k - 1 - 1) * deriv f u *
        deriv f u + f u ^ (k - 1) * deriv (fun r => deriv f r) u)) u := by
    convert hd using 1
    funext r
    dsimp
    rw [hfirst]
    ring
  convert he using 1
  simp only [Nat.sub_sub]
  ring

private lemma bounded_power_first (x y xp yp : ℂ) (q a0 a1 L : ℝ)
    (hq : 0 ≤ q) (hx : ‖x‖ ≤ q) (hy : ‖y‖ ≤ q)
    (h0 : ‖x - y‖ ≤ a0) (h1 : ‖xp - yp‖ ≤ a1)
    (hyp : ‖yp‖ ≤ L) (k : ℕ) :
    ‖(k : ℂ) * x ^ (k - 1) * xp - (k : ℂ) * y ^ (k - 1) * yp‖ ≤
      (k : ℝ) * a1 * q ^ (k - 1) +
        (k : ℝ) * ((k - 1 : ℕ) : ℝ) * L * a0 * q ^ (k - 2) := by
  have ha0 := (norm_nonneg (x - y)).trans h0
  have ha1 := (norm_nonneg (xp - yp)).trans h1
  have hL := (norm_nonneg yp).trans hyp
  have hp := bounded_power_difference x y q a0 hq hx hy h0 (k - 1)
  simp only [Nat.sub_sub] at hp
  have hs : ‖(xp - yp) * x ^ (k - 1) + yp * (x ^ (k - 1) - y ^ (k - 1))‖ ≤
      a1 * q ^ (k - 1) + L * (((k - 1 : ℕ) : ℝ) * a0 * q ^ (k - 2)) := by
    calc
      _ ≤ ‖(xp - yp) * x ^ (k - 1)‖ + ‖yp * (x ^ (k - 1) - y ^ (k - 1))‖ :=
        norm_add_le _ _
      _ ≤ _ := by simp only [norm_mul, norm_pow]; gcongr
  calc
    _ = ‖(k : ℂ) * ((xp - yp) * x ^ (k - 1) +
        yp * (x ^ (k - 1) - y ^ (k - 1)))‖ := by congr 1; ring
    _ = (k : ℝ) * ‖(xp - yp) * x ^ (k - 1) +
        yp * (x ^ (k - 1) - y ^ (k - 1))‖ := by simp only [norm_mul, norm_natCast]
    _ ≤ _ := by
      calc
        _ ≤ (k : ℝ) * (a1 * q ^ (k - 1) +
            L * (((k - 1 : ℕ) : ℝ) * a0 * q ^ (k - 2))) :=
          mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg k)
        _ = _ := by ring

private lemma bounded_power_second (x y xp yp xpp ypp : ℂ)
    (q a0 a1 a2 L m2 : ℝ)
    (hq : 0 ≤ q) (hx : ‖x‖ ≤ q) (hy : ‖y‖ ≤ q)
    (h0 : ‖x - y‖ ≤ a0) (h1 : ‖xp - yp‖ ≤ a1)
    (h2 : ‖xpp - ypp‖ ≤ a2) (hxp : ‖xp‖ ≤ L) (hyp : ‖yp‖ ≤ L)
    (hypp : ‖ypp‖ ≤ m2) (k : ℕ) :
    ‖((k : ℂ) * x ^ (k - 1) * xpp +
        (k : ℂ) * ((k - 1 : ℕ) : ℂ) * x ^ (k - 2) * xp ^ 2) -
      ((k : ℂ) * y ^ (k - 1) * ypp +
        (k : ℂ) * ((k - 1 : ℕ) : ℂ) * y ^ (k - 2) * yp ^ 2)‖ ≤
      (k : ℝ) * a2 * q ^ (k - 1) +
        2 * (k : ℝ) * ((k - 1 : ℕ) : ℝ) * L * a1 * q ^ (k - 2) +
        (k : ℝ) * ((k - 1 : ℕ) : ℝ) * m2 * a0 * q ^ (k - 2) +
        (k : ℝ) * ((k - 1 : ℕ) : ℝ) * ((k - 2 : ℕ) : ℝ) *
          L ^ 2 * a0 * q ^ (k - 3) := by
  have ha0 := (norm_nonneg (x - y)).trans h0
  have ha1 := (norm_nonneg (xp - yp)).trans h1
  have ha2 := (norm_nonneg (xpp - ypp)).trans h2
  have hL := (norm_nonneg yp).trans hyp
  have hm := (norm_nonneg ypp).trans hypp
  have hp1 := bounded_power_difference x y q a0 hq hx hy h0 (k - 1)
  have hp2 := bounded_power_difference x y q a0 hq hx hy h0 (k - 2)
  simp only [Nat.sub_sub] at hp1 hp2
  have hsum : ‖xp + yp‖ ≤ 2 * L := (norm_add_le _ _).trans (by linarith)
  have hA : ‖(xpp - ypp) * x ^ (k - 1) +
      ypp * (x ^ (k - 1) - y ^ (k - 1))‖ ≤
      a2 * q ^ (k - 1) + m2 * (((k - 1 : ℕ) : ℝ) * a0 * q ^ (k - 2)) := by
    calc
      _ ≤ ‖(xpp - ypp) * x ^ (k - 1)‖ +
          ‖ypp * (x ^ (k - 1) - y ^ (k - 1))‖ := norm_add_le _ _
      _ ≤ _ := by simp only [norm_mul, norm_pow]; gcongr
  have hB : ‖(xp - yp) * (xp + yp) * x ^ (k - 2) +
      yp ^ 2 * (x ^ (k - 2) - y ^ (k - 2))‖ ≤
      a1 * (2 * L) * q ^ (k - 2) +
        L ^ 2 * (((k - 2 : ℕ) : ℝ) * a0 * q ^ (k - 3)) := by
    calc
      _ ≤ ‖(xp - yp) * (xp + yp) * x ^ (k - 2)‖ +
          ‖yp ^ 2 * (x ^ (k - 2) - y ^ (k - 2))‖ := norm_add_le _ _
      _ ≤ _ := by simp only [norm_mul, norm_pow]; gcongr
  calc
    _ = ‖(k : ℂ) * ((xpp - ypp) * x ^ (k - 1) +
        ypp * (x ^ (k - 1) - y ^ (k - 1))) +
        ((k : ℂ) * ((k - 1 : ℕ) : ℂ)) * ((xp - yp) * (xp + yp) * x ^ (k - 2) +
          yp ^ 2 * (x ^ (k - 2) - y ^ (k - 2)))‖ := by congr 1; ring
    _ ≤ ‖(k : ℂ) * ((xpp - ypp) * x ^ (k - 1) +
        ypp * (x ^ (k - 1) - y ^ (k - 1)))‖ +
        ‖((k : ℂ) * ((k - 1 : ℕ) : ℂ)) * ((xp - yp) * (xp + yp) * x ^ (k - 2) +
          yp ^ 2 * (x ^ (k - 2) - y ^ (k - 2)))‖ := norm_add_le _ _
    _ ≤ (k : ℝ) * (a2 * q ^ (k - 1) +
          m2 * (((k - 1 : ℕ) : ℝ) * a0 * q ^ (k - 2))) +
        ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) * (a1 * (2 * L) * q ^ (k - 2) +
          L ^ 2 * (((k - 2 : ℕ) : ℝ) * a0 * q ^ (k - 3))) := by
      simp only [norm_mul, norm_natCast]
      gcongr
    _ = _ := by ring

private lemma single_first_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) (u v : ℝ) :
    ‖deriv (fun r => quadraticChar ν r v) u‖ ≤
      |∫ a : ℝ, a ∂ν| + (∫ a : ℝ, a ^ 2 ∂ν) * |u| +
        (∫ a : ℝ, |a| ^ 3 ∂ν) * |v| := by
  have hb := (quadraticChar_single_derivative_bounds ν h3 u v).1
  have ht := norm_add_le
    (deriv (fun r => quadraticChar ν r v) u - Complex.I * ((∫ a : ℝ, a ∂ν : ℝ) : ℂ))
    (Complex.I * ((∫ a : ℝ, a ∂ν : ℝ) : ℂ))
  simp only [sub_add_cancel, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs] at ht
  linarith

theorem quadraticChar_odd_power_residual_bounds (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (ℓ : ℕ) (u v : ℝ)
    (hu : |u| ≤ (1 / 128 : ℝ) /
      ((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν))
    (hv : |v| ≤ (1 / 128 : ℝ) * |u| /
      ((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν)) :
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let q : ℝ := Real.exp (-(variance (id : ℝ → ℝ) ν) * u ^ 2 / 32)
    let a0 : ℝ := 2 * |μ| * |u| + m3 * (|u| ^ 3 / 3 + 2 * |u| * |v|)
    let a1 : ℝ := 2 * |μ| + m3 * (u ^ 2 + 2 * |v|)
    let a2 : ℝ := 2 * m3 * |u|
    let L : ℝ := |μ| + m2 * |u| + m3 * |v|
    let N : ℝ := (ℓ : ℝ)
    let N1 : ℝ := ((ℓ - 1 : ℕ) : ℝ)
    let N2 : ℝ := ((ℓ - 2 : ℕ) : ℝ)
    let d : ℝ → ℂ := fun r =>
      (quadraticChar ν r v) ^ ℓ - (quadraticChar ν (-r) v) ^ ℓ
    ‖d u‖ ≤ N * a0 * q ^ (ℓ - 1) ∧
      ‖deriv d u‖ ≤
        N * a1 * q ^ (ℓ - 1) +
          N * N1 * L * a0 * q ^ (ℓ - 2) ∧
      ‖deriv (fun r : ℝ => deriv d r) u‖ ≤
        N * a2 * q ^ (ℓ - 1) +
          2 * N * N1 * L * a1 * q ^ (ℓ - 2) +
          N * N1 * m2 * a0 * q ^ (ℓ - 2) +
          N * N1 * N2 * L ^ 2 * a0 * q ^ (ℓ - 3) := by
  dsimp only
  let f : ℝ → ℂ := fun r => quadraticChar ν r v
  let g : ℝ → ℂ := fun r => quadraticChar ν (-r) v
  have h2 := (odd_moments h3).2
  have hf (r : ℝ) : HasDerivAt f (deriv f r) r :=
    (single_hasDerivAt ν h2 r v).differentiableAt.hasDerivAt
  have hff (r : ℝ) : HasDerivAt (fun s => deriv f s)
      (deriv (fun s => deriv f s) r) r := single_deriv_hasDerivAt ν h2 r v
  have hg0 (r : ℝ) : HasDerivAt g (-(deriv f (-r))) r := by
    simpa only [Function.comp_def, neg_one_smul] using
      ((hf (-r)).scomp r (hasDerivAt_id r).neg)
  have hg (r : ℝ) : HasDerivAt g (deriv g r) r :=
    (hg0 r).differentiableAt.hasDerivAt
  have hgg0 (r : ℝ) : HasDerivAt (fun s => deriv g s)
      (deriv (fun s => deriv f s) (-r)) r := by
    have hh := (((hff (-r)).scomp r (hasDerivAt_id r).neg).neg)
    simp only [neg_one_smul, neg_neg] at hh
    exact hh.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => (hg0 s).deriv)
  have hgg (r : ℝ) : HasDerivAt (fun s => deriv g s)
      (deriv (fun s => deriv g s) r) r := (hgg0 r).differentiableAt.hasDerivAt
  have hdelta (r : ℝ) : deriv (fun s => f s - g s) r = deriv f r - deriv g r :=
    ((hf r).sub (hg r)).deriv
  have hdelta2 : deriv (fun r => deriv (fun s => f s - g s) r) u =
      deriv (fun r => deriv f r) u - deriv (fun r => deriv g r) u :=
    (((hff u).sub (hgg u)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hdelta)).deriv
  have hb := quadraticChar_odd_derivative_bounds ν h3 u v
  change ‖deriv (fun s => f s - g s) u -
      2 * Complex.I * ((∫ a : ℝ, a ∂ν : ℝ) : ℂ)‖ ≤ _ ∧
      ‖deriv (fun r => deriv (fun s => f s - g s) r) u‖ ≤ _ at hb
  rw [hdelta u] at hb
  rw [hdelta2] at hb
  have ha1 : ‖deriv f u - deriv g u‖ ≤
      2 * |∫ a : ℝ, a ∂ν| + (∫ a : ℝ, |a| ^ 3 ∂ν) * (u ^ 2 + 2 * |v|) := by
    have ht := norm_add_le (deriv f u - deriv g u -
      2 * Complex.I * ((∫ a : ℝ, a ∂ν : ℝ) : ℂ))
      (2 * Complex.I * ((∫ a : ℝ, a ∂ν : ℝ) : ℂ))
    simp only [sub_add_cancel, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs] at ht
    have hn : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [hn] at ht
    linarith [hb.1]
  have hfp := single_first_bound ν h3 u v
  have hgp : ‖deriv g u‖ ≤ |∫ a : ℝ, a ∂ν| +
      (∫ a : ℝ, a ^ 2 ∂ν) * |u| + (∫ a : ℝ, |a| ^ 3 ∂ν) * |v| := by
    rw [(hg0 u).deriv, norm_neg]
    simpa only [abs_neg] using single_first_bound ν h3 (-u) v
  have hgpp : ‖deriv (fun r => deriv g r) u‖ ≤ ∫ a : ℝ, a ^ 2 ∂ν := by
    rw [(hgg0 u).deriv]
    exact (quadraticChar_single_derivative_bounds ν h3 (-u) v).2
  have hq := quadraticChar_lowFrequency_damping ν h3 hV u v hu hv
  have hq0 := (Real.exp_pos (-(variance (id : ℝ → ℝ) ν) * u ^ 2 / 32)).le
  have h0 := quadraticChar_odd_bound ν h3 u v
  refine ⟨bounded_power_difference (f u) (g u) _ _ hq0 hq.1 hq.2 h0 ℓ, ?_, ?_⟩
  · have hd := ((hf u).pow ℓ |>.sub ((hg u).pow ℓ)).deriv
    change ‖deriv (f ^ ℓ - g ^ ℓ) u‖ ≤ _
    rw [hd]
    exact bounded_power_first (f u) (g u) (deriv f u) (deriv g u)
      _ _ _ _ hq0 hq.1 hq.2 h0 ha1 hgp ℓ
  · have hdp := second_power_hasDerivAt f hf u (hff u) ℓ
    have hdg := second_power_hasDerivAt g hg u (hgg u) ℓ
    have hderiv (r : ℝ) : deriv (fun s => f s ^ ℓ - g s ^ ℓ) r =
        deriv (fun s => f s ^ ℓ) r - deriv (fun s => g s ^ ℓ) r :=
      (((hf r).pow ℓ).differentiableAt.hasDerivAt.sub
        ((hg r).pow ℓ).differentiableAt.hasDerivAt).deriv
    have hd2 := ((hdp.sub hdg).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hderiv)).deriv
    rw [hd2]
    exact bounded_power_second (f u) (g u) (deriv f u) (deriv g u)
      (deriv (fun r => deriv f r) u) (deriv (fun r => deriv g r) u)
      _ _ _ _ _ _ hq0 hq.1 hq.2 h0 ha1 hb.2 hfp hgp hgpp ℓ

private lemma odd_third_pos (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν) :
    0 < ∫ a : ℝ, |a| ^ 3 ∂ν := by
  have hn : 0 ≤ ∫ a : ℝ, |a| ^ 3 ∂ν :=
    integral_nonneg (fun a => pow_nonneg (abs_nonneg a) 3)
  by_contra h
  have hz : (∫ a : ℝ, |a| ^ 3 ∂ν) = 0 := by linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun a => pow_nonneg (abs_nonneg a) 3) h3).mp hz
  have hid : (id : ℝ → ℝ) =ᵐ[ν] (fun _ => (0 : ℝ)) := by
    filter_upwards [hae] with a ha
    exact abs_eq_zero.mp (eq_zero_of_pow_eq_zero ha)
  have hv := variance_congr hid
  have hv0 : variance (fun _ : ℝ => (0 : ℝ)) ν = 0 := by
    rw [variance_eq_sub (memLp_const (0 : ℝ))]
    simp
  linarith

private lemma residual_exponential (ℓ j : ℕ) (hℓ : 6 ≤ ℓ) (hj : j ≤ 3)
    (V m2 u : ℝ) (hV : 0 ≤ V) (hcomp : m2 ≤ 4 * V) :
    Real.exp (-V * u ^ 2 / 32) ^ (ℓ - j) ≤
      Real.exp (-((ℓ : ℝ) * m2) * u ^ 2 / 256) := by
  have hnat : ℓ ≤ 2 * (ℓ - j) := by omega
  have hcast : (ℓ : ℝ) ≤ 2 * ((ℓ - j : ℕ) : ℝ) := by exact_mod_cast hnat
  have hc : (ℓ : ℝ) * m2 ≤ 8 * ((ℓ - j : ℕ) : ℝ) * V := by
    calc
      _ ≤ (ℓ : ℝ) * (4 * V) := mul_le_mul_of_nonneg_left hcomp (Nat.cast_nonneg _)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hcast hV]
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg u)]

private lemma normalized_drift_payment (n ℓ : ℕ) (hℓ : ℓ ≤ n)
    (μ m2 : ℝ) (hm2 : 0 ≤ m2)
    (hscale : (3 / 4 : ℝ) ≤ (n : ℝ) * m2)
    (hbias : (n : ℝ) * |μ| ≤ 1) :
    (ℓ : ℝ) * |μ| ≤ 2 * Real.sqrt ((ℓ : ℝ) * m2) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hl : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have hln : (ℓ : ℝ) ≤ n := Nat.cast_le.mpr hℓ
  have hnb : 0 ≤ (n : ℝ) * |μ| := mul_nonneg hn (abs_nonneg μ)
  have hsq : ((n : ℝ) * |μ|) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbias) (by linarith : 0 ≤ 1 + (n : ℝ) * |μ|)]
  rw [mul_pow, sq_abs] at hsq
  have hc : (n : ℝ) * μ ^ 2 ≤ (4 / 3 : ℝ) * m2 := by
    have hp := mul_le_mul_of_nonneg_right hscale (mul_nonneg hn (sq_nonneg μ))
    have hq := mul_le_mul_of_nonneg_left hsq hm2
    nlinarith [hp, hq]
  have hlsq : ((ℓ : ℝ) * |μ|) ^ 2 ≤ (4 / 3 : ℝ) * ((ℓ : ℝ) * m2) := by
    calc
      _ = (ℓ : ℝ) * ((ℓ : ℝ) * μ ^ 2) := by rw [mul_pow, sq_abs]; ring
      _ ≤ (ℓ : ℝ) * ((n : ℝ) * μ ^ 2) := by gcongr
      _ ≤ (ℓ : ℝ) * ((4 / 3 : ℝ) * m2) := mul_le_mul_of_nonneg_left hc hl
      _ = _ := by ring
  have hT := mul_nonneg hl hm2
  have hs := Real.sq_sqrt hT
  nlinarith [Real.sqrt_nonneg ((ℓ : ℝ) * m2)]

theorem quadraticChar_odd_power_lowFrequency_normalized (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (n ℓ : ℕ) (hℓ : ℓ ≤ n) (hℓ6 : 6 ≤ ℓ)
    (hscale : (3 / 4 : ℝ) ≤ (n : ℝ) * ∫ a : ℝ, a ^ 2 ∂ν)
    (hbias : (n : ℝ) * |∫ a : ℝ, a ∂ν| ≤ 1)
    (hcomp : (∫ a : ℝ, a ^ 2 ∂ν) ≤ 4 * variance (id : ℝ → ℝ) ν)
    (u v : ℝ)
    (hu : |u| ≤ (1 / 128 : ℝ) /
      ((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν))
    (hv : |v| ≤ (1 / 128 : ℝ) * |u| /
      ((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν)) :
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let T : ℝ := (ℓ : ℝ) * m2
    let A : ℝ := (ℓ : ℝ) * |μ| * |u| +
      (ℓ : ℝ) * m3 * (|u| ^ 3 + |u| * |v|)
    let B : ℝ := (ℓ : ℝ) * |μ| + (ℓ : ℝ) * m3 * (u ^ 2 + |v|)
    let R : ℝ := Real.sqrt T * (1 + Real.sqrt T * |u|)
    let E : ℝ := Real.exp (-T * u ^ 2 / 256)
    let d : ℝ → ℂ := fun r =>
      (quadraticChar ν r v) ^ ℓ - (quadraticChar ν (-r) v) ^ ℓ
    ‖d u‖ ≤ 2 * E * A ∧
      ‖deriv d u‖ ≤ 4 * E * (B + R * A) ∧
      ‖deriv (fun r : ℝ => deriv d r) u‖ ≤
        18 * E * ((ℓ : ℝ) * m3 * |u| + R * B + T * (1 + T * u ^ 2) * A) := by
  let μ : ℝ := ∫ a : ℝ, a ∂ν
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
  let V : ℝ := variance (id : ℝ → ℝ) ν
  let N : ℝ := (ℓ : ℝ)
  let N1 : ℝ := ((ℓ - 1 : ℕ) : ℝ)
  let N2 : ℝ := ((ℓ - 2 : ℕ) : ℝ)
  let T : ℝ := N * m2
  let A : ℝ := N * |μ| * |u| + N * m3 * (|u| ^ 3 + |u| * |v|)
  let B : ℝ := N * |μ| + N * m3 * (u ^ 2 + |v|)
  let R : ℝ := Real.sqrt T * (1 + Real.sqrt T * |u|)
  let E : ℝ := Real.exp (-T * u ^ 2 / 256)
  let q : ℝ := Real.exp (-V * u ^ 2 / 32)
  let a0 : ℝ := 2 * |μ| * |u| + m3 * (|u| ^ 3 / 3 + 2 * |u| * |v|)
  let a1 : ℝ := 2 * |μ| + m3 * (u ^ 2 + 2 * |v|)
  let a2 : ℝ := 2 * m3 * |u|
  let L : ℝ := |μ| + m2 * |u| + m3 * |v|
  let d : ℝ → ℂ := fun r => quadraticChar ν r v ^ ℓ - quadraticChar ν (-r) v ^ ℓ
  change ‖d u‖ ≤ 2 * E * A ∧ ‖deriv d u‖ ≤ 4 * E * (B + R * A) ∧
    ‖deriv (fun r => deriv d r) u‖ ≤
      18 * E * (N * m3 * |u| + R * B + T * (1 + T * u ^ 2) * A)
  have hm2 : 0 ≤ m2 := integral_nonneg (fun a => sq_nonneg a)
  have hm3 : 0 < m3 := odd_third_pos ν h3 hV
  have hN : 0 ≤ N := Nat.cast_nonneg ℓ
  have hN1 : 0 ≤ N1 := Nat.cast_nonneg (ℓ - 1)
  have hN2 : 0 ≤ N2 := Nat.cast_nonneg (ℓ - 2)
  have hN1N : N1 ≤ N := Nat.cast_le.mpr (Nat.sub_le ℓ 1)
  have hN2N : N2 ≤ N := Nat.cast_le.mpr (Nat.sub_le ℓ 2)
  have hT : 0 ≤ T := mul_nonneg hN hm2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have ha0 : 0 ≤ a0 := by dsimp [a0]; positivity
  have ha1 : 0 ≤ a1 := by dsimp [a1]; positivity
  have ha2 : 0 ≤ a2 := by dsimp [a2]; positivity
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hVm2 : V ≤ m2 := by
    have he : V = m2 - μ ^ 2 := by
      simpa only [Pi.pow_apply, id_eq] using
        variance_eq_sub ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr
          (odd_moments h3).2)
    nlinarith only [he, sq_nonneg μ]
  have hγ : 0 < m3 / V := div_pos hm3 hV
  have hvstrip : |v| * (m3 / V) ≤ (1 / 128 : ℝ) * |u| := (le_div_iff₀ hγ).mp hv
  have hγV : (m3 / V) * V = m3 := div_mul_cancel₀ m3 (ne_of_gt hV)
  have hvpaid : m3 * |v| ≤ m2 * |u| / 128 := by
    have hp : |v| * (m3 / V) * V ≤ (1 / 128 : ℝ) * |u| * V :=
      mul_le_mul_of_nonneg_right hvstrip hV.le
    rw [mul_assoc, hγV] at hp
    have hm := mul_le_mul_of_nonneg_right hVm2 (abs_nonneg u)
    nlinarith only [hp, hm]
  have hL : L ≤ |μ| + 2 * m2 * |u| := by
    dsimp only [L]
    nlinarith only [hvpaid, mul_nonneg hm2 (abs_nonneg u)]
  have hμ : N * |μ| ≤ 2 * Real.sqrt T := normalized_drift_payment n ℓ hℓ μ m2 hm2 hscale hbias
  have hNL : N * L ≤ 2 * R := by
    calc
      _ ≤ N * (|μ| + 2 * m2 * |u|) := mul_le_mul_of_nonneg_left hL hN
      _ = N * |μ| + 2 * T * |u| := by dsimp [T]; ring
      _ ≤ 2 * Real.sqrt T + 2 * T * |u| := add_le_add hμ le_rfl
      _ = _ := by dsimp only [R]; ring_nf; rw [Real.sq_sqrt hT]
  have hN1L : N1 * L ≤ 2 * R :=
    (mul_le_mul_of_nonneg_right hN1N hL0).trans hNL
  have hN2L : N2 * L ≤ 2 * R :=
    (mul_le_mul_of_nonneg_right hN2N hL0).trans hNL
  have hN1m : N1 * m2 ≤ T := mul_le_mul_of_nonneg_right hN1N hm2
  have hNa0 : N * a0 ≤ 2 * A := by
    dsimp only [a0, A]
    nlinarith only [mul_nonneg (mul_nonneg hN hm3.le) (pow_nonneg (abs_nonneg u) 3)]
  have hNa1 : N * a1 ≤ 2 * B := by
    dsimp only [a1, B]
    nlinarith only [mul_nonneg (mul_nonneg hN hm3.le) (sq_nonneg u)]
  have hq1 : q ^ (ℓ - 1) ≤ E := residual_exponential ℓ 1 hℓ6 (by omega) V m2 u hV.le hcomp
  have hq2 : q ^ (ℓ - 2) ≤ E := residual_exponential ℓ 2 hℓ6 (by omega) V m2 u hV.le hcomp
  have hq3 : q ^ (ℓ - 3) ≤ E := residual_exponential ℓ 3 hℓ6 (by omega) V m2 u hV.le hcomp
  have hraw := quadraticChar_odd_power_residual_bounds ν h3 hV ℓ u v hu hv
  change ‖d u‖ ≤ N * a0 * q ^ (ℓ - 1) ∧
      ‖deriv d u‖ ≤ N * a1 * q ^ (ℓ - 1) + N * N1 * L * a0 * q ^ (ℓ - 2) ∧
      ‖deriv (fun r => deriv d r) u‖ ≤ N * a2 * q ^ (ℓ - 1) +
        2 * N * N1 * L * a1 * q ^ (ℓ - 2) + N * N1 * m2 * a0 * q ^ (ℓ - 2) +
        N * N1 * N2 * L ^ 2 * a0 * q ^ (ℓ - 3) at hraw
  have hz : N * a0 * q ^ (ℓ - 1) ≤ E * (2 * A) := by
    calc
      _ ≤ (2 * A) * E := by gcongr
      _ = _ := by ring
  have hf1 : N * a1 * q ^ (ℓ - 1) ≤ E * (2 * B) := by
    calc
      _ ≤ (2 * B) * E := by gcongr
      _ = _ := by ring
  have hf2 : N * N1 * L * a0 * q ^ (ℓ - 2) ≤ E * (4 * R * A) := by
    calc
      _ = (N1 * L) * (N * a0) * q ^ (ℓ - 2) := by ring
      _ ≤ (2 * R) * (2 * A) * E := by gcongr
      _ = _ := by ring
  have hs1 : N * a2 * q ^ (ℓ - 1) ≤ E * (2 * N * m3 * |u|) := by
    dsimp only [a2]
    calc
      _ ≤ N * (2 * m3 * |u|) * E := by gcongr
      _ = _ := by ring
  have hs2 : 2 * N * N1 * L * a1 * q ^ (ℓ - 2) ≤ E * (8 * R * B) := by
    calc
      _ = 2 * (N1 * L) * (N * a1) * q ^ (ℓ - 2) := by ring
      _ ≤ 2 * (2 * R) * (2 * B) * E := by gcongr
      _ = _ := by ring
  have hs3 : N * N1 * m2 * a0 * q ^ (ℓ - 2) ≤ E * (2 * T * A) := by
    calc
      _ = (N1 * m2) * (N * a0) * q ^ (ℓ - 2) := by ring
      _ ≤ T * (2 * A) * E := by gcongr
      _ = _ := by ring
  have hs4 : N * N1 * N2 * L ^ 2 * a0 * q ^ (ℓ - 3) ≤ E * (8 * R ^ 2 * A) := by
    calc
      _ = (N1 * L) * (N2 * L) * (N * a0) * q ^ (ℓ - 3) := by ring
      _ ≤ (2 * R) * (2 * R) * (2 * A) * E := by gcongr
      _ = _ := by ring
  have hR2 : R ^ 2 ≤ 2 * T * (1 + T * u ^ 2) := by
    have hx : (Real.sqrt T * |u|) ^ 2 = T * u ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hT, sq_abs]
    have hp : (1 + Real.sqrt T * |u|) ^ 2 ≤ 2 * (1 + T * u ^ 2) := by
      nlinarith only [hx, sq_nonneg (1 - Real.sqrt T * |u|)]
    calc
      _ = T * (1 + Real.sqrt T * |u|) ^ 2 := by dsimp [R]; rw [mul_pow, Real.sq_sqrt hT]
      _ ≤ T * (2 * (1 + T * u ^ 2)) := mul_le_mul_of_nonneg_left hp hT
      _ = _ := by ring
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ E * (2 * A) := hraw.1.trans hz
      _ = _ := by ring
  · calc
      _ ≤ E * (2 * B) + E * (4 * R * A) := hraw.2.1.trans (add_le_add hf1 hf2)
      _ ≤ _ := by nlinarith only [mul_nonneg hE hB]
  · calc
      _ ≤ E * (2 * N * m3 * |u|) + E * (8 * R * B) +
          E * (2 * T * A) + E * (8 * R ^ 2 * A) :=
        hraw.2.2.trans (add_le_add (add_le_add (add_le_add hs1 hs2) hs3) hs4)
      _ = E * (2 * (N * m3 * |u|) + 8 * (R * B) + 2 * T * A + 8 * R ^ 2 * A) := by ring
      _ ≤ E * (18 * (N * m3 * |u| + R * B + T * (1 + T * u ^ 2) * A)) := by
        apply mul_le_mul_of_nonneg_left _ hE
        have hp := mul_le_mul_of_nonneg_right hR2 hA
        have ht : T * A ≤ T * (1 + T * u ^ 2) * A := by
          nlinarith only [mul_nonneg (mul_nonneg hT hT) (mul_nonneg (sq_nonneg u) hA)]
        nlinarith only [hp, ht,
          mul_nonneg (mul_nonneg hN hm3.le) (abs_nonneg u), mul_nonneg hR hB]
      _ = _ := by ring

end Shao.Probability
