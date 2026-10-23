import Shao.Probability.QuadraticComplexChord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable def quadraticCharComplex
    (nu : Measure ℝ) (z zeta : ℂ) : ℂ :=
  ∫ a : ℝ,
    Complex.exp ((z * (a : ℂ) + zeta * ((a ^ 2 : ℝ) : ℂ)) * Complex.I) ∂nu

private theorem qcx_pair_L1
    (mu : Measure (ℝ × ℝ)) [IsProbabilityMeasure mu]
    (M1 M2 : ℝ)
    (hs : ∀ᵐ p : ℝ × ℝ ∂mu, |p.1| ≤ M1 ∧ |p.2| ≤ M2)
    (z w : ℂ) :
    Integrable (fun p : ℝ × ℝ =>
      Complex.exp ((z * (p.1 : ℂ) + w * (p.2 : ℂ)) * Complex.I)) mu ∧
      ‖∫ p : ℝ × ℝ,
        Complex.exp ((z * (p.1 : ℂ) + w * (p.2 : ℂ)) * Complex.I) ∂mu‖ ≤
        Real.exp (M1 * |z.im| + M2 * |w.im|) := by
  run_tac
    let n : Lean.Name := .str (.str (.str
      (.num (.str (.str (.str (.str .anonymous "_private") "Shao")
        "Probability") "QuadraticComplexChord") 0) "Shao") "Probability")
      "qcc_measure_L1"
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      apply $(Lean.mkIdent n) <;> assumption))

private theorem qcx_pair_entire
    (mu : Measure (ℝ × ℝ)) [IsProbabilityMeasure mu]
    (M1 M2 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hs : ∀ᵐ p : ℝ × ℝ ∂mu, |p.1| ≤ M1 ∧ |p.2| ≤ M2) :
    Differentiable ℂ (fun p : ℂ × ℂ =>
      ∫ x : ℝ × ℝ,
        Complex.exp ((p.1 * (x.1 : ℂ) + p.2 * (x.2 : ℂ)) * Complex.I) ∂mu) := by
  run_tac
    let n : Lean.Name := .str (.str (.str
      (.num (.str (.str (.str (.str .anonymous "_private") "Shao")
        "Probability") "QuadraticComplexChord") 0) "Shao") "Probability")
      "qcc_measure_entire"
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      exact $(Lean.mkIdent n) $(Lean.mkIdent `mu) $(Lean.mkIdent `M1)
        $(Lean.mkIdent `M2) $(Lean.mkIdent `hM1) $(Lean.mkIdent `hM2)
        $(Lean.mkIdent `hs)))

private theorem qcx_pushforward_data
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂nu, |a| ≤ h) :
    Differentiable ℂ (fun p : ℂ × ℂ => quadraticCharComplex nu p.1 p.2) ∧
      ∀ z w : ℂ,
        Integrable (fun a : ℝ =>
          Complex.exp ((z * (a : ℂ) + w * ((a ^ 2 : ℝ) : ℂ)) * Complex.I)) nu ∧
        ‖quadraticCharComplex nu z w‖ ≤
          Real.exp (h * |z.im| + h ^ 2 * |w.im|) := by
  let Q : ℝ → ℝ × ℝ := fun a => (a, a ^ 2)
  have hQ : Measurable Q := by fun_prop
  let mu : Measure (ℝ × ℝ) := nu.map Q
  haveI : IsProbabilityMeasure mu :=
    (Measure.isProbabilityMeasure_map_iff hQ.aemeasurable).mpr inferInstance
  have hsm : ∀ᵐ p : ℝ × ℝ ∂mu, |p.1| ≤ h ∧ |p.2| ≤ h ^ 2 := by
    rw [ae_map_iff hQ.aemeasurable (by measurability)]
    filter_upwards [hs] with a ha
    exact ⟨ha, by simpa [Q, abs_pow] using pow_le_pow_left₀ (abs_nonneg a) ha 2⟩
  have he (z w : ℂ) :
      (∫ p : ℝ × ℝ, Complex.exp
        ((z * (p.1 : ℂ) + w * (p.2 : ℂ)) * Complex.I) ∂mu) =
      quadraticCharComplex nu z w := by
    exact integral_map hQ.aemeasurable (by fun_prop)
  constructor
  · have hd := qcx_pair_entire mu h (h ^ 2) hh.le (sq_nonneg h) hsm
    convert hd using 1
    funext p
    exact (he p.1 p.2).symm
  · intro z w
    obtain ⟨hi, hb⟩ := qcx_pair_L1 mu h (h ^ 2) hsm z w
    constructor
    · exact (integrable_map_measure (by fun_prop) hQ.aemeasurable).mp hi
    · rw [he] at hb
      exact hb

private theorem qcx_cosh_remainder (b : ℝ) :
    Real.cosh b - 1 ≤ b ^ 2 * Real.exp |b| := by
  run_tac
    let n : Lean.Name := .str (.str (.str
      (.num (.str (.str (.str (.str .anonymous "_private") "Shao")
        "Probability") "QuadraticComplexChord") 0) "Shao") "Probability")
      "qcc_cosh_remainder"
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply $(Lean.mkIdent n)))

private theorem qcx_exp_cubic_remainder (b : ℝ) :
    |Real.exp b - (1 + b + b ^ 2 / 2)| ≤ |b| ^ 3 * Real.exp |b| := by
  have hp := Complex.norm_exp_sub_sum_le_norm_mul_exp (b : ℂ) 3
  norm_num [Finset.sum_range_succ] at hp
  convert hp using 1 <;> norm_cast

private theorem qcx_sinh_remainder (b : ℝ) :
    |Real.sinh b - b| ≤ |b| ^ 3 * Real.exp |b| := by
  have hp := qcx_exp_cubic_remainder b
  have hn := qcx_exp_cubic_remainder (-b)
  rw [abs_neg, neg_sq] at hn
  rw [Real.sinh_eq]
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hp).1, (abs_le.mp hn).2],
    by linarith [(abs_le.mp hp).2, (abs_le.mp hn).1]⟩

private theorem qcx_sin_remainder (z : ℂ) :
    ‖Complex.sin z - z‖ ≤ 2 * ‖z‖ ^ 3 * Real.exp |z.im| := by
  let a : ℝ := |z.re|
  let b : ℝ := |z.im|
  let E : ℝ := Real.exp b
  have ha : 0 ≤ a := abs_nonneg _
  have hb : 0 ≤ b := abs_nonneg _
  have he : 1 ≤ E := Real.one_le_exp hb
  have hsin : |Real.sin z.re - z.re| ≤ a ^ 3 := by
    have hs := Real.abs_sub_sin_le z.re
    rw [abs_sub_comm] at hs
    dsimp [a]
    linarith [pow_nonneg (abs_nonneg z.re) 3]
  have hcos : |Real.cos z.re - 1| ≤ a ^ 2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one _))]
    dsimp [a]
    rw [sq_abs]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := z.re)]
  have hch : |Real.cosh z.im - 1| ≤ b ^ 2 * E := by
    have hc : 1 ≤ Real.cosh z.im := by
      rw [Real.cosh_eq]
      linarith [Real.add_one_le_exp z.im, Real.add_one_le_exp (-z.im)]
    rw [abs_of_nonneg (sub_nonneg.mpr hc)]
    simpa [b, E, sq_abs] using qcx_cosh_remainder z.im
  have hsh : |Real.sinh z.im - z.im| ≤ b ^ 3 * E :=
    qcx_sinh_remainder z.im
  have hv : Complex.sin z - z =
      ((Real.sin z.re - z.re : ℝ) : ℂ) +
      ((Real.sin z.re * (Real.cosh z.im - 1) : ℝ) : ℂ) +
      ((z.im * (Real.cos z.re - 1) : ℝ) : ℂ) * Complex.I +
      ((Real.cos z.re * (Real.sinh z.im - z.im) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.sin_eq]
    push_cast
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cos,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    linear_combination z.re_add_im
  have hn : ‖Complex.sin z - z‖ ≤ a ^ 3 + a * (b ^ 2 * E) + b * a ^ 2 + b ^ 3 * E := by
    rw [hv]
    calc
      _ ≤ ‖((Real.sin z.re - z.re : ℝ) : ℂ)‖ +
          ‖((Real.sin z.re * (Real.cosh z.im - 1) : ℝ) : ℂ)‖ +
          ‖((z.im * (Real.cos z.re - 1) : ℝ) : ℂ) * Complex.I‖ +
          ‖((Real.cos z.re * (Real.sinh z.im - z.im) : ℝ) : ℂ) * Complex.I‖ :=
        by
          apply (norm_add_le _ _).trans
          apply add_le_add _ le_rfl
          apply (norm_add_le _ _).trans
          exact add_le_add (norm_add_le _ _) le_rfl
      _ ≤ _ := by
        simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
          abs_mul]
        exact add_le_add (add_le_add (add_le_add hsin
          (mul_le_mul (Real.abs_sin_le_abs) hch (abs_nonneg _) ha))
          (mul_le_mul_of_nonneg_left hcos hb))
          (by simpa using mul_le_mul (Real.abs_cos_le_one _) hsh (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
  have hnorm : a ^ 2 + b ^ 2 = ‖z‖ ^ 2 := by
    simp [a, b, Complex.sq_norm, Complex.normSq_apply]
    ring
  have ham : a ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hbm : b ≤ ‖z‖ := Complex.abs_im_le_norm z
  calc
    _ ≤ a ^ 3 + a * (b ^ 2 * E) + b * a ^ 2 + b ^ 3 * E := hn
    _ ≤ E * ((a + b) * (a ^ 2 + b ^ 2)) := by
      nlinarith [mul_le_mul_of_nonneg_right he (pow_nonneg ha 3),
        mul_le_mul_of_nonneg_right he (mul_nonneg hb (sq_nonneg a))]
    _ ≤ E * (2 * ‖z‖ * ‖z‖ ^ 2) := by
      rw [hnorm]
      gcongr
      linarith
    _ = _ := by dsimp [E, b]; ring

private theorem qcx_tilt_data
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h : ℝ) (hh : 0 < h) (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (b s : ℝ) :
    let W : ℝ → ℝ := fun a => Real.exp (b * a - s * a ^ 2)
    let Z : ℝ := ∫ a : ℝ, W a ∂nu
    let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
    Integrable W nu ∧ 0 < Z ∧ IsProbabilityMeasure rho ∧
      ∀ u v : ℝ,
        quadraticCharComplex nu
            ((u : ℂ) - (b : ℂ) * Complex.I)
            ((v : ℂ) + (s : ℂ) * Complex.I) =
          (Z : ℂ) * quadraticChar rho u v := by
  dsimp only
  have hW : Integrable (fun a : ℝ => Real.exp (b * a - s * a ^ 2)) nu := by
    refine (integrable_const (Real.exp (|b| * h + |s| * h ^ 2))).mono'
      (by fun_prop) ?_
    filter_upwards [hsupport] with a ha
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      b * a - s * a ^ 2 ≤ |b * a| + |s * a ^ 2| := by
        linarith [le_abs_self (b * a), neg_le_abs (s * a ^ 2)]
      _ = |b| * |a| + |s| * |a| ^ 2 := by rw [abs_mul, abs_mul, abs_pow]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left ha (abs_nonneg b))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg a) ha 2) (abs_nonneg s))
  have hZ := integral_exp_pos hW
  refine ⟨hW, hZ, isProbabilityMeasure_tilted hW, ?_⟩
  intro u v
  unfold quadraticCharComplex quadraticChar
  rw [integral_tilted, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with a
  rw [Complex.real_smul]
  have hc : ((∫ a : ℝ, Real.exp (b * a - s * a ^ 2) ∂nu : ℝ) : ℂ) *
      ((Real.exp (b * a - s * a ^ 2) /
        ∫ a : ℝ, Real.exp (b * a - s * a ^ 2) ∂nu : ℝ) : ℂ) =
      (Real.exp (b * a - s * a ^ 2) : ℂ) := by
    rw [Complex.ofReal_div]
    have hZc : (((∫ a : ℝ, Real.exp (b * a - s * a ^ 2) ∂nu : ℝ) : ℂ)) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hZ.ne'
    exact mul_div_cancel₀ _ hZc
  rw [← mul_assoc, hc, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq] <;> ring

private theorem qcx_energy_exp_bounds (s v a : ℝ) (hs : 0 ≤ s) :
    let E : ℂ := Complex.exp
      ((((v * a ^ 2 : ℝ) : ℂ)) * Complex.I - ((s * a ^ 2 : ℝ) : ℂ))
    ‖E‖ ≤ 1 ∧ ‖E - 1‖ ≤ (|v| + s) * a ^ 2 := by
  dsimp only
  let D : ℝ := Real.exp (-s * a ^ 2)
  let U : ℂ := Complex.exp (((v * a ^ 2 : ℝ) : ℂ) * Complex.I)
  have hD : 0 ≤ D := (Real.exp_pos _).le
  have hD1 : D ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg a])
  have hDm : |D - 1| ≤ s * a ^ 2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hD1)]
    dsimp [D]
    linarith [Real.add_one_le_exp (-s * a ^ 2)]
  have hU : ‖U‖ = 1 := by
    simp only [U, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, Real.exp_zero]
  have hUm : ‖U - 1‖ ≤ |v| * a ^ 2 := by
    have hp := Real.norm_exp_I_mul_ofReal_sub_one_le (x := v * a ^ 2)
    simpa [U, mul_comm, abs_mul, abs_of_nonneg (sq_nonneg a)] using hp
  have he : Complex.exp
      ((((v * a ^ 2 : ℝ) : ℂ)) * Complex.I - ((s * a ^ 2 : ℝ) : ℂ)) =
      (D : ℂ) * U := by
    rw [show (D : ℂ) = Complex.exp ((-s * a ^ 2 : ℝ) : ℂ) from
      Complex.ofReal_exp _, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  constructor
  · simpa [norm_mul, hU, Complex.norm_real, abs_of_nonneg hD] using hD1
  · calc
      _ = ‖(D : ℂ) * (U - 1) + ((D : ℂ) - 1)‖ := by congr 1; ring
      _ ≤ ‖(D : ℂ) * (U - 1)‖ + ‖(D : ℂ) - 1‖ := norm_add_le _ _
      _ = D * ‖U - 1‖ + |D - 1| := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hD]
        norm_cast
      _ ≤ D * (|v| * a ^ 2) + s * a ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hUm hD) hDm
      _ ≤ (|v| + s) * a ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hD1 (mul_nonneg (abs_nonneg v) (sq_nonneg a))]

private theorem qcx_odd_bound
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (h : ℝ) (hh : 0 < h) (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (lam s u v : ℝ) (hlam : 0 ≤ lam) (hs : 0 ≤ s) :
    let z : ℂ := (u : ℂ) - (lam : ℂ) * Complex.I
    let zeta : ℂ := (v : ℂ) + (s : ℂ) * Complex.I
    let mu : ℝ := ∫ a : ℝ, a ∂nu
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
    ‖quadraticCharComplex nu z zeta - quadraticCharComplex nu (-z) zeta‖ ≤
      4 * Real.exp (lam * h) *
        (|mu| * ‖z‖ + m3 * (‖z‖ ^ 3 + ‖z‖ * (|v| + s))) := by
  dsimp only
  let z : ℂ := (u : ℂ) - (lam : ℂ) * Complex.I
  let zeta : ℂ := (v : ℂ) + (s : ℂ) * Complex.I
  let E : ℝ → ℂ := fun a => Complex.exp
    ((((v * a ^ 2 : ℝ) : ℂ)) * Complex.I - ((s * a ^ 2 : ℝ) : ℂ))
  let R : ℝ → ℂ := fun a =>
    (Complex.sin (z * (a : ℂ)) - z * (a : ℂ)) * E a +
      z * (a : ℂ) * (E a - 1)
  let K : ℝ := 2 * ‖z‖ ^ 3 * Real.exp (lam * h) + ‖z‖ * (|v| + s)
  change ‖quadraticCharComplex nu z zeta - quadraticCharComplex nu (-z) zeta‖ ≤
    4 * Real.exp (lam * h) *
      (|∫ a : ℝ, a ∂nu| * ‖z‖ + (∫ a : ℝ, |a| ^ 3 ∂nu) *
        (‖z‖ ^ 3 + ‖z‖ * (|v| + s)))
  have hE (a : ℝ) : ‖E a‖ ≤ 1 ∧ ‖E a - 1‖ ≤ (|v| + s) * a ^ 2 :=
    qcx_energy_exp_bounds s v a hs
  have hsin : ∀ᵐ a : ℝ ∂nu,
      ‖Complex.sin (z * (a : ℂ)) - z * (a : ℂ)‖ ≤
        2 * ‖z‖ ^ 3 * Real.exp (lam * h) * |a| ^ 3 := by
    filter_upwards [hsupport] with a ha
    have him : |(z * (a : ℂ)).im| = lam * |a| := by
      simp [z, Complex.mul_im, abs_mul, abs_of_nonneg hlam]
    have hex : Real.exp |(z * (a : ℂ)).im| ≤ Real.exp (lam * h) := by
      rw [him]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha hlam)
    calc
      _ ≤ 2 * ‖z * (a : ℂ)‖ ^ 3 * Real.exp |(z * (a : ℂ)).im| :=
        qcx_sin_remainder _
      _ ≤ 2 * ‖z * (a : ℂ)‖ ^ 3 * Real.exp (lam * h) := by gcongr
      _ = _ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]; ring
  have hRbound : ∀ᵐ a : ℝ ∂nu, ‖R a‖ ≤ K * |a| ^ 3 := by
    filter_upwards [hsin] with a ha
    calc
      _ ≤ ‖Complex.sin (z * (a : ℂ)) - z * (a : ℂ)‖ * ‖E a‖ +
          ‖z * (a : ℂ)‖ * ‖E a - 1‖ := by
        exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
      _ ≤ (2 * ‖z‖ ^ 3 * Real.exp (lam * h) * |a| ^ 3) * 1 +
          ‖z * (a : ℂ)‖ * ((|v| + s) * a ^ 2) :=
        add_le_add (mul_le_mul ha (hE a).1 (norm_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_left (hE a).2 (norm_nonneg _))
      _ = K * |a| ^ 3 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← sq_abs a]
        dsimp [K]
        ring
  have hRi : Integrable R nu := (h3.const_mul K).mono' (by
    dsimp [R, E]
    fun_prop) hRbound
  have h1 : Integrable (fun a : ℝ => a) nu :=
    (integrable_const h).mono' measurable_id.aestronglyMeasurable hsupport
  have hp := (qcx_pushforward_data nu h hh hsupport).2 z zeta
  have hn := (qcx_pushforward_data nu h hh hsupport).2 (-z) zeta
  have hid (a : ℝ) :
      Complex.exp ((z * (a : ℂ) + zeta * ((a ^ 2 : ℝ) : ℂ)) * Complex.I) -
        Complex.exp ((-z * (a : ℂ) + zeta * ((a ^ 2 : ℝ) : ℂ)) * Complex.I) =
      (2 * Complex.I) * (z * (a : ℂ) + R a) := by
    have he : Complex.exp (zeta * ((a ^ 2 : ℝ) : ℂ) * Complex.I) = E a := by
      congr 1
      dsimp [zeta, E]
      push_cast
      ring_nf
      simp [Complex.I_sq] <;> ring
    have hsm : Complex.exp (z * (a : ℂ) * Complex.I) -
        Complex.exp (-z * (a : ℂ) * Complex.I) =
        (2 * Complex.I) * Complex.sin (z * (a : ℂ)) := by
      have hc : -z * (a : ℂ) = -(z * (a : ℂ)) := by ring
      simp only [hc, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
      ring
    simp only [add_mul, Complex.exp_add]
    rw [he, ← sub_mul, hsm]
    dsimp [R]
    ring
  have hint : quadraticCharComplex nu z zeta - quadraticCharComplex nu (-z) zeta =
      (2 * Complex.I) *
        (z * ((∫ a : ℝ, a ∂nu : ℝ) : ℂ) + ∫ a : ℝ, R a ∂nu) := by
    unfold quadraticCharComplex
    rw [← integral_sub hp.1 hn.1]
    simp_rw [hid]
    rw [integral_const_mul]
    congr 1
    calc
      (∫ a : ℝ, z * (a : ℂ) + R a ∂nu) =
          (∫ a : ℝ, z * (a : ℂ) ∂nu) + ∫ a : ℝ, R a ∂nu :=
        integral_add ((h1.ofReal (𝕜 := ℂ)).const_mul z) hRi
      _ = _ := by
        have ho : (∫ a : ℝ, (a : ℂ) ∂nu) = ((∫ a : ℝ, a ∂nu : ℝ) : ℂ) :=
          integral_ofReal
        rw [integral_const_mul, ho]
  have hRb : ‖∫ a : ℝ, R a ∂nu‖ ≤ K * ∫ a : ℝ, |a| ^ 3 ∂nu := by
    calc
      _ ≤ ∫ a : ℝ, K * |a| ^ 3 ∂nu := norm_integral_le_of_norm_le (h3.const_mul K) hRbound
      _ = _ := integral_const_mul _ _
  have hM : 0 ≤ ∫ a : ℝ, |a| ^ 3 ∂nu := integral_nonneg (fun a => by positivity)
  have he : 1 ≤ Real.exp (lam * h) := Real.one_le_exp (mul_nonneg hlam hh.le)
  rw [hint, norm_mul]
  have htwo : ‖(2 : ℂ) * Complex.I‖ = 2 := by norm_num
  rw [htwo]
  calc
    _ ≤ 2 * (‖z * ((∫ a : ℝ, a ∂nu : ℝ) : ℂ)‖ + K * ∫ a : ℝ, |a| ^ 3 ∂nu) := by
      gcongr
      exact (norm_add_le _ _).trans (add_le_add le_rfl hRb)
    _ = 2 * (‖z‖ * |∫ a : ℝ, a ∂nu| + K * ∫ a : ℝ, |a| ^ 3 ∂nu) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ _ := by
      dsimp [K]
      have hA : 0 ≤ |∫ a : ℝ, a ∂nu| * ‖z‖ := by positivity
      have hC : 0 ≤ (∫ a : ℝ, |a| ^ 3 ∂nu) * (‖z‖ * (|v| + s)) :=
        mul_nonneg hM (mul_nonneg (norm_nonneg z) (add_nonneg (abs_nonneg v) hs))
      nlinarith [mul_le_mul_of_nonneg_right he
          (mul_nonneg (abs_nonneg (∫ a : ℝ, a ∂nu)) (norm_nonneg z)),
        mul_le_mul_of_nonneg_right he
          (mul_nonneg hM (mul_nonneg (norm_nonneg z) (add_nonneg (abs_nonneg v) hs)))]

theorem quadraticCharComplex_data
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (h : ℝ) (hh : 0 < h)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h) :
    Differentiable ℂ (fun p : ℂ × ℂ =>
      quadraticCharComplex nu p.1 p.2) ∧
      (∀ z zeta : ℂ,
        Integrable (fun a : ℝ =>
          Complex.exp ((z * (a : ℂ) +
            zeta * ((a ^ 2 : ℝ) : ℂ)) * Complex.I)) nu ∧
        ‖quadraticCharComplex nu z zeta‖ ≤
          Real.exp (h * |z.im| + h ^ 2 * |zeta.im|)) ∧
      (∀ u v : ℝ,
        quadraticCharComplex nu (u : ℂ) (v : ℂ) = quadraticChar nu u v) ∧
      (∀ b s : ℝ,
        let W : ℝ → ℝ := fun a => Real.exp (b * a - s * a ^ 2)
        let Z : ℝ := ∫ a : ℝ, W a ∂nu
        let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
        Integrable W nu ∧ 0 < Z ∧ IsProbabilityMeasure rho ∧
          ∀ u v : ℝ,
            quadraticCharComplex nu
                ((u : ℂ) - (b : ℂ) * Complex.I)
                ((v : ℂ) + (s : ℂ) * Complex.I) =
              (Z : ℂ) * quadraticChar rho u v) ∧
      ∀ lam s u v : ℝ, 0 ≤ lam → 0 ≤ s →
        let z : ℂ := (u : ℂ) - (lam : ℂ) * Complex.I
        let zeta : ℂ := (v : ℂ) + (s : ℂ) * Complex.I
        let mu : ℝ := ∫ a : ℝ, a ∂nu
        let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
        ‖quadraticCharComplex nu z zeta -
            quadraticCharComplex nu (-z) zeta‖ ≤
          4 * Real.exp (lam * h) *
            (|mu| * ‖z‖ + m3 *
              (‖z‖ ^ 3 + ‖z‖ * (|v| + s))) := by
  obtain ⟨hd, hL⟩ := qcx_pushforward_data nu h hh hsupport
  refine ⟨hd, hL, ?_, ?_, ?_⟩
  · intro u v
    unfold quadraticCharComplex quadraticChar
    congr 1
    funext a
    congr 1
    push_cast
    ring
  · intro b s
    exact qcx_tilt_data nu h hh hsupport b s
  · intro lam s u v hlam hs
    exact qcx_odd_bound nu h3 h hh hsupport lam s u v hlam hs

end Shao.Probability
