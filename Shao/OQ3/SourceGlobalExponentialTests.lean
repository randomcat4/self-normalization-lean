import Shao.OQ3.EnergyBernoulliMGF
import Shao.OQ3.PositiveRate
import Shao.OQ3.RegularCovariance

/-!
Actual finite exponential tests for the source saddle and its full positive tail domain.
Source: current/oq3/proofs/r1/report.md; frozen scope 68.
The tests use the original inverse-tilted law and true positive integrals.
-/

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology BigOperators
noncomputable section

private theorem original_quadratic_exp_log (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (s t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (s * x + t * x ^ 2)) (originalMeasure ell w) ∧
    0 < (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂originalMeasure ell w) ∧
    Real.log (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂originalMeasure ell w) =
      Real.log (∫ x : ℝ, Real.exp ((s - 8 * ell) * x + (t + ell) * x ^ 2)
        ∂atomicMeasure w) - Real.log (inverseNormalizer ell w) := by
  let := atomicMeasure_isProbabilityMeasure w hw hs
  let := originalMeasure_isProbabilityMeasure ell w hw hs
  have hi : Integrable (fun x : ℝ => Real.exp (s * x + t * x ^ 2))
      (originalMeasure ell w) := by
    apply integrable_continuous_of_fixed_bounds _
      ((originalMeasure_ae_bounds ell w).mono fun _ hx => hx.2)
    fun_prop
  have hj : Integrable (fun x : ℝ => Real.exp ((s - 8 * ell) * x +
      (t + ell) * x ^ 2)) (atomicMeasure w) := by
    apply integrable_continuous_of_fixed_bounds _
      ((atomicMeasure_ae_bounds w).mono fun _ hx => hx.2)
    fun_prop
  have he : (fun x : ℝ => -ell * normalValue x) +
      (fun x => s * x + t * x ^ 2) =
      (fun x => (s - 8 * ell) * x + (t + ell) * x ^ 2) := by
    funext x
    simp only [Pi.add_apply, normalValue]
    ring
  refine ⟨hi, integral_exp_pos hi, ?_⟩
  rw [originalMeasure, integral_exp_tilted, he]
  change Real.log ((_ : ℝ) / inverseNormalizer ell w) = _
  exact Real.log_div (integral_exp_pos hj).ne' (inverseNormalizer_pos ell w hw hs).ne'

private theorem atomic_quadratic_log_lower (q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k : Fin 4, HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
      (constraintTarget q k)) (s t : ℝ) :
    s * (q / 4) + t * q ≤
      Real.log (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂atomicMeasure w) := by
  have hs : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  let := atomicMeasure_isProbabilityMeasure w hw hs
  have hb := (atomicMeasure_ae_bounds w).mono fun _ hx => hx.2
  have hx := atomicMeasure_mean sourceEll q w hw hm
  have hx2 : Integrable (fun x : ℝ => x ^ 2) (atomicMeasure w) ∧
      (∫ x : ℝ, x ^ 2 ∂atomicMeasure w) = q := by
    simpa [constraintFeature, constraintTarget] using
      atomicMeasure_constraints sourceEll q w hw hm 3
  let h : ℝ → ℝ := fun x => s * (x - q / 4) + t * (x ^ 2 - q)
  have hh : Integrable h (atomicMeasure w) := by
    exact ((hx.1.sub (integrable_const _)).const_mul s).add
      ((hx2.1.sub (integrable_const _)).const_mul t)
  have he : Integrable (fun x => Real.exp (h x)) (atomicMeasure w) := by
    apply integrable_continuous_of_fixed_bounds _ hb
    dsimp [h]
    fun_prop
  have hmean : (∫ x : ℝ, h x ∂atomicMeasure w) = 0 := by
    have hxs : Integrable (fun x : ℝ => x - q / 4) (atomicMeasure w) :=
      hx.1.sub (integrable_const _)
    have hx2s : Integrable (fun x : ℝ => x ^ 2 - q) (atomicMeasure w) :=
      hx2.1.sub (integrable_const _)
    have hss : Integrable (fun x : ℝ => s * (x - q / 4)) (atomicMeasure w) :=
      hxs.const_mul s
    have htt : Integrable (fun x : ℝ => t * (x ^ 2 - q)) (atomicMeasure w) :=
      hx2s.const_mul t
    dsimp [h]
    rw [integral_add hss htt, integral_const_mul,
      integral_const_mul, integral_sub hx.1 (integrable_const _),
      integral_sub hx2.1 (integrable_const _), hx.2, hx2.2]
    simp
  have hge : 1 ≤ ∫ x : ℝ, Real.exp (h x) ∂atomicMeasure w := by
    have hlin : Integrable (fun x : ℝ => 1 + h x) (atomicMeasure w) :=
      (integrable_const 1).add hh
    have hc : (∫ x : ℝ, 1 + h x ∂atomicMeasure w) ≤
        ∫ x : ℝ, Real.exp (h x) ∂atomicMeasure w :=
      integral_mono_ae hlin he (Filter.Eventually.of_forall fun x => by
        simpa only [add_comm] using Real.add_one_le_exp (h x))
    rw [integral_add (integrable_const 1) hh, hmean] at hc
    simpa using hc
  have hf (x : ℝ) : Real.exp (s * x + t * x ^ 2) =
      Real.exp (s * (q / 4) + t * q) * Real.exp (h x) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [h]
    ring
  simp_rw [hf]
  rw [integral_const_mul, Real.log_mul (Real.exp_pos _).ne' (integral_exp_pos he).ne',
    Real.log_exp]
  exact le_add_of_nonneg_right (Real.log_nonneg hge)

private theorem raw_energy_log_upper (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q H u : ℝ) (hH : 0 < H)
    (henergy : ∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + H)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂mu) = q) :
    Real.log (∫ x : ℝ, Real.exp (u * x ^ 2) ∂mu) ≤
      u + Real.log (1 - (q - 1) / H + ((q - 1) / H) * Real.exp (u * H)) := by
  obtain ⟨hi, hp, hl⟩ := bounded_energy_logMGF_le_bernoulli mu hb q H u hH henergy hsecond
  have hf (x : ℝ) : Real.exp (u * x ^ 2) =
      Real.exp (u * q) * Real.exp (u * (x ^ 2 - q)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hf]
  rw [integral_const_mul, Real.log_mul (Real.exp_pos _).ne' hp.ne', Real.log_exp]
  linarith

theorem source_saddle_exponential_value_bound
    (q : ℝ) (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    (∀ s t : ℝ,
      Integrable (fun x : ℝ => Real.exp (s * x + t * x ^ 2))
        (originalMeasure sourceEll w) ∧
      0 < (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂originalMeasure sourceEll w) ∧
      s * (q / 4) + t * q -
        Real.log (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂originalMeasure sourceEll w) ≤
          saddleRate sourceEll q w) ∧
    (8 * sourceEll) * (q / 4) + (-sourceEll) * q -
      Real.log (∫ x : ℝ, Real.exp ((8 * sourceEll) * x + (-sourceEll) * x ^ 2)
        ∂originalMeasure sourceEll w) = saddleRate sourceEll q w := by
  have hs : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  let := atomicMeasure_isProbabilityMeasure w hw hs
  constructor
  · intro s t
    obtain ⟨hi, hp, hl⟩ := original_quadratic_exp_log sourceEll w hw hs s t
    refine ⟨hi, hp, ?_⟩
    rw [hl]
    have hb := atomic_quadratic_log_lower q w hw hm (s - 8 * sourceEll) (t + sourceEll)
    unfold saddleRate
    nlinarith
  · obtain ⟨_, _, hl⟩ := original_quadratic_exp_log sourceEll w hw hs
      (8 * sourceEll) (-sourceEll)
    simp at hl
    simp only [neg_mul]
    rw [hl]
    unfold saddleRate
    ring

theorem exists_source_tail_exponential_separator
    (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k))
    (a c : ℝ) (hc0 : 0 < c)
    (htail : (Real.sqrt q / 4) * Real.sqrt c ≤ a)
    (hne : a ≠ q / 4 ∨ c ≠ q) :
    ∃ s t : ℝ,
      Integrable (fun x : ℝ => Real.exp (s * x + t * x ^ 2))
        (originalMeasure sourceEll w) ∧
      0 < (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂originalMeasure sourceEll w) ∧
      saddleRate sourceEll q w < s * a + t * c -
        Real.log (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂originalMeasure sourceEll w) := by
  have hs : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  let := atomicMeasure_isProbabilityMeasure w hw hs
  have hb := (atomicMeasure_ae_bounds w).mono fun _ hx => hx.2
  have hsecond : (∫ x : ℝ, x ^ 2 ∂atomicMeasure w) = q := by
    simpa [constraintFeature, constraintTarget] using
      (atomicMeasure_constraints sourceEll q w hw hm 3).2
  have hq : 0 < q := lt_trans zero_lt_one hq0
  have hell := sourceEll_pos
  let H : ℝ := 25 + 8 * Real.sqrt 10
  have hsqrt : (Real.sqrt 10) ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have hsqrt0 := Real.sqrt_nonneg (10 : ℝ)
  have hH0 : 50 < H := by dsimp [H]; nlinarith
  have hH1 : H < 51 := by dsimp [H]; nlinarith
  have hH : 0 < H := by linarith
  have henergy : ∀ᵐ x ∂atomicMeasure w, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + H := by
    filter_upwards [atomicMeasure_ae_bounds w] with x hx
    have habs := sq_abs x
    have hlo := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) hx.1
    have hhi := mul_self_le_mul_self (abs_nonneg x) hx.2
    constructor
    · nlinarith
    · dsimp [H]
      nlinarith
  have hrawi (u : ℝ) : Integrable (fun x : ℝ => Real.exp (u * x ^ 2))
      (atomicMeasure w) := by
    apply integrable_continuous_of_fixed_bounds _ hb
    fun_prop
  have hrawp (u : ℝ) : 0 < ∫ x : ℝ, Real.exp (u * x ^ 2) ∂atomicMeasure w :=
    integral_exp_pos (hrawi u)
  let B : ℝ := 8 * sourceEll * a - sourceEll * c + Real.log (inverseNormalizer sourceEll w)
  have hprovide (u : ℝ)
      (hu : saddleRate sourceEll q w < B + u * c -
        Real.log (∫ x : ℝ, Real.exp (u * x ^ 2) ∂atomicMeasure w)) :
      ∃ s t : ℝ,
        Integrable (fun x : ℝ => Real.exp (s * x + t * x ^ 2))
          (originalMeasure sourceEll w) ∧
        0 < (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂originalMeasure sourceEll w) ∧
        saddleRate sourceEll q w < s * a + t * c -
          Real.log (∫ x : ℝ, Real.exp (s * x + t * x ^ 2)
            ∂originalMeasure sourceEll w) := by
    obtain ⟨hi, hp, hl⟩ := original_quadratic_exp_log sourceEll w hw hs
      (8 * sourceEll) (-sourceEll + u)
    have he : (fun x : ℝ => Real.exp (((8 * sourceEll) - 8 * sourceEll) * x +
        ((-sourceEll + u) + sourceEll) * x ^ 2)) =
        (fun x : ℝ => Real.exp (u * x ^ 2)) := by
      funext x
      congr 1
      ring
    rw [he] at hl
    refine ⟨8 * sourceEll, -sourceEll + u, hi, hp, ?_⟩
    rw [hl]
    dsimp [B] at hu
    nlinarith
  let T : ℝ := |saddleRate sourceEll q w - B| + 1
  have hT : 0 < T := by dsimp [T]; positivity
  have hBT : saddleRate sourceEll q w < B + T := by
    have h := le_abs_self (saddleRate sourceEll q w - B)
    dsimp [T]
    linarith
  by_cases hc1 : c < 1
  · let u : ℝ := T / (c - 1)
    have hden : c - 1 < 0 := sub_neg.mpr hc1
    have hu : u < 0 := div_neg_of_pos_of_neg hT hden
    have hprod : u * (c - 1) = T := by dsimp [u]; field_simp [hden.ne]
    have hi : (∫ x : ℝ, Real.exp (u * x ^ 2) ∂atomicMeasure w) ≤ Real.exp u := by
      have h := integral_mono_ae (hrawi u) (integrable_const (Real.exp u)) ?_
      · simpa using h
      filter_upwards [henergy] with x hx
      exact Real.exp_le_exp.mpr (by
        simpa only [mul_one] using mul_le_mul_of_nonpos_left hx.1 hu.le)
    have hl := Real.log_le_log (hrawp u) hi
    rw [Real.log_exp] at hl
    exact hprovide u (by nlinarith)
  by_cases hc2 : 1 + H < c
  · let u : ℝ := T / (c - (1 + H))
    have hden : 0 < c - (1 + H) := sub_pos.mpr hc2
    have hu : 0 < u := div_pos hT hden
    have hprod : u * (c - (1 + H)) = T := by dsimp [u]; field_simp [hden.ne']
    have hi : (∫ x : ℝ, Real.exp (u * x ^ 2) ∂atomicMeasure w) ≤
        Real.exp (u * (1 + H)) := by
      have h := integral_mono_ae (hrawi u) (integrable_const (Real.exp (u * (1 + H)))) ?_
      · simpa using h
      filter_upwards [henergy] with x hx
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.2 hu.le)
    have hl := Real.log_le_log (hrawp u) hi
    rw [Real.log_exp] at hl
    exact hprovide u (by nlinarith)
  have hc1' : 1 ≤ c := le_of_not_gt hc1
  have hc2' : c ≤ 1 + H := le_of_not_gt hc2
  let R : ℝ := Real.sqrt c / Real.sqrt q
  have hsqc : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc0.le
  have hsqq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq.le
  have hsqcp : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hsqqp : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hR : 0 < R := div_pos hsqcp hsqqp
  have hcR : c = q * R ^ 2 := by
    dsimp [R]
    rw [div_pow, hsqq, hsqc]
    field_simp [hq.ne']
  have htailR : q * R / 4 ≤ a := by
    have he : q * R / 4 = (Real.sqrt q / 4) * Real.sqrt c := by
      dsimp [R]
      calc
        q * (Real.sqrt c / Real.sqrt q) / 4 =
            (Real.sqrt q) ^ 2 * (Real.sqrt c / Real.sqrt q) / 4 := by rw [hsqq]
        _ = (Real.sqrt q / 4) * Real.sqrt c := by field_simp [hsqqp.ne']
    rwa [he]
  by_cases hRone : R = 1
  · have hcq : c = q := by simpa [hRone] using hcR
    have haneq : a ≠ q / 4 := hne.resolve_right (fun h => h hcq)
    have ha : q / 4 < a := lt_of_le_of_ne (by simpa [hRone] using htailR) haneq.symm
    have hz : (∫ x : ℝ, Real.exp ((0 : ℝ) * x ^ 2) ∂atomicMeasure w) = 1 := by simp
    apply hprovide 0
    rw [hz, Real.log_one]
    dsimp [B, saddleRate]
    rw [hcq]
    nlinarith [mul_pos hell (sub_pos.mpr ha)]
  have hp0 : 0 ≤ (q * R ^ 2 - 1) / H := by
    rw [← hcR]
    exact div_nonneg (sub_nonneg.mpr hc1') hH.le
  have hp1 : (q * R ^ 2 - 1) / H ≤ 1 := by
    rw [← hcR]
    exact (div_le_one hH).mpr (by linarith)
  have hz0 : 0 < (q - 1) / H := div_pos (sub_pos.mpr hq0) hH
  have hz1 : (q - 1) / H < 1 := (div_lt_one hH).mpr (by linarith)
  have hgap := binaryRelativeEntropy_source_gap q H R hq0 hq1 hH0 hH1 hR hRone hp0 hp1
  have hellq : sourceEll * q < 7 / 200 := by
    have h1 := mul_lt_mul_of_pos_right sourceEll_lt_one_div_thirty hq
    nlinarith
  have hsq : 0 < (R - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hRone)
  have hL : sourceEll * q * (R - 1) ^ 2 <
      binaryRelativeEntropy ((q * R ^ 2 - 1) / H) ((q - 1) / H) :=
    lt_trans (mul_lt_mul_of_pos_right hellq hsq) hgap
  obtain ⟨theta, _, htheta⟩ := exists_binary_exponential_test
    ((q * R ^ 2 - 1) / H) ((q - 1) / H)
    (sourceEll * q * (R - 1) ^ 2) hp0 hp1 hz0 hz1 hL
  let u : ℝ := theta / H
  have huH : u * H = theta := by dsimp [u]; field_simp [hH.ne']
  have hl := raw_energy_log_upper (atomicMeasure w) hb q H u hH henergy hsecond
  rw [huH] at hl
  have htprod : theta * ((q * R ^ 2 - 1) / H) = u * (c - 1) := by
    rw [← hcR]
    dsimp [u]
    ring
  rw [htprod] at htheta
  have hdelta : 0 ≤ 8 * sourceEll * (a - q * R / 4) :=
    mul_nonneg (mul_nonneg (by norm_num) hell.le) (sub_nonneg.mpr htailR)
  have he : B + u * c - saddleRate sourceEll q w =
      8 * sourceEll * (a - q * R / 4) - sourceEll * q * (R - 1) ^ 2 + u * c := by
    dsimp [B, saddleRate]
    rw [hcR]
    ring
  exact hprovide u (by linarith)

end
end Shao.OQ3
