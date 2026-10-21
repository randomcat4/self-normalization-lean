import Shao.Probability.QuadraticCharacteristic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance

/-!
Low-frequency damping of the true quadratic characteristic integral.
The law is fixed and may have nonzero mean. No source-specific cutoff-law
bridge, high-frequency damping or strict-CDF comparison is asserted here.
-/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private lemma moments_of_third {ν : Measure ℝ} [IsProbabilityMeasure ν]
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

private lemma integral_fst (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} (hf : Integrable f ν) :
    (∫ z : ℝ × ℝ, f z.1 ∂ν.prod ν) = ∫ a : ℝ, f a ∂ν := by
  rw [integral_prod _ (hf.comp_fst ν)]
  simp

private lemma integral_snd (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} (hf : Integrable f ν) :
    (∫ z : ℝ × ℝ, f z.2 ∂ν.prod ν) = ∫ a : ℝ, f a ∂ν := by
  rw [integral_prod _ (hf.comp_snd ν)]
  simp

private lemma pair_square_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) :
    Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) (ν.prod ν) := by
  refine (((h2.comp_fst ν).add (h2.comp_snd ν)).const_mul 2).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun z => ?_)
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (z.1 - z.2))]
  change (z.1 - z.2) ^ 2 ≤ 2 * (z.1 ^ 2 + z.2 ^ 2)
  nlinarith [sq_nonneg (z.1 + z.2)]

theorem quadratic_pair_square_moment (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) :
    Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) (ν.prod ν) ∧
      (∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2 ∂ν.prod ν) =
        2 * variance (id : ℝ → ℝ) ν := by
  obtain ⟨h1, h2⟩ := moments_of_third h3
  refine ⟨pair_square_integrable ν h2, ?_⟩
  have hV : variance (id : ℝ → ℝ) ν =
      (∫ a : ℝ, a ^ 2 ∂ν) - (∫ a : ℝ, a ∂ν) ^ 2 := by
    simpa only [Pi.pow_apply, id_eq] using
      variance_eq_sub ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr h2)
  have hi : (∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2 ∂ν.prod ν) =
      (∫ a : ℝ, a ^ 2 ∂ν) + (∫ a : ℝ, a ^ 2 ∂ν) -
        2 * (∫ a : ℝ, a ∂ν) * (∫ a : ℝ, a ∂ν) := by
    calc
      _ = ∫ z : ℝ × ℝ, (z.1 ^ 2 + z.2 ^ 2) - 2 * (z.1 * z.2) ∂ν.prod ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by ring
      _ = _ := by
        have hs : Integrable (fun z : ℝ × ℝ => z.1 ^ 2 + z.2 ^ 2) (ν.prod ν) :=
          (h2.comp_fst ν).add (h2.comp_snd ν)
        have hc : Integrable (fun z : ℝ × ℝ => 2 * (z.1 * z.2)) (ν.prod ν) :=
          (h1.mul_prod h1).const_mul 2
        rw [integral_sub hs hc,
          integral_add (h2.comp_fst ν) (h2.comp_snd ν), integral_const_mul,
          integral_fst ν h2, integral_snd ν h2,
          integral_prod_mul (fun a : ℝ => a) (fun b : ℝ => b)]
        ring
  rw [hV]
  nlinarith [hi]

private lemma bad_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) (d : ℝ) :
    Integrable (fun z : ℝ × ℝ =>
      if d < |z.1| ∨ d < |z.2| then (z.1 - z.2) ^ 2 else 0) (ν.prod ν) := by
  have hB : MeasurableSet {z : ℝ × ℝ | d < |z.1| ∨ d < |z.2|} :=
    (measurableSet_lt measurable_const (continuous_abs.measurable.comp measurable_fst)).union
      (measurableSet_lt measurable_const (continuous_abs.measurable.comp measurable_snd))
  refine ((quadratic_pair_square_moment ν h3).1.indicator hB).congr
    (Filter.Eventually.of_forall fun z => ?_)
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

private lemma good_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) (d : ℝ) :
    Integrable (fun z : ℝ × ℝ =>
      if |z.1| ≤ d ∧ |z.2| ≤ d then (z.1 - z.2) ^ 2 else 0) (ν.prod ν) := by
  have hB : MeasurableSet {z : ℝ × ℝ | |z.1| ≤ d ∧ |z.2| ≤ d} :=
    (measurableSet_le (continuous_abs.measurable.comp measurable_fst) measurable_const).inter
      (measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const)
  refine ((quadratic_pair_square_moment ν h3).1.indicator hB).congr
    (Filter.Eventually.of_forall fun z => ?_)
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

private lemma pair_tail_pointwise (a b d : ℝ) (hd : 0 < d) :
    (if d < |a| ∨ d < |b| then (a - b) ^ 2 else 0) ≤
      (4 / d) * (|a| ^ 3 + |b| ^ 3) := by
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  by_cases h : d < |a| ∨ d < |b|
  · simp only [h, ite_true]
    have hs : d ≤ |a| + |b| := by rcases h with h | h <;> linarith
    have hab : (a - b) ^ 2 ≤ (|a| + |b|) ^ 2 := by
      have ht := abs_sub a b
      nlinarith [sq_abs (a - b), abs_nonneg (a - b)]
    have hc : (|a| + |b|) ^ 3 ≤ 4 * (|a| ^ 3 + |b| ^ 3) := by
      nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (|a| - |b|))]
    have hp : d * (a - b) ^ 2 ≤ 4 * (|a| ^ 3 + |b| ^ 3) := by
      calc
        _ ≤ d * (|a| + |b|) ^ 2 := mul_le_mul_of_nonneg_left hab hd.le
        _ ≤ (|a| + |b|) * (|a| + |b|) ^ 2 :=
          mul_le_mul_of_nonneg_right hs (sq_nonneg _)
        _ ≤ _ := by nlinarith [hc]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hd).mpr
    convert hp using 1; ring
  · simp only [h, ite_false]
    positivity

theorem quadratic_pair_tail_square_bound (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (d : ℝ) (hd : 0 < d) :
    Integrable
      (fun z : ℝ × ℝ =>
        if d < |z.1| ∨ d < |z.2| then (z.1 - z.2) ^ 2 else 0) (ν.prod ν) ∧
      (∫ z : ℝ × ℝ,
        if d < |z.1| ∨ d < |z.2| then (z.1 - z.2) ^ 2 else 0 ∂ν.prod ν) ≤
        8 * (∫ a : ℝ, |a| ^ 3 ∂ν) / d := by
  refine ⟨bad_integrable ν h3 d, ?_⟩
  calc
    _ ≤ ∫ z : ℝ × ℝ, (4 / d) * (|z.1| ^ 3 + |z.2| ^ 3) ∂ν.prod ν :=
      integral_mono (bad_integrable ν h3 d)
        (((h3.comp_fst ν).add (h3.comp_snd ν)).const_mul _)
        (fun z => pair_tail_pointwise z.1 z.2 d hd)
    _ = _ := by
      rw [integral_const_mul, integral_add (h3.comp_fst ν) (h3.comp_snd ν),
        integral_fst ν h3, integral_snd ν h3]
      ring

theorem quadratic_pair_retained_square_lower (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (d : ℝ) (hd : 0 < d)
    (hbudget : 8 * (∫ a : ℝ, |a| ^ 3 ∂ν) ≤
      d * variance (id : ℝ → ℝ) ν) :
    Integrable
      (fun z : ℝ × ℝ =>
        if |z.1| ≤ d ∧ |z.2| ≤ d then (z.1 - z.2) ^ 2 else 0) (ν.prod ν) ∧
      variance (id : ℝ → ℝ) ν ≤
        (∫ z : ℝ × ℝ,
          if |z.1| ≤ d ∧ |z.2| ≤ d then (z.1 - z.2) ^ 2 else 0 ∂ν.prod ν) := by
  refine ⟨good_integrable ν h3 d, ?_⟩
  have ht := (quadratic_pair_tail_square_bound ν h3 d hd).2
  have hlim : 8 * (∫ a : ℝ, |a| ^ 3 ∂ν) / d ≤ variance (id : ℝ → ℝ) ν :=
    (div_le_iff₀ hd).mpr (by nlinarith [hbudget])
  have he : (∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2 ∂ν.prod ν) =
      (∫ z : ℝ × ℝ, if |z.1| ≤ d ∧ |z.2| ≤ d then (z.1 - z.2) ^ 2 else 0 ∂ν.prod ν) +
      (∫ z : ℝ × ℝ, if d < |z.1| ∨ d < |z.2| then (z.1 - z.2) ^ 2 else 0 ∂ν.prod ν) := by
    rw [← integral_add (good_integrable ν h3 d) (bad_integrable ν h3 d)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      by_cases hz : |z.1| ≤ d ∧ |z.2| ≤ d
      · simp [hz, not_lt_of_ge hz.1, not_lt_of_ge hz.2]
      · have hb : d < |z.1| ∨ d < |z.2| := by
          simpa only [not_and_or, not_le] using hz
        simp [hz, hb]
  have hm := (quadratic_pair_square_moment ν h3).2
  have hr : 1 ≤ (∫ z : ℝ × ℝ,
      if |z.1| ≤ d ∧ |z.2| ≤ d then (z.1 - z.2) ^ 2 else 0 ∂ν.prod ν) /
      variance (id : ℝ → ℝ) ν := by
    apply (le_div_iff₀ hV).mpr
    linarith only [ht, hlim, he, hm]
  simpa only [one_mul] using (le_div_iff₀ hV).mp hr

private noncomputable def phase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

private lemma phase_norm (t : ℝ) : ‖phase t‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]

private lemma phase_continuous : Continuous phase := by unfold phase; fun_prop

private lemma phase_conj (t : ℝ) : (starRingEnd ℂ) (phase t) = phase (-t) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp

private lemma phase_pair (a b u v : ℝ) :
    phase (u * a + v * a ^ 2) * (starRingEnd ℂ) (phase (u * b + v * b ^ 2)) =
      phase ((a - b) * (u + v * (a + b))) := by
  rw [phase_conj]
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma phase_re (t : ℝ) : (phase t).re = Real.cos t := by
  simp [phase, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private lemma phase_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν] (u v : ℝ) :
    Integrable (fun a : ℝ => phase (u * a + v * a ^ 2)) ν := by
  refine (integrable_const (1 : ℝ)).mono'
    (phase_continuous.comp (by fun_prop)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => (phase_norm _).le)

private lemma cos_pair_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν] (u v : ℝ) :
    Integrable (fun z : ℝ × ℝ => Real.cos ((z.1 - z.2) * (u + v * (z.1 + z.2))))
      (ν.prod ν) := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun z => ?_)
  simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one ((z.1 - z.2) * (u + v * (z.1 + z.2)))

theorem quadraticChar_gap_identity (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (u v : ℝ) :
    1 - ‖quadraticChar ν u v‖ ^ 2 =
      ∫ z : ℝ × ℝ,
        1 - Real.cos ((z.1 - z.2) * (u + v * (z.1 + z.2))) ∂ν.prod ν := by
  have hg : Integrable (fun a : ℝ => (starRingEnd ℂ) (phase (u * a + v * a ^ 2))) ν := by
    simpa only [phase_conj, neg_add_rev, neg_mul, mul_neg, add_comm] using
      phase_integrable ν (-u) (-v)
  have hp := (phase_integrable ν u v).mul_prod hg
  have he : (∫ z : ℝ × ℝ, phase (u * z.1 + v * z.1 ^ 2) *
      (starRingEnd ℂ) (phase (u * z.2 + v * z.2 ^ 2)) ∂ν.prod ν) =
      quadraticChar ν u v * (starRingEnd ℂ) (quadraticChar ν u v) := by
    rw [integral_prod_mul (fun a : ℝ => phase (u * a + v * a ^ 2))
      (fun b : ℝ => (starRingEnd ℂ) (phase (u * b + v * b ^ 2))), integral_conj]
    rfl
  have hr := integral_re hp
  rw [he, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hr
  have hc : (∫ z : ℝ × ℝ, Real.cos ((z.1 - z.2) * (u + v * (z.1 + z.2))) ∂ν.prod ν) =
      ‖quadraticChar ν u v‖ ^ 2 := by
    convert hr using 1
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change Real.cos ((z.1 - z.2) * (u + v * (z.1 + z.2))) =
          (phase (u * z.1 + v * z.1 ^ 2) * (starRingEnd ℂ) (phase (u * z.2 + v * z.2 ^ 2))).re
        rw [phase_pair, phase_re]
  have hi : (∫ z : ℝ × ℝ, 1 - Real.cos ((z.1 - z.2) * (u + v * (z.1 + z.2))) ∂ν.prod ν) =
      1 - ∫ z : ℝ × ℝ, Real.cos ((z.1 - z.2) * (u + v * (z.1 + z.2))) ∂ν.prod ν := by
    rw [integral_sub (integrable_const (1 : ℝ)) (cos_pair_integrable ν u v)]
    simp
  rw [hi, hc]

private lemma small_cos_gap (t : ℝ) (ht : |t| ≤ 1) : t ^ 2 / 4 ≤ 1 - Real.cos t := by
  let x : ℝ := |t / 2|
  have hx : 0 ≤ x := abs_nonneg _
  have hx1 : x ≤ 1 := by dsimp [x]; rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
  have hx2 : x ^ 2 ≤ 1 := pow_le_one₀ hx hx1
  have hx3 : x ^ 3 ≤ x := by nlinarith [mul_nonneg hx (sub_nonneg.mpr hx2)]
  have hs := Real.abs_sub_sin_le (t / 2)
  have ha := abs_add_le (t / 2 - Real.sin (t / 2)) (Real.sin (t / 2))
  simp only [sub_add_cancel] at ha
  have hsin : (5 / 6 : ℝ) * x ≤ |Real.sin (t / 2)| := by dsimp only [x] at *; nlinarith
  have hsq : (25 / 36 : ℝ) * x ^ 2 ≤ Real.sin (t / 2) ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hsin)
      (add_nonneg (abs_nonneg (Real.sin (t / 2)))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 6) hx))
    nlinarith [sq_abs (Real.sin (t / 2))]
  have hc := Real.sin_sq_eq_half_sub (t / 2)
  rw [show 2 * (t / 2) = t by ring] at hc
  have hxv : x ^ 2 = t ^ 2 / 4 := by dsimp only [x]; rw [sq_abs]; ring
  nlinarith [hsq, sq_nonneg t]

private lemma retained_phase_gap (a b d u v : ℝ) (hd : 0 < d)
    (hu : |u| * d ≤ 1 / 3) (hv : 4 * |v| * d ≤ |u|) :
    (u ^ 2 / 16) * (if |a| ≤ d ∧ |b| ≤ d then (a - b) ^ 2 else 0) ≤
      1 - Real.cos ((a - b) * (u + v * (a + b))) := by
  by_cases h : |a| ≤ d ∧ |b| ≤ d
  · simp only [h]
    let w : ℝ := u + v * (a + b)
    change u ^ 2 / 16 * (a - b) ^ 2 ≤ 1 - Real.cos ((a - b) * w)
    have hsum : |a + b| ≤ 2 * d := (abs_add_le a b).trans (by linarith [h.1, h.2])
    have hdiff : |a - b| ≤ 2 * d := (abs_sub a b).trans (by linarith [h.1, h.2])
    have hvb : |v * (a + b)| ≤ |u| / 2 := by
      rw [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left hsum (abs_nonneg v)]
    have hupper : |w| ≤ (3 / 2) * |u| := by
      have hh := abs_add_le u (v * (a + b))
      dsimp only [w]
      linarith
    have hreverse : |u| ≤ |w| + |v * (a + b)| := by
      calc
        _ = |w - v * (a + b)| := by congr 1; dsimp [w]; ring
        _ ≤ _ := abs_sub _ _
    have hlower : |u| / 2 ≤ |w| := by linarith
    have hphase : |(a - b) * w| ≤ 1 := by
      rw [abs_mul]
      calc
        _ ≤ (2 * d) * ((3 / 2) * |u|) :=
          mul_le_mul hdiff hupper (abs_nonneg w) (by linarith)
        _ ≤ 1 := by nlinarith [hu]
    have hsq : u ^ 2 / 4 ≤ w ^ 2 := by
      have hp := mul_nonneg (sub_nonneg.mpr hlower)
        (add_nonneg (abs_nonneg w) (div_nonneg (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 2)))
      nlinarith [sq_abs u, sq_abs w]
    have hm := mul_le_mul_of_nonneg_left hsq (sq_nonneg (a - b))
    have hc := small_cos_gap ((a - b) * w) hphase
    nlinarith [hm, hc]
  · simp only [h, ite_false, mul_zero]
    linarith [Real.cos_le_one ((a - b) * (u + v * (a + b)))]

theorem quadraticChar_local_gap (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (d : ℝ) (hd : 0 < d)
    (hbudget : 8 * (∫ a : ℝ, |a| ^ 3 ∂ν) ≤
      d * variance (id : ℝ → ℝ) ν)
    (u v : ℝ) (hu : |u| * d ≤ 1 / 3)
    (hv : 4 * |v| * d ≤ |u|) :
    variance (id : ℝ → ℝ) ν * u ^ 2 / 16 ≤
      1 - ‖quadraticChar ν u v‖ ^ 2 := by
  have hk := quadratic_pair_retained_square_lower ν h3 hV d hd hbudget
  have hmon : (u ^ 2 / 16) *
      (∫ z : ℝ × ℝ, if |z.1| ≤ d ∧ |z.2| ≤ d then (z.1 - z.2) ^ 2 else 0 ∂ν.prod ν) ≤
      ∫ z : ℝ × ℝ, 1 - Real.cos ((z.1 - z.2) * (u + v * (z.1 + z.2))) ∂ν.prod ν := by
    rw [← integral_const_mul]
    exact integral_mono (hk.1.const_mul _)
      ((integrable_const (1 : ℝ)).sub (cos_pair_integrable ν u v))
      (fun z => retained_phase_gap z.1 z.2 d u v hd hu hv)
  have hpaid := mul_le_mul_of_nonneg_left hk.2
    (div_nonneg (sq_nonneg u) (by norm_num : (0 : ℝ) ≤ 16))
  rw [quadraticChar_gap_identity]
  nlinarith [hpaid, hmon]

private lemma third_moment_pos (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν) :
    0 < ∫ a : ℝ, |a| ^ 3 ∂ν := by
  have hn : 0 ≤ ∫ a : ℝ, |a| ^ 3 ∂ν := integral_nonneg (fun a => pow_nonneg (abs_nonneg a) 3)
  by_contra h
  have hz : (∫ a : ℝ, |a| ^ 3 ∂ν) = 0 := by linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun a => pow_nonneg (abs_nonneg a) 3) h3).mp hz
  have hid : (id : ℝ → ℝ) =ᵐ[ν] (fun _ => (0 : ℝ)) := by
    filter_upwards [hae] with a ha
    have hp : |a| ^ 3 = 0 := ha
    have hzero : |a| = 0 := eq_zero_of_pow_eq_zero hp
    exact abs_eq_zero.mp hzero
  have hv := variance_congr hid
  have hv0 : variance (fun _ : ℝ => (0 : ℝ)) ν = 0 := by
    rw [variance_eq_sub (memLp_const (0 : ℝ))]
    simp
  linarith

private lemma norm_le_exp_of_gap (z : ℂ) (δ : ℝ) (hgap : δ ≤ 1 - ‖z‖ ^ 2) :
    ‖z‖ ≤ Real.exp (-δ / 2) := by
  have he : Real.exp (-δ / 2) ^ 2 = Real.exp (-δ) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hx := Real.one_sub_le_exp_neg δ
  nlinarith [norm_nonneg z, Real.exp_pos (-δ / 2)]

theorem quadraticChar_lowFrequency_damping (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (u v : ℝ)
    (hu : |u| ≤ (1 / 128 : ℝ) /
      ((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν))
    (hv : |v| ≤ (1 / 128 : ℝ) * |u| /
      ((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν)) :
    ‖quadraticChar ν u v‖ ≤
        Real.exp (-(variance (id : ℝ → ℝ) ν) * u ^ 2 / 32) ∧
      ‖quadraticChar ν (-u) v‖ ≤
        Real.exp (-(variance (id : ℝ → ℝ) ν) * u ^ 2 / 32) := by
  let V : ℝ := variance (id : ℝ → ℝ) ν
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
  let γ : ℝ := m3 / V
  let d : ℝ := 16 * γ
  have hm3 : 0 < m3 := third_moment_pos ν h3 hV
  have hγ : 0 < γ := div_pos hm3 hV
  have hd : 0 < d := mul_pos (by norm_num) hγ
  have hγV : γ * V = m3 := div_mul_cancel₀ _ (ne_of_gt hV)
  have hub : |u| * γ ≤ (1 / 128 : ℝ) := (le_div_iff₀ hγ).mp hu
  have hvb : |v| * γ ≤ (1 / 128 : ℝ) * |u| := (le_div_iff₀ hγ).mp hv
  have hbudget : 8 * (∫ a : ℝ, |a| ^ 3 ∂ν) ≤ d * variance (id : ℝ → ℝ) ν := by
    change 8 * m3 ≤ d * V
    dsimp only [d]
    nlinarith [hγV]
  have hul : |u| * d ≤ 1 / 3 := by dsimp only [d]; nlinarith [hub]
  have hvl : 4 * |v| * d ≤ |u| := by dsimp only [d]; nlinarith [hvb, abs_nonneg u]
  have hg := quadraticChar_local_gap ν h3 hV d hd hbudget u v hul hvl
  have hgn := quadraticChar_local_gap ν h3 hV d hd hbudget (-u) v
    (by simpa only [abs_neg] using hul) (by simpa only [abs_neg] using hvl)
  have h1 := norm_le_exp_of_gap (quadraticChar ν u v) (V * u ^ 2 / 16) hg
  have h2 := norm_le_exp_of_gap (quadraticChar ν (-u) v) (V * u ^ 2 / 16)
    (by simpa only [neg_sq] using hgn)
  have heq : -(V * u ^ 2 / 16) / 2 = -V * u ^ 2 / 32 := by ring
  rw [heq] at h1 h2
  exact ⟨h1, h2⟩

end Shao.Probability
