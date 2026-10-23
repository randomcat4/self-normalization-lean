import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

private theorem bqt_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ᵐ a : ℝ ∂ν, |f a| ≤ C) : Integrable f ν := by
  exact (integrable_const C).mono' hf.aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs] using hC)

private theorem bqt_powers (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hh : 0 ≤ h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) (k : ℕ) :
    Integrable (fun a : ℝ => a ^ k) ν ∧
      Integrable (fun a : ℝ => |a| ^ k) ν ∧
      (∫ a : ℝ, |a| ^ k ∂ν) ≤ h ^ k := by
  have hp : ∀ᵐ a : ℝ ∂ν, |a| ^ k ≤ h ^ k := by
    filter_upwards [hs] with a ha
    exact pow_le_pow_left₀ (abs_nonneg a) ha k
  have hi : Integrable (fun a : ℝ => |a| ^ k) ν :=
    bqt_integrable ν _ (by fun_prop) _ (by
      filter_upwards [hp] with a ha
      simpa only [abs_of_nonneg (pow_nonneg (abs_nonneg a) k)] using ha)
  refine ⟨?_, hi, ?_⟩
  · exact bqt_integrable ν _ (by fun_prop) _ (by simpa only [abs_pow] using hp)
  · simpa only [integral_const, probReal_univ, one_smul] using
      integral_mono_ae hi (integrable_const (h ^ k)) hp

private theorem bqt_mean_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hh : 0 ≤ h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    |∫ a : ℝ, a ∂ν| ≤ h := by
  have hi := (bqt_powers ν h hh hs 1).1
  have ha : (∫ a : ℝ, ‖a‖ ∂ν) ≤ h := by
    simpa only [pow_one, Real.norm_eq_abs] using (bqt_powers ν h hh hs 1).2.2
  simpa only [Real.norm_eq_abs] using
    (norm_integral_le_integral_norm (f := fun a : ℝ => a)).trans ha

private theorem bqt_var_formula (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) :
    variance (id : ℝ → ℝ) ν =
      (∫ a : ℝ, a ^ 2 ∂ν) - (∫ a : ℝ, a ∂ν) ^ 2 := by
  simpa only [Pi.pow_apply, id_eq] using
    variance_eq_sub ((memLp_two_iff_integrable_sq
      measurable_id.aestronglyMeasurable).2 h2)

private theorem bqt_square_shift (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h1 : Integrable (fun a : ℝ => a) ν)
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (c : ℝ) :
    Integrable (fun a : ℝ => (a - c) ^ 2) ν ∧
      (∫ a : ℝ, (a - c) ^ 2 ∂ν) =
        variance (id : ℝ → ℝ) ν + ((∫ a : ℝ, a ∂ν) - c) ^ 2 := by
  have hi : Integrable (fun a : ℝ => a ^ 2 - (2 * c) * a + c ^ 2) ν :=
    (h2.sub (h1.const_mul (2 * c))).add (integrable_const _)
  have he : (fun a : ℝ => (a - c) ^ 2) =
      (fun a : ℝ => a ^ 2 - (2 * c) * a + c ^ 2) := by
    funext a; ring
  refine ⟨by rw [he]; exact hi, ?_⟩
  have hadd := integral_add (f := fun a : ℝ => a ^ 2 - (2 * c) * a)
    (g := fun _ : ℝ => c ^ 2) (h2.sub (h1.const_mul (2 * c)))
      (integrable_const (c ^ 2))
  have hsub := integral_sub (f := fun a : ℝ => a ^ 2)
    (g := fun a : ℝ => (2 * c) * a) h2 (h1.const_mul (2 * c))
  rw [he, hadd, hsub, integral_const_mul, integral_const,
    probReal_univ, one_smul, bqt_var_formula ν h2]
  ring

private theorem bqt_general (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (f : ℝ → ℝ) (hf : Measurable f) (L U : ℝ)
    (hLU : ∀ᵐ a : ℝ ∂ν, L ≤ f a ∧ f a ≤ U) :
    let W : ℝ → ℝ := fun a => Real.exp (f a)
    let Z : ℝ := ∫ a : ℝ, W a ∂ν
    let ρ : Measure ℝ := ν.tilted f
    let w : ℝ → ℝ := fun a => W a / Z
    let D : ℝ := U - L
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let μρ : ℝ := ∫ a : ℝ, a ∂ρ
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let Vρ : ℝ := variance (id : ℝ → ℝ) ρ
    Integrable W ν ∧ 0 < Z ∧ Real.exp L ≤ Z ∧ Z ≤ Real.exp U ∧
      L ≤ Real.log Z ∧ Real.log Z ≤ U ∧
      IsProbabilityMeasure ρ ∧ ρ ≪ ν ∧ ν ≪ ρ ∧
      (∀ᵐ a : ℝ ∂ρ, |a| ≤ h) ∧
      (∀ᵐ a : ℝ ∂ν, Real.exp (-D) ≤ w a ∧ w a ≤ Real.exp D) ∧
      (∀ g : ℝ → ℝ, Integrable g ρ ↔ Integrable g ν) ∧
      (∀ g : ℝ → ℝ, Integrable g ν →
        (∫ a : ℝ, g a ∂ρ) = ∫ a : ℝ, w a * g a ∂ν) ∧
      (∀ g : ℝ → ℝ, Integrable g ν → (∀ᵐ a : ℝ ∂ν, 0 ≤ g a) →
        Real.exp (-D) * (∫ a : ℝ, g a ∂ν) ≤ (∫ a : ℝ, g a ∂ρ) ∧
          (∫ a : ℝ, g a ∂ρ) ≤ Real.exp D * (∫ a : ℝ, g a ∂ν)) ∧
      (∀ k : ℕ,
        Integrable (fun a : ℝ => a ^ k) ν ∧
        Integrable (fun a : ℝ => a ^ k) ρ ∧
        Integrable (fun a : ℝ => |a| ^ k) ν ∧
        Integrable (fun a : ℝ => |a| ^ k) ρ ∧
        (∫ a : ℝ, |a| ^ k ∂ν) ≤ h ^ k ∧
        (∫ a : ℝ, |a| ^ k ∂ρ) ≤ h ^ k) ∧
      |μ| ≤ h ∧ |μρ| ≤ h ∧
      V = (∫ a : ℝ, a ^ 2 ∂ν) - μ ^ 2 ∧
      Vρ = (∫ a : ℝ, a ^ 2 ∂ρ) - μρ ^ 2 ∧
      Real.exp (-D) * V ≤ Vρ ∧ Vρ ≤ Real.exp D * V ∧ (Vρ = 0 ↔ V = 0) := by
  dsimp only
  let Z : ℝ := ∫ a : ℝ, Real.exp (f a) ∂ν
  let ρ : Measure ℝ := ν.tilted f
  let w : ℝ → ℝ := fun a => Real.exp (f a) / Z
  let D : ℝ := U - L
  have hW : Integrable (fun a : ℝ => Real.exp (f a)) ν :=
    bqt_integrable ν _ (Real.measurable_exp.comp hf) (Real.exp U) (by
      filter_upwards [hLU] with a ha
      simpa only [abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr ha.2)
  have hZ : 0 < Z := integral_exp_pos hW
  have hZL : Real.exp L ≤ Z := by
    have hi := integral_mono_ae (integrable_const (Real.exp L)) hW
      (hLU.mono fun a ha => Real.exp_le_exp.mpr ha.1)
    simpa only [integral_const, probReal_univ, one_smul] using hi
  have hZU : Z ≤ Real.exp U := by
    have hi := integral_mono_ae hW (integrable_const (Real.exp U))
      (hLU.mono fun a ha => Real.exp_le_exp.mpr ha.2)
    simpa only [integral_const, probReal_univ, one_smul] using hi
  letI : IsProbabilityMeasure ρ := isProbabilityMeasure_tilted hW
  have hρν : ρ ≪ ν := tilted_absolutelyContinuous ν f
  have hνρ : ν ≪ ρ := absolutelyContinuous_tilted hW
  have hsρ : ∀ᵐ a : ℝ ∂ρ, |a| ≤ h :=
    hρν.ae_le hs
  have hd : ∀ᵐ a : ℝ ∂ν, Real.exp (-D) ≤ w a ∧ w a ≤ Real.exp D := by
    filter_upwards [hLU] with a ha
    have hwL := Real.exp_le_exp.mpr ha.1
    have hwU := Real.exp_le_exp.mpr ha.2
    constructor
    · calc
        Real.exp (-D) = Real.exp L / Real.exp U := by
          rw [← Real.exp_sub]; congr 1; dsimp [D]; ring
        _ ≤ Real.exp (f a) / Z := div_le_div₀ (Real.exp_pos _).le hwL hZ hZU
    · calc
        w a ≤ Real.exp U / Real.exp L :=
          div_le_div₀ (Real.exp_pos U).le hwU (Real.exp_pos L) hZL
        _ = Real.exp D := by rw [← Real.exp_sub]
  have hL1 : ∀ g : ℝ → ℝ, Integrable g ρ ↔ Integrable g ν := by
    intro g
    rw [integrable_tilted_iff hW]
    simp only [smul_eq_mul]
    constructor
    · intro hg
      have hi := hg.bdd_mul
        (Real.measurable_exp.comp hf.neg).aestronglyMeasurable
        (c := Real.exp (-L)) (by
          filter_upwards [hLU] with a ha
          simpa only [Function.comp_apply, Pi.neg_apply, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _)] using
            Real.exp_le_exp.mpr (neg_le_neg ha.1))
      convert hi using 1
      funext a
      simp only [Function.comp_apply, Pi.neg_apply]
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    · intro hg
      exact hg.bdd_mul (Real.measurable_exp.comp hf).aestronglyMeasurable
        (c := Real.exp U) (by
          filter_upwards [hLU] with a ha
          simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
            Real.exp_le_exp.mpr ha.2)
  have hident : ∀ g : ℝ → ℝ, Integrable g ν →
      (∫ a : ℝ, g a ∂ρ) = ∫ a : ℝ, w a * g a ∂ν := by
    intro g _
    exact integral_tilted f g
  have hcompare : ∀ g : ℝ → ℝ, Integrable g ν →
      (∀ᵐ a : ℝ ∂ν, 0 ≤ g a) →
      Real.exp (-D) * (∫ a : ℝ, g a ∂ν) ≤ (∫ a : ℝ, g a ∂ρ) ∧
        (∫ a : ℝ, g a ∂ρ) ≤ Real.exp D * (∫ a : ℝ, g a ∂ν) := by
    intro g hg hn
    have hwg : Integrable (fun a => w a * g a) ν := by
      exact hg.bdd_mul ((Real.measurable_exp.comp hf).div_const Z).aestronglyMeasurable
        (c := Real.exp D) (by
          filter_upwards [hd] with a ha
          change |w a| ≤ Real.exp D
          rw [abs_of_nonneg (show 0 ≤ w a from
            div_nonneg (Real.exp_pos _).le hZ.le)]
          exact ha.2)
    rw [hident g hg]
    constructor
    · have hi := integral_mono_ae (hg.const_mul (Real.exp (-D))) hwg (by
        filter_upwards [hd, hn] with a ha hn
        exact mul_le_mul_of_nonneg_right ha.1 hn)
      simpa only [integral_const_mul] using hi
    · have hi := integral_mono_ae hwg (hg.const_mul (Real.exp D)) (by
        filter_upwards [hd, hn] with a ha hn
        exact mul_le_mul_of_nonneg_right ha.2 hn)
      simpa only [integral_const_mul] using hi
  have hp := bqt_powers ν h hh.le hs
  have hpρ := bqt_powers ρ h hh.le hsρ
  have h1 : Integrable (fun a : ℝ => a) ν := by simpa using (hp 1).1
  have h1ρ : Integrable (fun a : ℝ => a) ρ := by simpa using (hpρ 1).1
  have hvl : Real.exp (-D) * variance (id : ℝ → ℝ) ν ≤
      variance (id : ℝ → ℝ) ρ := by
    let c : ℝ := ∫ a : ℝ, a ∂ρ
    have hn := bqt_square_shift ν h1 (hp 2).1 c
    have hq := bqt_square_shift ρ h1ρ (hpρ 2).1 c
    have hi := (hcompare (fun a => (a - c) ^ 2) hn.1
      (Filter.Eventually.of_forall fun a => sq_nonneg _)).1
    rw [hn.2, hq.2] at hi
    dsimp [c] at hi
    simp only [sub_self, zero_pow (by omega : (2 : ℕ) ≠ 0), add_zero] at hi
    exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _))
      (Real.exp_pos _).le).trans hi
  have hvu : variance (id : ℝ → ℝ) ρ ≤
      Real.exp D * variance (id : ℝ → ℝ) ν := by
    let c : ℝ := ∫ a : ℝ, a ∂ν
    have hn := bqt_square_shift ν h1 (hp 2).1 c
    have hq := bqt_square_shift ρ h1ρ (hpρ 2).1 c
    have hi := (hcompare (fun a => (a - c) ^ 2) hn.1
      (Filter.Eventually.of_forall fun a => sq_nonneg _)).2
    rw [hn.2, hq.2] at hi
    dsimp [c] at hi
    simp only [sub_self, zero_pow (by omega : (2 : ℕ) ≠ 0), add_zero] at hi
    exact (le_add_of_nonneg_right (sq_nonneg _)).trans hi
  refine ⟨hW, hZ, hZL, hZU, ?_, ?_, inferInstance, hρν, hνρ, hsρ,
    hd, hL1, hident, hcompare, ?_, bqt_mean_bound ν h hh.le hs,
    bqt_mean_bound ρ h hh.le hsρ, bqt_var_formula ν (hp 2).1,
    bqt_var_formula ρ (hpρ 2).1, hvl, hvu, ?_⟩
  · exact (Real.log_exp L).ge.trans (Real.log_le_log (Real.exp_pos _) hZL)
  · exact (Real.log_le_log hZ hZU).trans (Real.log_exp U).le
  · intro k
    exact ⟨(hp k).1, (hpρ k).1, (hp k).2.1, (hpρ k).2.1,
      (hp k).2.2, (hpρ k).2.2⟩
  · constructor
    · intro hv
      have hi := hvl
      rw [hv] at hi
      have : variance (id : ℝ → ℝ) ν ≤ 0 :=
        nonpos_of_mul_nonpos_right hi (Real.exp_pos (-D))
      exact le_antisymm this (variance_nonneg _ _)
    · intro hv
      rw [hv, mul_zero] at hvu
      exact le_antisymm hvu (variance_nonneg _ _)

private theorem bqt_lyapunov (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν)
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) :
    |∫ a : ℝ, a ∂ν| * (∫ a : ℝ, a ^ 2 ∂ν) ≤ (∫ a : ℝ, |a| ^ 3 ∂ν) ∧
      |∫ a : ℝ, a ∂ν| ^ 3 ≤ (∫ a : ℝ, |a| ^ 3 ∂ν) := by
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
  let r : ℝ := Real.sqrt m2
  let μ : ℝ := ∫ a : ℝ, a ∂ν
  have hm2 : 0 ≤ m2 := integral_nonneg fun a => sq_nonneg a
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
  have hμ2 : μ ^ 2 ≤ m2 := by
    have hv := variance_nonneg (id : ℝ → ℝ) ν
    rw [bqt_var_formula ν h2] at hv
    change 0 ≤ m2 - μ ^ 2 at hv
    linarith
  have hμr : |μ| ≤ r := by nlinarith [sq_abs μ, abs_nonneg μ]
  have hf : |μ| * m2 ≤ ∫ a : ℝ, |a| ^ 3 ∂ν :=
    (mul_le_mul_of_nonneg_right hμr hm2).trans hlyap
  refine ⟨hf, ?_⟩
  have hc := mul_le_mul_of_nonneg_left hμ2 (abs_nonneg μ)
  change |μ| ^ 3 ≤ _
  have he : |μ| ^ 3 = |μ| * μ ^ 2 := by rw [pow_succ, sq_abs]; ring
  rw [he]
  exact hc.trans hf

private theorem bqt_centered_third (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    Integrable (fun a : ℝ => |a - ∫ z : ℝ, z ∂ν| ^ 3) ν ∧
      (∫ a : ℝ, |a - ∫ z : ℝ, z ∂ν| ^ 3 ∂ν) ≤
        8 * (∫ a : ℝ, |a| ^ 3 ∂ν) := by
  let μ : ℝ := ∫ a : ℝ, a ∂ν
  have hp := bqt_powers ν h hh.le hs
  have hc : Integrable (fun a : ℝ => |a - μ| ^ 3) ν :=
    bqt_integrable ν _ (by fun_prop) ((h + |μ|) ^ 3) (by
      filter_upwards [hs] with a ha
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub a μ).trans (by linarith)) 3)
  have hpoint (a : ℝ) : |a - μ| ^ 3 ≤ 4 * (|a| ^ 3 + |μ| ^ 3) := by
    have htri := pow_le_pow_left₀ (abs_nonneg (a - μ)) (abs_sub a μ) 3
    have hf := mul_nonneg (sq_nonneg (|a| - |μ|))
      (add_nonneg (abs_nonneg a) (abs_nonneg μ))
    nlinarith only [htri, hf]
  have hi := integral_mono hc (((hp 3).2.1.add (integrable_const (|μ| ^ 3))).const_mul 4)
    hpoint
  change (∫ a : ℝ, |a - μ| ^ 3 ∂ν) ≤
    ∫ a : ℝ, 4 * (|a| ^ 3 + |μ| ^ 3) ∂ν at hi
  rw [integral_const_mul, integral_add (hp 3).2.1 (integrable_const (|μ| ^ 3))] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  have hμ := (bqt_lyapunov ν (hp 2).1 (hp 3).2.1).2
  exact ⟨hc, by dsimp [μ] at hi ⊢; linarith⟩

theorem boundedQuadraticTilt_density_moments
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h b s : ℝ) (hh : 0 < h) (hs : 0 ≤ s)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    let W : ℝ → ℝ := fun a => Real.exp (b * a - s * a ^ 2)
    let Z : ℝ := ∫ a : ℝ, W a ∂ν
    let ρ : Measure ℝ := ν.tilted (fun a => b * a - s * a ^ 2)
    let w : ℝ → ℝ := fun a => W a / Z
    let S : ℝ := |b| * h + s * h ^ 2
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let μρ : ℝ := ∫ a : ℝ, a ∂ρ
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let Vρ : ℝ := variance (id : ℝ → ℝ) ρ
    Integrable W ν ∧
      0 < Z ∧
      Real.exp (-S) ≤ Z ∧ Z ≤ Real.exp S ∧
      -S ≤ Real.log Z ∧ Real.log Z ≤ S ∧
      IsProbabilityMeasure ρ ∧
      ρ ≪ ν ∧ ν ≪ ρ ∧
      (∀ᵐ a : ℝ ∂ρ, |a| ≤ h) ∧
      (∀ᵐ a : ℝ ∂ν,
        Real.exp (-(2 * S)) ≤ w a ∧ w a ≤ Real.exp (2 * S)) ∧
      (∀ g : ℝ → ℝ, Integrable g ρ ↔ Integrable g ν) ∧
      (∀ g : ℝ → ℝ, Integrable g ν →
        (∫ a : ℝ, g a ∂ρ) = ∫ a : ℝ, w a * g a ∂ν) ∧
      (∀ g : ℝ → ℝ, Integrable g ν →
        (∀ᵐ a : ℝ ∂ν, 0 ≤ g a) →
        Real.exp (-(2 * S)) * (∫ a : ℝ, g a ∂ν) ≤
            (∫ a : ℝ, g a ∂ρ) ∧
          (∫ a : ℝ, g a ∂ρ) ≤
            Real.exp (2 * S) * (∫ a : ℝ, g a ∂ν)) ∧
      (∀ k : ℕ,
        Integrable (fun a : ℝ => a ^ k) ν ∧
        Integrable (fun a : ℝ => a ^ k) ρ ∧
        Integrable (fun a : ℝ => |a| ^ k) ν ∧
        Integrable (fun a : ℝ => |a| ^ k) ρ ∧
        (∫ a : ℝ, |a| ^ k ∂ν) ≤ h ^ k ∧
        (∫ a : ℝ, |a| ^ k ∂ρ) ≤ h ^ k) ∧
      |μ| ≤ h ∧ |μρ| ≤ h ∧
      V = (∫ a : ℝ, a ^ 2 ∂ν) - μ ^ 2 ∧
      Vρ = (∫ a : ℝ, a ^ 2 ∂ρ) - μρ ^ 2 ∧
      Real.exp (-(2 * S)) * V ≤ Vρ ∧
      Vρ ≤ Real.exp (2 * S) * V ∧
      (Vρ = 0 ↔ V = 0) := by
  let S : ℝ := |b| * h + s * h ^ 2
  have hbound : ∀ᵐ a : ℝ ∂ν, -S ≤ b * a - s * a ^ 2 ∧
      b * a - s * a ^ 2 ≤ S := by
    filter_upwards [hsupport] with a ha
    have hba : |b * a| ≤ |b| * h := by rw [abs_mul]; gcongr
    have ha2 : a ^ 2 ≤ h ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) ha 2
    have hsa := mul_le_mul_of_nonneg_left ha2 hs
    have hab := abs_sub (b * a) (s * a ^ 2)
    have hsabs : |s * a ^ 2| = s * a ^ 2 := abs_of_nonneg (mul_nonneg hs (sq_nonneg a))
    rw [hsabs] at hab
    have ht : |b * a - s * a ^ 2| ≤ S := by dsimp [S]; linarith
    exact abs_le.mp ht
  have hg := bqt_general ν h hh hsupport (fun a => b * a - s * a ^ 2)
    (by fun_prop) (-S) S hbound
  have he : S - -S = 2 * S := by ring
  simpa only [he] using hg

private theorem bqt_exp_neg (t : ℝ) (ht : 0 ≤ t) :
    |Real.exp (-t) - 1| ≤ t := by
  have hu : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  linarith [Real.add_one_le_exp (-t)]

private theorem bqt_exp_neg_half (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (-t) ≤ 1 - t / 2 := by
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp t)
    (Real.exp_pos (-t)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at he
  have htpos : 0 < 1 + t := by linarith
  have hrec : Real.exp (-t) ≤ 1 / (1 + t) :=
    (le_div_iff₀ htpos).2 (by nlinarith only [he])
  exact hrec.trans ((div_le_iff₀ htpos).2 (by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr ht1)]))

private theorem bqt_abs_integral (ν : Measure ℝ) (F G : ℝ → ℝ)
    (hF : Integrable F ν) (hG : Integrable G ν)
    (hbound : ∀ᵐ a : ℝ ∂ν, |F a| ≤ G a) :
    |∫ a : ℝ, F a ∂ν| ≤ ∫ a : ℝ, G a ∂ν := by
  have hi := integral_mono_ae hF.norm hG (by
    filter_upwards [hbound] with a ha
    simpa only [Real.norm_eq_abs] using ha)
  have hn : |∫ a : ℝ, F a ∂ν| ≤ ∫ a : ℝ, ‖F a‖ ∂ν := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm F
  exact hn.trans hi

private theorem bqt_mean_tilt (ν : Measure ℝ) (f : ℝ → ℝ) :
    (∫ a : ℝ, a ∂ν.tilted f) =
      (∫ a : ℝ, a * Real.exp (f a) ∂ν) /
        (∫ a : ℝ, Real.exp (f a) ∂ν) := by
  rw [integral_tilted f (fun a : ℝ => a)]
  simp only [smul_eq_mul]
  calc
    _ = ∫ a : ℝ, (a * Real.exp (f a)) /
        (∫ a : ℝ, Real.exp (f a) ∂ν) ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun a => by ring
    _ = _ := integral_div _ _

theorem boundedEnergyTilt_drift_decay
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h s : ℝ) (hh : 0 < h) (hs : 0 ≤ s)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (hsmall : s * h ^ 2 ≤ 1) :
    let W : ℝ → ℝ := fun a => Real.exp (-s * a ^ 2)
    let Z : ℝ := ∫ a : ℝ, W a ∂ν
    let ρ : Measure ℝ := ν.tilted (fun a => -s * a ^ 2)
    let w : ℝ → ℝ := fun a => W a / Z
    let S : ℝ := s * h ^ 2
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let μρ : ℝ := ∫ a : ℝ, a ∂ρ
    let m2ρ : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
    let m3ρ : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
    let Vρ : ℝ := variance (id : ℝ → ℝ) ρ
    Integrable W ν ∧ IsProbabilityMeasure ρ ∧
      (∀ᵐ a : ℝ ∂ρ, |a| ≤ h) ∧
      Integrable (fun a : ℝ => a) ρ ∧
      Integrable (fun a : ℝ => a ^ 2) ρ ∧
      Integrable (fun a : ℝ => |a| ^ 3) ρ ∧
      Integrable (fun a : ℝ => |a - μρ| ^ 3) ρ ∧
      0 < Z ∧ Real.exp (-S) ≤ Z ∧ Z ≤ 1 ∧
      (∀ᵐ a : ℝ ∂ν,
        Real.exp (-S) ≤ w a ∧ w a ≤ Real.exp S) ∧
      Real.exp (-S) * V ≤ Vρ ∧ Vρ ≤ Real.exp S * V ∧
      Real.exp (-S) * m2 ≤ m2ρ ∧ m2ρ ≤ Real.exp S * m2 ∧
      Real.exp (-S) * m3 ≤ m3ρ ∧ m3ρ ≤ Real.exp S * m3 ∧
      Vρ = m2ρ - μρ ^ 2 ∧
      μρ - μ = (∫ a : ℝ, (a - μ) * (W a - 1) ∂ν) / Z ∧
      |μρ - μ| ≤ 2 * s * Real.exp S * m3 ∧
      |μρ| ≤ |μ| + 2 * s * Real.exp S * m3 ∧
      (∫ a : ℝ, |a - μρ| ^ 3 ∂ρ) ≤ 8 * Real.exp S * m3 ∧
      Z ≤ 1 - s * m2 / 2 ∧
      Z ≤ Real.exp (-(s * m2 / 2)) ∧
      (∀ i : ℕ, Z ^ i ≤ Real.exp (-(s * m2 / 2) * (i : ℝ))) ∧
      (s = 0 → ρ = ν ∧ Z = 1) := by
  dsimp only
  let W : ℝ → ℝ := fun a => Real.exp (-s * a ^ 2)
  let Z : ℝ := ∫ a : ℝ, W a ∂ν
  let ρ : Measure ℝ := ν.tilted (fun a => -s * a ^ 2)
  let S : ℝ := s * h ^ 2
  let μ : ℝ := ∫ a : ℝ, a ∂ν
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
  let μρ : ℝ := ∫ a : ℝ, a ∂ρ
  have hbound : ∀ᵐ a : ℝ ∂ν, -S ≤ -s * a ^ 2 ∧ -s * a ^ 2 ≤ 0 := by
    filter_upwards [hsupport] with a ha
    have ha2 : a ^ 2 ≤ h ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) ha 2
    have hi := mul_le_mul_of_nonneg_left ha2 hs
    dsimp [S]
    constructor <;> nlinarith [mul_nonneg hs (sq_nonneg a)]
  have hg := bqt_general ν h hh hsupport (fun a => -s * a ^ 2)
    (by fun_prop) (-S) 0 hbound
  dsimp only at hg
  simp only [zero_sub, neg_neg, Real.exp_zero] at hg
  obtain ⟨hW, hZ, hZL, hZU, _, _, hprob, _, _, hsρ, hd, _, _, hcompare,
    hp, _, _, _, hVρ, hvl, hvu, _⟩ := hg
  letI : IsProbabilityMeasure ρ := hprob
  have h1 : Integrable (fun a : ℝ => a) ν := by simpa only [pow_one] using (hp 1).1
  have h1ρ : Integrable (fun a : ℝ => a) ρ := by
    simpa only [pow_one] using (hp 1).2.1
  have h2 : Integrable (fun a : ℝ => a ^ 2) ν := (hp 2).1
  have h3 : Integrable (fun a : ℝ => |a| ^ 3) ν := (hp 3).2.2.1
  have hm2 : 0 ≤ m2 := integral_nonneg fun a => sq_nonneg a
  have hm3 : 0 ≤ m3 := integral_nonneg fun a => pow_nonneg (abs_nonneg a) 3
  have hWmeas : Measurable W := by dsimp [W]; fun_prop
  have hWnorm : ∀ᵐ a : ℝ ∂ν, ‖W a‖ ≤ 1 := by
    filter_upwards [hbound] with a ha
    simpa only [W, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      Real.exp_le_one_iff.mpr ha.2
  have hAW : Integrable (fun a : ℝ => a * W a) ν :=
    h1.mul_bdd hWmeas.aestronglyMeasurable hWnorm
  have hnum : Integrable (fun a : ℝ => (a - μ) * (W a - 1)) ν :=
    (h1.sub (integrable_const μ)).mul_bdd
      (hWmeas.sub measurable_const).aestronglyMeasurable (c := 2) (by
        filter_upwards [hWnorm] with a ha
        have hi := norm_sub_le (W a) 1
        simp only [Real.norm_eq_abs, norm_one] at ha hi ⊢
        linarith)
  have hmean : μρ = (∫ a : ℝ, a * W a ∂ν) / Z :=
    bqt_mean_tilt ν (fun a => -s * a ^ 2)
  have hnumval : (∫ a : ℝ, (a - μ) * (W a - 1) ∂ν) =
      (∫ a : ℝ, a * W a ∂ν) - μ * Z := by
    calc
      _ = ∫ a : ℝ, (a * W a - μ * W a) - (a - μ) ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun a => by ring
      _ = _ := by
        rw [integral_sub (f := fun a => a * W a - μ * W a)
            (g := fun a => a - μ) (hAW.sub (hW.const_mul μ))
            (h1.sub (integrable_const μ)),
          integral_sub (f := fun a => a * W a) (g := fun a => μ * W a)
            hAW (hW.const_mul μ),
          integral_sub (f := fun a : ℝ => a) (g := fun _ : ℝ => μ)
            h1 (integrable_const μ), integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul]
        change _ - μ * Z - (μ - μ) = _
        ring
  have hid : μρ - μ = (∫ a : ℝ, (a - μ) * (W a - 1) ∂ν) / Z := by
    rw [hmean, hnumval]
    have hZ0 : Z ≠ 0 := hZ.ne'
    field_simp [hZ0]
    <;> ring
  have hnumbound : |∫ a : ℝ, (a - μ) * (W a - 1) ∂ν| ≤ 2 * s * m3 := by
    have hi := bqt_abs_integral ν _ (fun a => s * (|a| ^ 3 + |μ| * a ^ 2))
      hnum ((h3.add (h2.const_mul |μ|)).const_mul s) (by
        filter_upwards with a
        have hw : |W a - 1| ≤ s * a ^ 2 := by
          simpa only [W, neg_mul] using
            bqt_exp_neg (s * a ^ 2) (mul_nonneg hs (sq_nonneg a))
        rw [abs_mul]
        calc
          |a - μ| * |W a - 1| ≤ (|a| + |μ|) * (s * a ^ 2) :=
            mul_le_mul (abs_sub a μ) hw (abs_nonneg _)
              (add_nonneg (abs_nonneg _) (abs_nonneg _))
          _ = _ := by rw [← sq_abs a]; ring)
    rw [integral_const_mul, integral_add h3 (h2.const_mul |μ|),
      integral_const_mul] at hi
    have hl := (bqt_lyapunov ν h2 h3).1
    change |μ| * m2 ≤ m3 at hl
    change |∫ a : ℝ, (a - μ) * (W a - 1) ∂ν| ≤ s * (m3 + |μ| * m2) at hi
    nlinarith [mul_le_mul_of_nonneg_left hl hs]
  have hdrift : |μρ - μ| ≤ 2 * s * Real.exp S * m3 := by
    rw [hid, abs_div, abs_of_pos hZ]
    have htop : 0 ≤ 2 * s * m3 := by positivity
    calc
      _ ≤ (2 * s * m3) / Real.exp (-S) :=
        div_le_div₀ htop hnumbound (Real.exp_pos _) hZL
      _ = _ := by rw [Real.exp_neg, div_eq_mul_inv, inv_inv]; ring
  have hraw2 := hcompare (fun a : ℝ => a ^ 2) h2
    (Filter.Eventually.of_forall fun a => sq_nonneg a)
  have hraw3 := hcompare (fun a : ℝ => |a| ^ 3) h3
    (Filter.Eventually.of_forall fun a => pow_nonneg (abs_nonneg a) 3)
  obtain ⟨hcenter, hcenterbound⟩ := bqt_centered_third ρ h hh hsρ
  have hzdec : Z ≤ 1 - s * m2 / 2 := by
    have hi := integral_mono_ae hW
      ((integrable_const (1 : ℝ)).sub (h2.const_mul (s / 2))) (by
        filter_upwards [hsupport] with a ha
        have ha2 : a ^ 2 ≤ h ^ 2 := by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) ha 2
        have ht : s * a ^ 2 ≤ 1 := (mul_le_mul_of_nonneg_left ha2 hs).trans hsmall
        have hi := bqt_exp_neg_half (s * a ^ 2) (mul_nonneg hs (sq_nonneg a)) ht
        change Real.exp (-s * a ^ 2) ≤ 1 - (s / 2) * a ^ 2
        simpa only [neg_mul, div_mul_eq_mul_div] using hi)
    change (∫ a : ℝ, Real.exp (-s * a ^ 2) ∂ν) ≤
      ∫ a : ℝ, 1 - (s / 2) * a ^ 2 ∂ν at hi
    rw [integral_sub (f := fun _ : ℝ => (1 : ℝ))
        (g := fun a : ℝ => (s / 2) * a ^ 2) (integrable_const 1) (h2.const_mul _),
      integral_const_mul] at hi
    simpa only [integral_const, probReal_univ, one_smul, div_mul_eq_mul_div] using hi
  have hzexp : Z ≤ Real.exp (-(s * m2 / 2)) :=
    hzdec.trans (by linarith [Real.add_one_le_exp (-(s * m2 / 2))])
  refine ⟨hW, hprob, hsρ, h1ρ, (hp 2).2.1, (hp 3).2.2.2.1,
    hcenter, hZ, hZL, hZU, hd, hvl, hvu, hraw2.1, hraw2.2,
    hraw3.1, hraw3.2, hVρ, hid, hdrift, ?_, ?_, hzdec, hzexp, ?_, ?_⟩
  · calc
      |μρ| = |(μρ - μ) + μ| := by congr 1; ring
      _ ≤ |μρ - μ| + |μ| := abs_add_le _ _
      _ ≤ _ := by linarith
  · exact hcenterbound.trans (by linarith [hraw3.2])
  · intro i
    have hi := pow_le_pow_left₀ hZ.le hzexp i
    simpa only [← Real.exp_nat_mul, mul_comm (i : ℝ)] using hi
  · intro hs0
    subst s
    constructor
    · simpa only [ρ, neg_zero, zero_mul] using tilted_const ν 0
    · simp [Z, W]

private theorem bqt_derivatives (b s : ℝ) :
    let F : ℝ → ℝ := fun x => Real.exp (b * x - s * x ^ 2)
    (iteratedDeriv 1 F = fun x => F x * (b - 2 * s * x)) ∧
      (iteratedDeriv 2 F = fun x => F x * ((b - 2 * s * x) ^ 2 - 2 * s)) ∧
      (iteratedDeriv 3 F = fun x =>
        F x * ((b - 2 * s * x) ^ 3 - 6 * s * (b - 2 * s * x))) := by
  dsimp only
  let F : ℝ → ℝ := fun x => Real.exp (b * x - s * x ^ 2)
  have hP (x : ℝ) : HasDerivAt (fun x => b * x - s * x ^ 2) (b - 2 * s * x) x := by
    convert ((hasDerivAt_id x).const_mul b).sub ((hasDerivAt_pow 2 x).const_mul s)
      using 1 <;> (try ext y) <;> (try dsimp only [Pi.sub_apply, Pi.pow_apply, id_eq]) <;>
      norm_num <;> ring
  have hA (x : ℝ) : HasDerivAt (fun x => b - 2 * s * x) (-2 * s) x := by
    convert ((hasDerivAt_id x).const_mul (2 * s)).const_sub b using 1 <;>
      (try ext y) <;> (try dsimp only [id_eq]) <;> ring
  have hF (x : ℝ) : HasDerivAt F (F x * (b - 2 * s * x)) x := (hP x).exp
  have hF1 (x : ℝ) : HasDerivAt (fun x => F x * (b - 2 * s * x))
      (F x * ((b - 2 * s * x) ^ 2 - 2 * s)) x := by
    convert (hF x).mul (hA x) using 1 <;>
      (try dsimp only [Pi.sub_apply, Pi.pow_apply]) <;> ring
  have hF2 (x : ℝ) : HasDerivAt
      (fun x => F x * ((b - 2 * s * x) ^ 2 - 2 * s))
      (F x * ((b - 2 * s * x) ^ 3 - 6 * s * (b - 2 * s * x))) x := by
    convert (hF x).mul (((hA x).pow 2).sub_const (2 * s)) using 1 <;>
      (try dsimp only [Pi.sub_apply, Pi.pow_apply]) <;> ring
  have hd1 : iteratedDeriv 1 F = fun x => F x * (b - 2 * s * x) := by
    rw [iteratedDeriv_one]
    exact funext fun x => (hF x).deriv
  have hd2 : iteratedDeriv 2 F = fun x => F x * ((b - 2 * s * x) ^ 2 - 2 * s) := by
    rw [iteratedDeriv_succ, hd1]
    exact funext fun x => (hF1 x).deriv
  have hd3 : iteratedDeriv 3 F = fun x =>
      F x * ((b - 2 * s * x) ^ 3 - 6 * s * (b - 2 * s * x)) := by
    rw [iteratedDeriv_succ, hd2]
    exact funext fun x => (hF2 x).deriv
  exact ⟨hd1, hd2, hd3⟩

private theorem bqt_taylor (h lam b s a : ℝ) (hh : 0 < h) (hlam : 0 ≤ lam)
    (hb : |b| = lam) (hs : 0 ≤ s) (hsquare : s ≤ lam ^ 2)
    (hslope : s * h ≤ lam) (ha : |a| ≤ h) :
    |Real.exp (b * a - s * a ^ 2) - 1 - b * a - (lam ^ 2 / 2 - s) * a ^ 2| ≤
      24 * lam ^ 3 * |a| ^ 3 * Real.exp (lam * h) := by
  let F : ℝ → ℝ := fun x => Real.exp (b * x - s * x ^ 2)
  obtain ⟨hd1, hd2, hd3⟩ := bqt_derivatives b s
  have hb2 : b ^ 2 = lam ^ 2 := by rw [← sq_abs b, hb]
  by_cases ha0 : a = 0
  · simp [ha0]
  have hcont : ContDiff ℝ 3 F := by dsimp [F]; fun_prop
  obtain ⟨t, ht, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := F) (x₀ := 0) (x := a) (n := 2) (Ne.symm ha0) hcont.contDiffOn
  have htbound : |t| ≤ h := by
    change min 0 a < t ∧ t < max 0 a at ht
    have hl : -h ≤ min 0 a := le_min (by linarith) (abs_le.mp ha).1
    have hu : max 0 a ≤ h := max_le hh.le (abs_le.mp ha).2
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hst : |s * t| ≤ lam := by
    rw [abs_mul, abs_of_nonneg hs]
    exact (mul_le_mul_of_nonneg_left htbound hs).trans hslope
  have hA : |b - 2 * s * t| ≤ 3 * lam := by
    have ht := abs_sub b (2 * s * t)
    rw [show 2 * s * t = 2 * (s * t) by ring, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      hb] at ht
    rw [show 2 * s * t = 2 * (s * t) by ring]
    linarith
  have hpoly : |(b - 2 * s * t) ^ 3 - 6 * s * (b - 2 * s * t)| ≤ 45 * lam ^ 3 := by
    calc
      _ ≤ |b - 2 * s * t| ^ 3 + 6 * s * |b - 2 * s * t| := by
        have hi := abs_sub ((b - 2 * s * t) ^ 3) (6 * s * (b - 2 * s * t))
        rw [abs_pow, abs_mul, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 6), abs_of_nonneg hs] at hi
        exact hi
      _ ≤ (3 * lam) ^ 3 + 6 * (lam ^ 2) * (3 * lam) := by
        gcongr
      _ = _ := by ring
  have hFbound : F t ≤ Real.exp (lam * h) := by
    apply Real.exp_le_exp.mpr
    have hi : b * t ≤ lam * h :=
      (le_abs_self _).trans (by rw [abs_mul, hb]; gcongr)
    nlinarith [mul_nonneg hs (sq_nonneg t)]
  have hd3bound : |iteratedDeriv 3 F t| ≤ 45 * lam ^ 3 * Real.exp (lam * h) := by
    rw [hd3]
    change |F t * _| ≤ _
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (lam * h) * (45 * lam ^ 3) :=
        mul_le_mul hFbound hpoly (abs_nonneg _) (Real.exp_pos _).le
      _ = _ := by ring
  have hwithin (k : ℕ) : iteratedDerivWithin k F (Set.uIcc 0 a) 0 = iteratedDeriv k F 0 := by
    exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (Ne.symm ha0))
      (by dsimp [F]; fun_prop : ContDiffAt ℝ k F 0) Set.left_mem_uIcc
  have htaylor : taylorWithinEval F 2 (Set.uIcc 0 a) 0 a =
      1 + b * a + (lam ^ 2 / 2 - s) * a ^ 2 := by
    rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval,
      hwithin 1, hwithin 2, hd1, hd2]
    norm_num [F]
    rw [← hb2]
    ring
  rw [htaylor] at hrem
  have hremabs : |Real.exp (b * a - s * a ^ 2) - 1 - b * a -
        (lam ^ 2 / 2 - s) * a ^ 2| = |iteratedDeriv 3 F t| * |a| ^ 3 / 6 := by
    calc
      _ = |F a - (1 + b * a + (lam ^ 2 / 2 - s) * a ^ 2)| := by
        congr 1
        dsimp [F]
        ring
      _ = _ := by rw [hrem, abs_div, abs_mul, abs_pow]; norm_num
  rw [hremabs]
  calc
    _ ≤ (45 * lam ^ 3 * Real.exp (lam * h)) * |a| ^ 3 / 6 := by gcongr
    _ ≤ _ := by
      have hp : 0 ≤ lam ^ 3 * |a| ^ 3 * Real.exp (lam * h) := by positivity
      nlinarith only [hp]

private theorem bqt_exp_abs (r : ℝ) :
    |Real.exp r - 1| ≤ Real.exp |r| * |r| := by
  by_cases hr : 0 ≤ r
  · have he : 1 ≤ Real.exp r := Real.one_le_exp_iff.mpr hr
    have hi := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-r))
      (Real.exp_pos r).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hi
    rw [abs_of_nonneg (sub_nonneg.mpr he), abs_of_nonneg hr]
    nlinarith only [hi]
  · have hr0 : r ≤ 0 := le_of_not_ge hr
    have he : Real.exp r ≤ 1 := Real.exp_le_one_iff.mpr hr0
    have hi := Real.add_one_le_exp r
    have hp := mul_le_mul_of_nonneg_right
      (Real.one_le_exp_iff.mpr (neg_nonneg.mpr hr0)) (neg_nonneg.mpr hr0)
    rw [abs_of_nonpos (sub_nonpos.mpr he), abs_of_nonpos hr0]
    nlinarith only [hi, hp]

theorem boundedQuadraticTilt_joint_moments_normalizer
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h «λ» b s : ℝ) (hh : 0 < h) («hλ» : 0 ≤ «λ»)
    (hb : b = «λ» ∨ b = -«λ»)
    (hs : 0 ≤ s) (hsquare : s ≤ «λ» ^ 2)
    (hslope : s * h ≤ «λ»)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    let W : ℝ → ℝ := fun a => Real.exp (b * a - s * a ^ 2)
    let Z : ℝ := ∫ a : ℝ, W a ∂ν
    let ρ : Measure ℝ := ν.tilted (fun a => b * a - s * a ^ 2)
    let w : ℝ → ℝ := fun a => W a / Z
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let μρ : ℝ := ∫ a : ℝ, a ∂ρ
    let m2ρ : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
    let m3ρ : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
    let Vρ : ℝ := variance (id : ℝ → ℝ) ρ
    let Γ : ℝ := 8 * Real.exp (8 * «λ» * h) * (m3 / V)
    Integrable W ν ∧ IsProbabilityMeasure ρ ∧
      (∀ᵐ a : ℝ ∂ρ, |a| ≤ h) ∧
      Integrable (fun a : ℝ => a) ρ ∧
      Integrable (fun a : ℝ => a ^ 2) ρ ∧
      Integrable (fun a : ℝ => |a| ^ 3) ρ ∧
      Integrable (fun a : ℝ => |a - μρ| ^ 3) ρ ∧
      0 < Z ∧ Real.exp (-(2 * «λ» * h)) ≤ Z ∧
      Z ≤ Real.exp («λ» * h) ∧
      (∀ᵐ a : ℝ ∂ν,
        Real.exp (-(4 * «λ» * h)) ≤ w a ∧
          w a ≤ Real.exp (4 * «λ» * h)) ∧
      Real.exp (-(4 * «λ» * h)) * V ≤ Vρ ∧
      Vρ ≤ Real.exp (4 * «λ» * h) * V ∧
      Real.exp (-(4 * «λ» * h)) * m2 ≤ m2ρ ∧
      m2ρ ≤ Real.exp (4 * «λ» * h) * m2 ∧
      m3ρ ≤ Real.exp (4 * «λ» * h) * m3 ∧
      Vρ = m2ρ - μρ ^ 2 ∧
      |μρ| ≤ Real.exp (4 * «λ» * h) * (|μ| + «λ» * m2 + s * m3) ∧
      (∫ a : ℝ, |a - μρ| ^ 3 ∂ρ) ≤
        8 * Real.exp (4 * «λ» * h) * m3 ∧
      (Vρ = 0 ↔ V = 0) ∧
      (0 < V → 0 < Vρ ∧ m3ρ / Vρ ≤ Γ) ∧
      |Z - 1 - b * μ - («λ» ^ 2 / 2 - s) * m2| ≤
        24 * «λ» ^ 3 * m3 * Real.exp («λ» * h) ∧
      Real.log Z ≤ b * μ + («λ» ^ 2 / 2 - s) * m2 +
        24 * «λ» ^ 3 * m3 * Real.exp («λ» * h) ∧
      («λ» = 0 → s = 0 ∧ ρ = ν ∧ Z = 1) := by
  dsimp only
  let lam : ℝ := «λ»
  let W : ℝ → ℝ := fun a => Real.exp (b * a - s * a ^ 2)
  let Z : ℝ := ∫ a : ℝ, W a ∂ν
  let ρ : Measure ℝ := ν.tilted (fun a => b * a - s * a ^ 2)
  let μ : ℝ := ∫ a : ℝ, a ∂ν
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
  let V : ℝ := variance (id : ℝ → ℝ) ν
  let μρ : ℝ := ∫ a : ℝ, a ∂ρ
  let m3ρ : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
  let Vρ : ℝ := variance (id : ℝ → ℝ) ρ
  have hbabs : |b| = lam := by
    rcases hb with hb | hb <;> rw [hb] <;>
      simp only [lam, abs_neg, abs_of_nonneg «hλ»]
  have hlh : 0 ≤ lam * h := mul_nonneg «hλ» hh.le
  have hactual : ∀ᵐ a : ℝ ∂ν, -(2 * lam * h) ≤ b * a - s * a ^ 2 ∧
      b * a - s * a ^ 2 ≤ lam * h := by
    filter_upwards [hsupport] with a ha
    have hba : |b * a| ≤ lam * h := by rw [abs_mul, hbabs]; gcongr
    have ha2 : a ^ 2 ≤ h ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) ha 2
    have hs1 := mul_le_mul_of_nonneg_left ha2 hs
    have hs2 := mul_le_mul_of_nonneg_right hslope hh.le
    have hab := abs_le.mp hba
    constructor <;> nlinarith [mul_nonneg hs (sq_nonneg a)]
  have hbox : ∀ᵐ a : ℝ ∂ν, -(2 * lam * h) ≤ b * a - s * a ^ 2 ∧
      b * a - s * a ^ 2 ≤ 2 * lam * h :=
    hactual.mono fun a ha => ⟨ha.1, ha.2.trans (by nlinarith)⟩
  have hg := bqt_general ν h hh hsupport (fun a => b * a - s * a ^ 2)
    (by fun_prop) (-(2 * lam * h)) (2 * lam * h) hbox
  dsimp only at hg
  rw [show 2 * lam * h - -(2 * lam * h) = 4 * lam * h by ring] at hg
  obtain ⟨hW, hZ, hZL, _, _, _, hprob, _, _, hsρ, hd, _, _, hcompare,
    hp, _, _, _, hVρ, hvl, hvu, hzero⟩ := hg
  letI : IsProbabilityMeasure ρ := hprob
  have h1 : Integrable (fun a : ℝ => a) ν := by simpa only [pow_one] using (hp 1).1
  have h1ρ : Integrable (fun a : ℝ => a) ρ := by
    simpa only [pow_one] using (hp 1).2.1
  have h2 : Integrable (fun a : ℝ => a ^ 2) ν := (hp 2).1
  have h3 : Integrable (fun a : ℝ => |a| ^ 3) ν := (hp 3).2.2.1
  have hm2 : 0 ≤ m2 := integral_nonneg fun a => sq_nonneg a
  have hm3 : 0 ≤ m3 := integral_nonneg fun a => pow_nonneg (abs_nonneg a) 3
  have hZU : Z ≤ Real.exp (lam * h) := by
    have hi := integral_mono_ae hW (integrable_const (Real.exp (lam * h)))
      (hactual.mono fun a ha => Real.exp_le_exp.mpr ha.2)
    simpa only [integral_const, probReal_univ, one_smul] using hi
  have hWmeas : Measurable W := by dsimp [W]; fun_prop
  have hWnorm : ∀ᵐ a : ℝ ∂ν, ‖W a‖ ≤ Real.exp (2 * lam * h) := by
    filter_upwards [hbox] with a ha
    simpa only [W, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      Real.exp_le_exp.mpr ha.2
  have hnum : Integrable (fun a : ℝ => a * (W a - 1)) ν :=
    h1.mul_bdd (hWmeas.sub measurable_const).aestronglyMeasurable
      (c := Real.exp (2 * lam * h) + 1) (by
        filter_upwards [hWnorm] with a ha
        have hi := norm_sub_le (W a) 1
        simp only [Real.norm_eq_abs, norm_one] at ha hi ⊢
        linarith)
  have hnumBound : |∫ a : ℝ, a * (W a - 1) ∂ν| ≤
      Real.exp (2 * lam * h) * (lam * m2 + s * m3) := by
    have hi := bqt_abs_integral ν _
      (fun a => Real.exp (2 * lam * h) * (lam * a ^ 2 + s * |a| ^ 3))
      hnum (((h2.const_mul lam).add (h3.const_mul s)).const_mul _) (by
        filter_upwards [hbox] with a ha
        have habs : |b * a - s * a ^ 2| ≤ 2 * lam * h := abs_le.mpr ha
        have hlin : |b * a - s * a ^ 2| ≤ lam * |a| + s * a ^ 2 := by
          have hi := abs_sub (b * a) (s * a ^ 2)
          rw [abs_mul, hbabs, abs_of_nonneg (mul_nonneg hs (sq_nonneg a))] at hi
          exact hi
        have hw : |W a - 1| ≤ Real.exp (2 * lam * h) *
            (lam * |a| + s * a ^ 2) :=
          (bqt_exp_abs (b * a - s * a ^ 2)).trans
            (mul_le_mul (Real.exp_le_exp.mpr habs) hlin (abs_nonneg _)
              (Real.exp_pos _).le)
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left hw (abs_nonneg a)).trans_eq (by
          rw [← sq_abs a]
          ring))
    rw [integral_const_mul,
      integral_add (h2.const_mul lam) (h3.const_mul s), integral_const_mul,
      integral_const_mul] at hi
    exact hi
  have hnumval : (∫ a : ℝ, a * W a ∂ν) =
      μ + (∫ a : ℝ, a * (W a - 1) ∂ν) := by
    change _ = (∫ a : ℝ, a ∂ν) + _
    rw [← integral_add h1 hnum]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun a => by ring
  have hmean : μρ = (μ + ∫ a : ℝ, a * (W a - 1) ∂ν) / Z := by
    rw [show μρ = (∫ a : ℝ, a * W a ∂ν) / Z from
      bqt_mean_tilt ν (fun a => b * a - s * a ^ 2), hnumval]
  have hmeanBound : |μρ| ≤ Real.exp (4 * lam * h) * (|μ| + lam * m2 + s * m3) := by
    let K : ℝ := Real.exp (2 * lam * h)
    let B : ℝ := lam * m2 + s * m3
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hK : 1 ≤ K := Real.one_le_exp_iff.mpr (by nlinarith)
    have hKpos : 0 < K := Real.exp_pos _
    have hK2 : K * K = Real.exp (4 * lam * h) := by
      dsimp [K]
      rw [← Real.exp_add]
      congr 1
      ring
    have hn : |μ + ∫ a : ℝ, a * (W a - 1) ∂ν| ≤ |μ| + K * B :=
      (abs_add_le _ _).trans (by dsimp [K, B]; linarith)
    rw [hmean, abs_div, abs_of_pos hZ]
    calc
      _ ≤ (|μ| + K * B) / Real.exp (-(2 * lam * h)) :=
        div_le_div₀ (by positivity) hn (Real.exp_pos _) hZL
      _ = K * |μ| + (K * K) * B := by
        rw [Real.exp_neg, div_eq_mul_inv, inv_inv]
        dsimp [K]
        ring
      _ ≤ (K * K) * (|μ| + B) := by
        have hi := mul_le_mul_of_nonneg_left hK hKpos.le
        have hj := mul_le_mul_of_nonneg_right hi (abs_nonneg μ)
        nlinarith only [hj]
      _ = _ := by rw [hK2]; dsimp [B]; ring
  have hraw2 := hcompare (fun a : ℝ => a ^ 2) h2
    (Filter.Eventually.of_forall fun a => sq_nonneg a)
  have hraw3 := (hcompare (fun a : ℝ => |a| ^ 3) h3
    (Filter.Eventually.of_forall fun a => pow_nonneg (abs_nonneg a) 3)).2
  obtain ⟨hcenter, hcenterBound⟩ := bqt_centered_third ρ h hh hsρ
  have hratio : 0 < V → 0 < Vρ ∧ m3ρ / Vρ ≤
      8 * Real.exp (8 * lam * h) * (m3 / V) := by
    intro hV
    have hVρpos : 0 < Vρ := (mul_pos (Real.exp_pos _) hV).trans_le hvl
    refine ⟨hVρpos, ?_⟩
    calc
      m3ρ / Vρ ≤ (Real.exp (4 * lam * h) * m3) /
          (Real.exp (-(4 * lam * h)) * V) :=
        div_le_div₀ (mul_nonneg (Real.exp_pos _).le hm3) hraw3
          (mul_pos (Real.exp_pos _) hV) hvl
      _ = Real.exp (8 * lam * h) * (m3 / V) := by
        have he : Real.exp (8 * lam * h) =
            Real.exp (4 * lam * h) * Real.exp (4 * lam * h) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [he, Real.exp_neg]
        field_simp
      _ ≤ _ := by
        have hn : 0 ≤ Real.exp (8 * lam * h) * (m3 / V) :=
          mul_nonneg (Real.exp_pos _).le (div_nonneg hm3 hV.le)
        nlinarith only [hn]
  have hRint : Integrable
      (fun a : ℝ => W a - 1 - b * a - (lam ^ 2 / 2 - s) * a ^ 2) ν :=
    ((hW.sub (integrable_const 1)).sub (h1.const_mul b)).sub
      (h2.const_mul (lam ^ 2 / 2 - s))
  have hRval : (∫ a : ℝ, W a - 1 - b * a - (lam ^ 2 / 2 - s) * a ^ 2 ∂ν) =
      Z - 1 - b * μ - (lam ^ 2 / 2 - s) * m2 := by
    rw [integral_sub (f := fun a => W a - 1 - b * a)
        (g := fun a => (lam ^ 2 / 2 - s) * a ^ 2)
        ((hW.sub (integrable_const 1)).sub (h1.const_mul b))
        (h2.const_mul (lam ^ 2 / 2 - s)),
      integral_sub (f := fun a => W a - 1) (g := fun a => b * a)
        (hW.sub (integrable_const 1)) (h1.const_mul b),
      integral_sub (f := W) (g := fun _ : ℝ => (1 : ℝ)) hW (integrable_const 1),
      integral_const_mul, integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    rfl
  have hTaylor : |Z - 1 - b * μ - (lam ^ 2 / 2 - s) * m2| ≤
      24 * lam ^ 3 * m3 * Real.exp (lam * h) := by
    have hi := bqt_abs_integral ν _
      (fun a => (24 * lam ^ 3 * Real.exp (lam * h)) * |a| ^ 3)
      hRint (h3.const_mul _) (by
        filter_upwards [hsupport] with a ha
        have hi := bqt_taylor h lam b s a hh «hλ» hbabs hs hsquare hslope ha
        convert hi using 1 <;> ring)
    rw [hRval, integral_const_mul] at hi
    convert hi using 1 <;> ring
  have hlog : Real.log Z ≤ b * μ + (lam ^ 2 / 2 - s) * m2 +
      24 * lam ^ 3 * m3 * Real.exp (lam * h) := by
    have hl := Real.log_le_sub_one_of_pos hZ
    have hr := (abs_le.mp hTaylor).2
    linarith
  refine ⟨hW, hprob, hsρ, h1ρ, (hp 2).2.1, (hp 3).2.2.2.1,
    hcenter, hZ, hZL, hZU, hd, hvl, hvu, hraw2.1, hraw2.2, hraw3,
    hVρ, hmeanBound, ?_, hzero, hratio, hTaylor, hlog, ?_⟩
  · exact hcenterBound.trans (by linarith [hraw3])
  · intro hlam0
    have hs0 : s = 0 := le_antisymm (by simpa only [hlam0, zero_pow (by omega : (2 : ℕ) ≠ 0)] using hsquare) hs
    have hb0 : b = 0 := by rcases hb with hb | hb <;> simpa only [hlam0, neg_zero] using hb
    refine ⟨hs0, ?_, ?_⟩
    · simpa only [ρ, hb0, hs0, zero_mul, sub_zero] using tilted_const ν 0
    · simp only [Z, W, hb0, hs0, zero_mul, sub_zero, Real.exp_zero,
        integral_const, probReal_univ, one_smul]

end Shao.Probability
