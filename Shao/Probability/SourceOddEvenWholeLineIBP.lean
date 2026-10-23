import Shao.Probability.SourceFutureNoiseOddEven
import Shao.Probability.QuadraticCharacteristicPower
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped Topology FourierTransform

private def boundedC2 (f : ℝ → ℝ → ℂ) : Prop :=
  (∀ v : ℝ, Differentiable ℝ (f v)) ∧ (∀ v : ℝ, Differentiable ℝ (deriv (f v))) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v u : ℝ,
      ‖f v u‖ ≤ C ∧ ‖deriv (f v) u‖ ≤ C ∧ ‖deriv (deriv (f v)) u‖ ≤ C

private lemma boundedC2_const (c : ℂ) : boundedC2 (fun (_ : ℝ) (_ : ℝ) => c) := by
  refine ⟨fun _ => differentiable_const c, ?_, ‖c‖, norm_nonneg c, ?_⟩
  · simp
  · intro v u
    simp [norm_nonneg]

private lemma boundedC2_add (f g : ℝ → ℝ → ℂ) (hf : boundedC2 f) (hg : boundedC2 g) :
    boundedC2 (fun v u => f v u + g v u) := by
  obtain ⟨hfd, hfdd, A, hA, hfB⟩ := hf
  obtain ⟨hgd, hgdd, B, hB, hgB⟩ := hg
  have he (v : ℝ) : deriv (fun u => f v u + g v u) = fun u => deriv (f v) u + deriv (g v) u :=
    funext fun u => ((hfd v u).hasDerivAt.add (hgd v u).hasDerivAt).deriv
  have hde (v : ℝ) : Differentiable ℝ (deriv (fun u => f v u + g v u)) := by
    rw [he]
    exact (hfdd v).add (hgdd v)
  refine ⟨fun v => (hfd v).add (hgd v), hde, A + B, add_nonneg hA hB, fun v u => ⟨?_, ?_, ?_⟩⟩
  · exact (norm_add_le _ _).trans (add_le_add (hfB v u).1 (hgB v u).1)
  · rw [he]
    exact (norm_add_le _ _).trans (add_le_add (hfB v u).2.1 (hgB v u).2.1)
  · rw [he]
    change ‖deriv (deriv (f v) + deriv (g v)) u‖ ≤ _
    rw [((hfdd v u).hasDerivAt.add (hgdd v u).hasDerivAt).deriv]
    exact (norm_add_le _ _).trans (add_le_add (hfB v u).2.2 (hgB v u).2.2)

private lemma boundedC2_mul (f g : ℝ → ℝ → ℂ) (hf : boundedC2 f) (hg : boundedC2 g) :
    boundedC2 (fun v u => f v u * g v u) := by
  obtain ⟨hfd, hfdd, A, hA, hfB⟩ := hf
  obtain ⟨hgd, hgdd, B, hB, hgB⟩ := hg
  have he (v u : ℝ) : deriv (fun r => f v r * g v r) u = deriv (f v) u * g v u + f v u * deriv (g v) u :=
    ((hfd v u).hasDerivAt.mul (hgd v u).hasDerivAt).deriv
  have hdd (v u : ℝ) : HasDerivAt (deriv (fun r => f v r * g v r))
      ((deriv (deriv (f v)) u * g v u + deriv (f v) u * deriv (g v) u) +
        (deriv (f v) u * deriv (g v) u + f v u * deriv (deriv (g v)) u)) u := by
    exact (((hfdd v u).hasDerivAt.mul (hgd v u).hasDerivAt).add
      ((hfd v u).hasDerivAt.mul (hgdd v u).hasDerivAt)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (he v))
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  refine ⟨fun v => (hfd v).mul (hgd v), fun v u => (hdd v u).differentiableAt,
    4 * A * B, by positivity, fun v u => ⟨?_, ?_, ?_⟩⟩
  · calc
      _ = ‖f v u‖ * ‖g v u‖ := norm_mul _ _
      _ ≤ A * B := mul_le_mul (hfB v u).1 (hgB v u).1 (norm_nonneg _) hA
      _ ≤ _ := by nlinarith
  · rw [he]
    calc
      _ ≤ ‖deriv (f v) u‖ * ‖g v u‖ + ‖f v u‖ * ‖deriv (g v) u‖ := by
        simpa only [norm_mul] using norm_add_le (deriv (f v) u * g v u) (f v u * deriv (g v) u)
      _ ≤ A * B + A * B := add_le_add
        (mul_le_mul (hfB v u).2.1 (hgB v u).1 (norm_nonneg _) hA)
        (mul_le_mul (hfB v u).1 (hgB v u).2.1 (norm_nonneg _) hA)
      _ ≤ _ := by nlinarith
  · rw [(hdd v u).deriv]
    calc
      _ ≤ (‖deriv (deriv (f v)) u‖ * ‖g v u‖ + ‖deriv (f v) u‖ * ‖deriv (g v) u‖) +
          (‖deriv (f v) u‖ * ‖deriv (g v) u‖ + ‖f v u‖ * ‖deriv (deriv (g v)) u‖) := by
        exact (norm_add_le _ _).trans (add_le_add
          (by simpa only [norm_mul] using (norm_add_le
            (deriv (deriv (f v)) u * g v u) (deriv (f v) u * deriv (g v) u)))
          (by simpa only [norm_mul] using (norm_add_le
            (deriv (f v) u * deriv (g v) u) (f v u * deriv (deriv (g v)) u))))
      _ ≤ (A * B + A * B) + (A * B + A * B) := by
        apply add_le_add <;> apply add_le_add
        · exact mul_le_mul (hfB v u).2.2 (hgB v u).1 (norm_nonneg _) hA
        · exact mul_le_mul (hfB v u).2.1 (hgB v u).2.1 (norm_nonneg _) hA
        · exact mul_le_mul (hfB v u).2.1 (hgB v u).2.1 (norm_nonneg _) hA
        · exact mul_le_mul (hfB v u).1 (hgB v u).2.2 (norm_nonneg _) hA
      _ = _ := by ring

private lemma boundedC2_const_mul (c : ℂ) (f : ℝ → ℝ → ℂ) (hf : boundedC2 f) :
    boundedC2 (fun v u => c * f v u) := boundedC2_mul _ _ (boundedC2_const c) hf

private lemma boundedC2_pow (f : ℝ → ℝ → ℂ) (hf : boundedC2 f) (n : ℕ) :
    boundedC2 (fun v u => f v u ^ n) := by
  induction n with
  | zero => simpa using boundedC2_const 1
  | succ n ih => simpa only [pow_succ] using boundedC2_mul _ _ ih hf

private lemma boundedC2_reflect (f : ℝ → ℝ → ℂ) (hf : boundedC2 f) :
    boundedC2 (fun v u => f v (-u)) := by
  obtain ⟨hfd, hfdd, A, hA, hfB⟩ := hf
  have hn (u : ℝ) : HasDerivAt (fun r : ℝ => -r) (-1 : ℝ) u := by
    exact hasDerivAt_neg' u
  have hd (v u : ℝ) : HasDerivAt (fun r => f v (-r)) (-deriv (f v) (-u)) u := by
    simpa only [Function.comp_def, neg_one_smul] using
      (hfd v (-u)).hasDerivAt.scomp u (hn u)
  have hdd (v u : ℝ) : HasDerivAt (deriv (fun r => f v (-r))) (deriv (deriv (f v)) (-u)) u := by
    have ht := ((hfdd v (-u)).hasDerivAt.scomp u (hn u)).neg
    simpa only [neg_one_smul, neg_neg] using ht.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r => (hd v r).deriv)
  refine ⟨fun v u => (hd v u).differentiableAt, fun v u => (hdd v u).differentiableAt,
    A, hA, fun v u => ⟨(hfB v (-u)).1, ?_, ?_⟩⟩
  · simpa only [(hd v u).deriv, norm_neg] using (hfB v (-u)).2.1
  · simpa only [(hdd v u).deriv] using (hfB v (-u)).2.2

private noncomputable def characteristicMoment {Ω : Type*} [MeasurableSpace Ω]
    (_μ : Measure Ω) (X Y : Ω → ℝ) (v : ℝ) (j : ℕ) (u : ℝ) (ω : Ω) : ℂ :=
  (Complex.I * (X ω : ℂ)) ^ j *
    Complex.exp (((u * X ω + v * Y ω : ℝ) : ℂ) * Complex.I)

private lemma characteristicMoment_norm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) (v : ℝ) (j : ℕ) (u : ℝ) (ω : Ω) :
    ‖characteristicMoment μ X Y v j u ω‖ = |X ω| ^ j := by
  simp [characteristicMoment, norm_pow, Complex.norm_exp, Complex.mul_re]

private lemma characteristicMoment_hasDerivAt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) (v : ℝ) (j : ℕ) (u : ℝ) (ω : Ω) :
    HasDerivAt (fun r => characteristicMoment μ X Y v j r ω)
      (characteristicMoment μ X Y v (j + 1) u ω) u := by
  have he := (((((hasDerivAt_id u).mul_const (X ω)).add_const (v * Y ω)).ofReal_comp).mul_const
    Complex.I).cexp
  convert he.const_mul ((Complex.I * (X ω : ℂ)) ^ j) using 1
  · rfl
  · dsimp [characteristicMoment]
    rw [pow_succ]
    ring

private lemma characteristicIntegral_hasDerivAt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (v : ℝ) (j : ℕ) (hj : Integrable (fun ω => |X ω| ^ j) μ)
    (hj1 : Integrable (fun ω => |X ω| ^ (j + 1)) μ) (u : ℝ) :
    HasDerivAt (fun r => ∫ ω, characteristicMoment μ X Y v j r ω ∂μ)
      (∫ ω, characteristicMoment μ X Y v (j + 1) u ω ∂μ) u := by
  have hm (k : ℕ) (r : ℝ) : AEStronglyMeasurable (characteristicMoment μ X Y v k r) μ := by
    unfold characteristicMoment
    fun_prop
  have hi : Integrable (characteristicMoment μ X Y v j u) μ :=
    hj.mono' (hm j u) (Filter.Eventually.of_forall fun ω =>
      (characteristicMoment_norm μ X Y v j u ω).le)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (F' := characteristicMoment μ X Y v (j + 1))
    (bound := fun ω => |X ω| ^ (j + 1)) (by simp)
    (Filter.Eventually.of_forall fun r => hm j r) hi (hm (j + 1) u)
    (Filter.Eventually.of_forall fun ω r _ => (characteristicMoment_norm μ X Y v (j + 1) r ω).le)
    hj1 (Filter.Eventually.of_forall fun ω r _ =>
      characteristicMoment_hasDerivAt μ X Y v j r ω)).2

private lemma characteristic_boundedC2 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (h1 : Integrable (fun ω => |X ω|) μ) (h2 : Integrable (fun ω => X ω ^ 2) μ)
    : boundedC2 (fun v u => ∫ ω, Complex.exp
      (((u * X ω + v * Y ω : ℝ) : ℂ) * Complex.I) ∂μ) := by
  let f : ℝ → ℝ → ℂ := fun v u => ∫ ω, Complex.exp
    (((u * X ω + v * Y ω : ℝ) : ℂ) * Complex.I) ∂μ
  have h0 : Integrable (fun ω : Ω => |X ω| ^ 0) μ := by simp
  have h1' : Integrable (fun ω => |X ω| ^ 1) μ := by simpa using h1
  have h2' : Integrable (fun ω => |X ω| ^ 2) μ := by simpa only [sq_abs] using h2
  have hd (v u : ℝ) : HasDerivAt (f v) (∫ ω, characteristicMoment μ X Y v 1 u ω ∂μ) u := by
    simpa only [characteristicMoment, pow_zero, one_mul] using
      characteristicIntegral_hasDerivAt μ X Y hX hY v 0 h0 h1' u
  have hdd (v u : ℝ) : HasDerivAt (deriv (f v))
      (∫ ω, characteristicMoment μ X Y v 2 u ω ∂μ) u :=
    (characteristicIntegral_hasDerivAt μ X Y hX hY v 1 h1' h2' u).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r => (hd v r).deriv)
  have hb (j : ℕ) (hj : Integrable (fun ω => |X ω| ^ j) μ) (v u : ℝ) :
      ‖∫ ω, characteristicMoment μ X Y v j u ω ∂μ‖ ≤ ∫ ω, |X ω| ^ j ∂μ :=
    norm_integral_le_of_norm_le hj (Filter.Eventually.of_forall fun ω =>
      (characteristicMoment_norm μ X Y v j u ω).le)
  have hp1 : 0 ≤ ∫ ω, |X ω| ∂μ := integral_nonneg fun _ => abs_nonneg _
  have hp2 : 0 ≤ ∫ ω, X ω ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  refine ⟨fun v u => (hd v u).differentiableAt, fun v u => (hdd v u).differentiableAt,
    1 + (∫ ω, |X ω| ∂μ) + (∫ ω, X ω ^ 2 ∂μ), by positivity, fun v u => ⟨?_, ?_, ?_⟩⟩
  · have hbf : ‖f v u‖ ≤ 1 := by simpa [f, characteristicMoment] using hb 0 h0 v u
    exact hbf.trans (by linarith)
  · rw [(hd v u).deriv]
    have hbf := hb 1 h1' v u
    simp only [pow_one] at hbf
    exact hbf.trans (by linarith)
  · rw [(hdd v u).deriv]
    have hbf := hb 2 h2' v u
    simp only [sq_abs] at hbf
    exact hbf.trans (by linarith)

private noncomputable def densitySchwartz : SchwartzMap ℝ ℂ :=
  (sourceScalarDensity_data.2.1.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp sourceScalarDensity_data.1)

private lemma scalarChar_fourier (t : ℝ) :
    sourceScalarChar t = 𝓕 densitySchwartz (-t / (2 * Real.pi)) := by
  unfold sourceScalarChar sourceScalarLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    sourceScalarDensity_data.1.continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r => by
    have he : -2 * Real.pi * r * (-t / (2 * Real.pi)) = t * r := by field_simp
    simp only [ENNReal.toReal_ofReal (sourceScalarDensity_data.2.2.1 r), Complex.real_smul,
      smul_eq_mul, he]
    change (sourceScalarDensity r : ℂ) * Complex.exp (((t * r : ℝ) : ℂ) * Complex.I) = _
    rw [mul_comm (sourceScalarDensity r : ℂ)]
    congr 1

private lemma scaledScalar_schwartz (gamma : ℝ) (hg : gamma ≠ 0) :
    ∃ s : SchwartzMap ℝ ℂ, (fun u : ℝ => sourceScalarChar (gamma * u)) = s := by
  let c : ℝ := -gamma / (2 * Real.pi)
  have hc : c ≠ 0 := div_ne_zero (neg_ne_zero.mpr hg) (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  let L : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ) (Units.mk0 c hc)
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L (𝓕 densitySchwartz), ?_⟩
  funext u
  rw [scalarChar_fourier]
  change 𝓕 densitySchwartz (-(gamma * u) / (2 * Real.pi)) = 𝓕 densitySchwartz (c * u)
  congr 1
  dsimp [c]
  ring

private lemma schwartz_product_data (p : ℝ → ℝ → ℂ) (hp : boundedC2 p) (s : SchwartzMap ℝ ℂ) (v : ℝ) :
    let F : ℝ → ℂ := fun u => p v u * s u
    Differentiable ℝ F ∧ Differentiable ℝ (deriv F) ∧
      Integrable F ∧ Integrable (deriv F) ∧ Integrable (deriv (deriv F)) := by
  obtain ⟨hpd, hpdd, C, hC, hB⟩ := hp
  let s1 : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ s
  let s2 : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ s1
  have hs1 : (deriv s : ℝ → ℂ) = s1 := rfl
  have hs2 : (deriv (deriv s) : ℝ → ℂ) = s2 := rfl
  have hd (u : ℝ) : HasDerivAt (fun r => p v r * s r)
      (deriv (p v) u * s u + p v u * s1 u) u := (hpd v u).hasDerivAt.mul (s.hasDerivAt u)
  have hdd (u : ℝ) : HasDerivAt (deriv (fun r => p v r * s r))
      ((deriv (deriv (p v)) u * s u + deriv (p v) u * s1 u) +
        (deriv (p v) u * s1 u + p v u * s2 u)) u :=
    (((hpdd v u).hasDerivAt.mul (s.hasDerivAt u)).add
      ((hpd v u).hasDerivAt.mul (s1.hasDerivAt u))).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun r => (hd r).deriv)
  have hi0 (t : SchwartzMap ℝ ℂ) : Integrable (fun u => p v u * t u) :=
    t.integrable.bdd_mul (hpd v).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => (hB v u).1)
  have hi1 (t : SchwartzMap ℝ ℂ) : Integrable (fun u => deriv (p v) u * t u) :=
    t.integrable.bdd_mul (aestronglyMeasurable_deriv (p v) volume)
      (Filter.Eventually.of_forall fun u => (hB v u).2.1)
  have hi2 (t : SchwartzMap ℝ ℂ) : Integrable (fun u => deriv (deriv (p v)) u * t u) :=
    t.integrable.bdd_mul (aestronglyMeasurable_deriv (deriv (p v)) volume)
      (Filter.Eventually.of_forall fun u => (hB v u).2.2)
  refine ⟨fun u => (hd u).differentiableAt, fun u => (hdd u).differentiableAt,
    hi0 s, ?_, ?_⟩
  · exact ((hi1 s).add (hi0 s1)).congr
      (Filter.Eventually.of_forall fun u => (hd u).deriv.symm)
  · exact (((hi2 s).add (hi1 s1)).add ((hi1 s1).add (hi0 s2))).congr
      (Filter.Eventually.of_forall fun u => (hdd u).deriv.symm)

private lemma schwartz_product_envelope (p : ℝ → ℝ → ℂ) (hp : boundedC2 p)
    (s : SchwartzMap ℝ ℂ) :
    let F : ℝ → ℝ → ℂ := fun v u => p v u * s u
    ∃ B : ℝ → ℝ, (∀ u : ℝ, 0 ≤ B u) ∧
      (∀ k : ℕ, Integrable (fun u : ℝ => |u| ^ k * B u)) ∧
      ∀ u v : ℝ, ‖F v u‖ ≤ B u ∧ ‖deriv (F v) u‖ ≤ B u ∧
        ‖deriv (deriv (F v)) u‖ ≤ B u := by
  obtain ⟨hpd, hpdd, C, hC, hB⟩ := hp
  let s1 : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ s
  let s2 : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ s1
  let B : ℝ → ℝ := fun u => C * (‖s u‖ + 2 * ‖s1 u‖ + ‖s2 u‖)
  have hd (v u : ℝ) : HasDerivAt (fun r => p v r * s r)
      (deriv (p v) u * s u + p v u * s1 u) u := (hpd v u).hasDerivAt.mul (s.hasDerivAt u)
  have hdd (v u : ℝ) : HasDerivAt (deriv (fun r => p v r * s r))
      ((deriv (deriv (p v)) u * s u + deriv (p v) u * s1 u) +
        (deriv (p v) u * s1 u + p v u * s2 u)) u :=
    (((hpdd v u).hasDerivAt.mul (s.hasDerivAt u)).add
      ((hpd v u).hasDerivAt.mul (s1.hasDerivAt u))).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun r => (hd v r).deriv)
  refine ⟨B, fun u => by dsimp [B]; positivity, ?_, fun u v => ⟨?_, ?_, ?_⟩⟩
  · intro k
    have hi (t : SchwartzMap ℝ ℂ) : Integrable (fun u : ℝ => |u| ^ k * ‖t u‖) := by
      simpa only [Real.norm_eq_abs] using t.integrable_pow_mul volume k
    convert (((hi s).add ((hi s1).const_mul 2)).add (hi s2)).const_mul C using 1
    funext u
    dsimp [B]
    ring
  · calc
      _ = ‖p v u‖ * ‖s u‖ := norm_mul _ _
      _ ≤ C * ‖s u‖ := mul_le_mul_of_nonneg_right (hB v u).1 (norm_nonneg _)
      _ ≤ B u := by
        dsimp [B]
        apply mul_le_mul_of_nonneg_left _ hC
        linarith [norm_nonneg (s1 u), norm_nonneg (s2 u)]
  · rw [(hd v u).deriv]
    calc
      _ ≤ ‖deriv (p v) u‖ * ‖s u‖ + ‖p v u‖ * ‖s1 u‖ := by
        simpa only [norm_mul] using norm_add_le
          (deriv (p v) u * s u) (p v u * s1 u)
      _ ≤ C * ‖s u‖ + C * ‖s1 u‖ := add_le_add
        (mul_le_mul_of_nonneg_right (hB v u).2.1 (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hB v u).1 (norm_nonneg _))
      _ ≤ B u := by
        dsimp [B]
        rw [← mul_add]
        apply mul_le_mul_of_nonneg_left _ hC
        linarith [norm_nonneg (s1 u), norm_nonneg (s2 u)]
  · rw [(hdd v u).deriv]
    calc
      _ ≤ (‖deriv (deriv (p v)) u‖ * ‖s u‖ + ‖deriv (p v) u‖ * ‖s1 u‖) +
          (‖deriv (p v) u‖ * ‖s1 u‖ + ‖p v u‖ * ‖s2 u‖) := by
        exact (norm_add_le _ _).trans (add_le_add
          (by simpa only [norm_mul] using (norm_add_le
            (deriv (deriv (p v)) u * s u) (deriv (p v) u * s1 u)))
          (by simpa only [norm_mul] using (norm_add_le
            (deriv (p v) u * s1 u) (p v u * s2 u))))
      _ ≤ (C * ‖s u‖ + C * ‖s1 u‖) + (C * ‖s1 u‖ + C * ‖s2 u‖) := by
        apply add_le_add <;> apply add_le_add
        · exact mul_le_mul_of_nonneg_right (hB v u).2.2 (norm_nonneg _)
        · exact mul_le_mul_of_nonneg_right (hB v u).2.1 (norm_nonneg _)
        · exact mul_le_mul_of_nonneg_right (hB v u).2.1 (norm_nonneg _)
        · exact mul_le_mul_of_nonneg_right (hB v u).1 (norm_nonneg _)
      _ = B u := by dsimp [B]; ring

private lemma bounded_sin_mul (F : ℝ → ℂ) (hF : Integrable F) (a : ℝ) :
    Integrable (fun u => (Real.sin (a * u) : ℂ) * F u) := by
  refine hF.bdd_mul (c := 1) (by fun_prop) (Filter.Eventually.of_forall fun u => ?_)
  simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_sin_le_one (a * u)

private lemma bounded_cos_mul (F : ℝ → ℂ) (hF : Integrable F) (a : ℝ) :
    Integrable (fun u => (Real.cos (a * u) : ℂ) * F u) := by
  refine hF.bdd_mul (c := 1) (by fun_prop) (Filter.Eventually.of_forall fun u => ?_)
  simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one (a * u)

private lemma wholeLine_twiceIBP (F : ℝ → ℂ)
    (hd : Differentiable ℝ F) (hdd : Differentiable ℝ (deriv F))
    (hi : Integrable F) (hi1 : Integrable (deriv F)) (hi2 : Integrable (deriv (deriv F)))
    (a : ℝ) (ha : a ≠ 0) :
    Integrable (fun u : ℝ => (Real.sin (a * u) : ℂ) * F u) ∧
    Integrable (fun u : ℝ => (Real.sin (a * u) : ℂ) * deriv (deriv F) u) ∧
    (∫ u : ℝ, (Real.sin (a * u) : ℂ) * F u) =
      -(((a ^ 2 : ℝ) : ℂ)⁻¹) *
        ∫ u : ℝ, (Real.sin (a * u) : ℂ) * deriv (deriv F) u := by
  have hs (u : ℝ) : HasDerivAt (fun t : ℝ => (Real.sin (a * t) : ℂ))
      ((a : ℂ) * (Real.cos (a * u) : ℂ)) u := by
    simpa only [id_eq, mul_one, Complex.ofReal_mul, mul_comm] using
      (((hasDerivAt_id u).const_mul a).sin).ofReal_comp
  have hc (u : ℝ) : HasDerivAt (fun t : ℝ => (Real.cos (a * t) : ℂ))
      (-(a : ℂ) * (Real.sin (a * u) : ℂ)) u := by
    simpa only [id_eq, mul_one, Complex.ofReal_mul, Complex.ofReal_neg, neg_mul, mul_neg, mul_comm] using
      (((hasDerivAt_id u).const_mul a).cos).ofReal_comp
  have hci : Integrable (fun u : ℝ =>
      ((a : ℂ) * (Real.cos (a * u) : ℂ)) * deriv F u) := by
    simpa only [mul_assoc] using (bounded_cos_mul _ hi1 a).const_mul (a : ℂ)
  have hsi : Integrable (fun u : ℝ =>
      (-(a : ℂ) * (Real.sin (a * u) : ℂ)) * F u) := by
    simpa only [mul_assoc] using (bounded_sin_mul _ hi a).const_mul (-(a : ℂ))
  have ibp1 := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun u _ => hs u) (fun u _ => (hdd u).hasDerivAt)
    (bounded_sin_mul _ hi2 a)
    hci
    (bounded_sin_mul _ hi1 a)
  have ibp2 := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun u _ => hc u) (fun u _ => (hd u).hasDerivAt)
    (bounded_cos_mul _ hi1 a)
    hsi
    (bounded_cos_mul _ hi a)
  change (∫ u, (Real.sin (a * u) : ℂ) * deriv (deriv F) u) =
    -(∫ u, ((a : ℂ) * (Real.cos (a * u) : ℂ)) * deriv F u) at ibp1
  change (∫ u, (Real.cos (a * u) : ℂ) * deriv F u) =
    -(∫ u, (-(a : ℂ) * (Real.sin (a * u) : ℂ)) * F u) at ibp2
  simp_rw [mul_assoc] at ibp1 ibp2
  rw [integral_const_mul, ibp2, integral_const_mul] at ibp1
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  refine ⟨bounded_sin_mul _ hi a, bounded_sin_mul _ hi2 a, ?_⟩
  rw [Complex.ofReal_pow, ibp1]
  field_simp [haC]

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
    exact abs_eq_zero.mp (eq_zero_of_pow_eq_zero ha)
  have hv := variance_congr hid
  have hv0 : variance (fun _ : ℝ => (0 : ℝ)) ν = 0 := by
    rw [variance_eq_sub (memLp_const (0 : ℝ))]
    simp
  linarith

private lemma quadraticChar_boundedC2 (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    boundedC2 (fun v u => quadraticChar ν u v) := by
  have h1 : Integrable (fun a : ℝ => |a|) ν :=
    (integrable_const (μ := ν) h).mono' (by fun_prop)
      (hs.mono fun a ha => by simpa only [Real.norm_eq_abs, abs_abs] using ha)
  have h2 : Integrable (fun a : ℝ => a ^ 2) ν := by
    refine (integrable_const (μ := ν) (h ^ 2)).mono' (by fun_prop) ?_
    filter_upwards [hs] with a ha
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a), sq_abs] using
      pow_le_pow_left₀ (abs_nonneg a) ha 2
  exact characteristic_boundedC2 ν id (fun a : ℝ => a ^ 2) measurable_id (by fun_prop) h1 h2

private lemma chord_boundedC2 (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    boundedC2 (fun v u => quadraticChordChar ν u v) := by
  have : IsProbabilityMeasure (quadraticChordLaw ν) :=
    (quadraticChord_law_data ν h3 hV h hh hs).2.1
  have hm := quadraticChord_moments ν h3 hV h hh hs
  exact characteristic_boundedC2 (quadraticChordLaw ν) Prod.fst Prod.snd
    measurable_fst measurable_snd hm.2.1 hm.2.2.1

private lemma signed_prefix_boundedC2 (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (σ : ℂ) :
    boundedC2 (fun v u =>
      (((quadraticChar ν u v) ^ m + σ * (quadraticChar ν (-u) v) ^ m) / 2) *
        ((quadraticChordChar ν u v) ^ 8 * (quadraticChordChar ν (-u) v) ^ 8)) := by
  have hp := boundedC2_pow _ (quadraticChar_boundedC2 ν h hs) m
  have hn := boundedC2_reflect _ hp
  have hsum := boundedC2_add _ _ hp (boundedC2_const_mul σ _ hn)
  have hhalf := boundedC2_const_mul (1 / 2) _ hsum
  have hk := chord_boundedC2 ν h3 hV h hh hs
  have hprod := boundedC2_mul _ _ (boundedC2_pow _ hk 8)
    (boundedC2_pow _ (boundedC2_reflect _ hk) 8)
  convert boundedC2_mul _ _ hhalf hprod using 1
  funext v u
  ring

theorem quadraticFullNoise_odd_wholeLine_twiceIBP
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (v : ℝ) :
    let D : ℝ → ℂ := fun u =>
      ((quadraticChar ν u v) ^ m - (quadraticChar ν (-u) v) ^ m) / 2 *
        quadraticFullNoiseChar ν u v
    Differentiable ℝ D ∧ Differentiable ℝ (fun u : ℝ => deriv D u) ∧
      Integrable D ∧ Integrable (fun u : ℝ => deriv D u) ∧
      Integrable (fun u : ℝ => deriv (fun t : ℝ => deriv D t) u) ∧
      ∀ a : ℝ, a ≠ 0 →
        Integrable (fun u : ℝ => (Real.sin (a * u) : ℂ) * D u) ∧
        Integrable (fun u : ℝ => (Real.sin (a * u) : ℂ) *
          deriv (fun t : ℝ => deriv D t) u) ∧
        (∫ u : ℝ, (Real.sin (a * u) : ℂ) * D u) =
          -(((a ^ 2 : ℝ) : ℂ)⁻¹) *
            ∫ u : ℝ, (Real.sin (a * u) : ℂ) * deriv (fun t : ℝ => deriv D t) u := by
  let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν
  have hg : 0 < gamma := div_pos (third_moment_pos ν h3 hV) hV
  obtain ⟨s, hsS⟩ := scaledScalar_schwartz gamma hg.ne'
  let p : ℝ → ℝ → ℂ := fun v u =>
    (((quadraticChar ν u v) ^ m + (-1 : ℂ) * (quadraticChar ν (-u) v) ^ m) / 2) *
      ((quadraticChordChar ν u v) ^ 8 * (quadraticChordChar ν (-u) v) ^ 8)
  have hdata := schwartz_product_data p (signed_prefix_boundedC2 ν h3 hV h hh hs m (-1)) s v
  have he : (fun u => p v u * s u) = fun u =>
      ((quadraticChar ν u v) ^ m - (quadraticChar ν (-u) v) ^ m) / 2 *
        quadraticFullNoiseChar ν u v := by
    funext u
    rw [← congrFun hsS u, (quadraticFullNoiseChar_product ν h3 hV h hh hs u v).1]
    dsimp [p, gamma]
    ring
  rw [he] at hdata
  obtain ⟨hd, hdd, hi, hi1, hi2⟩ := hdata
  exact ⟨hd, hdd, hi, hi1, hi2, fun a ha => wholeLine_twiceIBP _ hd hdd hi hi1 hi2 a ha⟩

theorem quadraticFullNoise_odd_even_derivative_envelope
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) :
    let D : ℝ → ℝ → ℂ := fun v u =>
      ((quadraticChar ν u v) ^ m - (quadraticChar ν (-u) v) ^ m) / 2 *
        quadraticFullNoiseChar ν u v
    let E : ℝ → ℝ → ℂ := fun v u =>
      ((quadraticChar ν u v) ^ m + (quadraticChar ν (-u) v) ^ m) / 2 *
        quadraticFullNoiseChar ν u v
    let W : ℝ → ℝ → ℂ := fun v u => (u : ℂ) * E v u
    ∃ B : ℝ → ℝ, (∀ u : ℝ, 0 ≤ B u) ∧
      (∀ k : ℕ, Integrable (fun u : ℝ => |u| ^ k * B u)) ∧
      ∀ u v : ℝ,
        ‖D v u‖ ≤ B u ∧
        ‖deriv (D v) u‖ ≤ B u ∧
        ‖deriv (fun t : ℝ => deriv (D v) t) u‖ ≤ B u ∧
        ‖W v u‖ ≤ B u ∧
        ‖deriv (W v) u‖ ≤ B u ∧
        ‖deriv (fun t : ℝ => deriv (W v) t) u‖ ≤ B u := by
  let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν
  have hg : 0 < gamma := div_pos (third_moment_pos ν h3 hV) hV
  obtain ⟨s, hsS⟩ := scaledScalar_schwartz gamma hg.ne'
  let sU : SchwartzMap ℝ ℂ := SchwartzMap.smulLeftCLM ℂ (fun u : ℝ => (u : ℂ)) s
  have hsU (u : ℝ) : sU u = (u : ℂ) * s u :=
    SchwartzMap.smulLeftCLM_apply_apply Complex.hasTemperateGrowth_ofReal s u
  let p (σ : ℂ) : ℝ → ℝ → ℂ := fun v u =>
    (((quadraticChar ν u v) ^ m + σ * (quadraticChar ν (-u) v) ^ m) / 2) *
      ((quadraticChordChar ν u v) ^ 8 * (quadraticChordChar ν (-u) v) ^ 8)
  have ho := schwartz_product_envelope (p (-1))
    (signed_prefix_boundedC2 ν h3 hV h hh hs m (-1)) s
  have he := schwartz_product_envelope (p 1)
    (signed_prefix_boundedC2 ν h3 hV h hh hs m 1) sU
  have hfo : (fun v u => p (-1) v u * s u) = fun v u =>
      ((quadraticChar ν u v) ^ m - (quadraticChar ν (-u) v) ^ m) / 2 *
        quadraticFullNoiseChar ν u v := by
    funext v u
    rw [← congrFun hsS u, (quadraticFullNoiseChar_product ν h3 hV h hh hs u v).1]
    dsimp [p, gamma]
    ring
  have hfe : (fun v u => p 1 v u * sU u) = fun (v : ℝ) (u : ℝ) =>
      (u : ℂ) * (((quadraticChar ν u v) ^ m + (quadraticChar ν (-u) v) ^ m) / 2 *
        quadraticFullNoiseChar ν u v) := by
    funext v u
    rw [hsU, ← congrFun hsS u, (quadraticFullNoiseChar_product ν h3 hV h hh hs u v).1]
    dsimp [p, gamma]
    ring
  rw [hfo] at ho
  rw [hfe] at he
  obtain ⟨Bo, hBo, hBoI, hBoB⟩ := ho
  obtain ⟨Be, hBe, hBeI, hBeB⟩ := he
  refine ⟨fun u => Bo u + Be u, fun u => add_nonneg (hBo u) (hBe u), ?_, ?_⟩
  · intro k
    convert (hBoI k).add (hBeI k) using 1
    funext u
    dsimp
    ring
  · intro u v
    have hoB := hBoB u v
    have heB := hBeB u v
    exact ⟨hoB.1.trans (le_add_of_nonneg_right (hBe u)),
      hoB.2.1.trans (le_add_of_nonneg_right (hBe u)),
      hoB.2.2.trans (le_add_of_nonneg_right (hBe u)),
      heB.1.trans (le_add_of_nonneg_left (hBo u)),
      heB.2.1.trans (le_add_of_nonneg_left (hBo u)),
      heB.2.2.trans (le_add_of_nonneg_left (hBo u))⟩

theorem quadraticFullNoise_even_wholeLine_twiceIBP
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (v : ℝ) :
    let E : ℝ → ℂ := fun u =>
      ((quadraticChar ν u v) ^ m + (quadraticChar ν (-u) v) ^ m) / 2 *
        quadraticFullNoiseChar ν u v
    let W : ℝ → ℂ := fun u => (u : ℂ) * E u
    Differentiable ℝ W ∧ Differentiable ℝ (fun u : ℝ => deriv W u) ∧
      Integrable W ∧ Integrable (fun u : ℝ => deriv W u) ∧
      Integrable (fun u : ℝ => deriv (fun t : ℝ => deriv W t) u) ∧
      ∀ a : ℝ, a ≠ 0 →
        Integrable (fun u : ℝ => (Real.sin (a * u) : ℂ) * W u) ∧
        Integrable (fun u : ℝ => (Real.sin (a * u) : ℂ) *
          deriv (fun t : ℝ => deriv W t) u) ∧
        (∫ u : ℝ, (Real.sin (a * u) : ℂ) * W u) =
          -(((a ^ 2 : ℝ) : ℂ)⁻¹) *
            ∫ u : ℝ, (Real.sin (a * u) : ℂ) * deriv (fun t : ℝ => deriv W t) u := by
  let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν
  have hg : 0 < gamma := div_pos (third_moment_pos ν h3 hV) hV
  obtain ⟨s, hsS⟩ := scaledScalar_schwartz gamma hg.ne'
  let sU : SchwartzMap ℝ ℂ := SchwartzMap.smulLeftCLM ℂ (fun u : ℝ => (u : ℂ)) s
  have hsU (u : ℝ) : sU u = (u : ℂ) * s u :=
    SchwartzMap.smulLeftCLM_apply_apply Complex.hasTemperateGrowth_ofReal s u
  let p : ℝ → ℝ → ℂ := fun v u =>
    (((quadraticChar ν u v) ^ m + (1 : ℂ) * (quadraticChar ν (-u) v) ^ m) / 2) *
      ((quadraticChordChar ν u v) ^ 8 * (quadraticChordChar ν (-u) v) ^ 8)
  have hdata := schwartz_product_data p (signed_prefix_boundedC2 ν h3 hV h hh hs m 1) sU v
  have he : (fun u => p v u * sU u) = fun u : ℝ =>
      (u : ℂ) * (((quadraticChar ν u v) ^ m + (quadraticChar ν (-u) v) ^ m) / 2 *
        quadraticFullNoiseChar ν u v) := by
    funext u
    rw [hsU, ← congrFun hsS u, (quadraticFullNoiseChar_product ν h3 hV h hh hs u v).1]
    dsimp [p, gamma]
    ring
  rw [he] at hdata
  obtain ⟨hd, hdd, hi, hi1, hi2⟩ := hdata
  exact ⟨hd, hdd, hi, hi1, hi2, fun a ha => wholeLine_twiceIBP _ hd hdd hi hi1 hi2 a ha⟩

end Shao.Probability
