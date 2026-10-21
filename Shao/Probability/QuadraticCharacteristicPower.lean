import Shao.Probability.QuadraticCharacteristic
import Shao.Probability.FiniteIIDMoments
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance

/-!
Actual finite-power derivatives on the real frequency plane. The fixed
increment law may have nonzero mean. No damping estimate is asserted here.
-/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private lemma phase_norm (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 := by
  simp [Complex.norm_exp, Complex.mul_re]

private lemma law_memLp_two {ν : Measure ℝ}
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) : MemLp (id : ℝ → ℝ) 2 ν :=
  (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr h2

private lemma law_variance_eq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) :
    variance (id : ℝ → ℝ) ν = (∫ a : ℝ, a ^ 2 ∂ν) - (∫ a : ℝ, a ∂ν) ^ 2 := by
  simpa only [Pi.pow_apply, id_eq] using variance_eq_sub (law_memLp_two h2)

private lemma sum_memLp_two
    {ℓ : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ} {X : Fin ℓ → Ω → ℝ}
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) :
    MemLp (fun ω => Shao.prefixSum (samplePath X ω) ℓ) 2 μ := by
  have hcoord (i : Fin ℓ) : MemLp (X i) 2 μ :=
    (hLaw i).memLp_iff.mpr (law_memLp_two h2)
  simpa [Shao.prefixSum, samplePath] using
    memLp_finsetSum Finset.univ (fun i _ => hcoord i)

private lemma exp_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S Q : Ω → ℝ} (hS : Measurable S) (hQ : Measurable Q) (u v : ℝ) :
    Integrable (fun ω => Complex.exp (((u * S ω + v * Q ω : ℝ) : ℂ) * Complex.I)) μ := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun ω => (phase_norm _).le)

private lemma weighted_exp_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S Q g : Ω → ℝ} (hS : Measurable S) (hQ : Measurable Q)
    (hg : Integrable g μ) (u v : ℝ) :
    Integrable (fun ω => (g ω : ℂ) *
      Complex.exp (((u * S ω + v * Q ω : ℝ) : ℂ) * Complex.I)) μ := by
  refine hg.norm.mono' ((hg.ofReal (𝕜 := ℂ)).aestronglyMeasurable.mul
    (by fun_prop)) (Filter.Eventually.of_forall fun ω => ?_)
  simp only [norm_mul, phase_norm, mul_one, Complex.norm_real]
  exact le_rfl

private lemma exp_hasDerivAt (S Q r v : ℝ) :
    HasDerivAt
      (fun s : ℝ => Complex.exp (((s * S + v * Q : ℝ) : ℂ) * Complex.I))
      (Complex.I * (S : ℂ) * Complex.exp (((r * S + v * Q : ℝ) : ℂ) * Complex.I)) r := by
  convert (((((hasDerivAt_id r).mul_const S).add_const (v * Q)).ofReal_comp).mul_const
    Complex.I).cexp using 1
  all_goals try funext x
  all_goals try dsimp
  all_goals push_cast
  all_goals ring

private lemma exp_integral_hasDerivAt
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S Q : Ω → ℝ} (hS : Measurable S) (hQ : Measurable Q)
    (hS2 : MemLp S 2 μ) (u v : ℝ) :
    HasDerivAt
      (fun r : ℝ => ∫ ω, Complex.exp (((r * S ω + v * Q ω : ℝ) : ℂ) * Complex.I) ∂μ)
      (Complex.I * ∫ ω, (S ω : ℂ) *
        Complex.exp (((u * S ω + v * Q ω : ℝ) : ℂ) * Complex.I) ∂μ) u := by
  have h1 : Integrable S μ := hS2.integrable (by norm_num)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ)
    (F' := fun r ω => Complex.I * ((S ω : ℂ) *
      Complex.exp (((r * S ω + v * Q ω : ℝ) : ℂ) * Complex.I)))
    (bound := fun ω => |S ω|) (by simp)
    (Filter.Eventually.of_forall fun r => (exp_integrable hS hQ r v).aestronglyMeasurable)
    (exp_integrable hS hQ u v)
    ((weighted_exp_integrable hS hQ h1 u v).const_mul Complex.I).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω r _ => by
      simp only [norm_mul, Complex.norm_I, one_mul, phase_norm, mul_one,
        Complex.norm_real, Real.norm_eq_abs]
      exact le_rfl) h1.abs
    (Filter.Eventually.of_forall fun ω r _ => by
      simpa only [mul_assoc] using exp_hasDerivAt (S ω) (Q ω) r v)).2
  simpa only [mul_assoc, integral_const_mul] using hd

private lemma weighted_exp_integral_hasDerivAt
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S Q : Ω → ℝ} (hS : Measurable S) (hQ : Measurable Q)
    (hS2 : MemLp S 2 μ) (u v : ℝ) :
    HasDerivAt
      (fun r : ℝ => ∫ ω, (S ω : ℂ) *
        Complex.exp (((r * S ω + v * Q ω : ℝ) : ℂ) * Complex.I) ∂μ)
      (Complex.I * ∫ ω, ((S ω ^ 2 : ℝ) : ℂ) *
        Complex.exp (((u * S ω + v * Q ω : ℝ) : ℂ) * Complex.I) ∂μ) u := by
  have h1 : Integrable S μ := hS2.integrable (by norm_num)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ)
    (F' := fun r ω => Complex.I * (((S ω ^ 2 : ℝ) : ℂ) *
      Complex.exp (((r * S ω + v * Q ω : ℝ) : ℂ) * Complex.I)))
    (bound := fun ω => S ω ^ 2) (by simp)
    (Filter.Eventually.of_forall fun r => (weighted_exp_integrable hS hQ h1 r v).aestronglyMeasurable)
    (weighted_exp_integrable hS hQ h1 u v)
    ((weighted_exp_integrable hS hQ hS2.integrable_sq u v).const_mul Complex.I).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω r _ => by
      simp only [norm_mul, Complex.norm_I, one_mul, phase_norm, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (S ω))]
      exact le_rfl)
    hS2.integrable_sq
    (Filter.Eventually.of_forall fun ω r _ => by
      convert (exp_hasDerivAt (S ω) (Q ω) r v).const_mul (S ω : ℂ) using 1
      push_cast
      ring)).2
  simpa only [mul_assoc, integral_const_mul] using hd

theorem iid_quadraticChar_power_hasDerivAt
    {ℓ : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin ℓ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (u v : ℝ) :
    HasDerivAt (fun r : ℝ => (quadraticChar ν r v) ^ ℓ)
      (Complex.I * ∫ ω,
        (Shao.prefixSum (samplePath X ω) ℓ : ℂ) *
          Complex.exp
            (((u * Shao.prefixSum (samplePath X ω) ℓ +
                v * Shao.energy (samplePath X ω) : ℝ) : ℂ) * Complex.I) ∂μ) u := by
  exact (exp_integral_hasDerivAt (by unfold Shao.prefixSum samplePath; fun_prop)
    (by unfold Shao.energy samplePath; fun_prop) (sum_memLp_two hLaw h2) u v).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r => (iid_quadraticChar_factor hX hIndep hLaw r v).symm)

theorem iid_quadraticChar_power_deriv_hasDerivAt
    {ℓ : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin ℓ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (u v : ℝ) :
    HasDerivAt
      (fun r : ℝ => deriv (fun s : ℝ => (quadraticChar ν s v) ^ ℓ) r)
      (-(∫ ω,
        ((Shao.prefixSum (samplePath X ω) ℓ ^ 2 : ℝ) : ℂ) *
          Complex.exp
            (((u * Shao.prefixSum (samplePath X ω) ℓ +
                v * Shao.energy (samplePath X ω) : ℝ) : ℂ) * Complex.I) ∂μ)) u := by
  have hd := (weighted_exp_integral_hasDerivAt
    (S := fun ω => Shao.prefixSum (samplePath X ω) ℓ)
    (Q := fun ω => Shao.energy (samplePath X ω))
    (by unfold Shao.prefixSum samplePath; fun_prop)
    (by unfold Shao.energy samplePath; fun_prop) (sum_memLp_two hLaw h2) u v).const_mul Complex.I
  simp only [← mul_assoc, Complex.I_mul_I, neg_one_mul] at hd
  exact hd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => (iid_quadraticChar_power_hasDerivAt hX hIndep hLaw h2 r v).deriv)

private lemma canonical_law (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (ℓ : ℕ) (i : Fin ℓ) :
    IdentDistrib (fun a : Shao.Path ℓ => a i) (id : ℝ → ℝ)
      (Measure.pi (fun _ : Fin ℓ => ν)) ν := by
  refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
  simpa only [Measure.map_id] using (measurePreserving_eval (fun _ : Fin ℓ => ν) i).map_eq

private lemma canonical_indep (ν : Measure ℝ) [IsProbabilityMeasure ν] (ℓ : ℕ) :
    iIndepFun (fun (i : Fin ℓ) (a : Shao.Path ℓ) => a i)
      (Measure.pi (fun _ : Fin ℓ => ν)) :=
  iIndepFun_pi (fun _ => measurable_id.aemeasurable)

private lemma canonical_sum_memLp (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (ℓ : ℕ) :
    MemLp (fun a : Shao.Path ℓ => Shao.prefixSum a ℓ) 2
      (Measure.pi (fun _ : Fin ℓ => ν)) := by
  exact sum_memLp_two (canonical_law ν ℓ) h2

private lemma canonical_sum_mean (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (ℓ : ℕ) :
    (∫ a : Shao.Path ℓ, Shao.prefixSum a ℓ ∂Measure.pi (fun _ : Fin ℓ => ν)) =
      (ℓ : ℝ) * ∫ a : ℝ, a ∂ν := by
  have hi (i : Fin ℓ) : Integrable (fun a : Shao.Path ℓ => a i)
      (Measure.pi (fun _ : Fin ℓ => ν)) :=
    ((canonical_law ν ℓ i).memLp_iff.mpr (law_memLp_two h2)).integrable (by norm_num)
  have hs (a : Shao.Path ℓ) : Shao.prefixSum a ℓ = ∑ i, a i := by simp [Shao.prefixSum]
  simp_rw [hs]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [(canonical_law ν ℓ _).integral_eq, id_eq, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private lemma abs_integral_le_sqrt_second
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ) :
    (∫ ω, |Y ω| ∂μ) ≤ Real.sqrt (∫ ω, Y ω ^ 2 ∂μ) := by
  have hYa : MemLp (fun ω => |Y ω|) 2 μ := by simpa only [Real.norm_eq_abs] using hY.norm
  have hv := variance_nonneg (fun ω => |Y ω|) μ
  rw [variance_eq_sub hYa] at hv
  simp only [Pi.pow_apply, sq_abs] at hv
  have hs := Real.sq_sqrt (integral_nonneg (fun ω => sq_nonneg (Y ω)) (μ := μ))
  have ha : 0 ≤ (∫ ω, |Y ω| ∂μ) := integral_nonneg (fun ω => abs_nonneg (Y ω))
  nlinarith [Real.sqrt_nonneg (∫ ω, Y ω ^ 2 ∂μ)]

private lemma canonical_derivative_integral_bounds (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (h2 : Integrable (fun a : ℝ => a ^ 2) ν)
    (ℓ : ℕ) (u v : ℝ) :
    let P : Measure (Shao.Path ℓ) := Measure.pi (fun _ : Fin ℓ => ν)
    let f : ℝ → ℂ := fun r => (quadraticChar ν r v) ^ ℓ
    ‖deriv f u‖ ≤ (∫ a : Shao.Path ℓ, |Shao.prefixSum a ℓ| ∂P) ∧
      ‖deriv (fun r : ℝ => deriv f r) u‖ ≤
        (∫ a : Shao.Path ℓ, Shao.prefixSum a ℓ ^ 2 ∂P) := by
  dsimp only
  have hS2 := canonical_sum_memLp ν h2 ℓ
  have hd := (iid_quadraticChar_power_hasDerivAt
    (X := fun (i : Fin ℓ) (a : Shao.Path ℓ) => a i) (fun i => measurable_pi_apply i)
    (canonical_indep ν ℓ) (canonical_law ν ℓ) h2 u v).deriv
  have hdd := (iid_quadraticChar_power_deriv_hasDerivAt
    (X := fun (i : Fin ℓ) (a : Shao.Path ℓ) => a i) (fun i => measurable_pi_apply i)
    (canonical_indep ν ℓ) (canonical_law ν ℓ) h2 u v).deriv
  constructor
  · rw [hd, norm_mul, Complex.norm_I, one_mul]
    exact norm_integral_le_of_norm_le (hS2.integrable (by norm_num)).abs
      (Filter.Eventually.of_forall fun a => by
        simp only [norm_mul, phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
        exact le_rfl)
  · rw [hdd, norm_neg]
    exact norm_integral_le_of_norm_le hS2.integrable_sq
      (Filter.Eventually.of_forall fun a : Shao.Path ℓ => by
        simp only [norm_mul, phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
        change |Shao.prefixSum a ℓ ^ 2| ≤ Shao.prefixSum a ℓ ^ 2
        rw [abs_of_nonneg (sq_nonneg (Shao.prefixSum a ℓ))])

private lemma scale_payment (n ℓ : ℕ) (hℓ : ℓ ≤ n) (m2 μ θ B : ℝ)
    (hθ : 0 < θ) (hscale : θ ≤ (n : ℝ) * m2)
    (hbias : (n : ℝ) * |μ| ≤ B) :
    (ℓ : ℝ) * (m2 - μ ^ 2) + (ℓ : ℝ) ^ 2 * μ ^ 2 ≤
      (1 + B ^ 2 / θ) * ((ℓ : ℝ) * m2) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hl : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have hln : (ℓ : ℝ) ≤ n := Nat.cast_le.mpr hℓ
  have hm : 0 ≤ m2 := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos hn (le_of_lt (lt_of_not_ge h))
    linarith
  have hnm : 0 ≤ (n : ℝ) * |μ| := mul_nonneg hn (abs_nonneg μ)
  have hB : 0 ≤ B := hnm.trans hbias
  have hsq : ((n : ℝ) * |μ|) ^ 2 ≤ B ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbias) (add_nonneg hB hnm)]
  have hc : (n : ℝ) * μ ^ 2 ≤ B ^ 2 / θ * m2 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hθ).mpr
    calc
      (n : ℝ) * μ ^ 2 * θ ≤ ((n : ℝ) * m2) * ((n : ℝ) * μ ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_right hscale (mul_nonneg hn (sq_nonneg μ))]
      _ = m2 * ((n : ℝ) * |μ|) ^ 2 := by rw [mul_pow, sq_abs]; ring
      _ ≤ m2 * B ^ 2 := mul_le_mul_of_nonneg_left hsq hm
      _ = B ^ 2 * m2 := mul_comm _ _
  have hp : (ℓ : ℝ) ^ 2 * μ ^ 2 ≤ (B ^ 2 / θ) * ((ℓ : ℝ) * m2) := by
    calc
      _ ≤ (ℓ : ℝ) * ((n : ℝ) * μ ^ 2) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hln) (mul_nonneg hl (sq_nonneg μ))]
      _ ≤ (ℓ : ℝ) * (B ^ 2 / θ * m2) := mul_le_mul_of_nonneg_left hc hl
      _ = _ := by ring
  nlinarith [mul_nonneg hl (sq_nonneg μ)]

private lemma abs_integral_center_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ) (c : ℝ) :
    (∫ ω, |Y ω| ∂μ) ≤ Real.sqrt (∫ ω, (Y ω - c) ^ 2 ∂μ) + |c| := by
  have h1 : Integrable Y μ := hY.integrable (by norm_num)
  have hC : MemLp (fun ω => Y ω - c) 2 μ := hY.sub (memLp_const c)
  have hi : (∫ ω, |Y ω| ∂μ) ≤ ∫ ω, |Y ω - c| + |c| ∂μ := by
    refine integral_mono h1.abs (((h1.sub (integrable_const c)).abs).add (integrable_const |c|))
      (fun ω => ?_)
    simpa only [sub_add_cancel] using abs_add_le (Y ω - c) c
  have hs : Integrable (fun ω => |Y ω - c|) μ := (hC.integrable (by norm_num)).abs
  have he : (∫ ω, |Y ω - c| + |c| ∂μ) = (∫ ω, |Y ω - c| ∂μ) + |c| := by
    rw [integral_add hs (integrable_const |c|)]
    simp
  rw [he] at hi
  have habs := abs_integral_le_sqrt_second hC
  linarith

private lemma power_hasDerivAt (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (ℓ : ℕ) (u v : ℝ) :
    HasDerivAt (fun r : ℝ => quadraticChar ν r v ^ ℓ)
      (deriv (fun r : ℝ => quadraticChar ν r v ^ ℓ) u) u :=
  (iid_quadraticChar_power_hasDerivAt
    (X := fun (i : Fin ℓ) (a : Shao.Path ℓ) => a i) (fun i => measurable_pi_apply i)
    (canonical_indep ν ℓ) (canonical_law ν ℓ) h2 u v).differentiableAt.hasDerivAt

private lemma power_deriv_hasDerivAt (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (ℓ : ℕ) (u v : ℝ) :
    HasDerivAt (fun r : ℝ => deriv (fun s : ℝ => quadraticChar ν s v ^ ℓ) r)
      (deriv (fun r : ℝ => deriv (fun s : ℝ => quadraticChar ν s v ^ ℓ) r) u) u :=
  (iid_quadraticChar_power_deriv_hasDerivAt
    (X := fun (i : Fin ℓ) (a : Shao.Path ℓ) => a i) (fun i => measurable_pi_apply i)
    (canonical_indep ν ℓ) (canonical_law ν ℓ) h2 u v).differentiableAt.hasDerivAt

private lemma signed_power_deriv (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (ℓ : ℕ) (σ u v : ℝ) :
    deriv (fun r : ℝ => quadraticChar ν (σ * r) v ^ ℓ) u =
      σ • deriv (fun r : ℝ => quadraticChar ν r v ^ ℓ) (σ * u) := by
  exact ((power_hasDerivAt ν h2 ℓ (σ * u) v).scomp u
    (by simpa using (hasDerivAt_id u).const_mul σ)).deriv

private lemma signed_power_second_deriv (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (ℓ : ℕ) (σ u v : ℝ) :
    deriv (fun r : ℝ => deriv (fun s : ℝ => quadraticChar ν (σ * s) v ^ ℓ) r) u =
      σ • (σ • deriv (fun r : ℝ => deriv (fun s : ℝ => quadraticChar ν s v ^ ℓ) r) (σ * u)) := by
  have hd := ((power_deriv_hasDerivAt ν h2 ℓ (σ * u) v).scomp u
    (by simpa using (hasDerivAt_id u).const_mul σ)).const_smul σ
  exact (hd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => signed_power_deriv ν h2 ℓ σ r v)).deriv

private lemma canonical_sum_second (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (ℓ : ℕ) :
    (∫ a : Shao.Path ℓ, Shao.prefixSum a ℓ ^ 2 ∂Measure.pi (fun _ : Fin ℓ => ν)) =
      (ℓ : ℝ) * ((∫ a : ℝ, a ^ 2 ∂ν) - (∫ a : ℝ, a ∂ν) ^ 2) +
        (ℓ : ℝ) ^ 2 * (∫ a : ℝ, a ∂ν) ^ 2 := by
  have h := finite_iid_sumSquare_integral
    (Z := fun (i : Fin ℓ) (a : Shao.Path ℓ) => a i)
    (fun i => measurable_pi_apply i) (canonical_indep ν ℓ) (canonical_law ν ℓ)
    (law_memLp_two h2)
  have he : finiteFeatureSum (fun (i : Fin ℓ) (a : Shao.Path ℓ) => a i) =
      (fun a : Shao.Path ℓ => Shao.prefixSum a ℓ) := by
    funext a
    simp [finiteFeatureSum, Shao.prefixSum]
  rw [he] at h
  by_cases hℓ : ℓ = 0
  · simp [hℓ, Shao.prefixSum]
  · rw [Nat.cast_sub (by omega : 1 ≤ ℓ)] at h
    norm_num only [Nat.cast_one] at h
    nlinarith [h]

private lemma canonical_centered_second (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (ℓ : ℕ) :
    (∫ a : Shao.Path ℓ, (Shao.prefixSum a ℓ - (ℓ : ℝ) * ∫ z : ℝ, z ∂ν) ^ 2
      ∂Measure.pi (fun _ : Fin ℓ => ν)) =
      (ℓ : ℝ) * ((∫ z : ℝ, z ^ 2 ∂ν) - (∫ z : ℝ, z ∂ν) ^ 2) := by
  have hS2 := canonical_sum_memLp ν h2 ℓ
  have hvar : variance (fun a : Shao.Path ℓ => Shao.prefixSum a ℓ)
      (Measure.pi (fun _ : Fin ℓ => ν)) = (ℓ : ℝ) * variance (id : ℝ → ℝ) ν := by
    rw [variance_eq_sub hS2, law_variance_eq ν h2, canonical_sum_mean ν h2 ℓ]
    simp only [Pi.pow_apply]
    rw [canonical_sum_second ν h2 ℓ]
    ring
  rw [variance_eq_integral hS2.aemeasurable, canonical_sum_mean ν h2 ℓ,
    law_variance_eq ν h2] at hvar
  exact hvar

theorem quadraticChar_power_derivative_bounds (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν)
    (ℓ : ℕ) (u v : ℝ) :
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let V : ℝ := m2 - μ ^ 2
    let f : ℝ → ℂ := fun r => (quadraticChar ν r v) ^ ℓ
    ‖deriv f u‖ ≤ Real.sqrt ((ℓ : ℝ) * V) + (ℓ : ℝ) * |μ| ∧
      ‖deriv (fun r : ℝ => deriv f r) u‖ ≤
        (ℓ : ℝ) * V + (ℓ : ℝ) ^ 2 * μ ^ 2 := by
  dsimp only
  have hd := canonical_derivative_integral_bounds ν h2 ℓ u v
  constructor
  · calc
      _ ≤ ∫ a : Shao.Path ℓ, |Shao.prefixSum a ℓ| ∂Measure.pi (fun _ : Fin ℓ => ν) := hd.1
      _ ≤ Real.sqrt (∫ a : Shao.Path ℓ,
          (Shao.prefixSum a ℓ - (ℓ : ℝ) * ∫ z : ℝ, z ∂ν) ^ 2
          ∂Measure.pi (fun _ : Fin ℓ => ν)) + |(ℓ : ℝ) * ∫ z : ℝ, z ∂ν| :=
        abs_integral_center_bound (canonical_sum_memLp ν h2 ℓ) _
      _ = _ := by rw [canonical_centered_second ν h2 ℓ, abs_mul, abs_of_nonneg (Nat.cast_nonneg ℓ)]
  · exact hd.2.trans_eq (canonical_sum_second ν h2 ℓ)

theorem quadraticChar_power_derivative_scale_bounds (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν)
    (n ℓ : ℕ) (hℓ : ℓ ≤ n) (θ B : ℝ)
    (hθ : 0 < θ)
    (hscale : θ ≤ (n : ℝ) * ∫ a : ℝ, a ^ 2 ∂ν)
    (hbias : (n : ℝ) * |∫ a : ℝ, a ∂ν| ≤ B)
    (u v : ℝ) :
    let T : ℝ := (ℓ : ℝ) * ∫ a : ℝ, a ^ 2 ∂ν
    let f : ℝ → ℂ := fun r => (quadraticChar ν r v) ^ ℓ
    ‖deriv f u‖ ≤ Real.sqrt (1 + B ^ 2 / θ) * Real.sqrt T ∧
      ‖deriv (fun r : ℝ => deriv f r) u‖ ≤ (1 + B ^ 2 / θ) * T := by
  dsimp only
  have hd := canonical_derivative_integral_bounds ν h2 ℓ u v
  have ha := abs_integral_le_sqrt_second (canonical_sum_memLp ν h2 ℓ)
  rw [canonical_sum_second ν h2 ℓ] at ha
  have hp := scale_payment n ℓ hℓ (∫ a : ℝ, a ^ 2 ∂ν) (∫ a : ℝ, a ∂ν)
    θ B hθ hscale hbias
  have hc : 0 ≤ 1 + B ^ 2 / θ := by positivity
  constructor
  · calc
      _ ≤ _ := hd.1.trans ha
      _ ≤ Real.sqrt ((1 + B ^ 2 / θ) * ((ℓ : ℝ) * ∫ a : ℝ, a ^ 2 ∂ν)) := Real.sqrt_le_sqrt hp
      _ = _ := Real.sqrt_mul hc _
  · exact (hd.2.trans_eq (canonical_sum_second ν h2 ℓ)).trans hp

theorem quadraticChar_power_global_normalized (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν)
    (n ℓ : ℕ) (hℓ : ℓ ≤ n)
    (hscale : (3 / 4 : ℝ) ≤ (n : ℝ) * ∫ a : ℝ, a ^ 2 ∂ν)
    (hbias : (n : ℝ) * |∫ a : ℝ, a ∂ν| ≤ 1)
    (σ u v : ℝ) (hσ : |σ| = 1) :
    let T : ℝ := (ℓ : ℝ) * ∫ a : ℝ, a ^ 2 ∂ν
    let f : ℝ → ℂ := fun r => (quadraticChar ν (σ * r) v) ^ ℓ
    ‖f u‖ ≤ 1 ∧
      ‖deriv f u‖ ≤ 2 * Real.sqrt T ∧
      ‖deriv (fun r : ℝ => deriv f r) u‖ ≤ 3 * T := by
  dsimp only
  have hb := quadraticChar_power_derivative_scale_bounds ν h2 n ℓ hℓ (3 / 4) 1
    (by norm_num) hscale hbias (σ * u) v
  dsimp only at hb
  have heq : (1 + (1 : ℝ) ^ 2 / (3 / 4)) = (7 / 3 : ℝ) := by norm_num
  rw [heq] at hb
  have hT : 0 ≤ (ℓ : ℝ) * ∫ a : ℝ, a ^ 2 ∂ν :=
    mul_nonneg (Nat.cast_nonneg ℓ) (integral_nonneg fun a => sq_nonneg a)
  have hroot : Real.sqrt (7 / 3 : ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_quadraticChar_le_one ν (σ * u) v)
  · rw [signed_power_deriv ν h2 ℓ σ u v, norm_smul, Real.norm_eq_abs, hσ, one_mul]
    exact hb.1.trans (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _))
  · rw [signed_power_second_deriv ν h2 ℓ σ u v, norm_smul, norm_smul,
      Real.norm_eq_abs, hσ, one_mul, one_mul]
    nlinarith [hb.2]

end Shao.Probability
