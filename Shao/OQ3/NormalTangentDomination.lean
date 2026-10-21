import Shao.OQ3.NormalTangentMoments
import Shao.OQ3.FiniteFarArc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Uniform Gaussian domination on the actual central arc

Source: current/oq3/proofs/r1/report.md, lines 309-345, especially 339-343.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U12e scope: 576ad253917355393b231302dba1aced8a1123bacb2d111f0e8eaeb6df299520.
-/

namespace Shao.OQ3

open MeasureTheory Filter
open scoped ComplexConjugate

noncomputable section

theorem exists_normalTangentQuadratic_coercive (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det) :
    ∃ c : ℝ, 0 < c ∧ ∀ t s : ℝ,
      c * (t ^ 2 + s ^ 2) ≤ normalTangentQuadratic mu t s := by
  let k := ProbabilityTheory.covariance normalValue (fun x : ℝ => x) mu / normalVariance mu
  let T := transverseVariance mu
  have hT : 0 < T := div_pos hD hS
  have hden : 0 < 2 * k ^ 2 + 1 := by positivity
  let c := min (normalVariance mu / 2) (T / (2 * k ^ 2 + 1))
  have hc : 0 < c := lt_min (half_pos hS) (div_pos hT hden)
  have hcS : 2 * c ≤ normalVariance mu := by
    have hh : c ≤ normalVariance mu / 2 := min_le_left _ _
    linarith
  have hcT : c * (2 * k ^ 2 + 1) ≤ T :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  refine ⟨c, hc, ?_⟩
  intro t s
  rw [normalTangentQuadratic_complete_square mu hb hS t s]
  change c * (t ^ 2 + s ^ 2) ≤ normalVariance mu * (t + k * s) ^ 2 + T * s ^ 2
  have hgeom : t ^ 2 + s ^ 2 ≤
      2 * (t + k * s) ^ 2 + (2 * k ^ 2 + 1) * s ^ 2 := by
    nlinarith only [sq_nonneg (t + 2 * k * s)]
  calc
    c * (t ^ 2 + s ^ 2) ≤
        c * (2 * (t + k * s) ^ 2 + (2 * k ^ 2 + 1) * s ^ 2) :=
      mul_le_mul_of_nonneg_left hgeom hc.le
    _ = (2 * c) * (t + k * s) ^ 2 + (c * (2 * k ^ 2 + 1)) * s ^ 2 := by ring
    _ ≤ normalVariance mu * (t + k * s) ^ 2 + T * s ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_right hcS (sq_nonneg _))
        (mul_le_mul_of_nonneg_right hcT (sq_nonneg _))

private theorem phase_integrable (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable (fun x : ℝ => Complex.exp ((f x : ℂ) * Complex.I)) mu := by
  apply Integrable.of_bound (by fun_prop) 1
  exact ae_of_all _ fun x => by simp only [Complex.norm_exp_ofReal_mul_I, le_refl]

private theorem phase_norm_sq_eq_cos (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (f : ℝ → ℝ) (hf : Continuous f) :
    ‖∫ x : ℝ, Complex.exp ((f x : ℂ) * Complex.I) ∂mu‖ ^ 2 =
      ∫ z : ℝ × ℝ, Real.cos (f z.1 - f z.2) ∂mu.prod mu := by
  have hF := phase_integrable mu f hf
  have hconj : Integrable (fun x : ℝ => conj (Complex.exp ((f x : ℂ) * Complex.I))) mu := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun x => by simp
  have hprod := hF.mul_prod hconj
  have heq : (fun z : ℝ × ℝ =>
      Complex.exp (((f z.1 - f z.2 : ℝ) : ℂ) * Complex.I)) =
      (fun z : ℝ × ℝ => Complex.exp ((f z.1 : ℂ) * Complex.I) *
        conj (Complex.exp ((f z.2 : ℂ) * Complex.I))) := by
    funext z
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hdiff' : Integrable (fun z : ℝ × ℝ =>
      Complex.exp (((f z.1 - f z.2 : ℝ) : ℂ) * Complex.I)) (mu.prod mu) := by
    rw [heq]
    exact hprod
  have hint : (∫ z : ℝ × ℝ,
      Complex.exp (((f z.1 - f z.2 : ℝ) : ℂ) * Complex.I) ∂mu.prod mu) =
      (∫ x : ℝ, Complex.exp ((f x : ℂ) * Complex.I) ∂mu) *
        conj (∫ x : ℝ, Complex.exp ((f x : ℂ) * Complex.I) ∂mu) := by
    rw [heq, integral_prod_mul (fun x : ℝ => Complex.exp ((f x : ℂ) * Complex.I))
      (fun x : ℝ => conj (Complex.exp ((f x : ℂ) * Complex.I))), integral_conj]
  have hreal := congrArg Complex.re hint
  rw [Complex.mul_conj'] at hreal
  have hre := integral_re hdiff'
  change (∫ z : ℝ × ℝ,
      (Complex.exp (((f z.1 - f z.2 : ℝ) : ℂ) * Complex.I)).re ∂mu.prod mu) =
      (∫ z : ℝ × ℝ,
        Complex.exp (((f z.1 - f z.2 : ℝ) : ℂ) * Complex.I) ∂mu.prod mu).re at hre
  rw [← hre] at hreal
  simpa only [Complex.exp_ofReal_mul_I_re, ← Complex.ofReal_pow, Complex.ofReal_re] using hreal.symm

private theorem phase_difference_square_integrable (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (f : ℝ → ℝ) (hf : MemLp f 2 mu) :
    Integrable (fun z : ℝ × ℝ => (f z.1 - f z.2) ^ 2) (mu.prod mu) := by
  have hfi := hf.integrable (by norm_num)
  have hfsq := hf.integrable_sq
  have hfst : Integrable (fun z : ℝ × ℝ => (f z.1) ^ 2) (mu.prod mu) := hfsq.comp_fst mu
  have hsnd : Integrable (fun z : ℝ × ℝ => (f z.2) ^ 2) (mu.prod mu) := hfsq.comp_snd mu
  have hcross := hfi.mul_prod hfi
  have heq : (fun z : ℝ × ℝ => (f z.1 - f z.2) ^ 2) =
      (fun z : ℝ × ℝ => (f z.1) ^ 2 - 2 * (f z.1 * f z.2) + (f z.2) ^ 2) := by
    funext z
    ring
  rw [heq]
  exact (hfst.sub (hcross.const_mul 2)).add hsnd

private theorem phase_difference_second_moment (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (f : ℝ → ℝ) (hf : MemLp f 2 mu)
    (hzero : (∫ x : ℝ, f x ∂mu) = 0) :
    (∫ z : ℝ × ℝ, (f z.1 - f z.2) ^ 2 ∂mu.prod mu) =
      2 * ∫ x : ℝ, (f x) ^ 2 ∂mu := by
  have hfi := hf.integrable (by norm_num)
  have hfsq := hf.integrable_sq
  have hfst : Integrable (fun z : ℝ × ℝ => (f z.1) ^ 2) (mu.prod mu) := hfsq.comp_fst mu
  have hsnd : Integrable (fun z : ℝ × ℝ => (f z.2) ^ 2) (mu.prod mu) := hfsq.comp_snd mu
  have hcross : Integrable (fun z : ℝ × ℝ => f z.1 * f z.2) (mu.prod mu) :=
    hfi.mul_prod hfi
  have hsub : Integrable (fun z : ℝ × ℝ => (f z.1) ^ 2 - 2 * (f z.1 * f z.2))
      (mu.prod mu) := hfst.sub (hcross.const_mul 2)
  have heq : (fun z : ℝ × ℝ => (f z.1 - f z.2) ^ 2) =
      (fun z : ℝ × ℝ => (f z.1) ^ 2 - 2 * (f z.1 * f z.2) + (f z.2) ^ 2) := by
    funext z
    ring
  rw [heq, integral_add hsub hsnd, integral_sub hfst (hcross.const_mul 2),
    integral_const_mul, integral_prod_mul, integral_fun_fst (fun x : ℝ => (f x) ^ 2),
    integral_fun_snd (fun x : ℝ => (f x) ^ 2), hzero]
  simp [measureReal_def]
  ring

private theorem phase_norm_sq_le (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (f : ℝ → ℝ) (hf : Continuous f) (hmem : MemLp f 2 mu)
    (hzero : (∫ x : ℝ, f x ∂mu) = 0)
    (hphase : ∀ᵐ z : ℝ × ℝ ∂mu.prod mu, |f z.1 - f z.2| ≤ Real.pi) :
    ‖∫ x : ℝ, Complex.exp ((f x : ℂ) * Complex.I) ∂mu‖ ^ 2 ≤
      1 - (4 / Real.pi ^ 2) * ∫ x : ℝ, (f x) ^ 2 ∂mu := by
  have hsq := phase_difference_square_integrable mu f hmem
  have hcos : Integrable (fun z : ℝ × ℝ => Real.cos (f z.1 - f z.2))
      (mu.prod mu) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _
  have hmajor : Integrable (fun z : ℝ × ℝ =>
      1 - (2 / Real.pi ^ 2) * (f z.1 - f z.2) ^ 2) (mu.prod mu) :=
    (integrable_const 1).sub (hsq.const_mul _)
  rw [phase_norm_sq_eq_cos mu f hf]
  calc
    (∫ z : ℝ × ℝ, Real.cos (f z.1 - f z.2) ∂mu.prod mu) ≤
        ∫ z : ℝ × ℝ, 1 - (2 / Real.pi ^ 2) * (f z.1 - f z.2) ^ 2 ∂mu.prod mu :=
      integral_mono_ae hcos hmajor (hphase.mono fun _ hz =>
        Real.cos_le_one_sub_mul_cos_sq hz)
    _ = 1 - (4 / Real.pi ^ 2) * ∫ x : ℝ, (f x) ^ 2 ∂mu := by
      rw [integral_sub (integrable_const 1) (hsq.const_mul _), integral_const_mul,
        phase_difference_second_moment mu f hmem hzero]
      simp [measureReal_def]
      ring

private theorem normalValue_abs_le (B x : ℝ) (hx : |x| ≤ B) :
    |normalValue x| ≤ 8 * B + B ^ 2 := by
  unfold normalValue
  calc
    |8 * x - x ^ 2| ≤ |8 * x| + |x ^ 2| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (8 * x) 0 (x ^ 2)
    _ = 8 * |x| + |x| ^ 2 := by simp
    _ ≤ 8 * B + B ^ 2 := add_le_add
      (mul_le_mul_of_nonneg_left hx (by norm_num))
      (pow_le_pow_left₀ (abs_nonneg x) hx 2)

theorem exists_centeredNormalTangentCharacteristic_gaussian_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det) :
    ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧ ∀ t s : ℝ,
      |t| ≤ delta → |s| ≤ delta →
        ‖centeredNormalTangentCharacteristic mu q a t s‖ ≤
          Real.exp (-c * (t ^ 2 + s ^ 2)) := by
  obtain ⟨c0, hc0, hcoercive⟩ := exists_normalTangentQuadratic_coercive mu hb hS hD
  let B : ℝ := 4 + Real.sqrt 10
  let BY : ℝ := 8 * B + B ^ 2
  let delta := Real.pi / (2 * (BY + B))
  let c := 2 * c0 / Real.pi ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hBY : 0 < BY := by dsimp [BY]; positivity
  have hden : 0 < 2 * (BY + B) := by positivity
  have hdelta : 0 < delta := div_pos Real.pi_pos hden
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨delta, c, hdelta, hc, ?_⟩
  intro t s ht hs
  let f := centeredNormalProjection q a t s
  have hf : Continuous f := by
    dsimp only [f]
    unfold centeredNormalProjection normalValue
    fun_prop
  have hmem : MemLp f 2 mu := centeredNormalProjection_memLp_two mu hb q a t s
  have hzero : (∫ x : ℝ, f x ∂mu) = 0 :=
    centeredNormalProjection_integral_zero mu hb q a hq ha t s
  have hquad : (∫ x : ℝ, (f x) ^ 2 ∂mu) = normalTangentQuadratic mu t s :=
    centeredNormalProjection_second_moment mu hb q a hq ha t s
  have hphase : ∀ᵐ z : ℝ × ℝ ∂mu.prod mu, |f z.1 - f z.2| ≤ Real.pi := by
    have hb1 : ∀ᵐ z : ℝ × ℝ ∂mu.prod mu, |z.1| ≤ B := by
      apply (Measure.ae_prod_iff_ae_ae
        (isClosed_le (by fun_prop) continuous_const).measurableSet).mpr
      filter_upwards [hb] with x hx
      exact ae_of_all _ fun _ => hx
    have hb2 : ∀ᵐ z : ℝ × ℝ ∂mu.prod mu, |z.2| ≤ B := by
      apply (Measure.ae_prod_iff_ae_ae
        (isClosed_le (by fun_prop) continuous_const).measurableSet).mpr
      exact ae_of_all _ fun _ => hb
    filter_upwards [hb1, hb2] with z hz1 hz2
    have hY1 := normalValue_abs_le B z.1 hz1
    have hY2 := normalValue_abs_le B z.2 hz2
    have hY : |normalValue z.1 - normalValue z.2| ≤ 2 * BY := by
      calc
        |normalValue z.1 - normalValue z.2| ≤ |normalValue z.1| + |normalValue z.2| :=
          by simpa using abs_sub_le (normalValue z.1) 0 (normalValue z.2)
        _ ≤ 2 * BY := by change _ ≤ 2 * (8 * B + B ^ 2); linarith
    have hX : |z.1 - z.2| ≤ 2 * B := by
      have hh : |z.1 - z.2| ≤ |z.1| + |z.2| := by simpa using abs_sub_le z.1 0 z.2
      linarith
    have heq : f z.1 - f z.2 =
        t * (normalValue z.1 - normalValue z.2) + s * (z.1 - z.2) := by
      dsimp [f, centeredNormalProjection]
      ring
    rw [heq]
    calc
      |t * (normalValue z.1 - normalValue z.2) + s * (z.1 - z.2)| ≤
          |t| * |normalValue z.1 - normalValue z.2| + |s| * |z.1 - z.2| := by
        simpa only [abs_mul] using abs_add_le
          (t * (normalValue z.1 - normalValue z.2)) (s * (z.1 - z.2))
      _ ≤ delta * (2 * BY) + delta * (2 * B) := add_le_add
        (mul_le_mul ht hY (abs_nonneg _) hdelta.le)
        (mul_le_mul hs hX (abs_nonneg _) hdelta.le)
      _ = Real.pi := by dsimp [delta]; field_simp [hden.ne']
  have hsq := phase_norm_sq_le mu f hf hmem hzero hphase
  rw [hquad] at hsq
  have hexp0 : ‖∫ x : ℝ, Complex.exp ((f x : ℂ) * Complex.I) ∂mu‖ ^ 2 ≤
      Real.exp (-(4 / Real.pi ^ 2) * normalTangentQuadratic mu t s) := by
    have he := Real.add_one_le_exp (-(4 / Real.pi ^ 2) * normalTangentQuadratic mu t s)
    exact hsq.trans (by linarith)
  have hce : -(4 / Real.pi ^ 2) * normalTangentQuadratic mu t s ≤
      2 * (-c * (t ^ 2 + s ^ 2)) := by
    calc
      -(4 / Real.pi ^ 2) * normalTangentQuadratic mu t s ≤
          -(4 / Real.pi ^ 2) * (c0 * (t ^ 2 + s ^ 2)) := by
        have hcoeff : 0 ≤ (4 : ℝ) / Real.pi ^ 2 := by positivity
        simpa only [neg_mul] using
          neg_le_neg (mul_le_mul_of_nonneg_left (hcoercive t s) hcoeff)
      _ = 2 * (-c * (t ^ 2 + s ^ 2)) := by dsimp [c]; ring
  have hexp := hexp0.trans (Real.exp_le_exp.mpr hce)
  have hexpid : (Real.exp (-c * (t ^ 2 + s ^ 2))) ^ 2 =
      Real.exp (2 * (-c * (t ^ 2 + s ^ 2))) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  change ‖∫ x : ℝ, Complex.exp ((f x : ℂ) * Complex.I) ∂mu‖ ≤ _
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp (hexp.trans_eq hexpid.symm)

theorem exists_centeredNormalTangentCharacteristic_scaled_domination (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det) :
    ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧ ∀ s : ℝ,
      ∀ᶠ n : ℕ in atTop, ∀ v : ℝ,
        |v| ≤ delta * Real.sqrt (n : ℝ) →
          ‖(centeredNormalTangentCharacteristic mu q a
            ((Real.sqrt (n : ℝ))⁻¹ * v) ((Real.sqrt (n : ℝ))⁻¹ * s)) ^ n‖ ≤
            Real.exp (-c * v ^ 2) := by
  obtain ⟨delta, c, hdelta, hc, hlocal⟩ :=
    exists_centeredNormalTangentCharacteristic_gaussian_bound mu hb q a hq ha hS hD
  refine ⟨delta, c, hdelta, hc, ?_⟩
  intro s
  have ht : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in atTop, |s| / delta ≤ Real.sqrt (n : ℝ) :=
    ht.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop 1, hlarge] with n hn hsn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hroot2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hs : |(Real.sqrt (n : ℝ))⁻¹ * s| ≤ delta := by
    have hh : |s| ≤ delta * Real.sqrt (n : ℝ) := by
      simpa only [mul_comm] using (div_le_iff₀ hdelta).mp hsn
    simpa [abs_mul, abs_inv, abs_of_pos hroot, div_eq_mul_inv, mul_comm] using
      (div_le_iff₀ hroot).mpr hh
  intro v hv
  have hv' : |(Real.sqrt (n : ℝ))⁻¹ * v| ≤ delta := by
    simpa [abs_mul, abs_inv, abs_of_pos hroot, div_eq_mul_inv, mul_comm] using
      (div_le_iff₀ hroot).mpr hv
  have hh := hlocal _ _ hv' hs
  rw [norm_pow]
  calc
    ‖centeredNormalTangentCharacteristic mu q a
        ((Real.sqrt (n : ℝ))⁻¹ * v) ((Real.sqrt (n : ℝ))⁻¹ * s)‖ ^ n ≤
        (Real.exp (-c * (((Real.sqrt (n : ℝ))⁻¹ * v) ^ 2 +
          ((Real.sqrt (n : ℝ))⁻¹ * s) ^ 2))) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) hh n
    _ = Real.exp (-c * (v ^ 2 + s ^ 2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp [hroot.ne']
      rw [hroot2]
    _ ≤ Real.exp (-c * v ^ 2) := Real.exp_le_exp.mpr (by
      nlinarith only [mul_nonneg hc.le (sq_nonneg s)])

end
end Shao.OQ3
