import Shao.OQ3.NormalTangentMoments
import Shao.OQ3.FiniteFarArc
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Actual centered normal/tangent characteristic power limit

Source: current/oq3/proofs/r1/report.md, lines 309-345, especially 339-343.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U12d v2 scope: 39dd7f63f4b6ff42e3c45516cb6bab093e158cf388836721f178ec77a4528717.
-/

namespace Shao.OQ3

open MeasureTheory Filter
open scoped Matrix

noncomputable section

private theorem exp_real_phase_cubic (z : ℝ) (hz : |z| ≤ 1) :
    ‖Complex.exp ((z : ℂ) * Complex.I) -
      (1 + (z : ℂ) * Complex.I - (z : ℂ) ^ 2 / 2)‖ ≤ |z| ^ 3 := by
  have hsmall : ‖(z : ℂ) * Complex.I‖ ≤ 1 := by simpa [norm_mul] using hz
  have hh := Complex.exp_bound hsmall (n := 3) (by decide)
  norm_num [Finset.sum_range_succ, mul_pow, Complex.I_sq, norm_mul] at hh
  have hpoly : (1 + (z : ℂ) * Complex.I + (-(z : ℂ) ^ 2) / 2) =
      1 + (z : ℂ) * Complex.I - (z : ℂ) ^ 2 / 2 := by ring
  rw [hpoly] at hh
  exact hh.trans (by nlinarith only [pow_nonneg (abs_nonneg z) 3])

private theorem exists_projection_bound (mu : Measure ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a v s : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ᵐ x ∂mu, |centeredNormalProjection q a v s x| ≤ M := by
  have hf : Continuous (centeredNormalProjection q a v s) := by
    unfold centeredNormalProjection normalValue
    fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact
    (Set.Icc (-(4 + Real.sqrt 10)) (4 + Real.sqrt 10))).exists_bound_of_continuousOn
      hf.continuousOn
  refine ⟨|C| + 1, by positivity, ?_⟩
  filter_upwards [hb] with x hx
  have hh : |centeredNormalProjection q a v s x| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC x (abs_le.mp hx)
  exact hh.trans (by linarith only [le_abs_self C])

theorem centeredNormalTangentCharacteristic_cubic_remainder (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (v s : ℝ) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ ∀ u : ℝ, |u| ≤ delta →
      ‖centeredNormalTangentCharacteristic mu q a (u * v) (u * s) -
        (1 - ((normalTangentQuadratic mu v s * u ^ 2 / 2 : ℝ) : ℂ))‖ ≤
          C * |u| ^ 3 := by
  let f := centeredNormalProjection q a v s
  have hf : Continuous f := by
    dsimp only [f]
    unfold centeredNormalProjection normalValue
    fun_prop
  obtain ⟨M, hM, hbound⟩ := exists_projection_bound mu hb q a v s
  have hmem : MemLp f 2 mu := centeredNormalProjection_memLp_two mu hb q a v s
  have hfi : Integrable f mu := hmem.integrable (by norm_num)
  have hfsq : Integrable (fun x : ℝ => (f x) ^ 2) mu := hmem.integrable_sq
  have hzero : (∫ x : ℝ, f x ∂mu) = 0 :=
    centeredNormalProjection_integral_zero mu hb q a hq ha v s
  have hquad : (∫ x : ℝ, (f x) ^ 2 ∂mu) = normalTangentQuadratic mu v s :=
    centeredNormalProjection_second_moment mu hb q a hq ha v s
  refine ⟨M ^ 3, M⁻¹, by positivity, inv_pos.mpr hM, ?_⟩
  intro u hu
  let P : ℝ → ℂ := fun x => 1 + (u : ℂ) * ((f x : ℂ) * Complex.I) -
    ((u : ℂ) ^ 2 / 2) * (f x : ℂ) ^ 2
  have hfc : Integrable (fun x : ℝ => (f x : ℂ)) mu := hfi.ofReal
  have hfsqc : Integrable (fun x : ℝ => (f x : ℂ) ^ 2) mu := by
    simp_rw [← Complex.ofReal_pow]
    exact hfsq.ofReal
  have hlin : Integrable (fun x : ℝ => 1 + (u : ℂ) * ((f x : ℂ) * Complex.I)) mu :=
    (integrable_const 1).add ((hfc.mul_const Complex.I).const_mul (u : ℂ))
  have hP : Integrable P mu := hlin.sub (hfsqc.const_mul _)
  have hE : Integrable (fun x : ℝ => Complex.exp (((u * f x : ℝ) : ℂ) * Complex.I)) mu := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun x => by simp only [Complex.norm_exp_ofReal_mul_I, le_refl]
  have hR := hE.sub hP
  have hfc0 : (∫ x : ℝ, (f x : ℂ) ∂mu) = 0 := by
    rw [integral_complex_ofReal, hzero, Complex.ofReal_zero]
  have hfc2 : (∫ x : ℝ, (f x : ℂ) ^ 2 ∂mu) = (normalTangentQuadratic mu v s : ℂ) := by
    simp_rw [← Complex.ofReal_pow]
    rw [integral_complex_ofReal, hquad]
  have hPint : (∫ x : ℝ, P x ∂mu) =
      1 - ((normalTangentQuadratic mu v s * u ^ 2 / 2 : ℝ) : ℂ) := by
    dsimp only [P]
    rw [integral_sub hlin (hfsqc.const_mul _),
      integral_add (integrable_const 1) ((hfc.mul_const Complex.I).const_mul (u : ℂ)),
      integral_const_mul, integral_mul_const, integral_const_mul, hfc0, hfc2]
    simp [measureReal_def]
    ring
  have hchar : centeredNormalTangentCharacteristic mu q a (u * v) (u * s) =
      ∫ x : ℝ, Complex.exp (((u * f x : ℝ) : ℂ) * Complex.I) ∂mu := by
    unfold centeredNormalTangentCharacteristic
    congr 1
    funext x
    congr 1
    dsimp [f, centeredNormalProjection]
    push_cast
    ring
  have hRint : (∫ x : ℝ,
      Complex.exp (((u * f x : ℝ) : ℂ) * Complex.I) - P x ∂mu) =
      centeredNormalTangentCharacteristic mu q a (u * v) (u * s) -
        (1 - ((normalTangentQuadratic mu v s * u ^ 2 / 2 : ℝ) : ℂ)) := by
    rw [integral_sub hE hP, hPint, hchar]
  have hRb : ∀ᵐ x ∂mu,
      ‖Complex.exp (((u * f x : ℝ) : ℂ) * Complex.I) - P x‖ ≤ M ^ 3 * |u| ^ 3 := by
    filter_upwards [hbound] with x hx
    have huf : |u * f x| ≤ 1 := by
      rw [abs_mul]
      calc
        |u| * |f x| ≤ M⁻¹ * M := mul_le_mul hu hx (abs_nonneg _) (inv_nonneg.mpr hM.le)
        _ = 1 := inv_mul_cancel₀ hM.ne'
    have hh := exp_real_phase_cubic (u * f x) huf
    have heq : (1 + ((u * f x : ℝ) : ℂ) * Complex.I -
        ((u * f x : ℝ) : ℂ) ^ 2 / 2) = P x := by
      dsimp [P]
      push_cast
      ring
    rw [heq] at hh
    calc
      ‖Complex.exp (((u * f x : ℝ) : ℂ) * Complex.I) - P x‖ ≤ |u * f x| ^ 3 := hh
      _ ≤ (|u| * M) ^ 3 := pow_le_pow_left₀ (abs_nonneg _)
        (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)) 3
      _ = M ^ 3 * |u| ^ 3 := by ring
  rw [← hRint]
  calc
    ‖∫ x : ℝ, Complex.exp (((u * f x : ℝ) : ℂ) * Complex.I) - P x ∂mu‖ ≤
        ∫ x : ℝ, ‖Complex.exp (((u * f x : ℝ) : ℂ) * Complex.I) - P x‖ ∂mu :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _ : ℝ, M ^ 3 * |u| ^ 3 ∂mu := integral_mono_ae hR.norm (integrable_const _) hRb
    _ = M ^ 3 * |u| ^ 3 := by simp [measureReal_def]

theorem centeredNormalTangentCharacteristic_power_tendsto (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (v s : ℝ) :
    Tendsto (fun n : ℕ =>
      (centeredNormalTangentCharacteristic mu q a
        ((Real.sqrt (n : ℝ))⁻¹ * v) ((Real.sqrt (n : ℝ))⁻¹ * s)) ^ n)
      atTop (nhds (Complex.exp ((-normalTangentQuadratic mu v s / 2 : ℝ) : ℂ))) := by
  obtain ⟨C, delta, hC, hdelta, hrem⟩ :=
    centeredNormalTangentCharacteristic_cubic_remainder mu hb q a hq ha v s
  apply Complex.tendsto_pow_exp_of_isLittleO_sub_add_div
    ((-normalTangentQuadratic mu v s / 2 : ℝ) : ℂ)
  apply Asymptotics.IsLittleO.of_bound
  intro eps heps
  have ht : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hd : ∀ᶠ n : ℕ in atTop, delta⁻¹ ≤ Real.sqrt (n : ℝ) :=
    ht.eventually (eventually_ge_atTop _)
  have he : ∀ᶠ n : ℕ in atTop, C / eps ≤ Real.sqrt (n : ℝ) :=
    ht.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop 1, hd, he] with n hn hdn hen
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hroot2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hsmall : |(Real.sqrt (n : ℝ))⁻¹| ≤ delta := by
    have hh : 1 ≤ delta * Real.sqrt (n : ℝ) := by
      calc
        1 = delta * delta⁻¹ := (mul_inv_cancel₀ hdelta.ne').symm
        _ ≤ delta * Real.sqrt (n : ℝ) := mul_le_mul_of_nonneg_left hdn hdelta.le
    simpa only [one_div, abs_of_pos (inv_pos.mpr hroot)] using (div_le_iff₀ hroot).mpr hh
  have hCe : C ≤ eps * Real.sqrt (n : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ heps).mp hen
  have hri2 : ((Real.sqrt (n : ℝ))⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
    rw [inv_pow, hroot2]
  have happrox : (1 - ((normalTangentQuadratic mu v s *
      ((Real.sqrt (n : ℝ))⁻¹) ^ 2 / 2 : ℝ) : ℂ)) =
      1 + ((-normalTangentQuadratic mu v s / 2 : ℝ) : ℂ) / (n : ℂ) := by
    rw [hri2]
    push_cast
    ring
  have hh := hrem (Real.sqrt (n : ℝ))⁻¹ hsmall
  rw [happrox] at hh
  calc
    ‖centeredNormalTangentCharacteristic mu q a
        ((Real.sqrt (n : ℝ))⁻¹ * v) ((Real.sqrt (n : ℝ))⁻¹ * s) -
        (1 + ((-normalTangentQuadratic mu v s / 2 : ℝ) : ℂ) / (n : ℂ))‖ ≤
        C * |(Real.sqrt (n : ℝ))⁻¹| ^ 3 := hh
    _ ≤ eps * ‖(1 : ℂ) / (n : ℂ)‖ := by
      rw [abs_of_pos (inv_pos.mpr hroot), norm_div, norm_one, Complex.norm_natCast]
      calc
        C * ((Real.sqrt (n : ℝ))⁻¹) ^ 3 ≤
            (eps * Real.sqrt (n : ℝ)) * ((Real.sqrt (n : ℝ))⁻¹) ^ 3 :=
          mul_le_mul_of_nonneg_right hCe (by positivity)
        _ = eps * (1 / (n : ℝ)) := by
          field_simp [hroot.ne', hnpos.ne']
          rw [hroot2]

theorem finite_atomic_normal_tangent_power_tendsto (ell q : ℝ) (p : Fin 4 → ℝ)
    (r : ℕ → ℝ) (J : ℕ) (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hp : ∀ i, 0 ≤ finiteBase ell p r J i) (hr : ∀ j, 0 ≤ r j)
    (v s : ℝ) :
    Tendsto (fun n : ℕ =>
      (centeredNormalTangentCharacteristic (atomicMeasure (finiteMass ell p r J))
        q (q / 4) ((Real.sqrt (n : ℝ))⁻¹ * v) ((Real.sqrt (n : ℝ))⁻¹ * s)) ^ n)
      atTop (nhds (Complex.exp
        ((-normalTangentQuadratic (atomicMeasure (finiteMass ell p r J)) v s / 2 : ℝ) : ℂ))) := by
  have hm := finite_atomic_normal_tangent_moments ell q p r J hM hc hp hr
  let := hm.1
  have hb : ∀ᵐ x ∂atomicMeasure (finiteMass ell p r J), |x| ≤ 4 + Real.sqrt 10 :=
    (atomicMeasure_ae_bounds _).mono fun _ hx => hx.2
  exact centeredNormalTangentCharacteristic_power_tendsto _ hb q (q / 4)
    hm.2.2.1 hm.2.1 v s

end
end Shao.OQ3
