import Shao.OQ3.SampleBoundary
import Shao.OQ3.FiniteFarArc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Pi

namespace Shao.OQ3

open MeasureTheory
open scoped BigOperators Matrix

noncomputable section

def normalLayerIntegrand (q a d s : ℝ) (n : ℕ) (z : Shao.Path n) : ℂ :=
  ({w : Shao.Path n | normalDeviation q w = d}).indicator
    (fun w : Shao.Path n => Complex.exp
      (((s * ((∑ i, w i) - (n : ℝ) * a) / Real.sqrt (n : ℝ) : ℝ) : ℂ) * Complex.I)) z

def normalLayerCharacteristic (mu : Measure ℝ) (q a d s : ℝ) (n : ℕ) : ℂ :=
  ∫ z : Shao.Path n, normalLayerIntegrand q a d s n z
    ∂Measure.pi (fun _ : Fin n => mu)

theorem normal_lattice_character_orthogonality (h : ℝ) (hh : 0 < h) (k : ℤ) :
    ((h / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ in Set.Icc (-Real.pi / h) (Real.pi / h),
        Complex.exp (((t * (h * (k : ℝ)) : ℝ) : ℂ) * Complex.I)
          ∂(volume : Measure ℝ)) = if k = 0 then 1 else 0 := by
  have hab : -Real.pi / h ≤ Real.pi / h := by
    exact div_le_div_of_nonneg_right (by linarith [Real.pi_pos]) hh.le
  have hcont : Continuous (fun t : ℝ =>
      Complex.exp (((t * (h * (k : ℝ)) : ℝ) : ℂ) * Complex.I)) := by fun_prop
  have _hint : IntegrableOn (fun t : ℝ =>
      Complex.exp (((t * (h * (k : ℝ)) : ℝ) : ℂ) * Complex.I))
      (Set.Icc (-Real.pi / h) (Real.pi / h)) (volume : Measure ℝ) :=
    hcont.integrableOn_Icc
  by_cases hk : k = 0
  · subst k
    simp only [Int.cast_zero, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, ite_true]
    rw [setIntegral_const, Real.volume_real_Icc_of_le hab]
    simp only [Complex.real_smul, mul_one]
    have heq : h / (2 * Real.pi) * (Real.pi / h - -Real.pi / h) = 1 := by
      field_simp; ring
    rw [← Complex.ofReal_mul, heq, Complex.ofReal_one]
  · let c : ℂ := ((h * (k : ℝ) : ℝ) : ℂ) * Complex.I
    have hc : c ≠ 0 := by
      apply mul_ne_zero _ Complex.I_ne_zero
      exact Complex.ofReal_ne_zero.mpr (mul_ne_zero hh.ne' (by exact_mod_cast hk))
    have hfun : (fun t : ℝ =>
        Complex.exp (((t * (h * (k : ℝ)) : ℝ) : ℂ) * Complex.I)) =
        (fun t : ℝ => Complex.exp (c * (t : ℂ))) := by
      funext t
      congr 1
      dsimp [c]
      push_cast
      ring
    have hends : Complex.exp (c * ((Real.pi / h : ℝ) : ℂ)) =
        Complex.exp (c * ((-Real.pi / h : ℝ) : ℂ)) := by
      apply Complex.exp_eq_exp_iff_exists_int.mpr
      refine ⟨k, ?_⟩
      apply Complex.ext
      · simp [c]
      · simp [c]
        field_simp; ring
    rw [hfun, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab, integral_exp_mul_complex hc,
      hends, sub_self, zero_div, mul_zero, ite_eq_right_iff.mpr (fun hzero => (hk hzero).elim)]

theorem iid_centeredNormalTangentCharacteristic_power (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (q a t s : ℝ) (n : ℕ) :
    (∫ z : Shao.Path n, Complex.exp
      (((t * normalDeviation q z + s * ((∑ i, z i) - (n : ℝ) * a) : ℝ) : ℂ) * Complex.I)
        ∂Measure.pi (fun _ : Fin n => mu)) =
      centeredNormalTangentCharacteristic mu q a t s ^ n := by
  let f : ℝ → ℂ := fun x => Complex.exp
    (((t * (normalValue x - q) + s * (x - a) : ℝ) : ℂ) * Complex.I)
  have hf : Integrable f mu := by
    apply Integrable.of_bound (by dsimp [f]; unfold normalValue; fun_prop) 1
    exact ae_of_all _ fun x => by
      dsimp [f]
      simp only [Complex.norm_exp_ofReal_mul_I, le_refl]
  have _hprod : Integrable (fun z : Shao.Path n => ∏ i, f (z i))
      (Measure.pi (fun _ : Fin n => mu)) :=
    Integrable.fin_nat_prod (fun _ => hf)
  have heq (z : Shao.Path n) : Complex.exp
      (((t * normalDeviation q z + s * ((∑ i, z i) - (n : ℝ) * a) : ℝ) : ℂ) * Complex.I) =
      ∏ i, f (z i) := by
    have hsum : t * normalDeviation q z + s * ((∑ i, z i) - (n : ℝ) * a) =
        ∑ i, (t * (normalValue (z i) - q) + s * (z i - a)) := by
      simp only [normalDeviation, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        mul_sub, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [hsum]
    dsimp [f]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
  simp_rw [heq]
  simpa only [Fintype.card_fin, f, centeredNormalTangentCharacteristic] using
    (integral_fintype_prod_eq_pow (ι := Fin n) (μ := mu) f)

theorem normalLayerIntegrand_integrable (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (q a d s : ℝ) (n : ℕ) :
    Integrable (normalLayerIntegrand q a d s n) (Measure.pi (fun _ : Fin n => mu)) := by
  have hnormal : Continuous (fun z : Shao.Path n => normalDeviation q z) := by
    unfold normalDeviation normalValue
    fun_prop
  have hset : MeasurableSet {z : Shao.Path n | normalDeviation q z = d} :=
    (isClosed_eq hnormal continuous_const).measurableSet
  have hphase : Continuous (fun z : Shao.Path n => Complex.exp
      (((s * ((∑ i, z i) - (n : ℝ) * a) / Real.sqrt (n : ℝ) : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  have hp : Integrable (fun z : Shao.Path n => Complex.exp
      (((s * ((∑ i, z i) - (n : ℝ) * a) / Real.sqrt (n : ℝ) : ℝ) : ℂ) * Complex.I))
      (Measure.pi (fun _ : Fin n => mu)) := by
    apply Integrable.of_bound hphase.aestronglyMeasurable 1
    exact ae_of_all _ fun z => by simp only [Complex.norm_exp_ofReal_mul_I, le_refl]
  exact hp.indicator hset

theorem normal_layer_Fourier_identity (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (q a h d s : ℝ) (hh : 0 < h)
    (hgrid : ∀ᵐ x ∂mu, ∃ k : ℤ, normalValue x = h * (k : ℝ))
    (n : ℕ) (hlayer : ∃ k : ℤ, d + (n : ℝ) * q = h * (k : ℝ)) :
    normalLayerCharacteristic mu q a d s n =
      ((h / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ in Set.Icc (-Real.pi / h) (Real.pi / h),
          Complex.exp (((-(t * d) : ℝ) : ℂ) * Complex.I) *
            centeredNormalTangentCharacteristic mu q a t
              ((Real.sqrt (n : ℝ))⁻¹ * s) ^ n ∂(volume : Measure ℝ)) := by
  classical
  let B : Set ℝ := Set.Icc (-Real.pi / h) (Real.pi / h)
  let C : ℂ := ((h / (2 * Real.pi) : ℝ) : ℂ)
  let nu : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
  let T : Shao.Path n → ℂ := fun z => Complex.exp
    (((s * ((∑ i, z i) - (n : ℝ) * a) / Real.sqrt (n : ℝ) : ℝ) : ℂ) * Complex.I)
  let F : ℝ → Shao.Path n → ℂ := fun t z =>
    Complex.exp (((t * (normalDeviation q z - d) : ℝ) : ℂ) * Complex.I) * T z
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict B) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (show (volume : Measure ℝ) B < ⊤ from
        (isCompact_Icc : IsCompact B).measure_lt_top)⟩
  have hFcont : Continuous (Function.uncurry F) := by
    dsimp [F, T, Function.uncurry]
    unfold normalDeviation normalValue
    fun_prop
  have hF : Integrable (Function.uncurry F) (((volume : Measure ℝ).restrict B).prod nu) := by
    apply Integrable.of_bound hFcont.aestronglyMeasurable 1
    exact ae_of_all _ fun z => by
      dsimp [F, T, Function.uncurry]
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
  have hcoords (i : Fin n) : ∀ᵐ z ∂nu,
      ∃ k : ℤ, normalValue (z i) = h * (k : ℝ) :=
    (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => mu) (i := i)).eventually hgrid
  have hall : ∀ᵐ z ∂nu, ∀ i : Fin n,
      ∃ k : ℤ, normalValue (z i) = h * (k : ℝ) := ae_all_iff.mpr hcoords
  obtain ⟨k0, hk0⟩ := hlayer
  have hZ : ∀ᵐ z ∂nu, ∃ k : ℤ, normalDeviation q z - d = h * (k : ℝ) := by
    filter_upwards [hall] with z hz
    choose k hk using hz
    refine ⟨(∑ i, k i) - k0, ?_⟩
    simp only [normalDeviation, Int.cast_sub, Int.cast_sum]
    have hsum : (∑ i, normalValue (z i)) = h * ∑ i, (k i : ℝ) := by
      simp_rw [hk]
      rw [Finset.mul_sum]
    rw [hsum]
    nlinarith [hk0]
  have hpoint : ∀ᵐ z ∂nu,
      normalLayerIntegrand q a d s n z = C * ∫ t : ℝ in B, F t z ∂(volume : Measure ℝ) := by
    filter_upwards [hZ] with z hz
    obtain ⟨k, hk⟩ := hz
    have hzero : k = 0 ↔ normalDeviation q z = d := by
      constructor
      · intro hzero
        rw [hzero, Int.cast_zero, mul_zero] at hk
        linarith
      · intro heq
        have hmul : h * (k : ℝ) = 0 := by linarith [hk]
        have hcast : (k : ℝ) = 0 := (mul_eq_zero.mp hmul).resolve_left hh.ne'
        exact_mod_cast hcast
    have hcoeff : C * (∫ t : ℝ in B,
        Complex.exp (((t * (normalDeviation q z - d) : ℝ) : ℂ) * Complex.I)
          ∂(volume : Measure ℝ)) = if normalDeviation q z = d then 1 else 0 := by
      dsimp [C, B]
      rw [hk]
      simpa only [hzero] using normal_lattice_character_orthogonality h hh k
    calc
      normalLayerIntegrand q a d s n z =
          (if normalDeviation q z = d then 1 else 0) * T z := by
        by_cases heq : normalDeviation q z = d
        · simp [normalLayerIntegrand, heq, T]
        · simp [normalLayerIntegrand, heq]
      _ = (C * (∫ t : ℝ in B,
          Complex.exp (((t * (normalDeviation q z - d) : ℝ) : ℂ) * Complex.I)
            ∂(volume : Measure ℝ))) * T z := by rw [hcoeff]
      _ = C * ∫ t : ℝ in B, F t z ∂(volume : Measure ℝ) := by
        dsimp [F]
        rw [integral_mul_const]
        ring
  have hinner (t : ℝ) : (∫ z : Shao.Path n, F t z ∂nu) =
      Complex.exp (((-(t * d) : ℝ) : ℂ) * Complex.I) *
        centeredNormalTangentCharacteristic mu q a t ((Real.sqrt (n : ℝ))⁻¹ * s) ^ n := by
    rw [← iid_centeredNormalTangentCharacteristic_power mu q a t
      ((Real.sqrt (n : ℝ))⁻¹ * s) n, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun z => by
      dsimp [F, T]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
  unfold normalLayerCharacteristic
  change (∫ z : Shao.Path n, normalLayerIntegrand q a d s n z ∂nu) = _
  calc
    (∫ z : Shao.Path n, normalLayerIntegrand q a d s n z ∂nu) =
        ∫ z : Shao.Path n, C * ∫ t : ℝ in B, F t z ∂(volume : Measure ℝ) ∂nu :=
      integral_congr_ae hpoint
    _ = C * ∫ z : Shao.Path n, ∫ t : ℝ in B, F t z ∂(volume : Measure ℝ) ∂nu :=
      integral_const_mul C _
    _ = C * ∫ t : ℝ in B, ∫ z : Shao.Path n, F t z ∂nu ∂(volume : Measure ℝ) := by
      rw [integral_integral_swap hF]
    _ = _ := by simp_rw [hinner]; rfl

theorem finite_atomic_normal_layer_Fourier_identity (ell q : ℝ) (p : Fin 4 → ℝ)
    (r : ℕ → ℝ) (J : ℕ) (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hp : ∀ i, 0 ≤ finiteBase ell p r J i) (hr : ∀ j, 0 ≤ r j)
    (d s : ℝ) (n : ℕ)
    (hlayer : ∃ k : ℤ, d + (n : ℝ) * q = dyadicMesh J * (k : ℝ)) :
    normalLayerCharacteristic (atomicMeasure (finiteMass ell p r J)) q (q / 4) d s n =
      ((dyadicMesh J / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ in Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J),
          Complex.exp (((-(t * d) : ℝ) : ℂ) * Complex.I) *
            centeredNormalTangentCharacteristic (atomicMeasure (finiteMass ell p r J))
              q (q / 4) t ((Real.sqrt (n : ℝ))⁻¹ * s) ^ n ∂(volume : Measure ℝ)) := by
  let w := finiteMass ell p r J
  have hw : ∀ i, 0 ≤ w i := finiteMass_nonneg ell p r J hp hr
  have hm := finiteMass_constraints ell q p r J hM hc
  have hmass : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  let := atomicMeasure_isProbabilityMeasure w hw hmass
  have hgrid : ∀ᵐ x ∂atomicMeasure w, ∃ k : ℤ, normalValue x = dyadicMesh J * (k : ℝ) := by
    filter_upwards [atomicMeasure_finiteMass_ae_range ell p r J] with x hx
    obtain ⟨i, rfl⟩ := hx
    exact stageAtom_normalValue_lattice J i
  exact normal_layer_Fourier_identity (atomicMeasure w) q (q / 4) (dyadicMesh J) d s
    (by unfold dyadicMesh; positivity) hgrid n hlayer

end
end Shao.OQ3
