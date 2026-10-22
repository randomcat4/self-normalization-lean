import Shao.OQ3.NormalTangentMoments
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Shao.OQ3

open MeasureTheory

noncomputable section

def centeredNormalLogMGF (mu : Measure ℝ) (q a v s : ℝ) : ℝ :=
  Real.log (∫ x : ℝ, Real.exp (centeredNormalProjection q a v s x) ∂mu)

private theorem real_exp_cubic_upper (z : ℝ) (hz : |z| ≤ 1) :
    Real.exp z ≤ 1 + z + z ^ 2 / 2 + |z| ^ 3 := by
  have hh := Real.exp_bound hz (n := 3) (by decide)
  norm_num [Finset.sum_range_succ] at hh
  have hle := le_abs_self (Real.exp z - (1 + z + z ^ 2 / 2))
  nlinarith only [hh, hle, pow_nonneg (abs_nonneg z) 3]

private theorem exists_uniform_projection_bound (mu : Measure ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ v s : ℝ, ∀ᵐ x ∂mu,
      |centeredNormalProjection q a v s x| ≤ K * (|v| + |s|) := by
  let g : ℝ → ℝ := fun x => |normalValue x - q| + |x - a|
  have hg : Continuous g := by dsimp [g, normalValue]; fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact
    (Set.Icc (-(4 + Real.sqrt 10)) (4 + Real.sqrt 10))).exists_bound_of_continuousOn
      hg.continuousOn
  let K : ℝ := |C| + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hCK : C ≤ K := by dsimp only [K]; linarith only [le_abs_self C]
  refine ⟨K, hK, ?_⟩
  intro v s
  filter_upwards [hb] with x hx
  have hsum : |normalValue x - q| + |x - a| ≤ C := by
    have hh : |g x| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC x (abs_le.mp hx)
    exact (le_abs_self (g x)).trans hh
  have hy : |normalValue x - q| ≤ K := by
    have hh := abs_nonneg (x - a)
    linarith only [hsum, hCK, hh]
  have hx' : |x - a| ≤ K := by
    have hh := abs_nonneg (normalValue x - q)
    linarith only [hsum, hCK, hh]
  unfold centeredNormalProjection
  calc
    |v * (normalValue x - q) + s * (x - a)| ≤
        |v * (normalValue x - q)| + |s * (x - a)| := abs_add_le _ _
    _ = |v| * |normalValue x - q| + |s| * |x - a| := by rw [abs_mul, abs_mul]
    _ ≤ |v| * K + |s| * K :=
      add_le_add (mul_le_mul_of_nonneg_left hy (abs_nonneg v))
        (mul_le_mul_of_nonneg_left hx' (abs_nonneg s))
    _ = K * (|v| + |s|) := by ring

theorem exists_centeredNormalLogMGF_cubic_upper (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ ∀ v s : ℝ, |v| + |s| ≤ delta →
      Integrable (fun x : ℝ => Real.exp (centeredNormalProjection q a v s x)) mu ∧
        0 < (∫ x : ℝ, Real.exp (centeredNormalProjection q a v s x) ∂mu) ∧
        centeredNormalLogMGF mu q a v s ≤
          normalTangentQuadratic mu v s / 2 + C * (|v| + |s|) ^ 3 := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_projection_bound mu hb q a
  refine ⟨K ^ 3, K⁻¹, by positivity, inv_pos.mpr hK, ?_⟩
  intro v s hsmall
  let f : ℝ → ℝ := centeredNormalProjection q a v s
  let R : ℝ := K ^ 3 * (|v| + |s|) ^ 3
  have hf : Continuous f := by
    dsimp only [f]
    unfold centeredNormalProjection normalValue
    fun_prop
  have hmem : MemLp f 2 mu := centeredNormalProjection_memLp_two mu hb q a v s
  have hfi : Integrable f mu := hmem.integrable (by norm_num)
  have hfsq : Integrable (fun x : ℝ => (f x) ^ 2) mu := hmem.integrable_sq
  have hE : Integrable (fun x : ℝ => Real.exp (f x)) mu :=
    integrable_continuous_of_fixed_bounds mu hb _ (Real.continuous_exp.comp hf)
  have hZ : 0 < (∫ x : ℝ, Real.exp (f x) ∂mu) := integral_exp_pos hE
  have hsmallf : ∀ᵐ x ∂mu, |f x| ≤ 1 := by
    filter_upwards [hbound v s] with x hx
    calc
      |f x| ≤ K * (|v| + |s|) := hx
      _ ≤ K * K⁻¹ := mul_le_mul_of_nonneg_left hsmall hK.le
      _ = 1 := mul_inv_cancel₀ hK.ne'
  have hpoint : ∀ᵐ x ∂mu, Real.exp (f x) ≤ 1 + f x + (f x) ^ 2 / 2 + R := by
    filter_upwards [hbound v s, hsmallf] with x hx hxs
    have hcubic : |f x| ^ 3 ≤ R := by
      calc
        |f x| ^ 3 ≤ (K * (|v| + |s|)) ^ 3 :=
          pow_le_pow_left₀ (abs_nonneg _) hx 3
        _ = R := by dsimp only [R]; rw [mul_pow]
    exact (real_exp_cubic_upper (f x) hxs).trans (add_le_add (le_refl _) hcubic)
  have hzero : (∫ x : ℝ, f x ∂mu) = 0 :=
    centeredNormalProjection_integral_zero mu hb q a hq ha v s
  have hquad : (∫ x : ℝ, (f x) ^ 2 ∂mu) = normalTangentQuadratic mu v s :=
    centeredNormalProjection_second_moment mu hb q a hq ha v s
  have hP1 : Integrable (fun x : ℝ => 1 + f x) mu := (integrable_const 1).add hfi
  have hP2 : Integrable (fun x : ℝ => 1 + f x + (f x) ^ 2 / 2) mu :=
    hP1.add (hfsq.div_const 2)
  have hP : Integrable (fun x : ℝ => 1 + f x + (f x) ^ 2 / 2 + R) mu :=
    hP2.add (integrable_const R)
  have hPint : (∫ x : ℝ, 1 + f x + (f x) ^ 2 / 2 + R ∂mu) =
      1 + normalTangentQuadratic mu v s / 2 + R := by
    rw [integral_add hP2 (integrable_const R), integral_add hP1 (hfsq.div_const 2),
      integral_add (integrable_const 1) hfi]
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const, hzero, hquad]
    simp [measureReal_def]
  have hZupper : (∫ x : ℝ, Real.exp (f x) ∂mu) ≤
      1 + normalTangentQuadratic mu v s / 2 + R :=
    (integral_mono_ae hE hP hpoint).trans_eq hPint
  refine ⟨hE, hZ, ?_⟩
  change Real.log (∫ x : ℝ, Real.exp (f x) ∂mu) ≤ normalTangentQuadratic mu v s / 2 + R
  exact (Real.log_le_sub_one_of_pos hZ).trans (by linarith only [hZupper])

end
end Shao.OQ3
