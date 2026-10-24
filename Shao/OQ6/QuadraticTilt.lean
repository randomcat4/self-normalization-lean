import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

universe u

namespace Shao.OQ6.QuadraticTilt

noncomputable section

open MeasureTheory ProbabilityTheory

private theorem qt_factor (t : ℝ) :
    Real.exp (t - t ^ 2 / 2) =
      Real.exp (1 / 2 : ℝ) * Real.exp (-((t - 1) ^ 2 / 2)) := by
  rw [← Real.exp_add]
  congr 1
  ring

private theorem qt_upper (t : ℝ) :
    Real.exp (t - t ^ 2 / 2) ≤ Real.exp (1 / 2 : ℝ) := by
  have he : Real.exp (-((t - 1) ^ 2 / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (t - 1)])
  rw [qt_factor]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left he (Real.exp_pos (1 / 2 : ℝ)).le

private theorem qt_hasDeriv (t : ℝ) :
    HasDerivAt (fun z : ℝ => Real.exp (z - z ^ 2 / 2))
      (Real.exp (t - t ^ 2 / 2) * (1 - t)) t := by
  have hp : HasDerivAt (fun z : ℝ => z - z ^ 2 / 2) (1 - t) t := by
    convert (hasDerivAt_id t).sub
      ((hasDerivAt_pow 2 t).const_mul (1 / 2 : ℝ)) using 1 <;>
      (try ext z) <;> (try dsimp only [Pi.sub_apply, Pi.pow_apply, id_eq]) <;>
      norm_num <;> ring
  exact hp.exp

private theorem qt_deriv_bound (t : ℝ) :
    |Real.exp (t - t ^ 2 / 2) * (1 - t)| ≤ Real.exp (1 / 2 : ℝ) := by
  let r : ℝ := |t - 1|
  have hr2 : r ^ 2 = (t - 1) ^ 2 := sq_abs (t - 1)
  have hr : r ≤ Real.exp (r ^ 2 / 2) := by
    have hi : r ≤ 1 + r ^ 2 / 2 := by nlinarith [sq_nonneg (r - 1)]
    linarith [Real.add_one_le_exp (r ^ 2 / 2)]
  have hprod : r * Real.exp (-(r ^ 2 / 2)) ≤ 1 := by
    calc
      r * Real.exp (-(r ^ 2 / 2)) ≤
          Real.exp (r ^ 2 / 2) * Real.exp (-(r ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have habs : |1 - t| = r := abs_sub_comm 1 t
  rw [abs_mul, abs_of_pos (Real.exp_pos _), habs, qt_factor]
  calc
    (Real.exp (1 / 2 : ℝ) * Real.exp (-((t - 1) ^ 2 / 2))) * r =
        Real.exp (1 / 2 : ℝ) * (r * Real.exp (-(r ^ 2 / 2))) := by
      rw [hr2]
      ring
    _ ≤ Real.exp (1 / 2 : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp (1 / 2 : ℝ) := mul_one _

private theorem qt_integrable_bdd
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ ω, |f ω| ≤ C) : Integrable f μ := by
  exact (integrable_const C).mono' hf.aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs] using Filter.Eventually.of_forall hC)

private theorem qt_square_shift
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (h1 : Integrable f μ)
    (h2 : Integrable (fun ω => f ω ^ 2) μ) (c : ℝ) :
    Integrable (fun ω => (f ω - c) ^ 2) μ ∧
      (∫ ω, (f ω - c) ^ 2 ∂μ) =
        (∫ ω, f ω ^ 2 ∂μ) - 2 * c * (∫ ω, f ω ∂μ) + c ^ 2 := by
  have hi : Integrable (fun ω => f ω ^ 2 - (2 * c) * f ω + c ^ 2) μ :=
    (h2.sub (h1.const_mul (2 * c))).add (integrable_const _)
  have he : (fun ω => (f ω - c) ^ 2) =
      (fun ω => f ω ^ 2 - (2 * c) * f ω + c ^ 2) := by
    funext ω
    ring
  refine ⟨by rw [he]; exact hi, ?_⟩
  have hadd := integral_add (f := fun ω => f ω ^ 2 - (2 * c) * f ω)
    (g := fun _ : Ω => c ^ 2) (h2.sub (h1.const_mul (2 * c)))
      (integrable_const (c ^ 2))
  have hsub := integral_sub (f := fun ω => f ω ^ 2)
    (g := fun ω => (2 * c) * f ω) h2 (h1.const_mul (2 * c))
  rw [he, hadd, hsub, integral_const_mul, integral_const,
    probReal_univ, one_smul]

theorem weight_bounds (u v : ℝ) :
    0 < Real.exp (u - u ^ 2 / 2) ∧
      Real.exp (u - u ^ 2 / 2) ≤ Real.exp (1 / 2 : ℝ) ∧
        |Real.exp (u - u ^ 2 / 2) - Real.exp (v - v ^ 2 / 2)| ≤
          Real.exp (1 / 2 : ℝ) * |u - v| := by
  refine ⟨Real.exp_pos _, qt_upper u, ?_⟩
  have hm :=
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun t _ => (qt_hasDeriv t).differentiableAt)
      (fun t _ => by
        rw [(qt_hasDeriv t).deriv, Real.norm_eq_abs]
        exact qt_deriv_bound t)
      (Set.mem_univ v) (Set.mem_univ u)
  simpa only [Real.norm_eq_abs] using hm

theorem normalizer_density_L2
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgsecond : (∫ ω, g ω ^ 2 ∂μ) = 1)
    (a : ℝ) (ha : |a| ≤ (2 * Real.exp (1 / 2 : ℝ))⁻¹) :
    let w : Ω → ℝ := fun ω => Real.exp (a * g ω - (a * g ω) ^ 2 / 2)
    let m : ℝ := ∫ ω, w ω ∂μ
    let L : Ω → ℝ := fun ω => w ω / m
    Integrable w μ ∧
      (1 / 2 : ℝ) ≤ m ∧ m ≤ (3 / 2 : ℝ) ∧
        Measurable L ∧ Integrable L μ ∧
          (∀ ω, 0 < L ω ∧ L ω ≤ 2 * Real.exp (1 / 2 : ℝ)) ∧
            (∫ ω, L ω ∂μ) = 1 ∧
              IsProbabilityMeasure (μ.tilted
                (fun ω => a * g ω - (a * g ω) ^ 2 / 2)) ∧
                Integrable (fun ω => (L ω - 1) ^ 2) μ ∧
                  (∫ ω, (L ω - 1) ^ 2 ∂μ) ≤
                    4 * (Real.exp (1 / 2 : ℝ)) ^ 2 * a ^ 2 := by
  dsimp only
  let C : ℝ := Real.exp (1 / 2 : ℝ)
  let w : Ω → ℝ := fun ω => Real.exp (a * g ω - (a * g ω) ^ 2 / 2)
  let m : ℝ := ∫ ω, w ω ∂μ
  let L : Ω → ℝ := fun ω => w ω / m
  have hC : 0 < C := Real.exp_pos _
  have hwmeas : Measurable w := by dsimp [w]; fun_prop
  have hwb (ω : Ω) : 0 < w ω ∧ w ω ≤ C :=
    ⟨Real.exp_pos _, (weight_bounds (a * g ω) 0).2.1⟩
  have hW : Integrable w μ :=
    qt_integrable_bdd μ w hwmeas C (fun ω => by
      rw [abs_of_pos (hwb ω).1]
      exact (hwb ω).2)
  have hW2 : Integrable (fun ω => w ω ^ 2) μ :=
    qt_integrable_bdd μ _ (by fun_prop) (C ^ 2) (fun ω => by
      rw [abs_of_nonneg (sq_nonneg (w ω))]
      exact pow_le_pow_left₀ (hwb ω).1.le (hwb ω).2 2)
  have herror := qt_square_shift μ w hW hW2 1
  have hcenter := qt_square_shift μ w hW hW2 m
  have hgSq : Integrable (fun ω => g ω ^ 2) μ := hg2.integrable_sq
  have hlin (ω : Ω) : |w ω - 1| ≤ C * |a| * |g ω| := by
    simpa [w, C, abs_mul, mul_assoc] using (weight_bounds (a * g ω) 0).2.2
  have hpoint (ω : Ω) : (w ω - 1) ^ 2 ≤ (C ^ 2 * a ^ 2) * g ω ^ 2 := by
    have hi := pow_le_pow_left₀ (abs_nonneg (w ω - 1)) (hlin ω) 2
    simpa only [mul_pow, sq_abs] using hi
  have herrBound : (∫ ω, (w ω - 1) ^ 2 ∂μ) ≤ C ^ 2 * a ^ 2 := by
    have hi := integral_mono_ae herror.1 (hgSq.const_mul (C ^ 2 * a ^ 2))
      (Filter.Eventually.of_forall hpoint)
    rw [integral_const_mul, hgsecond, mul_one] at hi
    exact hi
  have hcenterEq : (∫ ω, (w ω - m) ^ 2 ∂μ) =
      (∫ ω, (w ω - 1) ^ 2 ∂μ) - (m - 1) ^ 2 := by
    rw [hcenter.2, herror.2]
    change (∫ ω, w ω ^ 2 ∂μ) - 2 * m * m + m ^ 2 =
      ((∫ ω, w ω ^ 2 ∂μ) - 2 * 1 * m + 1 ^ 2) - (m - 1) ^ 2
    ring
  have hmdev : (m - 1) ^ 2 ≤ C ^ 2 * a ^ 2 := by
    have hi : 0 ≤ ∫ ω, (w ω - m) ^ 2 ∂μ :=
      integral_nonneg fun ω => sq_nonneg (w ω - m)
    rw [hcenterEq] at hi
    linarith only [hi, herrBound]
  have hca : C * |a| ≤ (1 / 2 : ℝ) := by
    calc
      C * |a| ≤ C * (2 * C)⁻¹ := mul_le_mul_of_nonneg_left ha hC.le
      _ = 1 / 2 := by
        change C / (2 * C) = 1 / 2
        apply (div_eq_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hC.ne')).2
        ring
  have hca2 : C ^ 2 * a ^ 2 ≤ (1 / 4 : ℝ) := by
    have hi := pow_le_pow_left₀ (mul_nonneg hC.le (abs_nonneg a)) hca 2
    norm_num only [mul_pow, sq_abs] at hi
    exact hi
  have hmabs : |m - 1| ≤ (1 / 2 : ℝ) := by
    have hi : (m - 1) ^ 2 ≤ (1 / 4 : ℝ) := hmdev.trans hca2
    nlinarith only [hi, abs_nonneg (m - 1), sq_abs (m - 1)]
  have hml : (1 / 2 : ℝ) ≤ m := by linarith [(abs_le.mp hmabs).1]
  have hmu : m ≤ (3 / 2 : ℝ) := by linarith [(abs_le.mp hmabs).2]
  have hmp : 0 < m := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hml
  have hLmeas : Measurable L := hwmeas.div_const m
  have hLint : Integrable L μ := hW.div_const m
  have hLb (ω : Ω) : 0 < L ω ∧ L ω ≤ 2 * C := by
    refine ⟨div_pos (hwb ω).1 hmp, ?_⟩
    calc
      L ω = w ω / m := rfl
      _ ≤ C / (1 / 2 : ℝ) :=
        div_le_div₀ hC.le (hwb ω).2 (by norm_num) hml
      _ = 2 * C := by ring
  have hLmean : (∫ ω, L ω ∂μ) = 1 := by
    change (∫ ω, w ω / m ∂μ) = 1
    rw [integral_div]
    change m / m = 1
    exact div_self hmp.ne'
  have hprob : IsProbabilityMeasure
      (μ.tilted (fun ω => a * g ω - (a * g ω) ^ 2 / 2)) :=
    isProbabilityMeasure_tilted hW
  have hquot₁ (ω : Ω) : L ω - 1 = (w ω - m) / m := by
    dsimp only [L]
    rw [← div_self hmp.ne', ← sub_div]
  have hquot : (fun ω => (L ω - 1) ^ 2) =
      (fun ω => (w ω - m) ^ 2 / m ^ 2) := by
    funext ω
    rw [hquot₁ ω, div_pow]
  have hL2int : Integrable (fun ω => (L ω - 1) ^ 2) μ := by
    rw [hquot]
    exact hcenter.1.div_const (m ^ 2)
  have hL2val : (∫ ω, (L ω - 1) ^ 2 ∂μ) =
      (∫ ω, (w ω - m) ^ 2 ∂μ) / m ^ 2 := by
    rw [hquot, integral_div]
  have hcenterBound : (∫ ω, (w ω - m) ^ 2 ∂μ) ≤ C ^ 2 * a ^ 2 := by
    rw [hcenterEq]
    nlinarith only [herrBound, sq_nonneg (m - 1)]
  have hm2 : (1 / 4 : ℝ) ≤ m ^ 2 := by
    have hi := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hml 2
    norm_num at hi
    exact hi
  have hL2bound : (∫ ω, (L ω - 1) ^ 2 ∂μ) ≤ 4 * C ^ 2 * a ^ 2 := by
    calc
      (∫ ω, (L ω - 1) ^ 2 ∂μ) = (∫ ω, (w ω - m) ^ 2 ∂μ) / m ^ 2 := hL2val
      _ ≤ (C ^ 2 * a ^ 2) / (1 / 4 : ℝ) :=
        div_le_div₀ (by positivity) hcenterBound (by norm_num) hm2
      _ = 4 * C ^ 2 * a ^ 2 := by ring
  exact ⟨hW, hml, hmu, hLmeas, hLint, hLb, hLmean, hprob, hL2int, hL2bound⟩

end

end Shao.OQ6.QuadraticTilt
