import Shao.Probability.TruncationIntegrals
import Shao.Probability.MeasurablePath
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The actual normalized energy lower tail

This is the original-law Chernoff subestimate at main.tex 1258–1261.
The energy is the full square sum. The weak event includes its equality
atoms, including zero-energy atoms when `kappa = 1`.

Only second and absolute third integrability and the actual normalization
are used. This auxiliary bound does not close the full C2 comparison.
-/

set_option autoImplicit false

namespace Shao.Probability
open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem exp_neg_sq_le_cubic (u : ℝ) (hu : 0 ≤ u) :
    Real.exp (-(u ^ 2)) ≤ 1 - u ^ 2 + u ^ 3 := by
  have hd : 0 < 1 + u ^ 2 := by positivity
  have he : 1 + u ^ 2 ≤ Real.exp (u ^ 2) := by
    linarith [Real.add_one_le_exp (u ^ 2)]
  calc
    Real.exp (-(u ^ 2)) = 1 / Real.exp (u ^ 2) := by
      rw [Real.exp_neg, one_div]
    _ ≤ 1 / (1 + u ^ 2) := one_div_le_one_div_of_le hd he
    _ ≤ 1 - u ^ 2 + u ^ 3 := by
      apply (div_le_iff₀ hd).2
      have hq : 0 ≤ u ^ 2 - u + 1 := by nlinarith [sq_nonneg (u - 1 / 2)]
      nlinarith [mul_nonneg (pow_nonneg hu 3) hq]

private theorem coordinate_energy_laplace_integrable
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun z : ℝ => Real.exp (-s * z ^ 2)) nu := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  exact ae_of_all nu fun z => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z])

private theorem energy_laplace_integrable
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun v : Shao.Path n => Real.exp (-s * Shao.energy v))
      (Measure.pi (fun _ : Fin n => nu)) := by
  refine (integrable_const (1 : ℝ)).mono' ?_ ?_
  · exact (Real.continuous_exp.comp
      (continuous_const.mul Shao.continuous_energy)).aestronglyMeasurable
  · exact ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith [Shao.energy_nonneg v])

private theorem coordinate_energy_laplace_bound
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (s : ℝ) (hs : 0 ≤ s) :
    (∫ z : ℝ, Real.exp (-s * z ^ 2) ∂nu) ≤
      Real.exp (-s * (∫ z : ℝ, z ^ 2 ∂nu) +
        (Real.sqrt s) ^ 3 * (∫ z : ℝ, |z| ^ 3 ∂nu)) := by
  have hp (z : ℝ) : Real.exp (-s * z ^ 2) ≤
      1 - s * z ^ 2 + (Real.sqrt s) ^ 3 * |z| ^ 3 := by
    have h := exp_neg_sq_le_cubic (Real.sqrt s * |z|)
      (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    simpa only [mul_pow, Real.sq_sqrt hs, sq_abs, neg_mul] using h
  have hi : Integrable (fun z : ℝ =>
      1 - s * z ^ 2 + (Real.sqrt s) ^ 3 * |z| ^ 3) nu :=
    ((integrable_const (1 : ℝ)).sub (h2.const_mul s)).add
      (h3.const_mul ((Real.sqrt s) ^ 3))
  calc
    (∫ z : ℝ, Real.exp (-s * z ^ 2) ∂nu) ≤
        ∫ z : ℝ, 1 - s * z ^ 2 + (Real.sqrt s) ^ 3 * |z| ^ 3 ∂nu :=
      integral_mono (coordinate_energy_laplace_integrable nu s hs) hi hp
    _ = 1 + (-s * (∫ z : ℝ, z ^ 2 ∂nu) +
        (Real.sqrt s) ^ 3 * (∫ z : ℝ, |z| ^ 3 ∂nu)) := by
      rw [integral_add (f := fun z : ℝ => 1 - s * z ^ 2)
        (g := fun z : ℝ => (Real.sqrt s) ^ 3 * |z| ^ 3)
        ((integrable_const (1 : ℝ)).sub (h2.const_mul s))
        (h3.const_mul ((Real.sqrt s) ^ 3)),
        integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun z : ℝ => s * z ^ 2)
          (integrable_const (1 : ℝ)) (h2.const_mul s)]
      simp only [integral_const, probReal_univ, one_smul, integral_const_mul]
      ring
    _ ≤ _ := by
      have he := Real.add_one_le_exp (-s * (∫ z : ℝ, z ^ 2 ∂nu) +
        (Real.sqrt s) ^ 3 * (∫ z : ℝ, |z| ^ 3 ∂nu))
      linarith

private theorem normalized_third_moment_pos
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1) :
    0 < (n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂nu) := by
  apply mul_pos (Nat.cast_pos.mpr hn)
  have hm : 0 ≤ ∫ z : ℝ, |z| ^ 3 ∂nu :=
    integral_nonneg fun z => pow_nonneg (abs_nonneg z) 3
  by_contra hpos
  have hz : (∫ z : ℝ, |z| ^ 3 ∂nu) = 0 :=
    le_antisymm (le_of_not_gt hpos) hm
  have hae : (fun z : ℝ => |z| ^ 3) =ᵐ[nu] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (ae_of_all nu fun z => pow_nonneg (abs_nonneg z) 3) h3).mp hz
  have hsq : (fun z : ℝ => z ^ 2) =ᵐ[nu] 0 := hae.mono fun z hz => by
    have hz0 : |z| = 0 := (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hz
    have hzz : z = 0 := abs_eq_zero.mp hz0
    simp [hzz]
  have hz2 : (∫ z : ℝ, z ^ 2 ∂nu) = 0 := by
    calc
      _ = ∫ _ : ℝ, (0 : ℝ) ∂nu := integral_congr_ae hsq
      _ = 0 := integral_zero _ _
  rw [hz2, mul_zero] at hnorm
  norm_num at hnorm

theorem finite_iid_energy_laplace_bound
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (s : ℝ) (hs : 0 ≤ s) :
    let beta : ℝ := (n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂nu)
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    Integrable (fun v : Shao.Path n => Real.exp (-s * Shao.energy v)) P ∧
      (∫ v : Shao.Path n, Real.exp (-s * Shao.energy v) ∂P) ≤
        Real.exp (-s + (Real.sqrt s) ^ 3 * beta) := by
  dsimp only
  refine ⟨energy_laplace_integrable nu n s hs, ?_⟩
  have hprod (v : Shao.Path n) :
      Real.exp (-s * Shao.energy v) = ∏ i : Fin n, Real.exp (-s * (v i) ^ 2) := by
    rw [← Real.exp_sum]
    congr 1
    simp only [Shao.energy, Finset.mul_sum]
  calc
    (∫ v : Shao.Path n, Real.exp (-s * Shao.energy v)
        ∂Measure.pi (fun _ : Fin n => nu)) =
        ∏ _ : Fin n, ∫ z : ℝ, Real.exp (-s * z ^ 2) ∂nu := by
      simp_rw [hprod]
      exact integral_fintype_prod_eq_prod (fun _ : Fin n => fun z : ℝ => Real.exp (-s * z ^ 2))
    _ ≤ ∏ _ : Fin n, Real.exp (-s * (∫ z : ℝ, z ^ 2 ∂nu) +
        (Real.sqrt s) ^ 3 * (∫ z : ℝ, |z| ^ 3 ∂nu)) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact integral_nonneg fun z => (Real.exp_pos _).le
      · intro i hi
        exact coordinate_energy_laplace_bound nu h2 h3 s hs
    _ = Real.exp ((n : ℝ) * (-s * (∫ z : ℝ, z ^ 2 ∂nu) +
        (Real.sqrt s) ^ 3 * (∫ z : ℝ, |z| ^ 3 ∂nu))) := by
      rw [← Real.exp_sum]
      simp
      ring
    _ = _ := by
      congr 1
      calc
        (n : ℝ) * (-s * (∫ z : ℝ, z ^ 2 ∂nu) +
            (Real.sqrt s) ^ 3 * (∫ z : ℝ, |z| ^ 3 ∂nu)) =
            -s * ((n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu)) +
              (Real.sqrt s) ^ 3 * ((n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂nu)) := by ring
        _ = _ := by rw [hnorm]; ring

theorem finite_iid_energy_lower_tail
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (kappa : ℝ) (hkappa : 0 < kappa) (hkappa1 : kappa ≤ 1) :
    let beta : ℝ := (n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂nu)
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    0 < beta ∧
      P.real {v : Shao.Path n | Shao.energy v ≤ 1 - kappa} ≤
        Real.exp (-(kappa ^ 3 / (8 * beta ^ 2))) := by
  dsimp only
  let beta : ℝ := (n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂nu)
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  change 0 < beta ∧ P.real {v : Shao.Path n | Shao.energy v ≤ 1 - kappa} ≤
    Real.exp (-(kappa ^ 3 / (8 * beta ^ 2)))
  have hb : 0 < beta := normalized_third_moment_pos nu n hn h2 h3 hnorm
  refine ⟨hb, ?_⟩
  let a : ℝ := kappa / (2 * beta)
  have ha : 0 < a := div_pos hkappa (mul_pos (by norm_num) hb)
  have hsqrt : Real.sqrt (a ^ 2) = a := Real.sqrt_sq ha.le
  have hlap := finite_iid_energy_laplace_bound nu n hn h2 h3 hnorm
    (a ^ 2) (sq_nonneg a)
  change Integrable (fun v : Shao.Path n => Real.exp (-(a ^ 2) * Shao.energy v)) P ∧
    (∫ v : Shao.Path n, Real.exp (-(a ^ 2) * Shao.energy v) ∂P) ≤
      Real.exp (-(a ^ 2) + (Real.sqrt (a ^ 2)) ^ 3 * beta) at hlap
  have hA : MeasurableSet {v : Shao.Path n | Shao.energy v ≤ 1 - kappa} :=
    measurableSet_le Shao.measurable_energy measurable_const
  have hprob : Real.exp (-(a ^ 2) * (1 - kappa)) *
      P.real {v : Shao.Path n | Shao.energy v ≤ 1 - kappa} ≤
      Real.exp (-(a ^ 2) + (Real.sqrt (a ^ 2)) ^ 3 * beta) := by
    calc
      _ = ∫ v : Shao.Path n,
          {v : Shao.Path n | Shao.energy v ≤ 1 - kappa}.indicator
            (fun _ => Real.exp (-(a ^ 2) * (1 - kappa))) v ∂P := by
        rw [integral_indicator_const _ hA, smul_eq_mul, mul_comm]
      _ ≤ ∫ v : Shao.Path n, Real.exp (-(a ^ 2) * Shao.energy v) ∂P := by
        apply integral_mono ((integrable_const _).indicator hA) hlap.1
        intro v
        by_cases hv : Shao.energy v ≤ 1 - kappa
        · rw [Set.indicator_of_mem hv]
          apply Real.exp_le_exp.mpr
          nlinarith [sq_nonneg a]
        · rw [Set.indicator_of_notMem hv]
          exact (Real.exp_pos _).le
      _ ≤ _ := hlap.2
  calc
    P.real {v : Shao.Path n | Shao.energy v ≤ 1 - kappa} ≤
        Real.exp (-(a ^ 2) + (Real.sqrt (a ^ 2)) ^ 3 * beta) /
          Real.exp (-(a ^ 2) * (1 - kappa)) := by
      apply (le_div_iff₀ (Real.exp_pos _)).mpr
      simpa only [mul_comm] using hprob
    _ = Real.exp (-(kappa ^ 3 / (8 * beta ^ 2))) := by
      rw [← Real.exp_sub, hsqrt]
      congr 1
      dsimp [a]
      field_simp
      <;> ring

end Shao.Probability
