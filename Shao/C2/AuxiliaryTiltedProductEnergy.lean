import Shao.C2.AuxiliaryEnergyLaplace
import Shao.Probability.MeasurablePath
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.C2.AuxiliaryTiltedProductEnergy
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem auxiliary_tilted_product_low_energy
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (s q : ℝ) (hs : 0 ≤ s) (hq : 0 ≤ q) (hsq : s ≤ q)
    (hsmall : (s + q) * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 ≤ 1 / 64)
    (n : ℕ) :
    let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
    IsProbabilityMeasure P ∧
      Integrable (fun v : Shao.Path n => Real.exp (-q * Shao.energy v)) P ∧
      (∫ v : Shao.Path n, Real.exp (-q * Shao.energy v) ∂P) ≤
        Real.exp (-(3 / 4) * q * (n : ℝ)) ∧
      P.real {v : Shao.Path n | Shao.energy v ≤ (n : ℝ) / 8} ≤
        Real.exp (-(5 / 8) * q * (n : ℝ)) := by
  classical
  intro rho P
  have hRho : IsProbabilityMeasure rho :=
    (Shao.C2.AuxiliaryEnergyTilt.auxiliary_energy_tilt_normalizer_and_drift
      nu h2 h3 hmean hnorm s hs).2.2.2.2.1
  letI : IsProbabilityMeasure rho := hRho
  have hP : IsProbabilityMeasure P := inferInstance
  letI : IsProbabilityMeasure P := hP
  have hCoord := Shao.C2.AuxiliaryEnergyLaplace.auxiliary_tilted_energy_laplace
    nu h2 h3 hmean hnorm s q hs hq hsq hsmall
  have hInt : Integrable (fun v : Shao.Path n => Real.exp (-q * Shao.energy v)) P := by
    refine (integrable_const (1 : ℝ)).mono'
      (Real.continuous_exp.comp (continuous_const.mul Shao.continuous_energy)).aestronglyMeasurable ?_
    exact ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) (Shao.energy_nonneg v))
  have hProd (v : Shao.Path n) :
      Real.exp (-q * Shao.energy v) = ∏ i : Fin n, Real.exp (-q * (v i) ^ 2) := by
    rw [← Real.exp_sum]
    congr 1
    simp only [Shao.energy, Finset.mul_sum]
  have hMoment : (∫ v : Shao.Path n, Real.exp (-q * Shao.energy v) ∂P) ≤
      Real.exp (-(3 / 4) * q * (n : ℝ)) := by
    calc
      (∫ v : Shao.Path n, Real.exp (-q * Shao.energy v) ∂P) =
          ∏ _ : Fin n, ∫ z : ℝ, Real.exp (-q * z ^ 2) ∂rho := by
        simp_rw [hProd]
        exact integral_fintype_prod_eq_prod (fun _ : Fin n =>
          fun z : ℝ => Real.exp (-q * z ^ 2))
      _ ≤ ∏ _ : Fin n, Real.exp (-(3 / 4) * q) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact integral_nonneg (fun z => (Real.exp_pos _).le)
        · intro i hi
          exact hCoord.2
      _ = _ := by
        rw [← Real.exp_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        congr 1
        ring
  let A : Set (Shao.Path n) := {v | Shao.energy v ≤ (n : ℝ) / 8}
  have hA : MeasurableSet A := measurableSet_le Shao.measurable_energy measurable_const
  have hWeighted : Real.exp (-q * ((n : ℝ) / 8)) * P.real A ≤
      Real.exp (-(3 / 4) * q * (n : ℝ)) := by
    calc
      Real.exp (-q * ((n : ℝ) / 8)) * P.real A =
          ∫ v : Shao.Path n, A.indicator (fun _ => Real.exp (-q * ((n : ℝ) / 8))) v ∂P := by
        rw [integral_indicator_const _ hA, smul_eq_mul, mul_comm]
      _ ≤ ∫ v : Shao.Path n, Real.exp (-q * Shao.energy v) ∂P := by
        apply integral_mono ((integrable_const _).indicator hA) hInt
        intro v
        by_cases hv : v ∈ A
        · rw [Set.indicator_of_mem hv]
          apply Real.exp_le_exp.mpr
          change Shao.energy v ≤ (n : ℝ) / 8 at hv
          have hh := mul_nonneg hq (sub_nonneg.mpr hv)
          nlinarith
        · rw [Set.indicator_of_notMem hv]
          exact (Real.exp_pos _).le
      _ ≤ _ := hMoment
  have hTail : P.real A ≤ Real.exp (-(5 / 8) * q * (n : ℝ)) := by
    calc
      P.real A ≤ Real.exp (-(3 / 4) * q * (n : ℝ)) /
          Real.exp (-q * ((n : ℝ) / 8)) := by
        apply (le_div_iff₀ (Real.exp_pos _)).2
        simpa only [mul_comm] using hWeighted
      _ = _ := by
        rw [← Real.exp_sub]
        congr 1
        ring
  exact ⟨hP, hInt, hMoment, hTail⟩

theorem auxiliary_tilted_source_low_energy
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (s : ℝ) (hs : 0 ≤ s)
    (hsBound : s ≤ 1 / (128 * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2))
    (n : ℕ) :
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
    let q : ℝ := 1 / (128 * beta ^ 2)
    let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
    0 < q ∧ IsProbabilityMeasure P ∧
      P.real {v : Shao.Path n | Shao.energy v ≤ (n : ℝ) / 8} ≤
        Real.exp (-(5 * (n : ℝ) / (1024 * beta ^ 2))) := by
  intro beta q rho P
  have hBeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one nu h2 h3 hnorm
  have hBetaPos : 0 < beta := lt_of_lt_of_le zero_lt_one hBeta
  have hq : 0 < q := by dsimp [q]; positivity
  change s ≤ q at hsBound
  have hQ : q * beta ^ 2 = 1 / 128 := by
    dsimp [q]
    field_simp [ne_of_gt hBetaPos]
    <;> ring
  have hSmall : (s + q) * beta ^ 2 ≤ 1 / 64 := by
    have hh := mul_le_mul_of_nonneg_right hsBound (sq_nonneg beta)
    calc
      (s + q) * beta ^ 2 = s * beta ^ 2 + q * beta ^ 2 := by ring
      _ ≤ q * beta ^ 2 + q * beta ^ 2 := by linarith
      _ = 1 / 64 := by rw [hQ]; norm_num
  have hResult := auxiliary_tilted_product_low_energy nu h2 h3 hmean hnorm
    s q hs hq.le hsBound hSmall n
  refine ⟨hq, hResult.1, hResult.2.2.2.trans_eq ?_⟩
  congr 1
  dsimp [q]
  field_simp [ne_of_gt hBetaPos]
  <;> ring

end Shao.C2.AuxiliaryTiltedProductEnergy
