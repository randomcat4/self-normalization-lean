import Shao.OQ4.EnergyE1Bounds
import Shao.OQ4.EnergyLinearTiltComparisons
import Shao.OQ4.EnergyLinearTiltDerivatives

/-! An explicit common finite-parameter window for the actual centered-square integral. -/

namespace Shao.OQ4

open MeasureTheory

noncomputable def energyLinearVarianceA (M T : ℝ) : ℝ := energyE1Constant T * M

noncomputable def energyLinearVarianceB (M T K : ℝ) : ℝ :=
  Real.exp 2 * K * (energyLinearVarianceA M T + 6)

noncomputable def energyLinearVarianceC (M T K : ℝ) : ℝ :=
  energyLinearVarianceA M T + 5 * Real.exp 2 * K

noncomputable def energyLinearVarianceThreshold (M T K : ℝ) : ℝ :=
  energyLogThreshold M T +
    8 * (1 + energyLinearVarianceA M T + energyLinearVarianceB M T K + energyLinearVarianceC M T K + K)

theorem energyLinearVariance_constants_nonneg (M T K : ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T) (hK : 0 ≤ K) :
    0 ≤ energyLinearVarianceA M T ∧ 0 ≤ energyLinearVarianceB M T K ∧ 0 ≤ energyLinearVarianceC M T K := by
  have hP : 0 ≤ energyE1Constant T := le_trans (by norm_num) (energyE1Constant_dominates T hT).1
  unfold energyLinearVarianceB energyLinearVarianceC energyLinearVarianceA
  exact ⟨by positivity, by positivity, by positivity⟩

theorem energyLinearVariance_height_bounds (M T K h : ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hh : energyLinearVarianceThreshold M T K ≤ h) :
    energyLogThreshold M T ≤ h ∧ 2 ≤ h ∧ 8 * energyLinearVarianceA M T ≤ h ∧
      8 * energyLinearVarianceB M T K ≤ h ∧ 8 * energyLinearVarianceC M T K ≤ h ∧ 8 * K ≤ h := by
  obtain ⟨hA, hB, hC⟩ := energyLinearVariance_constants_nonneg M T K hM hT hK
  have h0 := (energyLog_threshold_bounds M T hM hT).1
  unfold energyLinearVarianceThreshold at hh
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- A weak-boundary payment, including X=0 and with division only by positive h. -/
theorem energyLinearVariance_fraction_bounds (X h : ℝ) (hX : 0 ≤ X) (hh : 1 ≤ h) (h8 : 8 * X ≤ h) :
    X / h ≤ (1 / 8 : ℝ) ∧ X / h ^ 2 ≤ (1 / 8 : ℝ) ∧ X / h ^ 2 ≤ (1 / 2 : ℝ) := by
  have hh0 : 0 < h := by linarith
  have h1 : X / h ≤ (1 / 8 : ℝ) := (div_le_iff₀ hh0).2 (by linarith)
  have h2 : X / h ^ 2 ≤ X / h := by
    apply (div_le_div_iff₀ (pow_pos hh0 2) hh0).2
    exact mul_le_mul_of_nonneg_left (by nlinarith : h ≤ h ^ 2) hX
  exact ⟨h1, h2.trans h1, le_trans (h2.trans h1) (by norm_num)⟩

theorem energyLinearVariance_exponential_bound (M T K h t : ℝ)
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hK : 0 ≤ K) (hh : energyLinearVarianceThreshold M T K ≤ h)
    (ht : |t| ≤ K / h ^ 2) : Real.exp (2 * h * |t|) ^ 2 ≤ Real.exp 2 := by
  obtain ⟨_h0, hh2, _hA, _hB, _hC, h8K⟩ := energyLinearVariance_height_bounds M T K h hM hT hK hh
  have hh0 : 0 < h := by linarith
  have hp := (le_div_iff₀ (pow_pos hh0 2)).1 ht
  have harg : 4 * h * |t| ≤ (1 / 2 : ℝ) := by
    by_contra hn
    have hm : 0 < h * (4 * h * |t| - (1 / 2 : ℝ)) := mul_pos hh0 (by linarith)
    nlinarith
  calc
    _ = Real.exp (4 * h * |t|) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)

section Admissible

variable (ν : Measure ℝ) [IsProbabilityMeasure ν] (M T K h s : ℝ)
  (hM : 0 ≤ M) (hT : 0 ≤ T) (hK : 0 ≤ K)
  (hh : energyLinearVarianceThreshold M T K ≤ h) (hs : |s| ≤ T)
  (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
  (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0)
  (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M)

include hM hT hK hh hs hSq hCube hsecond hmean hβM

/-- Actual E1 supplies both retained small errors and the coarse initial moment bounds. -/
theorem energyLinearVariance_initial_bounds :
    Integrable (fun x : ℝ => |x|) (energyTiltedLaw ν h s) ∧
    |(∫ x : ℝ, x ^ 2 ∂energyTiltedLaw ν h s) - 1| ≤ energyLinearVarianceA M T / h ∧
    |∫ x : ℝ, x ∂energyTiltedLaw ν h s| ≤ energyLinearVarianceA M T / h ^ 2 ∧
    (∫ x : ℝ, x ^ 2 ∂energyTiltedLaw ν h s) ≤ 2 ∧
    (∫ x : ℝ, |x| ∂energyTiltedLaw ν h s) ≤ 3 ∧
    |∫ x : ℝ, x ∂energyTiltedLaw ν h s| ≤ 1 ∧
    (∫ x : ℝ, |x| ^ 3 ∂energyTiltedLaw ν h s) ≤ energyLinearVarianceA M T := by
  obtain ⟨hh0, hh2, h8A, _h8B, _h8C, _h8K⟩ := energyLinearVariance_height_bounds M T K h hM hT hK hh
  have hE := energyE1_common_bounds ν M T h s hM hT hh0 hs hSq hCube hsecond hmean hβM
  rcases hE with ⟨hprob, hi, hq, _hc, _hsupport, _hh2, _hZ, _hlog, hm0, hq0, hr0⟩
  have : IsProbabilityMeasure (energyTiltedLaw ν h s) := hprob
  have hP : 0 ≤ energyE1Constant T := le_trans (by norm_num) (energyE1Constant_dominates T hT).1
  have hβ : energyE1Constant T * (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ energyLinearVarianceA M T :=
    mul_le_mul_of_nonneg_left hβM hP
  have hhpos : 0 < h := by linarith
  have hqErr := hq0.trans (div_le_div_of_nonneg_right hβ hhpos.le)
  have hmErr := hm0.trans (div_le_div_of_nonneg_right hβ (sq_nonneg h))
  have hfrac := energyLinearVariance_fraction_bounds (energyLinearVarianceA M T) h
    (energyLinearVariance_constants_nonneg M T K hM hT hK).1 (by linarith) h8A
  have hq2 : (∫ x : ℝ, x ^ 2 ∂energyTiltedLaw ν h s) ≤ 2 := by
    have ha := le_abs_self ((∫ x : ℝ, x ^ 2 ∂energyTiltedLaw ν h s) - 1)
    linarith [hfrac.1]
  have hu : (∫ x : ℝ, |x| ∂energyTiltedLaw ν h s) ≤ 1 + (∫ x : ℝ, x ^ 2 ∂energyTiltedLaw ν h s) := by
    calc
      _ ≤ ∫ x : ℝ, 1 + x ^ 2 ∂energyTiltedLaw ν h s := by
        apply integral_mono hi.abs ((integrable_const 1).add hq)
        intro x
        change |x| ≤ 1 + x ^ 2
        nlinarith [sq_nonneg (|x| - 1), sq_abs x]
      _ = _ := by
        rw [integral_add (integrable_const 1) hq, integral_const]
        simp only [probReal_univ, smul_eq_mul, one_mul]
  exact ⟨hi.abs, hqErr, hmErr, hq2, by linarith, hmErr.trans (le_trans hfrac.2.1 (by norm_num)), hr0.trans hβ⟩

/-- Actual normalized comparisons are paid by the fixed B and C and the common threshold. -/
theorem energyLinearVariance_moment_bounds (t : ℝ) (ht : |t| ≤ K / h ^ 2) :
    |(∫ x : ℝ, x ^ 2 ∂energyLinearTiltLaw ν h s t) - (∫ x : ℝ, x ^ 2 ∂energyTiltedLaw ν h s)| ≤
      energyLinearVarianceB M T K / h ^ 2 ∧
    |(∫ x : ℝ, x ^ 2 ∂energyLinearTiltLaw ν h s t) - 1| ≤
      energyLinearVarianceA M T / h + energyLinearVarianceB M T K / h ^ 2 ∧
    energyLinearVarianceA M T / h + energyLinearVarianceB M T K / h ^ 2 ≤ (1 / 4 : ℝ) ∧
    |energyLinearMean ν h s t| ≤ energyLinearVarianceC M T K / h ^ 2 ∧
    energyLinearVarianceC M T K / h ^ 2 ≤ (1 / 2 : ℝ) := by
  let q : ℝ := ∫ x : ℝ, x ^ 2 ∂energyTiltedLaw ν h s
  let u : ℝ := ∫ x : ℝ, |x| ∂energyTiltedLaw ν h s
  let r : ℝ := ∫ x : ℝ, |x| ^ 3 ∂energyTiltedLaw ν h s
  let m0 : ℝ := ∫ x : ℝ, x ∂energyTiltedLaw ν h s
  let qt : ℝ := ∫ x : ℝ, x ^ 2 ∂energyLinearTiltLaw ν h s t
  let mt : ℝ := energyLinearMean ν h s t
  obtain ⟨_huInt, hqErr, hmErr, hq, hu, hm, hr⟩ :=
    energyLinearVariance_initial_bounds ν M T K h s hM hT hK hh hs hSq hCube hsecond hmean hβM
  obtain ⟨_h0, hh2, h8A, h8B, h8C, _h8K⟩ := energyLinearVariance_height_bounds M T K h hM hT hK hh
  have hh1 : 1 ≤ h := by linarith
  have hcomp := energyLinear_normalized_comparisons ν T h s hT hh1 hs hSq hsecond t
  have hD := energyLinearVariance_exponential_bound M T K h t hM hT hK hh ht
  have hdt : Real.exp (2 * h * |t|) ^ 2 * |t| ≤ Real.exp 2 * (K / h ^ 2) :=
    mul_le_mul hD ht (abs_nonneg t) (Real.exp_nonneg _)
  have hq0 : 0 ≤ q := integral_nonneg fun _ => sq_nonneg _
  have hu0 : 0 ≤ u := integral_nonneg fun _ => abs_nonneg _
  have hr0 : 0 ≤ r := integral_nonneg fun _ => pow_nonneg (abs_nonneg _) 3
  have hpayQ : r + q * u ≤ energyLinearVarianceA M T + 6 := by
    nlinarith [mul_le_mul hq hu hu0 (by norm_num : (0 : ℝ) ≤ 2)]
  have hpayM : q + |m0| * u ≤ 5 := by
    nlinarith [mul_le_mul hm hu hu0 (by norm_num : (0 : ℝ) ≤ 1)]
  have hqChange : |qt - q| ≤ energyLinearVarianceB M T K / h ^ 2 := by
    calc
      _ ≤ Real.exp (2 * h * |t|) ^ 2 * |t| * (r + q * u) := hcomp.2.1
      _ ≤ (Real.exp 2 * (K / h ^ 2)) * (energyLinearVarianceA M T + 6) :=
        mul_le_mul hdt hpayQ (by positivity) (by positivity)
      _ = _ := by unfold energyLinearVarianceB; ring
  have hmeanChange : |mt - m0| ≤ 5 * Real.exp 2 * K / h ^ 2 := by
    calc
      _ ≤ Real.exp (2 * h * |t|) ^ 2 * |t| * (q + |m0| * u) := hcomp.1
      _ ≤ (Real.exp 2 * (K / h ^ 2)) * 5 := mul_le_mul hdt hpayM (by positivity) (by positivity)
      _ = _ := by ring
  have hqFinal : |qt - 1| ≤ energyLinearVarianceA M T / h + energyLinearVarianceB M T K / h ^ 2 := by
    calc
      _ = |(qt - q) + (q - 1)| := congrArg abs (by ring)
      _ ≤ |qt - q| + |q - 1| := abs_add_le _ _
      _ ≤ energyLinearVarianceB M T K / h ^ 2 + energyLinearVarianceA M T / h := add_le_add hqChange hqErr
      _ = _ := add_comm _ _
  have hmeanFinal : |mt| ≤ energyLinearVarianceC M T K / h ^ 2 := by
    calc
      _ = |(mt - m0) + m0| := congrArg abs (by ring)
      _ ≤ |mt - m0| + |m0| := abs_add_le _ _
      _ ≤ 5 * Real.exp 2 * K / h ^ 2 + energyLinearVarianceA M T / h ^ 2 := add_le_add hmeanChange hmErr
      _ = _ := by unfold energyLinearVarianceC; ring
  obtain ⟨hA0, hB0, hC0⟩ := energyLinearVariance_constants_nonneg M T K hM hT hK
  have hAf := energyLinearVariance_fraction_bounds _ h hA0 hh1 h8A
  have hBf := energyLinearVariance_fraction_bounds _ h hB0 hh1 h8B
  have hCf := energyLinearVariance_fraction_bounds _ h hC0 hh1 h8C
  exact ⟨hqChange, hqFinal, by linarith [hAf.1, hBf.2.1], hmeanFinal, hCf.2.2⟩

/-- Genuine centered-square integrability and the actual derivative on the common closed window. -/
theorem energyLinearVariance_window (t : ℝ) (ht : |t| ≤ K / h ^ 2) :
    IsProbabilityMeasure (energyLinearTiltLaw ν h s t) ∧
    Integrable (fun x : ℝ => x) (energyLinearTiltLaw ν h s t) ∧
    Integrable (fun x : ℝ => x ^ 2) (energyLinearTiltLaw ν h s t) ∧
    Integrable (fun x : ℝ => (x - energyLinearMean ν h s t) ^ 2) (energyLinearTiltLaw ν h s t) ∧
    (∫ x : ℝ, (x - energyLinearMean ν h s t) ^ 2 ∂energyLinearTiltLaw ν h s t) =
      (∫ x : ℝ, x ^ 2 ∂energyLinearTiltLaw ν h s t) - energyLinearMean ν h s t ^ 2 ∧
    ((1 / 2 : ℝ) ≤ (∫ x : ℝ, (x - energyLinearMean ν h s t) ^ 2 ∂energyLinearTiltLaw ν h s t) ∧
      (∫ x : ℝ, (x - energyLinearMean ν h s t) ^ 2 ∂energyLinearTiltLaw ν h s t) ≤ 2) ∧
    HasDerivAt (energyLinearMean ν h s)
      (∫ x : ℝ, (x - energyLinearMean ν h s t) ^ 2 ∂energyLinearTiltLaw ν h s t) t := by
  have hh2 := (energyLinearVariance_height_bounds M T K h hM hT hK hh).2.1
  have hh1 : 1 ≤ h := by linarith
  have hmom := energyLinearTiltLaw_moments ν T h s hT hh1 hs hSq hsecond t
  obtain ⟨hcenterInt, hcenterEq⟩ := energyLinear_centeredSquare_integral ν T h s hT hh1 hs hSq hsecond t
  rw [← hmom.2.2.2.2.2.1] at hcenterEq
  obtain ⟨_hChange, hQ, hQsmall, hMean, hMeanSmall⟩ :=
    energyLinearVariance_moment_bounds ν M T K h s hM hT hK hh hs hSq hCube hsecond hmean hβM t ht
  have hqFinal := hQ.trans hQsmall
  have hmFinal := hMean.trans hMeanSmall
  have hmsq : energyLinearMean ν h s t ^ 2 ≤ (1 / 4 : ℝ) := by
    have ha := abs_le.mp hmFinal
    nlinarith [sq_nonneg (energyLinearMean ν h s t - (1 / 2 : ℝ)),
      sq_nonneg (energyLinearMean ν h s t + (1 / 2 : ℝ))]
  have hqbounds := abs_le.mp hqFinal
  refine ⟨energyLinearTiltLaw_isProbabilityMeasure ν T h s hT hh1 hs hSq hsecond t,
    hmom.1, hmom.2.1, hcenterInt, hcenterEq, ⟨?_, ?_⟩,
    energyLinearMean_hasDerivAt_centeredSquare ν T h s hT hh1 hs hSq hsecond hCube t⟩
  · rw [hcenterEq]
    linarith
  · rw [hcenterEq]
    linarith [sq_nonneg (energyLinearMean ν h s t)]

end Admissible

end Shao.OQ4
