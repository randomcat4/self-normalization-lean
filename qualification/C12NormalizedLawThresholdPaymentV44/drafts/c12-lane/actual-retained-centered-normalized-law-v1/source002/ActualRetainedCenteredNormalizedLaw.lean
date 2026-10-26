import Shao.Probability.SourceTruncationBridge
import Shao.Probability.RetainedComparison

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
noncomputable section
namespace Shao.C2.ActualRetainedCenteredNormalizedLaw
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

theorem source_truncation_centered_normalized_law_data
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x) (hepsilon : 0 < epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : Shao.truncationBudget nu n x ≤ epsilon ^ 3 / 8) :
    let a : ℝ := 1 + x
    let rho : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ epsilon / a}
    let mu : ℝ := ∫ z : ℝ, z ∂rho
    let V : ℝ := ∫ z : ℝ, (z - mu) ^ 2 ∂rho
    let chi : Measure ℝ := Measure.map (fun z : ℝ => (z - mu) / Real.sqrt V) rho
    let R : ℝ := Shao.truncationBudget nu n x
    IsProbabilityMeasure chi ∧
      Integrable (fun z : ℝ => z) chi ∧
      Integrable (fun z : ℝ => z ^ 2) chi ∧
      Integrable (fun z : ℝ => |z| ^ 3) chi ∧
      (∫ z : ℝ, z ∂chi) = 0 ∧
      (∫ z : ℝ, z ^ 2 ∂chi) = 1 ∧
      (∀ᵐ z : ℝ ∂chi, |z| ≤ 2 * (epsilon / a) / Real.sqrt V) ∧
      0 < V ∧ (1 / 2 : ℝ) ≤ (n : ℝ) * V ∧ (n : ℝ) * V ≤ 4 / 3 ∧
      (∫ z : ℝ, |z| ^ 3 ∂chi) =
        (∫ z : ℝ, |z - mu| ^ 3 ∂rho) / (Real.sqrt V) ^ 3 ∧
      (∫ z : ℝ, |z| ^ 3 ∂chi) / Real.sqrt (n : ℝ) ≤ 64 * R / a ^ 3 := by
  intro a rho mu V chi R
  let b : ℝ := a / epsilon
  rcases Shao.sourceTruncation_sample_size nu n h2 hnorm x epsilon hx hepsilon
      hepsilonHalf hR with ⟨hb, hsize, _hn64, hcut⟩
  change 2 ≤ b at hb
  change b ^ 6 ≤ (n : ℝ) at hsize
  change (n : ℝ) * (∫ z : ℝ, Shao.truncationF (b * z) ∂nu) ≤ 1 / 8 at hcut
  have hLaw : Shao.retainedCutoffLaw nu b = rho :=
    (Shao.sourceTruncation_reparameterization nu n h2 x epsilon hx hepsilon
      (hepsilonHalf.trans (by norm_num))).2.2.1
  have hChiEq : chi = Shao.retainedStandardLaw nu b := by
    dsimp only [chi, Shao.retainedStandardLaw, Shao.retainedStandardize]
    simpa only [hLaw]
  have hMoments := Shao.retainedStandardLaw_moments nu n 0 b hb hsize
    (by norm_num) h2 hmean hnorm (hcut.trans (by norm_num))
  rw [← hChiEq] at hMoments
  rcases hMoments with
    ⟨hChi, hChiI1, hChiI2, hChiI3, hChiMean, hChiSecond, _hUnusedCoarseThird⟩
  rcases Shao.sourceTruncation_law_data nu n h2 hnorm x epsilon hx hepsilon
      hepsilonHalf hR with
    ⟨_hMassLower, _hMassUpper, hRho, hSupport, hId, _hSquare, _hThird, _hFourth⟩
  change IsProbabilityMeasure rho at hRho
  letI : IsProbabilityMeasure rho := hRho
  change (∀ᵐ z : ℝ ∂rho, |z| ≤ epsilon / a) at hSupport
  change Integrable (fun z : ℝ => z) rho at hId
  rcases Shao.sourceTruncation_variance_bounds nu n h2 hnorm hmean x epsilon hx
      hepsilon hepsilonHalf hR with
    ⟨_hSecondLower, _hSecondUpper, _hMeanSquare, _hVarianceFormula,
      hVarianceIntegral, hVpos, hVlower, hVupper⟩
  change ProbabilityTheory.variance (id : ℝ → ℝ) rho = V at hVarianceIntegral
  rw [hVarianceIntegral] at hVpos hVlower hVupper
  rcases Shao.sourceTruncation_paid_moments nu n h2 hnorm hmean x epsilon hx
      hepsilon hepsilonHalf hR with
    ⟨_hMeanPayment, hRawThirdPayment, _hFourthPayment, _hCenteredI3, hCenteredThird⟩
  let C : ℝ := ∫ z : ℝ, |z - mu| ^ 3 ∂rho
  let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
  change (n : ℝ) * m3 ≤ 2 * R / a ^ 3 at hRawThirdPayment
  change C ≤ 8 * m3 at hCenteredThird
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hSqrtV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hVpos
  have hMuBound : |mu| ≤ epsilon / a := by
    change |∫ z : ℝ, z ∂rho| ≤ epsilon / a
    calc
      |∫ z : ℝ, z ∂rho| ≤ ∫ z : ℝ, |z| ∂rho := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ := rho) (fun z : ℝ => z))
      _ ≤ ∫ _z : ℝ, epsilon / a ∂rho :=
        integral_mono_ae hId.abs (integrable_const _) hSupport
      _ = epsilon / a := by simp
  have hF : Measurable (fun z : ℝ => (z - mu) / Real.sqrt V) := by fun_prop
  have hChiSupport : ∀ᵐ z : ℝ ∂chi, |z| ≤ 2 * (epsilon / a) / Real.sqrt V := by
    change ∀ᵐ z : ℝ ∂Measure.map (fun z : ℝ => (z - mu) / Real.sqrt V) rho,
      |z| ≤ 2 * (epsilon / a) / Real.sqrt V
    rw [ae_map_iff hF.aemeasurable
      (measurableSet_le continuous_abs.measurable measurable_const)]
    filter_upwards [hSupport] with z hz
    rw [abs_div, abs_of_pos hSqrtV]
    have hTriangle : |z - mu| ≤ |z| + |mu| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le z mu
    apply div_le_div_of_nonneg_right _ hSqrtV.le
    linarith only [hTriangle, hz, hMuBound]
  have hCube : (∫ z : ℝ, |z| ^ 3 ∂chi) = C / (Real.sqrt V) ^ 3 := by
    change (∫ z : ℝ, |z| ^ 3 ∂Measure.map
      (fun z : ℝ => (z - mu) / Real.sqrt V) rho) = C / (Real.sqrt V) ^ 3
    rw [integral_map hF.aemeasurable (continuous_abs.pow 3).aestronglyMeasurable]
    simp_rw [abs_div, abs_of_pos hSqrtV, div_pow]
    rw [integral_div]
  have hMC : (n : ℝ) * C ≤ 16 * R / a ^ 3 := by
    calc
      (n : ℝ) * C ≤ (n : ℝ) * (8 * m3) :=
        mul_le_mul_of_nonneg_left hCenteredThird hnReal.le
      _ = 8 * ((n : ℝ) * m3) := by ring
      _ ≤ 8 * (2 * R / a ^ 3) :=
        mul_le_mul_of_nonneg_left hRawThirdPayment (by norm_num)
      _ = 16 * R / a ^ 3 := by ring
  have hCnonneg : 0 ≤ C := integral_nonneg (fun z => pow_nonneg (abs_nonneg (z - mu)) 3)
  have hPaymentNonneg : 0 ≤ 16 * R / a ^ 3 :=
    (mul_nonneg hnReal.le hCnonneg).trans hMC
  let sigma : ℝ := Real.sqrt V
  let s : ℝ := Real.sqrt ((n : ℝ) * V)
  have hsPos : 0 < s := Real.sqrt_pos.mpr (mul_pos hnReal hVpos)
  have hsSquare : s ^ 2 = (n : ℝ) * V := Real.sq_sqrt (mul_pos hnReal hVpos).le
  have hsHalf : (1 / 2 : ℝ) ≤ s := by
    apply Real.le_sqrt_of_sq_le
    linarith only [hVlower]
  have hsCube : (1 / 4 : ℝ) ≤ s ^ 3 := by
    calc
      (1 / 4 : ℝ) = (1 / 2) * (1 / 2) := by norm_num
      _ ≤ s * ((n : ℝ) * V) := mul_le_mul hsHalf hVlower (by norm_num) hsPos.le
      _ = s ^ 3 := by rw [← hsSquare]; ring
  have hsProduct : s = Real.sqrt (n : ℝ) * sigma :=
    Real.sqrt_mul hnReal.le V
  have hDen : s ^ 3 = (n : ℝ) * (Real.sqrt (n : ℝ) * sigma ^ 3) := by
    calc
      s ^ 3 = (Real.sqrt (n : ℝ)) ^ 2 * (Real.sqrt (n : ℝ) * sigma ^ 3) := by
        rw [hsProduct]
        ring
      _ = (n : ℝ) * (Real.sqrt (n : ℝ) * sigma ^ 3) := by
        rw [Real.sq_sqrt hnReal.le]
  have hDenPos : 0 < Real.sqrt (n : ℝ) * sigma ^ 3 :=
    mul_pos (Real.sqrt_pos.mpr hnReal) (pow_pos hSqrtV 3)
  have hRatio : C / sigma ^ 3 / Real.sqrt (n : ℝ) = (n : ℝ) * C / s ^ 3 := by
    rw [div_div, mul_comm (sigma ^ 3)]
    apply (div_eq_div_iff hDenPos.ne' (pow_pos hsPos 3).ne').mpr
    rw [hDen]
    ring
  refine ⟨hChi, hChiI1, hChiI2, hChiI3, hChiMean, hChiSecond,
    hChiSupport, hVpos, hVlower, hVupper, hCube, ?_⟩
  rw [hCube]
  change C / sigma ^ 3 / Real.sqrt (n : ℝ) ≤ 64 * R / a ^ 3
  rw [hRatio]
  apply (div_le_iff₀ (pow_pos hsPos 3)).mpr
  have hQuarter : (1 : ℝ) ≤ 4 * s ^ 3 := by linarith only [hsCube]
  calc
    (n : ℝ) * C ≤ 16 * R / a ^ 3 := hMC
    _ ≤ (16 * R / a ^ 3) * (4 * s ^ 3) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hQuarter hPaymentNonneg
    _ = (64 * R / a ^ 3) * s ^ 3 := by ring

end Shao.C2.ActualRetainedCenteredNormalizedLaw
