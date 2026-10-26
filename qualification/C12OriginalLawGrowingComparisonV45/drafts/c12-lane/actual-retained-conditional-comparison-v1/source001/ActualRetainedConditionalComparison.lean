import Shao.C2.ActualRetainedCenteredNormalizedLaw
import Shao.C2.CenteredConditionalComparison

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace Shao.C2.ActualRetainedConditionalComparison
open MeasureTheory ProbabilityTheory Set
open Shao.C2.BridgeDomination
open scoped BigOperators NNReal Topology Classical

theorem source_truncation_actual_retained_double_comparison :
    ∃ epsilon eta C : ℝ, 0 < epsilon ∧ epsilon ≤ 1 / 800 ∧ 0 < eta ∧ 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
        IsBrownianReal Bm PB →
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
          (n : ℕ) (hn : 0 < n)
          (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
          (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
          (hmean : (∫ z : ℝ, z ∂nu) = 0)
          (x : ℝ), 1 ≤ x → Shao.truncationBudget nu n x ≤ eta →
          let rho : Measure ℝ :=
            ProbabilityTheory.cond nu {z | |z| ≤ epsilon / (1 + x)}
          IsProbabilityMeasure rho ∧
            |(Measure.pi (fun _ : Fin n => rho)).real (Shao.C2.doubleCrossing hn x) -
                PB.real {omega |
                  (∃ s : BridgeTime, x ≤ Bm ⟨(s : ℝ), s.property.1⟩ omega) ∧
                  ∃ s : BridgeTime, Bm ⟨(s : ℝ), s.property.1⟩ omega ≤ -x}| ≤
              C * Shao.truncationBudget nu n x * Shao.standardNormalTail x := by
  obtain ⟨etaG, epsilonG, Cg, hetaG, hepsilonG, hCg, hCompare⟩ :=
    Shao.C2.CenteredConditionalComparison.iid_centered_scaled_law_double_comparison
  let epsilon : ℝ := min (1 / 800) (etaG / 4)
  let eta : ℝ := min (epsilon ^ 3 / 8) (min (epsilon ^ 2 / 12) (epsilonG / 64))
  have hepsilon : 0 < epsilon := lt_min (by norm_num) (div_pos hetaG (by norm_num))
  have hepsilonCap : epsilon ≤ 1 / 800 := min_le_left _ _
  have hepsilonHalf : epsilon ≤ 1 / 2 := hepsilonCap.trans (by norm_num)
  have hepsilonEta : 4 * epsilon ≤ etaG := by
    have hh : epsilon ≤ etaG / 4 := min_le_right _ _
    linarith only [hh]
  have heta : 0 < eta :=
    lt_min (div_pos (pow_pos hepsilon 3) (by norm_num))
      (lt_min (div_pos (pow_pos hepsilon 2) (by norm_num))
        (div_pos hepsilonG (by norm_num)))
  refine ⟨epsilon, eta, Cg * (64 + 6 / epsilon ^ 2),
    hepsilon, hepsilonCap, heta, by positivity, ?_⟩
  intro ΩB _ Bm PB _ hBrownian nu _ n hn h2 hnorm hmean x hx hR rho
  let a : ℝ := 1 + x
  let R : ℝ := Shao.truncationBudget nu n x
  have hx0 : 0 ≤ x := by linarith only [hx]
  have ha : 0 < a := by dsimp only [a]; linarith only [hx]
  have ha1 : 1 ≤ a := by dsimp only [a]; linarith only [hx]
  have hR0 : 0 ≤ R := Shao.truncationBudget_nonneg nu n h2 x
  have hRcut : R ≤ epsilon ^ 3 / 8 := hR.trans (min_le_left _ _)
  have hRmean : R ≤ epsilon ^ 2 / 12 :=
    hR.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRcompare : R ≤ epsilonG / 64 :=
    hR.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLaw := Shao.sourceTruncation_law_data nu n h2 hnorm x epsilon hx0
    hepsilon hepsilonHalf hRcut
  have hRho : IsProbabilityMeasure rho := hLaw.2.2.1
  letI : IsProbabilityMeasure rho := hRho
  let mu : ℝ := ∫ z : ℝ, z ∂rho
  let V : ℝ := ∫ z : ℝ, (z - mu) ^ 2 ∂rho
  let chi : Measure ℝ := Measure.map (fun z : ℝ => (z - mu) / Real.sqrt V) rho
  let delta : ℝ := (∫ z : ℝ, |z| ^ 3 ∂chi) / Real.sqrt (n : ℝ)
  let h : ℝ := 3 * ((n : ℝ) * |mu|)
  rcases
    Shao.C2.ActualRetainedCenteredNormalizedLaw.source_truncation_centered_normalized_law_data
      nu n hn h2 hnorm hmean x epsilon hx0 hepsilon hepsilonHalf hRcut with
    ⟨hChi, _hChi1, hChi2, hChi3, hChiMean, hChiSecond,
      hChiSupport, hVpos, hVlower, _hVupper, _hThirdIdentity, hDelta⟩
  change IsProbabilityMeasure chi at hChi
  letI : IsProbabilityMeasure chi := hChi
  change Integrable (fun z : ℝ => z ^ 2) chi at hChi2
  change Integrable (fun z : ℝ => |z| ^ 3) chi at hChi3
  change (∫ z : ℝ, z ∂chi) = 0 at hChiMean
  change (∫ z : ℝ, z ^ 2 ∂chi) = 1 at hChiSecond
  change (∀ᵐ z : ℝ ∂chi, |z| ≤ 2 * (epsilon / a) / Real.sqrt V) at hChiSupport
  change 0 < V at hVpos
  change (1 / 2 : ℝ) ≤ (n : ℝ) * V at hVlower
  change delta ≤ 64 * R / a ^ 3 at hDelta
  have hDeltaBudget : delta * a ^ 3 ≤ 64 * R :=
    (le_div_iff₀ (pow_pos ha 3)).mp hDelta
  have hSmall : delta * a ^ 3 ≤ epsilonG := by
    linarith only [hDeltaBudget, hRcompare]
  have hMean := (Shao.sourceTruncation_paid_moments nu n h2 hnorm hmean x epsilon
    hx0 hepsilon hepsilonHalf hRcut).1
  change (n : ℝ) * |mu| ≤ 2 * R / (epsilon ^ 2 * a) at hMean
  have hMeanScaled := (le_div_iff₀ (mul_pos (pow_pos hepsilon 2) ha)).mp hMean
  have hShiftBudget : a * h ≤ 6 * R / epsilon ^ 2 := by
    apply (le_div_iff₀ (pow_pos hepsilon 2)).mpr
    calc
      a * h * epsilon ^ 2 = 3 * (((n : ℝ) * |mu|) * (epsilon ^ 2 * a)) := by
        dsimp only [h]
        ring
      _ ≤ 3 * (2 * R) := mul_le_mul_of_nonneg_left hMeanScaled (by norm_num)
      _ = 6 * R := by ring
  have hShiftHalf : a * h ≤ 1 / 2 := by
    apply hShiftBudget.trans
    apply (div_le_iff₀ (pow_pos hepsilon 2)).mpr
    nlinarith only [hRmean]
  have hh : 0 ≤ h := by dsimp only [h]; positivity
  have hHalf : h ≤ 1 / 2 := by
    calc
      h = 1 * h := by ring
      _ ≤ a * h := mul_le_mul_of_nonneg_right ha1 hh
      _ ≤ 1 / 2 := hShiftHalf
  have hShift : (1 + x) * h ≤ 1 := by
    change a * h ≤ 1
    linarith only [hShiftHalf]
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnReal
  have hSV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hVpos
  have hProductSquare : (Real.sqrt (n : ℝ) * Real.sqrt V) ^ 2 = (n : ℝ) * V := by
    rw [mul_pow, Real.sq_sqrt hnReal.le, Real.sq_sqrt hVpos.le]
  have hProductNonneg : 0 ≤ Real.sqrt (n : ℝ) * Real.sqrt V :=
    mul_nonneg hsn.le hSV.le
  have hProductLower : (1 / 2 : ℝ) ≤ Real.sqrt (n : ℝ) * Real.sqrt V := by
    nlinarith only [hProductSquare, hVlower, hProductNonneg]
  have hCap : 2 * (epsilon / a) / Real.sqrt V ≤
      4 * epsilon * Real.sqrt (n : ℝ) / a := by
    apply (div_le_iff₀ hSV).mpr
    calc
      2 * (epsilon / a) = (4 * (epsilon / a)) * (1 / 2 : ℝ) := by ring
      _ ≤ (4 * (epsilon / a)) * (Real.sqrt (n : ℝ) * Real.sqrt V) :=
        mul_le_mul_of_nonneg_left hProductLower (by positivity)
      _ = (4 * epsilon * Real.sqrt (n : ℝ) / a) * Real.sqrt V := by ring
  have hxPlus : 0 < x + h := by linarith only [hx, hh]
  have hxPlusA : x + h ≤ a := by dsimp only [a]; linarith only [hHalf]
  have hCapEta : 4 * epsilon * Real.sqrt (n : ℝ) / a ≤
      etaG * Real.sqrt (n : ℝ) / (x + h) := by
    calc
      4 * epsilon * Real.sqrt (n : ℝ) / a ≤ etaG * Real.sqrt (n : ℝ) / a :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hepsilonEta hsn.le) ha.le
      _ ≤ etaG * Real.sqrt (n : ℝ) / (x + h) :=
        div_le_div_of_nonneg_left (mul_nonneg hetaG.le hsn.le) hxPlus hxPlusA
  have hSupport : ∀ᵐ z : ℝ ∂chi,
      |z| ≤ etaG * Real.sqrt (n : ℝ) / (x + h) := by
    filter_upwards [hChiSupport] with z hz
    exact hz.trans (hCap.trans hCapEta)
  let b : ℝ := a / epsilon
  rcases Shao.sourceTruncation_sample_size nu n h2 hnorm x epsilon hx0 hepsilon
      hepsilonHalf hRcut with ⟨hb, hsize, _hn64, _hcut⟩
  change 2 ≤ b at hb
  change b ^ 6 ≤ (n : ℝ) at hsize
  have hbpos : 0 < b := by linarith only [hb]
  have hbSquare : 1 ≤ b ^ 2 := by
    nlinarith only [hb, sq_nonneg (b - 1)]
  have hbCube : b ≤ b ^ 3 := by
    calc
      b = b * 1 := by ring
      _ ≤ b * b ^ 2 := mul_le_mul_of_nonneg_left hbSquare hbpos.le
      _ = b ^ 3 := by ring
  have hbRoot : b ^ 3 ≤ Real.sqrt (n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    calc
      (b ^ 3) ^ 2 = b ^ 6 := by ring
      _ ≤ (n : ℝ) := hsize
  have hTwoX : 2 * x ≤ b := by
    change 2 * x ≤ a / epsilon
    apply (le_div_iff₀ hepsilon).mpr
    calc
      2 * x * epsilon ≤ 2 * x * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hepsilonHalf (by positivity)
      _ ≤ a := by dsimp only [a]; linarith only [hx]
  have hxScale : x / Real.sqrt (n : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hsn).mpr
    have hhx : 2 * x ≤ Real.sqrt (n : ℝ) := hTwoX.trans (hbCube.trans hbRoot)
    linarith only [hhx]
  have hNormScale : (1 / 2 : ℝ) ≤ (n : ℝ) * Real.sqrt V ^ 2 := by
    simpa only [Real.sq_sqrt hVpos.le] using hVlower
  have hResult := hCompare Bm PB hBrownian rho n hn mu (Real.sqrt V) x hSV hx
    hxScale hChi2 hChi3 hChiMean hChiSecond hSupport hNormScale hHalf hShift hSmall
  change |(Measure.pi (fun _ : Fin n => rho)).real (Shao.C2.doubleCrossing hn x) -
      PB.real {omega |
        (∃ s : BridgeTime, x ≤ Bm ⟨(s : ℝ), s.property.1⟩ omega) ∧
          ∃ s : BridgeTime, Bm ⟨(s : ℝ), s.property.1⟩ omega ≤ -x}| ≤
        Cg * (delta * a ^ 3 + a * h) * Shao.standardNormalTail x at hResult
  have hBudget : delta * a ^ 3 + a * h ≤ (64 + 6 / epsilon ^ 2) * R := by
    calc
      delta * a ^ 3 + a * h ≤ 64 * R + 6 * R / epsilon ^ 2 :=
        add_le_add hDeltaBudget hShiftBudget
      _ = (64 + 6 / epsilon ^ 2) * R := by ring
  have hPsi : 0 ≤ Shao.standardNormalTail x :=
    (Shao.standardNormalTail_basic.2.2.1 x).1.le
  refine ⟨hRho, hResult.trans ?_⟩
  change Cg * (delta * a ^ 3 + a * h) * Shao.standardNormalTail x ≤
    (Cg * (64 + 6 / epsilon ^ 2)) * R * Shao.standardNormalTail x
  calc
    Cg * (delta * a ^ 3 + a * h) * Shao.standardNormalTail x ≤
        Cg * ((64 + 6 / epsilon ^ 2) * R) * Shao.standardNormalTail x :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBudget hCg.le) hPsi
    _ = (Cg * (64 + 6 / epsilon ^ 2)) * R * Shao.standardNormalTail x := by ring

end Shao.C2.ActualRetainedConditionalComparison
