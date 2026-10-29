import Shao.OQ6.UniformPMomentPhysicalFiniteCostTail
import Shao.OQ6.OriginalEnvelopeRhoBound
import Shao.OQ6.OriginalExceptionalTailAbsorption
import Shao.OQ6.IIDSourceStrictMomentBudgets

set_option autoImplicit false
universe u
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology MeasureTheory symmDiff ENNReal
open Shao.OQ5.P51
namespace Shao.OQ6.UniformPMomentSingleWindowPhysicalRelativePolynomialRate
noncomputable section

theorem uniform_pmoment_actual_original_single_window_physical_relative_polynomial_rate
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (B : ℝ) (hB : 1 ≤ B)
    (cSZ C1 C2 C3 C4 : ℝ)
    (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
      cSZ C1 C2 C3 C4) :
    ∀ (Cenv aenv t0 Menv : ℝ)
      (hCenv : 0 ≤ Cenv) (haenv : 0 ≤ aenv)
      (ht0 : 0 < t0) (hMenv : 0 ≤ Menv),
    let q : ℝ := (p - 2) / (2 * p)
    let cMoment : ℝ := Real.rpow (min (1 / 2 : ℝ) cSZ / 2) (1 / p)
    let cRemainder : ℝ := remainderWindowScale
      (Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv) t0
    let cAbsorb : ℝ := min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ))
    let cTilt : ℝ := 1 / (2 * Real.exp (1 / 2 : ℝ))
    let cGeometry : ℝ := 1 / (1 + Menv)
    let c : ℝ := min cMoment (min cRemainder (min cAbsorb (min cTilt cGeometry)))
    let K0 : ℝ :=
      64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ))
    let K : ℝ := 8 * (1 + C1 + C2 + C3 + C4) * Real.exp C3 * (1 + K0)
    0 < c ∧ 0 < K ∧
      ∃ N : ℕ, 4 ≤ N ∧
        ∀ (n : ℕ), N ≤ n →
          (2 : ℝ) ≤ c * Real.rpow B (-1 / p) * Real.rpow (n : ℝ) q ∧
          ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω]
            (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
            (h : Ω → Ω → ℝ)
            (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
            (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
            (hhsymm : ∀ o y, h o y = h y o)
            (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
            (hprojectionsecond :
              (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1),
            let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
            let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
            let v : ℝ :=
              ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω mΩ mΩ μ μ)
            let rho : ℝ := Real.sqrt v
            let β : ℝ := ∫ o : Ω, Real.rpow |g o| p ∂μ
            ∀ (hgp : Integrable[mΩ] (fun o : Ω => Real.rpow |g o| p) μ)
              (hβBound : β ≤ B),
              1 ≤ β ∧
              (2 : ℝ) ≤ c * Real.rpow β (-1 / p) * Real.rpow (n : ℝ) q ∧
              ∀ (w : Ω → ℝ)
                (hW : ∀ᵐ o : Ω ∂μ, 0 ≤ w o)
                (hWR : ∀ᵐ o : Ω ∂μ, w o ≤ boundedPolylogHeight Cenv aenv n)
                (hSq : Integrable[mΩ] (fun o : Ω => (w o) ^ (2 : ℕ)) μ)
                (hSqBound : (∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ≤ Menv)
                (hEnv : ∀ᵐ t : Ω × Ω ∂(@Measure.prod Ω Ω mΩ mΩ μ μ),
                  |r t.1 t.2| ≤ w t.1 * w t.2)
                (z : ℝ) (hz : 1 ≤ z)
                (hWindow : z ≤ c * Real.rpow β (-1 / p) * Real.rpow (n : ℝ) q),
                let mN : MeasurableSpace (Fin n → Ω) :=
                  @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω)
                    (fun _ : Fin n => mΩ)
                let P : @Measure (Fin n → Ω) mN :=
                  @Measure.pi (Fin n) (fun _ : Fin n => Ω)
                    (inferInstance : Fintype (Fin n))
                    (fun _ : Fin n => mΩ) (fun _ : Fin n => μ)
                let D1 : (Fin n → Ω) → ℝ := residualStatisticD n r
                let physical : (Fin n → Ω) → ℝ := fun ζ =>
                  if Real.sqrt (centeredSq n g r ζ) = 0 then 0 else
                    (projectionW n g ζ + D1 ζ) / Real.sqrt (centeredSq n g r ζ)
                |P.real {ζ : Fin n → Ω | z ≤ physical ζ} / Shao.standardNormalTail z - 1| ≤
                  K * (β * Real.rpow (1 + z) p *
                    Real.rpow (n : ℝ) (-((p - 2) / 2)) +
                    (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ))
:= by
  set_option maxHeartbeats 800000 in
    classical
    intro Cenv aenv t0 Menv hCenv haenv ht0 hMenv
      q cMoment cRemainder cAbsorb cTilt cGeometry c K0 K
    have hp0 : 0 < p := lt_trans (by norm_num : (0 : ℝ) < 2) hp2
    have hcSZ : 0 < cSZ := hSZ.1
    have hC1 : 0 < C1 := hSZ.2.1
    have hC2 : 0 < C2 := hSZ.2.2.1
    have hC3 : 0 < C3 := hSZ.2.2.2.1
    have hC4 : 0 < C4 := hSZ.2.2.2.2.1
    have hK0 : 0 < K0 := by dsimp only [K0]; positivity
    have hK : 0 < K := by dsimp only [K]; positivity
    have hqpos : 0 < q := by
      dsimp only [q]
      exact div_pos (sub_pos.mpr hp2) (mul_pos (by norm_num) hp0)
    have hqSixth : q ≤ (1 / 6 : ℝ) := by
      dsimp only [q]
      apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hp0)).2
      nlinarith only [hp3]
    have hcMoment : 0 < cMoment :=
      Real.rpow_pos_of_pos
        (div_pos (lt_min (by norm_num : (0 : ℝ) < 1 / 2) hcSZ) (by norm_num)) _
    have hTailScale : 0 ≤ Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv := by
      unfold Shao.OQ6.BoundedProductEnvelopeTails.tailScale
      apply le_trans _ (le_max_left _ _)
      dsimp only [Shao.OQ6.BoundedProductEnvelopeTails.squareTailScale]
      exact mul_nonneg (Real.exp_pos _).le (by linarith only [hMenv])
    have hcRemainder : 0 < cRemainder :=
      (remainderWindowScale_bounds _ _ hTailScale ht0).1
    have hcAbsorb : 0 < cAbsorb :=
      lt_min zero_lt_one (div_pos (Real.sqrt_pos.mpr ht0) (by norm_num))
    have hcTilt : 0 < cTilt := by dsimp only [cTilt]; positivity
    have hMone : 0 < 1 + Menv := by linarith only [hMenv]
    have hcGeometry : 0 < cGeometry := one_div_pos.mpr hMone
    have hc : 0 < c :=
      lt_min hcMoment (lt_min hcRemainder (lt_min hcAbsorb (lt_min hcTilt hcGeometry)))
    have hcMomentBound : c ≤ cMoment := min_le_left _ _
    have hcRest : c ≤ min cRemainder (min cAbsorb (min cTilt cGeometry)) :=
      min_le_right _ _
    have hcRemainderBound : c ≤ cRemainder := hcRest.trans (min_le_left _ _)
    have hcRest2 : c ≤ min cAbsorb (min cTilt cGeometry) :=
      hcRest.trans (min_le_right _ _)
    have hcAbsorbBound : c ≤ cAbsorb := hcRest2.trans (min_le_left _ _)
    have hcRest3 : c ≤ min cTilt cGeometry := hcRest2.trans (min_le_right _ _)
    have hcTiltBound : c ≤ cTilt := hcRest3.trans (min_le_left _ _)
    have hcGeometryBound : c ≤ cGeometry := hcRest3.trans (min_le_right _ _)
    refine ⟨hc, hK, ?_⟩
    -- Every threshold below is selected before n or any original model.
    let cg : ℝ := Real.rpow (1 / (4 * B)) (2 / (p - 2)) / 4
    have hFinite :=
      Shao.OQ6.UniformPMomentPhysicalFiniteCostTail.uniform_pmoment_actual_original_current_level_physical_finite_cost_tail.{u}
        p hp2 hp3 B hB
    dsimp only at hFinite
    change 0 < cg ∧ _ at hFinite
    rcases hFinite with ⟨hcg, hAll⟩
    obtain ⟨Ncommon, hNcommon4, hCommonN⟩ :=
      hAll Cenv aenv t0 Menv hCenv haenv ht0 hMenv
    have hAbs :=
      Shao.OQ6.OriginalExceptionalTailAbsorption.eventually_original_exceptional_payment_absorbed
        t0 cg ht0 hcg
    dsimp only at hAbs
    rcases hAbs with ⟨hAbsWindowPositive, hAbs⟩
    obtain ⟨Nabs, hNabs⟩ := Filter.eventually_atTop.1 hAbs
    have hnat : Filter.Tendsto (fun n : ℕ => (n : ℝ))
        Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
    have hthird : Filter.Tendsto
        (fun n : ℕ => Real.rpow (n : ℝ) (1 / 3 : ℝ))
        Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hnat
    have hRlimit : Filter.Tendsto
        (fun n : ℕ => Real.sqrt (n : ℝ) *
          Real.exp (-(t0 / 2) * Real.rpow (n : ℝ) (1 / 3 : ℝ)))
        Filter.atTop (nhds (0 : ℝ)) := by
      have hlim :=
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
          (3 / 2 : ℝ) (t0 / 2) (by positivity)).comp hthird
      apply hlim.congr'
      filter_upwards [] with n
      have hpower : Real.rpow (Real.rpow (n : ℝ) (1 / 3 : ℝ)) (3 / 2 : ℝ) =
          Real.sqrt (n : ℝ) := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_mul (Nat.cast_nonneg n)]
        convert (Real.sqrt_eq_rpow (n : ℝ)).symm using 1 <;> norm_num
      simp only [Real.rpow_eq_pow] at hpower ⊢
      simp only [Function.comp_def, hpower]
    have hRsmall : ∀ᶠ n : ℕ in Filter.atTop,
        Real.sqrt (n : ℝ) *
          Real.exp (-(t0 / 2) * Real.rpow (n : ℝ) (1 / 3 : ℝ)) ≤ 1 :=
      (hRlimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
        (fun _ hn => hn.le)
    obtain ⟨Nsmall, hNsmall⟩ := Filter.eventually_atTop.1 hRsmall
    let commonA : ℝ := c * Real.rpow B (-1 / p)
    have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
    have hcommonA : 0 < commonA :=
      mul_pos hc (Real.rpow_pos_of_pos hBpos _)
    have hpower : Filter.Tendsto (fun n : ℕ => Real.rpow (n : ℝ) q)
        Filter.atTop Filter.atTop := (tendsto_rpow_atTop hqpos).comp hnat
    have hnonempty : ∀ᶠ n : ℕ in Filter.atTop,
        (2 : ℝ) ≤ commonA * Real.rpow (n : ℝ) q := by
      filter_upwards [hpower.eventually_ge_atTop (2 / commonA)] with n hn
      have hscaled := (div_le_iff₀ hcommonA).mp hn
      simpa only [mul_comm] using hscaled
    obtain ⟨Nwin, hNwin⟩ := Filter.eventually_atTop.1 hnonempty
    refine ⟨max Ncommon (max Nabs (max Nsmall Nwin)),
      hNcommon4.trans (le_max_left _ _), ?_⟩
    intro n hn
    have hnCommon : Ncommon ≤ n := (le_max_left _ _).trans hn
    have hnRest : max Nabs (max Nsmall Nwin) ≤ n := (le_max_right _ _).trans hn
    have hnAbs : Nabs ≤ n := (le_max_left _ _).trans hnRest
    have hnRest2 : max Nsmall Nwin ≤ n := (le_max_right _ _).trans hnRest
    have hnSmall : Nsmall ≤ n := (le_max_left _ _).trans hnRest2
    have hnWin : Nwin ≤ n := (le_max_right _ _).trans hnRest2
    have hn4 : 4 ≤ n := hNcommon4.trans hnCommon
    have hn1 : 1 ≤ n := by omega
    have hnPos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hnRealOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnPower : 0 ≤ Real.rpow (n : ℝ) q := Real.rpow_nonneg hnPos.le _
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnPos
    have hCommonWindow : (2 : ℝ) ≤ c * Real.rpow B (-1 / p) * Real.rpow (n : ℝ) q :=
      hNwin n hnWin
    have hAbsN := hNabs n hnAbs
    have hRsmallN := hNsmall n hnSmall
    refine ⟨hCommonWindow, ?_⟩
    intro Ω mΩ μ hμ h hh hh2 hhsymm hcenter hprojectionsecond g r v rho β hgp hβBound
    -- Extract only the original-space projection and residual facts, at fixed (3,0).
    have hCanonical :=
      Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
        μ h hh hh2 hhsymm hcenter hprojectionsecond
        3 (by norm_num) 0 (by norm_num) (by positivity)
    dsimp only at hCanonical
    rcases hCanonical with
      ⟨hg, hg2, hgmean, hgsecond, hr, hr2, hsym, hcR, _⟩
    change Measurable[mΩ, borel ℝ] g at hg
    change MemLp g 2 μ at hg2
    change (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1 at hgsecond
    change MemLp (Function.uncurry r) 2 (μ.prod μ) at hr2
    have hβnonneg : 0 ≤ β :=
      integral_nonneg (fun o : Ω => Real.rpow_nonneg (abs_nonneg (g o)) p)
    -- Probability-space Lp monotonicity gives beta >= 1 from the actual normalization.
    have hpENN0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp0)
    have hpENNTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
    have hgP : MemLp g (ENNReal.ofReal p) μ := by
      apply (integrable_norm_rpow_iff hg.aestronglyMeasurable hpENN0 hpENNTop).mp
      simpa only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs] using hgp
    have hExponent : (2 : ENNReal) ≤ ENNReal.ofReal p := by
      calc
        (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
        _ ≤ ENNReal.ofReal p := ENNReal.ofReal_le_ofReal hp2.le
    have hCompare : eLpNorm g 2 μ ≤ eLpNorm g (ENNReal.ofReal p) μ :=
      eLpNorm_le_eLpNorm_of_exponent_le hExponent
    have hNormSecond : (∫ o : Ω, ‖g o‖ ^ (2 : ℝ) ∂μ) = 1 := by
      simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs] using hgsecond
    have hNormP : (∫ o : Ω, ‖g o‖ ^ p ∂μ) = β := by
      simpa only [Real.norm_eq_abs]
    have hTwoReal : (2 : ENNReal).toReal = (2 : ℝ) := by norm_num
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ENNReal) ≠ 0)
        (by norm_num : (2 : ENNReal) ≠ ∞) hg2,
      MemLp.eLpNorm_eq_integral_rpow_norm hpENN0 hpENNTop hgP,
      hTwoReal, ENNReal.toReal_ofReal hp0.le, hNormSecond, hNormP] at hCompare
    have hRoot : (1 : ℝ) ≤ Real.rpow β p⁻¹ := by
      have hRealCompare :=
        (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hβnonneg p⁻¹)).mp hCompare
      simpa only [Real.one_rpow] using hRealCompare
    have hβone : 1 ≤ β :=
      (Real.rpow_le_rpow_iff zero_le_one hβnonneg (inv_pos.mpr hp0)).mp
        (by simpa only [Real.one_rpow] using hRoot)
    have hβpos : 0 < β := lt_of_lt_of_le zero_lt_one hβone
    have hNegativeExponent : -1 / p ≤ (0 : ℝ) := by
      apply (div_le_iff₀ hp0).2
      norm_num
    have hβB : Real.rpow B (-1 / p) ≤ Real.rpow β (-1 / p) :=
      Real.rpow_le_rpow_of_nonpos hβpos hβBound hNegativeExponent
    have hModelWindow : (2 : ℝ) ≤ c * Real.rpow β (-1 / p) * Real.rpow (n : ℝ) q :=
      hCommonWindow.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hβB hc.le) hnPower)
    refine ⟨hβone, hModelWindow, ?_⟩
    intro w hW hWR hSq hSqBound hEnv z hz hWindow mN P D1 physical
    have hz0 : 0 ≤ z := le_trans (by norm_num : (0 : ℝ) ≤ 1) hz
    have hRhoBound :=
      Shao.OQ6.OriginalEnvelopeRhoBound.original_residual_rho_le_envelope_second_moment
        μ r hr2 w hW hSq Menv hMenv hSqBound hEnv
    change 0 ≤ v ∧ v ≤ Menv ^ (2 : ℕ) ∧ 0 ≤ rho ∧ rho ≤ Menv at hRhoBound
    rcases hRhoBound with ⟨hvNonneg, hvBound, hrho, hrhoM⟩
    have hβInverse : 0 ≤ Real.rpow β (-1 / p) := Real.rpow_nonneg hβnonneg _
    have hβInverseOne : Real.rpow β (-1 / p) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hβone hNegativeExponent
    have hBaseWindow : z ≤ c * Real.rpow (n : ℝ) q := by
      calc
        z ≤ c * Real.rpow β (-1 / p) * Real.rpow (n : ℝ) q := hWindow
        _ ≤ (c * 1) * Real.rpow (n : ℝ) q :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hβInverseOne hc.le) hnPower
        _ = c * Real.rpow (n : ℝ) q := by ring
    have hPowerSixth : Real.rpow (n : ℝ) q ≤ Real.rpow (n : ℝ) (1 / 6 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hnRealOne hqSixth
    have hSixthSqrt : Real.rpow (n : ℝ) (1 / 6 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      calc
        Real.rpow (n : ℝ) (1 / 6 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hnRealOne (by norm_num : (1 / 6 : ℝ) ≤ 1 / 2)
        _ = Real.sqrt (n : ℝ) := (Real.sqrt_eq_rpow _).symm
    have hSixthWindow : z ≤ c * Real.rpow (n : ℝ) (1 / 6 : ℝ) :=
      hBaseWindow.trans (mul_le_mul_of_nonneg_left hPowerSixth hc.le)
    have hSqrtWindow : z ≤ c * Real.sqrt (n : ℝ) :=
      hSixthWindow.trans (mul_le_mul_of_nonneg_left hSixthSqrt hc.le)
    have hnSixth : 0 ≤ Real.rpow (n : ℝ) (1 / 6 : ℝ) := Real.rpow_nonneg hnPos.le _
    have hEnvelopeWindow : z ≤ remainderWindowScale
        (Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv) t0 *
          Real.rpow (n : ℝ) (1 / 6 : ℝ) :=
      hSixthWindow.trans (mul_le_mul_of_nonneg_right hcRemainderBound hnSixth)
    have hAbsorptionWindow : z ≤ min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ)) *
        Real.rpow (n : ℝ) (1 / 6 : ℝ) :=
      hSixthWindow.trans (mul_le_mul_of_nonneg_right hcAbsorbBound hnSixth)
    have hTiltWindow : z ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ)) := by
      calc
        z ≤ cTilt * Real.sqrt (n : ℝ) :=
          hSqrtWindow.trans (mul_le_mul_of_nonneg_right hcTiltBound (Real.sqrt_nonneg _))
        _ = Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ)) := by
          dsimp only [cTilt]
          ring
    have hGeometryWindow : z ≤ cGeometry * Real.sqrt (n : ℝ) :=
      hSqrtWindow.trans (mul_le_mul_of_nonneg_right hcGeometryBound (Real.sqrt_nonneg _))
    have hGeometry : (1 + rho) * z ≤ Real.sqrt (n : ℝ) := by
      calc
        (1 + rho) * z ≤ (1 + Menv) * z :=
          mul_le_mul_of_nonneg_right (_root_.add_le_add_left hrhoM 1) hz0
        _ ≤ (1 + Menv) * (cGeometry * Real.sqrt (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hGeometryWindow hMone.le
        _ = Real.sqrt (n : ℝ) := by
          dsimp only [cGeometry]
          field_simp [hMone.ne']
    have hMomentWindow : β = 0 ∨ (0 < β ∧
        z ≤ cMoment * Real.rpow β (-1 / p) * Real.rpow (n : ℝ) q) := by
      refine Or.inr ⟨hβpos, hWindow.trans ?_⟩
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcMomentBound hβInverse) hnPower
    let ξ : Fin n → (Fin n → Ω) → ℝ :=
      fun i ζ => g (ζ i) / Real.sqrt (n : ℝ)
    let δ : Fin n → ℝ := fun i =>
      ∫ ζ, (z * ξ i ζ) ^ 2 * min |z * ξ i ζ| 1 ∂P
    let L : ℝ := ∑ i : Fin n, δ i
    let A : ℝ := β * Real.rpow (1 + z) p * Real.rpow (n : ℝ) (-((p - 2) / 2))
    let E : ℝ := (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ)
    let R : ℝ := Real.exp (-(t0 / 2) * Real.rpow (n : ℝ) (1 / 3 : ℝ))
    let payment : ℝ :=
      (3 : ℝ) * Real.exp (-boundedPolylogMomentOrder t0 n) +
        Real.exp (-cg * (n : ℝ)) +
        (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ))
    let cubic : ℝ :=
      64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) *
        (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ)
    let Q : ℝ := P.real {ζ : Fin n → Ω | z ≤ physical ζ} / Shao.standardNormalTail z
    have hE : 0 ≤ E := by dsimp only [E]; positivity
    have hRinv : R ≤ 1 / Real.sqrt (n : ℝ) := by
      apply (le_div_iff₀ hsqrt).2
      change Real.sqrt (n : ℝ) * R ≤ 1 at hRsmallN
      nlinarith only [hRsmallN]
    have hEinv : 1 / Real.sqrt (n : ℝ) ≤ E := by
      apply div_le_div_of_nonneg_right _ hsqrt.le
      have hzOne : 1 ≤ 1 + z := by linarith only [hz]
      have hcube : (1 : ℝ) ≤ (1 + z) ^ 3 := one_le_pow₀ hzOne
      have hrhoOne : 1 ≤ 1 + rho := by linarith only [hrho]
      exact (by simpa only [one_mul] using
        mul_le_mul hrhoOne hcube (by norm_num : (0 : ℝ) ≤ 1) (by linarith only [hrho]))
    have hRE : R ≤ E := hRinv.trans hEinv
    -- Use the original product-law moment producer, without a second coding witness.
    have hMoment :=
      @Shao.OQ6.IIDSourceStrictMomentBudgets.actual_iid_source_z_strict_moment_budgets
        Ω mΩ μ (inferInstance : @IsProbabilityMeasure Ω mΩ μ)
        g hg hg2 p hp2 hp3 hgp cSZ hcSZ
    dsimp only at hMoment
    rcases hMoment with ⟨hBeta, hcPositive, hcPower, hcSmall, hMomentAll⟩
    have hMomentN := hMomentAll n hn1 z hz
    rcases hMomentN with
      ⟨hPprob, hScalarInt, hDeltaInt, hDeltaScalar, hLScalar, hLi,
        hDeltaNonneg, hLNonneg, hRate, hZero, hStrictWindow⟩
    change 0 ≤ β at hBeta
    change 0 ≤ L at hLNonneg
    change L ≤ β * Real.rpow z p / Real.rpow (n : ℝ) ((p - 2) / 2) at hRate
    have hLc : L ≤ Real.rpow cMoment p := (hStrictWindow hMomentWindow).1
    change Real.rpow cMoment p = min (1 / 2 : ℝ) cSZ / 2 at hcPower
    have hLquarter : L ≤ (1 / 4 : ℝ) := by
      rw [hcPower] at hLc
      have hmin := min_le_left (1 / 2 : ℝ) cSZ
      linarith only [hLc, hmin]
    have hA : 0 ≤ A := by
      dsimp only [A]
      exact mul_nonneg
        (mul_nonneg hBeta (Real.rpow_nonneg (by linarith only [hz0]) _))
        (Real.rpow_nonneg hnPos.le _)
    have hLA : L ≤ A := by
      calc
        L ≤ β * Real.rpow z p / Real.rpow (n : ℝ) ((p - 2) / 2) := hRate
        _ ≤ β * Real.rpow (1 + z) p / Real.rpow (n : ℝ) ((p - 2) / 2) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow hz0 (by linarith : z ≤ 1 + z) hp0.le) hBeta)
            (Real.rpow_nonneg hnPos.le _)
        _ = A := by
          dsimp only [A]
          simp only [Real.rpow_eq_pow]
          rw [Real.rpow_neg hnPos.le]
          ring
    have hFiniteN := hCommonN n hnCommon μ h hh hh2 hhsymm hcenter hprojectionsecond
      w hW hWR hSq hSqBound hEnv z hz hTiltWindow hEnvelopeWindow hGeometry
      hgp hβBound cSZ C1 C2 C3 C4 hSZ
    rcases hFiniteN hMomentWindow with
      ⟨hCostNonneg, hCostCubic, hLowerSource, hUpperSource, hLower, hUpper⟩
    change Shao.standardNormalTail z * Real.exp (-C1 * L) *
        (1 - C2 * cubic) - 2 * payment ≤
      P.real {ζ : Fin n → Ω | z ≤ physical ζ} at hLower
    change P.real {ζ : Fin n → Ω | z ≤ physical ζ} ≤
      Shao.standardNormalTail z * Real.exp (C3 * L) *
        (1 + C4 * cubic) + 4 * payment at hUpper
    have hcubic : cubic = K0 * E := by dsimp only [cubic, K0, E]; ring
    rw [hcubic] at hLower hUpper
    have hPsi : 0 < Shao.standardNormalTail z :=
      (Shao.standardNormalTail_basic.2.2.1 z).1
    -- Keep the lower2 and upper4 physical fees distinct throughout absorption.
    have hExpZ : Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ)) ≤
        Real.exp (-(Real.sqrt (n : ℝ)) / (2 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_right hz hsqrt.le
      nlinarith only [hm]
    have hAbsZ := hAbsN.2.2 z hz hAbsorptionWindow
    change (6 : ℝ) * Real.exp (-boundedPolylogMomentOrder t0 n) +
        (2 : ℝ) * Real.exp (-cg * (n : ℝ)) +
        (8 : ℝ) * Real.exp (-(Real.sqrt (n : ℝ)) / (2 : ℝ)) ≤
      R * Shao.standardNormalTail z at hAbsZ
    have hPay2 : 2 * payment ≤ R * Shao.standardNormalTail z := by
      dsimp only [payment]
      linarith only [hAbsZ, hExpZ]
    have hPay4 : 4 * payment ≤ 2 * R * Shao.standardNormalTail z := by
      nlinarith only [hPay2]
    have hLowerPaid :
        Shao.standardNormalTail z * (Real.exp (-C1 * L) * (1 - C2 * (K0 * E)) - R) ≤
          P.real {ζ : Fin n → Ω | z ≤ physical ζ} := by
      nlinarith only [hLower, hPay2]
    have hUpperPaid : P.real {ζ : Fin n → Ω | z ≤ physical ζ} ≤
        Shao.standardNormalTail z * (Real.exp (C3 * L) * (1 + C4 * (K0 * E)) + 2 * R) := by
      nlinarith only [hUpper, hPay4]
    have hLowerRatio : Real.exp (-C1 * L) * (1 - C2 * (K0 * E)) - R ≤ Q := by
      apply (le_div_iff₀ hPsi).2
      nlinarith only [hLowerPaid]
    have hUpperRatio : Q ≤ Real.exp (C3 * L) * (1 + C4 * (K0 * E)) + 2 * R := by
      apply (div_le_iff₀ hPsi).2
      nlinarith only [hUpperPaid]
    -- Expand the lower expression before estimating; its factor need not be positive.
    have hExpLower : Real.exp (-C1 * L) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hC1.le hLNonneg])
    have hLowerLinear : 1 - Real.exp (-C1 * L) ≤ C1 * L := by
      linarith only [Real.add_one_le_exp (-C1 * L)]
    have hLowerCost : Real.exp (-C1 * L) * (C2 * (K0 * E)) ≤ C2 * (K0 * E) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hExpLower (mul_nonneg hC2.le (mul_nonneg hK0.le hE))
    have hC1Rate : C1 * L ≤ C1 * A := mul_le_mul_of_nonneg_left hLA hC1.le
    have hLowerDeviation : 1 - Q ≤ C1 * A + (C2 * K0 + 1) * E := by
      nlinarith only [hLowerRatio, hLowerLinear, hLowerCost, hC1Rate, hRE]
    have hQuarterExp : Real.exp (C3 * L) ≤ Real.exp (C3 / 4) := by
      apply Real.exp_le_exp.mpr
      have ht := mul_le_mul_of_nonneg_left hLquarter hC3.le
      nlinarith only [ht]
    have hQuarterFull : Real.exp (C3 / 4) ≤ Real.exp C3 :=
      Real.exp_le_exp.mpr (by linarith only [hC3])
    have hUpperLinear : Real.exp (C3 * L) - 1 ≤ C3 * Real.exp (C3 / 4) * L := by
      have htangent := mul_le_mul_of_nonneg_right
        (Real.add_one_le_exp (-(C3 * L))) (Real.exp_pos (C3 * L)).le
      have hcancel : Real.exp (-(C3 * L)) * Real.exp (C3 * L) = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1 <;> ring
      rw [hcancel] at htangent
      have hproduct := mul_le_mul_of_nonneg_left hQuarterExp
        (mul_nonneg hC3.le hLNonneg)
      nlinarith only [htangent, hproduct]
    have hUpperCost : Real.exp (C3 * L) * (C4 * (K0 * E)) ≤
        Real.exp (C3 / 4) * (C4 * (K0 * E)) :=
      mul_le_mul_of_nonneg_right hQuarterExp (mul_nonneg hC4.le (mul_nonneg hK0.le hE))
    have hC3Rate : C3 * Real.exp (C3 / 4) * L ≤ C3 * Real.exp (C3 / 4) * A :=
      mul_le_mul_of_nonneg_left hLA (mul_nonneg hC3.le (Real.exp_pos _).le)
    have hUpperDeviation : Q - 1 ≤
        C3 * Real.exp (C3 / 4) * A + (C4 * K0 * Real.exp (C3 / 4) + 2) * E := by
      nlinarith only [hUpperRatio, hUpperLinear, hUpperCost, hC3Rate, hRE]
    -- Compare every coefficient with one fixed explicit K.
    let S : ℝ := 1 + C1 + C2 + C3 + C4
    let H : ℝ := S * Real.exp C3 * (1 + K0)
    have hSone : 1 ≤ S := by dsimp only [S]; linarith only [hC1, hC2, hC3, hC4]
    have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hSone
    have hC1S : C1 ≤ S := by dsimp only [S]; linarith only [hC2, hC3, hC4]
    have hC2S : C2 ≤ S := by dsimp only [S]; linarith only [hC1, hC3, hC4]
    have hC3S : C3 ≤ S := by dsimp only [S]; linarith only [hC1, hC2, hC4]
    have hC4S : C4 ≤ S := by dsimp only [S]; linarith only [hC1, hC2, hC3]
    have hExpOne : 1 ≤ Real.exp C3 := by linarith only [Real.add_one_le_exp C3, hC3]
    have hT : 1 ≤ 1 + K0 := by linarith only [hK0]
    have hK0T : K0 ≤ 1 + K0 := by linarith
    have hST : 0 ≤ S * (1 + K0) := mul_nonneg hSpos.le (by linarith only [hT])
    have hHpos : 0 < H := by dsimp only [H]; positivity
    have hHE : S * Real.exp C3 ≤ H := by
      dsimp only [H]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hT (mul_nonneg hSpos.le (Real.exp_pos _).le)
    have hSexp : S ≤ S * Real.exp C3 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hExpOne hSpos.le
    have hHS : S ≤ H := hSexp.trans hHE
    have hHone : 1 ≤ H := hSone.trans hHS
    have hHST : S * (1 + K0) ≤ H := by
      have ht := mul_le_mul_of_nonneg_left hExpOne hST
      dsimp only [H]
      nlinarith only [ht]
    have hC1H : C1 ≤ H := hC1S.trans hHS
    have hC2H : C2 * K0 ≤ H :=
      (mul_le_mul hC2S hK0T hK0.le hSpos.le).trans hHST
    have hC3H : C3 * Real.exp (C3 / 4) ≤ H :=
      (mul_le_mul hC3S hQuarterFull (Real.exp_pos _).le hSpos.le).trans hHE
    have hC4K : C4 * K0 ≤ S * (1 + K0) :=
      mul_le_mul hC4S hK0T hK0.le hSpos.le
    have hC4H : C4 * K0 * Real.exp (C3 / 4) ≤ H := by
      have ht := mul_le_mul hC4K hQuarterFull (Real.exp_pos _).le hST
      dsimp only [H]
      nlinarith only [ht]
    have hKEq : K = 8 * H := by dsimp only [K, H, S]; ring
    have hC1K : C1 ≤ K := by rw [hKEq]; linarith only [hC1H, hHpos]
    have hC2K : C2 * K0 + 1 ≤ K := by
      rw [hKEq]
      linarith only [hC2H, hHone, hHpos]
    have hC3K : C3 * Real.exp (C3 / 4) ≤ K := by
      rw [hKEq]
      linarith only [hC3H, hHpos]
    have hC4Ktail : C4 * K0 * Real.exp (C3 / 4) + 2 ≤ K := by
      rw [hKEq]
      linarith only [hC4H, hHone, hHpos]
    have hLowerFinal : 1 - Q ≤ K * (A + E) := by
      calc
        1 - Q ≤ C1 * A + (C2 * K0 + 1) * E := hLowerDeviation
        _ ≤ K * A + K * E :=
          _root_.add_le_add (mul_le_mul_of_nonneg_right hC1K hA)
            (mul_le_mul_of_nonneg_right hC2K hE)
        _ = K * (A + E) := by ring
    have hUpperFinal : Q - 1 ≤ K * (A + E) := by
      calc
        Q - 1 ≤ C3 * Real.exp (C3 / 4) * A +
            (C4 * K0 * Real.exp (C3 / 4) + 2) * E := hUpperDeviation
        _ ≤ K * A + K * E :=
          _root_.add_le_add (mul_le_mul_of_nonneg_right hC3K hA)
            (mul_le_mul_of_nonneg_right hC4Ktail hE)
        _ = K * (A + E) := by ring
    change |Q - 1| ≤ K * (A + E)
    apply abs_le.mpr
    exact ⟨by linarith only [hLowerFinal], hUpperFinal⟩
end
end Shao.OQ6.UniformPMomentSingleWindowPhysicalRelativePolynomialRate
