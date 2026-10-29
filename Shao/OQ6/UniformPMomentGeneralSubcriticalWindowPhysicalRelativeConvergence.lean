import Shao.OQ6.UniformPMomentSingleWindowPhysicalRelativePolynomialRate
import Shao.OQ6.OriginalEnvelopeRhoBound

set_option autoImplicit false
universe u
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology MeasureTheory symmDiff ENNReal
open Shao.OQ5.P51
namespace Shao.OQ6.UniformPMomentGeneralSubcriticalWindowPhysicalRelativeConvergence
noncomputable section

theorem uniform_pmoment_actual_original_subcritical_window_physical_relative_convergence
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (B : ℝ) (hB : 1 ≤ B)
    (cSZ C1 C2 C3 C4 : ℝ)
    (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
      cSZ C1 C2 C3 C4) :
    ∀ (Cenv aenv t0 Menv : ℝ)
      (hCenv : 0 ≤ Cenv) (haenv : 0 ≤ aenv)
      (ht0 : 0 < t0) (hMenv : 0 ≤ Menv),
    let q : ℝ := (p - 2) / (2 * p)
    ∀ (b : ℕ → ℝ)
      (hbLower : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) ≤ b n)
      (hbSmall : Filter.Tendsto
        (fun n : ℕ => b n / Real.rpow (n : ℝ) q) Filter.atTop (nhds (0 : ℝ)))
      (ε : ℝ) (hε : 0 < ε),
      ∃ N : ℕ, 4 ≤ N ∧
        ∀ (n : ℕ), N ≤ n →
          (1 : ℝ) ≤ b n ∧
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
              ∀ (w : Ω → ℝ)
                (hW : ∀ᵐ o : Ω ∂μ, 0 ≤ w o)
                (hWR : ∀ᵐ o : Ω ∂μ, w o ≤ boundedPolylogHeight Cenv aenv n)
                (hSq : Integrable[mΩ] (fun o : Ω => (w o) ^ (2 : ℕ)) μ)
                (hSqBound : (∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ≤ Menv)
                (hEnv : ∀ᵐ t : Ω × Ω ∂(@Measure.prod Ω Ω mΩ mΩ μ μ),
                  |r t.1 t.2| ≤ w t.1 * w t.2)
                (z : ℝ) (hz : 1 ≤ z) (hWindow : z ≤ b n),
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
                |P.real {ζ : Fin n → Ω | z ≤ physical ζ} / Shao.standardNormalTail z - 1| ≤ ε
:= by
  set_option maxHeartbeats 800000 in
    classical
    intro Cenv aenv t0 Menv hCenv haenv ht0 hMenv q b hbLower hbSmall ε hε
    have hp0 : 0 < p := lt_trans (by norm_num : (0 : ℝ) < 2) hp2
    have hqpos : 0 < q := by
      dsimp only [q]
      exact div_pos (sub_pos.mpr hp2) (mul_pos (by norm_num) hp0)
    have hqSixth : q ≤ (1 / 6 : ℝ) := by
      dsimp only [q]
      apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hp0)).2
      nlinarith only [hp3]
    have h3q : 3 * q ≤ (1 / 2 : ℝ) := by linarith only [hqSixth]
    have hqp : q * p = (p - 2) / 2 := by
      dsimp only [q]
      field_simp [hp0.ne']
      <;> ring
    let cMoment : ℝ := Real.rpow (min (1 / 2 : ℝ) cSZ / 2) (1 / p)
    let cRemainder : ℝ := remainderWindowScale
      (Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv) t0
    let cAbsorb : ℝ := min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ))
    let cTilt : ℝ := 1 / (2 * Real.exp (1 / 2 : ℝ))
    let cGeometry : ℝ := 1 / (1 + Menv)
    let c : ℝ := min cMoment (min cRemainder (min cAbsorb (min cTilt cGeometry)))
    let K0 : ℝ := 64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ))
    let K : ℝ := 8 * (1 + C1 + C2 + C3 + C4) * Real.exp C3 * (1 + K0)
    have h270 :=
      Shao.OQ6.UniformPMomentSingleWindowPhysicalRelativePolynomialRate.uniform_pmoment_actual_original_single_window_physical_relative_polynomial_rate.{u}
        p hp2 hp3 B hB cSZ C1 C2 C3 C4 hSZ
        Cenv aenv t0 Menv hCenv haenv ht0 hMenv
    dsimp only at h270
    change 0 < c ∧ 0 < K ∧ _ at h270
    rcases h270 with ⟨hc, hK, N270, hN2704, h270N⟩
    have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
    let commonA : ℝ := c * Real.rpow B (-1 / p)
    have hcommonA : 0 < commonA :=
      mul_pos hc (Real.rpow_pos_of_pos hBpos _)
    -- All four clocks below are fixed before n and every original model.
    have hnat : Filter.Tendsto (fun n : ℕ => (n : ℝ))
        Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
    have hpower : Filter.Tendsto (fun n : ℕ => Real.rpow (n : ℝ) q)
        Filter.atTop Filter.atTop := (tendsto_rpow_atTop hqpos).comp hnat
    have hinv : Filter.Tendsto (fun n : ℕ => 1 / Real.rpow (n : ℝ) q)
        Filter.atTop (nhds (0 : ℝ)) := by
      simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hpower
    let a : ℕ → ℝ := fun n => (1 + b n) / Real.rpow (n : ℝ) q
    have haLimit : Filter.Tendsto a Filter.atTop (nhds (0 : ℝ)) := by
      simpa only [← add_div, add_zero] using hinv.add hbSmall
    have hpContinuous : Continuous (fun x : ℝ => Real.rpow x p) := by
      simpa only [Real.rpow_eq_pow, id_eq] using
        (continuous_id.rpow_const (fun _ : ℝ => Or.inr hp0.le))
    have hapLimit : Filter.Tendsto (fun n : ℕ => Real.rpow (a n) p)
        Filter.atTop (nhds (0 : ℝ)) := by
      have hlim := (hpContinuous.tendsto (0 : ℝ)).comp haLimit
      simpa only [Function.comp_def, Real.rpow_eq_pow, Real.zero_rpow hp0.ne'] using hlim
    have haCubeLimit : Filter.Tendsto (fun n : ℕ => (a n) ^ (3 : ℕ))
        Filter.atTop (nhds (0 : ℝ)) := by
      simpa only [zero_pow (by norm_num : (3 : ℕ) ≠ 0)] using haLimit.pow 3
    let E : ℕ → ℝ := fun n =>
      K * (B * Real.rpow (a n) p + (1 + Menv) * (a n) ^ (3 : ℕ))
    have hELimit : Filter.Tendsto E Filter.atTop (nhds (0 : ℝ)) := by
      have hlim :=
        ((hapLimit.const_mul B).add (haCubeLimit.const_mul (1 + Menv))).const_mul K
      simpa only [mul_zero, add_zero] using hlim
    have hWindowEventually : ∀ᶠ n : ℕ in Filter.atTop,
        b n / Real.rpow (n : ℝ) q ≤ commonA :=
      (hbSmall.eventually (gt_mem_nhds hcommonA)).mono (fun _ hn => hn.le)
    have hErrorEventually : ∀ᶠ n : ℕ in Filter.atTop, E n ≤ ε :=
      (hELimit.eventually (gt_mem_nhds hε)).mono (fun _ hn => hn.le)
    obtain ⟨Nwin, hNwin⟩ := Filter.eventually_atTop.1 hWindowEventually
    obtain ⟨Nlower, hNlower⟩ := Filter.eventually_atTop.1 hbLower
    obtain ⟨Nerror, hNerror⟩ := Filter.eventually_atTop.1 hErrorEventually
    refine ⟨max N270 (max Nwin (max Nlower Nerror)),
      hN2704.trans (le_max_left _ _), ?_⟩
    intro n hn
    have hn270 : N270 ≤ n := (le_max_left _ _).trans hn
    have hnRest : max Nwin (max Nlower Nerror) ≤ n := (le_max_right _ _).trans hn
    have hnWin : Nwin ≤ n := (le_max_left _ _).trans hnRest
    have hnRest2 : max Nlower Nerror ≤ n := (le_max_right _ _).trans hnRest
    have hnLower : Nlower ≤ n := (le_max_left _ _).trans hnRest2
    have hnError : Nerror ≤ n := (le_max_right _ _).trans hnRest2
    have hn4 : 4 ≤ n := hN2704.trans hn270
    have hn1 : 1 ≤ n := by omega
    have hnPos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hnRealOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnqPos : 0 < Real.rpow (n : ℝ) q := Real.rpow_pos_of_pos hnPos _
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnPos
    have hbOne : (1 : ℝ) ≤ b n := hNlower n hnLower
    have hOneb : 0 ≤ 1 + b n := by linarith only [hbOne]
    have haNonneg : 0 ≤ a n := div_nonneg hOneb hnqPos.le
    have hbScaled : b n ≤ c * Real.rpow B (-1 / p) * Real.rpow (n : ℝ) q :=
      (div_le_iff₀ hnqPos).mp (hNwin n hnWin)
    have hErrorN : E n ≤ ε := hNerror n hnError
    refine ⟨hbOne, ?_⟩
    intro Ω mΩ μ hμ h hh hh2 hhsymm hcenter hprojectionsecond g r v rho β hgp hβBound
    have hModel := (h270N n hn270).2 μ h hh hh2 hhsymm hcenter hprojectionsecond
      hgp hβBound
    change 1 ≤ β ∧
      (2 : ℝ) ≤ c * Real.rpow β (-1 / p) * Real.rpow (n : ℝ) q ∧ _ at hModel
    rcases hModel with ⟨hβone, hβNonempty, hRate⟩
    have hβpos : 0 < β := lt_of_lt_of_le zero_lt_one hβone
    have hNegativeExponent : -1 / p ≤ (0 : ℝ) := by
      apply (div_le_iff₀ hp0).2
      norm_num
    have hβB : Real.rpow B (-1 / p) ≤ Real.rpow β (-1 / p) :=
      Real.rpow_le_rpow_of_nonpos hβpos hβBound hNegativeExponent
    intro w hW hWR hSq hSqBound hEnv z hz hWindow mN P D1 physical
    have hTrueWindow : z ≤ c * Real.rpow β (-1 / p) * Real.rpow (n : ℝ) q :=
      hWindow.trans (hbScaled.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hβB hc.le) hnqPos.le))
    have hRateZ := hRate w hW hWR hSq hSqBound hEnv z hz hTrueWindow
    change |P.real {ζ : Fin n → Ω | z ≤ physical ζ} / Shao.standardNormalTail z - 1| ≤
      K * (β * Real.rpow (1 + z) p * Real.rpow (n : ℝ) (-((p - 2) / 2)) +
        (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ)) at hRateZ
    -- Recover the same original residual L2 fact at fixed auxiliary (3,0).
    have hCanonical :=
      Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
        μ h hh hh2 hhsymm hcenter hprojectionsecond
        3 (by norm_num) 0 (by norm_num) (by positivity)
    dsimp only at hCanonical
    rcases hCanonical with ⟨hg, hg2, hgmean, hgsecond, hr, hr2, hrest⟩
    change MemLp (Function.uncurry r) 2 (μ.prod μ) at hr2
    have hRhoBound :=
      Shao.OQ6.OriginalEnvelopeRhoBound.original_residual_rho_le_envelope_second_moment
        μ r hr2 w hW hSq Menv hMenv hSqBound hEnv
    change 0 ≤ v ∧ v ≤ Menv ^ (2 : ℕ) ∧ 0 ≤ rho ∧ rho ≤ Menv at hRhoBound
    rcases hRhoBound with ⟨hvNonneg, hvBound, hrho, hrhoM⟩
    have hOnez : 0 ≤ 1 + z := by linarith only [hz]
    have hBaseOrder : 1 + z ≤ 1 + b n := _root_.add_le_add (le_refl (1 : ℝ)) hWindow
    have hMomentNumerator : β * Real.rpow (1 + z) p ≤ B * Real.rpow (1 + b n) p :=
      mul_le_mul hβBound (Real.rpow_le_rpow hOnez hBaseOrder hp0.le)
        (Real.rpow_nonneg hOnez _) hBpos.le
    have hqPowerP : Real.rpow (Real.rpow (n : ℝ) q) p =
        Real.rpow (n : ℝ) ((p - 2) / 2) := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_mul hnPos.le, hqp]
    have haPowerP : Real.rpow (a n) p =
        Real.rpow (1 + b n) p / Real.rpow (n : ℝ) ((p - 2) / 2) := by
      calc
        Real.rpow (a n) p =
            Real.rpow (1 + b n) p / Real.rpow (Real.rpow (n : ℝ) q) p :=
          Real.div_rpow hOneb hnqPos.le p
        _ = Real.rpow (1 + b n) p / Real.rpow (n : ℝ) ((p - 2) / 2) := by
          rw [hqPowerP]
    have hnNegative : Real.rpow (n : ℝ) (-((p - 2) / 2)) =
        (Real.rpow (n : ℝ) ((p - 2) / 2))⁻¹ := Real.rpow_neg hnPos.le _
    have hFirst : β * Real.rpow (1 + z) p *
        Real.rpow (n : ℝ) (-((p - 2) / 2)) ≤ B * Real.rpow (a n) p := by
      calc
        β * Real.rpow (1 + z) p * Real.rpow (n : ℝ) (-((p - 2) / 2)) ≤
            B * Real.rpow (1 + b n) p * Real.rpow (n : ℝ) (-((p - 2) / 2)) :=
          mul_le_mul_of_nonneg_right hMomentNumerator (Real.rpow_nonneg hnPos.le _)
        _ = B * Real.rpow (a n) p := by
          rw [hnNegative, haPowerP]
          ring
    have hqCube : (Real.rpow (n : ℝ) q) ^ (3 : ℕ) =
        Real.rpow (n : ℝ) (3 * q) := by
      calc
        (Real.rpow (n : ℝ) q) ^ (3 : ℕ) =
            Real.rpow (Real.rpow (n : ℝ) q) (3 : ℝ) :=
          (Real.rpow_natCast _ 3).symm
        _ = Real.rpow (n : ℝ) (q * 3) := (Real.rpow_mul hnPos.le q 3).symm
        _ = Real.rpow (n : ℝ) (3 * q) := by congr 1 <;> ring
    have hCubeSqrt : (Real.rpow (n : ℝ) q) ^ (3 : ℕ) ≤ Real.sqrt (n : ℝ) := by
      calc
        (Real.rpow (n : ℝ) q) ^ (3 : ℕ) = Real.rpow (n : ℝ) (3 * q) := hqCube
        _ ≤ Real.rpow (n : ℝ) (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hnRealOne h3q
        _ = Real.sqrt (n : ℝ) := (Real.sqrt_eq_rpow _).symm
    have haCube : (a n) ^ (3 : ℕ) =
        (1 + b n) ^ (3 : ℕ) / (Real.rpow (n : ℝ) q) ^ (3 : ℕ) := by
      dsimp only [a]
      rw [div_pow]
    have hCubicNumerator : (1 + rho) * (1 + z) ^ (3 : ℕ) ≤
        (1 + Menv) * (1 + b n) ^ (3 : ℕ) :=
      mul_le_mul (_root_.add_le_add (le_refl (1 : ℝ)) hrhoM) (pow_le_pow_left₀ hOnez hBaseOrder 3)
        (pow_nonneg hOnez 3) (by linarith only [hMenv])
    have hCubic : (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ) ≤
        (1 + Menv) * (a n) ^ (3 : ℕ) := by
      calc
        (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ) ≤
            (1 + Menv) * (1 + b n) ^ 3 / Real.sqrt (n : ℝ) :=
          div_le_div_of_nonneg_right hCubicNumerator hsqrt.le
        _ ≤ (1 + Menv) * (1 + b n) ^ 3 / (Real.rpow (n : ℝ) q) ^ (3 : ℕ) :=
          div_le_div_of_nonneg_left
            (mul_nonneg (by linarith only [hMenv]) (pow_nonneg hOneb 3))
            (pow_pos hnqPos 3) hCubeSqrt
        _ = (1 + Menv) * (a n) ^ (3 : ℕ) := by
          rw [haCube]
          ring
    calc
      |P.real {ζ : Fin n → Ω | z ≤ physical ζ} / Shao.standardNormalTail z - 1| ≤
          K * (β * Real.rpow (1 + z) p * Real.rpow (n : ℝ) (-((p - 2) / 2)) +
            (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ)) := hRateZ
      _ ≤ K * (B * Real.rpow (a n) p + (1 + Menv) * (a n) ^ (3 : ℕ)) :=
        mul_le_mul_of_nonneg_left (_root_.add_le_add hFirst hCubic) hK.le
      _ = E n := rfl
      _ ≤ ε := hErrorN

end
end Shao.OQ6.UniformPMomentGeneralSubcriticalWindowPhysicalRelativeConvergence
