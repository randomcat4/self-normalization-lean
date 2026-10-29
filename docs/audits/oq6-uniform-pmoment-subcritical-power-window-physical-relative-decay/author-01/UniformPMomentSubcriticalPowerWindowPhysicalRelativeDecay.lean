import Shao.OQ6.UniformPMomentSingleWindowPhysicalRelativePolynomialRate
import Shao.OQ6.OriginalEnvelopeRhoBound

set_option autoImplicit false
universe u
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology MeasureTheory symmDiff ENNReal
open Shao.OQ5.P51
namespace Shao.OQ6.UniformPMomentSubcriticalPowerWindowPhysicalRelativeDecay
noncomputable section

theorem uniform_pmoment_actual_original_subcritical_power_window_physical_relative_decay
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (B : ℝ) (hB : 1 ≤ B)
    (s : ℝ) (hs0 : 0 ≤ s) (hsq : s < (p - 2) / (2 * p))
    (cSZ C1 C2 C3 C4 : ℝ)
    (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
      cSZ C1 C2 C3 C4) :
    ∀ (Cenv aenv t0 Menv : ℝ)
      (hCenv : 0 ≤ Cenv) (haenv : 0 ≤ aenv)
      (ht0 : 0 < t0) (hMenv : 0 ≤ Menv),
    let δ : ℝ := (p - 2) / 2 - s * p
    let K0 : ℝ :=
      64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ))
    let K270 : ℝ := 8 * (1 + C1 + C2 + C3 + C4) * Real.exp C3 * (1 + K0)
    let K : ℝ := K270 * (B * Real.rpow (2 : ℝ) p + 8 * (1 + Menv))
    0 < δ ∧ 0 < K ∧
      ∃ N : ℕ, 4 ≤ N ∧
        ∀ (n : ℕ), N ≤ n →
          (1 : ℝ) ≤ Real.rpow (n : ℝ) s ∧
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
                (z : ℝ) (hz : 1 ≤ z)
                (hPowerWindow : z ≤ Real.rpow (n : ℝ) s),
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
                  K * Real.rpow (n : ℝ) (-δ)
:= by
  set_option maxHeartbeats 800000 in
    classical
    intro Cenv aenv t0 Menv hCenv haenv ht0 hMenv δ K0 K270 K
    have hp0 : 0 < p := lt_trans (by norm_num : (0 : ℝ) < 2) hp2
    have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
    let q : ℝ := (p - 2) / (2 * p)
    let cMoment : ℝ := Real.rpow (min (1 / 2 : ℝ) cSZ / 2) (1 / p)
    let cRemainder : ℝ := remainderWindowScale
      (Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv) t0
    let cAbsorb : ℝ := min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ))
    let cTilt : ℝ := 1 / (2 * Real.exp (1 / 2 : ℝ))
    let cGeometry : ℝ := 1 / (1 + Menv)
    let c : ℝ := min cMoment (min cRemainder (min cAbsorb (min cTilt cGeometry)))
    have h270 :=
      Shao.OQ6.UniformPMomentSingleWindowPhysicalRelativePolynomialRate.uniform_pmoment_actual_original_single_window_physical_relative_polynomial_rate.{u}
        p hp2 hp3 B hB cSZ C1 C2 C3 C4 hSZ
        Cenv aenv t0 Menv hCenv haenv ht0 hMenv
    dsimp only at h270
    change 0 < c ∧ 0 < K270 ∧ _ at h270
    rcases h270 with ⟨hc, hK270, N270, hN2704, hAll⟩
    have hqSixth : q ≤ (1 / 6 : ℝ) := by
      dsimp only [q]
      apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hp0)).2
      nlinarith only [hp3]
    have hsq' : s < q := hsq
    have hsHalf : s < (1 / 2 : ℝ) := by
      linarith only [hsq', hqSixth]
    have hsTimes : s * (2 * p) < p - 2 :=
      (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hp0)).mp hsq
    have hδ : 0 < δ := by
      dsimp only [δ]
      nlinarith only [hsTimes]
    have hδThree : δ ≤ (1 / 2 : ℝ) - 3 * s := by
      have hproduct : 0 ≤ (3 - p) * (1 / 2 - s) :=
        mul_nonneg (sub_nonneg.mpr hp3) (sub_nonneg.mpr hsHalf.le)
      dsimp only [δ]
      nlinarith only [hproduct]
    have hFactor : 0 < B * Real.rpow (2 : ℝ) p + 8 * (1 + Menv) := by
      have hTwoPower : 0 < Real.rpow (2 : ℝ) p :=
        Real.rpow_pos_of_pos (by norm_num) p
      positivity
    have hK : 0 < K := by
      dsimp only [K]
      exact mul_pos hK270 hFactor
    refine ⟨hδ, hK, ?_⟩
    -- This single additional threshold is selected before n and every model.
    let A : ℝ := c * Real.rpow B (-1 / p)
    have hA : 0 < A := mul_pos hc (Real.rpow_pos_of_pos hBpos _)
    have hgap : 0 < q - s := sub_pos.mpr hsq'
    have hnat : Filter.Tendsto (fun n : ℕ => (n : ℝ))
        Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
    have hpower : Filter.Tendsto
        (fun n : ℕ => Real.rpow (n : ℝ) (q - s))
        Filter.atTop Filter.atTop := (tendsto_rpow_atTop hgap).comp hnat
    have hPowerLarge : ∀ᶠ n : ℕ in Filter.atTop,
        (1 : ℝ) ≤ A * Real.rpow (n : ℝ) (q - s) := by
      filter_upwards [hpower.eventually_ge_atTop (1 / A)] with n hn
      have hscaled := (div_le_iff₀ hA).mp hn
      simpa only [mul_comm] using hscaled
    obtain ⟨Npower, hNpower⟩ := Filter.eventually_atTop.1 hPowerLarge
    refine ⟨max N270 Npower, hN2704.trans (le_max_left _ _), ?_⟩
    intro n hn
    have hn270 : N270 ≤ n := (le_max_left _ _).trans hn
    have hnPower : Npower ≤ n := (le_max_right _ _).trans hn
    have hn4 : 4 ≤ n := hN2704.trans hn270
    have hn1 : 1 ≤ n := by omega
    have hnPos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hns : (1 : ℝ) ≤ Real.rpow (n : ℝ) s := Real.one_le_rpow hnOne hs0
    have hnsNonneg : 0 ≤ Real.rpow (n : ℝ) s := Real.rpow_nonneg hnPos.le s
    have hnqNonneg : 0 ≤ Real.rpow (n : ℝ) q := Real.rpow_nonneg hnPos.le q
    have hCommonPowerWindow : Real.rpow (n : ℝ) s ≤
        c * Real.rpow B (-1 / p) * Real.rpow (n : ℝ) q := by
      calc
        Real.rpow (n : ℝ) s = 1 * Real.rpow (n : ℝ) s := (one_mul _).symm
        _ ≤ (A * Real.rpow (n : ℝ) (q - s)) * Real.rpow (n : ℝ) s :=
          mul_le_mul_of_nonneg_right (hNpower n hnPower) hnsNonneg
        _ = A * Real.rpow (n : ℝ) q := by
          have hsum : q - s + s = q := by ring
          rw [mul_assoc, ← Real.rpow_add hnPos, hsum]
        _ = c * Real.rpow B (-1 / p) * Real.rpow (n : ℝ) q := rfl
    refine ⟨hns, ?_⟩
    intro Ω mΩ μ hμ h hh hh2 hhsymm hcenter hprojectionsecond g r v rho β hgp hβBound
    have hModel := (hAll n hn270).2 μ h hh hh2 hhsymm hcenter
      hprojectionsecond hgp hβBound
    change 1 ≤ β ∧ _ at hModel
    rcases hModel with ⟨hβone, hβWindow, hTail⟩
    have hβpos : 0 < β := lt_of_lt_of_le zero_lt_one hβone
    have hNegativeExponent : -1 / p ≤ (0 : ℝ) := by
      apply (div_le_iff₀ hp0).2
      norm_num
    have hβB : Real.rpow B (-1 / p) ≤ Real.rpow β (-1 / p) :=
      Real.rpow_le_rpow_of_nonpos hβpos hβBound hNegativeExponent
    have hTruePowerWindow : Real.rpow (n : ℝ) s ≤
        c * Real.rpow β (-1 / p) * Real.rpow (n : ℝ) q :=
      hCommonPowerWindow.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hβB hc.le) hnqNonneg)
    intro w hW hWR hSq hSqBound hEnv z hz hPowerWindow mN P D1 physical
    have hWindow : z ≤ c * Real.rpow β (-1 / p) * Real.rpow (n : ℝ) q :=
      hPowerWindow.trans hTruePowerWindow
    have hTailRate := hTail w hW hWR hSq hSqBound hEnv z hz hWindow
    change |P.real {ζ : Fin n → Ω | z ≤ physical ζ} / Shao.standardNormalTail z - 1| ≤
      K270 * (β * Real.rpow (1 + z) p * Real.rpow (n : ℝ) (-((p - 2) / 2)) +
        (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ)) at hTailRate
    -- Extract product L2 for the very same original residual, at fixed (3,0).
    have hCanonical :=
      Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
        μ h hh hh2 hhsymm hcenter hprojectionsecond
        3 (by norm_num) 0 (by norm_num) (by positivity)
    dsimp only at hCanonical
    rcases hCanonical with
      ⟨hg, hg2, hgmean, hgsecond, hr, hr2, hsym, hcR, _⟩
    change MemLp (Function.uncurry r) 2 (μ.prod μ) at hr2
    have hRhoBound :=
      Shao.OQ6.OriginalEnvelopeRhoBound.original_residual_rho_le_envelope_second_moment
        μ r hr2 w hW hSq Menv hMenv hSqBound hEnv
    change 0 ≤ v ∧ v ≤ Menv ^ (2 : ℕ) ∧ 0 ≤ rho ∧ rho ≤ Menv at hRhoBound
    rcases hRhoBound with ⟨hvNonneg, hvBound, hrho, hrhoM⟩
    have hOneZ : 0 ≤ 1 + z := by linarith only [hz]
    have hAffine : 1 + z ≤ 2 * Real.rpow (n : ℝ) s := by
      linarith only [hns, hPowerWindow]
    have hProductPower : Real.rpow (2 * Real.rpow (n : ℝ) s) p =
        Real.rpow (2 : ℝ) p * Real.rpow (n : ℝ) (s * p) := by
      calc
        Real.rpow (2 * Real.rpow (n : ℝ) s) p =
            Real.rpow (2 : ℝ) p * Real.rpow (Real.rpow (n : ℝ) s) p :=
          Real.mul_rpow (by norm_num) hnsNonneg
        _ = Real.rpow (2 : ℝ) p * Real.rpow (n : ℝ) (s * p) := by
          rw [← Real.rpow_mul hnPos.le]
    have hAffineP : Real.rpow (1 + z) p ≤
        Real.rpow (2 : ℝ) p * Real.rpow (n : ℝ) (s * p) :=
      (Real.rpow_le_rpow hOneZ hAffine hp0.le).trans_eq hProductPower
    have hMomentExponent : s * p + -((p - 2) / 2) = -δ := by
      dsimp only [δ]
      ring
    have hMomentRate : β * Real.rpow (1 + z) p *
        Real.rpow (n : ℝ) (-((p - 2) / 2)) ≤
        (B * Real.rpow (2 : ℝ) p) * Real.rpow (n : ℝ) (-δ) := by
      calc
        β * Real.rpow (1 + z) p * Real.rpow (n : ℝ) (-((p - 2) / 2)) ≤
            (B * (Real.rpow (2 : ℝ) p * Real.rpow (n : ℝ) (s * p))) *
              Real.rpow (n : ℝ) (-((p - 2) / 2)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hβBound hAffineP (Real.rpow_nonneg hOneZ p) hBpos.le)
            (Real.rpow_nonneg hnPos.le _)
        _ = (B * Real.rpow (2 : ℝ) p) *
            (Real.rpow (n : ℝ) (s * p) * Real.rpow (n : ℝ) (-((p - 2) / 2))) := by
          ring
        _ = (B * Real.rpow (2 : ℝ) p) * Real.rpow (n : ℝ) (-δ) := by
          rw [← Real.rpow_add hnPos, hMomentExponent]
    have hCube : (1 + z) ^ (3 : ℕ) ≤ (2 * Real.rpow (n : ℝ) s) ^ (3 : ℕ) :=
      pow_le_pow_left₀ hOneZ hAffine 3
    have hCubePower : (Real.rpow (n : ℝ) s) ^ (3 : ℕ) =
        Real.rpow (n : ℝ) (3 * s) := by
      calc
        (Real.rpow (n : ℝ) s) ^ (3 : ℕ) =
            Real.rpow (n : ℝ) (s * (3 : ℝ)) :=
          (Real.rpow_mul_natCast hnPos.le s 3).symm
        _ = Real.rpow (n : ℝ) (3 * s) := by
          congr 1
          ring
    have hCubicNumerator : (1 + rho) * (1 + z) ^ (3 : ℕ) ≤
        (1 + Menv) * (2 * Real.rpow (n : ℝ) s) ^ (3 : ℕ) :=
      mul_le_mul (_root_.add_le_add (le_refl (1 : ℝ)) hrhoM) hCube
        (pow_nonneg hOneZ 3) (by linarith only [hMenv])
    have hCubicExponent : 3 * s - (1 / 2 : ℝ) ≤ -δ := by
      linarith only [hδThree]
    have hCubicRate : (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ) ≤
        (8 * (1 + Menv)) * Real.rpow (n : ℝ) (-δ) := by
      calc
        (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ) ≤
            (1 + Menv) * (2 * Real.rpow (n : ℝ) s) ^ 3 / Real.sqrt (n : ℝ) :=
          div_le_div_of_nonneg_right hCubicNumerator (Real.sqrt_nonneg _)
        _ = (8 * (1 + Menv)) *
            (Real.rpow (n : ℝ) (3 * s) / Real.rpow (n : ℝ) (1 / 2 : ℝ)) := by
          rw [mul_pow, hCubePower, Real.sqrt_eq_rpow]
          norm_num <;> ring
        _ = (8 * (1 + Menv)) * Real.rpow (n : ℝ) (3 * s - (1 / 2 : ℝ)) := by
          rw [Real.rpow_sub hnPos]
        _ ≤ (8 * (1 + Menv)) * Real.rpow (n : ℝ) (-δ) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hnOne hCubicExponent)
            (by linarith only [hMenv])
    calc
      |P.real {ζ : Fin n → Ω | z ≤ physical ζ} / Shao.standardNormalTail z - 1| ≤
          K270 * (β * Real.rpow (1 + z) p * Real.rpow (n : ℝ) (-((p - 2) / 2)) +
            (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ)) := hTailRate
      _ ≤ K270 * ((B * Real.rpow (2 : ℝ) p) * Real.rpow (n : ℝ) (-δ) +
          (8 * (1 + Menv)) * Real.rpow (n : ℝ) (-δ)) :=
        mul_le_mul_of_nonneg_left (_root_.add_le_add hMomentRate hCubicRate) hK270.le
      _ = K * Real.rpow (n : ℝ) (-δ) := by
        dsimp only [K]
        ring

end
end Shao.OQ6.UniformPMomentSubcriticalPowerWindowPhysicalRelativeDecay
