import Shao.OQ6.OriginalCurrentLevelPhysicalRelativePolynomialRate
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
universe u
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology MeasureTheory symmDiff
open Shao.OQ5.P51

namespace Shao.OQ6.OriginalSingleWindowPhysicalRelativePolynomialRate
noncomputable section
theorem actual_original_single_window_physical_relative_polynomial_rate
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ :=
      ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω mΩ mΩ μ μ)
    let rho : ℝ := Real.sqrt v
    ∀ (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
      (hgp : Integrable[mΩ] (fun o : Ω => Real.rpow |g o| p) μ)
      (cSZ C1 C2 C3 C4 : ℝ)
      (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
        cSZ C1 C2 C3 C4),
    ∀ (Cenv aenv t0 Menv : ℝ)
      (hCenv : 0 ≤ Cenv) (haenv : 0 ≤ aenv)
      (ht0 : 0 < t0) (hMenv : 0 ≤ Menv),
    let β : ℝ := ∫ o : Ω, Real.rpow |g o| p ∂μ
    let K0 : ℝ :=
      64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ))
    let Ktail : ℝ :=
      8 * (1 + C1 + C2 + C3 + C4) * Real.exp C3 * (1 + K0)
    ∃ c : ℝ, 0 < c ∧ 0 < Ktail ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        4 ≤ n ∧
        1 ≤ c * Real.rpow β (-1 / p) *
          Real.rpow (n : ℝ) ((p - 2) / (2 * p)) ∧
        ∀ (w : Ω → ℝ)
          (hW : ∀ᵐ o : Ω ∂μ, 0 ≤ w o)
          (hWR : ∀ᵐ o : Ω ∂μ, w o ≤ boundedPolylogHeight Cenv aenv n)
          (hSq : Integrable[mΩ] (fun o : Ω => (w o) ^ (2 : ℕ)) μ)
          (hSqBound : (∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ≤ Menv)
          (hEnv : ∀ᵐ t : Ω × Ω ∂(@Measure.prod Ω Ω mΩ mΩ μ μ),
            |r t.1 t.2| ≤ w t.1 * w t.2)
          (z : ℝ) (hz : 1 ≤ z)
          (hWindow : z ≤ c * Real.rpow β (-1 / p) *
            Real.rpow (n : ℝ) ((p - 2) / (2 * p))),
        let mN : MeasurableSpace (Fin n → Ω) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ)
        let P : @Measure (Fin n → Ω) mN :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mΩ) (fun _ : Fin n => μ)
        let D1 : (Fin n → Ω) → ℝ := residualStatisticD n r
        let physical : (Fin n → Ω) → ℝ := fun ζ =>
          if Real.sqrt (centeredSq n g r ζ) = 0 then 0 else
            (projectionW n g ζ + D1 ζ) / Real.sqrt (centeredSq n g r ζ)
        |P.real {ζ : Fin n → Ω | z ≤ physical ζ} / Shao.standardNormalTail z - 1| ≤
          Ktail * (β * Real.rpow (1 + z) p * Real.rpow (n : ℝ) (-((p - 2) / 2)) +
            (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ))
:= by
  set_option maxHeartbeats 800000 in
    classical
    intro g r v rho p hp2 hp3 hgp cSZ C1 C2 C3 C4 hSZ
      Cenv aenv t0 Menv hCenv haenv ht0 hMenv β K0 Ktail
    have hp0 : 0 < p := lt_trans (by norm_num : (0 : ℝ) < 2) hp2
    have hβnonneg : 0 ≤ β := by
      dsimp only [β]
      exact integral_nonneg (fun o : Ω => Real.rpow_nonneg (abs_nonneg (g o)) p)
    -- Unit second moment excludes the zero-moment branch internally.
    have hβpos : 0 < β := by
      by_contra hnot
      have hβzero : β = 0 := le_antisymm (le_of_not_gt hnot) hβnonneg
      have hfzero := (integral_eq_zero_iff_of_nonneg
        (fun o : Ω => Real.rpow_nonneg (abs_nonneg (g o)) p) hgp).1 hβzero
      have hgzero : g =ᵐ[μ] (fun _ : Ω => (0 : ℝ)) := by
        filter_upwards [hfzero] with o ho
        by_contra hgo
        exact (ne_of_gt (Real.rpow_pos_of_pos (abs_pos.mpr hgo) p)) ho
      have hsecondzero : (∫ o : Ω, (g o) ^ 2 ∂μ) = 0 := by
        calc
          _ = ∫ _o : Ω, (0 : ℝ) ∂μ := integral_congr_ae (by
            filter_upwards [hgzero] with o ho
            simp only [ho, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])
          _ = 0 := by simp
      have hsecondone : (∫ o : Ω, (g o) ^ 2 ∂μ) = 1 := hprojectionsecond
      exact one_ne_zero (hsecondone.symm.trans hsecondzero)
    have hcSZ : 0 < cSZ := hSZ.1
    have hC1 : 0 < C1 := hSZ.2.1
    have hC2 : 0 < C2 := hSZ.2.2.1
    have hC3 : 0 < C3 := hSZ.2.2.2.1
    have hC4 : 0 < C4 := hSZ.2.2.2.2.1
    have hK0 : 0 < K0 := by dsimp only [K0]; positivity
    have hKtail : 0 < Ktail := by dsimp only [Ktail]; positivity
    have hrho : 0 ≤ rho := Real.sqrt_nonneg v
    have honeRho : 0 < 1 + rho := by linarith only [hrho]
    let q : ℝ := (p - 2) / (2 * p)
    have hqpos : 0 < q := by
      dsimp only [q]
      exact div_pos (sub_pos.mpr hp2) (mul_pos (by norm_num) hp0)
    have hqSixth : q ≤ (1 / 6 : ℝ) := by
      dsimp only [q]
      apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hp0)).2
      nlinarith only [hp3]
    let cMoment : ℝ := Real.rpow (min (1 / 2 : ℝ) cSZ / 2) (1 / p)
    have hcMoment : 0 < cMoment :=
      Real.rpow_pos_of_pos
        (div_pos (lt_min (by norm_num : (0 : ℝ) < 1 / 2) hcSZ) (by norm_num)) _
    have hTailScale : 0 ≤ Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv := by
      unfold Shao.OQ6.BoundedProductEnvelopeTails.tailScale
      apply le_trans _ (le_max_left _ _)
      dsimp only [Shao.OQ6.BoundedProductEnvelopeTails.squareTailScale]
      exact mul_nonneg (Real.exp_pos _).le (by linarith only [hMenv])
    let cRemainder : ℝ := remainderWindowScale
      (Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv) t0
    have hcRemainder : 0 < cRemainder :=
      (remainderWindowScale_bounds _ _ hTailScale ht0).1
    let cAbsorb : ℝ := min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ))
    have hcAbsorb : 0 < cAbsorb :=
      lt_min zero_lt_one (div_pos (Real.sqrt_pos.mpr ht0) (by norm_num))
    let cTilt : ℝ := 1 / (2 * Real.exp (1 / 2 : ℝ))
    have hcTilt : 0 < cTilt := by dsimp only [cTilt]; positivity
    let cGeometry : ℝ := 1 / (1 + rho)
    have hcGeometry : 0 < cGeometry := one_div_pos.mpr honeRho
    let cOther : ℝ := min cRemainder (min cAbsorb (min cTilt cGeometry))
    have hcOther : 0 < cOther :=
      lt_min hcRemainder (lt_min hcAbsorb (lt_min hcTilt hcGeometry))
    have hOtherRemainder : cOther ≤ cRemainder := min_le_left _ _
    have hOtherPair : cOther ≤ min cAbsorb (min cTilt cGeometry) := min_le_right _ _
    have hOtherAbsorb : cOther ≤ cAbsorb := hOtherPair.trans (min_le_left _ _)
    have hOtherTail : cOther ≤ min cTilt cGeometry := hOtherPair.trans (min_le_right _ _)
    have hOtherTilt : cOther ≤ cTilt := hOtherTail.trans (min_le_left _ _)
    have hOtherGeometry : cOther ≤ cGeometry := hOtherTail.trans (min_le_right _ _)
    let c : ℝ := min cMoment (cOther * Real.rpow β (1 / p))
    have hc : 0 < c := lt_min hcMoment
      (mul_pos hcOther (Real.rpow_pos_of_pos hβpos _))
    have hcMomentBound : c ≤ cMoment := min_le_left _ _
    have hcOtherBound : c ≤ cOther * Real.rpow β (1 / p) := min_le_right _ _
    have hβinverse : 0 < Real.rpow β (-1 / p) := Real.rpow_pos_of_pos hβpos _
    have hβcancel : Real.rpow β (1 / p) * Real.rpow β (-1 / p) = 1 := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hβpos]
      have hexponent : (1 / p : ℝ) + (-1 / p) = 0 := by ring
      rw [hexponent, Real.rpow_zero]
    let A : ℝ := c * Real.rpow β (-1 / p)
    have hA : 0 < A := mul_pos hc hβinverse
    -- Cancellation is valid for every positive beta, including beta below one.
    have hAOther : A ≤ cOther := by
      calc
        A ≤ (cOther * Real.rpow β (1 / p)) * Real.rpow β (-1 / p) :=
          mul_le_mul_of_nonneg_right hcOtherBound hβinverse.le
        _ = cOther := by rw [mul_assoc, hβcancel, mul_one]
    have hAMoment : A ≤ cMoment * Real.rpow β (-1 / p) :=
      mul_le_mul_of_nonneg_right hcMomentBound hβinverse.le
    have hnat : Filter.Tendsto (fun n : ℕ => (n : ℝ))
        Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
    have hpower : Filter.Tendsto (fun n : ℕ => Real.rpow (n : ℝ) q)
        Filter.atTop Filter.atTop := (tendsto_rpow_atTop hqpos).comp hnat
    have hnonempty : ∀ᶠ n : ℕ in Filter.atTop,
        1 ≤ A * Real.rpow (n : ℝ) q := by
      filter_upwards [hpower.eventually_ge_atTop (1 / A)] with n hn
      have hscaled := (div_le_iff₀ hA).mp hn
      simpa only [mul_comm] using hscaled
    have hUpstream :=
      Shao.OQ6.OriginalCurrentLevelPhysicalRelativePolynomialRate.actual_original_current_level_physical_relative_polynomial_rate
        μ h hh hh2 hhsymm hcenter hprojectionsecond
    dsimp only at hUpstream
    rcases hUpstream with ⟨cg, hcg, hAll⟩
    refine ⟨c, hc, hKtail, ?_⟩
    filter_upwards [hAll Cenv aenv t0 Menv hCenv haenv ht0 hMenv, hnonempty]
      with n hn hnonemptyN
    refine ⟨hn.1, hnonemptyN, ?_⟩
    intro w hW hWR hSq hSqBound hEnv z hz hWindow
    change z ≤ A * Real.rpow (n : ℝ) q at hWindow
    have hnOne : 1 ≤ n := Nat.le_trans (by norm_num : (1 : ℕ) ≤ 4) hn.1
    have hnRealOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnOne
    have hnPower : 0 ≤ Real.rpow (n : ℝ) q := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hnSixth : 0 ≤ Real.rpow (n : ℝ) (1 / 6 : ℝ) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hPowerSixth : Real.rpow (n : ℝ) q ≤ Real.rpow (n : ℝ) (1 / 6 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hnRealOne hqSixth
    have hSixthSqrt : Real.rpow (n : ℝ) (1 / 6 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      calc
        Real.rpow (n : ℝ) (1 / 6 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hnRealOne (by norm_num : (1 / 6 : ℝ) ≤ 1 / 2)
        _ = Real.sqrt (n : ℝ) := (Real.sqrt_eq_rpow _).symm
    have hBaseWindow : z ≤ cOther * Real.rpow (n : ℝ) q :=
      hWindow.trans (mul_le_mul_of_nonneg_right hAOther hnPower)
    have hSixthWindow : z ≤ cOther * Real.rpow (n : ℝ) (1 / 6 : ℝ) :=
      hBaseWindow.trans (mul_le_mul_of_nonneg_left hPowerSixth hcOther.le)
    have hSqrtWindow : z ≤ cOther * Real.sqrt (n : ℝ) :=
      hSixthWindow.trans (mul_le_mul_of_nonneg_left hSixthSqrt hcOther.le)
    have hEnvelopeWindow : z ≤ remainderWindowScale
        (Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv) t0 *
          Real.rpow (n : ℝ) (1 / 6 : ℝ) :=
      hSixthWindow.trans (mul_le_mul_of_nonneg_right hOtherRemainder hnSixth)
    have hAbsorptionWindow : z ≤ min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ)) *
        Real.rpow (n : ℝ) (1 / 6 : ℝ) :=
      hSixthWindow.trans (mul_le_mul_of_nonneg_right hOtherAbsorb hnSixth)
    have hTiltWindow : z ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ)) := by
      calc
        z ≤ cTilt * Real.sqrt (n : ℝ) :=
          hSqrtWindow.trans
            (mul_le_mul_of_nonneg_right hOtherTilt (Real.sqrt_nonneg _))
        _ = Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ)) := by
          dsimp only [cTilt]
          ring
    have hGeometryWindow : z ≤ cGeometry * Real.sqrt (n : ℝ) :=
      hSqrtWindow.trans
        (mul_le_mul_of_nonneg_right hOtherGeometry (Real.sqrt_nonneg _))
    have hGeometry : (1 + rho) * z ≤ Real.sqrt (n : ℝ) := by
      calc
        (1 + rho) * z ≤ (1 + rho) * (cGeometry * Real.sqrt (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hGeometryWindow honeRho.le
        _ = Real.sqrt (n : ℝ) := by
          dsimp only [cGeometry]
          field_simp [honeRho.ne']
    have hMomentWindow : β = 0 ∨ (0 < β ∧
        z ≤ cMoment * Real.rpow β (-1 / p) * Real.rpow (n : ℝ) q) :=
      Or.inr ⟨hβpos, hWindow.trans (mul_le_mul_of_nonneg_right hAMoment hnPower)⟩
    -- The original law, physical zero convention and explicit Ktail are unchanged.
    have hCurrent := hn.2 w hW hWR hSq hSqBound hEnv z hz
      hTiltWindow hEnvelopeWindow hGeometry hAbsorptionWindow
      p hp2 hp3 hgp cSZ C1 C2 C3 C4 hSZ
    exact (hCurrent hMomentWindow).2
end
end Shao.OQ6.OriginalSingleWindowPhysicalRelativePolynomialRate
