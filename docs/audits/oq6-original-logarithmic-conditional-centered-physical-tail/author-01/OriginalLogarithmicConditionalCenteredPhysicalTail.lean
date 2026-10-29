import Shao.OQ6.LogarithmicConditionalRates
import Shao.OQ6.ConditionalStandardizedPMoment
import Shao.OQ6.ConditionalStandardizedLowEnergy
import Shao.OQ6.ConditionalUniformStandardizedResidual
import Shao.OQ6.UniformPMomentSingleWindowPhysicalRelativePolynomialRate
import Shao.OQ6.FiniteRows

set_option autoImplicit false
universe u
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology MeasureTheory ENNReal
open Shao.OQ5.P51
namespace Shao.OQ6.OriginalLogarithmicConditionalCenteredPhysicalTail
noncomputable section
theorem actual_original_logarithmic_conditional_standardized_model_and_centered_physical_tail
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond : (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (w : Ω → ℝ) (hw : Measurable w)
    (hwone : ∀ᵐ o ∂μ, 1 ≤ w o)
    (α τ : ℝ) (hα : 0 < α) (hτ : 0 < τ)
    (hwexp : Integrable (fun o => Real.exp (τ * Real.rpow (w o) α)) μ)
    (henvelope : ∀ᵐ z : Ω × Ω ∂(μ.prod μ),
      |h z.1 z.2 - (∫ y, h z.1 y ∂μ) - (∫ y, h z.2 y ∂μ)| ≤
        w z.1 * w z.2)
    (p : ℝ) (hp : 2 < p ∧ p ≤ 3)
    (hgp : Integrable (fun o => Real.rpow |∫ y, h o y ∂μ| p) μ)
    (J : ℝ) (hJ : 0 ≤ J)
    (cSZ C1 C2 C3 C4 : ℝ)
    (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
      cSZ C1 C2 C3 C4)
    (t0 : ℝ) (ht0 : 0 < t0) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
    let B : ℝ := Real.rpow β (1 / p)
    let M2 : ℝ := ∫ o, w o ^ 2 ∂μ
    let W2 : ℝ := Real.sqrt M2
    let Mexp : ℝ := ∫ o, Real.exp (τ * Real.rpow (w o) α) ∂μ
    let e : ℝ := 1 - 2 / p
    let t : ℝ := 1 - 1 / p
    let A : ℝ := 2 * (J + 1) / e
    let qpow : ℝ := (p - 2) / (2 * p)
    let Cvar : ℝ := 32 * (1 + B ^ 2 + W2 ^ 2)
    let Cmean : ℝ := 4 * (1 + B)
    let Kvar : ℝ := Cvar *
      (Real.rpow Mexp e + W2 * Real.sqrt Mexp + W2 ^ 2 * Mexp)
    let Kmean : ℝ := Cmean * (Real.rpow Mexp t + W2 ^ 2 * Mexp)
    let Cenv : ℝ := 2 * (1 + 2 * W2) ^ 2
    let RhoBound : ℝ := 4 * Cenv ^ 2 * M2 ^ 2
    let wstd : Ω → ℝ := fun o => Real.sqrt Cenv * w o
    let Menv : ℝ := 2 * Cenv * M2
    let Cpoly : ℝ := Real.sqrt Cenv * Real.rpow (2 * A / τ) (1 / α)
    let apoly : ℝ := 1 / α
    1 ≤ β ∧ 0 < A ∧ 0 < Cenv ∧ 0 ≤ Menv ∧ 0 ≤ Cpoly ∧ 0 < apoly ∧
      ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
      ∃ N : ℕ, 8 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
      let Rn : ℝ := Real.rpow (A * Real.log (n : ℝ) / τ) (1 / α)
      let Cn : Set Ω := {o : Ω | w o ≤ Rn}
      let dn : ℝ := μ.real Cn
      let νn : Measure Ω := (μ Cn)⁻¹ • μ.restrict Cn
      (2 : ℝ) ≤ c * Real.rpow (n : ℝ) qpow ∧
        MeasurableSet Cn ∧ (1 / 2 : ℝ) ≤ dn ∧
        IsProbabilityMeasure νn ∧ νn ≪ μ ∧
        (νn.prod νn) ≪ (μ.prod μ) ∧ νn Cn = 1 ∧
        (∀ᵐ o ∂μ,
          (w o ≤ Rn ↔ τ * Real.rpow (w o) α ≤ A * Real.log (n : ℝ))) ∧
        (∀ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 →
          let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
          let κ : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(νn.prod νn)
          let G : Ω → ℝ := fun o => (∫ y, H o y ∂νn) - κ
          let σ2 : ℝ := ∫ o, G o ^ 2 ∂νn
          let σ : ℝ := Real.sqrt σ2
          let Kcond : Ω → Ω → ℝ := fun o y => H o y - κ - G o - G y
          let Hstd : Ω → Ω → ℝ := fun o y => (H o y - κ) / σ
          let gstd : Ω → ℝ := fun o => ∫ y, Hstd o y ∂νn
          let rstd : Ω → Ω → ℝ := fun o y => Hstd o y - gstd o - gstd y
          let βstd : ℝ := ∫ o, Real.rpow |gstd o| p ∂νn
          let ρstd : ℝ := Real.sqrt
            (∫ z : Ω × Ω, rstd z.1 z.2 ^ 2 ∂(νn.prod νn))
          (1 / 2 : ℝ) ≤ σ2 ∧ σ2 ≤ (3 / 2 : ℝ) ∧
            (1 / 2 : ℝ) ≤ σ ∧ 0 < σ ∧ σ ^ 2 = σ2 ∧
            |σ2 - 1| ≤ Kvar * Real.rpow (n : ℝ) (-J) ∧
            Measurable (fun z : Ω × Ω => Hstd z.1 z.2) ∧
            MemLp (fun z : Ω × Ω => Hstd z.1 z.2) 2 (νn.prod νn) ∧
            (∀ o y, Hstd o y = Hstd y o) ∧
            (∫ z : Ω × Ω, Hstd z.1 z.2 ∂(νn.prod νn)) = 0 ∧
            (∫ o, (∫ y, Hstd o y ∂νn) ^ 2 ∂νn) = 1 ∧
            Measurable gstd ∧ MemLp gstd 2 νn ∧
            (∫ o, gstd o ∂νn) = 0 ∧
            (∀ᵐ o ∂νn, gstd o = G o / σ) ∧
            (∀ᵐ z : Ω × Ω ∂(νn.prod νn),
              rstd z.1 z.2 = Kcond z.1 z.2 / σ) ∧
            Integrable (fun o => Real.rpow |gstd o| p) νn ∧
            1 ≤ βstd ∧ βstd ≤ 2 * β ∧
            MemLp (fun z : Ω × Ω => rstd z.1 z.2) 2 (νn.prod νn) ∧
            (∀ᵐ o ∂νn, (∫ y, rstd o y ∂νn) = 0) ∧
            0 ≤ ρstd ∧ ρstd ≤ Real.sqrt RhoBound ∧
            Measurable wstd ∧ (∀ᵐ o ∂νn, 0 ≤ wstd o) ∧
            Integrable (fun o => wstd o ^ 2) νn ∧
            (∫ o, wstd o ^ 2 ∂νn) ≤ Menv ∧
            (∀ᵐ z : Ω × Ω ∂(νn.prod νn),
              |rstd z.1 z.2| ≤ wstd z.1 * wstd z.2) ∧
            (∀ m : ℕ, n ≤ 2 * m → m ≤ n →
              let P : Measure (Fin m → Ω) := Measure.pi (fun _ : Fin m => νn)
              let Pμ : Measure (Fin m → Ω) := Measure.pi (fun _ : Fin m => μ)
              let allGood : Set (Fin m → Ω) := {ζ | ∀ i : Fin m, ζ i ∈ Cn}
              let sampleH : (Fin m → Ω) → Fin m → Fin m → ℝ :=
                fun ζ i j => H (ζ i) (ζ j)
              let U : (Fin m → Ω) → ℝ :=
                fun ζ => Shao.OQ6.FiniteRows.uStatistic (sampleH ζ)
              let RH : (Fin m → Ω) → ℝ :=
                fun ζ => Real.sqrt (Shao.OQ6.FiniteRows.jackknifeSq (sampleH ζ))
              let sstd : (Fin m → Ω) → ℝ :=
                fun ζ => Real.sqrt (centeredSq m gstd rstd ζ)
              let Tstd : (Fin m → Ω) → ℝ := fun ζ =>
                if sstd ζ = 0 then 0 else
                  (projectionW m gstd ζ + residualStatisticD m rstd ζ) / sstd ζ
              let Tcenter : (Fin m → Ω) → ℝ := fun ζ =>
                if RH ζ = 0 then 0 else Real.sqrt (m : ℝ) * (U ζ - κ) / RH ζ
              let Tuncenter : (Fin m → Ω) → ℝ := fun ζ =>
                if RH ζ = 0 then 0 else Real.sqrt (m : ℝ) * U ζ / RH ζ
              4 ≤ m ∧ IsProbabilityMeasure P ∧ IsProbabilityMeasure Pμ ∧
                MeasurableSet allGood ∧ Pμ.real allGood = dn ^ m ∧
                P = (Pμ allGood)⁻¹ • Pμ.restrict allGood ∧
                (∀ E : Set (Fin m → Ω), MeasurableSet E →
                  P.real E = Pμ.real (E ∩ allGood) / dn ^ m) ∧
                (∀ᵐ o ∂νn, wstd o ≤ boundedPolylogHeight Cpoly apoly m) ∧
                Real.sqrt (m : ℝ) * |κ| ≤ Kmean * Real.rpow (n : ℝ) (-J) ∧
                Measurable Tcenter ∧ Measurable Tuncenter ∧ Measurable Tstd ∧
                (∀ ζ : Fin m → Ω,
                  RH ζ = 2 * σ * sstd ζ ∧ Tcenter ζ = Tstd ζ ∧
                  Tuncenter ζ = (if RH ζ = 0 then 0 else
                    Tstd ζ + Real.sqrt (m : ℝ) * κ / RH ζ)) ∧
                Measure.map Tcenter P = Measure.map Tstd P ∧
                (∀ z : ℝ, 1 ≤ z → z ≤ c * Real.rpow (n : ℝ) qpow →
                  |P.real {ζ : Fin m → Ω | z ≤ Tcenter ζ} /
                      Shao.standardNormalTail z - 1| ≤
                    K * (β * Real.rpow (1 + z) p *
                      Real.rpow (n : ℝ) (-((p - 2) / 2)) +
                      (1 + z) ^ 3 / Real.sqrt (n : ℝ)))))
 := by
  classical
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
  let B : ℝ := Real.rpow β (1 / p)
  let M2 : ℝ := ∫ o, w o ^ 2 ∂μ
  let W2 : ℝ := Real.sqrt M2
  let Mexp : ℝ := ∫ o, Real.exp (τ * Real.rpow (w o) α) ∂μ
  let e : ℝ := 1 - 2 / p
  let t : ℝ := 1 - 1 / p
  let A : ℝ := 2 * (J + 1) / e
  let qpow : ℝ := (p - 2) / (2 * p)
  let Cvar : ℝ := 32 * (1 + B ^ 2 + W2 ^ 2)
  let Cmean : ℝ := 4 * (1 + B)
  let Kvar : ℝ := Cvar *
    (Real.rpow Mexp e + W2 * Real.sqrt Mexp + W2 ^ 2 * Mexp)
  let Kmean : ℝ := Cmean * (Real.rpow Mexp t + W2 ^ 2 * Mexp)
  let Cenv : ℝ := 2 * (1 + 2 * W2) ^ 2
  let RhoBound : ℝ := 4 * Cenv ^ 2 * M2 ^ 2
  let wstd : Ω → ℝ := fun o => Real.sqrt Cenv * w o
  let Menv : ℝ := 2 * Cenv * M2
  let Cpoly : ℝ := Real.sqrt Cenv * Real.rpow (2 * A / τ) (1 / α)
  let apoly : ℝ := 1 / α
  change 1 ≤ β ∧ 0 < A ∧ 0 < Cenv ∧ 0 ≤ Menv ∧ 0 ≤ Cpoly ∧ 0 < apoly ∧ _
  -- The original qualitative p-moment theorem is used through its qualified
  -- normalized low-energy consumer. No polynomial p-moment convergence is used.
  rcases Shao.OQ6.ConditionalStandardizedLowEnergy.actual_conditional_standardized_low_energy
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone α τ hα hτ
      hwexp henvelope p hp hgp with
    ⟨hβ, _, _, _, _, _, _, Nlow, hNlow, hlow⟩
  rcases Shao.OQ6.ConditionalUniformStandardizedResidual.actual_conditional_uniform_standardized_residual
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone α τ hα hτ
      hwexp henvelope p hp hgp with
    ⟨hw2μ, hwSqμ, hM2, hW2, hW2sq, hCenv, hRhoBound, Nres, hNres, hres⟩
  rcases Shao.OQ6.LogarithmicConditionalRates.actual_logarithmic_conditional_rates
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone α τ hα hτ
      hwexp henvelope p hp hgp J hJ with
    ⟨he, heupper, het, hA, hMexpLower, hMexp, hJAe, hJAhalf,
      hJA, hJAt, hJAmean, hrate⟩
  have hp0 : 0 < p := by linarith [hp.1]
  have hβpos : 0 < β := by linarith
  have hβ0 : 0 ≤ β := hβpos.le
  have hM20 : 0 ≤ M2 := by linarith
  have hq : 0 < qpow := div_pos (sub_pos.mpr hp.1) (by positivity)
  have hapoly : 0 < apoly := one_div_pos.mpr hα
  have hMenv : 0 ≤ Menv := by dsimp only [Menv]; positivity
  have hCpoly : 0 ≤ Cpoly := by dsimp only [Cpoly]; positivity
  have hBudget : 1 ≤ 2 * β := by linarith
  have hEngine :=
    Shao.OQ6.UniformPMomentSingleWindowPhysicalRelativePolynomialRate.uniform_pmoment_actual_original_single_window_physical_relative_polynomial_rate
      p hp.1 hp.2 (2 * β) hBudget cSZ C1 C2 C3 C4 hSZ
      Cpoly apoly t0 Menv hCpoly hapoly.le ht0 hMenv
  -- These are exactly the constants returned by unit270; they precede every
  -- member of the original conditional family.
  let c270 : ℝ := min
    (Real.rpow (min (1 / 2 : ℝ) cSZ / 2) (1 / p))
    (min
      (remainderWindowScale (Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv) t0)
      (min (min (1 : ℝ) (Real.sqrt t0 / 2))
        (min (1 / (2 * Real.exp (1 / 2 : ℝ))) (1 / (1 + Menv)))))
  let K270 : ℝ := 8 * (1 + C1 + C2 + C3 + C4) * Real.exp C3 *
    (1 + 64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)))
  change 0 < c270 ∧ 0 < K270 ∧ _ at hEngine
  rcases hEngine with ⟨hc270, hK270, N270, hN270, hEngine⟩
  let c : ℝ := c270 * Real.rpow (2 * β) (-1 / p) / Real.rpow 2 qpow
  let a : ℝ := (p - 2) / 2
  let L1 : ℝ := 2 * Real.rpow 2 a
  let L2 : ℝ := Real.sqrt 2 * (1 + Real.sqrt RhoBound)
  let K : ℝ := K270 * (L1 + L2)
  have ha : 0 < a := by dsimp only [a]; linarith [hp.1]
  have hc : 0 < c := by
    dsimp only [c]
    exact div_pos (mul_pos hc270 (Real.rpow_pos_of_pos (by linarith) _))
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hL1 : 0 < L1 := by dsimp only [L1]; positivity
  have hL2 : 0 < L2 := by dsimp only [L2]; positivity
  have hK : 0 < K := mul_pos hK270 (add_pos hL1 hL2)
  let Nrate : ℕ := Nat.ceil (max (3 : ℝ) (Real.rpow (2 * Mexp) (1 / A)))
  have hnat : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hnat
  have hRn : Filter.Tendsto
      (fun n : ℕ => Real.rpow (A * Real.log (n : ℝ) / τ) (1 / α))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hapoly).comp ((hlog.const_mul_atTop hA).atTop_div_const hτ)
  obtain ⟨Ncut, hNcut⟩ := Filter.eventually_atTop.1
    (hRn.eventually_ge_atTop (max (Nlow : ℝ) (Nres : ℝ)))
  have hPower : Filter.Tendsto (fun n : ℕ => Real.rpow (n : ℝ) qpow)
      Filter.atTop Filter.atTop := (tendsto_rpow_atTop hq).comp hnat
  have hWindowNonempty : ∀ᶠ n : ℕ in Filter.atTop,
      (2 : ℝ) ≤ c * Real.rpow (n : ℝ) qpow := by
    filter_upwards [hPower.eventually_ge_atTop (2 / c)] with n hn
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hn
  obtain ⟨Nwin, hNwin⟩ := Filter.eventually_atTop.1 hWindowNonempty
  let N : ℕ := max 8 (max Nrate (max Ncut (max Nwin (2 * N270))))
  refine ⟨hβ, hA, hCenv, hMenv, hCpoly, hapoly, c, K, hc, hK,
    N, le_max_left _ _, ?_⟩
  intro n hn
  have hn8 : 8 ≤ n := (le_max_left 8 _).trans hn
  have hnRest : max Nrate (max Ncut (max Nwin (2 * N270))) ≤ n :=
    (le_max_right 8 _).trans hn
  have hnRate : Nrate ≤ n := (le_max_left _ _).trans hnRest
  have hnCut : Ncut ≤ n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hnRest)
  have hnWin : Nwin ≤ n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hnRest))
  have hn270 : 2 * N270 ≤ n :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hnRest))
  let Rn : ℝ := Real.rpow (A * Real.log (n : ℝ) / τ) (1 / α)
  let Cn : Set Ω := {o | w o ≤ Rn}
  let dn : ℝ := μ.real Cn
  let νn : Measure Ω := (μ Cn)⁻¹ • μ.restrict Cn
  change (2 : ℝ) ≤ c * Real.rpow (n : ℝ) qpow ∧ _
  have hcut := hNcut n hnCut
  have hlowN : (Nlow : ℝ) ≤ Rn := (le_max_left _ _).trans hcut
  have hresN : (Nres : ℝ) ≤ Rn := (le_max_right _ _).trans hcut
  rcases hres Rn hresN with
    ⟨hCn, hdn, hνn, hνac, hνprodac, hνCn, hwCut, hw2ν, hwSqν,
      hMν0, hMνBound, hb0, hbBound, hc0, hcBound, hwPair2, hwPairSq,
      hwPairSqMean, hresLam⟩
  letI : IsProbabilityMeasure νn := hνn
  rcases hlow Rn hlowN with
    ⟨_, _, _, _, _, hlowLam⟩
  rcases hrate n hnRate with
    ⟨hn3, hRnPos, _, hlogCut, hπ0, hπBound, hπHalf, hdnIdentity,
      _, _, _, hbn0, hbnSq, hbnBound, hrateLam⟩
  refine ⟨hNwin n hnWin, hCn, hdn, hνn, hνac, hνprodac, hνCn, hlogCut, ?_⟩
  intro lam hLam
  let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
  let κ : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(νn.prod νn)
  let G : Ω → ℝ := fun o => (∫ y, H o y ∂νn) - κ
  let σ2 : ℝ := ∫ o, G o ^ 2 ∂νn
  let σ : ℝ := Real.sqrt σ2
  let Kcond : Ω → Ω → ℝ := fun o y => H o y - κ - G o - G y
  let Hstd : Ω → Ω → ℝ := fun o y => (H o y - κ) / σ
  let gstd : Ω → ℝ := fun o => ∫ y, Hstd o y ∂νn
  let rstd : Ω → Ω → ℝ := fun o y => Hstd o y - gstd o - gstd y
  let βstd : ℝ := ∫ o, Real.rpow |gstd o| p ∂νn
  let ρstd : ℝ := Real.sqrt
    (∫ z : Ω × Ω, rstd z.1 z.2 ^ 2 ∂(νn.prod νn))
  change (1 / 2 : ℝ) ≤ σ2 ∧ σ2 ≤ (3 / 2 : ℝ) ∧ _
  rcases hresLam lam hLam with
    ⟨hHm, hH2, hGm, hG2, hGSq, hGzero, hσ2low, hσ2up, hσlow,
      hσ, hσsq, hKm, hK2, hKsym, hKstdm, hKstd2, hKstdSq,
      hKstdsym, hKstdRows, hKstdMean, hKstdEnv, hKstdBound, hρ20, hρ2Bound⟩
  rcases hlowLam lam hLam with
    ⟨_, _, _, _, _, _, _, _, hXm, hXp, hX2, hXSq, hXsecond,
      hXpmoment, hXβBound, hLowEnergy⟩
  rcases hrateLam lam hLam with ⟨_, _, _, hVarianceRate, hMeanRate⟩
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hH1 : Integrable (fun z : Ω × Ω => H z.1 z.2) (νn.prod νn) :=
    hH2.integrable (by norm_num)
  have hHsym : ∀ o y, H o y = H y o := by
    intro o y
    dsimp only [H, r]
    rw [hhsymm o y]
    ring
  have hHstdm : Measurable (fun z : Ω × Ω => Hstd z.1 z.2) :=
    (hHm.sub measurable_const).div_const σ
  have hHstd2 : MemLp (fun z : Ω × Ω => Hstd z.1 z.2) 2 (νn.prod νn) := by
    simpa only [Hstd, div_eq_mul_inv, mul_comm] using
      (hH2.sub (memLp_const κ)).const_mul σ⁻¹
  have hHstdsym : ∀ o y, Hstd o y = Hstd y o := by
    intro o y
    dsimp only [Hstd]
    rw [hHsym o y]
  have hHstdMean : (∫ z : Ω × Ω, Hstd z.1 z.2 ∂(νn.prod νn)) = 0 := by
    change (∫ z : Ω × Ω, (H z.1 z.2 - κ) / σ ∂(νn.prod νn)) = 0
    rw [integral_div, integral_sub hH1 (integrable_const κ)]
    simp only [integral_const, probReal_univ, one_smul]
    change (κ - κ) / σ = 0
    ring
  have hgstdm : Measurable gstd :=
    hHstdm.stronglyMeasurable.integral_prod_right'.measurable
  -- Only almost-everywhere row linearity is used here.
  have hgstdAE : ∀ᵐ o ∂νn, gstd o = G o / σ := by
    filter_upwards [hH1.prod_right_ae] with o ho
    change (∫ y, (H o y - κ) / σ ∂νn) = ((∫ y, H o y ∂νn) - κ) / σ
    rw [integral_div, integral_sub ho (integrable_const κ)]
    simp only [integral_const, probReal_univ, one_smul]
  have hgstd2 : MemLp gstd 2 νn := (memLp_congr_ae hgstdAE).2 hX2
  have hgstdzero : (∫ o, gstd o ∂νn) = 0 := by
    rw [integral_congr_ae hgstdAE, integral_div, hGzero, zero_div]
  have hgstdSecond : (∫ o, gstd o ^ 2 ∂νn) = 1 := by
    calc
      _ = ∫ o, (G o / σ) ^ 2 ∂νn := integral_congr_ae (hgstdAE.mono (by
        intro o ho; rw [ho]))
      _ = 1 := hXsecond
  have hgstdpAE : (fun o => Real.rpow |gstd o| p) =ᵐ[νn]
      (fun o => Real.rpow |G o / σ| p) := hgstdAE.mono (by intro o ho; rw [ho])
  have hgstdp : Integrable (fun o => Real.rpow |gstd o| p) νn :=
    (integrable_congr hgstdpAE).2 hXpmoment
  have hβstdBound : βstd ≤ 2 * β := by
    change (∫ o, Real.rpow |gstd o| p ∂νn) ≤ 2 * β
    rw [integral_congr_ae hgstdpAE]
    exact hXβBound
  have hrstdm : Measurable (fun z : Ω × Ω => rstd z.1 z.2) :=
    (hHstdm.sub (hgstdm.comp measurable_fst)).sub (hgstdm.comp measurable_snd)
  have hrstdsym : ∀ o y, rstd o y = rstd y o := by
    intro o y
    dsimp only [rstd]
    rw [hHstdsym o y]
    ring
  have hrstdAE : ∀ᵐ z : Ω × Ω ∂(νn.prod νn),
      rstd z.1 z.2 = Kcond z.1 z.2 / σ := by
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hgstdAE,
      measurePreserving_snd.quasiMeasurePreserving.ae hgstdAE] with z hz1 hz2
    dsimp only [rstd, Hstd, Kcond]
    rw [hz1, hz2]
    ring
  have hrstd2 : MemLp (fun z : Ω × Ω => rstd z.1 z.2) 2 (νn.prod νn) :=
    (memLp_congr_ae hrstdAE).2 hKstd2
  have hrstdCan : ∀ᵐ o ∂νn, (∫ y, rstd o y ∂νn) = 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod hrstdAE, hKstdRows] with o ho hrow
    exact (integral_congr_ae ho).trans hrow.2
  have hρSq : (∫ z : Ω × Ω, rstd z.1 z.2 ^ 2 ∂(νn.prod νn)) =
      ∫ z : Ω × Ω, (Kcond z.1 z.2 / σ) ^ 2 ∂(νn.prod νn) :=
    integral_congr_ae (hrstdAE.mono (by intro z hz; rw [hz]))
  have hρ : ρstd ≤ Real.sqrt RhoBound := by
    dsimp only [ρstd]
    rw [hρSq]
    exact Real.sqrt_le_sqrt hρ2Bound
  have hwstdm : Measurable wstd := hw.const_mul _
  have hwstd0 : ∀ᵐ o ∂νn, 0 ≤ wstd o := by
    filter_upwards [hwCut] with o ho
    exact mul_nonneg (Real.sqrt_nonneg _) (by linarith [ho.1])
  have hwstdSqEq : (fun o => wstd o ^ 2) = (fun o => Cenv * w o ^ 2) := by
    funext o
    dsimp only [wstd]
    rw [mul_pow, Real.sq_sqrt hCenv.le]
  have hwstdSq : Integrable (fun o => wstd o ^ 2) νn := by
    rw [hwstdSqEq]
    exact hwSqν.const_mul Cenv
  have hwstdSqBound : (∫ o, wstd o ^ 2 ∂νn) ≤ Menv := by
    rw [hwstdSqEq, integral_const_mul]
    exact mul_le_mul_of_nonneg_left hMνBound hCenv.le
  have hrstdEnv : ∀ᵐ z : Ω × Ω ∂(νn.prod νn),
      |rstd z.1 z.2| ≤ wstd z.1 * wstd z.2 := by
    filter_upwards [hrstdAE, hKstdEnv] with z hz henv
    rw [hz]
    have hproduct : wstd z.1 * wstd z.2 = Cenv * w z.1 * w z.2 := by
      dsimp only [wstd]
      calc
        Real.sqrt Cenv * w z.1 * (Real.sqrt Cenv * w z.2) =
            (Real.sqrt Cenv) ^ 2 * w z.1 * w z.2 := by ring
        _ = Cenv * w z.1 * w z.2 := by rw [Real.sq_sqrt hCenv.le]
    rw [hproduct]
    exact henv
  -- Unit270 derives the true beta lower bound from the true standardized model.
  have hStandardAt := (hEngine N270 le_rfl).2 νn Hstd hHstdm hHstd2
    hHstdsym hHstdMean hgstdSecond hgstdp hβstdBound
  have hβstd : 1 ≤ βstd := hStandardAt.1
  refine ⟨hσ2low, hσ2up, hσlow, hσ, hσsq, hVarianceRate,
    hHstdm, hHstd2, hHstdsym, hHstdMean, hgstdSecond, hgstdm, hgstd2,
    hgstdzero, hgstdAE, hrstdAE, hgstdp, hβstd, hβstdBound, hrstd2,
    hrstdCan, Real.sqrt_nonneg _, hρ, hwstdm, hwstd0, hwstdSq,
    hwstdSqBound, hrstdEnv, ?_⟩
  intro m hnm hmn
  have hm4 : 4 ≤ m := by omega
  have hm270 : N270 ≤ m := by omega
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hm1 : (m : ℝ) - 1 ≠ 0 := by
    have hm4r : (4 : ℝ) ≤ m := by exact_mod_cast hm4
    linarith
  have hhalf : (n : ℝ) / 2 ≤ (m : ℝ) := by
    have hnr : (n : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hnm
    linarith
  let P : Measure (Fin m → Ω) := Measure.pi (fun _ : Fin m => νn)
  let Pμ : Measure (Fin m → Ω) := Measure.pi (fun _ : Fin m => μ)
  let allGood : Set (Fin m → Ω) := {ζ | ∀ i : Fin m, ζ i ∈ Cn}
  let sampleH : (Fin m → Ω) → Fin m → Fin m → ℝ :=
    fun ζ i j => H (ζ i) (ζ j)
  let U : (Fin m → Ω) → ℝ := fun ζ => Shao.OQ6.FiniteRows.uStatistic (sampleH ζ)
  let RH : (Fin m → Ω) → ℝ :=
    fun ζ => Real.sqrt (Shao.OQ6.FiniteRows.jackknifeSq (sampleH ζ))
  let sstd : (Fin m → Ω) → ℝ := fun ζ => Real.sqrt (centeredSq m gstd rstd ζ)
  let Tstd : (Fin m → Ω) → ℝ := fun ζ =>
    if sstd ζ = 0 then 0 else
      (projectionW m gstd ζ + residualStatisticD m rstd ζ) / sstd ζ
  let Tcenter : (Fin m → Ω) → ℝ := fun ζ =>
    if RH ζ = 0 then 0 else Real.sqrt (m : ℝ) * (U ζ - κ) / RH ζ
  let Tuncenter : (Fin m → Ω) → ℝ := fun ζ =>
    if RH ζ = 0 then 0 else Real.sqrt (m : ℝ) * U ζ / RH ζ
  change 4 ≤ m ∧ IsProbabilityMeasure P ∧ IsProbabilityMeasure Pμ ∧ _
  letI : IsProbabilityMeasure P := inferInstanceAs
    (IsProbabilityMeasure (Measure.pi (fun _ : Fin m => νn)))
  letI : IsProbabilityMeasure Pμ := inferInstanceAs
    (IsProbabilityMeasure (Measure.pi (fun _ : Fin m => μ)))
  have hall : allGood = Set.univ.pi (fun _ : Fin m => Cn) := by
    ext ζ
    simp only [allGood, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
  have hallMeas : MeasurableSet allGood := by
    rw [hall]
    exact MeasurableSet.univ_pi (fun _ => hCn)
  have hallMass : Pμ allGood = (μ Cn) ^ m := by
    rw [hall]
    simp only [Pμ, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hallReal : Pμ.real allGood = dn ^ m := by
    change (Pμ allGood).toReal = (μ Cn).toReal ^ m
    rw [hallMass, ENNReal.toReal_pow]
  have hCnNonzero : μ Cn ≠ 0 := by
    intro hz
    have hd' := hdn
    simp only [dn, Measure.real, hz, ENNReal.toReal_zero] at hd'
    norm_num at hd'
  have hallNonzero : Pμ allGood ≠ 0 := by
    rw [hallMass]
    exact pow_ne_zero _ hCnNonzero
  letI : IsProbabilityMeasure ((Pμ allGood)⁻¹ • Pμ.restrict allGood) := by
    change IsProbabilityMeasure (ProbabilityTheory.cond Pμ allGood)
    exact ProbabilityTheory.cond_isProbabilityMeasure hallNonzero
  have hLaw : P = (Pμ allGood)⁻¹ • Pμ.restrict allGood := by
    apply Measure.pi_eq
    intro E hE
    have hrect : Set.univ.pi E ∩ allGood =
        Set.univ.pi (fun i => E i ∩ Cn) := by
      ext ζ
      simp only [allGood, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_pi,
        Set.mem_univ, forall_true_left]
      exact ⟨fun h i => ⟨h.1 i, h.2 i⟩,
        fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
    have hcoord : ∀ i : Fin m, νn (E i) = (μ Cn)⁻¹ * μ (E i ∩ Cn) := by
      intro i
      rw [νn, Measure.smul_apply, Measure.restrict_apply (hE i), smul_eq_mul]
    rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hE),
      smul_eq_mul, hrect, hallMass, Measure.pi_pi]
    simp_rw [hcoord]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
    rfl
  have hLawReal : ∀ E : Set (Fin m → Ω), MeasurableSet E →
      P.real E = Pμ.real (E ∩ allGood) / dn ^ m := by
    intro E hE
    change (P E).toReal = (Pμ (E ∩ allGood)).toReal / dn ^ m
    rw [hLaw, Measure.smul_apply, Measure.restrict_apply hE, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_inv, hallMass, ENNReal.toReal_pow]
    change ((μ Cn).toReal ^ m)⁻¹ * (Pμ (E ∩ allGood)).toReal =
      (Pμ (E ∩ allGood)).toReal / (μ Cn).toReal ^ m
    ring
  have hwHeight : ∀ᵐ o ∂νn, wstd o ≤ boundedPolylogHeight Cpoly apoly m := by
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
    have hlogm0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith)
    have hlog2m : Real.log 2 ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by norm_num) hm2
    have hlognm : Real.log (n : ℝ) ≤ 2 * Real.log (m : ℝ) := by
      calc
        _ ≤ Real.log (2 * (m : ℝ)) := Real.log_le_log hnpos (by exact_mod_cast hnm)
        _ = Real.log 2 + Real.log (m : ℝ) := Real.log_mul (by norm_num) hmpos.ne'
        _ ≤ _ := by linarith
    have hbase0 : 0 ≤ A * Real.log (n : ℝ) / τ := by
      exact div_nonneg (mul_nonneg hA.le (Real.log_nonneg (by
        exact_mod_cast (by omega : 1 ≤ n)))) hτ.le
    have hbase : A * Real.log (n : ℝ) / τ ≤
        (2 * A / τ) * Real.log (m : ℝ) := by
      have ht := mul_le_mul_of_nonneg_left hlognm hA.le
      have ht' := div_le_div_of_nonneg_right ht hτ.le
      nlinarith only [ht']
    have hRnHeight : Rn ≤ Real.rpow (2 * A / τ) apoly *
        Real.rpow (Real.log (m : ℝ)) apoly := by
      change Real.rpow (A * Real.log (n : ℝ) / τ) apoly ≤ _
      calc
        _ ≤ Real.rpow ((2 * A / τ) * Real.log (m : ℝ)) apoly :=
          Real.rpow_le_rpow hbase0 hbase hapoly.le
        _ = _ := Real.mul_rpow (by positivity) hlogm0
    filter_upwards [hwCut] with o ho
    calc
      wstd o ≤ Real.sqrt Cenv * Rn :=
        mul_le_mul_of_nonneg_left ho.2 (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt Cenv * (Real.rpow (2 * A / τ) apoly *
          Real.rpow (Real.log (m : ℝ)) apoly) :=
        mul_le_mul_of_nonneg_left hRnHeight (Real.sqrt_nonneg _)
      _ = boundedPolylogHeight Cpoly apoly m := by
        dsimp only [boundedPolylogHeight, Cpoly, apoly]
        ring
  -- The remaining identities are pure finite algebra for every sample, even
  -- at observations belonging to the exceptional nonintegrable-row null set.
  have hstats : ∀ ζ : Fin m → Ω,
      RH ζ = 2 * σ * sstd ζ ∧ Tcenter ζ = Tstd ζ ∧
      Tuncenter ζ = (if RH ζ = 0 then 0 else
        Tstd ζ + Real.sqrt (m : ℝ) * κ / RH ζ) := by
    intro ζ
    let F : Fin m → Fin m → ℝ := sampleH ζ
    let Fs : Fin m → Fin m → ℝ := fun i j => Hstd (ζ i) (ζ j)
    have hFsym : ∀ i j, F i j = F j i := fun i j => hHsym (ζ i) (ζ j)
    have hFssym : ∀ i j, Fs i j = Fs j i := fun i j => hHstdsym (ζ i) (ζ j)
    have hsample : sampledKernel m gstd rstd ζ = Fs := by
      funext i j
      dsimp only [sampledKernel, Fs, rstd]
      ring
    have hrow : ∀ i : Fin m, Shao.OQ6.FiniteRows.rowMean Fs i =
        (Shao.OQ6.FiniteRows.rowMean F i - κ) / σ := by
      intro i
      have hsum : (∑ j : Fin m, Fs i j) =
          ((∑ j : Fin m, F i j) - (m : ℝ) * κ) / σ := by
        dsimp only [Fs, Hstd, F, sampleH]
        rw [← Finset.sum_div, Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hdiag : Fs i i = (F i i - κ) / σ := rfl
      unfold Shao.OQ6.FiniteRows.rowMean
      rw [Finset.sum_erase_eq_sub (by simp), hsum,
        Finset.sum_erase_eq_sub (by simp), hdiag]
      field_simp [hm1, hσne]
      <;> ring
    have hU : Shao.OQ6.FiniteRows.uStatistic Fs = (U ζ - κ) / σ := by
      have htotal := Shao.OQ6.FiniteRows.sum_rowMean Fs hFssym (by omega)
      have htotalF := Shao.OQ6.FiniteRows.sum_rowMean F hFsym (by omega)
      simp_rw [hrow] at htotal
      rw [← Finset.sum_div, Finset.sum_sub_distrib] at htotal
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htotal
      rw [htotalF] at htotal
      change ((m : ℝ) * U ζ - (m : ℝ) * κ) / σ =
        (m : ℝ) * Shao.OQ6.FiniteRows.uStatistic Fs at htotal
      apply (mul_left_cancel₀ (ne_of_gt hmpos))
      calc
        (m : ℝ) * Shao.OQ6.FiniteRows.uStatistic Fs = _ := htotal.symm
        _ = (m : ℝ) * ((U ζ - κ) / σ) := by ring
    have hcenterRow : ∀ i : Fin m,
        Shao.OQ6.FiniteRows.rowMean Fs i - Shao.OQ6.FiniteRows.uStatistic Fs =
          (Shao.OQ6.FiniteRows.rowMean F i - U ζ) / σ := by
      intro i
      rw [hrow i, hU]
      ring
    have hJsq : Shao.OQ6.FiniteRows.jackknifeSq Fs =
        Shao.OQ6.FiniteRows.jackknifeSq F / σ ^ 2 := by
      unfold Shao.OQ6.FiniteRows.jackknifeSq
      simp_rw [hcenterRow, div_pow]
      rw [← Finset.sum_div]
      change _ = (4 * ((m : ℝ) - 1) / ((m : ℝ) - 2) ^ 2 *
        ∑ i : Fin m, (Shao.OQ6.FiniteRows.rowMean F i - U ζ) ^ 2) / σ ^ 2
      ring
    have hcenterSq : centeredSq m gstd rstd ζ =
        Shao.OQ6.FiniteRows.jackknifeSq F / (4 * σ ^ 2) := by
      unfold centeredSq
      rw [hsample, hJsq]
      ring
    have hRnonneg : 0 ≤ RH ζ := Real.sqrt_nonneg _
    have hsnonneg : 0 ≤ sstd ζ := Real.sqrt_nonneg _
    have hJnonneg : 0 ≤ Shao.OQ6.FiniteRows.jackknifeSq F :=
      Shao.OQ6.FiniteRows.jackknifeSq_nonneg F (by omega)
    have hR2 : RH ζ ^ 2 = Shao.OQ6.FiniteRows.jackknifeSq F :=
      Real.sq_sqrt hJnonneg
    have hs2 : sstd ζ ^ 2 =
        Shao.OQ6.FiniteRows.jackknifeSq F / (4 * σ ^ 2) := by
      dsimp only [sstd]
      rw [hcenterSq, Real.sq_sqrt (by positivity)]
    have hscaleSq : (2 * σ * sstd ζ) ^ 2 = RH ζ ^ 2 := by
      rw [mul_pow, mul_pow, hs2, hR2]
      field_simp [hσne]
      <;> ring
    have hscale : RH ζ = 2 * σ * sstd ζ := by
      exact (sq_eq_sq₀ hRnonneg (by positivity)).mp hscaleSq.symm
    have hnum : projectionW m gstd ζ + residualStatisticD m rstd ζ =
        Real.sqrt (m : ℝ) * (U ζ - κ) / (2 * σ) := by
      have hformula := sampled_uStatistic_formula m gstd rstd ζ hrstdsym hm4
      rw [hsample, hU] at hformula
      have hroot : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hmpos.le
      have hrootne : Real.sqrt (m : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hmpos)
      unfold projectionW residualStatisticD
      have hformula' : U ζ - κ = σ *
          (2 * (∑ i : Fin m, gstd (ζ i)) / (m : ℝ) +
            2 * Shao.OQ6.CanonicalDoubleGhostScalarMoments.originalUpper m rstd ζ /
              ((m : ℝ) * ((m : ℝ) - 1))) := by
        simpa only [mul_comm] using (div_eq_iff hσne).mp hformula
      rw [hformula']
      field_simp [hσne, ne_of_gt hmpos, hm1, hrootne]
      <;> ring_nf <;> simp only [hroot] <;> ring
    have hzero : RH ζ = 0 ↔ sstd ζ = 0 := by
      rw [hscale]
      simp only [mul_eq_zero, OfNat.ofNat_ne_zero, hσne, false_or]
    have hT : Tcenter ζ = Tstd ζ := by
      dsimp only [Tcenter, Tstd]
      by_cases hz : RH ζ = 0
      · simp only [hz, (hzero.mp hz), if_pos]
      · have hsne : sstd ζ ≠ 0 := fun hs => hz (hzero.mpr hs)
        rw [if_neg hz, if_neg hsne, hnum, hscale]
        field_simp [hσne, hsne]
        <;> ring
    refine ⟨hscale, hT, ?_⟩
    dsimp only [Tuncenter]
    by_cases hz : RH ζ = 0
    · simp only [hz, if_pos]
    · rw [if_neg hz, if_neg hz, ← hT]
      dsimp only [Tcenter]
      rw [if_neg hz]
      ring
  have hUmeas : Measurable U := by
    unfold U Shao.OQ6.FiniteRows.uStatistic Shao.OQ5.P35.unorderedPairSum
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    apply Finset.measurable_sum
    intro j hj
    by_cases hij : i < j
    · simpa only [if_pos hij] using
        hHm.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
    · simpa only [if_neg hij] using (measurable_const : Measurable (fun _ : Fin m → Ω => (0 : ℝ)))
  have hRHmeas : Measurable RH := by
    unfold RH Shao.OQ6.FiniteRows.jackknifeSq
    apply Measurable.sqrt
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.pow_const
    apply Measurable.sub _ hUmeas
    unfold Shao.OQ6.FiniteRows.rowMean
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro j hj
    exact hHm.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
  have hTcenterMeas : Measurable Tcenter := by
    dsimp only [Tcenter]
    exact measurable_const.ite (hRHmeas (measurableSet_singleton 0))
      (((hUmeas.sub measurable_const).const_mul _).div hRHmeas)
  have hTuncenterMeas : Measurable Tuncenter := by
    dsimp only [Tuncenter]
    exact measurable_const.ite (hRHmeas (measurableSet_singleton 0))
      ((hUmeas.const_mul _).div hRHmeas)
  have hTfun : Tcenter = Tstd := funext (fun ζ => (hstats ζ).2.1)
  have hTstdMeas : Measurable Tstd := hTfun ▸ hTcenterMeas
  have hMap : Measure.map Tcenter P = Measure.map Tstd P := by rw [hTfun]
  refine ⟨hm4, inferInstance, inferInstance, hallMeas, hallReal, hLaw,
    hLawReal, hwHeight, hMeanRate m hmn, hTcenterMeas, hTuncenterMeas,
    hTstdMeas, hstats, hMap, ?_⟩
  intro z hz hzWindow
  change |P.real {ζ : Fin m → Ω | z ≤ Tcenter ζ} / Shao.standardNormalTail z - 1| ≤
    K * (β * Real.rpow (1 + z) p * Real.rpow (n : ℝ) (-a) +
      (1 + z) ^ 3 / Real.sqrt (n : ℝ))
  have hβstdpos : 0 < βstd := by linarith
  have hβInverse : Real.rpow (2 * β) (-1 / p) ≤ Real.rpow βstd (-1 / p) :=
    Real.rpow_le_rpow_of_nonpos hβstdpos hβstdBound
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) hp0.le)
  have hhalfPower : Real.rpow ((n : ℝ) / 2) qpow ≤ Real.rpow (m : ℝ) qpow :=
    Real.rpow_le_rpow (by positivity) hhalf hq.le
  have hhalfPowerEq : Real.rpow ((n : ℝ) / 2) qpow =
      Real.rpow (n : ℝ) qpow / Real.rpow 2 qpow :=
    Real.div_rpow hnpos.le (by norm_num)
  have hWindow270 : z ≤ c270 * Real.rpow βstd (-1 / p) * Real.rpow (m : ℝ) qpow := by
    calc
      z ≤ c * Real.rpow (n : ℝ) qpow := hzWindow
      _ = c270 * Real.rpow (2 * β) (-1 / p) *
          Real.rpow ((n : ℝ) / 2) qpow := by rw [hhalfPowerEq]; dsimp only [c]; ring
      _ ≤ c270 * Real.rpow βstd (-1 / p) * Real.rpow (m : ℝ) qpow :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left hβInverse hc270.le) hhalfPower
          (Real.rpow_nonneg (by positivity) _) (by positivity)
  have hTail := ((hEngine m hm270).2 νn Hstd hHstdm hHstd2 hHstdsym
    hHstdMean hgstdSecond hgstdp hβstdBound).2.2 wstd hwstd0 hwHeight
    hwstdSq hwstdSqBound hrstdEnv z hz hWindow270
  change |P.real {ζ : Fin m → Ω | z ≤ Tstd ζ} / Shao.standardNormalTail z - 1| ≤
    K270 * (βstd * Real.rpow (1 + z) p * Real.rpow (m : ℝ) (-a) +
      (1 + ρstd) * (1 + z) ^ 3 / Real.sqrt (m : ℝ)) at hTail
  have hNegPower : Real.rpow (m : ℝ) (-a) ≤
      Real.rpow 2 a * Real.rpow (n : ℝ) (-a) := by
    calc
      _ ≤ Real.rpow ((n : ℝ) / 2) (-a) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hhalf (by linarith)
      _ = Real.rpow (n : ℝ) (-a) / Real.rpow 2 (-a) :=
        Real.div_rpow hnpos.le (by norm_num)
      _ = _ := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
        ring
  have hRootComparison : Real.sqrt (n : ℝ) ≤ Real.sqrt 2 * Real.sqrt (m : ℝ) := by
    calc
      _ ≤ Real.sqrt (2 * (m : ℝ)) := Real.sqrt_le_sqrt (by exact_mod_cast hnm)
      _ = _ := Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _
  have hz0 : 0 ≤ z := by linarith
  have hzpp : 0 ≤ Real.rpow (1 + z) p := Real.rpow_nonneg (by linarith) _
  have hz3 : 0 ≤ (1 + z) ^ 3 := by positivity
  have hnPower0 : 0 ≤ Real.rpow (n : ℝ) (-a) := Real.rpow_nonneg hnpos.le _
  have hFirst : βstd * Real.rpow (1 + z) p * Real.rpow (m : ℝ) (-a) ≤
      L1 * (β * Real.rpow (1 + z) p * Real.rpow (n : ℝ) (-a)) := by
    have hb := mul_le_mul_of_nonneg_right hβstdBound hzpp
    have ht := mul_le_mul hb hNegPower (Real.rpow_nonneg hmpos.le _) (by positivity)
    dsimp only [L1]
    nlinarith only [ht]
  have hSecond : (1 + ρstd) * (1 + z) ^ 3 / Real.sqrt (m : ℝ) ≤
      L2 * ((1 + z) ^ 3 / Real.sqrt (n : ℝ)) := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hmpos)).2
    have hρRoot : (1 + ρstd) * Real.sqrt (n : ℝ) ≤
        L2 * Real.sqrt (m : ℝ) := by
      calc
        _ ≤ (1 + Real.sqrt RhoBound) * (Real.sqrt 2 * Real.sqrt (m : ℝ)) :=
          mul_le_mul (by linarith [hρ]) hRootComparison
            (Real.sqrt_nonneg _) (by positivity)
        _ = _ := by dsimp only [L2]; ring
    have hh := mul_le_mul_of_nonneg_right hρRoot hz3
    have hdiv : (1 + ρstd) * (1 + z) ^ 3 ≤
        (L2 * Real.sqrt (m : ℝ) * (1 + z) ^ 3) / Real.sqrt (n : ℝ) :=
      (le_div_iff₀ (Real.sqrt_pos.mpr hnpos)).2 (by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hh)
    convert hdiv using 1 <;> ring
  have hX0 : 0 ≤ β * Real.rpow (1 + z) p * Real.rpow (n : ℝ) (-a) := by positivity
  have hY0 : 0 ≤ (1 + z) ^ 3 / Real.sqrt (n : ℝ) := by positivity
  have hPaid : K270 * (βstd * Real.rpow (1 + z) p * Real.rpow (m : ℝ) (-a) +
      (1 + ρstd) * (1 + z) ^ 3 / Real.sqrt (m : ℝ)) ≤
      K * (β * Real.rpow (1 + z) p * Real.rpow (n : ℝ) (-a) +
        (1 + z) ^ 3 / Real.sqrt (n : ℝ)) := by
    apply le_trans (mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond) hK270.le)
    dsimp only [K]
    have hcross1 := mul_nonneg hL2.le hX0
    have hcross2 := mul_nonneg hL1.le hY0
    have hpayed := mul_nonneg hK270.le (add_nonneg hcross1 hcross2)
    nlinarith only [hpayed]
  rw [hTfun]
  exact hTail.trans hPaid
end
end Shao.OQ6.OriginalLogarithmicConditionalCenteredPhysicalTail
