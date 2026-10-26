import Shao.C2.OriginalFullTwoSidedRelative
import Shao.C2.OriginalMomentEnvelope
import Shao.Probability.SourceMomentDomain
import Shao.Probability.TruncationIntegrals
import Mathlib.Probability.Independence.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option Elab.async false
noncomputable section
namespace Shao.C2.OriginalUniformSubpower
open MeasureTheory ProbabilityTheory Filter Topology Shao.Probability
open Shao.C2.BridgeDomination
open scoped BigOperators Classical NNReal

theorem original_iid_two_sided_uniform_subpower_convergence
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    {Ω ΩB : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩB]
    (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hBrownian : IsBrownianReal Bm PB)
    (mu : Measure Ω) (rho : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure rho]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ i : ℕ, AEMeasurable (X i) mu)
    (hIndep : iIndepFun X mu)
    (hLaw : ∀ i : ℕ, IdentDistrib (X i) (id : ℝ → ℝ) mu rho)
    (h2 : Integrable (fun z : ℝ => z ^ 2) rho)
    (hmean : (∫ z : ℝ, z ∂rho) = 0)
    (hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂rho)
    (hp : Integrable (fun z : ℝ => Real.rpow |z| p) rho) :
    let sigma : ℝ := Real.sqrt (∫ z : ℝ, z ^ 2 ∂rho)
    ∀ (b : ℕ → ℝ), (∀ n : ℕ, 0 ≤ b n) →
      Tendsto (fun n : ℕ => b n / Real.rpow (n : ℝ) ((p - 2) / (2 * p)))
        atTop (𝓝 0) →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, ∀ (n : ℕ) (hn : 0 < n), N ≤ n →
          let Xn : Fin n → Ω → ℝ := fun i => X i.val
          let population : Ω → Shao.Path n := Shao.Probability.samplePath Xn
          let rawEnergy : Ω → ℝ := fun omega => ∑ i : Fin n, (Xn i omega) ^ 2
          ∀ x : ℝ, 0 ≤ x → x ≤ b n →
            let A : Set Ω := {omega |
              x * Real.sqrt (rawEnergy omega) ≤ Shao.absMax (population omega) hn}
            let H : ℝ := PB.real {omega |
              ∃ s : BridgeTime, x ≤ |Bm ⟨(s : ℝ), s.property.1⟩ omega|}
            0 < H ∧ |mu.real A / H - 1| < epsilon := by
  intro sigma b hb hRate epsilon hEpsilon
  obtain ⟨C, hC, hFull⟩ :=
    Shao.C2.OriginalFullTwoSidedRelative.original_iid_full_two_sided_relative_comparison
  let moment : ℝ := ∫ z : ℝ, Real.rpow |z| p ∂rho
  let Ln : ℕ → ℝ := fun n => moment /
    (Real.rpow sigma p * Real.rpow (n : ℝ) ((p - 2) / 2))
  let envelope : ℕ → ℝ := fun n => Real.rpow (1 + b n) p * Ln n
  have hSigma : 0 < sigma := Real.sqrt_pos.mpr hsecond
  have hMoment : 0 ≤ moment := integral_nonneg (fun z => Real.rpow_nonneg (abs_nonneg z) p)
  have hp0 : 0 < p := by linarith only [hp2]
  have hEnvelope : Tendsto envelope atTop (𝓝 0) :=
    Shao.C2.OriginalMomentEnvelope.original_moment_envelope_tendsto_zero
      p moment sigma hp2 hMoment hSigma b hb hRate
  have hCut : 0 < min (1 / 16 : ℝ) (epsilon / C) :=
    lt_min (by norm_num) (div_pos hEpsilon hC)
  have hEventually : ∀ᶠ n : ℕ in atTop,
      envelope n < min (1 / 16 : ℝ) (epsilon / C) :=
    hEnvelope.eventually (eventually_lt_nhds hCut)
  rcases Filter.eventually_atTop.1 hEventually with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hNn Xn population rawEnergy x hx hxb A H
  have hXn : ∀ i : Fin n, AEMeasurable (Xn i) mu := fun i => hX i.val
  have hIndepn : iIndepFun Xn mu :=
    ProbabilityTheory.iIndepFun.precomp (g := fun i : Fin n => i.val) Fin.val_injective hIndep
  have hLawn : ∀ i : Fin n, IdentDistrib (Xn i) (id : ℝ → ℝ) mu rho :=
    fun i => hLaw i.val
  let nu : Measure ℝ := Measure.map (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) rho
  let Rn : ℝ → ℝ := fun t => Shao.truncationBudget nu n t
  rcases Shao.Probability.original_raw_normalization_data p hp2 hp3 rho n hn h2 hmean
      hsecond hp with
    ⟨_hSigma, hNuProb, hNu2, _hNuMean, _hNuNorm, hNuP, _hNuPIdentity,
      _hLnPos, hLnIdentity, _hNormMap, _hNormalizedSigned⟩
  change IsProbabilityMeasure nu at hNuProb
  letI : IsProbabilityMeasure nu := hNuProb
  change Integrable (fun z : ℝ => z ^ 2) nu at hNu2
  change Integrable (fun z : ℝ => Real.rpow |z| p) nu at hNuP
  change Ln n = (n : ℝ) * (∫ z : ℝ, Real.rpow |z| p ∂nu) at hLnIdentity
  have hBudget := Shao.truncationBudget_le_rpow_moment nu n hNu2 x p hx hp2.le hp3 hNuP
  change Rn x ≤ Real.rpow (1 + x) p *
    ((n : ℝ) * (∫ z : ℝ, Real.rpow |z| p ∂nu)) at hBudget
  rw [← hLnIdentity] at hBudget
  have hLnNonneg : 0 ≤ Ln n := by
    exact div_nonneg hMoment (mul_nonneg (Real.rpow_nonneg hSigma.le p)
      (Real.rpow_nonneg (Nat.cast_nonneg n) ((p - 2) / 2)))
  have hPowerBound : Real.rpow (1 + x) p ≤ Real.rpow (1 + b n) p :=
    Real.rpow_le_rpow (by linarith only [hx]) (by linarith only [hxb]) hp0.le
  have hBudgetEnvelope : Rn x ≤ envelope n :=
    hBudget.trans (mul_le_mul_of_nonneg_right hPowerBound hLnNonneg)
  have hNSmall := hN n hNn
  have hBudgetSmall : Rn x ≤ (1 / 16 : ℝ) :=
    hBudgetEnvelope.trans (le_of_lt (lt_of_lt_of_le hNSmall (min_le_left _ _)))
  have hEnvelopeEpsilon : envelope n < epsilon / C :=
    lt_of_lt_of_le hNSmall (min_le_right _ _)
  have hCompare := hFull (1 / 16) (by norm_num) (le_refl _) p hp2 hp3 Bm PB hBrownian
    mu rho n hn Xn hXn hIndepn hLawn h2 hmean hsecond hp x hx
      (Or.inr ⟨hx, Or.inr hBudgetSmall⟩)
  change 0 < H ∧ |mu.real A / H - 1| ≤ C * Rn x ∧
    |mu.real A / H - 1| ≤ C * Real.rpow (1 + x) p * Ln n at hCompare
  refine ⟨hCompare.1, ?_⟩
  calc
    |mu.real A / H - 1| ≤ C * Rn x := hCompare.2.1
    _ ≤ C * envelope n := mul_le_mul_of_nonneg_left hBudgetEnvelope hC.le
    _ < epsilon := by
      simpa only [mul_comm] using (lt_div_iff₀ hC).mp hEnvelopeEpsilon

end Shao.C2.OriginalUniformSubpower
