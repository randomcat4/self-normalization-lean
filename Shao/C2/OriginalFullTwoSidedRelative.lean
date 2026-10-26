import Shao.C2.OriginalGrowingAbsoluteComparison
import Shao.C2.ActualOriginalCompactRelative
import Shao.Probability.SourceMomentDomain
import Shao.Probability.TruncationIntegrals

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option Elab.async false
noncomputable section
namespace Shao.C2.OriginalFullTwoSidedRelative
open MeasureTheory ProbabilityTheory Shao.Probability
open Shao.C2.BridgeDomination
open scoped BigOperators Classical NNReal

theorem original_iid_full_two_sided_relative_comparison :
    ∃ C : ℝ, 0 < C ∧
      ∀ rhoStar : ℝ, 0 < rhoStar → rhoStar ≤ 1 / 16 →
        ∀ p : ℝ, 2 < p → p ≤ 3 →
          ∀ {Ω ΩB : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩB]
            (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
            IsBrownianReal Bm PB →
            ∀ (mu : Measure Ω) (rho : Measure ℝ)
              [IsProbabilityMeasure mu] [IsProbabilityMeasure rho]
              (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ),
              (∀ i, AEMeasurable (X i) mu) →
              iIndepFun X mu →
              (∀ i, IdentDistrib (X i) (id : ℝ → ℝ) mu rho) →
              Integrable (fun z : ℝ => z ^ 2) rho →
              (∫ z : ℝ, z ∂rho) = 0 →
              (0 < ∫ z : ℝ, z ^ 2 ∂rho) →
              Integrable (fun z : ℝ => Real.rpow |z| p) rho →
              let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
              let sigma : ℝ := Real.sqrt sigmaSq
              let scale : ℝ := sigma * Real.sqrt (n : ℝ)
              let nu : Measure ℝ := Measure.map (fun z : ℝ => z / scale) rho
              let Ln : ℝ := (∫ z : ℝ, Real.rpow |z| p ∂rho) /
                (Real.rpow sigma p * Real.rpow (n : ℝ) ((p - 2) / 2))
              let Rn : ℝ → ℝ := fun t => Shao.truncationBudget nu n t
              let I : Set ℝ := {t | 0 ≤ t ∧
                (t ≤ Real.rpow Ln (-1 / p) ∨ Rn t ≤ rhoStar)}
              let population : Ω → Shao.Path n := Shao.Probability.samplePath X
              let rawEnergy : Ω → ℝ := fun omega => ∑ i : Fin n, (X i omega) ^ 2
              ∀ x : ℝ, 0 ≤ x → (x ≤ 1 ∨ x ∈ I) →
                let A : Set Ω := {omega |
                  x * Real.sqrt (rawEnergy omega) ≤ Shao.absMax (population omega) hn}
                let H : ℝ := PB.real {omega |
                  ∃ s : BridgeTime, x ≤ |Bm ⟨(s : ℝ), s.property.1⟩ omega|}
                0 < H ∧
                  |mu.real A / H - 1| ≤ C * Rn x ∧
                  |mu.real A / H - 1| ≤ C * Real.rpow (1 + x) p * Ln := by
  obtain ⟨Cc, hCc, hCompact⟩ :=
    Shao.C2.ActualOriginalCompactRelative.actual_original_iid_absolute_small_window_relative
  obtain ⟨Cg, hCg, hGrowing⟩ :=
    Shao.C2.OriginalGrowingAbsoluteComparison.original_iid_growing_double_and_absolute_comparison
  let C : ℝ := max Cc Cg
  have hC : 0 < C := lt_of_lt_of_le hCc (le_max_left Cc Cg)
  refine ⟨C, hC, ?_⟩
  intro rhoStar hrhoStar hrhoStarUpper p hp2 hp3 Ω ΩB _ _ Bm PB _ hBrownian
    mu rho _ _ n hn X hX hIndep hLaw h2 hmean hsecond hp
    sigmaSq sigma scale nu Ln Rn I population rawEnergy x hx hDomain A H
  rcases Shao.Probability.original_raw_normalization_data p hp2 hp3 rho n hn h2 hmean
      hsecond hp with
    ⟨_hSigma, hNuProb, hNu2, _hNuMean, _hNuNorm, hNuP, _hNuPIdentity,
      _hLnPos, hLnIdentity, _hNormMap, _hNormalizedSigned⟩
  change IsProbabilityMeasure nu at hNuProb
  letI : IsProbabilityMeasure nu := hNuProb
  change Integrable (fun z : ℝ => z ^ 2) nu at hNu2
  change Integrable (fun z : ℝ => Real.rpow |z| p) nu at hNuP
  change Ln = (n : ℝ) * (∫ z : ℝ, Real.rpow |z| p ∂nu) at hLnIdentity
  have hRnonneg : 0 ≤ Rn x := Shao.truncationBudget_nonneg nu n hNu2 x
  have hBound : 0 < H ∧ |mu.real A / H - 1| ≤ C * Rn x := by
    by_cases hxs : x ≤ 1
    · have hScale : Real.sqrt ((n : ℝ) * sigmaSq) = scale := by
        change Real.sqrt ((n : ℝ) * sigmaSq) =
          Real.sqrt sigmaSq * Real.sqrt (n : ℝ)
        rw [Real.sqrt_mul (Nat.cast_nonneg n)]
        exact mul_comm _ _
      have hSmall := hCompact Bm PB hBrownian mu rho n hn X hX hIndep hLaw
        h2 hmean hsecond x hx hxs
      change 0 < H ∧ |mu.real A / H - 1| ≤
        Cc * Shao.truncationBudget
          (Measure.map (fun z : ℝ => z / Real.sqrt ((n : ℝ) * sigmaSq)) rho) n 0 at hSmall
      rw [hScale] at hSmall
      change 0 < H ∧ |mu.real A / H - 1| ≤ Cc * Rn 0 at hSmall
      have hRmono : Rn 0 ≤ Rn x :=
        Shao.truncationBudget_mono nu n hNu2 0 x (by norm_num) hx
      refine ⟨hSmall.1, ?_⟩
      calc
        |mu.real A / H - 1| ≤ Cc * Rn 0 := hSmall.2
        _ ≤ Cc * Rn x := mul_le_mul_of_nonneg_left hRmono hCc.le
        _ ≤ C * Rn x := mul_le_mul_of_nonneg_right (le_max_left Cc Cg) hRnonneg
    · have hx1 : 1 ≤ x := le_of_lt (lt_of_not_ge hxs)
      have hxI : x ∈ I := hDomain.resolve_left hxs
      have hGrow := hGrowing rhoStar hrhoStar hrhoStarUpper p hp2 hp3 Bm PB hBrownian
        mu rho n hn X hX hIndep hLaw h2 hmean hsecond hp x hx1 hxI
      have hHpos : 0 < H := hGrow.2.2.2.2.1
      have hGrowBound : |mu.real A / H - 1| ≤ Cg * Rn x := hGrow.2.2.2.2.2.2.1
      refine ⟨hHpos, ?_⟩
      exact hGrowBound.trans
        (mul_le_mul_of_nonneg_right (le_max_right Cc Cg) hRnonneg)
  have hRmoment := Shao.truncationBudget_le_rpow_moment nu n hNu2 x p hx hp2.le hp3 hNuP
  change Rn x ≤ Real.rpow (1 + x) p *
    ((n : ℝ) * (∫ z : ℝ, Real.rpow |z| p ∂nu)) at hRmoment
  rw [← hLnIdentity] at hRmoment
  refine ⟨hBound.1, hBound.2, ?_⟩
  calc
    |mu.real A / H - 1| ≤ C * Rn x := hBound.2
    _ ≤ C * (Real.rpow (1 + x) p * Ln) :=
      mul_le_mul_of_nonneg_left hRmoment hC.le
    _ = C * Real.rpow (1 + x) p * Ln := by ring

end Shao.C2.OriginalFullTwoSidedRelative
