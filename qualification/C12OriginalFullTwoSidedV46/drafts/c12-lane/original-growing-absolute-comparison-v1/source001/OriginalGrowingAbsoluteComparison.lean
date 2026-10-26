import Shao.C2.OriginalGrowingDoubleComparison
import Shao.Probability.SourceOriginalFullRelative
import Shao.Probability.SourceMomentDomain
import Shao.Probability.SourceNonresidualBrownian
import Shao.Probability.TruncationIntegrals
import Shao.C2.TwoSided

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
namespace Shao.C2.OriginalGrowingAbsoluteComparison
open MeasureTheory ProbabilityTheory Set
open Shao.C2.BridgeDomination
open scoped BigOperators NNReal Topology Classical

theorem original_iid_growing_double_and_absolute_comparison :
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
              ∀ x : ℝ, 1 ≤ x → x ∈ I →
                let D : Set Ω := {omega |
                  x * Real.sqrt (rawEnergy omega) ≤ Shao.upperMax (population omega) hn ∧
                  x * Real.sqrt (rawEnergy omega) ≤ Shao.lowerMax (population omega) hn}
                let DB : Set ΩB := {omega |
                  (∃ s : BridgeTime, x ≤ Bm ⟨(s : ℝ), s.property.1⟩ omega) ∧
                  ∃ s : BridgeTime, Bm ⟨(s : ℝ), s.property.1⟩ omega ≤ -x}
                let A : Set Ω := {omega |
                  x * Real.sqrt (rawEnergy omega) ≤ Shao.absMax (population omega) hn}
                let H : ℝ := PB.real {omega |
                  ∃ s : BridgeTime, x ≤ |Bm ⟨(s : ℝ), s.property.1⟩ omega|}
                NullMeasurableSet D mu ∧
                  Integrable (D.indicator (fun _ : Ω => (1 : ℝ))) mu ∧
                  NullMeasurableSet A mu ∧
                  Integrable (A.indicator (fun _ : Ω => (1 : ℝ))) mu ∧
                  0 < H ∧
                  |mu.real D - PB.real DB| ≤ C * Rn x * Shao.standardNormalTail x ∧
                  |mu.real A / H - 1| ≤ C * Rn x ∧
                  |mu.real A / H - 1| ≤ C * Real.rpow (1 + x) p * Ln := by
  obtain ⟨C2, hC2, hDoubleCompare⟩ :=
    Shao.C2.OriginalGrowingDoubleComparison.original_iid_growing_double_relative_comparison
  obtain ⟨C1, hC1, hSignedCompare⟩ :=
    Shao.Probability.SourceOriginalFullRelative.original_iid_signed_halfline_full_relative_comparison
  let C : ℝ := 2 * C1 + C2
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro rhoStar hrhoStar hrhoStarUpper p hp2 hp3 Ω ΩB _ _ Bm PB _ hBrownian
    mu rho _ _ n hn X hX hIndep hLaw h2 hmean hsecond hp
    sigmaSq sigma scale nu Ln Rn I population rawEnergy x hx hxI D DB A H
  let U : Set Ω := {omega |
    x * Real.sqrt (rawEnergy omega) ≤ Shao.upperMax (population omega) hn}
  let L : Set Ω := {omega |
    x * Real.sqrt (rawEnergy omega) ≤ Shao.lowerMax (population omega) hn}
  let R : ℝ := Rn x
  let d : ℝ := PB.real DB
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hxpos : 0 < x := by linarith only [hx]
  have hDouble := hDoubleCompare rhoStar hrhoStar hrhoStarUpper p hp2 hp3 Bm PB hBrownian
    mu rho n hn X hX hIndep hLaw h2 hmean hsecond hp x hx hxI
  have hDn : NullMeasurableSet D mu := hDouble.1
  have hDI : Integrable (D.indicator (fun _ : Ω => (1 : ℝ))) mu := hDouble.2.1
  have hDError := hDouble.2.2
  change |mu.real D - d| ≤ C2 * R * Shao.standardNormalTail x at hDError
  have hPlus := hSignedCompare rhoStar hrhoStar hrhoStarUpper p hp2 hp3
    mu rho n hn X hX hIndep hLaw h2 hmean hsecond hp 1 x (Or.inl rfl) hx0 hxI
  have hMinus := hSignedCompare rhoStar hrhoStar hrhoStarUpper p hp2 hp3
    mu rho n hn X hX hIndep hLaw h2 hmean hsecond hp (-1) x (Or.inr rfl) hx0 hxI
  have hUI : Integrable (U.indicator (fun _ : Ω => (1 : ℝ))) mu := by
    simpa only [one_smul] using hPlus.1
  have hLI : Integrable (L.indicator (fun _ : Ω => (1 : ℝ))) mu := by
    simpa only [neg_one_smul, Shao.lowerMax] using hMinus.1
  have hUError : |mu.real U - 2 * Shao.standardNormalTail x| ≤
      C1 * R * Shao.standardNormalTail x := by
    simpa only [one_smul] using hPlus.2.2.2.1
  have hLError : |mu.real L - 2 * Shao.standardNormalTail x| ≤
      C1 * R * Shao.standardNormalTail x := by
    simpa only [neg_one_smul, Shao.lowerMax] using hMinus.2.2.2.1
  have hPop : AEMeasurable population mu := AEMeasurable.of_eval hX
  have hUn : NullMeasurableSet U mu :=
    hPop.nullMeasurableSet_preimage (Shao.measurableSet_upperCrossing hn x)
  have hLn : NullMeasurableSet L mu :=
    hPop.nullMeasurableSet_preimage (Shao.measurableSet_lowerCrossing hn x)
  have hAeq : A = U ∪ L := by
    ext omega
    change x * Real.sqrt (rawEnergy omega) ≤
        max (Shao.upperMax (population omega) hn) (Shao.lowerMax (population omega) hn) ↔
      x * Real.sqrt (rawEnergy omega) ≤ Shao.upperMax (population omega) hn ∨
        x * Real.sqrt (rawEnergy omega) ≤ Shao.lowerMax (population omega) hn
    exact le_max_iff
  have hDeq : D = U ∩ L := rfl
  have hAn : NullMeasurableSet A mu := by
    rw [hAeq]
    exact hUn.union hLn
  have hIndicator : A.indicator (fun _ : Ω => (1 : ℝ)) =
      fun omega => U.indicator (fun _ : Ω => (1 : ℝ)) omega +
        L.indicator (fun _ : Ω => (1 : ℝ)) omega -
          D.indicator (fun _ : Ω => (1 : ℝ)) omega := by
    funext omega
    by_cases hU : omega ∈ U <;> by_cases hL : omega ∈ L <;>
      simp [hAeq, hDeq, hU, hL]
  have hAI : Integrable (A.indicator (fun _ : Ω => (1 : ℝ))) mu := by
    rw [hIndicator]
    exact (hUI.add hLI).sub hDI
  have hIE := measureReal_union_add_inter₀ (μ := mu) (s := U) hLn
  rw [← hAeq, ← hDeq] at hIE
  have hBrownianData :=
    Shao.Probability.SourceNonresidualBrownian.actual_brownian_weak_double_crossing
      Bm PB hBrownian x hxpos
  have hBrownianIdentity : d = 4 * Shao.standardNormalTail x - H :=
    hBrownianData.2.2.2.2.1
  have hBrownianUpper : d ≤ 2 * Shao.standardNormalTail x :=
    hBrownianData.2.2.2.2.2.2.1
  have hPsiPos : 0 < Shao.standardNormalTail x :=
    (Shao.standardNormalTail_basic.2.2.1 x).1
  have hHLower : 2 * Shao.standardNormalTail x ≤ H := by
    linarith only [hBrownianIdentity, hBrownianUpper]
  have hPsiH : Shao.standardNormalTail x ≤ H := by
    linarith only [hHLower, hPsiPos]
  have hHpos : 0 < H := hPsiPos.trans_le hPsiH
  have hErrorIdentity : mu.real A - H =
      (mu.real U - 2 * Shao.standardNormalTail x) +
        (mu.real L - 2 * Shao.standardNormalTail x) - (mu.real D - d) := by
    linarith only [hIE, hBrownianIdentity]
  have hAbsoluteError : |mu.real A - H| ≤ C * R * Shao.standardNormalTail x := by
    rw [hErrorIdentity]
    calc
      |(mu.real U - 2 * Shao.standardNormalTail x) +
          (mu.real L - 2 * Shao.standardNormalTail x) - (mu.real D - d)| ≤
          |(mu.real U - 2 * Shao.standardNormalTail x) +
            (mu.real L - 2 * Shao.standardNormalTail x)| + |mu.real D - d| := abs_sub _ _
      _ ≤ (|mu.real U - 2 * Shao.standardNormalTail x| +
          |mu.real L - 2 * Shao.standardNormalTail x|) + |mu.real D - d| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (C1 * R * Shao.standardNormalTail x + C1 * R * Shao.standardNormalTail x) +
          C2 * R * Shao.standardNormalTail x :=
        add_le_add (add_le_add hUError hLError) hDError
      _ = C * R * Shao.standardNormalTail x := by dsimp only [C]; ring
  rcases Shao.Probability.original_raw_normalization_data p hp2 hp3 rho n hn h2 hmean
      hsecond hp with
    ⟨_hSigma, hNuProb, hNu2, _hNuMean, _hNuNorm, hNuP, _hNuPIdentity,
      _hLnPos, hLnIdentity, _hNormMap, _hNormalizedSigned⟩
  change IsProbabilityMeasure nu at hNuProb
  letI : IsProbabilityMeasure nu := hNuProb
  change Integrable (fun z : ℝ => z ^ 2) nu at hNu2
  change Integrable (fun z : ℝ => Real.rpow |z| p) nu at hNuP
  change Ln = (n : ℝ) * (∫ z : ℝ, Real.rpow |z| p ∂nu) at hLnIdentity
  have hR0 : 0 ≤ R := Shao.truncationBudget_nonneg nu n hNu2 x
  have hRelative : |mu.real A / H - 1| ≤ C * R := by
    have hRatio : mu.real A / H - 1 = (mu.real A - H) / H := by
      field_simp [hHpos.ne'] <;> ring
    rw [hRatio, abs_div, abs_of_pos hHpos]
    apply (div_le_iff₀ hHpos).mpr
    exact hAbsoluteError.trans
      (mul_le_mul_of_nonneg_left hPsiH (mul_nonneg hC.le hR0))
  have hRmoment := Shao.truncationBudget_le_rpow_moment nu n hNu2 x p hx0 hp2.le hp3 hNuP
  change R ≤ Real.rpow (1 + x) p *
    ((n : ℝ) * (∫ z : ℝ, Real.rpow |z| p ∂nu)) at hRmoment
  rw [← hLnIdentity] at hRmoment
  refine ⟨hDn, hDI, hAn, hAI, hHpos, ?_, hRelative, ?_⟩
  · apply hDError.trans
    apply mul_le_mul_of_nonneg_right _ hPsiPos.le
    apply mul_le_mul_of_nonneg_right _ hR0
    dsimp only [C]
    linarith only [hC1]
  · calc
      |mu.real A / H - 1| ≤ C * R := hRelative
      _ ≤ C * (Real.rpow (1 + x) p * Ln) := mul_le_mul_of_nonneg_left hRmoment hC.le
      _ = C * Real.rpow (1 + x) p * Ln := by ring

end Shao.C2.OriginalGrowingAbsoluteComparison
