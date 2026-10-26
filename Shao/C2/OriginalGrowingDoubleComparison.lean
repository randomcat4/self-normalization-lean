import Shao.C2.ActualOriginalSmallBudgetDouble
import Shao.C2.ActualCenteredProductTransport
import Shao.Probability.SourceOriginalFullRelative
import Shao.Probability.SourceMomentDomain
import Shao.Probability.SourceNonresidualBrownian

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
namespace Shao.C2.OriginalGrowingDoubleComparison
open MeasureTheory ProbabilityTheory Set
open Shao.C2.BridgeDomination
open scoped BigOperators NNReal Topology Classical

theorem original_iid_growing_double_relative_comparison :
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
                NullMeasurableSet D mu ∧
                  Integrable (D.indicator (fun _ : Ω => (1 : ℝ))) mu ∧
                  |mu.real D - PB.real DB| ≤ C * Rn x * Shao.standardNormalTail x := by
  obtain ⟨etaS, Cs, hetaS, hCs, hSmallCompare⟩ :=
    Shao.C2.ActualOriginalSmallBudgetDouble.iid_actual_original_small_budget_double_comparison
  obtain ⟨C1, hC1, hSignedCompare⟩ :=
    Shao.Probability.SourceOriginalFullRelative.original_iid_signed_halfline_full_relative_comparison
  refine ⟨max Cs (C1 + 4 / etaS), lt_of_lt_of_le hCs (le_max_left _ _), ?_⟩
  intro rhoStar hrhoStar hrhoStarUpper p hp2 hp3 Ω ΩB _ _ Bm PB _ hBrownian
    mu rho _ _ n hn X hX hIndep hLaw h2 hmean hsecond hp
    sigmaSq sigma scale nu Ln Rn I population rawEnergy x hx hxI D DB
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  rcases Shao.Probability.original_raw_normalization_data p hp2 hp3 rho n hn h2 hmean
      hsecond hp with
    ⟨hSigma, hNuProb, hNu2, hNuMean, hNuNorm, _hNuP, _hNuPIdentity,
      _hLnPos, _hLnIdentity, hNormMap, _hNormalizedSigned⟩
  change IsProbabilityMeasure nu at hNuProb
  letI : IsProbabilityMeasure nu := hNuProb
  change Integrable (fun z : ℝ => z ^ 2) nu at hNu2
  change (∫ z : ℝ, z ∂nu) = 0 at hNuMean
  change (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 at hNuNorm
  have hScale : 0 < scale := mul_pos hSigma (Real.sqrt_pos.mpr hnReal)
  let Praw : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  let PN : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  letI : IsProbabilityMeasure PN := by dsimp only [PN]; infer_instance
  let Traw : Shao.Path n → Shao.Path n := fun v i => v i / scale
  let normalizedPath : Ω → Shao.Path n := fun omega i => X i omega / scale
  let DA : Set (Shao.Path n) := Shao.C2.doubleCrossing hn x
  have hPop : AEMeasurable population mu := AEMeasurable.of_eval hX
  have hPopMap : Measure.map population mu = Praw := by
    change Measure.map (fun omega i => X i omega) mu = _
    rw [hIndep.map_fun_eq_pi_map hX]
    congr 1
    funext i
    simpa only [Measure.map_id] using (hLaw i).map_eq
  have hTraw : Measurable Traw := by dsimp only [Traw]; fun_prop
  have hNormalizedForm : normalizedPath = Traw ∘ population := rfl
  have hNormalized : AEMeasurable normalizedPath mu := by
    rw [hNormalizedForm]
    exact hTraw.comp_aemeasurable hPop
  have hNormalizedMap : Measure.map normalizedPath mu = PN := by
    rw [hNormalizedForm, ← AEMeasurable.map_map_of_aemeasurable hTraw.aemeasurable hPop,
      hPopMap]
    exact hNormMap
  have hPair : IdentDistrib normalizedPath (id : Shao.Path n → Shao.Path n) mu PN :=
    ⟨hNormalized, measurable_id.aemeasurable,
      by simpa only [Measure.map_id] using hNormalizedMap⟩
  have hDA : MeasurableSet DA := Shao.C2.measurableSet_doubleCrossing hn x
  have hDpre : normalizedPath ⁻¹' DA = D := by
    ext omega
    change normalizedPath omega ∈ Shao.C2.doubleCrossing hn x ↔
      population omega ∈ Shao.C2.doubleCrossing hn x
    have hRepresentation : normalizedPath omega = scale⁻¹ • population omega := by
      funext i
      change X i omega / scale = scale⁻¹ * X i omega
      rw [div_eq_mul_inv, mul_comm]
    rw [hRepresentation]
    exact Shao.C2.ActualCenteredProductTransport.double_crossing_smul_iff
      hn (population omega) scale⁻¹ (inv_pos.mpr hScale) x
  have hDn : NullMeasurableSet D mu := by
    rw [← hDpre]
    exact hNormalized.nullMeasurableSet_preimage hDA
  have hDraw : mu.real D = PN.real DA := by
    have hh := congrArg ENNReal.toReal (hPair.measure_mem_eq hDA)
    simpa only [Measure.real, hDpre, Set.preimage_id] using hh
  have hDI : Integrable (D.indicator (fun _ : Ω => (1 : ℝ))) mu := by
    let f : Shao.Path n → ℝ := DA.indicator (fun _ => (1 : ℝ))
    have hfm : Measurable f := measurable_const.indicator hDA
    have hfi : Integrable f PN := (integrable_const (1 : ℝ)).indicator hDA
    have hi := (hPair.comp hfm).integrable_iff.mpr hfi
    change Integrable (fun omega => f (normalizedPath omega)) mu at hi
    convert hi using 1
    funext omega
    rw [← hDpre]
    by_cases ho : normalizedPath omega ∈ DA <;> simp [f, Set.mem_preimage, ho]
  let R : ℝ := Rn x
  let d : ℝ := PB.real DB
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hxpos : 0 < x := by linarith only [hx]
  have hR0 : 0 ≤ R := Shao.truncationBudget_nonneg nu n hNu2 x
  have hPsi : 0 ≤ Shao.standardNormalTail x :=
    (Shao.standardNormalTail_basic.2.2.1 x).1.le
  have hBrownianData :=
    Shao.Probability.SourceNonresidualBrownian.actual_brownian_weak_double_crossing
      Bm PB hBrownian x hxpos
  have hd0 : 0 ≤ d := hBrownianData.2.2.2.2.2.1
  have hd2 : d ≤ 2 * Shao.standardNormalTail x := hBrownianData.2.2.2.2.2.2.1
  refine ⟨hDn, hDI, ?_⟩
  change |mu.real D - d| ≤ max Cs (C1 + 4 / etaS) * R * Shao.standardNormalTail x
  by_cases hSmall : R ≤ etaS
  · have hPaid := hSmallCompare Bm PB hBrownian nu n hn hNu2 hNuNorm hNuMean x hx hSmall
    change |PN.real DA - d| ≤ Cs * R * Shao.standardNormalTail x at hPaid
    rw [← hDraw] at hPaid
    exact hPaid.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hR0) hPsi)
  · have hEtaR : etaS ≤ R := (lt_of_not_ge hSmall).le
    have hSigned := hSignedCompare rhoStar hrhoStar hrhoStarUpper p hp2 hp3
      mu rho n hn X hX hIndep hLaw h2 hmean hsecond hp
      1 x (Or.inl rfl) hx0 hxI
    have hCrossRaw := hSigned.2.2.2.1
    let U : Set Ω := {omega |
      x * Real.sqrt (rawEnergy omega) ≤ Shao.upperMax (population omega) hn}
    have hCross : |mu.real U - 2 * Shao.standardNormalTail x| ≤
        C1 * R * Shao.standardNormalTail x := by
      simpa only [one_smul] using hCrossRaw
    have hUpper : mu.real U ≤ 2 * Shao.standardNormalTail x +
        C1 * R * Shao.standardNormalTail x := by
      linarith only [(abs_le.mp hCross).2]
    have hSub : mu.real D ≤ mu.real U :=
      measureReal_mono (fun _ homega => homega.1)
    have hD0 : 0 ≤ mu.real D := measureReal_nonneg
    have hAbs : |mu.real D - d| ≤ mu.real D + d := by
      simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hD0, abs_of_nonneg hd0]
        using (abs_sub_le (mu.real D) 0 d)
    have hCoarse : |mu.real D - d| ≤
        4 * Shao.standardNormalTail x + C1 * R * Shao.standardNormalTail x := by
      linarith only [hAbs, hSub, hUpper, hd2]
    have hFour : (4 : ℝ) ≤ (4 / etaS) * R := by
      calc
        (4 : ℝ) = (4 / etaS) * etaS := by field_simp [hetaS.ne']
        _ ≤ (4 / etaS) * R :=
          mul_le_mul_of_nonneg_left hEtaR (by positivity)
    calc
      |mu.real D - d| ≤ 4 * Shao.standardNormalTail x +
          C1 * R * Shao.standardNormalTail x := hCoarse
      _ ≤ ((4 / etaS) * R) * Shao.standardNormalTail x +
          C1 * R * Shao.standardNormalTail x :=
        add_le_add (mul_le_mul_of_nonneg_right hFour hPsi) (le_refl _)
      _ = (C1 + 4 / etaS) * R * Shao.standardNormalTail x := by ring
      _ ≤ max Cs (C1 + 4 / etaS) * R * Shao.standardNormalTail x :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hR0) hPsi

end Shao.C2.OriginalGrowingDoubleComparison
