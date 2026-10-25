/- Actual original-law double-wall restoration. Frozen declaration v1; 
   local implementation in progress, no mechanical qualification claimed. -/
import Shao.Probability.SourceMomentDomain
import Shao.Probability.SourceClockBridge
import Shao.Probability.OriginalCDFPullback
import Shao.Probability.QuadraticEnergyLowerTail
import Shao.Probability.SourceNonresidualBrownian
import Shao.C2.AuxiliaryCenteredProductLaw
import Shao.C2.TwoSided

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option Elab.async false
noncomputable section
namespace Shao.Probability.SourceActualOriginalLawBridge
open MeasureTheory ProbabilityTheory
open Shao.C2.BridgeDomination
open scoped BigOperators NNReal

theorem original_iid_actual_centered_double_crossing_restoration_bridge :
    ∃ C : ℝ, 0 < C ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 / 4096 →
        ∀ p : ℝ, 2 < p → p ≤ 3 →
          ∀ {Ω ΩB : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩB]
            (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
            IsBrownianReal B PB →
            ∀ (mu : Measure Ω) (rho : Measure ℝ)
              [IsProbabilityMeasure mu] [IsProbabilityMeasure rho]
              (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ),
              (∀ i, AEMeasurable (X i) mu) →
              iIndepFun X mu →
              (∀ i, IdentDistrib (X i) (id : ℝ → ℝ) mu rho) →
              Integrable (fun z : ℝ => z ^ 2) rho →
              (∫ z : ℝ, z ∂rho) = 0 →
              0 < (∫ z : ℝ, z ^ 2 ∂rho) →
              Integrable (fun z : ℝ => Real.rpow |z| p) rho →
              let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
              let sigma : ℝ := Real.sqrt sigmaSq
              let scale : ℝ := sigma * Real.sqrt (n : ℝ)
              let nu : Measure ℝ := Measure.map (fun z : ℝ => z / scale) rho
              let PN : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
              let population : Ω → Shao.Path n := Shao.Probability.samplePath X
              let normalizedPath : Ω → Shao.Path n :=
                fun omega i => X i omega / scale
              let rawEnergy : Ω → ℝ := fun omega => ∑ i : Fin n, (X i omega) ^ 2
              ∀ x : ℝ, 1 ≤ x →
                let a : ℝ := 1 + x
                let R : ℝ := Shao.truncationBudget nu n x
                R ≤ epsilon ^ 3 / 2 ^ 20 →
                let cutoff : ℝ := epsilon / a
                let N : Set (Shao.Path n) := {v | ∀ i : Fin n, |v i| ≤ cutoff}
                let rawN : Set Ω := normalizedPath ⁻¹' N
                let pN : ℝ := mu.real rawN
                let rhoA : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ cutoff}
                let PA : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rhoA)
                let m : ℝ := ∫ z : ℝ, z ∂rhoA
                let g : ℝ := (n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂rhoA)
                let v0 : ℝ := (n : ℝ) * (∫ z : ℝ, (z - m) ^ 2 ∂rhoA)
                let d0 : ℝ := (n : ℝ) * |m|
                let shift : ℝ := 3 * d0
                let cpath : Shao.Path n → Shao.Path n := fun v i => v i - m
                let zpath : Shao.Path n → Shao.Path n :=
                  fun v i => Real.sqrt (n : ℝ) * (v i - m) / Real.sqrt v0
                let rhoZ : Measure ℝ := Measure.map
                  (fun z : ℝ => Real.sqrt (n : ℝ) * (z - m) / Real.sqrt v0) rhoA
                let PZ : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rhoZ)
                let delta : ℝ := (∫ z : ℝ, |z| ^ 3 ∂rhoZ) / Real.sqrt (n : ℝ)
                let E : Set (Shao.Path n) := {v | v0 / 2 ≤ Shao.energy (cpath v)}
                let DA : Set (Shao.Path n) := Shao.C2.doubleCrossing hn x
                let D : Set Ω := {omega |
                  x * Real.sqrt (rawEnergy omega) ≤ Shao.upperMax (population omega) hn ∧
                  x * Real.sqrt (rawEnergy omega) ≤ Shao.lowerMax (population omega) hn}
                let DB : ℝ → Set ΩB := fun y => {omega |
                  (∃ t : BridgeTime, y ≤ B ⟨(t : ℝ), t.property.1⟩ omega) ∧
                  ∃ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ omega ≤ -y}
                let d : ℝ → ℝ := fun y => PB.real (DB y)
                let Delta : ℝ := max
                  |PZ.real (Shao.C2.doubleCrossing hn (x - shift)) - d (x - shift)|
                  |PZ.real (Shao.C2.doubleCrossing hn (x + shift)) - d (x + shift)|
                R = (n : ℝ) * (∫ z : ℝ,
                    Shao.truncationF ((1 + x) * z / scale) ∂rho) ∧
                  0 < scale ∧ IsProbabilityMeasure rhoA ∧ IsProbabilityMeasure rhoZ ∧
                  Measure.map normalizedPath mu = PN ∧
                  ProbabilityTheory.cond PN N = PA ∧
                  Measure.map zpath PA = PZ ∧
                  NullMeasurableSet rawN mu ∧ NullMeasurableSet D mu ∧
                  Integrable (D.indicator (fun _ : Ω => (1 : ℝ))) mu ∧
                  MeasurableSet N ∧ MeasurableSet E ∧
                  pN = PN.real N ∧ (7 / 8 : ℝ) ≤ pN ∧ pN ≤ 1 ∧
                  1 - pN ≤ R / epsilon ^ 3 ∧
                  mu.real D = PN.real DA ∧
                  (1 / 2 : ℝ) ≤ v0 ∧ v0 ≤ (4 / 3 : ℝ) ∧
                  d0 ≤ 2 * R / (epsilon ^ 2 * a) ∧
                  g ≤ 2 * R / a ^ 3 ∧
                  0 ≤ shift ∧ shift ≤ 1 / (2 * a) ∧ a * shift ≤ 6 * R / epsilon ^ 2 ∧
                  x / Real.sqrt (n : ℝ) ≤ (1 / 2 : ℝ) ∧
                  Integrable (fun z : ℝ => z ^ 2) rhoZ ∧
                  Integrable (fun z : ℝ => |z| ^ 3) rhoZ ∧
                  (∫ z : ℝ, z ∂rhoZ) = 0 ∧
                  (∫ z : ℝ, z ^ 2 ∂rhoZ) = 1 ∧
                  0 < delta ∧ delta * a ^ 3 ≤ 64 * R ∧
                  (∀ y : ℝ, y ∈ Set.Icc (x - shift) (x + shift) →
                    (1 / 2 : ℝ) ≤ y ∧ y ≤ a ∧
                    (∀ᵐ z : ℝ ∂rhoZ, |z| ≤ Real.sqrt (n : ℝ) / (200 * y)) ∧
                    delta * (1 + y) ^ 3 ≤ 512 * R ∧
                    NullMeasurableSet (DB y) PB ∧
                    |d y - d x| ≤ C * (R / epsilon ^ 2) * Shao.standardNormalTail x) ∧
                  (∀ (v : Shao.Path n) (y : ℝ),
                    zpath v ∈ Shao.C2.doubleCrossing hn y ↔
                      cpath v ∈ Shao.C2.doubleCrossing hn y) ∧
                  ((zpath ⁻¹' Shao.C2.doubleCrossing hn (x + shift)) ∩ E ⊆ DA ∩ E) ∧
                  (DA ∩ E ⊆ (zpath ⁻¹' Shao.C2.doubleCrossing hn (x - shift)) ∩ E) ∧
                  PA.real Eᶜ ≤ Real.exp (-(1 / (64 * delta ^ 2))) ∧
                  PA.real Eᶜ ≤ C * R * Shao.standardNormalTail x ∧
                  PZ.real (Shao.C2.doubleCrossing hn (x + shift)) - PA.real Eᶜ ≤ PA.real DA ∧
                  PA.real DA ≤ PZ.real (Shao.C2.doubleCrossing hn (x - shift)) + PA.real Eᶜ ∧
                  mu.real (D ∩ rawNᶜ) ≤ C * (R / epsilon ^ 3) * Shao.standardNormalTail x ∧
                  mu.real D - d x =
                    pN * (PA.real DA - d x) + mu.real (D ∩ rawNᶜ) - (1 - pN) * d x ∧
                  |PA.real DA - d x| ≤ Delta + C * (R / epsilon ^ 2) * Shao.standardNormalTail x ∧
                  |mu.real D - d x| ≤ pN * Delta + C * (R / epsilon ^ 3) * Shao.standardNormalTail x := by
  classical
  obtain ⟨Cb, hCb, hBad⟩ := Shao.Probability.sourceTruncation_original_two_signs_bad_crossing
  let K : ℝ := Real.sqrt (2 * Real.pi)
  let CG : ℝ := 48 * Real.exp 2
  let CE : ℝ := 512 * K
  let C : ℝ := 1 + 2 * (CG + CE) + Cb + 2
  have hK : 0 < K := by dsimp [K]; positivity
  have hCG : 0 < CG := by dsimp [CG]; positivity
  have hCE : 0 < CE := by dsimp [CE]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hCGC : CG ≤ C := by dsimp [C]; linarith only [hCG, hCE, hCb]
  have hCbC : Cb ≤ C := by dsimp [C]; linarith only [hCG, hCE, hCb]
  have hCEC : CE ≤ C := by dsimp [C]; linarith only [hCG, hCE, hCb]
  have hCEC' : CG + CE ≤ C := by dsimp [C]; linarith only [hCG, hCE, hCb]
  refine ⟨C, hC, ?_⟩
  intro epsilon hepsilon hepsilon4096 p hp2 hp3 Ω ΩB hΩ hΩB B PB hPB hB
    mu rho hmu hRho n hn X hX hIndep hLaw h2 hmean hsecond hp
    sigmaSq sigma scale nu PN population normalizedPath rawEnergy x hx a R hRsmall
    cutoff N rawN pN rhoA PA m g v0 d0 shift cpath zpath rhoZ PZ delta E DA D DB d Delta
  letI : IsProbabilityMeasure PB := hPB
  letI : IsProbabilityMeasure mu := hmu
  letI : IsProbabilityMeasure rho := hRho
  have hx0 : 0 ≤ x := by linarith only [hx]
  have ha : 0 < a := by dsimp [a]; linarith only [hx]
  have ha1 : 1 ≤ a := by dsimp [a]; linarith only [hx]
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hepsilon1 : epsilon ≤ 1 := hepsilon4096.trans (by norm_num)
  have hepsilonHalf : epsilon ≤ 1 / 2 := hepsilon4096.trans (by norm_num)
  have hepsilon2 : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  have hepsilon3 : 0 < epsilon ^ 3 := pow_pos hepsilon 3
  have hRcut : R ≤ epsilon ^ 3 / 8 := by
    apply hRsmall.trans
    apply div_le_div_of_nonneg_left hepsilon3.le (by norm_num) (by norm_num)
  obtain ⟨hSigma, hNuProb, hNu2, hNuMean, hNorm, hNuP, hNuPEq,
    hLnPos, hLnEq, hNormMap, hSigned⟩ :=
    Shao.Probability.original_raw_normalization_data p hp2 hp3 rho n hn h2 hmean hsecond hp
  letI : IsProbabilityMeasure nu := hNuProb
  letI : IsProbabilityMeasure PN := by dsimp [PN]; infer_instance
  have hScale : 0 < scale := mul_pos hSigma (Real.sqrt_pos.2 hN)
  have hR0 : 0 ≤ R := by
    apply mul_nonneg hN.le
    apply integral_nonneg
    intro z
    exact Shao.truncationF_nonneg _
  have hRraw : R = (n : ℝ) * (∫ z : ℝ,
      Shao.truncationF ((1 + x) * z / scale) ∂rho) := by
    change (n : ℝ) * (∫ z : ℝ, Shao.truncationF ((1 + x) * z)
      ∂Measure.map (fun z : ℝ => z / scale) rho) = _
    rw [integral_map (show AEMeasurable (fun z : ℝ => z / scale) rho from by fun_prop)
      (show AEStronglyMeasurable (fun z : ℝ => Shao.truncationF ((1 + x) * z))
        (Measure.map (fun z : ℝ => z / scale) rho) from
        (Shao.continuous_truncationF.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)]
    simp only [div_eq_mul_inv, mul_assoc]
  let Praw : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  letI : IsProbabilityMeasure Praw := by dsimp [Praw]; infer_instance
  have hPop : AEMeasurable population mu := AEMeasurable.of_eval hX
  have hPopMap : Measure.map population mu = Praw := by
    change Measure.map (fun omega i => X i omega) mu = _
    rw [hIndep.map_fun_eq_pi_map hX]
    congr 1
    funext i
    simpa only [Measure.map_id] using (hLaw i).map_eq
  let Traw : Shao.Path n → Shao.Path n := fun v i => v i / scale
  have hTraw : Measurable Traw := by dsimp [Traw]; fun_prop
  have hNormPath : normalizedPath = Traw ∘ population := rfl
  have hNormalized : AEMeasurable normalizedPath mu := by
    rw [hNormPath]
    exact hTraw.comp_aemeasurable hPop
  have hNormalizedMap : Measure.map normalizedPath mu = PN := by
    rw [hNormPath, ← AEMeasurable.map_map_of_aemeasurable hTraw.aemeasurable hPop,
      hPopMap]
    exact hNormMap
  have hNormalizedPair : IdentDistrib normalizedPath (id : Shao.Path n → Shao.Path n) mu PN :=
    ⟨hNormalized, measurable_id.aemeasurable, by simpa only [Measure.map_id] using hNormalizedMap⟩
  have hDAm : MeasurableSet DA := Shao.C2.measurableSet_doubleCrossing hn x
  have hScaleEvent (v : Shao.Path n) (y : ℝ) :
      Traw v ∈ Shao.C2.doubleCrossing hn y ↔ v ∈ Shao.C2.doubleCrossing hn y := by
    have hc : 0 < scale⁻¹ := inv_pos.2 hScale
    have hTv : Traw v = scale⁻¹ • v := by
      funext i
      change v i / scale = scale⁻¹ * v i
      rw [div_eq_mul_inv, mul_comm]
    change (y * Real.sqrt (Shao.energy (Traw v)) ≤ Shao.upperMax (Traw v) hn ∧
      y * Real.sqrt (Shao.energy (Traw v)) ≤ Shao.lowerMax (Traw v) hn) ↔ _
    rw [hTv, Shao.energy_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc.le,
      Shao.upperMax_smul_of_nonneg _ hc.le, Shao.lowerMax_smul_of_nonneg _ hc.le]
    rw [show y * (scale⁻¹ * Real.sqrt (Shao.energy v)) =
      scale⁻¹ * (y * Real.sqrt (Shao.energy v)) by ring]
    simp only [mul_le_mul_iff_right₀ hc]
    rfl
  have hDpre : normalizedPath ⁻¹' DA = D := by
    ext omega
    exact hScaleEvent (population omega) x
  have hDn : NullMeasurableSet D mu := by
    rw [← hDpre]
    exact hNormalized.nullMeasurableSet_preimage hDAm
  have hDraw : mu.real D = PN.real DA := by
    have hh := congrArg ENNReal.toReal (hNormalizedPair.measure_mem_eq hDAm)
    simpa only [Measure.real, hDpre, Set.preimage_id] using hh
  have hDI : Integrable (D.indicator (fun _ : Ω => (1 : ℝ))) mu := by
    let f : Shao.Path n → ℝ := DA.indicator (fun _ => (1 : ℝ))
    have hfm : Measurable f := measurable_const.indicator hDAm
    have hfi : Integrable f PN := (integrable_const (1 : ℝ)).indicator hDAm
    have hi := (hNormalizedPair.comp hfm).integrable_iff.mpr hfi
    change Integrable (fun omega => f (normalizedPath omega)) mu at hi
    convert hi using 1
    funext omega
    rw [← hDpre]
    by_cases ho : normalizedPath omega ∈ DA <;> simp [f, Set.mem_preimage, ho]
  have hNm : MeasurableSet N := by
    have hrepr : N = ⋂ i : Fin n, {v : Shao.Path n | |v i| ≤ cutoff} := by
      ext v
      simp only [N, Set.mem_setOf_eq, Set.mem_iInter]
    rw [hrepr]
    exact MeasurableSet.iInter (fun i => measurableSet_le
      (continuous_abs.measurable.comp (measurable_pi_apply i)) measurable_const)
  have hRawNn : NullMeasurableSet rawN mu := hNormalized.nullMeasurableSet_preimage hNm
  have hpN : pN = PN.real N := by
    have hh := congrArg ENNReal.toReal (hNormalizedPair.measure_mem_eq hNm)
    simpa only [Measure.real, rawN, pN, Set.preimage_id] using hh
  obtain ⟨hMass, hMass1, hAprob, hAsp, hA1, hA2, hA3, hA4⟩ :=
    Shao.sourceTruncation_law_data nu n hNu2 hNorm x epsilon hx0 hepsilon hepsilonHalf hRcut
  letI : IsProbabilityMeasure rhoA := hAprob
  letI : IsProbabilityMeasure PA := by dsimp [PA]; infer_instance
  obtain ⟨hm, hg, h4, hC3, hC3le⟩ :=
    Shao.sourceTruncation_paid_moments nu n hNu2 hNorm hNuMean x epsilon hx0 hepsilon
      hepsilonHalf hRcut
  change d0 ≤ 2 * R / (epsilon ^ 2 * a) at hm
  change g ≤ 2 * R / a ^ 3 at hg
  obtain ⟨hA2lo, hA2hi, hmu2, hvDef, hvInt, hvPos, hvLo, hvHi⟩ :=
    Shao.sourceTruncation_variance_bounds nu n hNu2 hNorm hNuMean x epsilon hx0 hepsilon
      hepsilonHalf hRcut
  have hVeq : v0 = (n : ℝ) * variance (id : ℝ → ℝ) rhoA := by
    dsimp only [v0]
    rw [← hvInt]
  have hVlo : (1 / 2 : ℝ) ≤ v0 := by rw [hVeq]; exact hvLo
  have hVhi : v0 ≤ (4 / 3 : ℝ) := by rw [hVeq]; exact hvHi
  have hV : 0 < v0 := by linarith only [hVlo]
  have hC1 : Integrable (fun z : ℝ => z - m) rhoA := hA1.sub (integrable_const m)
  have hC2 : Integrable (fun z : ℝ => (z - m) ^ 2) rhoA := by
    convert (hA2.sub (hA1.const_mul (2 * m))).add (integrable_const (m ^ 2)) using 1
    funext z
    change (z - m) ^ 2 = z ^ 2 - (2 * m) * z + m ^ 2
    ring
  have hCMean : (∫ z : ℝ, z - m ∂rhoA) = 0 := by
    rw [integral_sub hA1 (integrable_const m)]
    simp only [integral_const, probReal_univ, one_smul]
    change m - m = 0
    ring
  let sV : ℝ := Real.sqrt v0
  have hsV : 0 < sV := Real.sqrt_pos.2 hV
  have hsV2 : sV ^ 2 = v0 := Real.sq_sqrt hV.le
  have hsVhalf : (1 / 2 : ℝ) ≤ sV := by
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hsV.le).mp
    rw [hsV2]
    nlinarith only [hVlo]
  let f : ℝ → ℝ := fun z => (z - m) / sV
  let zeta : Measure ℝ := Measure.map f rhoA
  have hfm : Measurable f := by fun_prop
  letI : IsProbabilityMeasure zeta := by dsimp [zeta]; infer_instance
  have hf2 : Integrable (fun z : ℝ => (f z) ^ 2) rhoA := by
    simpa only [f, div_pow] using hC2.div_const (sV ^ 2)
  have hfcube (z : ℝ) : |f z| ^ 3 = |z - m| ^ 3 / sV ^ 3 := by
    change |(z - m) / sV| ^ 3 = |z - m| ^ 3 / sV ^ 3
    rw [abs_div, abs_of_pos hsV, div_pow]
  have hf3 : Integrable (fun z : ℝ => |f z| ^ 3) rhoA :=
    (hC3.div_const (sV ^ 3)).congr (ae_of_all rhoA (fun z => (hfcube z).symm))
  have hz2 : Integrable (fun z : ℝ => z ^ 2) zeta :=
    (integrable_map_measure (continuous_id.pow 2).aestronglyMeasurable hfm.aemeasurable).2 hf2
  have hz3 : Integrable (fun z : ℝ => |z| ^ 3) zeta :=
    (integrable_map_measure (continuous_abs.pow 3).aestronglyMeasurable hfm.aemeasurable).2 hf3
  have hzMean : (∫ z : ℝ, z ∂zeta) = 0 := by
    rw [show zeta = Measure.map f rhoA from rfl,
      integral_map (μ := rhoA) (φ := f) (f := fun z : ℝ => z) hfm.aemeasurable
        continuous_id.aestronglyMeasurable]
    change (∫ z : ℝ, (z - m) / sV ∂rhoA) = 0
    rw [integral_div, hCMean, zero_div]
  have hzNorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂zeta) = 1 := by
    rw [show zeta = Measure.map f rhoA from rfl,
      integral_map (μ := rhoA) (φ := f) (f := fun z : ℝ => z ^ 2) hfm.aemeasurable
        (continuous_id.pow 2).aestronglyMeasurable]
    simp_rw [f, div_pow]
    rw [integral_div, ← mul_div_assoc, hsV2]
    change v0 / v0 = 1
    exact div_self hV.ne'
  let betaC : ℝ := (n : ℝ) * ∫ z : ℝ, |z| ^ 3 ∂zeta
  have hDeltaEq : betaC = ((n : ℝ) * ∫ z : ℝ, |z - m| ^ 3 ∂rhoA) / sV ^ 3 := by
    dsimp only [betaC, zeta]
    rw [integral_map (μ := rhoA) (φ := f) (f := fun z : ℝ => |z| ^ 3) hfm.aemeasurable
      (continuous_abs.pow 3).aestronglyMeasurable]
    simp_rw [hfcube]
    rw [integral_div, mul_div_assoc]
  have hDeltaBound : betaC ≤ 64 * R / a ^ 3 := by
    rw [hDeltaEq]
    apply (div_le_iff₀ (pow_pos hsV 3)).2
    have hc : (n : ℝ) * (∫ z : ℝ, |z - m| ^ 3 ∂rhoA) ≤ 8 * g := by
      have hh := mul_le_mul_of_nonneg_left hC3le hN.le
      convert hh using 1 <;> dsimp [g] <;> ring
    have hsCube : (1 / 4 : ℝ) ≤ sV ^ 3 := by
      calc
        _ = (1 / 2 : ℝ) * (1 / 2 : ℝ) := by norm_num
        _ ≤ v0 * sV := mul_le_mul hVlo hsVhalf (by norm_num) hV.le
        _ = sV ^ 3 := by rw [← hsV2]; ring
    have hRdiv : 0 ≤ R / a ^ 3 := by positivity
    have hHG : g ≤ 2 * (R / a ^ 3) := by simpa only [mul_div_assoc] using hg
    calc
      _ ≤ 8 * g := hc
      _ ≤ 8 * (2 * (R / a ^ 3)) := mul_le_mul_of_nonneg_left hHG (by norm_num)
      _ = (64 * (R / a ^ 3)) * (1 / 4) := by ring
      _ ≤ (64 * (R / a ^ 3)) * sV ^ 3 :=
        mul_le_mul_of_nonneg_left hsCube (by positivity)
      _ = _ := by ring
  have hmAbs : |m| ≤ epsilon / a := by
    calc
      _ = |∫ z : ℝ, z ∂rhoA| := rfl
      _ ≤ ∫ z : ℝ, |z| ∂rhoA := abs_integral_le_integral_abs
      _ ≤ ∫ _z : ℝ, epsilon / a ∂rhoA := integral_mono_ae hA1.abs (integrable_const _) hAsp
      _ = epsilon / a := by simp
  have hzSupport : ∀ᵐ z : ℝ ∂zeta, |z| ≤ 4 * epsilon / a := by
    apply (ae_map_iff hfm.aemeasurable (measurableSet_le continuous_abs.measurable measurable_const)).2
    filter_upwards [hAsp] with z hz
    change |z| ≤ epsilon / a at hz
    change |(z - m) / sV| ≤ 4 * epsilon / a
    rw [abs_div, abs_of_pos hsV]
    apply (div_le_iff₀ hsV).2
    have hzm : |z - m| ≤ 2 * epsilon / a :=
      (abs_sub z m).trans (by
        calc
          _ ≤ epsilon / a + epsilon / a := add_le_add hz hmAbs
          _ = _ := by ring)
    calc
      _ ≤ 2 * epsilon / a := hzm
      _ = (4 * (epsilon / a)) * (1 / 2) := by ring
      _ ≤ (4 * (epsilon / a)) * sV :=
        mul_le_mul_of_nonneg_left hsVhalf (by positivity)
      _ = _ := by ring
  let sn : ℝ := Real.sqrt (n : ℝ)
  have hsn : 0 < sn := Real.sqrt_pos.2 hN
  have hsn2 : sn ^ 2 = (n : ℝ) := Real.sq_sqrt hN.le
  let sf : ℝ → ℝ := fun z => sn * f z
  have hsfm : Measurable sf := by dsimp [sf]; fun_prop
  have hsf : (fun z : ℝ => Real.sqrt (n : ℝ) * (z - m) / Real.sqrt v0) = sf := by
    funext z
    dsimp [sf, sn, f, sV]
    ring
  have hRhoZ : rhoZ = Measure.map sf rhoA := by rw [← hsf]
  letI : IsProbabilityMeasure rhoZ := by rw [hRhoZ]; infer_instance
  letI : IsProbabilityMeasure PZ := by dsimp [PZ]; infer_instance
  have hsf2 : Integrable (fun z : ℝ => (sf z) ^ 2) rhoA := by
    simpa only [sf, mul_pow] using hf2.const_mul (sn ^ 2)
  have hsf3 : Integrable (fun z : ℝ => |sf z| ^ 3) rhoA := by
    simpa only [sf, abs_mul, abs_of_pos hsn, mul_pow] using hf3.const_mul (sn ^ 3)
  have hZ2 : Integrable (fun z : ℝ => z ^ 2) rhoZ := by
    rw [hRhoZ]
    exact (integrable_map_measure (continuous_id.pow 2).aestronglyMeasurable hsfm.aemeasurable).2 hsf2
  have hZ3 : Integrable (fun z : ℝ => |z| ^ 3) rhoZ := by
    rw [hRhoZ]
    exact (integrable_map_measure (continuous_abs.pow 3).aestronglyMeasurable hsfm.aemeasurable).2 hsf3
  have hZMean : (∫ z : ℝ, z ∂rhoZ) = 0 := by
    rw [hRhoZ, integral_map (μ := rhoA) (φ := sf) (f := fun z : ℝ => z)
      hsfm.aemeasurable continuous_id.aestronglyMeasurable]
    change (∫ z : ℝ, sn * ((z - m) / sV) ∂rhoA) = 0
    rw [integral_const_mul, integral_div, hCMean]
    ring
  have hZNorm : (∫ z : ℝ, z ^ 2 ∂rhoZ) = 1 := by
    rw [hRhoZ, integral_map (μ := rhoA) (φ := sf) (f := fun z : ℝ => z ^ 2)
      hsfm.aemeasurable (continuous_id.pow 2).aestronglyMeasurable]
    simp_rw [sf, mul_pow]
    rw [integral_const_mul, hsn2]
    have hh := hzNorm
    rw [show zeta = Measure.map f rhoA from rfl,
      integral_map (μ := rhoA) (φ := f) (f := fun z : ℝ => z ^ 2)
        hfm.aemeasurable (continuous_id.pow 2).aestronglyMeasurable] at hh
    exact hh
  have hDelta : delta = betaC := by
    change (∫ z : ℝ, |z| ^ 3 ∂rhoZ) / sn = betaC
    rw [hRhoZ, integral_map (μ := rhoA) (φ := sf) (f := fun z : ℝ => |z| ^ 3)
      hsfm.aemeasurable (continuous_abs.pow 3).aestronglyMeasurable]
    simp_rw [sf, abs_mul, abs_of_pos hsn, mul_pow]
    rw [integral_const_mul]
    dsimp only [betaC, zeta]
    rw [integral_map (μ := rhoA) (φ := f) (f := fun z : ℝ => |z| ^ 3)
      hfm.aemeasurable (continuous_abs.pow 3).aestronglyMeasurable]
    rw [← hsn2]
    field_simp
  have hZSupport : ∀ᵐ z : ℝ ∂rhoZ, |z| ≤ 4 * epsilon * sn / a := by
    rw [hRhoZ]
    apply (ae_map_iff hsfm.aemeasurable (measurableSet_le continuous_abs.measurable measurable_const)).2
    have hfSupport : ∀ᵐ z : ℝ ∂rhoA, |f z| ≤ 4 * epsilon / a := by
      exact (ae_map_iff hfm.aemeasurable (measurableSet_le continuous_abs.measurable measurable_const)).1 hzSupport
    filter_upwards [hfSupport] with z hz
    change |sn * f z| ≤ _
    rw [abs_mul, abs_of_pos hsn]
    calc
      _ ≤ sn * (4 * epsilon / a) := mul_le_mul_of_nonneg_left hz hsn.le
      _ = _ := by ring
  have hCm : Measurable cpath := by dsimp [cpath]; fun_prop
  have hZm : Measurable zpath := by dsimp [zpath]; fun_prop
  have hZmap : Measure.map zpath PA = PZ := by
    change Measure.map (fun v : Shao.Path n => fun i =>
      Real.sqrt (n : ℝ) * (v i - m) / Real.sqrt v0) PA = PZ
    exact Measure.pi_map_pi (fun _ : Fin n => (by fun_prop :
      AEMeasurable (fun z : ℝ => Real.sqrt (n : ℝ) * (z - m) / Real.sqrt v0) rhoA))
  have hEm : MeasurableSet E := measurableSet_le measurable_const
    (Shao.measurable_energy.comp hCm)
  let PC : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => zeta)
  let TC : Shao.Path n → Shao.Path n := fun v i => f (v i)
  letI : IsProbabilityMeasure PC := by dsimp [PC]; infer_instance
  have hTCm : Measurable TC := Measurable.of_eval (fun i => hfm.comp (measurable_pi_apply i))
  have hTCmap : Measure.map TC PA = PC := Measure.pi_map_pi (fun _ : Fin n => hfm.aemeasurable)
  have hTCscale (v : Shao.Path n) : TC v = sV⁻¹ • cpath v := by
    funext i
    change (v i - m) / sV = sV⁻¹ * (v i - m)
    rw [div_eq_mul_inv, mul_comm]
  have hZscale (v : Shao.Path n) : zpath v = (sn / sV) • cpath v := by
    funext i
    change sn * (v i - m) / sV = (sn / sV) * (v i - m)
    ring
  have hZevent (v : Shao.Path n) (y : ℝ) :
      zpath v ∈ Shao.C2.doubleCrossing hn y ↔ cpath v ∈ Shao.C2.doubleCrossing hn y := by
    have hc : 0 < sn / sV := div_pos hsn hsV
    change (y * Real.sqrt (Shao.energy (zpath v)) ≤ Shao.upperMax (zpath v) hn ∧
      y * Real.sqrt (Shao.energy (zpath v)) ≤ Shao.lowerMax (zpath v) hn) ↔ _
    rw [hZscale, Shao.energy_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc.le,
      Shao.upperMax_smul_of_nonneg _ hc.le, Shao.lowerMax_smul_of_nonneg _ hc.le]
    rw [show y * ((sn / sV) * Real.sqrt (Shao.energy (cpath v))) =
      (sn / sV) * (y * Real.sqrt (Shao.energy (cpath v))) by ring]
    simp only [mul_le_mul_iff_right₀ hc]
    rfl
  have hNrepr : (⋂ i : Fin n, (Function.eval i) ⁻¹' {z : ℝ | |z| ≤ epsilon / a}) = N := by
    ext v
    simp only [N, cutoff, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq, Function.eval]
  have hPNIndep : iIndepFun (fun i : Fin n => Function.eval i) PN :=
    iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
  have hPNLaw (i : Fin n) : IdentDistrib (Function.eval i) (id : ℝ → ℝ) PN nu := by
    refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    exact (measurePreserving_eval (fun _ : Fin n => nu) i).map_eq.trans Measure.map_id.symm
  have hData := Shao.Probability.sourceTruncation_conditioned_sample
    (fun i : Fin n => measurable_pi_apply i) hPNIndep hPNLaw hNu2
    x epsilon hx0 hepsilon hepsilon1 hRcut
  dsimp only at hData
  change PN.real ((⋂ i : Fin n, (Function.eval i) ⁻¹' {z : ℝ | |z| ≤ epsilon / a})ᶜ) ≤
    R / epsilon ^ 3 ∧ _ at hData
  rw [hNrepr] at hData
  have hCond : ProbabilityTheory.cond PN N = PA := by
    have hh := hData.2.2.2.1
    change Measure.map (id : Shao.Path n → Shao.Path n) (ProbabilityTheory.cond PN N) = PA at hh
    simpa only [Measure.map_id] using hh
  have hpNlo : (7 / 8 : ℝ) ≤ pN := by rw [hpN]; exact hData.2.1
  have hpN1 : pN ≤ 1 := measureReal_le_one
  have hpN0 : 0 ≤ pN := measureReal_nonneg
  have hpNbad : 1 - pN ≤ R / epsilon ^ 3 := by
    rw [hpN]
    have hc := measureReal_compl (μ := PN) hNm
    simp only [Measure.real, measure_univ, ENNReal.toReal_one] at hc
    change PN.real Nᶜ = 1 - PN.real N at hc
    rw [← hc]
    exact hData.1
  have hd0 : 0 ≤ d0 := by dsimp [d0]; positivity
  have hShift0 : 0 ≤ shift := by dsimp [shift]; positivity
  have haShift : a * shift ≤ 6 * R / epsilon ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ 3 * a by positivity)
    have heq : 3 * a * (2 * R / (epsilon ^ 2 * a)) = 6 * R / epsilon ^ 2 := by
      field_simp
      ring
    dsimp only [shift]
    nlinarith only [hh, heq]
  have haShiftSmall : a * shift ≤ 1 / 2 := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hRsmall (by norm_num : (0 : ℝ) ≤ 6)) hepsilon2.le
    have heq : 6 * (epsilon ^ 3 / 2 ^ 20) / epsilon ^ 2 = 6 * epsilon / 2 ^ 20 := by
      field_simp
    have hnum : 6 * epsilon / 2 ^ 20 ≤ (1 / 2 : ℝ) := by
      nlinarith only [hepsilon4096]
    rw [heq] at hh
    exact haShift.trans (hh.trans hnum)
  have hShiftNear : shift ≤ 1 / (2 * a) := (le_div_iff₀ (by positivity : 0 < 2 * a)).2
    (by nlinarith only [haShiftSmall])
  have hShiftHalf : shift ≤ (1 / 2 : ℝ) := by
    have hh : 1 / (2 * a) ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * a)).2
      linarith only [ha1]
    exact hShiftNear.trans hh
  have hYbounds (y : ℝ) (hy : y ∈ Set.Icc (x - shift) (x + shift)) :
      (1 / 2 : ℝ) ≤ y ∧ y ≤ a := by
    constructor
    · linarith only [hy.1, hx, hShiftHalf]
    · change y ≤ 1 + x
      linarith only [hy.2, hShiftHalf]
  have hASquare : (∫ z : ℝ, z ^ 2 ∂rhoA) ≤ (epsilon / a) ^ 2 := by
    calc
      _ ≤ ∫ _z : ℝ, (epsilon / a) ^ 2 ∂rhoA := by
        apply integral_mono_ae hA2 (integrable_const _)
        filter_upwards [hAsp] with z hz
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg z) (by positivity)).2 hz
      _ = (epsilon / a) ^ 2 := by simp
  have hSample : x ≤ sn / 2 := by
    have hh : (3 / 4 : ℝ) ≤ (n : ℝ) * (epsilon / a) ^ 2 :=
      hA2lo.trans (mul_le_mul_of_nonneg_left hASquare hN.le)
    have hh' : (3 / 4 : ℝ) * a ^ 2 ≤ (n : ℝ) * epsilon ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos ha)).mp
      simpa only [div_pow, mul_div_assoc] using hh
    have hxa2 : x ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hx0 (by dsimp [a]; linarith only [hx]) 2
    have hepssq : epsilon ^ 2 ≤ (1 / 16 : ℝ) := by
      have hh := pow_le_pow_left₀ hepsilon.le (hepsilon4096.trans (by norm_num : (1 / 4096 : ℝ) ≤ 1 / 4)) 2
      norm_num at hh
      exact hh
    have hepsN := mul_le_mul_of_nonneg_left hepssq hN.le
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    apply (sq_le_sq₀ (by positivity : 0 ≤ x * 2) hsn.le).mp
    rw [mul_pow, hsn2]
    nlinarith only [hh', hxa2, hepsN]
  have hSampleRatio : x / Real.sqrt (n : ℝ) ≤ (1 / 2 : ℝ) :=
    (div_le_iff₀ hsn).2 (by linarith only [hSample])
  have hGeometry (v : Shao.Path n) :
      Real.sqrt (Shao.energy (cpath v)) ≤ Real.sqrt (Shao.energy v) + sn * |m| :=
    (Shao.C2.AuxiliaryCenteredEvent.auxiliary_centered_path_energy_and_sum v m).2
  have hGeometryRev (v : Shao.Path n) :
      Real.sqrt (Shao.energy v) ≤ Real.sqrt (Shao.energy (cpath v)) + sn * |m| := by
    have hh := (Shao.C2.AuxiliaryCenteredEvent.auxiliary_centered_path_energy_and_sum (cpath v) (-m)).2
    have heq : (fun i : Fin n => cpath v i - -m) = v := by
      funext i
      change v i - m - -m = v i
      ring
    simpa only [heq, abs_neg] using hh
  have hPrefix (v : Shao.Path n) (k : ℕ) :
      |Shao.prefixSum v k - Shao.prefixSum (cpath v) k| ≤ d0 := by
    let U : Finset (Fin n) := Finset.univ.filter (fun i => i.val < k)
    have hcard : U.card ≤ n := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_le_card (Finset.filter_subset (fun i : Fin n => i.val < k) Finset.univ))
    have hcardR : (U.card : ℝ) ≤ n := by exact_mod_cast hcard
    change |(∑ i ∈ U, v i) - ∑ i ∈ U, (v i - m)| ≤ d0
    rw [← Finset.sum_sub_distrib]
    simp only [sub_sub_cancel, Finset.sum_const, nsmul_eq_mul, abs_mul]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ (U.card : ℝ) from Nat.cast_nonneg U.card)]
    exact mul_le_mul_of_nonneg_right hcardR (abs_nonneg m)
  have hQC (v : Shao.Path n) (hv : v ∈ E) :
      (1 / 2 : ℝ) ≤ Real.sqrt (Shao.energy (cpath v)) := by
    have he : v0 / 2 ≤ Shao.energy (cpath v) := hv
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (Real.sqrt_nonneg (Shao.energy (cpath v)))).mp
    rw [Real.sq_sqrt (Shao.energy_nonneg (cpath v))]
    linarith only [he, hVlo]
  have hDrift : x * (sn * |m|) ≤ d0 / 2 := by
    calc
      _ ≤ (sn / 2) * (sn * |m|) := mul_le_mul_of_nonneg_right hSample (by positivity)
      _ = d0 / 2 := by
        dsimp [d0]
        rw [show sn / 2 * (sn * |m|) = sn ^ 2 * |m| / 2 by ring, hsn2]
  have hWallShift (v : Shao.Path n) (hv : v ∈ E) :
      d0 + x * (sn * |m|) ≤ shift * Real.sqrt (Shao.energy (cpath v)) := by
    have hh := mul_le_mul_of_nonneg_left (hQC v hv) hShift0
    dsimp only [shift] at hh ⊢
    linarith only [hh, hDrift]
  have hContainLo : DA ∩ E ⊆
      (zpath ⁻¹' Shao.C2.doubleCrossing hn (x - shift)) ∩ E := by
    intro v hv
    refine ⟨(hZevent v (x - shift)).2 ?_, hv.2⟩
    have hWall : (x - shift) * Real.sqrt (Shao.energy (cpath v)) ≤
        x * Real.sqrt (Shao.energy v) - d0 := by
      have hh := mul_le_mul_of_nonneg_left (hGeometry v) hx0
      nlinarith only [hh, hWallShift v hv.2]
    change ((x - shift) * Real.sqrt (Shao.energy (cpath v)) ≤ Shao.upperMax (cpath v) hn) ∧
      ((x - shift) * Real.sqrt (Shao.energy (cpath v)) ≤ Shao.lowerMax (cpath v) hn)
    constructor
    · obtain ⟨k, hk, hkn, hw⟩ := (Shao.upperMax_ge_iff v hn _).mp hv.1.1
      have hp := (le_abs_self (Shao.prefixSum v k - Shao.prefixSum (cpath v) k)).trans (hPrefix v k)
      exact (show (x - shift) * Real.sqrt (Shao.energy (cpath v)) ≤ Shao.prefixSum (cpath v) k by
        linarith only [hWall, hw, hp]).trans (Shao.le_upperMax (cpath v) hn k hk hkn)
    · obtain ⟨k, hk, hkn, hw⟩ := (Shao.upperMax_ge_iff (-v) hn _).mp hv.1.2
      have hp := (neg_le_abs (Shao.prefixSum v k - Shao.prefixSum (cpath v) k)).trans (hPrefix v k)
      rw [Shao.prefixSum_neg] at hw
      change (x - shift) * Real.sqrt (Shao.energy (cpath v)) ≤ Shao.upperMax (-(cpath v)) hn
      have hw' := Shao.le_upperMax (-(cpath v)) hn k hk hkn
      rw [Shao.prefixSum_neg] at hw'
      linarith only [hWall, hw, hp, hw']
  have hContainHi : (zpath ⁻¹' Shao.C2.doubleCrossing hn (x + shift)) ∩ E ⊆ DA ∩ E := by
    intro v hv
    have hcv := (hZevent v (x + shift)).1 hv.1
    refine ⟨?_, hv.2⟩
    have hWall : x * Real.sqrt (Shao.energy v) ≤
        (x + shift) * Real.sqrt (Shao.energy (cpath v)) - d0 := by
      have hh := mul_le_mul_of_nonneg_left (hGeometryRev v) hx0
      nlinarith only [hh, hWallShift v hv.2]
    change (x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax v hn) ∧
      (x * Real.sqrt (Shao.energy v) ≤ Shao.lowerMax v hn)
    constructor
    · obtain ⟨k, hk, hkn, hw⟩ := (Shao.upperMax_ge_iff (cpath v) hn _).mp hcv.1
      have hp := (neg_le_abs (Shao.prefixSum v k - Shao.prefixSum (cpath v) k)).trans (hPrefix v k)
      exact (show x * Real.sqrt (Shao.energy v) ≤ Shao.prefixSum v k by
        linarith only [hWall, hw, hp]).trans (Shao.le_upperMax v hn k hk hkn)
    · obtain ⟨k, hk, hkn, hw⟩ := (Shao.upperMax_ge_iff (-(cpath v)) hn _).mp hcv.2
      have hp := (le_abs_self (Shao.prefixSum v k - Shao.prefixSum (cpath v) k)).trans (hPrefix v k)
      rw [Shao.prefixSum_neg] at hw
      change x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (-v) hn
      have hw' := Shao.le_upperMax (-v) hn k hk hkn
      rw [Shao.prefixSum_neg] at hw'
      linarith only [hWall, hw, hp, hw']
  obtain ⟨hBetaC, hLow⟩ := finite_iid_energy_lower_tail zeta n hn hz2 hz3 hzNorm
    (1 / 2) (by norm_num) (by norm_num)
  change 0 < betaC at hBetaC
  have hR : 0 < R := by
    have hh := (le_div_iff₀ (pow_pos ha 3)).mp hDeltaBound
    have hp := mul_pos hBetaC (pow_pos ha 3)
    nlinarith only [hh, hp]
  change PC.real {v : Shao.Path n | Shao.energy v ≤ 1 - (1 / 2 : ℝ)} ≤
    Real.exp (-((1 / 2 : ℝ) ^ 3 / (8 * betaC ^ 2))) at hLow
  norm_num at hLow
  have hEnergyT (A : Shao.Path n) : Shao.energy (TC A) = Shao.energy (cpath A) / v0 := by
    rw [hTCscale, Shao.energy_smul, inv_pow, hsV2]
    ring
  have hLowContain : Eᶜ ⊆ TC ⁻¹' {v : Shao.Path n | Shao.energy v ≤ 1 / 2} := by
    intro A hA
    have hh : Shao.energy (cpath A) < v0 / 2 := lt_of_not_ge hA
    change Shao.energy (TC A) ≤ (1 / 2 : ℝ)
    rw [hEnergyT]
    exact (div_le_iff₀ hV).2 (by linarith only [hh])
  have hELowC : PA.real Eᶜ ≤ Real.exp (-(1 / (64 * betaC ^ 2))) := by
    calc
      _ ≤ PA.real (TC ⁻¹' {v : Shao.Path n | Shao.energy v ≤ 1 / 2}) :=
        measureReal_mono hLowContain
      _ = PC.real {v : Shao.Path n | Shao.energy v ≤ 1 / 2} := by
        rw [← hTCmap]
        simp only [Measure.real_def]
        rw [Measure.map_apply hTCm (measurableSet_le Shao.measurable_energy measurable_const)]
      _ ≤ _ := by convert hLow using 1 <;> congr 1 <;> field_simp <;> ring
  let q : ℝ := 512 * R
  have hq : 0 < q := by dsimp [q]; positivity
  have hqsmall : q ≤ 1 / 32 := by
    have hepsCube := pow_le_pow_left₀ hepsilon.le hepsilon1 3
    norm_num at hepsCube
    dsimp only [q]
    nlinarith only [hRsmall, hepsCube]
  have hLowExponent : a ^ 6 / (16 * q ^ 2) ≤ 1 / (64 * betaC ^ 2) := by
    have hd : betaC * a ^ 3 ≤ 64 * R := (le_div_iff₀ (pow_pos ha 3)).mp hDeltaBound
    have hs := pow_le_pow_left₀ (show 0 ≤ betaC * a ^ 3 by positivity) hd 2
    apply (div_le_div_iff₀ (by positivity : 0 < 16 * q ^ 2)
      (by positivity : 0 < 64 * betaC ^ 2)).2
    dsimp only [q]
    nlinarith only [hs, sq_nonneg R]
  have hNumericExponent : x ^ 2 / 2 + a / q ≤ a ^ 6 / (16 * q ^ 2) := by
    have ha6 : a ^ 2 ≤ a ^ 6 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) ha1 4
      norm_num at hh
      nlinarith only [mul_le_mul_of_nonneg_left hh (sq_nonneg a)]
    have h32 : 32 * q ≤ a := by linarith only [hqsmall, ha1]
    have hq2 : q ^ 2 ≤ 1 / 16 := by
      have hh := pow_le_pow_left₀ hq.le hqsmall 2
      norm_num at hh
      linarith only [hh]
    apply (le_div_iff₀ (by positivity : 0 < 16 * q ^ 2)).2
    have hid : a / q * (16 * q ^ 2) = 16 * a * q := by field_simp
    rw [add_mul, hid]
    have hxa : x ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hx0 (by dsimp [a]; linarith only [hx, hx0]) 2
    have hpart : 8 * x ^ 2 * q ^ 2 ≤ a ^ 2 / 2 := by
      have hh := mul_le_mul_of_nonneg_left hq2 (sq_nonneg x)
      nlinarith only [hh, hxa]
    have hpart2 : 16 * a * q ≤ a ^ 2 / 2 := by
      nlinarith only [mul_le_mul_of_nonneg_left h32 ha.le]
    nlinarith only [hpart, hpart2, ha6]
  have hExpSmall : Real.exp (-(a / q)) ≤ q / a := by
    have hh : a / q ≤ Real.exp (a / q) := by linarith only [Real.add_one_le_exp (a / q)]
    have hm := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-(a / q))).le
    rw [show Real.exp (a / q) * Real.exp (-(a / q)) = 1 by
      rw [← Real.exp_add]; simp] at hm
    apply (le_div_iff₀ ha).2
    have hm' := mul_le_mul_of_nonneg_right hm hq.le
    convert hm' using 1 <;> field_simp <;> ring
  have hDensity : Real.exp (-x ^ 2 / 2) = K * Shao.standardNormalDensity x := by
    dsimp [K]
    simp only [Shao.standardNormalDensity, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
    field_simp
  have hMills : Real.exp (-x ^ 2 / 2) / a ≤ K * Shao.standardNormalTail x := by
    rw [hDensity, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (Shao.standardNormal_mills_bounds x hx0).1 hK.le
  have hEPaidC : PA.real Eᶜ ≤ 512 * K * R * Shao.standardNormalTail x := by
    calc
      _ ≤ Real.exp (-(1 / (64 * betaC ^ 2))) := hELowC
      _ ≤ Real.exp (-(a ^ 6 / (16 * q ^ 2))) := Real.exp_le_exp.2 (neg_le_neg hLowExponent)
      _ ≤ Real.exp (-(x ^ 2 / 2 + a / q)) := Real.exp_le_exp.2 (neg_le_neg hNumericExponent)
      _ = Real.exp (-x ^ 2 / 2) * Real.exp (-(a / q)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-x ^ 2 / 2) * (q / a) :=
        mul_le_mul_of_nonneg_left hExpSmall (Real.exp_pos _).le
      _ = q * (Real.exp (-x ^ 2 / 2) / a) := by ring
      _ ≤ q * (K * Shao.standardNormalTail x) := mul_le_mul_of_nonneg_left hMills hq.le
      _ = _ := by dsimp [q]; ring
  have hDeltaPos : 0 < delta := by rw [hDelta]; exact hBetaC
  have hDeltaBound' : delta * a ^ 3 ≤ 64 * R := by
    rw [hDelta]
    exact (le_div_iff₀ (pow_pos ha 3)).mp hDeltaBound
  have hELow : PA.real Eᶜ ≤ Real.exp (-(1 / (64 * delta ^ 2))) := by
    rw [hDelta]
    exact hELowC
  have hEPaid : PA.real Eᶜ ≤ CE * R * Shao.standardNormalTail x := hEPaidC
  have hTail : 0 < Shao.standardNormalTail x := (Shao.standardNormalTail_basic.2.2.1 x).1
  have hR2 : 0 ≤ (R / epsilon ^ 2) * Shao.standardNormalTail x := by positivity
  have hR3 : 0 ≤ (R / epsilon ^ 3) * Shao.standardNormalTail x := by positivity
  have hFee23 : (R / epsilon ^ 2) * Shao.standardNormalTail x ≤
      (R / epsilon ^ 3) * Shao.standardNormalTail x := by
    apply mul_le_mul_of_nonneg_right _ hTail.le
    apply div_le_div_of_nonneg_left hR.le hepsilon3
    nlinarith only [mul_le_mul_of_nonneg_left hepsilon1 hepsilon2.le]
  have hFee02 : R * Shao.standardNormalTail x ≤
      (R / epsilon ^ 2) * Shao.standardNormalTail x := by
    apply mul_le_mul_of_nonneg_right _ hTail.le
    apply (le_div_iff₀ hepsilon2).2
    have hepssq : epsilon ^ 2 ≤ 1 := by nlinarith only [hepsilon.le, hepsilon1]
    exact mul_le_of_le_one_right hR.le hepssq
  have hEPaid2 : PA.real Eᶜ ≤ CE * ((R / epsilon ^ 2) * Shao.standardNormalTail x) := by
    calc
      _ ≤ CE * (R * Shao.standardNormalTail x) := by simpa only [mul_assoc] using hEPaid
      _ ≤ _ := mul_le_mul_of_nonneg_left hFee02 hCE.le
  have hYdata (y : ℝ) (hy : y ∈ Set.Icc (x - shift) (x + shift)) :
      (1 / 2 : ℝ) ≤ y ∧ y ≤ a ∧
      (∀ᵐ z : ℝ ∂rhoZ, |z| ≤ Real.sqrt (n : ℝ) / (200 * y)) ∧
      delta * (1 + y) ^ 3 ≤ 512 * R := by
    obtain ⟨hyhalf, hya⟩ := hYbounds y hy
    have hy0 : 0 < y := by linarith only [hyhalf]
    have hcap : 4 * epsilon * sn / a ≤ sn / (200 * y) := by
      apply (div_le_div_iff₀ ha (by positivity : 0 < 200 * y)).2
      have hnum : 800 * epsilon ≤ 1 := by nlinarith only [hepsilon4096]
      have hh := mul_le_mul_of_nonneg_right hnum (mul_nonneg hsn.le hy0.le)
      have hh' := mul_le_mul_of_nonneg_left hya hsn.le
      nlinarith only [hh, hh']
    refine ⟨hyhalf, hya, ?_, ?_⟩
    · filter_upwards [hZSupport] with z hz
      exact hz.trans hcap
    · have hya2 : 1 + y ≤ 2 * a := by linarith only [hya, ha1]
      calc
        _ ≤ delta * (2 * a) ^ 3 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by linarith only [hyhalf]) hya2 3) hDeltaPos.le
        _ = 8 * (delta * a ^ 3) := by ring
        _ ≤ _ := by linarith only [hDeltaBound']
  let H : ℝ → ℝ := fun y => PB.real {omega | ∃ t : BridgeTime,
    y ≤ |B ⟨(t : ℝ), t.property.1⟩ omega|}
  have hBData (y : ℝ) (hy : 0 < y) :
      NullMeasurableSet (DB y) PB ∧
      d y = 4 * Shao.standardNormalTail y - H y ∧
      0 ≤ d y ∧ d y ≤ 2 * Shao.standardNormalTail y := by
    obtain ⟨hU, hL, hDB, hUL, hId, hd0, hdCoarse, hdExp⟩ :=
      Shao.Probability.SourceNonresidualBrownian.actual_brownian_weak_double_crossing B PB hB y hy
    exact ⟨hDB, hId, hd0, hdCoarse⟩
  have hBAnti (s t : ℝ) (hst : s ≤ t) : d t ≤ d s := by
    apply measureReal_mono (μ := PB)
    intro omega homega
    rcases homega with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    exact ⟨⟨u, hst.trans hu⟩, ⟨v, hv.trans (neg_le_neg hst)⟩⟩
  have hHAnti (s t : ℝ) (hst : s ≤ t) : H t ≤ H s := by
    apply measureReal_mono (μ := PB)
    intro omega homega
    rcases homega with ⟨u, hu⟩
    exact ⟨u, hst.trans hu⟩
  have hBDiff (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (hst : s ≤ t) :
      d s - d t ≤ 4 * (Shao.standardNormalTail s - Shao.standardNormalTail t) := by
    have hsId := (hBData s hs).2.1
    have htId := (hBData t ht).2.1
    have hHA := hHAnti s t hst
    linarith only [hsId, htId, hHA]
  have hTailShift (y : ℝ) (hy : y ∈ Set.Icc (x - shift) (x + shift)) :
      |Shao.standardNormalTail y - Shao.standardNormalTail x| ≤
        2 * Real.exp 2 * a * shift * Shao.standardNormalTail x := by
    have hNear (t : ℝ) (ht : t ∈ Set.Icc (x - shift) (x + shift)) :
        |t - x| ≤ 1 / (1 + x) := by
      have habs : |t - x| ≤ shift := abs_le.mpr ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
      have hh : 1 / (2 * a) ≤ 1 / a := by
        apply div_le_div_of_nonneg_left (by norm_num) ha
        linarith only [ha.le]
      exact habs.trans (hShiftNear.trans hh)
    have hDerivative (t : ℝ) (ht : t ∈ Set.Icc (x - shift) (x + shift)) :
        ‖deriv Shao.standardNormalTail t‖ ≤ 2 * Real.exp 2 * a * Shao.standardNormalTail x := by
      obtain ⟨hthalf, hta⟩ := hYbounds t ht
      have ht0 : 0 ≤ t := by linarith only [hthalf]
      have hphi0 : 0 ≤ Shao.standardNormalDensity t := by
        unfold Shao.standardNormalDensity gaussianPDFReal
        positivity
      rw [(Shao.standardNormal_derivatives t).2.deriv, norm_neg,
        Real.norm_eq_abs, abs_of_nonneg hphi0]
      have hphi := (div_le_iff₀ (show 0 < 1 + t by linarith only [ht0])).mp
        (Shao.standardNormal_mills_bounds t ht0).1
      have htTail := (Shao.standardNormalTail_local_comparison x t hx0 ht0 (hNear t ht)).2
      have hCoeff : 1 + t ≤ 2 * a := by linarith only [hta, ha1]
      calc
        _ ≤ Shao.standardNormalTail t * (1 + t) := hphi
        _ ≤ (Real.exp 2 * Shao.standardNormalTail x) * (2 * a) :=
          mul_le_mul htTail hCoeff (by linarith only [ht0]) (by positivity)
        _ = _ := by ring
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
      (C := 2 * Real.exp 2 * a * Shao.standardNormalTail x)
      (fun t (_ : t ∈ Set.Icc (x - shift) (x + shift)) =>
        (Shao.standardNormal_derivatives t).2.differentiableAt)
      hDerivative (convex_Icc (x - shift) (x + shift))
      (show x ∈ Set.Icc (x - shift) (x + shift) from ⟨by linarith only [hShift0], by linarith only [hShift0]⟩) hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    have habs : |y - x| ≤ shift := abs_le.mpr ⟨by linarith only [hy.1], by linarith only [hy.2]⟩
    exact hmvt.trans (by
      convert mul_le_mul_of_nonneg_left habs
        (show 0 ≤ 2 * Real.exp 2 * a * Shao.standardNormalTail x by positivity) using 1 <;> ring)
  have hBShift (y : ℝ) (hy : y ∈ Set.Icc (x - shift) (x + shift)) :
      NullMeasurableSet (DB y) PB ∧
      |d y - d x| ≤ CG * (R / epsilon ^ 2) * Shao.standardNormalTail x := by
    have hypos : 0 < y := by linarith only [(hYbounds y hy).1]
    have hxpos : 0 < x := by linarith only [hx]
    refine ⟨(hBData y hypos).1, ?_⟩
    have hdiff : |d y - d x| ≤ 4 * |Shao.standardNormalTail y - Shao.standardNormalTail x| := by
      rcases le_total y x with hyx | hxy
      · rw [abs_of_nonneg (sub_nonneg.mpr (hBAnti y x hyx)),
          abs_of_nonneg (sub_nonneg.mpr (Shao.standardNormalTail_basic.1 hyx))]
        exact hBDiff y x hypos hxpos hyx
      · rw [abs_of_nonpos (sub_nonpos.mpr (hBAnti x y hxy)),
          abs_of_nonpos (sub_nonpos.mpr (Shao.standardNormalTail_basic.1 hxy))]
        have hh := hBDiff x y hxpos hypos hxy
        linarith only [hh]
    calc
      _ ≤ 4 * (2 * Real.exp 2 * a * shift * Shao.standardNormalTail x) :=
        hdiff.trans (mul_le_mul_of_nonneg_left (hTailShift y hy) (by norm_num))
      _ = (8 * Real.exp 2 * Shao.standardNormalTail x) * (a * shift) := by ring
      _ ≤ (8 * Real.exp 2 * Shao.standardNormalTail x) * (6 * R / epsilon ^ 2) :=
        mul_le_mul_of_nonneg_left haShift (by positivity)
      _ = _ := by dsimp [CG]; ring
  have hZProb (y : ℝ) : PA.real (zpath ⁻¹' Shao.C2.doubleCrossing hn y) =
      PZ.real (Shao.C2.doubleCrossing hn y) := by
    rw [← hZmap]
    simp only [Measure.real_def]
    rw [Measure.map_apply hZm (Shao.C2.measurableSet_doubleCrossing hn y)]
  have hPASandHi : PZ.real (Shao.C2.doubleCrossing hn (x + shift)) - PA.real Eᶜ ≤ PA.real DA := by
    have hSub : zpath ⁻¹' Shao.C2.doubleCrossing hn (x + shift) ⊆ DA ∪ Eᶜ := by
      intro v hv
      by_cases hE : v ∈ E
      · exact Or.inl (hContainHi ⟨hv, hE⟩).1
      · exact Or.inr hE
    have hh := (measureReal_mono (μ := PA) hSub).trans (measureReal_union_le _ _)
    rw [hZProb] at hh
    linarith only [hh]
  have hPASandLo : PA.real DA ≤ PZ.real (Shao.C2.doubleCrossing hn (x - shift)) + PA.real Eᶜ := by
    have hSub : DA ⊆ (zpath ⁻¹' Shao.C2.doubleCrossing hn (x - shift)) ∪ Eᶜ := by
      intro v hv
      by_cases hE : v ∈ E
      · exact Or.inl (hContainLo ⟨hv, hE⟩).1
      · exact Or.inr hE
    exact (measureReal_mono (μ := PA) hSub).trans
      ((measureReal_union_le _ _).trans_eq (by rw [hZProb]))
  have hBadEq : mu.real (D ∩ rawNᶜ) = PN.real (DA ∩ Nᶜ) := by
    have hh := congrArg ENNReal.toReal
      (hNormalizedPair.measure_mem_eq (hDAm.inter hNm.compl))
    simpa only [Measure.real, Set.preimage_inter, Set.preimage_compl,
      hDpre, rawN, Set.preimage_id] using hh
  have hMarked := (hBad nu n hn hNu2 hNuMean hNorm x epsilon hx0 hepsilon
    (hepsilon4096.trans (by norm_num : (1 / 4096 : ℝ) ≤ 1 / 800)) hRcut
    x (by linarith only [hx]) (by simp; positivity)).1 1 (Or.inl rfl)
  have hBadD : mu.real (D ∩ rawNᶜ) ≤ Cb * (R / epsilon ^ 3) * Shao.standardNormalTail x := by
    rw [hBadEq]
    have hsub : DA ∩ Nᶜ ⊆ Shao.upperCrossing hn x ∩ Nᶜ := by
      intro v hv
      exact ⟨hv.1.1, hv.2⟩
    apply (measureReal_mono (μ := PN) hsub).trans
    convert hMarked using 1 <;>
      simp only [PN, R, N, cutoff, a, Shao.upperCrossing, one_smul] <;> ring
  have hMultiply : PA.real DA * PN.real N = PN.real (N ∩ DA) := by
    simpa only [hCond, Measure.real_def, ENNReal.toReal_mul] using
      congrArg ENNReal.toReal (cond_mul_eq_inter hNm DA PN)
  have hSplit := measureReal_inter_add_sdiff (μ := PN) (s := DA) hNm
  change PN.real (DA ∩ N) + PN.real (DA ∩ Nᶜ) = PN.real DA at hSplit
  rw [Set.inter_comm DA N, ← hMultiply, ← hpN, ← hBadEq, ← hDraw] at hSplit
  have hMix : mu.real D - d x =
      pN * (PA.real DA - d x) + mu.real (D ∩ rawNᶜ) - (1 - pN) * d x := by
    linarith only [hSplit]
  have hMinusMem : x - shift ∈ Set.Icc (x - shift) (x + shift) :=
    ⟨le_rfl, by linarith only [hShift0]⟩
  have hPlusMem : x + shift ∈ Set.Icc (x - shift) (x + shift) :=
    ⟨by linarith only [hShift0], le_rfl⟩
  have hMinus : |PZ.real (Shao.C2.doubleCrossing hn (x - shift)) - d (x - shift)| ≤ Delta :=
    le_max_left _ _
  have hPlus : |PZ.real (Shao.C2.doubleCrossing hn (x + shift)) - d (x + shift)| ≤ Delta :=
    le_max_right _ _
  have hMinusShift := (hBShift (x - shift) hMinusMem).2
  have hPlusShift := (hBShift (x + shift) hPlusMem).2
  have hConditional : |PA.real DA - d x| ≤
      Delta + (CG + CE) * ((R / epsilon ^ 2) * Shao.standardNormalTail x) := by
    obtain ⟨hmlo, hmhi⟩ := abs_le.mp hMinus
    obtain ⟨hplo, hphi⟩ := abs_le.mp hPlus
    obtain ⟨hmslo, hmshi⟩ := abs_le.mp hMinusShift
    obtain ⟨hpslo, hpshi⟩ := abs_le.mp hPlusShift
    apply abs_le.mpr
    constructor <;> nlinarith only [hPASandHi, hPASandLo, hEPaid2,
      hmlo, hmhi, hplo, hphi, hmslo, hmshi, hpslo, hpshi]
  have hConditionalC : |PA.real DA - d x| ≤
      Delta + C * (R / epsilon ^ 2) * Shao.standardNormalTail x := by
    apply hConditional.trans
    have hh := mul_le_mul_of_nonneg_right hCEC' hR2
    nlinarith only [hh]
  have hdx0 : 0 ≤ d x := (hBData x (by linarith only [hx])).2.2.1
  have hdxTail : d x ≤ 2 * Shao.standardNormalTail x :=
    (hBData x (by linarith only [hx])).2.2.2
  have hMassFee : (1 - pN) * d x ≤ 2 * ((R / epsilon ^ 3) * Shao.standardNormalTail x) := by
    calc
      _ ≤ (R / epsilon ^ 3) * (2 * Shao.standardNormalTail x) :=
        mul_le_mul hpNbad hdxTail hdx0 (by positivity)
      _ = _ := by ring
  have hFinal : |mu.real D - d x| ≤
      pN * Delta + C * (R / epsilon ^ 3) * Shao.standardNormalTail x := by
    rw [hMix]
    have hB0 : 0 ≤ mu.real (D ∩ rawNᶜ) := measureReal_nonneg
    have hM0 : 0 ≤ (1 - pN) * d x := mul_nonneg (sub_nonneg.mpr hpN1) hdx0
    have hTri : |pN * (PA.real DA - d x) + mu.real (D ∩ rawNᶜ) - (1 - pN) * d x| ≤
        pN * |PA.real DA - d x| + mu.real (D ∩ rawNᶜ) + (1 - pN) * d x := by
      calc
        _ ≤ |pN * (PA.real DA - d x) + mu.real (D ∩ rawNᶜ)| + |(1 - pN) * d x| := abs_sub _ _
        _ ≤ |pN * (PA.real DA - d x)| + |mu.real (D ∩ rawNᶜ)| + |(1 - pN) * d x| :=
          by
            have hh := abs_add_le (pN * (PA.real DA - d x)) (mu.real (D ∩ rawNᶜ))
            linarith only [hh]
        _ = _ := by rw [abs_mul, abs_of_nonneg hpN0, abs_of_nonneg hB0, abs_of_nonneg hM0]
    have hPay : pN * |PA.real DA - d x| ≤
        pN * Delta + (CG + CE) * ((R / epsilon ^ 3) * Shao.standardNormalTail x) := by
      calc
        _ ≤ pN * (Delta + (CG + CE) * ((R / epsilon ^ 2) * Shao.standardNormalTail x)) :=
          mul_le_mul_of_nonneg_left hConditional hpN0
        _ = pN * Delta + pN * ((CG + CE) * ((R / epsilon ^ 2) * Shao.standardNormalTail x)) := by ring
        _ ≤ pN * Delta + (CG + CE) * ((R / epsilon ^ 2) * Shao.standardNormalTail x) :=
          by
            have hh : pN * ((CG + CE) * ((R / epsilon ^ 2) * Shao.standardNormalTail x)) ≤
                (CG + CE) * ((R / epsilon ^ 2) * Shao.standardNormalTail x) :=
              mul_le_of_le_one_left (by positivity) hpN1
            linarith only [hh]
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_left hFee23 (add_nonneg hCG.le hCE.le)
          linarith only [hh]
    have hCoeff : CG + CE + Cb + 2 ≤ C := by dsimp [C]; linarith only [hCG, hCE]
    have hh := mul_le_mul_of_nonneg_right hCoeff hR3
    nlinarith only [hTri, hPay, hBadD, hMassFee, hh]
  refine ⟨hRraw, hScale, hAprob, inferInstance, hNormalizedMap, hCond, hZmap,
    hRawNn, hDn, hDI, hNm, hEm, hpN, hpNlo, hpN1, hpNbad, hDraw,
    hVlo, hVhi, hm, hg, hShift0, hShiftNear, haShift, hSampleRatio,
    hZ2, hZ3, hZMean, hZNorm, hDeltaPos, hDeltaBound', ?_, hZevent,
    hContainHi, hContainLo, hELow, ?_, hPASandHi, hPASandLo, ?_, hMix, hConditionalC, hFinal⟩
  · intro y hy
    obtain ⟨hyhalf, hya, hsupport, hbudget⟩ := hYdata y hy
    obtain ⟨hDBn, hDBshift⟩ := hBShift y hy
    refine ⟨hyhalf, hya, hsupport, hbudget, hDBn, ?_⟩
    apply hDBshift.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCGC (by positivity)) hTail.le
  · exact hEPaid.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCEC hR.le) hTail.le)
  · exact hBadD.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCbC (by positivity)) hTail.le)

end Shao.Probability.SourceActualOriginalLawBridge
