import Shao.OQ6.OriginalLiteralRemainderEnvelope
import Shao.OQ6.NormalizedRemainderEnvelope
import Shao.OQ6.NormalizedStrictMomentBudgets
import Shao.OQ6.IIDSourceStrictMomentBudgets
import Shao.OQ6.ActualQuadraticTiltMoments

set_option autoImplicit false
universe u
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology MeasureTheory
open Shao.OQ5.P51

namespace Shao.OQ6.OriginalCodedStrictMomentFrontier
noncomputable section

theorem actual_original_coded_source_z_strict_moment_frontier
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond : (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (hgp : Integrable (fun o : Ω => Real.rpow |∫ y, h o y ∂μ| p) μ)
    (cBudget : ℝ) (hcBudget : 0 < cBudget) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω mΩ mΩ μ μ)
    let rho : ℝ := Real.sqrt v
    let β : ℝ := ∫ o : Ω, Real.rpow |g o| p ∂μ
    let cWindow : ℝ := Real.rpow (min (1 / 2 : ℝ) cBudget / 2) (1 / p)
    -- P01
    Measurable[mΩ, borel ℝ] g ∧ MemLp g 2 μ ∧
    -- P02
    0 ≤ β ∧ 0 < cWindow ∧
      Real.rpow cWindow p = min (1 / 2 : ℝ) cBudget / 2 ∧
      Real.rpow cWindow p < min (1 / 2 : ℝ) cBudget ∧
    ∃ (m₀ : MeasurableSpace Ω) (hm₀ : m₀ ≤ mΩ)
        (hcg : @MeasurableSpace.CountablyGenerated Ω m₀),
      let μ₀ : @Measure Ω m₀ := μ.trim hm₀
      letI : MeasurableSpace Ω := m₀
      letI : MeasurableSpace.CountablyGenerated Ω := hcg
      -- P03
      IsProbabilityMeasure μ₀ ∧
      ∀ (n : ℕ) (hn : 4 ≤ n) (C0 : ℝ) (hC0 : 0 ≤ C0)
          (z : ℝ) (hz : 1 ≤ z),
        let mN : MeasurableSpace (Fin n → Ω) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ)
        let mN₀ : MeasurableSpace (Fin n → Ω) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => m₀)
        let P : @Measure (Fin n → Ω) mN :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mΩ) (fun _ : Fin n => μ)
        let P₀ : @Measure (Fin n → Ω) mN₀ :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => m₀) (fun _ : Fin n => μ₀)
        let N : ℝ := Real.sqrt (n : ℝ)
        let K : ℝ := 4 * Real.sqrt (n : ℝ)
        let ε : ℕ → ℝ := fun k => 1 / (8 * Real.sqrt (n : ℝ) * ((k : ℝ) + 1))
        let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
        let D1 : (Fin n → Ω) → ℝ := residualStatisticD n r
        let D2 : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r C0 rho 1
        let A0 : (Fin n → Ω) → ℝ := fun ζ => |D1 ζ|
        let B0 : (Fin n → Ω) → ℝ := studentizerClipBudget n r C0 rho 1
        let A0delete : Fin n → (Fin n → Ω) → ℝ :=
          fun i ζ => |residualStatisticDDeleted n r ζ i|
        let B0delete : Fin n → (Fin n → Ω) → ℝ :=
          fun i ζ => studentizerClipBudgetDeleted n r C0 rho 1 ζ i
        let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
        let mAugLocal : MeasurableSpace (Ω × ℝ) := m₀.prod (borel ℝ)
        let mAug : MeasurableSpace (Fin n → Ω × ℝ) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (fun _ : Fin n => mAugLocal)
        let νlocal : Fin n → @Measure (Ω × ℝ) mAugLocal :=
          fun _ => @Measure.prod Ω ℝ m₀ (borel ℝ) μ₀ lambda01
        let ν : @Measure (Fin n → Ω × ℝ) mAug :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (inferInstance : Fintype (Fin n)) (fun _ : Fin n => mAugLocal) νlocal
        let q : (Fin n → Ω × ℝ) → (Fin n → Ω) := fun x i => (x i).1
        let cCode : Fin n → (Ω × ℝ) → ℝ := fun _ =>
          Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode
            (MeasurableSpace.natGeneratingSequence (Ω × ℝ))
        let ξlocal : Fin n → (Ω × ℝ) → ℝ := fun i t => g t.1 / N
        let Ylocal : ℕ → Fin n → (Ω × ℝ) → ℝ := fun k i =>
          Shao.OQ6.QuantizedObservationCoding.quantizedObservation (ε k) (ξlocal i) (cCode i)
        let ξ : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => ξlocal i (x i)
        let Y : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x => Ylocal k i (x i)
        let a : ℕ → Fin n → ℝ := fun k =>
          Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν (Y k)
        let s : ℕ → ℝ := fun k =>
          Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν (Y k)
        let ηlocal : ℕ → Fin n → (Ω × ℝ) → ℝ := fun k i =>
          Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a k i) (s k) (Ylocal k i)
        let η : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k =>
          Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
        let C : ℕ → (Fin n → Ω × ℝ) → (Fin n → ℝ) := fun k x i => η k i x
        let W : (Fin n → Ω × ℝ) → ℝ := fun x => ∑ i : Fin n, ξ i x
        let V : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (ξ i x) ^ 2)
        let Wη : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => ∑ i : Fin n, η k i x
        let Vη : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => Real.sqrt (∑ i : Fin n, (η k i x) ^ 2)
        let b : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (1 + D2 (q x))
        let Qε : ℕ → (Fin n → Ω × ℝ) → ℝ :=
          fun k x => W x - Wη k x + z * b x * (Vη k x - V x)
        let Dη : ℕ → (Fin n → Ω × ℝ) → ℝ :=
          fun k x => D1 (q x) + W x - Wη k x + z * b x * (Vη k x - V x)
        let A : (Fin n → Ω × ℝ) → ℝ := fun x => A0 (q x)
        let B : (Fin n → Ω × ℝ) → ℝ := fun x => B0 (q x)
        let Adelete : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => A0delete i (q x)
        let Bdelete : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => B0delete i (q x)
        let Vdelete : Fin n → (Fin n → Ω × ℝ) → ℝ :=
          fun i x => Real.sqrt (∑ j ∈ Finset.univ.erase i, (ξ j x) ^ 2)
        let H : (Fin n → Ω × ℝ) → ℝ :=
          fun x => (1 + V x) * (N + z * Real.sqrt (1 + B x))
        let Hdelete : Fin n → (Fin n → Ω × ℝ) → ℝ :=
          fun i x => (1 + Vdelete i x) * (N + z * Real.sqrt (1 + Bdelete i x))
        let M : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => K * ε k * H x
        let Mdelete : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x => K * ε k * Hdelete i x
        let Anew : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => A x + M k x
        let AdeleteNew : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x => Adelete i x + Mdelete k i x
        let Fz : ℝ → ℝ := fun t => (z * t) ^ 2 * min |z * t| 1
        let δ0 : Fin n → ℝ := fun i => ∫ ζ, Fz (ξ0 i ζ) ∂P
        let δν : Fin n → ℝ := fun i => ∫ x, Fz (ξ i x) ∂ν
        let δη : ℕ → Fin n → ℝ := fun k i => ∫ x, Fz (η k i x) ∂ν
        let L0 : ℝ := ∑ i : Fin n, δ0 i
        let Lν : ℝ := ∑ i : Fin n, δν i
        let Lη : ℕ → ℝ := fun k => ∑ i : Fin n, δη k i
        let scalarBudget : ℝ := ∫ o : Ω, Fz (g o / N) ∂μ
        -- P04
        @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ ∧
          P₀ = @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P ∧
          IsProbabilityMeasure ν ∧ MeasurePreserving q ν P₀ ∧
        -- P05
        (∀ i : Fin n, Measurable[mN₀, borel ℝ] (ξ0 i)) ∧
        -- P06
        (∀ k : ℕ, 0 < ε k ∧ ε k < 1 / (4 * Real.sqrt (n : ℝ))) ∧
          Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ)) ∧
        -- P07
        (∀ i : Fin n, Measurable[mAug, borel ℝ] (ξ i) ∧ MemLp (ξ i) 2 ν ∧
          (∫ x, ξ i x ∂ν) = 0) ∧
          (∑ i : Fin n, ∫ x, (ξ i x) ^ 2 ∂ν) = 1 ∧
        -- P08
        (∀ (k : ℕ) (i : Fin n), Measurable[mAugLocal, borel ℝ] (Ylocal k i) ∧
          Measurable[mAug, borel ℝ] (Y k i) ∧
          ∀ x : Fin n → Ω × ℝ, |Y k i x - ξ i x| ≤ ε k) ∧
        -- P09
        (∀ k : ℕ, (1 / 2 : ℝ) < s k ∧
          (∀ (i : Fin n) (x : Fin n → Ω × ℝ), η k i x = ηlocal k i (x i)) ∧
          iIndepFun (η k) ν ∧
          (∀ i : Fin n, Measurable[mAug, borel ℝ] (η k i) ∧ MemLp (η k i) 2 ν ∧
            (∫ x, η k i x ∂ν) = 0) ∧
          (∑ i : Fin n, ∫ x, (η k i x) ^ 2 ∂ν) = 1 ∧
          ν {x : Fin n → Ω × ℝ | Vη k x = 0} = 0 ∧
          (∀ᵐ x ∂ν, 0 < Vη k x ∧ 0 < b x ∧ 0 < Vη k x * b x)) ∧
        -- P10
        (∀ (k : ℕ) (x : Fin n → Ω × ℝ),
          Dη k x = D1 (q x) + Qε k x ∧
          Wη k x + Dη k x - z * Vη k x * b x = W x + D1 (q x) - z * V x * b x ∧
          |Qε k x| ≤ M k x ∧ |Dη k x| ≤ Anew k x) ∧
        -- P11
        (∀ k : ℕ, Measurable[mAug, borel ℝ] (Qε k) ∧ Integrable[mAug] (Qε k) ν ∧
          Integrable[mAug] (fun x => |Qε k x|) ν) ∧
          Filter.Tendsto (fun k => ∫ x, |Qε k x| ∂ν) Filter.atTop (nhds (0 : ℝ)) ∧
        -- P12
        (∀ k : ℕ, ∃ Ffull : (Fin n → ℝ) → ℝ × ℝ × ℝ,
          Measurable[borel (Fin n → ℝ), borel (ℝ × ℝ × ℝ)] Ffull ∧
          ∀ x : Fin n → Ω × ℝ, (M k x, Anew k x, B x) = Ffull (C k x)) ∧
        -- P13
        (∀ (k : ℕ) (i : Fin n), ∃ Fdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
          Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdelete ∧
          ∀ x : Fin n → Ω × ℝ,
            (Mdelete k i x, AdeleteNew k i x, Bdelete i x) =
              Fdelete (fun j : {j : Fin n // j ≠ i} => η k j.val x)) ∧
        -- P14
        (∀ k : ℕ, ∃ G1 G2 : (Fin n → ℝ) → ℝ,
          Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
          Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
          ∀ x : Fin n → Ω × ℝ, Dη k x = G1 (C k x) ∧ D2 (q x) = G2 (C k x)) ∧
        -- P16
        (∀ i : Fin n, Integrable[mN] (fun ζ => Fz (ξ0 i ζ)) P) ∧
          (∀ i : Fin n, Integrable[mN₀] (fun ζ => Fz (ξ0 i ζ)) P₀) ∧
          (∀ i : Fin n, Integrable[mAug] (fun x => Fz (ξ i x)) ν) ∧
          (∀ (k : ℕ) (i : Fin n), Integrable[mAug] (fun x => Fz (η k i x)) ν) ∧
        -- P17
        (∀ i : Fin n, δν i = δ0 i) ∧ Lν = L0 ∧
        -- P18
        Integrable[mΩ] (fun o : Ω => Fz (g o / N)) μ ∧
          (∀ i : Fin n, δ0 i = scalarBudget) ∧
          L0 = (n : ℝ) * scalarBudget ∧
          (∀ i : Fin n, L0 = (n : ℝ) * δ0 i) ∧
          (∀ i : Fin n, 0 ≤ δ0 i) ∧ 0 ≤ L0 ∧
          L0 ≤ β * Real.rpow z p / Real.rpow (n : ℝ) ((p - 2) / 2) ∧
          (β = 0 → L0 = 0 ∧ (∀ i : Fin n, δ0 i = 0)) ∧
        -- P19
        (∀ i : Fin n, Filter.Tendsto (fun k => δη k i) Filter.atTop (nhds (δ0 i))) ∧
          Filter.Tendsto Lη Filter.atTop (nhds L0) ∧
        -- P20
        ((β = 0 ∨ (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
            Real.rpow (n : ℝ) ((p - 2) / (2 * p)))) →
          L0 ≤ Real.rpow cWindow p ∧
          (∀ i : Fin n, δ0 i < (1 / 2 : ℝ)) ∧
          L0 < cBudget * z ^ 2 ∧
          ∀ (τ : ℝ), 0 < τ →
            ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
              (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧
              Lη k < cBudget * z ^ 2 ∧
              (∫ x, |Qε k x| ∂ν) < τ)
 := by
  classical
  intro g r v rho β cWindow
  have hProjection :=
    Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
      μ h hh hh2 hhsymm hcenter hprojectionsecond 3 (by norm_num) 0
        (by norm_num) (by positivity)
  dsimp only at hProjection
  have hg : Measurable[mΩ, borel ℝ] g := hProjection.1
  have hg2 : MemLp g 2 μ := hProjection.2.1
  change Integrable (fun o : Ω => Real.rpow |g o| p) μ at hgp
  have hIID :=
    @Shao.OQ6.IIDSourceStrictMomentBudgets.actual_iid_source_z_strict_moment_budgets
      Ω mΩ μ inferInstance g hg hg2 p hp2 hp3 hgp cBudget hcBudget
  dsimp only at hIID
  change 0 ≤ β ∧ 0 < cWindow ∧
      Real.rpow cWindow p = min (1 / 2 : ℝ) cBudget / 2 ∧
      Real.rpow cWindow p < min (1 / 2 : ℝ) cBudget ∧ _ at hIID
  rcases hIID with ⟨hβ, hcWindow, hcPower, hcStrict, hIIDAll⟩
  have hModel :=
    Shao.OQ6.OriginalLiteralRemainderEnvelope.actual_original_literal_remainder_envelope
      μ h hh hh2 hhsymm hcenter hprojectionsecond
  dsimp only at hModel
  rcases hModel with ⟨m₀, hm₀, hcg, hModelBody⟩
  refine ⟨hg, hg2, hβ, hcWindow, hcPower, hcStrict, m₀, hm₀, hcg, ?_⟩
  intro μ₀
  letI : MeasurableSpace Ω := m₀
  letI : MeasurableSpace.CountablyGenerated Ω := hcg
  rcases hModelBody with ⟨hμ₀prob, hModelAll⟩
  letI : IsProbabilityMeasure μ₀ := hμ₀prob
  refine ⟨hμ₀prob, ?_⟩
  intro n hn C0 hC0 z hz
  intro mN mN₀ P P₀ N K ε ξ0 D1 D2 A0 B0 A0delete B0delete
    lambda01 mAugLocal mAug νlocal ν q cCode ξlocal Ylocal ξ Y a s ηlocal η C
    W V Wη Vη b Qε Dη A B Adelete Bdelete Vdelete H Hdelete
    M Mdelete Anew AdeleteNew Fz δ0 δν δη L0 Lν Lη scalarBudget
  have hn1 : 1 ≤ n := by omega
  have hz0 : 0 ≤ z := le_trans (by norm_num) hz
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by linarith only [hnR])
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hεpos (k : ℕ) : 0 < ε k := by dsimp only [ε]; positivity
  have hεsmall (k : ℕ) : ε k < 1 / (4 * Real.sqrt (n : ℝ)) := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    dsimp only [ε]
    apply (div_lt_div_iff₀
      (by positivity : 0 < 8 * Real.sqrt (n : ℝ) * ((k : ℝ) + 1))
      (by positivity : 0 < 4 * Real.sqrt (n : ℝ))).2
    nlinarith [mul_nonneg hN.le hk]
  have hεfactor : ε = fun k : ℕ =>
      (1 / (8 * Real.sqrt (n : ℝ))) * (1 / ((k : ℝ) + 1)) := by
    funext k
    simp only [ε, div_eq_mul_inv, one_mul, mul_inv_rev]
    ring
  have hεlim : Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ)) := by
    rw [hεfactor]
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto
        (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds (0 : ℝ))).const_mul
          (1 / (8 * Real.sqrt (n : ℝ)))
  have hScale (k : ℕ) : 4 * ε k * Real.sqrt (n : ℝ) = K * ε k := by
    dsimp only [K]
    ring
  -- A single model supplies the fixed-law packet and all current-epsilon packets.
  have hFixed := hModelAll n hn C0 hC0 z hz0 K hK
    (ε 0) (hεpos 0) (hεsmall 0)
  rcases hFixed with
    ⟨hP₀prob, hP₀map, hObs, hObsIndep, hGcoord, hGenergy,
      hQid, hWorig, hVorig, hTorig, hD1red, hD2red, hHalf,
      hTred, hTambient, hTLaw, hνprob, hq,
      hScale0, hLocal0, hIndep0, hEtaL20, hEtaInt0, hEtaMean0, hEtaEnergy0,
      hEtaAtoms0, hEtaZero0, hEtaPositive0, hCmeas0, hCcomap0,
      hAnyFull0, hAnyDelete0, hScalar0, hResidualDelete0, hTetaMeas0,
      hZeroRed, hZeroAmbient, hZeroAug, hZeroLawAug, hZeroLawAmbient,
      hZeroReal, hSigned0, hComparisons0, hBounds, hDeleteBounds,
      hJred, hAred, hBred, hDeletedMeas, hAredInt, hBredInt, hD2redInt,
      hDeletedInts, hTotalRed, hTotalRedInt, hApull, hBpull, hD2pull,
      hApullInt, hBpullInt, hD2pullInt, hDeletedPull, hTotalPull,
      hTotalPullInt, hLiteral⟩
  rcases hLiteral with
    ⟨hXiL2, hXiSecond, hXiEnergy, hVmeas, hVdeleteMeas, hVdeleteBounds,
      hBudgetMeas, hBudgetDeleteMeas, hBudgetLower, hBudgetDeleteLower,
      hHmeas, hHint, hHdelete, hHpositive, hHdeletePositive,
      hMMeas, hMInt, hMAbsInt, hMNonneg, hMIntegral, hMdIntegral,
      hMAbsIntegral, hMdAbsIntegral, hPayment, hPaymentNonneg, hTotalPaymentNonneg,
      hMPayment, hMAbsPayment, hMTotalPayment, hMAbsTotalPayment,
      hMLimit, hMAbsLimit, hMdLimit, hMdAbsLimit, hEnvelopeMeasInt,
      hDeletedEnvelopeMeasInt, hEnvelopeNonneg, hFullFactor0, hDeleteFactor0,
      hDeltaFormula, hDeltaAbs, hDeltaNonnegBound, hDeltaInts,
      hDeltaPayment, hDeltaLimit, hFeeInts, hFeeTotalInts,
      hFeePoint, hFeeIntegral, hFeeTotalIntegral, hFeeLimit, hFeeTotalLimit⟩
  letI : @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ := hP₀prob
  letI : @IsProbabilityMeasure (Fin n → Ω × ℝ) mAug ν := hνprob
  change @MeasurePreserving (Fin n → Ω × ℝ) (Fin n → Ω) mAug mN₀ q ν P₀ at hq
  have hXiMeas (i : Fin n) : Measurable[mAug, borel ℝ] (ξ i) := (hXiL2 i).1
  have hXi2 (i : Fin n) : MemLp (ξ i) 2 ν := (hXiL2 i).2
  let zeroSection : (Fin n → Ω) → (Fin n → Ω × ℝ) :=
    fun ζ i => (ζ i, (0 : ℝ))
  have hSection : Measurable[mN₀, mAug] zeroSection := by
    apply (@measurable_pi_iff (Fin n → Ω) (Fin n) (fun _ : Fin n => Ω × ℝ)
      mN₀ (fun _ : Fin n => mAugLocal) zeroSection).2
    intro i
    exact (@measurable_pi_apply (Fin n) (fun _ : Fin n => Ω)
      (fun _ : Fin n => m₀) i).prodMk measurable_const
  have hXi0Meas (i : Fin n) : Measurable[mN₀, borel ℝ] (ξ0 i) := by
    simpa only [zeroSection, ξ, ξlocal, ξ0] using (hXiMeas i).comp hSection
  have hXi0Mean (i : Fin n) : (∫ ζ, ξ0 i ζ ∂P₀) = 0 :=
    (hGcoord i).2.2.1
  have hXiMean (i : Fin n) : (∫ x, ξ i x ∂ν) = 0 := by
    have heq := integral_map_of_stronglyMeasurable (μ := ν)
      hq.measurable (hXi0Meas i).stronglyMeasurable
    rw [hq.map_eq] at heq
    have htransport : (∫ x, ξ i x ∂ν) = (∫ ζ, ξ0 i ζ ∂P₀) := by
      simpa only [ξ, ξlocal, ξ0, q] using heq.symm
    exact htransport.trans (hXi0Mean i)
  have hLocalXiMeas (i : Fin n) : Measurable[mAugLocal, borel ℝ] (ξlocal i) :=
    ((hGcoord i).1).comp measurable_fst
  have hCoding := Shao.OQ6.ScalarObservationCoding.countable_uniform_augmented_base_four_code μ₀
  rcases hCoding with ⟨hUniformProb, hProductProb, hCodeSum, hCodeRange,
    hCodeMeas, hCodeSets, hCodeRecover, hCodeComap, hCodeFibers, hCodeAtoms⟩
  have hLocalY (k : ℕ) (i : Fin n) :
      Measurable[mAugLocal, borel ℝ] (Ylocal k i) ∧
      ∀ t : Ω × ℝ, |Ylocal k i t - ξlocal i t| ≤ ε k := by
    have hQuant := Shao.OQ6.QuantizedObservationCoding.quantized_observation_spec
      (ξlocal i) (cCode i) (hLocalXiMeas i) hCodeMeas hCodeRange hCodeComap
      (ε k) (hεpos k)
    exact ⟨hQuant.1, hQuant.2.2.1⟩
  have hYMeas (k : ℕ) (i : Fin n) : Measurable[mAug, borel ℝ] (Y k i) :=
    (hLocalY k i).1.comp (measurable_pi_apply i)
  have hError (k : ℕ) (i : Fin n) (x : Fin n → Ω × ℝ) :
      |Y k i x - ξ i x| ≤ ε k := (hLocalY k i).2 (x i)
  have hCurrent (k : ℕ) :
      ((1 / 2 : ℝ) < s k ∧
        (∀ (i : Fin n) (x : Fin n → Ω × ℝ), η k i x = ηlocal k i (x i)) ∧
        iIndepFun (η k) ν ∧
        (∀ i : Fin n, Measurable[mAug, borel ℝ] (η k i) ∧ MemLp (η k i) 2 ν ∧
          (∫ x, η k i x ∂ν) = 0) ∧
        (∑ i : Fin n, ∫ x, (η k i x) ^ 2 ∂ν) = 1 ∧
        ν {x : Fin n → Ω × ℝ | Vη k x = 0} = 0 ∧
        (∀ᵐ x ∂ν, 0 < Vη k x ∧ 0 < b x ∧ 0 < Vη k x * b x)) ∧
      (∀ x : Fin n → Ω × ℝ,
        Wη k x + Dη k x - z * Vη k x * b x = W x + D1 (q x) - z * V x * b x) ∧
      (∃ Ffull : (Fin n → ℝ) → ℝ × ℝ × ℝ,
        Measurable[borel (Fin n → ℝ), borel (ℝ × ℝ × ℝ)] Ffull ∧
        ∀ x : Fin n → Ω × ℝ, (M k x, Anew k x, B x) = Ffull (C k x)) ∧
      (∀ i : Fin n, ∃ Fdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdelete ∧
        ∀ x : Fin n → Ω × ℝ,
          (Mdelete k i x, AdeleteNew k i x, Bdelete i x) =
            Fdelete (fun j : {j : Fin n // j ≠ i} => η k j.val x)) ∧
      (∃ G1 G2 : (Fin n → ℝ) → ℝ,
        Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
        Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
        ∀ x : Fin n → Ω × ℝ, Dη k x = G1 (C k x) ∧ D2 (q x) = G2 (C k x)) := by
    have hNow := hModelAll n hn C0 hC0 z hz0 K hK
      (ε k) (hεpos k) (hεsmall k)
    rcases hNow with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hNowScale, hNowLocal, hNowIndep, hNowL2, hNowInt, hNowMean, hNowEnergy,
        hNowAtoms, hNowZero, hNowPositive, hNowCMeas, hNowCComap,
        hNowAnyFull, hNowAnyDelete, hNowScalar, hNowResidualDelete, hNowTMeas,
        hNowZeroRed, hNowZeroAmbient, hNowZeroAug, hNowZeroLawAug,
        hNowZeroLawAmbient, hNowZeroReal, hNowSigned, hNowComparison,
        hNowBounds, hNowDeleteBounds, hNowJRed, hNowARed, hNowBRed,
        hNowDeletedMeas, hNowARedInt, hNowBRedInt, hNowD2RedInt,
        hNowDeletedInts, hNowTotalRed, hNowTotalRedInt, hNowAPull,
        hNowBPull, hNowD2Pull, hNowAPullInt, hNowBPullInt, hNowD2PullInt,
        hNowDeletedPull, hNowTotalPull, hNowTotalPullInt, hNowLiteral⟩
    rcases hNowLiteral with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hNowFullFactor,
        hNowDeleteFactor, hNowRest⟩
    refine ⟨⟨hNowScale, hNowLocal, hNowIndep,
      (fun i => ⟨(hNowL2 i).1, (hNowL2 i).2, hNowMean i⟩),
      hNowEnergy, hNowZero, hNowPositive⟩, hNowSigned z,
      hNowFullFactor (ε k), hNowDeleteFactor (ε k), ?_⟩
    rcases hNowScalar with ⟨G2, hG2, hG2eq, hSignedFactor⟩
    rcases hSignedFactor z with ⟨G1, hG1, hG1eq⟩
    exact ⟨G1, G2, hG1, hG2, fun x => ⟨hG1eq x, hG2eq x⟩⟩
  have hD1Meas : Measurable[mAug, borel ℝ] (fun x => D1 (q x)) :=
    hD1red.comp hq.measurable
  have hD2Meas : Measurable[mAug, borel ℝ] (fun x => D2 (q x)) :=
    hD2red.comp hq.measurable
  have hANonneg (x : Fin n → Ω × ℝ) : 0 ≤ A x := (hBounds (q x)).1
  have hBNonneg (x : Fin n → Ω × ℝ) : 0 ≤ B x := (hBounds (q x)).2.1
  have hD1Bound (x : Fin n → Ω × ℝ) : |D1 (q x)| ≤ A x := le_rfl
  have hD2Bound (x : Fin n → Ω × ℝ) : |D2 (q x)| ≤ B x := (hBounds (q x)).2.2
  have hQDifference (k : ℕ) (x : Fin n → Ω × ℝ) :
      Dη k x - D1 (q x) = Qε k x := by
    dsimp only [Dη, Qε]
    ring
  have hQEnvelope (k : ℕ) :
      Measurable[mAug, borel ℝ] (Qε k) ∧ Integrable[mAug] (Qε k) ν ∧
      Integrable[mAug] (fun x => |Qε k x|) ν ∧
      (∫ x, |Qε k x| ∂ν) ≤ K * ε k * (∫ x, H x ∂ν) ∧
      (∀ x : Fin n → Ω × ℝ, |Qε k x| ≤ M k x ∧ |Dη k x| ≤ Anew k x) := by
    have hEnv :=
      @Shao.OQ6.NormalizedRemainderEnvelope.actual_normalized_remainder_envelope_spec
        (Fin n → Ω × ℝ) mAug ν hνprob n hn1 ξ (Y k)
        hXiMeas hXi2 hXiMean hXiEnergy (hYMeas k)
        (fun x => D1 (q x)) (fun x => D2 (q x)) A B Adelete Bdelete
        hD1Meas hD2Meas hApull hBpull hANonneg hBNonneg hD1Bound hD2Bound
        hApullInt hBpullInt (ε k) (hεpos k) (hεsmall k) (hError k) z hz0
    rcases hEnv with
      ⟨hEnvEtaMeas, hEnvW, hEnvWEta, hEnvV, hEnvVEta, hEnvb, hEnvC,
        hEnvH, hEnvDEta, hEnvA, hEnvB, hEnvbBounds, hEnvHPos,
        hEnvRhoPos, hEnvRhoSmall, hEnvHInt, hEnvDInt, hEnvDEtaInt,
        hEnvAInt, hEnvDiffInt, hEnvAbsDiffInt, hEnvRhoHInt, hEnvAHInt,
        hEnvDiffBound, hEnvDEtaBound, hEnvANonneg, hEnvADom,
        hEnvBBounds, hEnvBEq, hEnvADelEq, hEnvBDelEq, hEnvADelBound,
        hEnvBDelBound, hEnvIntegralBound, hEnvAIntegralError, hEnvAIntegral⟩
    change Measurable[mAug, borel ℝ] (Dη k) at hEnvDEta
    change Integrable[mAug] (fun x => Dη k x - D1 (q x)) ν at hEnvDiffInt
    change Integrable[mAug] (fun x => |Dη k x - D1 (q x)|) ν at hEnvAbsDiffInt
    change (∀ x : Fin n → Ω × ℝ,
      |Dη k x - D1 (q x)| ≤ (4 * ε k * Real.sqrt (n : ℝ)) * H x) at hEnvDiffBound
    change (∀ x : Fin n → Ω × ℝ,
      |Dη k x| ≤ A x + (4 * ε k * Real.sqrt (n : ℝ)) * H x) at hEnvDEtaBound
    change (∫ x, |Dη k x - D1 (q x)| ∂ν) ≤
      (4 * ε k * Real.sqrt (n : ℝ)) * (∫ x, H x ∂ν) at hEnvIntegralBound
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hQDifference k] using hEnvDEta.sub hD1Meas
    · simpa only [hQDifference k] using hEnvDiffInt
    · simpa only [hQDifference k] using hEnvAbsDiffInt
    · simpa only [hQDifference k, hScale k] using hEnvIntegralBound
    · intro x
      constructor
      · simpa only [hQDifference k, hScale k, M] using hEnvDiffBound x
      · simpa only [hScale k, Anew, M] using hEnvDEtaBound x
  have hQLimit : Filter.Tendsto (fun k : ℕ => ∫ x, |Qε k x| ∂ν)
      Filter.atTop (nhds (0 : ℝ)) := by
    have hUpperLimit : Filter.Tendsto (fun k : ℕ => K * ε k * (∫ x, H x ∂ν))
        Filter.atTop (nhds (0 : ℝ)) := by
      simpa only [mul_zero, zero_mul] using
        (hεlim.const_mul K).mul_const (∫ x, H x ∂ν)
    exact squeeze_zero'
      (Filter.Eventually.of_forall (fun k : ℕ => integral_nonneg (fun x => abs_nonneg (Qε k x))))
      (Filter.Eventually.of_forall (fun k : ℕ => (hQEnvelope k).2.2.2.1)) hUpperLimit
  have hAnalytic :=
    @Shao.OQ6.NormalizedAnalyticCostLimits.actual_projection_tilt_and_truncated_cost_limits
      (Fin n → Ω × ℝ) mAug ν hνprob n hn1 ξ hXiMeas hXi2 hXiMean hXiEnergy
      Y hYMeas ε hεpos hεsmall hεlim hError z
  rcases hAnalytic with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hFzXiInt, hFzEtaInt,
      _, _, _, _, hDeltaLimitNu, hLLimitNu, hAnalyticRest⟩
  change (∀ i : Fin n, Integrable[mAug] (fun x => Fz (ξ i x)) ν) at hFzXiInt
  change (∀ (k : ℕ) (i : Fin n), Integrable[mAug] (fun x => Fz (η k i x)) ν) at hFzEtaInt
  change (∀ i : Fin n, Filter.Tendsto (fun k => δη k i) Filter.atTop (nhds (δν i)))
    at hDeltaLimitNu
  change Filter.Tendsto Lη Filter.atTop (nhds Lν) at hLLimitNu
  have hIdOmega : Measurable[mΩ, m₀] (id : Ω → Ω) := measurable_id'' hm₀
  have hIdMeas : Measurable[mN, mN₀] (id : (Fin n → Ω) → (Fin n → Ω)) := by
    apply (@measurable_pi_iff (Fin n → Ω) (Fin n) (fun _ : Fin n => Ω)
      mN (fun _ : Fin n => m₀) (id : (Fin n → Ω) → (Fin n → Ω))).2
    intro i
    exact hIdOmega.comp
      (@measurable_pi_apply (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ) i)
  have hId : @MeasurePreserving (Fin n → Ω) (Fin n → Ω) mN mN₀ id P P₀ :=
    @MeasurePreserving.mk (Fin n → Ω) (Fin n → Ω) mN mN₀ id P P₀ hIdMeas hP₀map.symm
  have hFz0Meas (i : Fin n) : Measurable[mN₀, borel ℝ] (fun ζ => Fz (ξ0 i ζ)) := by
    dsimp only [Fz]
    exact ((measurable_const.mul (hXi0Meas i)).pow_const 2).mul
      ((continuous_abs.measurable.comp (measurable_const.mul (hXi0Meas i))).min measurable_const)
  have hFz0Int (i : Fin n) : Integrable[mN₀] (fun ζ => Fz (ξ0 i ζ)) P₀ := by
    apply (hq.integrable_comp (hFz0Meas i).aestronglyMeasurable).1
    change Integrable[mAug] (fun x => Fz (ξ i x)) ν
    exact hFzXiInt i
  have hFzOriginalInt (i : Fin n) : Integrable[mN] (fun ζ => Fz (ξ0 i ζ)) P := by
    simpa only [Function.comp_def, id_eq] using hId.integrable_comp_of_integrable (hFz0Int i)
  have hDeltaTransport (i : Fin n) : δν i = δ0 i := by
    have hFromAug := integral_map_of_stronglyMeasurable (μ := ν)
      hq.measurable (hFz0Meas i).stronglyMeasurable
    have hFromOriginal := integral_map_of_stronglyMeasurable (μ := P)
      hId.measurable (hFz0Meas i).stronglyMeasurable
    rw [hq.map_eq] at hFromAug
    rw [hId.map_eq] at hFromOriginal
    change (∫ ζ, Fz (ξ0 i ζ) ∂P₀) = (∫ x, Fz (ξ i x) ∂ν) at hFromAug
    change (∫ ζ, Fz (ξ0 i ζ) ∂P₀) = (∫ ζ, Fz (ξ0 i ζ) ∂P) at hFromOriginal
    exact hFromAug.symm.trans hFromOriginal
  have hLTransport : Lν = L0 := Finset.sum_congr rfl (fun i _ => hDeltaTransport i)
  have hDeltaLimit (i : Fin n) :
      Filter.Tendsto (fun k => δη k i) Filter.atTop (nhds (δ0 i)) := by
    simpa only [hDeltaTransport i] using hDeltaLimitNu i
  have hLLimit : Filter.Tendsto Lη Filter.atTop (nhds L0) := by
    simpa only [hLTransport] using hLLimitNu
  -- The quantitative law is the original-mu product law, not a surrogate law.
  have hOriginalIID := hIIDAll n hn1 z hz
  change IsProbabilityMeasure P ∧
      Integrable[mΩ] (fun o : Ω => Fz (g o / N)) μ ∧
      (∀ i : Fin n, Integrable[mN] (fun ζ => Fz (ξ0 i ζ)) P) ∧
      (∀ i : Fin n, δ0 i = scalarBudget) ∧ L0 = (n : ℝ) * scalarBudget ∧
      (∀ i : Fin n, L0 = (n : ℝ) * δ0 i) ∧
      (∀ i : Fin n, 0 ≤ δ0 i) ∧ 0 ≤ L0 ∧
      L0 ≤ β * Real.rpow z p / Real.rpow (n : ℝ) ((p - 2) / 2) ∧
      (β = 0 → L0 = 0 ∧ (∀ i : Fin n, δ0 i = 0)) ∧
      ((β = 0 ∨ (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
        Real.rpow (n : ℝ) ((p - 2) / (2 * p)))) →
        L0 ≤ Real.rpow cWindow p ∧
        (∀ i : Fin n, δ0 i < (1 / 2 : ℝ)) ∧ L0 < cBudget * z ^ 2) at hOriginalIID
  rcases hOriginalIID with
    ⟨hOriginalProb, hScalarInt, hOriginalCoordinateInts, hDeltaScalar,
      hLScalar, hLCoordinate, hDeltaNonneg, hLNonneg, hOriginalRate,
      hZeroBeta, hOriginalWindow⟩
  have hWindow :
      (β = 0 ∨ (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
        Real.rpow (n : ℝ) ((p - 2) / (2 * p)))) →
      L0 ≤ Real.rpow cWindow p ∧
      (∀ i : Fin n, δ0 i < (1 / 2 : ℝ)) ∧ L0 < cBudget * z ^ 2 ∧
      ∀ τ : ℝ, 0 < τ → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧
        Lη k < cBudget * z ^ 2 ∧ (∫ x, |Qε k x| ∂ν) < τ := by
    intro hInWindow
    rcases hOriginalWindow hInWindow with ⟨hLc, hDeltaStrict, hLStrict⟩
    refine ⟨hLc, hDeltaStrict, hLStrict, ?_⟩
    intro τ hτ
    have hDeltaNuStrict (i : Fin n) : δν i < (1 / 2 : ℝ) := by
      rw [hDeltaTransport i]
      exact hDeltaStrict i
    have hLNuStrict : Lν < cBudget * z ^ 2 := by
      rw [hLTransport]
      exact hLStrict
    have hStrictSequence :=
      @Shao.OQ6.NormalizedStrictMomentBudgets.actual_source_z_strict_truncated_moment_budgets
        (Fin n → Ω × ℝ) mAug ν hνprob n hn1 ξ hXiMeas hXi2 hXiMean hXiEnergy
        Y hYMeas ε hεpos hεsmall hεlim hError z hz cBudget hcBudget
    dsimp only at hStrictSequence
    have hBudgetTail : ∃ kb : ℕ, ∀ k : ℕ, kb ≤ k →
        (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧ Lη k < cBudget * z ^ 2 := by
      exact (hStrictSequence hDeltaNuStrict hLNuStrict).2.2.2.2
    obtain ⟨kb, hkb⟩ := hBudgetTail
    have hQTolerance : ∀ᶠ k : ℕ in Filter.atTop, (∫ x, |Qε k x| ∂ν) < τ :=
      hQLimit.eventually (eventually_lt_nhds hτ)
    obtain ⟨kq, hkq⟩ := Filter.eventually_atTop.1 hQTolerance
    let tailIndex : ℕ := max kb kq
    refine ⟨tailIndex, ?_⟩
    intro k hk
    have hbk : kb ≤ k := (le_max_left kb kq).trans hk
    have hqk : kq ≤ k := (le_max_right kb kq).trans hk
    exact ⟨(hkb k hbk).1, (hkb k hbk).2, hkq k hqk⟩
  refine ⟨hP₀prob, hP₀map, hνprob, hq, hXi0Meas,
    (fun k => ⟨hεpos k, hεsmall k⟩), hεlim,
    (fun i => ⟨hXiMeas i, hXi2 i, hXiMean i⟩), hXiEnergy,
    (fun k i => ⟨(hLocalY k i).1, hYMeas k i, hError k i⟩),
    (fun k => (hCurrent k).1), ?_,
    (fun k => ⟨(hQEnvelope k).1, (hQEnvelope k).2.1, (hQEnvelope k).2.2.1⟩), hQLimit,
    (fun k => (hCurrent k).2.2.1), (fun k => (hCurrent k).2.2.2.1),
    (fun k => (hCurrent k).2.2.2.2),
    hFzOriginalInt, hFz0Int, hFzXiInt, hFzEtaInt,
    hDeltaTransport, hLTransport, hScalarInt, hDeltaScalar, hLScalar,
    hLCoordinate, hDeltaNonneg, hLNonneg, hOriginalRate, hZeroBeta,
    hDeltaLimit, hLLimit, hWindow⟩
  intro k x
  refine ⟨?_, (hCurrent k).2.1 x, (hQEnvelope k).2.2.2.2 x⟩
  dsimp only [Dη, Qε]
  ring
end

end Shao.OQ6.OriginalCodedStrictMomentFrontier
