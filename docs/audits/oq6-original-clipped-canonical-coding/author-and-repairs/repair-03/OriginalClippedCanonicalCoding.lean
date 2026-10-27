import Shao.OQ6.OriginalCountablyGeneratedModel
import Shao.OQ6.AmbientCanonicalCodingTransport

set_option autoImplicit false

universe u

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical symmDiff
open Shao.OQ5.P51

namespace Shao.OQ6.OriginalClippedCanonicalCoding

noncomputable section

theorem actual_original_clipped_canonical_normalized_coding
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
    ∃ (m₀ : MeasurableSpace Ω) (hm₀ : m₀ ≤ mΩ)
        (hcg : @MeasurableSpace.CountablyGenerated Ω m₀),
      let μ₀ : @Measure Ω m₀ := μ.trim hm₀
      letI : MeasurableSpace Ω := m₀
      letI : MeasurableSpace.CountablyGenerated Ω := hcg
      IsProbabilityMeasure μ₀ ∧
      ∀ (n : ℕ) (hn : 4 ≤ n) (C0 : ℝ) (hC0 : 0 ≤ C0)
          (ε : ℝ) (hε : 0 < ε)
          (hεsmall : ε < 1 / (4 * Real.sqrt (n : ℝ))),
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
        let O : Fin n → (Fin n → Ω) → Ω := fun i ξ => ξ i
        let gcoord : Fin n → Ω → ℝ := fun _ o => g o / N
        let Q : (Fin n → Ω) → (Fin n → Ω) := fun ξ i => O i ξ
        let D1 : (Fin n → Ω) → ℝ := residualStatisticD n r
        let D2 : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r C0 rho 1
        let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r C0 rho 1
        let Ddel : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
        let Jdel : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
        let B1del : (Fin n → Ω) → Fin n → ℝ := studentizerClipBudgetDeleted n r C0 rho 1
        let κ : (Fin n → Ω) → ℝ := fun _ => 0
        let W0 : (Fin n → Ω) → ℝ := fun ξ => ∑ i : Fin n, gcoord i (O i ξ)
        let V0 : (Fin n → Ω) → ℝ :=
          fun ξ => Real.sqrt (∑ i : Fin n, (gcoord i (O i ξ)) ^ 2)
        let T0 : (Fin n → Ω) → ℝ := fun ξ =>
          if V0 ξ = 0 then κ ξ else
            (W0 ξ + D1 (Q ξ)) / (V0 ξ * Real.sqrt (1 + D2 (Q ξ)))
        let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
        let mAugLocal : MeasurableSpace (Ω × ℝ) := m₀.prod (borel ℝ)
        let mAug : MeasurableSpace (Fin n → Ω × ℝ) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (fun _ : Fin n => mAugLocal)
        let νlocal : Fin n → @Measure (Ω × ℝ) mAugLocal :=
          fun _ => @Measure.prod Ω ℝ m₀ (borel ℝ) μ₀ lambda01
        let ν : @Measure (Fin n → Ω × ℝ) mAug :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mAugLocal) νlocal
        let q : (Fin n → Ω × ℝ) → (Fin n → Ω) := fun x i => (x i).1
        let c : Fin n → (Ω × ℝ) → ℝ := fun _ =>
          Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode
            (MeasurableSpace.natGeneratingSequence (Ω × ℝ))
        let ξlocal : Fin n → (Ω × ℝ) → ℝ := fun i t => gcoord i t.1
        let Ylocal : Fin n → (Ω × ℝ) → ℝ := fun i =>
          Shao.OQ6.QuantizedObservationCoding.quantizedObservation ε (ξlocal i) (c i)
        let ξ : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => gcoord i (x i).1
        let Y : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => Ylocal i (x i)
        let a : Fin n → ℝ := Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν Y
        let s : ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν Y
        let ηlocal : Fin n → (Ω × ℝ) → ℝ := fun i =>
          Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a i) s (Ylocal i)
        let η : Fin n → (Fin n → Ω × ℝ) → ℝ :=
          Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
        let C : (Fin n → Ω × ℝ) → (Fin n → ℝ) := fun x i => η i x
        let W : (Fin n → Ω × ℝ) → ℝ := fun x => ∑ i : Fin n, ξ i x
        let V : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (ξ i x) ^ 2)
        let Wη : (Fin n → Ω × ℝ) → ℝ := fun x => ∑ i : Fin n, η i x
        let Vη : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (η i x) ^ 2)
        let b : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (1 + D2 (q x))
        let Dη : ℝ → (Fin n → Ω × ℝ) → ℝ :=
          fun z x => D1 (q x) + W x - Wη x + z * b x * (Vη x - V x)
        let Tη : ℝ → (Fin n → Ω × ℝ) → ℝ :=
          fun z x => (Wη x + Dη z x) / (Vη x * b x)
        let Z0 : Set (Fin n → Ω) := {ξ | projectionV n g ξ = 0}
        let Z : Set (Fin n → Ω × ℝ) := {x | V x = 0}
        let p0 : ℝ := P.real Z0
        let comparisons : Set (ℝ → ℝ → Prop) :=
          {R | R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
            R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
            R = (fun a b : ℝ => a = b)}
        let F0 : (ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω) := fun R z =>
          {ξ | R (projectionW n g ξ + D1 ξ)
            (z * projectionV n g ξ * Real.sqrt (1 + D2 ξ))}
        let A0 : (ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω) :=
          fun R z => {ξ | R (Tclip ξ) z}
        let Eη : (ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω × ℝ) :=
          fun R z => {x | R (Tη z x) z}
        @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ ∧
        P₀ = @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P ∧
        (∀ i : Fin n, Measurable (O i) ∧ MeasurePreserving (O i) P₀ μ₀) ∧
        iIndepFun O P₀ ∧
        (∀ i : Fin n, Measurable (gcoord i) ∧
          MemLp (fun ξ => gcoord i (O i ξ)) 2 P₀ ∧
          (∫ ξ, gcoord i (O i ξ) ∂P₀) = 0 ∧
          (∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1 / (n : ℝ)) ∧
        (∑ i : Fin n, ∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1 ∧
        Q = id ∧ W0 = projectionW n g ∧ V0 = projectionV n g ∧ T0 = Tclip ∧
        Measurable D1 ∧ Measurable D2 ∧
        (∀ ξ : Fin n → Ω, (1 / 2 : ℝ) ≤ 1 + D2 ξ) ∧
        Measurable[mN₀, borel ℝ] Tclip ∧ Measurable[mN, borel ℝ] Tclip ∧
        @Measure.map (Fin n → Ω) ℝ mN₀ (borel ℝ) Tclip P₀ =
          @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) Tclip P ∧
        IsProbabilityMeasure ν ∧ MeasurePreserving q ν P₀ ∧
        (1 / 2 : ℝ) < s ∧
        (∀ (i : Fin n) (x : Fin n → Ω × ℝ), η i x = ηlocal i (x i)) ∧
        iIndepFun η ν ∧
        (∀ i : Fin n, Measurable (η i) ∧ MemLp (η i) 2 ν) ∧
        (∀ i : Fin n, Integrable (η i) ν ∧ Integrable (fun x => (η i x) ^ 2) ν) ∧
        (∀ i : Fin n, (∫ x, η i x ∂ν) = 0) ∧
        (∑ i : Fin n, ∫ x, (η i x) ^ 2 ∂ν) = 1 ∧
        (∀ (i : Fin n) (t : ℝ), ν {x : Fin n → Ω × ℝ | η i x = t} = 0) ∧
        ν {x : Fin n → Ω × ℝ | Vη x = 0} = 0 ∧
        (∀ᵐ x ∂ν, 0 < Vη x ∧ 0 < b x ∧ 0 < Vη x * b x) ∧
        Measurable[mAug, borel (Fin n → ℝ)] C ∧
        MeasurableSpace.comap C (borel (Fin n → ℝ)) = mAug ∧
        (∀ (H : (Fin n → Ω × ℝ) → ℝ), Measurable H →
          ∃ F : (Fin n → ℝ) → ℝ, Measurable[borel (Fin n → ℝ), borel ℝ] F ∧
            ∀ x : Fin n → Ω × ℝ, H x = F (C x)) ∧
        (∀ (i : Fin n) (d : ({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ), Measurable d →
          ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
            (∀ y : {j : Fin n // j ≠ i} → Ω × ℝ,
              d y = F (fun j => ηlocal j.val (y j))) ∧
            Measurable[borel (Fin n → ℝ), borel ℝ]
              (fun t : Fin n → ℝ => F (fun j => t j.val)) ∧
            ∀ x : Fin n → Ω × ℝ, d (fun j => x j.val) = F (fun j => η j.val x)) ∧
        (∃ G2 : (Fin n → ℝ) → ℝ,
          Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
          (∀ x : Fin n → Ω × ℝ, D2 (q x) = G2 (C x)) ∧
          ∀ z : ℝ, ∃ G1 : (Fin n → ℝ) → ℝ,
            Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
            ∀ x : Fin n → Ω × ℝ, Dη z x = G1 (C x)) ∧
        (∀ i : Fin n,
          ∃ Fdel : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdel ∧
            ∀ x : Fin n → Ω × ℝ,
              (Ddel (q x) i, Jdel (q x) i, B1del (q x) i) =
                Fdel (fun j : {j : Fin n // j ≠ i} => η j.val x)) ∧
        (∀ z : ℝ, Measurable (Dη z) ∧ Measurable (Tη z)) ∧
        MeasurableSet[mN₀] Z0 ∧ MeasurableSet[mN] Z0 ∧ MeasurableSet Z ∧
        ν Z = P₀ Z0 ∧ P₀ Z0 = P Z0 ∧ ν.real Z = p0 ∧
        (∀ (z : ℝ) (x : Fin n → Ω × ℝ),
          Wη x + Dη z x - z * Vη x * b x = W x + D1 (q x) - z * V x * b x) ∧
        (∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
          MeasurableSet[mN₀] (A0 R z) ∧ MeasurableSet[mN] (A0 R z) ∧
          MeasurableSet[mN₀] (F0 R z) ∧ MeasurableSet[mN] (F0 R z) ∧
          MeasurableSet (Eη R z) ∧
          ν (Eη R z) = P₀ (F0 R z) ∧ P₀ (F0 R z) = P (F0 R z) ∧
          (∀ ξ : Fin n → Ω, ξ ∈ (A0 R z ∆ F0 R z) → ξ ∈ Z0) ∧
          P (A0 R z ∆ F0 R z) ≤ P Z0 ∧
          |P.real (A0 R z) - ν.real (Eη R z)| ≤ p0)
:= by
  classical
  intro g r v rho
  have hmodel :=
    Shao.OQ6.OriginalCountablyGeneratedModel.actual_normalized_original_countably_generated_model
      μ h hh hh2 hhsymm hcenter hprojectionsecond
  dsimp only at hmodel
  rcases hmodel with ⟨m₀, hm₀, hcg, hh₀, hf₀, hbase⟩
  refine ⟨m₀, hm₀, hcg, ?_⟩
  intro μ₀
  letI : MeasurableSpace Ω := m₀
  letI : MeasurableSpace.CountablyGenerated Ω := hcg
  rcases hbase with
    ⟨hμ₀prob, hμ₀map, hgpoint, hrpoint, hvpoint, hrhopoint, hrow,
      hh₂₀, hcenter₀, hgmeas₀, hg₂₀, hgmean₀, hgsecond₀,
      hrmeas₀, hr₂₀, hrsymm₀, hrcanonical₀, hglaw₀, hglp₀,
      hpair₀, hfinite, hstatistics⟩
  change (fun o => ∫ y, h o y ∂μ₀) = g at hgpoint
  have hgmeas : Measurable g := by
    rw [← hgpoint]
    exact hgmeas₀
  have hg₂ : MemLp g 2 μ₀ := by
    rw [← hgpoint]
    exact hg₂₀
  have hgmean : (∫ o, g o ∂μ₀) = 0 := by
    rw [← hgpoint]
    exact hgmean₀
  have hgsecond : (∫ o, g o ^ 2 ∂μ₀) = 1 := by
    rw [← hgpoint]
    exact hgsecond₀
  letI : IsProbabilityMeasure μ₀ := hμ₀prob
  change IsProbabilityMeasure μ₀ ∧ _
  refine ⟨hμ₀prob, ?_⟩
  intro n hn C0 hC0 ε hε hεsmall
  intro mN mN₀ P P₀ N O gcoord Q D1 D2 Tclip Ddel Jdel B1del κ W0 V0 T0
    lambda01 mAugLocal mAug νlocal ν q c ξlocal Ylocal ξ Y a s ηlocal η C W V
    Wη Vη b Dη Tη Z0 Z p0 comparisons F0 A0 Eη
  have hfiniteN := hfinite (Fin n) (inferInstance : Fintype (Fin n))
  rcases hfiniteN with ⟨hP₀prob, hidmeas, hP₀map, hfiniteLaw⟩
  change @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ at hP₀prob
  change Measurable[mN, mN₀] (id : (Fin n → Ω) → Fin n → Ω) at hidmeas
  change P₀ = @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P at hP₀map
  letI : IsProbabilityMeasure P₀ := hP₀prob
  let zeroLevel : ℝ := 0
  have hstatistics0 := hstatistics n hn zeroLevel (by dsimp [zeroLevel]; norm_num)
    (by dsimp [zeroLevel]; norm_num) C0 hC0
  rcases hstatistics0 with
    ⟨hWm, hVm, hD1m, hJm, hAm, hB1m, hs2m, hsm, hdm, hD2m,
      hTclipm, hTactualm, hZ0m, hZsm, hhalf, hzero, hTcliplaw,
      hTactuallaw, hdeleted⟩
  change Measurable D1 at hD1m
  change Measurable D2 at hD2m
  change Measurable[mN₀, borel ℝ] Tclip at hTclipm
  change MeasurableSet[mN₀] Z0 at hZ0m
  change ∀ ξ : Fin n → Ω, (1 / 2 : ℝ) ≤ 1 + D2 ξ at hhalf
  change @Measure.map (Fin n → Ω) ℝ mN₀ (borel ℝ) Tclip P₀ =
    @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) Tclip P at hTcliplaw
  have hTclipOriginal : Measurable[mN, borel ℝ] Tclip :=
    hTclipm.comp hidmeas
  have hZ0Original : MeasurableSet[mN] Z0 := hZ0m.preimage hidmeas
  have hZ0law : P₀ Z0 = P Z0 := by
    rw [hP₀map]
    exact Measure.map_apply hidmeas hZ0m
  have hZ0real : P₀.real Z0 = p0 := by
    change (P₀ Z0).toReal = (P Z0).toReal
    exact congrArg ENNReal.toReal hZ0law
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 4) hn
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 4) hn
  have hnRpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
  have hnRne : (n : ℝ) ≠ 0 := ne_of_gt hnRpos
  have hNsq : N ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hO (i : Fin n) : Measurable (O i) := measurable_pi_apply i
  have hcoord (i : Fin n) : MeasurePreserving (O i) P₀ μ₀ :=
    measurePreserving_eval (μ := fun _ : Fin n => μ₀) i
  have hQid : Q = id := by
    funext ξ i
    rfl
  let coordinateMarginal : Fin n → @Measure Ω m₀ :=
    fun i => @Measure.map (Fin n → Ω) Ω mN₀ m₀ (O i) P₀
  let ambientProductLaw : @Measure (Fin n → Ω) mN₀ :=
    @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
      (fun _ : Fin n => m₀) coordinateMarginal
  have hcoordMap (i : Fin n) : P₀.map (O i) = μ₀ := (hcoord i).map_eq
  have hproduct : ambientProductLaw = P₀ := by
    dsimp only [ambientProductLaw, P₀]
    congr 1
    funext i
    exact hcoordMap i
  have hOindep : iIndepFun O P₀ := by
    apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hO i).aemeasurable)).2
    change Measure.map Q P₀ = ambientProductLaw
    rw [hQid, Measure.map_id, hproduct]
  have pullbackIntegral (i : Fin n) (f : Ω → ℝ) (hf : Measurable f) :
      (∫ ξ : Fin n → Ω, f (ξ i) ∂P₀) = ∫ o, f o ∂μ₀ := by
    calc
      _ = ∫ o, f o ∂P₀.map (O i) :=
        (integral_map (hcoord i).measurable.aemeasurable hf.aestronglyMeasurable).symm
      _ = _ := by rw [hcoordMap i]
  let squareProjection : Ω → ℝ := fun o => g o ^ 2
  have hgcoordm (i : Fin n) : Measurable (gcoord i) := hgmeas.div_const N
  have hgcoord₂ (i : Fin n) : MemLp (fun ξ => gcoord i (O i ξ)) 2 P₀ := by
    simpa only [gcoord, O, div_eq_mul_inv, Function.comp_def] using
      ((hg₂.comp_measurePreserving (hcoord i)).mul_const N⁻¹)
  have hgcoordmean (i : Fin n) : (∫ ξ, gcoord i (O i ξ) ∂P₀) = 0 := by
    change (∫ ξ, g (ξ i) / N ∂P₀) = 0
    rw [integral_div, pullbackIntegral i g hgmeas, hgmean, zero_div]
  have hgcoordsecond (i : Fin n) :
      (∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1 / (n : ℝ) := by
    change (∫ ξ, (g (ξ i) / N) ^ 2 ∂P₀) = 1 / (n : ℝ)
    simp_rw [div_pow]
    rw [integral_div, pullbackIntegral i squareProjection (hgmeas.pow_const 2),
      hgsecond, hNsq]
  have hgcoordenergy : (∑ i : Fin n, ∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1 := by
    simp_rw [hgcoordsecond]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hnRne]
  have hW0eq : W0 = projectionW n g := by
    funext ξ
    dsimp only [W0, gcoord, O, projectionW, N]
    rw [Finset.sum_div]
  have hV0eq : V0 = projectionV n g := by
    funext ξ
    dsimp only [V0, projectionV, projectionEnergy]
    apply congrArg Real.sqrt
    change (∑ i : Fin n, (g (ξ i) / N) ^ 2) =
      (∑ i : Fin n, g (ξ i) ^ 2) / (n : ℝ)
    simp only [div_pow, ← Finset.sum_div, hNsq]
  have hT0eq : T0 = Tclip := by
    funext ξ
    simp only [T0, hW0eq, hV0eq, hQid, id_eq, Tclip, clippedCenteredStatistic,
      κ, D1, D2]
  have hD2positive (ξ : Fin n → Ω) : 0 < 1 + D2 ξ :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hhalf ξ)
  have hD2pos : ∀ᵐ ξ ∂P₀, 0 < 1 + D2 (Q ξ) := by
    simpa only [hQid, id_eq] using ae_of_all P₀ hD2positive
  let ambientA : Type u := Fin n → Ω
  let ambientX : Fin n → Type u := fun _ : Fin n => Ω
  let ambientMX : ∀ i : Fin n, MeasurableSpace (ambientX i) := fun _ : Fin n => m₀
  letI : ∀ i : Fin n, MeasurableSpace (ambientX i) := ambientMX
  letI : ∀ i : Fin n, MeasurableSpace.CountablyGenerated (ambientX i) := fun _ => hcg
  have hcanonical :=
    Shao.OQ6.AmbientCanonicalCodingTransport.ambient_canonical_normalized_observation_consumer
      (X := ambientX) P₀ n hn1 O hO hOindep gcoord hgcoordm hgcoord₂ hgcoordmean
      hgcoordenergy D1 D2 hD1m hD2m κ (by exact measurable_const) hD2pos ε hε hεsmall
  dsimp only at hcanonical
  simp only [hcoordMap] at hcanonical
  rcases hcanonical with
    ⟨hνprob, hQpres, hqpres, hs, hηeval, hηindep, hηL2, hηInts,
      hηmean, hηenergy, hηnull, hVηnull, hVηpos, hCmeas, hCcomap,
      hfactor, hretained, hscalar, hT0meas, hTηmeas, hZambientmeas,
      hZmeas, hZlaw, hZreal, hsigned, hcompare⟩
  have hpositiveDenominator : ∀ᵐ x ∂ν, 0 < Vη x ∧ 0 < b x ∧ 0 < Vη x * b x := by
    filter_upwards [hVηpos] with x hx
    have hbpos : 0 < b x := Real.sqrt_pos.mpr (hD2positive (q x))
    exact ⟨hx, hbpos, mul_pos hx hbpos⟩
  have hZcodedlaw : ν Z = P₀ Z0 := by
    change ν Z = P₀ {ξ : Fin n → Ω | V0 ξ = 0} at hZlaw
    simpa only [hV0eq] using hZlaw
  have hZcodedreal : ν.real Z = p0 := by
    change (ν Z).toReal = (P Z0).toReal
    exact congrArg ENNReal.toReal (hZcodedlaw.trans hZ0law)
  have hdeletedFactor (i : Fin n) :
      ∃ Fdel : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdel ∧
        ∀ x : Fin n → Ω × ℝ,
          (Ddel (q x) i, Jdel (q x) i, B1del (q x) i) =
            Fdel (fun j : {j : Fin n // j ≠ i} => η j.val x) := by
    rcases hdeleted i with
      ⟨hcapi, hDdi, hJdi, hAdi, hBdi, htesti, E_i, hEmeas, hEpoint, hElaw, hERetlaw⟩
    let retainedMeasurableSpace : MeasurableSpace ({j : Fin n // j ≠ i} → Ω) :=
      @MeasurableSpace.pi {j : Fin n // j ≠ i} (fun _ => Ω) (fun _ => m₀)
    let retainedAugmentedMeasurableSpace : MeasurableSpace ({j : Fin n // j ≠ i} → Ω × ℝ) :=
      @MeasurableSpace.pi {j : Fin n // j ≠ i} (fun _ => Ω × ℝ) (fun _ => mAugLocal)
    let retainedFirstProjection : ({j : Fin n // j ≠ i} → Ω × ℝ) →
        ({j : Fin n // j ≠ i} → Ω) := fun y j => (y j).1
    have hFirstMeas : Measurable retainedFirstProjection := by
      apply Measurable.of_eval
      intro j
      exact (measurable_pi_apply j).fst
    let dD : ({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ :=
      fun y => (E_i (retainedFirstProjection y)).1
    let dJ : ({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ :=
      fun y => (E_i (retainedFirstProjection y)).2.1
    let dB : ({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ :=
      fun y => (E_i (retainedFirstProjection y)).2.2
    have hTripleBorel :
        (inferInstance : MeasurableSpace (ℝ × ℝ × ℝ)) =
          borel (ℝ × ℝ × ℝ) := BorelSpace.measurable_eq
    have hEproduct :
        Measurable[retainedMeasurableSpace,
          (inferInstance : MeasurableSpace (ℝ × ℝ × ℝ))] E_i := by
      rw [hTripleBorel]
      exact hEmeas
    have hdD : Measurable dD := hEproduct.fst.comp hFirstMeas
    have hdJ : Measurable dJ := hEproduct.snd.fst.comp hFirstMeas
    have hdB : Measurable dB := hEproduct.snd.snd.comp hFirstMeas
    rcases hretained i dD hdD with ⟨FD, hFDm, hFDpoint, hFDlift, hFDfull⟩
    rcases hretained i dJ hdJ with ⟨FJ, hFJm, hFJpoint, hFJlift, hFJfull⟩
    rcases hretained i dB hdB with ⟨FB, hFBm, hFBpoint, hFBlift, hFBfull⟩
    let FdelWitness : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ :=
      fun t => (FD t, FJ t, FB t)
    have hFdelBorel :
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ),
          borel (ℝ × ℝ × ℝ)] FdelWitness := by
      rw [← hTripleBorel]
      exact hFDm.prodMk (hFJm.prodMk hFBm)
    refine ⟨FdelWitness, hFdelBorel, ?_⟩
    intro x
    have hDpoint : Ddel (q x) i = dD (fun j => x j.val) :=
      congrArg Prod.fst (hEpoint (q x))
    have hJpoint : Jdel (q x) i = dJ (fun j => x j.val) :=
      congrArg Prod.fst (congrArg Prod.snd (hEpoint (q x)))
    have hBpoint : B1del (q x) i = dB (fun j => x j.val) :=
      congrArg Prod.snd (congrArg Prod.snd (hEpoint (q x)))
    change (Ddel (q x) i, Jdel (q x) i, B1del (q x) i) =
      (FD (fun j => η j.val x), FJ (fun j => η j.val x), FB (fun j => η j.val x))
    rw [hDpoint, hJpoint, hBpoint, hFDfull x, hFJfull x, hFBfull x]
  have hcomparison0 (z : ℝ) (R : ℝ → ℝ → Prop) (hR : R ∈ comparisons) :
      MeasurableSet[mN₀] (A0 R z) ∧ MeasurableSet[mN₀] (F0 R z) ∧
      MeasurableSet (Eη R z) ∧ ν (Eη R z) = P₀ (F0 R z) ∧
      (∀ᵐ ξ ∂P₀, ξ ∈ (A0 R z ∆ F0 R z) → ξ ∈ Z0) ∧
      P₀ (A0 R z ∆ F0 R z) ≤ P₀ Z0 ∧
      |P₀.real (A0 R z) - ν.real (Eη R z)| ≤ P₀.real Z0 := by
    have hc := hcompare z R hR
    change
      MeasurableSet {ξ : Fin n → Ω | R (T0 ξ) z} ∧
      MeasurableSet {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ))
        (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))} ∧
      MeasurableSet (Eη R z) ∧
      ν (Eη R z) = P₀ {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ))
        (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))} ∧
      (∀ᵐ ξ ∂P₀, ξ ∈ ({ξ : Fin n → Ω | R (T0 ξ) z} ∆
        {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ))
          (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))}) → V0 ξ = 0) ∧
      P₀ ({ξ : Fin n → Ω | R (T0 ξ) z} ∆
        {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ))
          (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))}) ≤
        P₀ {ξ : Fin n → Ω | V0 ξ = 0} ∧
      |P₀.real {ξ : Fin n → Ω | R (T0 ξ) z} - ν.real (Eη R z)| ≤
        P₀.real {ξ : Fin n → Ω | V0 ξ = 0} at hc
    simpa only [hT0eq, hW0eq, hV0eq, hQid, id_eq, A0, F0, Z0, Set.mem_setOf_eq] using hc
  refine ⟨hP₀prob, hP₀map, (fun i => ⟨hO i, hcoord i⟩), hOindep,
    (fun i => ⟨hgcoordm i, hgcoord₂ i, hgcoordmean i, hgcoordsecond i⟩),
    hgcoordenergy, hQid, hW0eq, hV0eq, hT0eq, hD1m, hD2m, hhalf,
    hTclipm, hTclipOriginal, hTcliplaw, hνprob, hqpres, hs, hηeval, hηindep,
    hηL2, hηInts, hηmean, hηenergy, hηnull, hVηnull, hpositiveDenominator,
    hCmeas, hCcomap, hfactor, hretained, hscalar, hdeletedFactor,
    (fun z => ⟨?_, hTηmeas z⟩), hZ0m, hZ0Original, hZmeas,
    hZcodedlaw, hZ0law, hZcodedreal, hsigned, ?_⟩
  · dsimp only [Dη]
    have hWηm : Measurable Wη :=
      Finset.measurable_sum Finset.univ (fun i _ => (hηL2 i).1)
    have hVηm : Measurable Vη :=
      (Finset.measurable_sum Finset.univ (fun i _ => ((hηL2 i).1).pow_const 2)).sqrt
    have hWaugm : Measurable W := by
      exact Finset.measurable_sum Finset.univ
        (fun i _ => (hgcoordm i).comp ((measurable_pi_apply i).fst))
    have hVaugm : Measurable V := by
      exact (Finset.measurable_sum Finset.univ
        (fun i _ => ((hgcoordm i).comp ((measurable_pi_apply i).fst)).pow_const 2)).sqrt
    exact (((hD1m.comp hqpres.measurable).add hWaugm).sub hWηm).add
      ((measurable_const.mul (measurable_const.add (hD2m.comp hqpres.measurable)).sqrt).mul
        (hVηm.sub hVaugm))
  · intro z R hR
    rcases hcomparison0 z R hR with ⟨hA0m, hF0m, hEηm, hEηlaw, hAFae, hAF₀, hreal₀⟩
    have hA0Original : MeasurableSet[mN] (A0 R z) := hA0m.preimage hidmeas
    have hF0Original : MeasurableSet[mN] (F0 R z) := hF0m.preimage hidmeas
    have hF0law : P₀ (F0 R z) = P (F0 R z) := by
      rw [hP₀map]
      exact Measure.map_apply hidmeas hF0m
    have hA0law : P₀ (A0 R z) = P (A0 R z) := by
      rw [hP₀map]
      exact Measure.map_apply hidmeas hA0m
    have hA0real : P₀.real (A0 R z) = P.real (A0 R z) := by
      change (P₀ (A0 R z)).toReal = (P (A0 R z)).toReal
      exact congrArg ENNReal.toReal hA0law
    have hpoint : ∀ ξ : Fin n → Ω, ξ ∈ (A0 R z ∆ F0 R z) → ξ ∈ Z0 := by
      intro ξ hdiff
      by_contra hnot
      have hvne : projectionV n g ξ ≠ 0 := hnot
      have hvpos : 0 < projectionV n g ξ :=
        lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hvne)
      have hbpos : 0 < Real.sqrt (1 + D2 ξ) := Real.sqrt_pos.mpr (hD2positive ξ)
      have hden : 0 < projectionV n g ξ * Real.sqrt (1 + D2 ξ) := mul_pos hvpos hbpos
      have hTeq : Tclip ξ = (projectionW n g ξ + D1 ξ) /
          (projectionV n g ξ * Real.sqrt (1 + D2 ξ)) := by
        simp only [Tclip, clippedCenteredStatistic, if_neg hvne, D1, D2]
      have hrel : R (Tclip ξ) z ↔ R (projectionW n g ξ + D1 ξ)
          (z * projectionV n g ξ * Real.sqrt (1 + D2 ξ)) := by
        rw [hTeq]
        rw [mul_assoc]
        change R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
          R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
          R = (fun a b : ℝ => a = b) at hR
        rcases hR with rfl | rfl | rfl | rfl | rfl
        · exact div_le_iff₀ hden
        · exact div_lt_iff₀ hden
        · exact le_div_iff₀ hden
        · exact lt_div_iff₀ hden
        · constructor
          · intro heq
            apply le_antisymm
            · exact (div_le_iff₀ hden).mp heq.le
            · exact (le_div_iff₀ hden).mp heq.ge
          · intro heq
            apply le_antisymm
            · exact (div_le_iff₀ hden).mpr heq.le
            · exact (le_div_iff₀ hden).mpr heq.ge
      have hevents : ξ ∈ A0 R z ↔ ξ ∈ F0 R z := hrel
      rcases Set.mem_symmDiff.mp hdiff with ⟨ha, hf⟩ | ⟨hf, ha⟩
      · exact hf (hevents.mp ha)
      · exact ha (hevents.mpr hf)
    have hreal : |P.real (A0 R z) - ν.real (Eη R z)| ≤ p0 := by
      simpa only [hA0real, hZ0real] using hreal₀
    exact ⟨hA0m, hA0Original, hF0m, hF0Original, hEηm, hEηlaw, hF0law,
      hpoint, measure_mono hpoint, hreal⟩

end

end Shao.OQ6.OriginalClippedCanonicalCoding
