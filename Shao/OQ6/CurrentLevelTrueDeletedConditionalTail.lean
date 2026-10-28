import Shao.OQ6.NormalizedIntegrableTailAssembly

set_option autoImplicit false
universe u v
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology symmDiff

namespace Shao.OQ6.CurrentLevelTrueDeletedConditionalTail
noncomputable section
theorem actual_current_level_true_deleted_conditional_tail_consumer
    {X : Type u} [MeasurableSpace X]
    {O : Type v} [MeasurableSpace O]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (P : Measure O) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (ξ : Fin n → X → ℝ) (ξ0 : Fin n → O → ℝ)
    (η : ℕ → Fin n → X → ℝ)
    (D D2 B : X → ℝ) (Aη : ℕ → X → ℝ)
    (Adeleteη : ℕ → Fin n → X → ℝ) (Bdelete : Fin n → X → ℝ)
    (A0 B0 : O → ℝ) (A0delete B0delete : Fin n → O → ℝ)
    (originalClip physical : O → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hD : Measurable D) (hD2 : Measurable D2)
    (hOriginalClip : Measurable originalClip) (hPhysical : Measurable physical)
    (hη : ∀ (k : ℕ) (i : Fin n), Measurable (η k i))
    (hηindep : ∀ k : ℕ, iIndepFun (η k) ν)
    (hη2 : ∀ (k : ℕ) (i : Fin n), MemLp (η k i) 2 ν)
    (hηmean : ∀ (k : ℕ) (i : Fin n), (∫ x, η k i x ∂ν) = 0)
    (hηenergy : ∀ k : ℕ, (∑ i : Fin n, ∫ x, (η k i x) ^ 2 ∂ν) = 1)
    (hD2pos : ∀ᵐ x ∂ν, 0 < 1 + D2 x)
    (hηpos : ∀ k : ℕ, ∀ᵐ x ∂ν,
      0 < Real.sqrt (∑ i : Fin n, (η k i x) ^ 2))
    (cSZ C1 C2 C3 C4 : ℝ)
    (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
      cSZ C1 C2 C3 C4)
    (z : ℝ) (hz : 1 ≤ z) (pUpper p2 pZ pClip : ℝ) :
    let C : ℕ → X → (Fin n → ℝ) := fun k x i => η k i x
    let W : X → ℝ := fun x => ∑ i : Fin n, ξ i x
    let V : X → ℝ := fun x => Real.sqrt (∑ i : Fin n, (ξ i x) ^ 2)
    let Wη : ℕ → X → ℝ := fun k x => ∑ i : Fin n, η k i x
    let Vη : ℕ → X → ℝ := fun k x => Real.sqrt (∑ i : Fin n, (η k i x) ^ 2)
    let b : X → ℝ := fun x => Real.sqrt (1 + D2 x)
    let Dη : ℕ → X → ℝ := fun k x =>
      D x + W x - Wη k x + z * b x * (Vη k x - V x)
    let Tη : ℕ → X → ℝ := fun k x => (Wη k x + Dη k x) / (Vη k x * b x)
    let codedClip : X → ℝ := fun x =>
      if V x = 0 then 0 else (W x + D x) / (V x * b x)
    let F : Set X := {x | z * V x * b x ≤ W x + D x}
    let Z : Set X := {x | V x = 0}
    let Eη : ℕ → Set X := fun k => {x | z * |Dη k x| > Vη k x / 4}
    let E2 : Set X := {x | z ^ 2 * |D2 x| > (1 / 4 : ℝ)}
    let ℓ0 : Fin n → O → ℝ := fun i o => z * ξ0 i o - (z * ξ0 i o) ^ 2 / 2
    let ℓη : ℕ → Fin n → X → ℝ := fun k i x => z * η k i x - (z * η k i x) ^ 2 / 2
    let S0 : O → ℝ := fun o => ∑ i : Fin n, ℓ0 i o
    let Sη : ℕ → X → ℝ := fun k x => ∑ i : Fin n, ℓη k i x
    let S0minus : Fin n → O → ℝ := fun i o => ∑ j ∈ Finset.univ.erase i, ℓ0 j o
    let Sηminus : ℕ → Fin n → X → ℝ := fun k i x => ∑ j ∈ Finset.univ.erase i, ℓη k j x
    let I0 : ℝ := ∫ o, Real.exp (S0 o) ∂P
    let Iη : ℕ → ℝ := fun k => ∫ x, Real.exp (Sη k x) ∂ν
    let full0 : O → ℝ := fun o => (z * A0 o + z ^ 2 * B0 o) * Real.exp (S0 o)
    let fullη : ℕ → X → ℝ := fun k x => (z * Aη k x + z ^ 2 * B x) * Real.exp (Sη k x)
    let deleted0 : Fin n → O → ℝ := fun i o =>
      (min |z * ξ0 i o| 1 * (|A0 o - A0delete i o| + z * |B0 o - B0delete i o|)) *
        Real.exp (S0minus i o)
    let deletedη : ℕ → Fin n → X → ℝ := fun k i x =>
      (min |z * η k i x| 1 * (|Aη k x - Adeleteη k i x| + z * |B x - Bdelete i x|)) *
        Real.exp (Sηminus k i x)
    let sourceCost0 : ℝ := ((∫ o, full0 o ∂P) + ∑ i : Fin n, ∫ o, deleted0 i o ∂P) / I0
    let sourceCostη : ℕ → ℝ := fun k =>
      ((∫ x, fullη k x ∂ν) + ∑ i : Fin n, ∫ x, deletedη k i x ∂ν) / Iη k
    let δ0 : Fin n → ℝ := fun i => ∫ o, (z * ξ0 i o) ^ 2 * min |z * ξ0 i o| 1 ∂P
    let δη : ℕ → Fin n → ℝ := fun k i => ∫ x, (z * η k i x) ^ 2 * min |z * η k i x| 1 ∂ν
    let L0 : ℝ := ∑ i : Fin n, δ0 i
    let Lη : ℕ → ℝ := fun k => ∑ i : Fin n, δη k i
    let lower0 : ℝ := Shao.standardNormalTail z * Real.exp (-C1 * L0) * (1 - C2 * sourceCost0)
    let lowerη : ℕ → ℝ := fun k =>
      Shao.standardNormalTail z * Real.exp (-C1 * Lη k) * (1 - C2 * sourceCostη k)
    let upper0 : ℝ := Shao.standardNormalTail z * Real.exp (C3 * L0) * (1 + C4 * sourceCost0)
    let upperη : ℕ → ℝ := fun k =>
      Shao.standardNormalTail z * Real.exp (C3 * Lη k) * (1 + C4 * sourceCostη k)
    (∀ k : ℕ, ∃ F1 F2 FA FB : (Fin n → ℝ) → ℝ,
      Measurable[borel (Fin n → ℝ), borel ℝ] F1 ∧
      Measurable[borel (Fin n → ℝ), borel ℝ] F2 ∧
      Measurable[borel (Fin n → ℝ), borel ℝ] FA ∧
      Measurable[borel (Fin n → ℝ), borel ℝ] FB ∧
      ∀ x : X, Dη k x = F1 (C k x) ∧ D2 x = F2 (C k x) ∧
        Aη k x = FA (C k x) ∧ B x = FB (C k x)) →
    (∀ (k : ℕ) (i : Fin n),
      ∃ FAdelete FBdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] FAdelete ∧
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] FBdelete ∧
        ∀ x : X, Adeleteη k i x = FAdelete (fun j => η k j.val x) ∧
          Bdelete i x = FBdelete (fun j => η k j.val x)) →
    (∀ (k : ℕ) (x : X), 0 ≤ Aη k x ∧ 0 ≤ B x) →
    (∀ (k : ℕ) (i : Fin n) (x : X), 0 ≤ Adeleteη k i x ∧ 0 ≤ Bdelete i x) →
    (∀ k : ℕ, ∀ᵐ x ∂ν, |Dη k x| ≤ Aη k x ∧ |D2 x| ≤ B x) →
    (∀ k : ℕ, Integrable (fun x => Real.exp (Sη k x)) ν ∧ 0 < Iη k) →
    (∀ k : ℕ, Integrable (fullη k) ν) →
    (∀ (k : ℕ) (i : Fin n), Integrable (deletedη k i) ν) →
    (∀ᶠ k : ℕ in Filter.atTop,
      (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧ Lη k < cSZ * z ^ 2) →
    Filter.Tendsto Lη Filter.atTop (nhds L0) →
    Filter.Tendsto sourceCostη Filter.atTop (nhds sourceCost0) →
    Measure.map codedClip ν = Measure.map originalClip P →
    P.real {o : O | originalClip o ≠ physical o} ≤ pClip →
    ν.real Z ≤ pZ →
    ν.real E2 ≤ p2 →
    (∀ γ : ℝ, 0 < γ → ∀ᶠ k : ℕ in Filter.atTop, ν.real (Eη k) ≤ pUpper + γ) →
    (∀ᶠ k : ℕ in Filter.atTop,
      lowerη k ≤ ν.real {x : X | z ≤ Tη k x} ∧
      ν.real {x : X | z ≤ Tη k x} ≤ upperη k + ν.real (Eη k) + ν.real E2) ∧
    Filter.Tendsto lowerη Filter.atTop (nhds lower0) ∧
    Filter.Tendsto upperη Filter.atTop (nhds upper0) ∧
    (∀ k : ℕ, ν.real {x : X | z ≤ Tη k x} = ν.real F) ∧
    lower0 ≤ ν.real F ∧
    ν.real F ≤ upper0 + pUpper + p2 ∧
    lower0 - pZ - pClip ≤ P.real {o : O | z ≤ physical o} ∧
    P.real {o : O | z ≤ physical o} ≤ upper0 + pUpper + p2 + pZ + pClip ∧
    (∀ payment : ℝ, pUpper ≤ payment → p2 ≤ payment → pZ ≤ payment → pClip ≤ payment →
      lower0 - 2 * payment ≤ P.real {o : O | z ≤ physical o} ∧
      P.real {o : O | z ≤ physical o} ≤ upper0 + 4 * payment)
:= by
  classical
  intro C W V Wη Vη b Dη Tη codedClip F Z Eη E2
    ℓ0 ℓη S0 Sη S0minus Sηminus I0 Iη full0 fullη deleted0 deletedη
    sourceCost0 sourceCostη δ0 δη L0 Lη lower0 lowerη upper0 upperη
  intro hFullFactor hDeletedFactor hNonneg hDeletedNonneg hDom
    hTilt hFullInt hDeletedInt hBudget hLlim hRlim hClippedLaw
    hClipPay hZPay hE2Pay hUpperPay
  rcases hSZ with ⟨hcSZ, hC1, hC2, hC3, hC4, hSource⟩
  -- The conditional engine receives the true deleted factor at each k.
  have hScalar (k : ℕ) (hd : ∀ i : Fin n, δη k i ≤ 1)
      (hl : Lη k ≤ cSZ * z ^ 2) :
      lowerη k ≤ ν.real {x : X | z ≤ Tη k x} ∧
      ν.real {x : X | z ≤ Tη k x} ≤
        upperη k + ν.real (Eη k) + ν.real E2 := by
    obtain ⟨F1, F2, FA, FB, hF1, hF2, hFA, hFB, hFactor⟩ := hFullFactor k
    let FAdelete (i : Fin n) : ({j : Fin n // j ≠ i} → ℝ) → ℝ :=
      Classical.choose (hDeletedFactor k i)
    let FBdelete (i : Fin n) : ({j : Fin n // j ≠ i} → ℝ) → ℝ :=
      Classical.choose (Classical.choose_spec (hDeletedFactor k i))
    have hDeleteSpec (i : Fin n) :
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FAdelete i) ∧
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FBdelete i) ∧
        ∀ x : X, Adeleteη k i x = FAdelete i (fun j => η k j.val x) ∧
          Bdelete i x = FBdelete i (fun j => η k j.val x) :=
      Classical.choose_spec (Classical.choose_spec (hDeletedFactor k i))
    have hF1eq (x : X) : Dη k x = F1 (fun i => η k i x) := (hFactor x).1
    have hF2eq (x : X) : D2 x = F2 (fun i => η k i x) := (hFactor x).2.1
    have hFAeq (x : X) : Aη k x = FA (fun i => η k i x) := (hFactor x).2.2.1
    have hFBeq (x : X) : B x = FB (fun i => η k i x) := (hFactor x).2.2.2
    have hFAdeleteEq (i : Fin n) (x : X) :
        Adeleteη k i x = FAdelete i (fun j => η k j.val x) :=
      ((hDeleteSpec i).2.2 x).1
    have hFBdeleteEq (i : Fin n) (x : X) :
        Bdelete i x = FBdelete i (fun j => η k j.val x) :=
      ((hDeleteSpec i).2.2 x).2
    have hs := hSource ν n hn (η k) F1 F2 FA FB FAdelete FBdelete
      (hη k) (hηindep k) (hη2 k) (hηmean k) (hηenergy k)
      hF1 hF2 hFA hFB (fun i => (hDeleteSpec i).1)
      (fun i => (hDeleteSpec i).2.1) z
    dsimp only at hs
    simp only [← hF1eq, ← hF2eq, ← hFAeq, ← hFBeq,
      ← hFAdeleteEq, ← hFBdeleteEq] at hs
    exact hs (hNonneg k) (hDeletedNonneg k) (hDom k)
      hD2pos (hηpos k) (hTilt k).1 (hTilt k).2
      (hFullInt k) (hDeletedInt k) hz hd hl
  have hEngineEventually : ∀ᶠ k : ℕ in Filter.atTop,
      lowerη k ≤ ν.real {x : X | z ≤ Tη k x} ∧
      ν.real {x : X | z ≤ Tη k x} ≤
        upperη k + ν.real (Eη k) + ν.real E2 := by
    filter_upwards [hBudget] with k hk
    exact hScalar k (fun i => (hk.1 i).le.trans (by norm_num)) hk.2.le
  -- These limits retain the literal full-Iη normalized source cost.
  have hLowerExp : Filter.Tendsto (fun k : ℕ => Real.exp (-C1 * Lη k))
      Filter.atTop (nhds (Real.exp (-C1 * L0))) :=
    Real.continuous_exp.continuousAt.tendsto.comp (hLlim.const_mul (-C1))
  have hLowerFactor : Filter.Tendsto (fun k : ℕ => 1 - C2 * sourceCostη k)
      Filter.atTop (nhds (1 - C2 * sourceCost0)) :=
    tendsto_const_nhds.sub (hRlim.const_mul C2)
  have hLowerLim : Filter.Tendsto lowerη Filter.atTop (nhds lower0) :=
    (tendsto_const_nhds.mul hLowerExp).mul hLowerFactor
  have hUpperExp : Filter.Tendsto (fun k : ℕ => Real.exp (C3 * Lη k))
      Filter.atTop (nhds (Real.exp (C3 * L0))) :=
    Real.continuous_exp.continuousAt.tendsto.comp (hLlim.const_mul C3)
  have hUpperFactor : Filter.Tendsto (fun k : ℕ => 1 + C4 * sourceCostη k)
      Filter.atTop (nhds (1 + C4 * sourceCost0)) :=
    tendsto_const_nhds.add (hRlim.const_mul C4)
  have hUpperLim : Filter.Tendsto upperη Filter.atTop (nhds upper0) :=
    (tendsto_const_nhds.mul hUpperExp).mul hUpperFactor
  have hWm : Measurable W :=
    Finset.measurable_sum Finset.univ (fun i _ => hξ i)
  have hVm : Measurable V := by
    apply Measurable.sqrt
    exact Finset.measurable_sum Finset.univ
      (fun i _ => (hξ i).pow_const (2 : ℕ))
  have hbm : Measurable b := (measurable_const.add hD2).sqrt
  have hCodedMeas : Measurable codedClip := by
    exact Measurable.ite (measurableSet_eq_fun hVm measurable_const)
      measurable_const ((hWm.add hD).div (hVm.mul hbm))
  have hFm : MeasurableSet F :=
    measurableSet_le ((measurable_const.mul hVm).mul hbm) (hWm.add hD)
  have hCodedTailMeas : MeasurableSet {x : X | z ≤ codedClip x} :=
    measurableSet_le measurable_const hCodedMeas
  -- The raw event is fixed in k, so no continuity of a CDF is used.
  have hSigned (k : ℕ) (x : X) :
      Wη k x + Dη k x - z * Vη k x * b x =
        W x + D x - z * V x * b x := by
    dsimp only [Dη]
    ring
  have hTailMass (k : ℕ) : ν.real {x : X | z ≤ Tη k x} = ν.real F := by
    have hAE : {x : X | z ≤ Tη k x} =ᵐ[ν] F := by
      filter_upwards [hD2pos, hηpos k] with x hd2 hVη
      have hbpos : 0 < b x := Real.sqrt_pos.mpr hd2
      have hden : 0 < Vη k x * b x := mul_pos hVη hbpos
      have hquot : z ≤ Tη k x ↔ z * Vη k x * b x ≤ Wη k x + Dη k x := by
        simpa only [Tη, mul_assoc] using
          (le_div_iff₀ hden :
            z ≤ (Wη k x + Dη k x) / (Vη k x * b x) ↔
              z * (Vη k x * b x) ≤ Wη k x + Dη k x)
      have hraw : z * Vη k x * b x ≤ Wη k x + Dη k x ↔
          z * V x * b x ≤ W x + D x := by
        have hdist := hSigned k x
        constructor <;> intro hle <;> linarith only [hdist, hle]
      exact propext (hquot.trans hraw)
    exact measureReal_congr hAE
  have hLowerRaw : lower0 ≤ ν.real F := by
    apply le_of_tendsto hLowerLim
    filter_upwards [hEngineEventually] with k hk
    calc
      lowerη k ≤ ν.real {x : X | z ≤ Tη k x} := hk.1
      _ = ν.real F := hTailMass k
  have hUpperError (γ : ℝ) (hγ : 0 < γ) :
      ν.real F ≤ upper0 + pUpper + γ + p2 := by
    have hEv : ∀ᶠ k : ℕ in Filter.atTop,
        ν.real F ≤ upperη k + pUpper + γ + p2 := by
      filter_upwards [hEngineEventually, hUpperPay γ hγ] with k hk hpay
      calc
        ν.real F = ν.real {x : X | z ≤ Tη k x} := (hTailMass k).symm
        _ ≤ upperη k + ν.real (Eη k) + ν.real E2 := hk.2
        _ ≤ upperη k + pUpper + γ + p2 := by linarith only [hpay, hE2Pay]
    have hLim : Filter.Tendsto (fun k : ℕ => upperη k + pUpper + γ + p2)
        Filter.atTop (nhds (upper0 + pUpper + γ + p2)) :=
      ((hUpperLim.add tendsto_const_nhds).add tendsto_const_nhds).add
        tendsto_const_nhds
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hLim hEv
  have hUpperRaw : ν.real F ≤ upper0 + pUpper + p2 := by
    by_contra hnot
    have hpos : 0 < ν.real F - (upper0 + pUpper + p2) :=
      sub_pos.mpr (lt_of_not_ge hnot)
    have hHalf := hUpperError ((ν.real F - (upper0 + pUpper + p2)) / 2)
      (by linarith only [hpos])
    linarith only [hHalf, hpos]
  -- The coded projection-zero fee and original clipping fee stay separate.
  have hRealSubset (S : Set X) (hS : ∀ᵐ x ∂ν, x ∈ S → x ∈ Z) :
      ν.real S ≤ ν.real Z := by
    have hEq : S =ᵐ[ν] (S ∩ Z) := by
      filter_upwards [hS] with x hx
      exact propext ⟨fun h => ⟨h, hx h⟩, fun h => h.1⟩
    calc
      ν.real S = ν.real (S ∩ Z) := measureReal_congr hEq
      _ ≤ ν.real Z := measureReal_mono (fun _ hx => hx.2) (measure_ne_top ν Z)
  have hCFsub : ∀ᵐ x ∂ν, x ∈ ({x : X | z ≤ codedClip x} ∆ F) → x ∈ Z := by
    filter_upwards [hD2pos] with x hd2
    intro hdiff
    by_contra hnot
    have hvne : V x ≠ 0 := hnot
    have hv : 0 < V x := by
      have hnonneg : 0 ≤ V x := Real.sqrt_nonneg _
      by_contra hbad
      apply hvne
      linarith only [hnonneg, hbad]
    have hbpos : 0 < b x := Real.sqrt_pos.mpr hd2
    have hden : 0 < V x * b x := mul_pos hv hbpos
    have heq : (x ∈ {x : X | z ≤ codedClip x} ↔ x ∈ F) := by
      change z ≤ codedClip x ↔ z * V x * b x ≤ W x + D x
      simpa only [codedClip, if_neg hvne, mul_assoc] using
        (le_div_iff₀ hden : z ≤ (W x + D x) / (V x * b x) ↔
          z * (V x * b x) ≤ W x + D x)
    rcases Set.mem_symmDiff.mp hdiff with ⟨hc, hf⟩ | ⟨hf, hc⟩
    · exact hf (heq.mp hc)
    · exact hc (heq.mpr hf)
  have hClipRaw : |ν.real {x : X | z ≤ codedClip x} - ν.real F| ≤ pZ :=
    (abs_measureReal_sub_le_measureReal_symmDiff
      hCodedTailMeas.nullMeasurableSet hFm.nullMeasurableSet).trans
        ((hRealSubset ({x : X | z ≤ codedClip x} ∆ F) hCFsub).trans hZPay)
  have hCodedTail : ν.real {x : X | z ≤ codedClip x} =
      P.real {o : O | z ≤ originalClip o} := by
    have hν := map_measureReal_apply (μ := ν) hCodedMeas
      (measurableSet_Ici : MeasurableSet (Set.Ici z))
    have hP := map_measureReal_apply (μ := P) hOriginalClip
      (measurableSet_Ici : MeasurableSet (Set.Ici z))
    change (Measure.map codedClip ν).real (Set.Ici z) =
      ν.real {x : X | z ≤ codedClip x} at hν
    rw [hClippedLaw] at hν
    exact hν.symm.trans hP
  have hOriginalTail : MeasurableSet {o : O | z ≤ originalClip o} :=
    measurableSet_le measurable_const hOriginalClip
  have hPhysicalTail : MeasurableSet {o : O | z ≤ physical o} :=
    measurableSet_le measurable_const hPhysical
  have hPhysicalSub :
      ({o : O | z ≤ physical o} ∆ {o : O | z ≤ originalClip o}) ⊆
        {o : O | originalClip o ≠ physical o} := by
    intro o ho
    change originalClip o ≠ physical o
    intro heq
    rcases Set.mem_symmDiff.mp ho with ⟨hp, hc⟩ | ⟨hc, hp⟩
    · apply hc
      change z ≤ originalClip o
      rw [heq]
      exact hp
    · apply hp
      change z ≤ physical o
      rw [← heq]
      exact hc
  have hPhysicalCoded :
      |P.real {o : O | z ≤ physical o} - ν.real {x : X | z ≤ codedClip x}| ≤ pClip := by
    rw [hCodedTail]
    exact (abs_measureReal_sub_le_measureReal_symmDiff
      hPhysicalTail.nullMeasurableSet hOriginalTail.nullMeasurableSet).trans
        ((measureReal_mono hPhysicalSub
          (measure_ne_top P {o : O | originalClip o ≠ physical o})).trans hClipPay)
  rcases abs_le.mp hClipRaw with ⟨hClipRawLower, hClipRawUpper⟩
  rcases abs_le.mp hPhysicalCoded with ⟨hPhysicalLower, hPhysicalUpper⟩
  have hLowerPhysical : lower0 - pZ - pClip ≤ P.real {o : O | z ≤ physical o} := by
    linarith only [hLowerRaw, hClipRawLower, hPhysicalLower]
  have hUpperPhysical : P.real {o : O | z ≤ physical o} ≤
      upper0 + pUpper + p2 + pZ + pClip := by
    linarith only [hUpperRaw, hClipRawUpper, hPhysicalUpper]
  refine ⟨hEngineEventually, hLowerLim, hUpperLim, hTailMass,
    hLowerRaw, hUpperRaw, hLowerPhysical, hUpperPhysical, ?_⟩
  intro payment hUpperFee h2Fee hZFee hClipFee
  constructor
  · linarith only [hLowerPhysical, hZFee, hClipFee]
  · linarith only [hUpperPhysical, hUpperFee, h2Fee, hZFee, hClipFee]

end
end Shao.OQ6.CurrentLevelTrueDeletedConditionalTail
