/- Mathematical candidate only: no production source or Lean/AX execution.
   One full original C1 head; no new definitions or instances.
   The concrete qualified Brownian witness is internal to the proof. -/
import Shao.Probability.SourceOriginalHalflineComparison
import Shao.Probability.SourceOriginalGrowingRelative
import Shao.Probability.SourceOriginalZeroEnergyBudget
import Shao.C2.BrownianUpperJointReflection
import Shao.OQ4.CanonicalBrownian

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace Shao.Probability.SourceOriginalFullRelative
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem original_iid_signed_halfline_full_relative_comparison :
    ∃ C : ℝ, 0 < C ∧
      ∀ rhoStar : ℝ, 0 < rhoStar → rhoStar ≤ 1 / 16 →
        ∀ p : ℝ, 2 < p → p ≤ 3 →
          ∀ {Ω : Type*} [MeasurableSpace Ω]
            (mu : Measure Ω) (rho : Measure ℝ)
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
            ∀ (s x : ℝ), (s = 1 ∨ s = -1) → 0 ≤ x → x ∈ I →
              let signedMax : Ω → ℝ := fun omega =>
                Shao.upperMax (s • population omega) hn
              let crossing : Set Ω :=
                {omega | x * Real.sqrt (rawEnergy omega) ≤ signedMax omega}
              let survival : Set Ω :=
                {omega | signedMax omega < x * Real.sqrt (rawEnergy omega)}
              Integrable (crossing.indicator (fun _ : Ω => (1 : ℝ))) mu ∧
              Integrable (survival.indicator (fun _ : Ω => (1 : ℝ))) mu ∧
              mu.real {omega : Ω | rawEnergy omega = 0} ≤
                C * Rn x * Shao.standardNormalTail x ∧
              |mu.real crossing - 2 * Shao.standardNormalTail x| ≤
                C * Rn x * Shao.standardNormalTail x ∧
              |mu.real survival - (1 - 2 * Shao.standardNormalTail x)| ≤
                C * Rn x * Shao.standardNormalTail x ∧
              |mu.real crossing / Shao.standardNormalTail x - 2| ≤ C * Rn x := by
  classical
  obtain ⟨Cc, hCc, hcompact⟩ :=
    SourceOriginalHalflineComparison.original_iid_signed_halfline_compact_comparison
  obtain ⟨Cg, hCg, hgrowing⟩ :=
    SourceOriginalGrowingRelative.original_iid_signed_halfline_growing_relative_comparison
  have hPsiPos (t : ℝ) : 0 < Shao.standardNormalTail t :=
    (Shao.standardNormalTail_basic.2.2.1 t).1
  let Ck : ℝ := (Cc + 16) / Shao.standardNormalTail 1
  let C : ℝ := 1 + Cg + Ck
  have hCk : 0 < Ck := div_pos (by linarith) (hPsiPos 1)
  have hC : 0 < C := by dsimp [C]; linarith
  have hCgC : Cg ≤ C := by dsimp [C]; linarith
  have hCkC : Ck ≤ C := by dsimp [C]; linarith
  -- The already qualified concrete Brownian witness discharges existence.
  have hBM (s x : ℝ) (hs : s = 1 ∨ s = -1) (hx : 0 ≤ x) :
      Shao.OQ4.CanonicalBrownian.law.real
        {omega | ∀ t : Shao.C2.BridgeDomination.BridgeTime,
          s * Shao.OQ4.CanonicalBrownian.B ⟨(t : ℝ), t.property.1⟩ omega < x} =
        1 - 2 * Shao.standardNormalTail x := by
    let PB := Shao.OQ4.CanonicalBrownian.law
    let U : NNReal → Shao.OQ4.CanonicalBrownian.Sample → ℝ :=
      fun t omega => s * Shao.OQ4.CanonicalBrownian.B t omega
    have hU : IsBrownianReal U PB := by
      rcases hs with rfl | rfl
      · simpa [U, PB] using Shao.OQ4.CanonicalBrownian.isBrownianReal
      · have hneg := Shao.OQ4.CanonicalBrownian.isBrownianReal.neg
        convert hneg using 1
        funext t omega
        simp [U, Pi.neg_apply]
    let S : Set Shao.OQ4.CanonicalBrownian.Sample :=
      {omega | ∀ t : Shao.C2.BridgeDomination.BridgeTime,
        U ⟨(t : ℝ), t.property.1⟩ omega < x}
    change PB.real S = 1 - 2 * Shao.standardNormalTail x
    by_cases hx0 : x = 0
    · have hzero := hU.toIsPreBrownianReal.eval_zero_ae_eq_zero
      have hSae : ∀ᵐ omega ∂PB, omega ∉ S := hzero.mono (by
        intro omega homega hS
        have hbad := hS (0 : Shao.C2.BridgeDomination.BridgeTime)
        change U 0 omega < x at hbad
        simpa [hx0, homega] using hbad)
      have hSzero : PB S = 0 := by simpa only [ae_iff, not_not, Set.setOf_mem_eq] using hSae
      have hSreal : PB.real S = 0 := by simp only [Measure.real, hSzero, ENNReal.toReal_zero]
      rw [hSreal, hx0, Shao.standardNormalTail_basic.2.1]
      norm_num
    have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hIic (t : ℝ) : (gaussianReal 0 1).real (Set.Iic t) =
        1 - Shao.standardNormalTail t := by
      have h := (Shao.standardNormalTail_representation t).2.1
      rw [ProbabilityTheory.cdf_eq_real] at h
      linarith
    have hIci (t : ℝ) : (gaussianReal 0 1).real (Set.Ici t) =
        Shao.standardNormalTail t :=
      (Shao.standardNormalTail_representation t).1.symm
    have hbracket (v : ℝ) (hv : v < x) :
        1 - Shao.standardNormalTail v - Shao.standardNormalTail (2 * x - v) ≤ PB.real S ∧
        PB.real S ≤ 1 - Shao.standardNormalTail x -
          Shao.standardNormalTail (2 * x - v) := by
      let J : Set Shao.OQ4.CanonicalBrownian.Sample :=
        {omega | omega ∈ S ∧ U 1 omega ≤ v}
      let E : Set Shao.OQ4.CanonicalBrownian.Sample :=
        {omega | v < U 1 omega ∧ U 1 omega < x}
      have href := Shao.C2.BrownianUpperJointReflection.brownian_upper_joint_reflection
        U PB hU x v hxpos hv
      change PB.real J + (gaussianReal 0 1).real (Set.Ici (2 * x - v)) =
        (gaussianReal 0 1).real (Set.Iic v) at href
      rw [hIci, hIic] at href
      have hJ : PB.real J =
          1 - Shao.standardNormalTail v - Shao.standardNormalTail (2 * x - v) := by
        linarith
      have hEnds : PB.real E = (gaussianReal 0 1).real (Set.Ioo v x) := by
        calc
          PB.real E = PB.real {omega | U 1 omega ∈ Set.Ioo v x} := by rfl
          _ = (gaussianReal 0 1).real {z : ℝ | z ∈ Set.Ioo v x} :=
            (hU.toIsPreBrownianReal.hasLaw_eval 1).measureReal_eq measurableSet_Ioo
          _ = (gaussianReal 0 1).real (Set.Ioo v x) := by rw [Set.setOf_mem_eq]
      have hTailSplit : Set.Ioi v = Set.Ioo v x ∪ Set.Ici x := by
        ext z
        simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioo, Set.mem_Ici]
        constructor
        · intro hz
          by_cases hzx : z < x
          · exact Or.inl ⟨hz, hzx⟩
          · exact Or.inr (le_of_not_gt hzx)
        · rintro (⟨hz, _⟩ | hz)
          · exact hz
          · exact hv.trans_le hz
      have hDisjoint : Disjoint (Set.Ioo v x) (Set.Ici x) := by
        apply Set.disjoint_left.mpr
        intro z hz hz'
        exact (not_lt_of_ge hz') hz.2
      have hSplit := measureReal_union (μ := gaussianReal 0 1) hDisjoint measurableSet_Ici
      rw [← hTailSplit, hIci] at hSplit
      change Shao.standardNormalTail v =
        (gaussianReal 0 1).real (Set.Ioo v x) + Shao.standardNormalTail x at hSplit
      have hE : PB.real E = Shao.standardNormalTail v - Shao.standardNormalTail x := by
        linarith
      have hsub0 : J ⊆ S := fun _ h => h.1
      have hsub1 : S ⊆ J ∪ E := by
        intro omega homega
        by_cases hv' : U 1 omega ≤ v
        · exact Or.inl ⟨homega, hv'⟩
        · apply Or.inr
          refine ⟨lt_of_not_ge hv', ?_⟩
          have hOne :
              (⟨((1 : Shao.C2.BridgeDomination.BridgeTime) : ℝ),
                (1 : Shao.C2.BridgeDomination.BridgeTime).property.1⟩ : NNReal) = 1 := by
            ext
            simp
          have hh := homega (1 : Shao.C2.BridgeDomination.BridgeTime)
          rw [hOne] at hh
          exact hh
      constructor
      · rw [← hJ]
        exact measureReal_mono hsub0
      · have hu := (measureReal_mono (μ := PB) hsub1).trans
          (measureReal_union_le J E)
        rw [hJ, hE] at hu
        linarith
    have hV : Filter.Tendsto (fun v : ℝ => v) (nhdsWithin x (Set.Iio x)) (nhds x) :=
      continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
    have hP := (Shao.standardNormal_derivatives x).2.continuousAt.tendsto.comp hV
    have hArg : Filter.Tendsto (fun v : ℝ => 2 * x - v)
        (nhdsWithin x (Set.Iio x)) (nhds x) := by
      convert Filter.Tendsto.sub tendsto_const_nhds hV using 1 <;> ring
    have hP2 := (Shao.standardNormal_derivatives x).2.continuousAt.tendsto.comp hArg
    have hev : Filter.Eventually (fun v : ℝ => v < x) (nhdsWithin x (Set.Iio x)) :=
      self_mem_nhdsWithin
    have hlo : 1 - Shao.standardNormalTail x - Shao.standardNormalTail x ≤ PB.real S :=
      le_of_tendsto ((tendsto_const_nhds.sub hP).sub hP2)
        (hev.mono fun v hv => (hbracket v hv).1)
    have hhi : PB.real S ≤ 1 - Shao.standardNormalTail x - Shao.standardNormalTail x :=
      ge_of_tendsto (tendsto_const_nhds.sub hP2)
        (hev.mono fun v hv => (hbracket v hv).2)
    linarith
  refine ⟨C, hC, ?_⟩
  intro rhoStar hrho0 hrho16 p hp2 hp3 Ω _ mu rho _ _ n hn X hX hIndep hLaw h2 hmean hsecond hp
  let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
  let sigma : ℝ := Real.sqrt sigmaSq
  let scale : ℝ := sigma * Real.sqrt (n : ℝ)
  let nu : Measure ℝ := Measure.map (fun z : ℝ => z / scale) rho
  let Rn : ℝ → ℝ := fun t => Shao.truncationBudget nu n t
  let population : Ω → Shao.Path n := Shao.Probability.samplePath X
  let rawEnergy : Ω → ℝ := fun omega => ∑ i : Fin n, (X i omega) ^ 2
  dsimp only
  intro s x hs hx hI
  let signedMax : Ω → ℝ := fun omega => Shao.upperMax (s • population omega) hn
  let crossing : Set Ω := {omega | x * Real.sqrt (rawEnergy omega) ≤ signedMax omega}
  let survival : Set Ω := {omega | signedMax omega < x * Real.sqrt (rawEnergy omega)}
  change Integrable (crossing.indicator (fun _ : Ω => (1 : ℝ))) mu ∧
    Integrable (survival.indicator (fun _ : Ω => (1 : ℝ))) mu ∧
    mu.real {omega | rawEnergy omega = 0} ≤ C * Rn x * Shao.standardNormalTail x ∧
    |mu.real crossing - 2 * Shao.standardNormalTail x| ≤ C * Rn x * Shao.standardNormalTail x ∧
    |mu.real survival - (1 - 2 * Shao.standardNormalTail x)| ≤
      C * Rn x * Shao.standardNormalTail x ∧
    |mu.real crossing / Shao.standardNormalTail x - 2| ≤ C * Rn x
  have hnorm := Shao.Probability.original_raw_normalization_data p hp2 hp3 rho n hn
    h2 hmean hsecond hp
  have h2nu : Integrable (fun z : ℝ => z ^ 2) nu := hnorm.2.2.1
  have hRn (t : ℝ) : 0 ≤ Rn t := Shao.truncationBudget_nonneg nu n h2nu t
  have hTail : 0 < Shao.standardNormalTail x := hPsiPos x
  by_cases hx1 : x ≤ 1
  · have hscale : Real.sqrt ((n : ℝ) * sigmaSq) = scale := by
      dsimp [scale, sigma]
      rw [Real.sqrt_mul (Nat.cast_nonneg n)]
      ring
    have hR : Shao.truncationBudget
        (Measure.map (fun z : ℝ => z / Real.sqrt ((n : ℝ) * sigmaSq)) rho) n 0 = Rn 0 := by
      rw [hscale]
    have hc := hcompact Shao.OQ4.CanonicalBrownian.B Shao.OQ4.CanonicalBrownian.law
      Shao.OQ4.CanonicalBrownian.isBrownianReal mu rho n hn X hX hIndep hLaw
      h2 hmean hsecond
    rcases hc with ⟨hpop, hpair, hshuffle, hstate, hperm, hcx⟩
    have hc0 := hcx s x hs hx hx1
    have hsurvInt : Integrable (survival.indicator (fun _ : Ω => (1 : ℝ))) mu := hc0.2.1
    let AB : Set Shao.OQ4.CanonicalBrownian.Sample :=
      {omega | ∀ t : Shao.C2.BridgeDomination.BridgeTime,
        s * Shao.OQ4.CanonicalBrownian.B ⟨(t : ℝ), t.property.1⟩ omega < x}
    have herror0 : |mu.real survival - Shao.OQ4.CanonicalBrownian.law.real AB| ≤
        Cc * Rn 0 := by
      have hh := hc0.2.2.2.1
      change |mu.real survival - Shao.OQ4.CanonicalBrownian.law.real AB| ≤
        Cc * Shao.truncationBudget
          (Measure.map (fun z : ℝ => z / Real.sqrt ((n : ℝ) * sigmaSq)) rho) n 0 at hh
      rwa [hR] at hh
    have hzero0 : mu.real {omega | rawEnergy omega = 0} ≤ 16 * Rn 0 := by
      have hh := SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget
        mu rho n hn X hX hIndep hLaw h2 hsecond
      change mu.real {omega | rawEnergy omega = 0} ≤
        16 * Shao.truncationBudget
          (Measure.map (fun z : ℝ => z / Real.sqrt ((n : ℝ) * sigmaSq)) rho) n 0 at hh
      rwa [hR] at hh
    have hRm : Rn 0 ≤ Rn x := Shao.truncationBudget_mono nu n h2nu 0 x (by norm_num) hx
    have hPsi1 : Shao.standardNormalTail 1 ≤ Shao.standardNormalTail x :=
      Shao.standardNormalTail_basic.1 hx1
    have hCkTail : Cc + 16 ≤ Ck * Shao.standardNormalTail x := by
      have heq : Ck * Shao.standardNormalTail 1 = Cc + 16 := by
        dsimp [Ck]
        exact div_mul_cancel₀ _ (ne_of_gt (hPsiPos 1))
      calc
        Cc + 16 = Ck * Shao.standardNormalTail 1 := heq.symm
        _ ≤ Ck * Shao.standardNormalTail x := mul_le_mul_of_nonneg_left hPsi1 hCk.le
    have hCcBudget : Cc * Rn 0 ≤ C * Rn x * Shao.standardNormalTail x := by
      calc
        Cc * Rn 0 ≤ Cc * Rn x := mul_le_mul_of_nonneg_left hRm hCc.le
        _ ≤ (Ck * Shao.standardNormalTail x) * Rn x :=
          mul_le_mul_of_nonneg_right (by linarith) (hRn x)
        _ = Ck * Rn x * Shao.standardNormalTail x := by ring
        _ ≤ C * Rn x * Shao.standardNormalTail x :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCkC (hRn x)) hTail.le
    have hzero : mu.real {omega | rawEnergy omega = 0} ≤
        C * Rn x * Shao.standardNormalTail x := by
      calc
        _ ≤ 16 * Rn 0 := hzero0
        _ ≤ 16 * Rn x := mul_le_mul_of_nonneg_left hRm (by norm_num)
        _ ≤ (Ck * Shao.standardNormalTail x) * Rn x :=
          mul_le_mul_of_nonneg_right (by linarith) (hRn x)
        _ = Ck * Rn x * Shao.standardNormalTail x := by ring
        _ ≤ C * Rn x * Shao.standardNormalTail x :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCkC (hRn x)) hTail.le
    have hsurv : |mu.real survival - (1 - 2 * Shao.standardNormalTail x)| ≤
        C * Rn x * Shao.standardNormalTail x := by
      have hAB : Shao.OQ4.CanonicalBrownian.law.real AB =
          1 - 2 * Shao.standardNormalTail x := hBM s x hs hx
      rw [hAB] at herror0
      exact herror0.trans hCcBudget
    have hindicator : crossing.indicator (fun _ : Ω => (1 : ℝ)) =
        fun omega => 1 - survival.indicator (fun _ : Ω => (1 : ℝ)) omega := by
      funext omega
      by_cases h : signedMax omega < x * Real.sqrt (rawEnergy omega)
      · simp [crossing, survival, h, not_le_of_gt h]
      · simp [crossing, survival, h, le_of_not_gt h]
    have hcrossInt : Integrable (crossing.indicator (fun _ : Ω => (1 : ℝ))) mu := by
      rw [hindicator]
      exact (integrable_const (1 : ℝ)).sub hsurvInt
    have hnull : NullMeasurableSet survival mu := by
      have hm : NullMeasurableSet
          {omega | (1 / 2 : ℝ) < survival.indicator (fun _ : Ω => (1 : ℝ)) omega} mu :=
        hsurvInt.aestronglyMeasurable.aemeasurable.nullMeasurable measurableSet_Ioi
      convert hm using 1
      ext omega
      by_cases h : omega ∈ survival <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, h] <;> norm_num
    have hcompl : crossing = survivalᶜ := by
      ext omega
      simp only [crossing, survival, Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
    have hprob : mu.real crossing = 1 - mu.real survival := by
      rw [hcompl, measureReal_compl₀ hnull]
      simp
    have hcross : |mu.real crossing - 2 * Shao.standardNormalTail x| ≤
        C * Rn x * Shao.standardNormalTail x := by
      rw [hprob]
      have heq : 1 - mu.real survival - 2 * Shao.standardNormalTail x =
          -(mu.real survival - (1 - 2 * Shao.standardNormalTail x)) := by ring
      rw [heq, abs_neg]
      exact hsurv
    have hrelative : |mu.real crossing / Shao.standardNormalTail x - 2| ≤ C * Rn x := by
      rw [show mu.real crossing / Shao.standardNormalTail x - 2 =
        (mu.real crossing - 2 * Shao.standardNormalTail x) / Shao.standardNormalTail x by
          field_simp, abs_div, abs_of_pos hTail]
      exact (div_le_iff₀ hTail).2 hcross
    exact ⟨hcrossInt, hsurvInt, hzero, hcross, hsurv, hrelative⟩
  · have hxlarge : 1 ≤ x := (lt_of_not_ge hx1).le
    have hg := hgrowing rhoStar hrho0 hrho16 p hp2 hp3 mu rho n hn X
      hX hIndep hLaw h2 hmean hsecond hp s x hs hxlarge hI
    rcases hg with ⟨hcrossInt, hsurvInt, hzero, hcross, hsurv, hrelative⟩
    have hbudget : Cg * Rn x * Shao.standardNormalTail x ≤
        C * Rn x * Shao.standardNormalTail x :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCgC (hRn x)) hTail.le
    exact ⟨hcrossInt, hsurvInt, hzero.trans hbudget, hcross.trans hbudget,
      hsurv.trans hbudget, hrelative.trans (mul_le_mul_of_nonneg_right hCgC (hRn x))⟩


end Shao.Probability.SourceOriginalFullRelative
