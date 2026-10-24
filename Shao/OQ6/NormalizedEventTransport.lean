import Shao.OQ6.ActualMomentNormalization
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

set_option autoImplicit false

namespace Shao.OQ6.NormalizedEventTransport

noncomputable section

open MeasureTheory
open scoped BigOperators Classical symmDiff

theorem actual_normalized_signed_distance_transport
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {n : ℕ} (ξ Y : Fin n → Ω → ℝ)
    (D1 D2 : Ω → ℝ) :
    let η : Fin n → Ω → ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
    let Wη : Ω → ℝ := fun ω => ∑ i : Fin n, η i ω
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let Vη : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (η i ω) ^ 2)
    let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
    let Dη : ℝ → Ω → ℝ := fun z ω => D1 ω + W ω - Wη ω + z * b ω * (Vη ω - V ω)
    let comparisons : Set (ℝ → ℝ → Prop) := {R | R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨ R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨ R = (fun a b : ℝ => a = b)}
    (∀ (z : ℝ) (ω : Ω),
      Wη ω + Dη z ω - z * Vη ω * b ω =
        W ω + D1 ω - z * V ω * b ω) ∧
    (∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
      {ω : Ω | R (Wη ω + Dη z ω) (z * Vη ω * b ω)} =
        {ω : Ω | R (W ω + D1 ω) (z * V ω * b ω)}) := by
  classical
  let η : Fin n → Ω → ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
  let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
  let Wη : Ω → ℝ := fun ω => ∑ i : Fin n, η i ω
  let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
  let Vη : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (η i ω) ^ 2)
  let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
  let Dη : ℝ → Ω → ℝ := fun z ω => D1 ω + W ω - Wη ω + z * b ω * (Vη ω - V ω)
  let comparisons : Set (ℝ → ℝ → Prop) := {R | R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨ R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨ R = (fun a b : ℝ => a = b)}
  change
    (∀ (z : ℝ) (ω : Ω),
      Wη ω + Dη z ω - z * Vη ω * b ω =
        W ω + D1 ω - z * V ω * b ω) ∧
    (∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
      {ω : Ω | R (Wη ω + Dη z ω) (z * Vη ω * b ω)} =
        {ω : Ω | R (W ω + D1 ω) (z * V ω * b ω)})
  have hdist : ∀ (z : ℝ) (ω : Ω),
      Wη ω + Dη z ω - z * Vη ω * b ω =
        W ω + D1 ω - z * V ω * b ω := by
    intro z ω
    dsimp only [Dη]
    ring
  refine ⟨hdist, ?_⟩
  intro z R hR
  change R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
    R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
    R = (fun a b : ℝ => a = b) at hR
  rcases hR with rfl | rfl | rfl | rfl | rfl
  all_goals
    ext ω
    simp only [Set.mem_setOf_eq]
    have heq := hdist z ω
    constructor <;> intro h <;> linarith only [heq, h]

theorem actual_normalized_quotient_projection_zero_transport
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    {n : ℕ} (ξ Y : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hY : ∀ i : Fin n, Measurable (Y i))
    (D1 D2 κ : Ω → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2) (hκ : Measurable κ)
    (hD2pos : ∀ᵐ ω ∂ν, 0 < 1 + D2 ω)
    (hηpos : ∀ᵐ ω ∂ν, 0 < Real.sqrt (∑ i : Fin n,
      (Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y i ω) ^ 2)) :
    let η : Fin n → Ω → ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
    let Wη : Ω → ℝ := fun ω => ∑ i : Fin n, η i ω
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let Vη : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (η i ω) ^ 2)
    let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
    let Dη : ℝ → Ω → ℝ := fun z ω => D1 ω + W ω - Wη ω + z * b ω * (Vη ω - V ω)
    let T : Ω → ℝ := fun ω => if V ω = 0 then κ ω else (W ω + D1 ω) / (V ω * b ω)
    let Tη : ℝ → Ω → ℝ := fun z ω => (Wη ω + Dη z ω) / (Vη ω * b ω)
    let Z : Set Ω := {ω : Ω | V ω = 0}
    let p0 : ℝ := ν.real Z
    let comparisons : Set (ℝ → ℝ → Prop) := {R | R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨ R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨ R = (fun a b : ℝ => a = b)}
    let F : (ℝ → ℝ → Prop) → ℝ → Set Ω := fun R z => {ω : Ω | R (W ω + D1 ω) (z * V ω * b ω)}
    let A : (ℝ → ℝ → Prop) → ℝ → Set Ω := fun R z => {ω : Ω | R (T ω) z}
    let E : (ℝ → ℝ → Prop) → ℝ → Set Ω := fun R z => {ω : Ω | R (Tη z ω) z}
    (∀ i : Fin n, Measurable (η i)) ∧
    Measurable W ∧ Measurable Wη ∧ Measurable V ∧ Measurable Vη ∧
    Measurable b ∧ (∀ z : ℝ, Measurable (Dη z)) ∧
    Measurable T ∧ (∀ z : ℝ, Measurable (Tη z)) ∧ MeasurableSet Z ∧
    (∀ᵐ ω ∂ν, ∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
      (R (Tη z ω) z ↔ R (W ω + D1 ω) (z * V ω * b ω))) ∧
    (∀ (ω : Ω), 0 < V ω → 0 < 1 + D2 ω →
      ∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
        (R (T ω) z ↔ R (W ω + D1 ω) (z * V ω * b ω))) ∧
    (∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
      MeasurableSet (F R z) ∧ MeasurableSet (A R z) ∧ MeasurableSet (E R z) ∧
      ν (E R z) = ν (F R z) ∧
      (∀ᵐ ω ∂ν, ω ∈ (A R z ∆ F R z) → ω ∈ Z) ∧
      ν (A R z ∆ F R z) ≤ ν Z ∧
      |ν.real (A R z) - ν.real (F R z)| ≤ p0 ∧
      ν (A R z ∆ E R z) ≤ ν Z ∧
      |ν.real (A R z) - ν.real (E R z)| ≤ p0) := by
  classical
  let η : Fin n → Ω → ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
  let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
  let Wη : Ω → ℝ := fun ω => ∑ i : Fin n, η i ω
  let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
  let Vη : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (η i ω) ^ 2)
  let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
  let Dη : ℝ → Ω → ℝ := fun z ω => D1 ω + W ω - Wη ω + z * b ω * (Vη ω - V ω)
  let T : Ω → ℝ := fun ω => if V ω = 0 then κ ω else (W ω + D1 ω) / (V ω * b ω)
  let Tη : ℝ → Ω → ℝ := fun z ω => (Wη ω + Dη z ω) / (Vη ω * b ω)
  let Z : Set Ω := {ω : Ω | V ω = 0}
  let p0 : ℝ := ν.real Z
  let comparisons : Set (ℝ → ℝ → Prop) := {R | R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨ R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨ R = (fun a b : ℝ => a = b)}
  let F : (ℝ → ℝ → Prop) → ℝ → Set Ω := fun R z => {ω : Ω | R (W ω + D1 ω) (z * V ω * b ω)}
  let A : (ℝ → ℝ → Prop) → ℝ → Set Ω := fun R z => {ω : Ω | R (T ω) z}
  let E : (ℝ → ℝ → Prop) → ℝ → Set Ω := fun R z => {ω : Ω | R (Tη z ω) z}
  change
    (∀ i : Fin n, Measurable (η i)) ∧
    Measurable W ∧ Measurable Wη ∧ Measurable V ∧ Measurable Vη ∧
    Measurable b ∧ (∀ z : ℝ, Measurable (Dη z)) ∧
    Measurable T ∧ (∀ z : ℝ, Measurable (Tη z)) ∧ MeasurableSet Z ∧
    (∀ᵐ ω ∂ν, ∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
      (R (Tη z ω) z ↔ R (W ω + D1 ω) (z * V ω * b ω))) ∧
    (∀ (ω : Ω), 0 < V ω → 0 < 1 + D2 ω →
      ∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
        (R (T ω) z ↔ R (W ω + D1 ω) (z * V ω * b ω))) ∧
    (∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
      MeasurableSet (F R z) ∧ MeasurableSet (A R z) ∧ MeasurableSet (E R z) ∧
      ν (E R z) = ν (F R z) ∧
      (∀ᵐ ω ∂ν, ω ∈ (A R z ∆ F R z) → ω ∈ Z) ∧
      ν (A R z ∆ F R z) ≤ ν Z ∧
      |ν.real (A R z) - ν.real (F R z)| ≤ p0 ∧
      ν (A R z ∆ E R z) ≤ ν Z ∧
      |ν.real (A R z) - ν.real (E R z)| ≤ p0)
  have hηm : ∀ i : Fin n, Measurable (η i) := by
    intro i
    change Measurable (fun ω =>
      (Y i ω - Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν Y i) /
        Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν Y)
    exact ((hY i).sub measurable_const).div_const _
  have hWm : Measurable W := by
    exact Finset.measurable_sum Finset.univ (fun i _ => hξ i)
  have hWηm : Measurable Wη := by
    exact Finset.measurable_sum Finset.univ (fun i _ => hηm i)
  have hVm : Measurable V := by
    apply Measurable.sqrt
    exact Finset.measurable_sum Finset.univ (fun i _ => by
      exact (hξ i).pow (measurable_const : Measurable (fun _ : Ω => (2 : ℕ))))
  have hVηm : Measurable Vη := by
    apply Measurable.sqrt
    exact Finset.measurable_sum Finset.univ (fun i _ => by
      exact (hηm i).pow (measurable_const : Measurable (fun _ : Ω => (2 : ℕ))))
  have hbm : Measurable b := by
    exact (measurable_const.add hD2).sqrt
  have hDηm : ∀ z : ℝ, Measurable (Dη z) := by
    intro z
    exact ((hD1.add hWm).sub hWηm).add
      ((measurable_const.mul hbm).mul (hVηm.sub hVm))
  have hZm : MeasurableSet Z := measurableSet_eq_fun hVm measurable_const
  have hTm : Measurable T := by
    exact Measurable.ite hZm hκ ((hWm.add hD1).div (hVm.mul hbm))
  have hTηm : ∀ z : ℝ, Measurable (Tη z) := by
    intro z
    exact (hWηm.add (hDηm z)).div (hVηm.mul hbm)
  have hrelm (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
      (R : ℝ → ℝ → Prop) (hR : R ∈ comparisons) :
      MeasurableSet {ω : Ω | R (f ω) (g ω)} := by
    change R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
      R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
      R = (fun a b : ℝ => a = b) at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl
    · exact measurableSet_le hf hg
    · exact measurableSet_lt hf hg
    · exact measurableSet_le hg hf
    · exact measurableSet_lt hg hf
    · exact measurableSet_eq_fun hf hg
  have hdiv_compare (a c z : ℝ) (hc : 0 < c)
      (R : ℝ → ℝ → Prop) (hR : R ∈ comparisons) :
      (R (a / c) z ↔ R a (z * c)) := by
    change R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
      R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
      R = (fun a b : ℝ => a = b) at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl
    · exact div_le_iff₀ hc
    · exact div_lt_iff₀ hc
    · exact le_div_iff₀ hc
    · exact lt_div_iff₀ hc
    · constructor
      · intro h
        exact le_antisymm ((div_le_iff₀ hc).mp h.le) ((le_div_iff₀ hc).mp h.ge)
      · intro h
        exact le_antisymm ((div_le_iff₀ hc).mpr h.le) ((le_div_iff₀ hc).mpr h.ge)
  have hmult (z : ℝ) (ω : Ω) (R : ℝ → ℝ → Prop) (hR : R ∈ comparisons) :
      (R (Wη ω + Dη z ω) (z * Vη ω * b ω) ↔
        R (W ω + D1 ω) (z * V ω * b ω)) := by
    have hsets :
        {ω : Ω | R (Wη ω + Dη z ω) (z * Vη ω * b ω)} =
          {ω : Ω | R (W ω + D1 ω) (z * V ω * b ω)} :=
      (actual_normalized_signed_distance_transport ν ξ Y D1 D2).2 z R hR
    change (ω ∈ {ω : Ω | R (Wη ω + Dη z ω) (z * Vη ω * b ω)} ↔
      ω ∈ {ω : Ω | R (W ω + D1 ω) (z * V ω * b ω)})
    rw [hsets]
  have hcommon : ∀ᵐ ω ∂ν, ∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
      (R (Tη z ω) z ↔ R (W ω + D1 ω) (z * V ω * b ω)) := by
    filter_upwards [hD2pos, hηpos] with ω hd he
    intro z R hR
    have hbpos : 0 < b ω := Real.sqrt_pos.mpr hd
    have hepos : 0 < Vη ω := he
    have hc : 0 < Vη ω * b ω := mul_pos hepos hbpos
    have hquot : R (Tη z ω) z ↔ R (Wη ω + Dη z ω) (z * Vη ω * b ω) := by
      simpa only [Tη, mul_assoc] using hdiv_compare (Wη ω + Dη z ω) (Vη ω * b ω) z hc R hR
    exact hquot.trans (hmult z ω R hR)
  have hphysical : ∀ (ω : Ω), 0 < V ω → 0 < 1 + D2 ω →
      ∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
        (R (T ω) z ↔ R (W ω + D1 ω) (z * V ω * b ω)) := by
    intro ω hv hd z R hR
    have hbpos : 0 < b ω := Real.sqrt_pos.mpr hd
    have hc : 0 < V ω * b ω := mul_pos hv hbpos
    simpa only [T, if_neg (ne_of_gt hv), mul_assoc] using
      hdiv_compare (W ω + D1 ω) (V ω * b ω) z hc R hR
  have hreal_subset (S : Set Ω) (hS : ∀ᵐ ω ∂ν, ω ∈ S → ω ∈ Z) :
      ν.real S ≤ p0 := by
    have hinter : S =ᵐ[ν] (S ∩ Z) := by
      filter_upwards [hS] with ω h
      exact propext ⟨fun hω => ⟨hω, h hω⟩, fun hω => hω.1⟩
    calc
      ν.real S = ν.real (S ∩ Z) := measureReal_congr hinter
      _ ≤ ν.real Z := measureReal_mono (fun _ h => h.2) (measure_ne_top ν Z)
      _ = p0 := rfl
  refine ⟨hηm, hWm, hWηm, hVm, hVηm, hbm, hDηm, hTm, hTηm, hZm,
    hcommon, hphysical, ?_⟩
  intro z R hR
  have hFm : MeasurableSet (F R z) :=
    hrelm (fun ω => W ω + D1 ω) (fun ω => z * V ω * b ω)
      (hWm.add hD1) ((measurable_const.mul hVm).mul hbm) R hR
  have hAm : MeasurableSet (A R z) := hrelm T (fun _ => z) hTm measurable_const R hR
  have hEm : MeasurableSet (E R z) := hrelm (Tη z) (fun _ => z) (hTηm z) measurable_const R hR
  have hEF : E R z =ᵐ[ν] F R z := by
    filter_upwards [hcommon] with ω h
    exact propext (h z R hR)
  have hEFmeasure : ν (E R z) = ν (F R z) := measure_congr hEF
  have hAF : ∀ᵐ ω ∂ν, ω ∈ (A R z ∆ F R z) → ω ∈ Z := by
    filter_upwards [hD2pos] with ω hd
    intro hdiff
    by_contra hnot
    have hvne : V ω ≠ 0 := hnot
    have hv : 0 < V ω := by
      have hvnonneg : 0 ≤ V ω := Real.sqrt_nonneg _
      by_contra hbad
      apply hvne
      linarith
    have heq : (ω ∈ A R z ↔ ω ∈ F R z) := hphysical ω hv hd z R hR
    rcases Set.mem_symmDiff.mp hdiff with ⟨ha, hf⟩ | ⟨hf, ha⟩
    · exact hf (heq.mp ha)
    · exact ha (heq.mpr hf)
  have hAFmeasure : ν (A R z ∆ F R z) ≤ ν Z := measure_mono_ae hAF
  have hAFreal : |ν.real (A R z) - ν.real (F R z)| ≤ p0 :=
    (abs_measureReal_sub_le_measureReal_symmDiff hAm.nullMeasurableSet hFm.nullMeasurableSet).trans
      (hreal_subset (A R z ∆ F R z) hAF)
  have hAE : ∀ᵐ ω ∂ν, ω ∈ (A R z ∆ E R z) → ω ∈ Z := by
    filter_upwards [hAF, hEF] with ω hsub heq
    intro hdiff
    apply hsub
    simpa only [Set.mem_symmDiff, heq] using hdiff
  have hAEmeasure : ν (A R z ∆ E R z) ≤ ν Z := measure_mono_ae hAE
  have hAEreal : |ν.real (A R z) - ν.real (E R z)| ≤ p0 :=
    (abs_measureReal_sub_le_measureReal_symmDiff hAm.nullMeasurableSet hEm.nullMeasurableSet).trans
      (hreal_subset (A R z ∆ E R z) hAE)
  exact ⟨hFm, hAm, hEm, hEFmeasure, hAF, hAFmeasure, hAFreal, hAEmeasure, hAEreal⟩

end

end Shao.OQ6.NormalizedEventTransport
