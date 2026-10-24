/- Original positive-prefix maxima at the zero wall; genuine finite-second raw-law budget. -/
import Shao.Probability.SourceFiniteSecondCompactBudget
import Shao.Probability.SourceOriginalZeroEnergyBudget
import Shao.Probability.MeasurablePath
import Shao.Basic.ClosedSurvival

import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000

noncomputable section
namespace Shao.Probability.SourceOriginalZeroWallBudget
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem original_iid_one_sided_zero_wall_budget :
    ∃ C : ℝ, 0 < C ∧
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
        let population : Ω → Shao.Path n := Shao.Probability.samplePath X
        let rawEnergy : Ω → ℝ := fun omega => ∑ i : Fin n, (X i omega) ^ 2
        let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
        let scale : ℝ := Real.sqrt ((n : ℝ) * sigmaSq)
        let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) rho
        let R : ℝ := Shao.truncationBudget normalizedLaw n 0
        let signedMax : ℝ → Ω → ℝ := fun s omega =>
          Shao.upperMax (s • population omega) hn
        ∀ s : ℝ, (s = 1 ∨ s = -1) →
          mu.real {omega : Ω | 0 < rawEnergy omega ∧ signedMax s omega ≤ 0} ≤ C * R ∧
          mu.real {omega : Ω | signedMax s omega < 0} ≤ C * R ∧
          mu.real {omega : Ω | signedMax s omega ≤ 0} ≤ (C + 16) * R ∧
          |mu.real {omega : Ω | 0 ≤ signedMax s omega} - 1| ≤ C * R ∧
          |mu.real {omega : Ω | 0 < signedMax s omega} - 1| ≤ (C + 16) * R := by
  classical
  obtain ⟨C, hC, hHost⟩ := Shao.Probability.finite_second_one_sided_compact_budget
  refine ⟨C, hC, ?_⟩
  intro Ω _ mu rho _ _ n hn X hX hIndep hLaw h2 hmean hsecond
    population rawEnergy sigmaSq scale normalizedLaw R signedMax s hs
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  let m : Shao.Path n → ℝ := fun a => Shao.upperMax (s • a) hn
  let E : Set (Shao.Path n) := {a | 0 < Shao.energy a ∧ m a ≤ 0}
  have : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hsmul : Measurable (fun a : Shao.Path n => s • a) := by
    apply Measurable.of_eval
    intro i
    exact measurable_const.mul (measurable_pi_apply i)
  have hm : Measurable m := (Shao.measurable_upperMax hn).comp hsmul
  have hEm : MeasurableSet E :=
    (measurableSet_lt measurable_const Shao.measurable_energy).inter
      (measurableSet_le hm measurable_const)
  have hscale : scale = Real.sqrt sigmaSq * Real.sqrt (n : ℝ) := by
    dsimp only [scale]
    rw [Real.sqrt_mul (show 0 ≤ (n : ℝ) by positivity)]
    exact mul_comm _ _
  have hPopulation : AEMeasurable population mu := AEMeasurable.of_eval hX
  have hMap : Measure.map population mu = P := by
    change Measure.map (fun omega i => X i omega) mu = _
    rw [hIndep.map_fun_eq_pi_map hX]
    congr 1
    funext i
    simpa only [Measure.map_id] using (hLaw i).map_eq
  have hPair : IdentDistrib population (id : Shao.Path n → Shao.Path n) mu P :=
    ⟨hPopulation, measurable_id.aemeasurable, by simpa only [Measure.map_id] using hMap⟩
  have hTransfer (A : Set (Shao.Path n)) (hA : MeasurableSet A) :
      mu.real {omega : Ω | population omega ∈ A} = P.real A := by
    simpa only [Measure.real, Set.preimage, id_eq, Set.ofPred_mem_eq] using
      congrArg ENNReal.toReal (hPair.measure_mem_eq hA)
  have hPositiveBound (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
      P.real E ≤ 1 - 2 * Shao.standardNormalTail eps + C * R := by
    have hHostAt := hHost rho n hn h2 hmean hsecond eps heps.le heps1 s hs
    change |P.real {a : Shao.Path n |
        eps * Real.sqrt (Shao.energy a) ≤ Shao.maxWithZero (s • a)} -
        2 * Shao.standardNormalTail eps| ≤
      C * Shao.truncationBudget
        (Measure.map (fun z : ℝ => z / (Real.sqrt sigmaSq * Real.sqrt (n : ℝ))) rho) n 0
      at hHostAt
    rw [← hscale] at hHostAt
    have hB : MeasurableSet {a : Shao.Path n |
        eps * Real.sqrt (Shao.energy a) ≤ Shao.maxWithZero (s • a)} := by
      apply measurableSet_le
      · exact measurable_const.mul Shao.measurable_sqrt_energy
      · exact Shao.measurable_maxWithZero.comp hsmul
    have hSubset : E ⊆ {a : Shao.Path n |
        Shao.maxWithZero (s • a) < eps * Real.sqrt (Shao.energy a)} := by
      intro a ha
      change Shao.maxWithZero (s • a) < eps * Real.sqrt (Shao.energy a)
      have hmax : Shao.maxWithZero (s • a) = 0 := by
        rw [Shao.maxWithZero_eq (s • a) hn]
        exact max_eq_left ha.2
      rw [hmax]
      exact mul_pos heps (Real.sqrt_pos.2 ha.1)
    have hComplement : {a : Shao.Path n |
        Shao.maxWithZero (s • a) < eps * Real.sqrt (Shao.energy a)} =
        {a : Shao.Path n |
          eps * Real.sqrt (Shao.energy a) ≤ Shao.maxWithZero (s • a)}ᶜ := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
    calc
      P.real E ≤ P.real {a : Shao.Path n |
          Shao.maxWithZero (s • a) < eps * Real.sqrt (Shao.energy a)} :=
        measureReal_mono hSubset
      _ = 1 - P.real {a : Shao.Path n |
          eps * Real.sqrt (Shao.energy a) ≤ Shao.maxWithZero (s • a)} := by
        rw [hComplement, measureReal_compl hB, probReal_univ]
      _ ≤ 1 - 2 * Shao.standardNormalTail eps + C * R := by
        linarith [(abs_le.mp hHostAt).1]
  have hE : P.real E ≤ C * R := by
    have ht : Tendsto
        (fun j : ℕ => Shao.standardNormalTail (1 / ((j : ℝ) + 1)))
        atTop (𝓝 (Shao.standardNormalTail 0)) :=
      (Shao.standardNormal_derivatives 0).2.continuousAt.tendsto.comp
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Tendsto (fun j : ℕ =>
        1 - 2 * Shao.standardNormalTail (1 / ((j : ℝ) + 1)) + C * R)
        atTop (𝓝 (C * R)) := by
      convert (tendsto_const_nhds.sub (ht.const_mul 2)).add_const (C * R) using 1 <;>
        norm_num [Shao.standardNormalTail_basic.2.1]
    apply ge_of_tendsto' hlim
    intro j
    apply hPositiveBound
    · positivity
    · apply (div_le_one (by positivity : 0 < (j : ℝ) + 1)).2
      linarith [Nat.cast_nonneg (α := ℝ) j]
  have hZero (a : Shao.Path n) (ha : Shao.energy a = 0) : m a = 0 := by
    apply Shao.upperMax_eq_zero_of_energy_eq_zero (s • a) hn
    rw [Shao.energy_smul, ha, mul_zero]
  have hStrict : P.real {a : Shao.Path n | m a < 0} ≤ C * R := by
    apply (measureReal_mono (show {a : Shao.Path n | m a < 0} ⊆ E from ?_)).trans hE
    intro a ha
    change m a < 0 at ha
    have hq : Shao.energy a ≠ 0 := by
      intro hz
      rw [hZero a hz] at ha
      exact (lt_irrefl 0) ha
    exact ⟨lt_of_le_of_ne (Shao.energy_nonneg a) (Ne.symm hq), ha.le⟩
  have hZeroEnergy : P.real {a : Shao.Path n | Shao.energy a = 0} ≤ 16 * R := by
    have hz := SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget
      mu rho n hn X hX hIndep hLaw h2 hsecond
    change mu.real {omega : Ω | population omega ∈
      {a : Shao.Path n | Shao.energy a = 0}} ≤ 16 * R at hz
    rw [hTransfer _ (measurableSet_eq_fun Shao.measurable_energy measurable_const)] at hz
    exact hz
  have hClosed : P.real {a : Shao.Path n | m a ≤ 0} ≤ (C + 16) * R := by
    have hSub : {a : Shao.Path n | m a ≤ 0} ⊆
        E ∪ {a : Shao.Path n | Shao.energy a = 0} := by
      intro a ha
      by_cases hq : Shao.energy a = 0
      · exact Or.inr hq
      · exact Or.inl ⟨lt_of_le_of_ne (Shao.energy_nonneg a) (Ne.symm hq), ha⟩
    calc
      _ ≤ P.real (E ∪ {a : Shao.Path n | Shao.energy a = 0}) := measureReal_mono hSub
      _ ≤ P.real E + P.real {a : Shao.Path n | Shao.energy a = 0} := measureReal_union_le _ _
      _ ≤ C * R + 16 * R := add_le_add hE hZeroEnergy
      _ = (C + 16) * R := by ring
  have hWeakCross : |P.real {a : Shao.Path n | 0 ≤ m a} - 1| ≤ C * R := by
    have hc : {a : Shao.Path n | 0 ≤ m a} = {a : Shao.Path n | m a < 0}ᶜ := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
    rw [hc, measureReal_compl (measurableSet_lt hm measurable_const), probReal_univ]
    have he : (1 - P.real {a : Shao.Path n | m a < 0}) - 1 =
        -P.real {a : Shao.Path n | m a < 0} := by ring
    rw [he, abs_neg, abs_of_nonneg measureReal_nonneg]
    exact hStrict
  have hStrictCross : |P.real {a : Shao.Path n | 0 < m a} - 1| ≤ (C + 16) * R := by
    have hc : {a : Shao.Path n | 0 < m a} = {a : Shao.Path n | m a ≤ 0}ᶜ := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
    rw [hc, measureReal_compl (measurableSet_le hm measurable_const), probReal_univ]
    have he : (1 - P.real {a : Shao.Path n | m a ≤ 0}) - 1 =
        -P.real {a : Shao.Path n | m a ≤ 0} := by ring
    rw [he, abs_neg, abs_of_nonneg measureReal_nonneg]
    exact hClosed
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change mu.real {omega : Ω | population omega ∈ E} ≤ C * R
    rw [hTransfer E hEm]
    exact hE
  · change mu.real {omega : Ω | population omega ∈ {a : Shao.Path n | m a < 0}} ≤ C * R
    rw [hTransfer _ (measurableSet_lt hm measurable_const)]
    exact hStrict
  · change mu.real {omega : Ω | population omega ∈ {a : Shao.Path n | m a ≤ 0}} ≤ (C + 16) * R
    rw [hTransfer _ (measurableSet_le hm measurable_const)]
    exact hClosed
  · change |mu.real {omega : Ω | population omega ∈ {a : Shao.Path n | 0 ≤ m a}} - 1| ≤ C * R
    rw [hTransfer _ (measurableSet_le measurable_const hm)]
    exact hWeakCross
  · change |mu.real {omega : Ω | population omega ∈ {a : Shao.Path n | 0 < m a}} - 1| ≤ (C + 16) * R
    rw [hTransfer _ (measurableSet_lt measurable_const hm)]
    exact hStrictCross

theorem original_absolute_zero_wall_identity
    (n : ℕ) (hn : 0 < n) (a : Shao.Path n) :
    (Shao.absMax a hn ≤ 0 ↔ Shao.energy a = 0) ∧
    (0 < Shao.absMax a hn ↔ 0 < Shao.energy a) := by
  have hzero : Shao.absMax a hn ≤ 0 ↔ Shao.energy a = 0 := by
    constructor
    · intro ha
      apply (Shao.energy_eq_zero_iff a).2
      intro i
      have hi := Shao.abs_coordinate_le_two_mul_of_absMax_le a hn 0 le_rfl ha i
      have habs : |a i| = 0 := le_antisymm (by simpa using hi) (abs_nonneg _)
      exact abs_eq_zero.mp habs
    · intro ha
      exact (Shao.absMax_eq_zero_of_energy_eq_zero a hn ha).le
  refine ⟨hzero, ?_⟩
  constructor
  · intro ha
    apply lt_of_le_of_ne (Shao.energy_nonneg a)
    intro hz
    exact (not_le_of_gt ha) (hzero.2 hz.symm)
  · intro ha
    apply lt_of_le_of_ne (Shao.absMax_nonneg a hn)
    intro hz
    exact (ne_of_gt ha) (hzero.1 hz.symm.le)

end Shao.Probability.SourceOriginalZeroWallBudget
