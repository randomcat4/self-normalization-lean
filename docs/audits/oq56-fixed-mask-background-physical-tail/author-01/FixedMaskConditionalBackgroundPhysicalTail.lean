import Shao.Probability.ConditionalIID
import Shao.OQ5.P41.FiniteBackgroundPhysicalTransport
import Shao.OQ6.OriginalPhysicalClippedTailTransfer
import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false

universe u

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ENNReal
open Shao.OQ5.P41.FiniteBackgroundPhysicalTransport
  (backgroundSample scaledResidual physicalStatistic)
open Shao.OQ5.P41.FiniteBackgroundPerturbation
  (backgroundNumerator backgroundStudentizer)

namespace Shao.OQ5.P41.FixedMaskConditionalBackgroundPhysicalTail

noncomputable section

def fixedMaskEvent {n : ℕ} {Ω : Type u}
    (C : Set Ω) (B : Finset (Fin n)) : Set (Fin n → Ω) :=
  ⋂ i : Fin n, (fun x : Fin n → Ω => x i) ⁻¹'
    (@ite (Set Ω) (i ∈ B) (Classical.propDecidable (i ∈ B)) C Cᶜ)

def backgroundClosedTail {n : ℕ} {Ω : Type u}
    (B : Finset (Fin n)) (g : Ω → ℝ) (r : Ω → Ω → ℝ)
    (z : ℝ) : Set (Fin B.card → Ω) :=
  {y : Fin B.card → Ω |
    z ≤ physicalStatistic B.card g (scaledResidual B r) y}

def originalBackgroundClosedTail {n : ℕ} {Ω : Type u}
    (B : Finset (Fin n)) (g : Ω → ℝ) (r : Ω → Ω → ℝ)
    (z : ℝ) : Set (Fin n → Ω) :=
  {x : Fin n → Ω |
    z ≤ (let s : ℝ :=
      backgroundStudentizer B (fun i : Fin n => g (x i))
        (fun i j : Fin n => r (x i) (x j));
      @ite ℝ (s = 0) (Classical.propDecidable (s = 0)) (0 : ℝ)
        (backgroundNumerator B (fun i : Fin n => g (x i))
          (fun i j : Fin n => r (x i) (x j)) / s))}

theorem measurableSet_fixedMaskEvent {n : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (C : Set Ω) (hC : MeasurableSet C)
    (B : Finset (Fin n)) :
    MeasurableSet (fixedMaskEvent C B)
:= by
  classical
  unfold fixedMaskEvent
  apply MeasurableSet.iInter
  intro i
  have hEval : Measurable (fun x : Fin n → Ω => x i) :=
    measurable_pi_apply i
  by_cases hi : i ∈ B
  · simpa only [if_pos hi] using hEval hC
  · simpa only [if_neg hi] using hEval hC.compl

theorem fixedMask_measure {n : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Set Ω) (hC : MeasurableSet C) (B : Finset (Fin n)) :
    (Measure.pi (fun _ : Fin n => μ)) (fixedMaskEvent C B) =
      (μ C) ^ B.card * (μ Cᶜ) ^ (n - B.card)
:= by
  classical
  have hSet : fixedMaskEvent C B =
      Set.pi Set.univ (fun i : Fin n =>
        @ite (Set Ω) (i ∈ B) (Classical.propDecidable (i ∈ B)) C Cᶜ) := by
    ext x
    simp only [fixedMaskEvent, Set.mem_iInter, Set.mem_preimage,
      Set.mem_pi, Set.mem_univ, true_implies]
  rw [hSet, Measure.pi_pi]
  simp only [apply_ite]
  rw [Finset.prod_ite]
  have hGood : Finset.univ.filter (fun i : Fin n => i ∈ B) = B := by
    ext i
    simp
  have hBad : Finset.univ.filter (fun i : Fin n => i ∉ B) = Bᶜ := by
    ext i
    simp
  simp only [hGood, hBad, Finset.prod_const, Finset.card_compl, Fintype.card_fin]

theorem fixedMask_real {n : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Set Ω) (hC : MeasurableSet C) (B : Finset (Fin n)) :
    (Measure.pi (fun _ : Fin n => μ)).real (fixedMaskEvent C B) =
      (μ.real C) ^ B.card * (1 - μ.real C) ^ (n - B.card)
:= by
  calc
    (Measure.pi (fun _ : Fin n => μ)).real (fixedMaskEvent C B) =
        (μ.real C) ^ B.card * (μ.real Cᶜ) ^ (n - B.card) := by
      simpa only [Measure.real_def, ENNReal.toReal_mul, ENNReal.toReal_pow] using
        congrArg ENNReal.toReal (fixedMask_measure μ C hC B)
    _ = (μ.real C) ^ B.card * (1 - μ.real C) ^ (n - B.card) := by
      rw [measureReal_compl hC, probReal_univ]

theorem fixedMask_real_boundary {n : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Set Ω) (hC : MeasurableSet C) (B : Finset (Fin n)) :
    let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let d : ℝ := μ.real C
    (B = Finset.univ → P.real (fixedMaskEvent C B) = d ^ n) ∧
      (B = ∅ → P.real (fixedMaskEvent C B) = (1 - d) ^ n) ∧
      (d = 0 → P.real (fixedMaskEvent C B) =
        (if B = ∅ then (1 : ℝ) else 0)) ∧
      (d = 1 → P.real (fixedMaskEvent C B) =
        (if B = Finset.univ then (1 : ℝ) else 0))
:= by
  classical
  intro P d
  have hMass : P.real (fixedMaskEvent C B) =
      d ^ B.card * (1 - d) ^ (n - B.card) :=
    fixedMask_real μ C hC B
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hB
    simpa [hB] using hMass
  · intro hB
    simpa [hB] using hMass
  · intro hd
    rw [hMass, hd]
    by_cases hB : B = ∅
    · subst B
      simp
    · have hm : B.card ≠ 0 := by
        intro hz
        exact hB (Finset.card_eq_zero.mp hz)
      simp [hB, hm]
  · intro hd
    rw [hMass, hd]
    by_cases hB : B = Finset.univ
    · subst B
      simp
    · have hComplement : (Bᶜ : Finset (Fin n)) ≠ ∅ := by
        intro hEmpty
        apply hB
        have hDouble := congrArg (fun S : Finset (Fin n) => Sᶜ) hEmpty
        simpa using hDouble
      have hCard : (Bᶜ : Finset (Fin n)).card ≠ 0 := by
        intro hz
        exact hComplement (Finset.card_eq_zero.mp hz)
      have hK : n - B.card ≠ 0 := by
        simpa only [Finset.card_compl, Fintype.card_fin] using hCard
      simp [hB, hK]

theorem measurable_backgroundSample {n : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (B : Finset (Fin n))
    (e : Fin B.card ≃ {i : Fin n // i ∈ B}) :
    Measurable (backgroundSample (Ω := Ω) B e)
:= by
  change Measurable (fun x : Fin n → Ω =>
    fun j : Fin B.card => x ((e j).val))
  apply Measurable.of_eval
  intro j
  exact (measurable_pi_apply ((e j).val) :
    Measurable (fun x : Fin n → Ω => x ((e j).val)))

theorem fixedMask_backgroundSample_cond_map {n : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Set Ω) (hC : MeasurableSet C)
    (B : Finset (Fin n)) (e : Fin B.card ≃ {i : Fin n // i ∈ B})
    (hMask : (Measure.pi (fun _ : Fin n => μ)) (fixedMaskEvent C B) ≠ 0) :
    Measure.map (backgroundSample B e)
      (cond (Measure.pi (fun _ : Fin n => μ)) (fixedMaskEvent C B)) =
      Measure.pi (fun _ : Fin B.card => (μ C)⁻¹ • μ.restrict C)
:= by
  classical
  let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let A : Fin n → Set Ω := fun i : Fin n =>
    @ite (Set Ω) (i ∈ B) (Classical.propDecidable (i ∈ B)) C Cᶜ
  let ρ : Fin n → Measure Ω := fun i : Fin n => cond μ (A i)
  letI : IsProbabilityMeasure P := by
    dsimp only [P]
    infer_instance
  have hA : ∀ i : Fin n, MeasurableSet (A i) := by
    intro i
    dsimp only [A]
    by_cases hi : i ∈ B
    · simpa only [if_pos hi] using hC
    · simpa only [if_neg hi] using hC.compl
  have hX (i : Fin n) : Measurable (Function.eval i : (Fin n → Ω) → Ω) :=
    measurable_pi_apply i
  have hEval (i : Fin n) : Measure.map (Function.eval i) P = μ :=
    (measurePreserving_eval (fun _ : Fin n => μ) i).map_eq
  have hInd : iIndepFun (fun i : Fin n => Function.eval i) P :=
    iIndepFun_pi (μ := fun _ : Fin n => μ)
      (X := fun _ : Fin n => (id : Ω → Ω))
      (fun _ : Fin n => measurable_id.aemeasurable)
  have hFull : cond P (fixedMaskEvent C B) = Measure.pi ρ := by
    have hJoint := Shao.Probability.indep_cond_joint_map_eq_pi
      (μ := P) (X := fun i : Fin n => Function.eval i)
      hX hInd A hA hMask
    change Measure.map (id : (Fin n → Ω) → (Fin n → Ω))
      (cond P (fixedMaskEvent C B)) =
      Measure.pi (fun i : Fin n => cond (Measure.map (Function.eval i) P) (A i))
      at hJoint
    simpa only [Measure.map_id, hEval, ρ] using hJoint
  have hMass (i : Fin n) : μ (A i) ≠ 0 := by
    have hSub : fixedMaskEvent C B ⊆ (Function.eval i) ⁻¹' A i :=
      Set.iInter_subset
        (fun j : Fin n => (Function.eval j) ⁻¹' A j) i
    have hBound : P (fixedMaskEvent C B) ≤ μ (A i) := by
      calc
        P (fixedMaskEvent C B) ≤ P ((Function.eval i) ⁻¹' A i) :=
          measure_mono hSub
        _ = μ (A i) := by
          rw [← Measure.map_apply (hX i) (hA i), hEval i]
    intro hz
    exact hMask (le_antisymm (hBound.trans_eq hz) bot_le)
  letI : ∀ i : Fin n, IsProbabilityMeasure (ρ i) :=
    fun i : Fin n => cond_isProbabilityMeasure (hMass i)
  have hProduct : iIndepFun (fun i : Fin n => Function.eval i) (Measure.pi ρ) :=
    iIndepFun_pi (μ := ρ) (X := fun _ : Fin n => (id : Ω → Ω))
      (fun _ : Fin n => measurable_id.aemeasurable)
  have hSelect :
      iIndepFun (fun j : Fin B.card => Function.eval ((e j).val)) (Measure.pi ρ) :=
    hProduct.precomp (Subtype.val_injective.comp e.injective)
  have hSelectedMap :
      Measure.map (backgroundSample B e) (Measure.pi ρ) =
        Measure.pi (fun j : Fin B.card => ρ ((e j).val)) := by
    change Measure.map (fun x : Fin n → Ω =>
      fun j : Fin B.card => x ((e j).val)) (Measure.pi ρ) = _
    rw [hSelect.map_fun_eq_pi_map
      (fun j : Fin B.card => (hX ((e j).val)).aemeasurable)]
    congr 1
    funext j
    exact (measurePreserving_eval ρ ((e j).val)).map_eq
  change Measure.map (backgroundSample B e)
    (cond P (fixedMaskEvent C B)) = _
  rw [hFull, hSelectedMap]
  congr 1
  funext j
  dsimp only [ρ, A]
  rw [if_pos (e j).property]
  rfl

theorem fixedMask_backgroundSample_restrict_map {n : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Set Ω) (hC : MeasurableSet C)
    (B : Finset (Fin n)) (e : Fin B.card ≃ {i : Fin n // i ∈ B}) :
    Measure.map (backgroundSample B e)
      ((Measure.pi (fun _ : Fin n => μ)).restrict (fixedMaskEvent C B)) =
      ((Measure.pi (fun _ : Fin n => μ)) (fixedMaskEvent C B)) •
        Measure.pi (fun _ : Fin B.card => (μ C)⁻¹ • μ.restrict C)
:= by
  classical
  let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  change Measure.map (backgroundSample B e) (P.restrict (fixedMaskEvent C B)) =
    (P (fixedMaskEvent C B)) •
      Measure.pi (fun _ : Fin B.card => (μ C)⁻¹ • μ.restrict C)
  by_cases hMask : P (fixedMaskEvent C B) = 0
  · have hRestrict : P.restrict (fixedMaskEvent C B) = 0 := by
      apply Measure.ext
      intro A hA
      have hZero : P (A ∩ fixedMaskEvent C B) = 0 :=
        measure_mono_null Set.inter_subset_right hMask
      rw [Measure.restrict_apply hA]
      simpa using hZero
    rw [hRestrict, hMask]
    simp
  · have hFinite : P (fixedMaskEvent C B) ≠ ⊤ := by
      exact measure_ne_top (Measure.pi (fun _ : Fin n => μ)) (fixedMaskEvent C B)
    have hCancel :
        P (fixedMaskEvent C B) * (P (fixedMaskEvent C B))⁻¹ = 1 := by
      rw [mul_comm, ENNReal.inv_mul_cancel hMask hFinite]
    have hRestrict :
        P.restrict (fixedMaskEvent C B) =
          (P (fixedMaskEvent C B)) • cond P (fixedMaskEvent C B) := by
      change P.restrict (fixedMaskEvent C B) =
        (P (fixedMaskEvent C B)) •
          ((P (fixedMaskEvent C B))⁻¹ • P.restrict (fixedMaskEvent C B))
      rw [smul_smul, hCancel, one_smul]
    rw [hRestrict,
      Measure.map_smul _ (measurable_backgroundSample (Ω := Ω) B e).aemeasurable,
      fixedMask_backgroundSample_cond_map μ C hC B e hMask]

theorem measurable_scaledResidual {n : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (B : Finset (Fin n)) (r : Ω → Ω → ℝ)
    (hr : Measurable (Function.uncurry r)) :
    Measurable (Function.uncurry (scaledResidual B r))
:= by
  change Measurable (fun p : Ω × Ω =>
    Shao.OQ5.P41.FiniteBackgroundPerturbation.backgroundScale B * r p.1 p.2)
  have hConstant : Measurable (fun _p : Ω × Ω =>
      Shao.OQ5.P41.FiniteBackgroundPerturbation.backgroundScale B) :=
    measurable_const
  exact hConstant.mul hr

theorem measurable_physicalStatistic {Ω : Type u}
    [MeasurableSpace Ω] (m : ℕ) (g : Ω → ℝ) (r : Ω → Ω → ℝ)
    (hg : Measurable g) (hr : Measurable (Function.uncurry r))
    (hsym : ∀ a b : Ω, r a b = r b a) (hm : 4 ≤ m) :
    Measurable (physicalStatistic m g r)
:= by
  classical
  let f : (Fin m → Ω) → ℝ := fun x : Fin m → Ω =>
    if Real.sqrt (Shao.OQ5.P51.centeredSq m g r x) = 0 then 0 else
      (Shao.OQ5.P51.projectionW m g x + Shao.OQ5.P51.residualStatisticD m r x) /
        Real.sqrt (Shao.OQ5.P51.centeredSq m g r x)
  have hf : Measurable f :=
    (Shao.OQ6.OriginalPhysicalClippedTailTransfer.physical_clipped_globally_measurable
      m g r hg hr 0 0 0).1
  have hEq : physicalStatistic m g r = f := by
    funext x
    rw [Shao.OQ5.P41.FiniteBackgroundPhysicalTransport.physicalStatistic_eq_projection_ratio
      m g r x hsym hm]
    by_cases hs : Real.sqrt (Shao.OQ5.P51.centeredSq m g r x) = 0
    · simp [f, hs]
    · simp only [f, if_neg hs]
  rw [hEq]
  exact hf

theorem measurableSet_backgroundClosedTail {n : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (B : Finset (Fin n))
    (g : Ω → ℝ) (r : Ω → Ω → ℝ)
    (hg : Measurable g) (hr : Measurable (Function.uncurry r))
    (hsym : ∀ a b : Ω, r a b = r b a) (hm : 4 ≤ B.card) (z : ℝ) :
    MeasurableSet (backgroundClosedTail B g r z)
:= by
  have hScaled : ∀ a b : Ω, scaledResidual B r a b = scaledResidual B r b a := by
    intro a b
    dsimp only [scaledResidual]
    rw [hsym a b]
  have hPhysical : Measurable (physicalStatistic B.card g (scaledResidual B r)) :=
    measurable_physicalStatistic B.card g (scaledResidual B r)
      hg (measurable_scaledResidual B r hr) hScaled hm
  change MeasurableSet {y : Fin B.card → Ω |
    z ≤ physicalStatistic B.card g (scaledResidual B r) y}
  exact measurableSet_le
    (measurable_const : Measurable (fun _y : Fin B.card → Ω => z)) hPhysical

theorem originalBackgroundClosedTail_eq_preimage {n : ℕ} {Ω : Type u}
    (B : Finset (Fin n)) (e : Fin B.card ≃ {i : Fin n // i ∈ B})
    (g : Ω → ℝ) (r : Ω → Ω → ℝ)
    (hsym : ∀ a b : Ω, r a b = r b a) (hm : 4 ≤ B.card) (z : ℝ) :
    originalBackgroundClosedTail B g r z =
      backgroundSample B e ⁻¹' backgroundClosedTail B g r z
:= by
  classical
  have hCard : B.card ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_le_card (Finset.subset_univ B))
  have hn : 4 ≤ n := le_trans hm hCard
  ext x
  simp only [originalBackgroundClosedTail, backgroundClosedTail,
    Set.mem_setOf_eq, Set.mem_preimage]
  rw [Shao.OQ5.P41.FiniteBackgroundPhysicalTransport.physicalStatistic_background_guarded
    B e g r x hsym hn hm]

theorem measurableSet_originalBackgroundClosedTail {n : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (B : Finset (Fin n))
    (e : Fin B.card ≃ {i : Fin n // i ∈ B})
    (g : Ω → ℝ) (r : Ω → Ω → ℝ)
    (hg : Measurable g) (hr : Measurable (Function.uncurry r))
    (hsym : ∀ a b : Ω, r a b = r b a) (hm : 4 ≤ B.card) (z : ℝ) :
    MeasurableSet (originalBackgroundClosedTail B g r z)
:= by
  rw [originalBackgroundClosedTail_eq_preimage B e g r hsym hm z]
  exact (measurable_backgroundSample (Ω := Ω) B e)
    (measurableSet_backgroundClosedTail B g r hg hr hsym hm z)

theorem fixedMask_physical_closed_tail_cond {n : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Set Ω) (hC : MeasurableSet C)
    (B : Finset (Fin n)) (e : Fin B.card ≃ {i : Fin n // i ∈ B})
    (g : Ω → ℝ) (r : Ω → Ω → ℝ)
    (hg : Measurable g) (hr : Measurable (Function.uncurry r))
    (hsym : ∀ a b : Ω, r a b = r b a) (hm : 4 ≤ B.card)
    (hMask : (Measure.pi (fun _ : Fin n => μ)) (fixedMaskEvent C B) ≠ 0)
    (z : ℝ) :
    (cond (Measure.pi (fun _ : Fin n => μ)) (fixedMaskEvent C B)).real
      (originalBackgroundClosedTail B g r z) =
      (Measure.pi (fun _ : Fin B.card => (μ C)⁻¹ • μ.restrict C)).real
        (backgroundClosedTail B g r z)
:= by
  have hMap := fixedMask_backgroundSample_cond_map μ C hC B e hMask
  have hTail : MeasurableSet (backgroundClosedTail B g r z) :=
    measurableSet_backgroundClosedTail B g r hg hr hsym hm z
  have hEval := congrArg
    (fun M : Measure (Fin B.card → Ω) => M (backgroundClosedTail B g r z)) hMap
  rw [Measure.map_apply (measurable_backgroundSample (Ω := Ω) B e) hTail,
    ← originalBackgroundClosedTail_eq_preimage B e g r hsym hm z] at hEval
  exact congrArg ENNReal.toReal hEval

theorem fixedMask_physical_closed_tail_intersection {n : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Set Ω) (hC : MeasurableSet C)
    (B : Finset (Fin n)) (e : Fin B.card ≃ {i : Fin n // i ∈ B})
    (g : Ω → ℝ) (r : Ω → Ω → ℝ)
    (hg : Measurable g) (hr : Measurable (Function.uncurry r))
    (hsym : ∀ a b : Ω, r a b = r b a) (hm : 4 ≤ B.card) (z : ℝ) :
    (Measure.pi (fun _ : Fin n => μ)).real
      (originalBackgroundClosedTail B g r z ∩ fixedMaskEvent C B) =
      ((μ.real C) ^ B.card * (1 - μ.real C) ^ (n - B.card)) *
        (Measure.pi (fun _ : Fin B.card => (μ C)⁻¹ • μ.restrict C)).real
          (backgroundClosedTail B g r z)
:= by
  have hMap := fixedMask_backgroundSample_restrict_map μ C hC B e
  have hTail : MeasurableSet (backgroundClosedTail B g r z) :=
    measurableSet_backgroundClosedTail B g r hg hr hsym hm z
  have hOriginal : MeasurableSet (originalBackgroundClosedTail B g r z) :=
    measurableSet_originalBackgroundClosedTail B e g r hg hr hsym hm z
  have hEval := congrArg
    (fun M : Measure (Fin B.card → Ω) => M (backgroundClosedTail B g r z)) hMap
  rw [Measure.map_apply (measurable_backgroundSample (Ω := Ω) B e) hTail,
    ← originalBackgroundClosedTail_eq_preimage B e g r hsym hm z,
    Measure.restrict_apply hOriginal, Measure.smul_apply, smul_eq_mul] at hEval
  have hReal :
      (Measure.pi (fun _ : Fin n => μ)).real
          (originalBackgroundClosedTail B g r z ∩ fixedMaskEvent C B) =
        (Measure.pi (fun _ : Fin n => μ)).real (fixedMaskEvent C B) *
          (Measure.pi (fun _ : Fin B.card => (μ C)⁻¹ • μ.restrict C)).real
            (backgroundClosedTail B g r z) := by
    simpa only [Measure.real_def, ENNReal.toReal_mul] using
      congrArg ENNReal.toReal hEval
  rw [fixedMask_real μ C hC B] at hReal
  exact hReal

theorem cutoff_fixedMask_physical_closed_tail_transport {n : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : Ω → ℝ) (hw : Measurable w) (R : ℝ)
    (B : Finset (Fin n)) (e : Fin B.card ≃ {i : Fin n // i ∈ B})
    (g : Ω → ℝ) (r : Ω → Ω → ℝ)
    (hg : Measurable g) (hr : Measurable (Function.uncurry r))
    (hsym : ∀ a b : Ω, r a b = r b a) (hm : 4 ≤ B.card) (z : ℝ) :
    let C : Set Ω := {o : Ω | w o ≤ R}
    let d : ℝ := μ.real C
    let E : Set (Fin n → Ω) := fixedMaskEvent C B
    let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
    MeasurableSet C ∧
      P.real E = d ^ B.card * (1 - d) ^ (n - B.card) ∧
      (P E ≠ 0 →
        Measure.map (backgroundSample B e) (cond P E) =
          Measure.pi (fun _ : Fin B.card => ν)) ∧
      (P E ≠ 0 →
        (cond P E).real (originalBackgroundClosedTail B g r z) =
          (Measure.pi (fun _ : Fin B.card => ν)).real
            (backgroundClosedTail B g r z)) ∧
      P.real (originalBackgroundClosedTail B g r z ∩ E) =
        (d ^ B.card * (1 - d) ^ (n - B.card)) *
          (Measure.pi (fun _ : Fin B.card => ν)).real
            (backgroundClosedTail B g r z)
:= by
  intro C d E P ν
  have hC : MeasurableSet C :=
    measurableSet_le hw (measurable_const : Measurable (fun _o : Ω => R))
  refine ⟨hC, ?_, ?_, ?_, ?_⟩
  · exact fixedMask_real μ C hC B
  · intro hMask
    exact fixedMask_backgroundSample_cond_map μ C hC B e hMask
  · intro hMask
    exact fixedMask_physical_closed_tail_cond μ C hC B e g r
      hg hr hsym hm hMask z
  · exact fixedMask_physical_closed_tail_intersection μ C hC B e g r
      hg hr hsym hm z

end

end Shao.OQ5.P41.FixedMaskConditionalBackgroundPhysicalTail
