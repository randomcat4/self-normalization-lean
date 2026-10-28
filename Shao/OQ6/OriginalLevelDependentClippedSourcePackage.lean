import Shao.OQ6.OriginalLevelDependentWeightedSourceCost
import Shao.OQ6.OriginalClippedStatisticMeasurable
import Shao.OQ5.P51.LiteralClippedComparison

set_option autoImplicit false

universe u

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology MeasureTheory symmDiff
open Shao.OQ5.P51

namespace Shao.OQ6.OriginalLevelDependentClippedSourcePackage

noncomputable section

theorem actual_original_level_dependent_clipped_source_package
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond : (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 4 ≤ n)
    (z : ℝ) (hz : 1 ≤ z)
    (hwindow : z ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ))) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
    let rho : ℝ := Real.sqrt v
    let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let N : ℝ := Real.sqrt (n : ℝ)
    let W : (Fin n → Ω) → ℝ := projectionW n g
    let V : (Fin n → Ω) → ℝ := projectionV n g
    let D : (Fin n → Ω) → ℝ := residualStatisticD n r
    let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
    let Ddelete : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
    let Jdelete : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
    let A : (Fin n → Ω) → ℝ := fun ζ => |D ζ|
    let Adelete : (Fin n → Ω) → Fin n → ℝ := fun ζ i => |Ddelete ζ i|
    let B : (Fin n → Ω) → ℝ := studentizerClipBudget n r 512 rho z
    let Bdelete : (Fin n → Ω) → Fin n → ℝ :=
      studentizerClipBudgetDeleted n r 512 rho z
    let d : (Fin n → Ω) → ℝ := centeredDelta n g r
    let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho z
    let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho z
    let s : (Fin n → Ω) → ℝ := fun ζ => Real.sqrt (centeredSq n g r ζ)
    let Tphysical : (Fin n → Ω) → ℝ := fun ζ =>
      if s ζ = 0 then 0 else (W ζ + D ζ) / s ζ
    let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
    let cap : (Fin n → Ω) → Fin n → ℝ := fun ζ i => min |z * ξ0 i ζ| 1
    let S : (Fin n → Ω) → ℝ := fun ζ =>
      ∑ j : Fin n, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)
    let Sdelete : (Fin n → Ω) → Fin n → ℝ := fun ζ i =>
      ∑ j ∈ Finset.univ.erase i, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)
    let fullTest : (Fin n → Ω) → ℝ := fun ζ => z * A ζ + z ^ 2 * B ζ
    let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ζ i =>
      cap ζ i * (|A ζ - Adelete ζ i| + z * |B ζ - Bdelete ζ i|)
    let I : ℝ := ∫ ζ, Real.exp (S ζ) ∂P
    let sourceCost : ℝ :=
      ((∫ ζ, fullTest ζ * Real.exp (S ζ) ∂P) +
        ∑ i : Fin n, ∫ ζ, deletedTest ζ i * Real.exp (Sdelete ζ i) ∂P) / I
    Measurable W ∧ Measurable V ∧ Measurable D ∧ Measurable J ∧
    Measurable A ∧ Measurable B ∧ Measurable d ∧ Measurable e ∧
    Measurable s ∧ Measurable Tclip ∧ Measurable Tphysical ∧
    Measurable fullTest ∧
    MeasurableSet {ζ : Fin n → Ω | V ζ = 0} ∧
    MeasurableSet {ζ : Fin n → Ω | s ζ = 0} ∧
    (∀ ζ : Fin n → Ω,
      (1 / 2 : ℝ) ≤ 1 + e ζ ∧ |e ζ| ≤ B ζ ∧ |e ζ| ≤ |d ζ| ∧
      (0 < V ζ → 0 < V ζ * Real.sqrt (1 + e ζ))) ∧
    (∀ ζ : Fin n → Ω, V ζ = 0 → d ζ = 0 ∧ e ζ = 0 ∧ Tclip ζ = 0) ∧
    (∀ ζ : Fin n → Ω, s ζ = 0 → Tphysical ζ = 0) ∧
    (∀ i : Fin n,
      Measurable (fun ζ : Fin n → Ω => cap ζ i) ∧
      Measurable (fun ζ : Fin n → Ω => Ddelete ζ i) ∧
      Measurable (fun ζ : Fin n → Ω => Jdelete ζ i) ∧
      Measurable (fun ζ : Fin n → Ω => Adelete ζ i) ∧
      Measurable (fun ζ : Fin n → Ω => Bdelete ζ i) ∧
      Measurable (fun ζ : Fin n → Ω => deletedTest ζ i) ∧
      ∃ E : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ,
        Measurable E ∧ ∀ ζ : Fin n → Ω,
          (Ddelete ζ i, Jdelete ζ i, Bdelete ζ i) =
            E (fun j : {j : Fin n // j ≠ i} => ζ j.val)) ∧
    ((1 + rho) * z ≤ N →
      (∀ ζ : Fin n → Ω, ζ ∈ projectionGood n g z →
        -(1 / 2 : ℝ) ≤ d ζ →
        e ζ = d ζ ∧ 0 < V ζ * Real.sqrt (1 + e ζ) ∧
        0 < s ζ ∧ V ζ * Real.sqrt (1 + e ζ) = s ζ ∧
        Tclip ζ = Tphysical ζ) ∧
      {ζ : Fin n → Ω | Tclip ζ ≠ Tphysical ζ} ⊆
        (projectionGood n g z)ᶜ ∪ lowerStudentizerBad n g r z) ∧
    0 < I ∧
    Integrable (fun ζ => fullTest ζ * Real.exp (S ζ)) P ∧
    (∀ i : Fin n,
      Integrable (fun ζ => deletedTest ζ i * Real.exp (Sdelete ζ i)) P) ∧
    0 ≤ sourceCost ∧
    sourceCost ≤
      64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
        (1 + z) ^ 3 / Real.sqrt (n : ℝ)
 := by
  classical
  intro g r v rho P N W V D J Ddelete Jdelete A Adelete B Bdelete d e
    Tclip s Tphysical ξ0 cap S Sdelete fullTest deletedTest I sourceCost
  have hC0 : (0 : ℝ) ≤ 512 := by norm_num
  have hz0 : (0 : ℝ) ≤ z := le_trans (by norm_num : (0 : ℝ) ≤ 1) hz
  have hrho : 0 ≤ rho := Real.sqrt_nonneg v
  have hg : Measurable g :=
    hh.stronglyMeasurable.integral_prod_right'.measurable
  have hsym : ∀ o y : Ω, r o y = r y o := by
    intro o y
    change h o y - g o - g y = h y o - g y - g o
    rw [hhsymm o y]
    ring
  have habs (f : (Fin n → Ω) → ℝ) (hf : Measurable f) :
      Measurable (fun ζ : Fin n → Ω => |f ζ|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hξ0 (i : Fin n) : Measurable (ξ0 i) :=
    (hg.comp (measurable_pi_apply i)).div_const N
  have hshared :
      Measurable W ∧ Measurable V ∧ Measurable D ∧ Measurable J ∧
      Measurable A ∧ Measurable (centeredSq n g r) ∧ Measurable s ∧
      Measurable d ∧ Measurable Tphysical ∧
      MeasurableSet {ζ : Fin n → Ω | V ζ = 0} ∧
      MeasurableSet {ζ : Fin n → Ω | s ζ = 0} ∧
      (∀ i : Fin n,
        Measurable (fun ζ : Fin n → Ω => Ddelete ζ i) ∧
        Measurable (fun ζ : Fin n → Ω => Jdelete ζ i) ∧
        Measurable (fun ζ : Fin n → Ω => Adelete ζ i) ∧
        ∃ E0 : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ,
          Measurable E0 ∧ ∀ ζ : Fin n → Ω,
            (Ddelete ζ i, Jdelete ζ i,
              studentizerClipBudgetDeleted n r 512 rho 1 ζ i) =
                E0 (fun j : {j : Fin n // j ≠ i} => ζ j.val)) := by
    rcases Shao.OQ6.OriginalClippedStatisticMeasurable.actual_normalized_compact_clipped_observables
        μ h hh hh2 hhsymm hcenter hprojectionsecond n hn 0
        (le_refl 0) (by norm_num) 512 hC0 with
      ⟨hW0, hV0, hD0, hJ0, hA0, _hB10, hs20, hs0, hd0, _he10,
        _hTclip10, hTphysical0, hVzero0, hszero0, _hpositive10,
        _hzero10, hdeletes0⟩
    refine ⟨hW0, hV0, hD0, hJ0, hA0, hs20, hs0, hd0, hTphysical0,
      hVzero0, hszero0, ?_⟩
    intro i
    rcases hdeletes0 i with
      ⟨_hcap0, hDdelete0, hJdelete0, hAdelete0, _hBdelete10,
        _hdeletedTest0, E0, hE0, hE0factor⟩
    exact ⟨hDdelete0, hJdelete0, hAdelete0, E0, hE0, hE0factor⟩
  rcases hshared with
    ⟨hW, hV, hD, hJ, hA, _hs2, hs, hd, hTphysical, hVzero, hszero,
      hdeletes⟩
  have hB : Measurable B := by
    change Measurable (fun ζ : Fin n → Ω =>
      512 * (((1 + rho) * z) / Real.sqrt (n : ℝ) +
        J ζ / ((1 + rho) * z * Real.sqrt (n : ℝ))))
    exact measurable_const.mul (measurable_const.add (hJ.div_const _))
  have hclipvalue : Measurable (fun ζ : Fin n → Ω =>
      studentizerClip (B ζ) (d ζ)) := by
    unfold studentizerClip
    exact ((hB.min measurable_const).neg).max (hd.min hB)
  have he : Measurable e := by
    change Measurable (fun ζ : Fin n → Ω =>
      if V ζ = 0 then 0 else studentizerClip (B ζ) (d ζ))
    exact Measurable.ite hVzero measurable_const hclipvalue
  have hTclip : Measurable Tclip := by
    change Measurable (fun ζ : Fin n → Ω =>
      if V ζ = 0 then 0 else
        (W ζ + D ζ) / (V ζ * Real.sqrt (1 + e ζ)))
    exact Measurable.ite hVzero measurable_const
      ((hW.add hD).div (hV.mul (measurable_const.add he).sqrt))
  have hfullTest : Measurable fullTest :=
    (measurable_const.mul hA).add (measurable_const.mul hB)
  have hglobal (ζ : Fin n → Ω) :
      (1 / 2 : ℝ) ≤ 1 + e ζ ∧ |e ζ| ≤ B ζ ∧ |e ζ| ≤ |d ζ| ∧
      (0 < V ζ → 0 < V ζ * Real.sqrt (1 + e ζ)) :=
    clippedCenteredDelta_bounds n g r 512 rho z ζ hC0 hrho hz0
  have hzero (ζ : Fin n → Ω) (hζ : V ζ = 0) :
      d ζ = 0 ∧ e ζ = 0 ∧ Tclip ζ = 0 :=
    clippedCentered_zero n g r 512 rho z ζ hζ
  have hphysicalzero (ζ : Fin n → Ω) (hζ : s ζ = 0) :
      Tphysical ζ = 0 := by
    change (if s ζ = 0 then 0 else (W ζ + D ζ) / s ζ) = 0
    rw [if_pos hζ]
  have hdeletion :
      ∀ i : Fin n,
        Measurable (fun ζ : Fin n → Ω => cap ζ i) ∧
        Measurable (fun ζ : Fin n → Ω => Ddelete ζ i) ∧
        Measurable (fun ζ : Fin n → Ω => Jdelete ζ i) ∧
        Measurable (fun ζ : Fin n → Ω => Adelete ζ i) ∧
        Measurable (fun ζ : Fin n → Ω => Bdelete ζ i) ∧
        Measurable (fun ζ : Fin n → Ω => deletedTest ζ i) ∧
        ∃ E : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ,
          Measurable E ∧ ∀ ζ : Fin n → Ω,
            (Ddelete ζ i, Jdelete ζ i, Bdelete ζ i) =
              E (fun j : {j : Fin n // j ≠ i} => ζ j.val) := by
    intro i
    rcases hdeletes i with ⟨hDdelete, hJdelete, hAdelete, E0, hE0, hE0factor⟩
    let pdel : (Fin n → Ω) → ({j : Fin n // j ≠ i} → Ω) :=
      fun (ζ : Fin n → Ω) (j : {j : Fin n // j ≠ i}) => ζ j.val
    let Dret : ({j : Fin n // j ≠ i} → Ω) → ℝ :=
      fun q : {j : Fin n // j ≠ i} → Ω => (E0 q).1
    let Jret : ({j : Fin n // j ≠ i} → Ω) → ℝ :=
      fun q : {j : Fin n // j ≠ i} → Ω => (E0 q).2.1
    let Bret : ({j : Fin n // j ≠ i} → Ω) → ℝ :=
      fun q : {j : Fin n // j ≠ i} → Ω =>
        512 * (((1 + rho) * z) / Real.sqrt (n : ℝ) +
          Jret q / ((1 + rho) * z * Real.sqrt (n : ℝ)))
    let E : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ :=
      fun q : {j : Fin n // j ≠ i} → Ω => (Dret q, Jret q, Bret q)
    have hDret : Measurable Dret := hE0.fst
    have hJret : Measurable Jret := hE0.snd.fst
    have hBret : Measurable Bret :=
      measurable_const.mul (measurable_const.add (hJret.div_const _))
    have hE : Measurable E := hDret.prodMk (hJret.prodMk hBret)
    have hDfactor (ζ : Fin n → Ω) : Ddelete ζ i = Dret (pdel ζ) :=
      congrArg (fun t : ℝ × ℝ × ℝ => t.1) (hE0factor ζ)
    have hJfactor (ζ : Fin n → Ω) : Jdelete ζ i = Jret (pdel ζ) :=
      congrArg (fun t : ℝ × ℝ × ℝ => t.2.1) (hE0factor ζ)
    have hBfactor (ζ : Fin n → Ω) : Bdelete ζ i = Bret (pdel ζ) := by
      change 512 * (((1 + rho) * z) / Real.sqrt (n : ℝ) +
          Jdelete ζ i / ((1 + rho) * z * Real.sqrt (n : ℝ))) =
        512 * (((1 + rho) * z) / Real.sqrt (n : ℝ) +
          Jret (pdel ζ) / ((1 + rho) * z * Real.sqrt (n : ℝ)))
      rw [hJfactor ζ]
    have hzξ0 : Measurable (fun ζ : Fin n → Ω => z * ξ0 i ζ) :=
      measurable_const.mul (hξ0 i)
    have hcap : Measurable (fun ζ : Fin n → Ω => cap ζ i) :=
      (habs (fun ζ : Fin n → Ω => z * ξ0 i ζ) hzξ0).min measurable_const
    have hBdelete : Measurable (fun ζ : Fin n → Ω => Bdelete ζ i) := by
      change Measurable (fun ζ : Fin n → Ω =>
        512 * (((1 + rho) * z) / Real.sqrt (n : ℝ) +
          Jdelete ζ i / ((1 + rho) * z * Real.sqrt (n : ℝ))))
      exact measurable_const.mul (measurable_const.add (hJdelete.div_const _))
    have hdeletedTest : Measurable (fun ζ : Fin n → Ω => deletedTest ζ i) :=
      hcap.mul
        ((habs (fun ζ : Fin n → Ω => A ζ - Adelete ζ i)
          (hA.sub hAdelete)).add
          (measurable_const.mul
            (habs (fun ζ : Fin n → Ω => B ζ - Bdelete ζ i)
              (hB.sub hBdelete))))
    refine ⟨hcap, hDdelete, hJdelete, hAdelete, hBdelete, hdeletedTest,
      E, hE, ?_⟩
    intro ζ
    change (Ddelete ζ i, Jdelete ζ i, Bdelete ζ i) =
      (Dret (pdel ζ), Jret (pdel ζ), Bret (pdel ζ))
    rw [hDfactor ζ, hJfactor ζ, hBfactor ζ]
  have hgeometry :
      (1 + rho) * z ≤ N →
        (∀ ζ : Fin n → Ω, ζ ∈ projectionGood n g z →
          -(1 / 2 : ℝ) ≤ d ζ →
          e ζ = d ζ ∧ 0 < V ζ * Real.sqrt (1 + e ζ) ∧
          0 < s ζ ∧ V ζ * Real.sqrt (1 + e ζ) = s ζ ∧
          Tclip ζ = Tphysical ζ) ∧
        {ζ : Fin n → Ω | Tclip ζ ≠ Tphysical ζ} ⊆
          (projectionGood n g z)ᶜ ∪ lowerStudentizerBad n g r z := by
    intro hgeom
    refine ⟨?_, ?_⟩
    · intro ζ hGood hLower
      exact literal_clippedCentered_comparison_on_projectionGood n g r rho z ζ
        hn hz hsym hrho hgeom hGood hLower
    · exact literal_clippedCentered_comparison_exception_subset n g r rho z
        hn hz hsym hrho hgeom
  have hcost :
      0 < I ∧
      Integrable (fun ζ => fullTest ζ * Real.exp (S ζ)) P ∧
      (∀ i : Fin n,
        Integrable (fun ζ => deletedTest ζ i * Real.exp (Sdelete ζ i)) P) ∧
      0 ≤ sourceCost ∧
      sourceCost ≤
        64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
          (1 + z) ^ 3 / Real.sqrt (n : ℝ) :=
    Shao.OQ6.OriginalLevelDependentWeightedSourceCost.actual_original_level_dependent_weighted_source_cost
      μ h hh hh2 hhsymm hcenter hprojectionsecond n hn z hz hwindow 512 hC0
  exact ⟨hW, hV, hD, hJ, hA, hB, hd, he, hs, hTclip, hTphysical, hfullTest,
    hVzero, hszero, hglobal, hzero, hphysicalzero, hdeletion, hgeometry, hcost⟩

end

end Shao.OQ6.OriginalLevelDependentClippedSourcePackage
