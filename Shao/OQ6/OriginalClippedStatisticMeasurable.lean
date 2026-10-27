import Shao.OQ6.ActualQuadraticTiltMoments
import Shao.OQ5.P51.ClippedDeletionEnvelope

set_option autoImplicit false

universe u

open MeasureTheory
open scoped BigOperators MeasureTheory ENNReal
open Shao.OQ5.P51

namespace Shao.OQ6.OriginalClippedStatisticMeasurable

noncomputable section

theorem actual_normalized_compact_clipped_observables
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 4 ≤ n)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (C0 : ℝ) (hC0 : 0 ≤ C0) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
    let rho : ℝ := Real.sqrt v
    let N : ℝ := Real.sqrt (n : ℝ)
    let W : (Fin n → Ω) → ℝ := projectionW n g
    let V : (Fin n → Ω) → ℝ := projectionV n g
    let D : (Fin n → Ω) → ℝ := residualStatisticD n r
    let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
    let Ddel : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
    let Jdel : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
    let A : (Fin n → Ω) → ℝ := fun ξ => |D ξ|
    let Adel : (Fin n → Ω) → Fin n → ℝ := fun ξ i => |Ddel ξ i|
    let B1 : (Fin n → Ω) → ℝ := studentizerClipBudget n r C0 rho 1
    let B1del : (Fin n → Ω) → Fin n → ℝ := studentizerClipBudgetDeleted n r C0 rho 1
    let s2 : (Fin n → Ω) → ℝ := centeredSq n g r
    let s : (Fin n → Ω) → ℝ := fun ξ => Real.sqrt (s2 ξ)
    let d : (Fin n → Ω) → ℝ := centeredDelta n g r
    let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r C0 rho 1
    let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r C0 rho 1
    let Tactual : (Fin n → Ω) → ℝ := fun ξ => if s ξ = 0 then 0 else (W ξ + D ξ) / s ξ
    let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i => min (|g (ξ i)| / N) (1 / (1 + z))
    let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ξ i => cap ξ i * (|A ξ - Adel ξ i| + z * |B1 ξ - B1del ξ i|)
    Measurable W ∧ Measurable V ∧ Measurable D ∧ Measurable J ∧
      Measurable A ∧ Measurable B1 ∧
      Measurable s2 ∧ Measurable s ∧ Measurable d ∧ Measurable e ∧
      Measurable Tclip ∧ Measurable Tactual ∧
      MeasurableSet {ξ : Fin n → Ω | V ξ = 0} ∧
      MeasurableSet {ξ : Fin n → Ω | s ξ = 0} ∧
      (∀ ξ : Fin n → Ω, (1 / 2 : ℝ) ≤ 1 + e ξ) ∧
      (∀ ξ : Fin n → Ω, V ξ = 0 →
        d ξ = 0 ∧ e ξ = 0 ∧ Tclip ξ = 0) ∧
      (∀ i : Fin n,
        Measurable (fun ξ : Fin n → Ω => cap ξ i) ∧
        Measurable (fun ξ : Fin n → Ω => Ddel ξ i) ∧
        Measurable (fun ξ : Fin n → Ω => Jdel ξ i) ∧
        Measurable (fun ξ : Fin n → Ω => Adel ξ i) ∧
        Measurable (fun ξ : Fin n → Ω => B1del ξ i) ∧
        Measurable (fun ξ : Fin n → Ω => deletedTest ξ i) ∧
        ∃ E : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ,
          Measurable E ∧
          ∀ ξ : Fin n → Ω,
            (Ddel ξ i, Jdel ξ i, B1del ξ i) =
              E (fun j : {j : Fin n // j ≠ i} => ξ j.val))
:= by
  classical
  intro g r v rho N W V D J Ddel Jdel A Adel B1 B1del s2 s d e
    Tclip Tactual cap deletedTest
  have hn3 : 3 ≤ n := Nat.le_trans (by norm_num) hn
  have hwindow0 :
      (0 : ℝ) ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ)) :=
    div_nonneg (Real.sqrt_nonneg (n : ℝ))
      (mul_nonneg (by norm_num) (le_of_lt (Real.exp_pos (1 / 2 : ℝ))))
  have hmodel :=
    Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
      μ h hh hh2 hhsymm hcenter hprojectionsecond n hn3 0 (le_refl 0) hwindow0
  have hg : Measurable g := hmodel.1
  have hr : Measurable (fun t : Ω × Ω => r t.1 t.2) :=
    hmodel.2.2.2.2.1
  have habs (f : (Fin n → Ω) → ℝ) (hf : Measurable f) :
      Measurable (fun ξ : Fin n → Ω => |f ξ|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hgcoord (i : Fin n) :
      Measurable (fun ξ : Fin n → Ω => g (ξ i)) :=
    hg.comp (measurable_pi_apply i)
  have hrcoord (i j : Fin n) :
      Measurable (fun ξ : Fin n → Ω => r (ξ i) (ξ j)) := by
    have hpair : Measurable (fun ξ : Fin n → Ω => (ξ i, ξ j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    exact hr.comp hpair
  have hW : Measurable W := by
    change Measurable (fun ξ : Fin n → Ω =>
      (∑ i : Fin n, g (ξ i)) / Real.sqrt (n : ℝ))
    exact (Finset.measurable_sum Finset.univ
      (fun (i : Fin n) (_hi : i ∈ Finset.univ) => hgcoord i)).div_const _
  have hgsquares :
      Measurable (fun ξ : Fin n → Ω => ∑ i : Fin n, g (ξ i) ^ 2) := by
    apply Finset.measurable_sum Finset.univ
    intro i _hi
    simpa only [pow_two, Pi.mul_def] using (hgcoord i).mul (hgcoord i)
  have hV : Measurable V := by
    change Measurable (fun ξ : Fin n → Ω =>
      Real.sqrt ((∑ i : Fin n, g (ξ i) ^ 2) / (n : ℝ)))
    exact (hgsquares.div_const (n : ℝ)).sqrt
  have hupper : Measurable (fun ξ : Fin n → Ω =>
      Shao.OQ6.CanonicalDoubleGhostScalarMoments.originalUpper n r ξ) := by
    unfold Shao.OQ6.CanonicalDoubleGhostScalarMoments.originalUpper
    apply Finset.measurable_sum Finset.univ
    intro i _hi
    apply Finset.measurable_sum Finset.univ
    intro j _hj
    by_cases hij : i < j
    · simpa only [if_pos hij] using hrcoord i j
    · simpa only [if_neg hij] using
        (measurable_const : Measurable (fun _ξ : Fin n → Ω => (0 : ℝ)))
  have hD : Measurable D := by
    change Measurable (fun ξ : Fin n → Ω =>
      Shao.OQ6.CanonicalDoubleGhostScalarMoments.originalUpper n r ξ /
        (Real.sqrt (n : ℝ) * ((n : ℝ) - 1)))
    exact hupper.div_const _
  have hrrow (i : Fin n) : Measurable (fun ξ : Fin n → Ω =>
      Shao.OQ6.ResidualDeletion.rowSum
        (fun j k : Fin n => r (ξ j) (ξ k)) i) := by
    unfold Shao.OQ6.ResidualDeletion.rowSum
    exact Finset.measurable_sum (Finset.univ.erase i)
      (fun (j : Fin n) (_hj : j ∈ Finset.univ.erase i) => hrcoord i j)
  have hrowsquares : Measurable (fun ξ : Fin n → Ω =>
      ∑ i : Fin n, (Shao.OQ6.ResidualDeletion.rowSum
        (fun j k : Fin n => r (ξ j) (ξ k)) i) ^ 2) := by
    apply Finset.measurable_sum Finset.univ
    intro i _hi
    simpa only [pow_two, Pi.mul_def] using (hrrow i).mul (hrrow i)
  have hJ : Measurable J := by
    have hJfun :
        J = (fun ξ : Fin n → Ω =>
          (∑ i : Fin n, (Shao.OQ6.ResidualDeletion.rowSum
            (fun j k : Fin n => r (ξ j) (ξ k)) i) ^ 2) /
              ((n : ℝ) - 2) ^ 2) := by
      funext ξ
      exact residualEnergyJ_eq_rowSqSum n r ξ
    rw [hJfun]
    exact hrowsquares.div_const (((n : ℝ) - 2) ^ 2)
  have hA : Measurable A := habs D hD
  have hB1 : Measurable B1 := by
    change Measurable (fun ξ : Fin n → Ω =>
      C0 * (((1 + rho) * 1) / Real.sqrt (n : ℝ) +
        J ξ / ((1 + rho) * 1 * Real.sqrt (n : ℝ))))
    exact measurable_const.mul
      (measurable_const.add (hJ.div_const _))
  have hsample (i j : Fin n) : Measurable (fun ξ : Fin n → Ω =>
      sampledKernel n g r ξ i j) := by
    exact ((hgcoord i).add (hgcoord j)).add (hrcoord i j)
  have hrowmean (i : Fin n) : Measurable (fun ξ : Fin n → Ω =>
      Shao.OQ6.FiniteRows.rowMean (sampledKernel n g r ξ) i) := by
    unfold Shao.OQ6.FiniteRows.rowMean
    exact measurable_const.mul
      (Finset.measurable_sum (Finset.univ.erase i)
        (fun (j : Fin n) (_hj : j ∈ Finset.univ.erase i) => hsample i j))
  have hustat : Measurable (fun ξ : Fin n → Ω =>
      Shao.OQ6.FiniteRows.uStatistic (sampledKernel n g r ξ)) := by
    unfold Shao.OQ6.FiniteRows.uStatistic Shao.OQ5.P35.unorderedPairSum
    apply Measurable.mul measurable_const
    apply Finset.measurable_sum Finset.univ
    intro i _hi
    apply Finset.measurable_sum Finset.univ
    intro j _hj
    by_cases hij : i < j
    · simpa only [if_pos hij] using hsample i j
    · simpa only [if_neg hij] using
        (measurable_const : Measurable (fun _ξ : Fin n → Ω => (0 : ℝ)))
  have hcenteredrowsquares : Measurable (fun ξ : Fin n → Ω =>
      ∑ i : Fin n,
        (Shao.OQ6.FiniteRows.rowMean (sampledKernel n g r ξ) i -
          Shao.OQ6.FiniteRows.uStatistic (sampledKernel n g r ξ)) ^ 2) := by
    apply Finset.measurable_sum Finset.univ
    intro i _hi
    simpa only [pow_two, Pi.mul_def, Pi.sub_def] using
      ((hrowmean i).sub hustat).mul ((hrowmean i).sub hustat)
  have hs2 : Measurable s2 := by
    change Measurable (fun ξ : Fin n → Ω =>
      ((4 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2) *
        ∑ i : Fin n,
          (Shao.OQ6.FiniteRows.rowMean (sampledKernel n g r ξ) i -
            Shao.OQ6.FiniteRows.uStatistic (sampledKernel n g r ξ)) ^ 2) / 4)
    exact (measurable_const.mul hcenteredrowsquares).div_const 4
  have hs : Measurable s := hs2.sqrt
  have hVzero : MeasurableSet {ξ : Fin n → Ω | V ξ = 0} :=
    measurableSet_eq_fun hV measurable_const
  have hszero : MeasurableSet {ξ : Fin n → Ω | s ξ = 0} :=
    measurableSet_eq_fun hs measurable_const
  have hV2 : Measurable (fun ξ : Fin n → Ω => V ξ ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using hV.mul hV
  have hd : Measurable d := by
    change Measurable (fun ξ : Fin n → Ω =>
      if V ξ = 0 then 0 else s2 ξ / V ξ ^ 2 - 1)
    exact Measurable.ite hVzero measurable_const
      ((hs2.div hV2).sub measurable_const)
  have hclipvalue : Measurable (fun ξ : Fin n → Ω =>
      studentizerClip (B1 ξ) (d ξ)) := by
    unfold studentizerClip
    exact ((hB1.min measurable_const).neg).max (hd.min hB1)
  have he : Measurable e := by
    change Measurable (fun ξ : Fin n → Ω =>
      if V ξ = 0 then 0 else studentizerClip (B1 ξ) (d ξ))
    exact Measurable.ite hVzero measurable_const hclipvalue
  have hTclip : Measurable Tclip := by
    change Measurable (fun ξ : Fin n → Ω =>
      if V ξ = 0 then 0 else
        (W ξ + D ξ) / (V ξ * Real.sqrt (1 + e ξ)))
    exact Measurable.ite hVzero measurable_const
      ((hW.add hD).div (hV.mul (measurable_const.add he).sqrt))
  have hTactual : Measurable Tactual := by
    exact Measurable.ite hszero measurable_const ((hW.add hD).div hs)
  have hpositive (ξ : Fin n → Ω) : (1 / 2 : ℝ) ≤ 1 + e ξ := by
    exact (clippedCenteredDelta_bounds n g r C0 rho 1 ξ
      hC0 (Real.sqrt_nonneg v) (by norm_num)).1
  have hzero (ξ : Fin n → Ω) (hξ : V ξ = 0) :
      d ξ = 0 ∧ e ξ = 0 ∧ Tclip ξ = 0 := by
    exact clippedCentered_zero n g r C0 rho 1 ξ hξ
  refine ⟨hW, hV, hD, hJ, hA, hB1, hs2, hs, hd, he, hTclip,
    hTactual, hVzero, hszero, hpositive, hzero, ?_⟩
  intro i
  have hcap : Measurable (fun ξ : Fin n → Ω => cap ξ i) := by
    exact ((habs (fun ξ : Fin n → Ω => g (ξ i)) (hgcoord i)).div_const N).min
      measurable_const
  obtain ⟨F, hF, hFeq⟩ :
      ∃ F : ({j : Fin n // j ≠ i} → Ω) → ℝ,
        Measurable F ∧ ∀ ξ : Fin n → Ω,
          Shao.OQ5.P35.unorderedPairSum
            (Shao.OQ6.ResidualDeletion.eraseIncident
              (fun j k : Fin n => r (ξ j) (ξ k)) i) =
            F (fun j : {j : Fin n // j ≠ i} => ξ j.val) :=
    Shao.OQ6.ResidualDeletion.erasedSamplePairSum_measurable_factorization r hr i
  obtain ⟨Lrow, hLrow, hLroweq⟩ :
      ∃ Lrow : ({j : Fin n // j ≠ i} → Ω) → ℝ,
        Measurable Lrow ∧ ∀ ξ : Fin n → Ω,
          (∑ j : Fin n,
            (Shao.OQ6.ResidualDeletion.rowSum
              (Shao.OQ6.ResidualDeletion.eraseIncident
                (fun k l : Fin n => r (ξ k) (ξ l)) i) j) ^ 2) =
            Lrow (fun j : {j : Fin n // j ≠ i} => ξ j.val) :=
    Shao.OQ6.ResidualDeletion.erasedSampleRowSqSum_measurable_factorization r hr i
  let pdel : (Fin n → Ω) → ({j : Fin n // j ≠ i} → Ω) :=
    fun (ξ : Fin n → Ω) (j : {j : Fin n // j ≠ i}) => ξ j.val
  let Dret : ({j : Fin n // j ≠ i} → Ω) → ℝ :=
    fun q : {j : Fin n // j ≠ i} → Ω =>
      F q / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
  let Jret : ({j : Fin n // j ≠ i} → Ω) → ℝ :=
    fun q : {j : Fin n // j ≠ i} → Ω => Lrow q / ((n : ℝ) - 2) ^ 2
  let Bret : ({j : Fin n // j ≠ i} → Ω) → ℝ :=
    fun q : {j : Fin n // j ≠ i} → Ω =>
      C0 * (((1 + rho) * 1) / Real.sqrt (n : ℝ) +
        Jret q / ((1 + rho) * 1 * Real.sqrt (n : ℝ)))
  let E : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ :=
    fun q : {j : Fin n // j ≠ i} → Ω => (Dret q, Jret q, Bret q)
  have hpdel : Measurable pdel :=
    measurable_pi_iff.2
      (fun j : {j : Fin n // j ≠ i} => measurable_pi_apply j.val)
  have hDret : Measurable Dret := hF.div_const _
  have hJret : Measurable Jret := hLrow.div_const _
  have hBret : Measurable Bret :=
    measurable_const.mul (measurable_const.add (hJret.div_const _))
  have hE : Measurable E := hDret.prodMk (hJret.prodMk hBret)
  have hDdeleq (ξ : Fin n → Ω) : Ddel ξ i = Dret (pdel ξ) := by
    change Shao.OQ5.P35.unorderedPairSum
        (Shao.OQ6.ResidualDeletion.eraseIncident
          (fun j k : Fin n => r (ξ j) (ξ k)) i) /
        (Real.sqrt (n : ℝ) * ((n : ℝ) - 1)) =
      F (fun j : {j : Fin n // j ≠ i} => ξ j.val) /
        (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    rw [hFeq ξ]
  have hJdeleq (ξ : Fin n → Ω) : Jdel ξ i = Jret (pdel ξ) := by
    change (∑ j : Fin n,
        (Shao.OQ6.ResidualDeletion.rowSum
          (Shao.OQ6.ResidualDeletion.eraseIncident
            (fun k l : Fin n => r (ξ k) (ξ l)) i) j) ^ 2) /
        ((n : ℝ) - 2) ^ 2 =
      Lrow (fun j : {j : Fin n // j ≠ i} => ξ j.val) / ((n : ℝ) - 2) ^ 2
    rw [hLroweq ξ]
  have hB1deleq (ξ : Fin n → Ω) : B1del ξ i = Bret (pdel ξ) := by
    change C0 * (((1 + rho) * 1) / Real.sqrt (n : ℝ) +
        Jdel ξ i / ((1 + rho) * 1 * Real.sqrt (n : ℝ))) =
      C0 * (((1 + rho) * 1) / Real.sqrt (n : ℝ) +
        Jret (pdel ξ) / ((1 + rho) * 1 * Real.sqrt (n : ℝ)))
    rw [hJdeleq ξ]
  have hDdel : Measurable (fun ξ : Fin n → Ω => Ddel ξ i) := by
    rw [show (fun ξ : Fin n → Ω => Ddel ξ i) =
        (fun ξ : Fin n → Ω => Dret (pdel ξ)) from
      funext (fun ξ : Fin n → Ω => hDdeleq ξ)]
    exact hDret.comp hpdel
  have hJdel : Measurable (fun ξ : Fin n → Ω => Jdel ξ i) := by
    rw [show (fun ξ : Fin n → Ω => Jdel ξ i) =
        (fun ξ : Fin n → Ω => Jret (pdel ξ)) from
      funext (fun ξ : Fin n → Ω => hJdeleq ξ)]
    exact hJret.comp hpdel
  have hAdel : Measurable (fun ξ : Fin n → Ω => Adel ξ i) :=
    habs (fun ξ : Fin n → Ω => Ddel ξ i) hDdel
  have hB1del : Measurable (fun ξ : Fin n → Ω => B1del ξ i) := by
    rw [show (fun ξ : Fin n → Ω => B1del ξ i) =
        (fun ξ : Fin n → Ω => Bret (pdel ξ)) from
      funext (fun ξ : Fin n → Ω => hB1deleq ξ)]
    exact hBret.comp hpdel
  have hdeletedTest : Measurable (fun ξ : Fin n → Ω => deletedTest ξ i) := by
    exact hcap.mul
      ((habs (fun ξ : Fin n → Ω => A ξ - Adel ξ i) (hA.sub hAdel)).add
        (measurable_const.mul
          (habs (fun ξ : Fin n → Ω => B1 ξ - B1del ξ i) (hB1.sub hB1del))))
  refine ⟨hcap, hDdel, hJdel, hAdel, hB1del, hdeletedTest, E, hE, ?_⟩
  intro ξ
  change (Ddel ξ i, Jdel ξ i, B1del ξ i) =
    (Dret (pdel ξ), Jret (pdel ξ), Bret (pdel ξ))
  rw [hDdeleq ξ, hJdeleq ξ, hB1deleq ξ]

end

end Shao.OQ6.OriginalClippedStatisticMeasurable
