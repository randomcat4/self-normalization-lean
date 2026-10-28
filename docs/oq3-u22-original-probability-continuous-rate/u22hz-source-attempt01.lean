import Shao.OQ3.ActualGaussianKernelComparison
import Shao.OQ3.ParabolaHalfOpenGridPartition
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff BigOperators
noncomputable section

set_option maxHeartbeats 2000000 in
theorem actual_mean_chart_gaussian_grid_integral_comparison
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (he : (e : (ℝ × ℝ) → (ℝ × ℝ)) = fun p =>
      (∫ x : ℝ, x ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2),
        ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)))
    (hsource : e.source ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (V : Set (ℝ × ℝ)) (hCompact : IsCompact V) (hTarget : V ⊆ e.target)
    (hPositive : ∀ y ∈ V, 0 < (parabolaCovariance
      (mu.tilted (fun x => (e.symm y).1 * x + (e.symm y).2 * x ^ 2))).det) :
    let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun y =>
      parabolaCovariance (nu (e.symm y))
    let K : (ℝ × ℝ) → ℝ := fun p => Real.log
      (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
    let J : (ℝ × ℝ) → ℝ := fun y =>
      (e.symm y).1 * y.1 + (e.symm y).2 * y.2 - K (e.symm y)
    let A : (ℝ × ℝ) → ℝ := fun y => (Real.sqrt (D y).det)⁻¹
    let Q : (ℝ × ℝ) → (ℝ × ℝ) → ℝ := fun y v =>
      (D y 1 1 * v.1 ^ 2 - 2 * D y 0 1 * v.1 * v.2 + D y 0 0 * v.2 ^ 2) /
        (D y).det
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let cell : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
        (Set.Ioc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
          Set.Ioc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))) ∩ V
      ∀ Kcells : Finset (ℤ × ℤ),
        (∀ k : ℤ × ℤ, k ∈ Kcells ↔ (cell k).Nonempty) →
      ∀ y : Kcells → V,
        (∀ k : Kcells, (y k : ℝ × ℝ) ∈
          Set.Icc ((k.val.1 : ℝ) / (n : ℝ)) (((k.val.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
          Set.Icc ((k.val.2 : ℝ) / (n : ℝ)) (((k.val.2 : ℝ) + 1) / (n : ℝ))) →
      ∀ J0 : ℝ,
        let T : (ℝ × ℝ) → ℝ := fun w => A w * Real.exp (-(n : ℝ) * (J w - J0))
        let g : Kcells → (ℝ × ℝ) → ℝ := fun k w =>
          A (y k) * Real.exp (-(n : ℝ) * (J (y k) +
            ((e.symm (y k)).1 * (w - y k).1 + (e.symm (y k)).2 * (w - y k).2) +
              Q (y k) (w - y k) / 2 - J0))
        let G : ℝ := ((n : ℝ) / (2 * Real.pi)) *
          ∑ k : Kcells, ∫ w : ℝ × ℝ in cell k, g k w
        let L : ℝ := ((n : ℝ) / (2 * Real.pi)) * ∫ w : ℝ × ℝ in V, T w
        IntegrableOn T V ∧ (∀ k : Kcells, IntegrableOn (g k) (cell k)) ∧
          0 ≤ L ∧ |G - L| ≤ (C / (n : ℝ)) * L := by
  classical
  intro nu D K J A Q
  obtain ⟨C, hC, N, hN, hCompare⟩ :=
    actual_mean_chart_uniform_gaussian_kernel_comparison mu e he hsource
      V hCompact hTarget hPositive
  have hSmooth (w : ℝ × ℝ) (hw : w ∈ V) : ContinuousAt J w ∧ ContinuousAt A w := by
    obtain ⟨_, _, _, _, hJ, _, _, _, hA, _⟩ :=
      actual_mean_chart_rate_covariance_derivatives mu e he hsource w (hTarget hw) (hPositive w hw)
    exact ⟨hJ.continuousAt, hA.continuousAt⟩
  have hContJ : ContinuousOn J V := fun w hw => (hSmooth w hw).1.continuousWithinAt
  have hContA : ContinuousOn A V := fun w hw => (hSmooth w hw).2.continuousWithinAt
  refine ⟨C, hC, N, hN, ?_⟩
  intro n hn cell Kcells hK y hRect J0 T g G L
  have hn1 : 1 ≤ n := hN.trans hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hCell (k : ℤ × ℤ) : MeasurableSet (cell k) :=
    (measurableSet_Ioc.prod measurableSet_Ioc).inter hCompact.measurableSet
  have hContT : ContinuousOn T V :=
    hContA.mul ((continuousOn_const.mul (hContJ.sub continuousOn_const)).exp)
  have hTV : IntegrableOn T V := hContT.integrableOn_compact hCompact
  have hTc (k : Kcells) : IntegrableOn T (cell k) :=
    hTV.mono_set (fun _ hw => hw.2)
  have hgc (k : Kcells) : IntegrableOn (g k) (cell k) := by
    have hcont : Continuous (g k) := by dsimp only [g, Q]; fun_prop
    exact (hcont.continuousOn.integrableOn_compact hCompact).mono_set (fun _ hw => hw.2)
  have hCover : (⋃ k : Kcells, cell k) = V := by
    apply Set.Subset.antisymm
    · intro w hw
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hw
      exact hk.2
    · intro w hw
      let k : ℤ × ℤ := (Int.ceil ((n : ℝ) * w.1) - 1, Int.ceil ((n : ℝ) * w.2) - 1)
      have hwk : w ∈ cell k :=
        ⟨⟨(real_ioc_grid_index_iff n hn1 w.1 k.1).mpr rfl,
          (real_ioc_grid_index_iff n hn1 w.2 k.2).mpr rfl⟩, hw⟩
      exact Set.mem_iUnion.mpr ⟨⟨k, (hK k).2 ⟨w, hwk⟩⟩, hwk⟩
  have hDisjoint : Pairwise (fun i j : Kcells => Disjoint (cell i) (cell j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro w hi hj
    apply hij
    apply Subtype.ext
    apply Prod.ext
    · exact ((real_ioc_grid_index_iff n hn1 w.1 i.val.1).mp hi.1.1).trans
        ((real_ioc_grid_index_iff n hn1 w.1 j.val.1).mp hj.1.1).symm
    · exact ((real_ioc_grid_index_iff n hn1 w.2 i.val.2).mp hi.1.2).trans
        ((real_ioc_grid_index_iff n hn1 w.2 j.val.2).mp hj.1.2).symm
  have hPartition : (∫ w : ℝ × ℝ in V, T w) =
      ∑ k : Kcells, ∫ w : ℝ × ℝ in cell k, T w := by
    rw [← hCover]
    exact integral_iUnion_fintype (fun k => hCell k) hDisjoint hTc
  have hMesh (k : Kcells) (w : ℝ × ℝ) (hw : w ∈ cell k) :
      ‖w - y k‖ ≤ 1 / (n : ℝ) := by
    have hWidth (i : ℤ) : ((i : ℝ) + 1) / (n : ℝ) - (i : ℝ) / (n : ℝ) =
        1 / (n : ℝ) := by ring
    have h1 : |w.1 - (y k : ℝ × ℝ).1| ≤ 1 / (n : ℝ) := by
      apply abs_le.mpr
      constructor <;> linarith [(hRect k).1.1, (hRect k).1.2, hw.1.1.1.le, hw.1.1.2,
        hWidth k.val.1]
    have h2 : |w.2 - (y k : ℝ × ℝ).2| ≤ 1 / (n : ℝ) := by
      apply abs_le.mpr
      constructor <;> linarith [(hRect k).2.1, (hRect k).2.2, hw.1.2.1.le, hw.1.2.2,
        hWidth k.val.2]
    rw [Prod.norm_def]
    change max |w.1 - (y k : ℝ × ℝ).1| |w.2 - (y k : ℝ × ℝ).2| ≤ 1 / (n : ℝ)
    exact max_le h1 h2
  have hPoint (k : Kcells) (w : ℝ × ℝ) (hw : w ∈ cell k) :
      |g k w - T w| ≤ (C / (n : ℝ)) * T w :=
    hCompare n hn (y k) (y k).property w hw.2 (hMesh k w hw) J0
  have hCellError (k : Kcells) :
      |(∫ w : ℝ × ℝ in cell k, g k w) - (∫ w : ℝ × ℝ in cell k, T w)| ≤
        (C / (n : ℝ)) * ∫ w : ℝ × ℝ in cell k, T w := by
    rw [← integral_sub (hgc k) (hTc k)]
    calc
      |∫ w : ℝ × ℝ in cell k, g k w - T w|
          ≤ ∫ w : ℝ × ℝ in cell k, |g k w - T w| := abs_integral_le_integral_abs
      _ ≤ ∫ w : ℝ × ℝ in cell k, (C / (n : ℝ)) * T w := by
        apply integral_mono_ae ((hgc k).sub (hTc k)).abs ((hTc k).const_mul _)
        filter_upwards [ae_restrict_mem (hCell k)] with w hw
        exact hPoint k w hw
      _ = _ := integral_const_mul _ _
  have hSum : |(∑ k : Kcells, ∫ w : ℝ × ℝ in cell k, g k w) -
      (∫ w : ℝ × ℝ in V, T w)| ≤ (C / (n : ℝ)) * ∫ w : ℝ × ℝ in V, T w := by
    rw [hPartition, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ k : Kcells, |(∫ w : ℝ × ℝ in cell k, g k w) -
          (∫ w : ℝ × ℝ in cell k, T w)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Kcells, (C / (n : ℝ)) * ∫ w : ℝ × ℝ in cell k, T w :=
        Finset.sum_le_sum (fun k _ => hCellError k)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hScale : 0 ≤ (n : ℝ) / (2 * Real.pi) :=
    div_nonneg hnpos.le (by positivity)
  have hTnonneg (w : ℝ × ℝ) : 0 ≤ T w := by dsimp only [T, A]; positivity
  refine ⟨hTV, hgc, mul_nonneg hScale (integral_nonneg hTnonneg), ?_⟩
  have hGL : G - L = ((n : ℝ) / (2 * Real.pi)) *
      ((∑ k : Kcells, ∫ w : ℝ × ℝ in cell k, g k w) - ∫ w : ℝ × ℝ in V, T w) := by
    dsimp only [G, L]
    ring
  rw [hGL, abs_mul, abs_of_nonneg hScale]
  calc
    _ ≤ ((n : ℝ) / (2 * Real.pi)) *
        ((C / (n : ℝ)) * ∫ w : ℝ × ℝ in V, T w) :=
      mul_le_mul_of_nonneg_left hSum hScale
    _ = (C / (n : ℝ)) * L := by dsimp only [L]; ring

end
end Shao.OQ3
