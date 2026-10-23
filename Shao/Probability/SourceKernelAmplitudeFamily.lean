import Shao.Probability.SourceFourierTestKernel
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Actual marked amplitude family, with a common derivative bound through 32.
The first frozen public statement is proved. The outside marked Fourier
integral statement remains under construction. -/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory
open scoped ContDiff Topology

private noncomputable def markedAmplitude (k : ℕ) (theta r : ℝ) : ℝ :=
  sourceKernelCutoff r / (Real.sqrt r + theta) ^ k

private lemma markedAmplitude_tsupport (k : ℕ) (theta : ℝ) :
    tsupport (markedAmplitude k theta) ⊆ tsupport sourceKernelCutoff := by
  apply closure_mono
  intro r hr
  change sourceKernelCutoff r ≠ 0
  change markedAmplitude k theta r ≠ 0 at hr
  intro hc
  exact hr (by simp [markedAmplitude, hc])

private lemma markedAmplitude_denominator_pos (theta r : ℝ)
    (ht : |theta| ≤ (1 / 16 : ℝ)) (hr : r ∈ tsupport sourceKernelCutoff) :
    0 < Real.sqrt r + theta := by
  have hr' := sourceKernelCutoff_data.2.2.2.2 hr
  have hpos : 0 ≤ r := by linarith [hr'.1]
  have hs : (1 / 4 : ℝ) < Real.sqrt r := by
    have hsq := Real.sq_sqrt hpos
    have hn := Real.sqrt_nonneg r
    nlinarith [hr'.1]
  have ht' := (abs_le.mp ht).1
  linarith

private lemma markedAmplitude_contDiff (k : ℕ) (theta : ℝ)
    (ht : |theta| ≤ (1 / 16 : ℝ)) :
    ContDiff ℝ ∞ (markedAmplitude k theta) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  by_cases hr : r ∈ tsupport sourceKernelCutoff
  · have hr' := sourceKernelCutoff_data.2.2.2.2 hr
    have hne : r ≠ 0 := by linarith [hr'.1]
    have hs : ContDiffAt ℝ ∞ (fun r : ℝ => Real.sqrt r + theta) r :=
      (contDiffAt_id.sqrt hne).add contDiffAt_const
    exact sourceKernelCutoff_data.1.contDiffAt.div (hs.pow k)
      (pow_ne_zero k (ne_of_gt (markedAmplitude_denominator_pos theta r ht hr)))
  · have hc : sourceKernelCutoff =ᶠ[𝓝 r] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp hr
    have ha : markedAmplitude k theta =ᶠ[𝓝 r] 0 := by
      filter_upwards [hc] with s hs
      simp only [Pi.zero_apply] at hs ⊢
      simp [markedAmplitude, hs]
    exact contDiffAt_const.congr_of_eventuallyEq ha

private lemma markedAmplitude_support_interval (k : ℕ) (theta : ℝ) :
    tsupport (markedAmplitude k theta) ⊆ Set.Icc (1 / 16 : ℝ) 4 := by
  intro r hr
  have h := sourceKernelCutoff_data.2.2.2.2 (markedAmplitude_tsupport k theta hr)
  exact ⟨h.1.le, h.2.le⟩

private noncomputable def markedParameterBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩

private noncomputable def markedJointAmplitude (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  markedParameterBump p.1 * sourceKernelCutoff p.2 /
    (Real.sqrt p.2 + p.1) ^ k

private lemma markedParameterBump_abs (theta : ℝ)
    (ht : theta ∈ tsupport (markedParameterBump : ℝ → ℝ)) :
    |theta| ≤ (1 / 8 : ℝ) := by
  rw [markedParameterBump.tsupport_eq] at ht
  simpa [markedParameterBump, Real.dist_eq] using ht

private lemma markedJointAmplitude_contDiff (k : ℕ) :
    ContDiff ℝ ∞ (markedJointAmplitude k) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have hnum : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      markedParameterBump p.1 * sourceKernelCutoff p.2) :=
    (markedParameterBump.contDiff.comp contDiff_fst).mul
      (sourceKernelCutoff_data.1.comp contDiff_snd)
  by_cases ht : p.1 ∈ tsupport (markedParameterBump : ℝ → ℝ)
  · by_cases hr : p.2 ∈ tsupport sourceKernelCutoff
    · have hr' := sourceKernelCutoff_data.2.2.2.2 hr
      have hs : (1 / 4 : ℝ) < Real.sqrt p.2 := by
        have hsq := Real.sq_sqrt (show 0 ≤ p.2 by linarith [hr'.1])
        have hn := Real.sqrt_nonneg p.2
        nlinarith [hr'.1]
      have hp : 0 < Real.sqrt p.2 + p.1 := by
        have h := (abs_le.mp (markedParameterBump_abs p.1 ht)).1
        linarith
      have hd : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Real.sqrt p.2 + p.1) p :=
        (contDiffAt_snd.sqrt (show p.2 ≠ 0 by linarith [hr'.1])).add contDiffAt_fst
      exact hnum.contDiffAt.div (hd.pow k) (pow_ne_zero k (ne_of_gt hp))
    · have he : (fun p : ℝ × ℝ => sourceKernelCutoff p.2) =ᶠ[𝓝 p] 0 :=
        (notMem_tsupport_iff_eventuallyEq.mp hr).comp_tendsto continuous_snd.continuousAt
      have hz : ContDiffAt ℝ ∞ (fun _ : ℝ × ℝ => (0 : ℝ)) p := contDiffAt_const
      apply hz.congr_of_eventuallyEq
      filter_upwards [he] with q hq
      simp only [Pi.zero_apply] at hq ⊢
      simp [markedJointAmplitude, hq]
  · have he : (fun p : ℝ × ℝ => markedParameterBump p.1) =ᶠ[𝓝 p] 0 :=
      (notMem_tsupport_iff_eventuallyEq.mp ht).comp_tendsto continuous_fst.continuousAt
    have hz : ContDiffAt ℝ ∞ (fun _ : ℝ × ℝ => (0 : ℝ)) p := contDiffAt_const
    apply hz.congr_of_eventuallyEq
    filter_upwards [he] with q hq
    simp only [Pi.zero_apply] at hq ⊢
    simp [markedJointAmplitude, hq]

private lemma markedJointAmplitude_compact (k : ℕ) :
    HasCompactSupport (markedJointAmplitude k) := by
  apply IsCompact.of_isClosed_subset
    (s := Set.Icc (-1 / 8 : ℝ) (1 / 8) ×ˢ Set.Icc (1 / 16 : ℝ) 4)
    (isCompact_Icc.prod isCompact_Icc) (isClosed_tsupport _)
  apply closure_minimal
  · intro p hp
    have hn : markedParameterBump p.1 * sourceKernelCutoff p.2 ≠ 0 := by
      intro h
      exact hp (by simp [markedJointAmplitude, h])
    have ht := markedParameterBump_abs p.1 (subset_tsupport _ (left_ne_zero_of_mul hn))
    have hr := sourceKernelCutoff_data.2.2.2.2
      (subset_tsupport _ (right_ne_zero_of_mul hn))
    exact ⟨⟨by linarith [(abs_le.mp ht).1], (abs_le.mp ht).2⟩, hr.1.le, hr.2.le⟩
  · exact isClosed_Icc.prod isClosed_Icc

private lemma markedJointAmplitude_slice (k : ℕ) (theta : ℝ)
    (ht : |theta| ≤ (1 / 16 : ℝ)) :
    (fun r : ℝ => markedJointAmplitude k (theta, r)) = markedAmplitude k theta := by
  have he : markedParameterBump theta = 1 := by
    apply markedParameterBump.one_of_mem_closedBall
    simpa [markedParameterBump, Real.dist_eq] using ht
  funext r
  simp [markedJointAmplitude, markedAmplitude, he]

private lemma markedAmplitude_deriv_eq (k j : ℕ) (theta r : ℝ)
    (ht : |theta| ≤ (1 / 16 : ℝ)) :
    iteratedDeriv j (markedAmplitude k theta) r =
      iteratedFDeriv ℝ j (markedJointAmplitude k) (theta, r)
        (fun _ : Fin j => ((0, 1) : ℝ × ℝ)) := by
  let L : ℝ →L[ℝ] ℝ × ℝ := (0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)
  let H : ℝ × ℝ → ℝ := fun p => markedJointAmplitude k ((theta, 0) + p)
  have hH : ContDiff ℝ ∞ H :=
    (markedJointAmplitude_contDiff k).comp (contDiff_const.add contDiff_id)
  have he : H ∘ L = markedAmplitude k theta := by
    rw [← markedJointAmplitude_slice k theta ht]
    funext s
    simp [H, L]
  rw [← he, iteratedDeriv_eq_iteratedFDeriv,
    L.iteratedFDeriv_comp_right hH r (by simp)]
  simp [H, L, iteratedFDeriv_comp_add_left]

private lemma markedAmplitude_uniform_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ theta : ℝ, |theta| ≤ (1 / 16 : ℝ) →
      ∀ j : ℕ, j ≤ 32 → ∀ r : ℝ,
        |iteratedDeriv j (markedAmplitude k theta) r| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := (markedJointAmplitude_compact k).exists_bound_iteratedFDeriv
    (markedJointAmplitude_contDiff k) 32
  refine ⟨C, hC, fun theta ht j hj r => ?_⟩
  rw [markedAmplitude_deriv_eq k j theta r ht, ← Real.norm_eq_abs]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (markedJointAmplitude k) (theta, r)‖ := by
      simpa using (iteratedFDeriv ℝ j (markedJointAmplitude k) (theta, r)).le_opNorm
        (fun _ : Fin j => ((0, 1) : ℝ × ℝ))
    _ ≤ C := hbound j hj (theta, r)

theorem sourceKernel_marked_amplitude_family :
    ∃ M : ℝ, 0 < M ∧
      ∀ (k : ℕ), (k = 0 ∨ k = 2) →
        ∀ (theta : ℝ), |theta| ≤ (1 / 16 : ℝ) →
          let a : ℝ → ℝ := fun r =>
            sourceKernelCutoff r / (Real.sqrt r + theta) ^ k
          ContDiff ℝ ∞ a ∧
            tsupport a ⊆ Set.Icc (1 / 16 : ℝ) 4 ∧
            ∀ (j : ℕ), j ≤ 32 → ∀ (r : ℝ),
              |iteratedDeriv j a r| ≤ M := by
  obtain ⟨C0, hC0, hb0⟩ := markedAmplitude_uniform_bound 0
  obtain ⟨C2, hC2, hb2⟩ := markedAmplitude_uniform_bound 2
  refine ⟨max C0 C2 + 1, by linarith [le_max_left C0 C2], ?_⟩
  intro k hk theta ht
  refine ⟨markedAmplitude_contDiff k theta ht,
    markedAmplitude_support_interval k theta, ?_⟩
  intro j hj r
  rcases hk with rfl | rfl
  · exact (hb0 theta ht j hj r).trans (by linarith [le_max_left C0 C2])
  · exact (hb2 theta ht j hj r).trans (by linarith [le_max_right C0 C2])

end Shao.Probability
