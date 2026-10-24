import Shao.C2.SineStoppedWallBound
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section
namespace Shao.C2.SineFirstLossLimit
open MeasureTheory Set Filter
open scoped NNReal Topology BigOperators
open Shao.C2.IntervalSineSeries Shao.C2.SineStoppedWallBound

private theorem first_loss_sum_abs_le (P : ℕ → Prop)
    (hP : ∀ i j : ℕ, i ≤ j → P j → P i) (N : ℕ) (F : ℕ → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ k ∈ Finset.range N, P k ∧ ¬ P (k + 1) → |F k| ≤ C) :
    |∑ k ∈ Finset.range N, {k : ℕ | P k ∧ ¬ P (k + 1)}.indicator F k| ≤ C := by
  classical
  let E : Set ℕ := {k | P k ∧ ¬ P (k + 1)}
  by_cases hex : ∃ i ∈ Finset.range N, i ∈ E
  · obtain ⟨i, hiN, hi⟩ := hex
    have hz (j : ℕ) (_hjN : j ∈ Finset.range N) (hji : j ≠ i) : E.indicator F j = 0 := by
      apply Set.indicator_of_notMem
      rintro ⟨hj, hnj⟩
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · exact hnj (hP (j + 1) i (by omega) hi.1)
      · exact hi.2 (hP (i + 1) j (by omega) hj)
    have he : (∑ k ∈ Finset.range N, E.indicator F k) = F i := by
      calc
        _ = E.indicator F i := Finset.sum_eq_single i hz (fun h => False.elim (h hiN))
        _ = F i := Set.indicator_of_mem hi F
    change |∑ k ∈ Finset.range N, E.indicator F k| ≤ C
    rw [he]
    exact hF i hiN hi
  · have he : (∑ k ∈ Finset.range N, E.indicator F k) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact Set.indicator_of_notMem (fun h => hex ⟨k, hk, h⟩) F
    change |∑ k ∈ Finset.range N, E.indicator F k| ≤ C
    rw [he, abs_zero]
    exact hC

theorem continuous_first_loss_wall_close (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (a : ℝ) (T : ℝ≥0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t u : ℝ≥0,
      t ≤ u → u ≤ T → (u : ℝ) - (t : ℝ) < δ →
      (∀ s : ℝ≥0, s ≤ t → |f s| < a) →
      ¬ (∀ s : ℝ≥0, s ≤ u → |f s| < a) → abs (abs (f u) - a) < ε := by
  intro ε hε
  have huc : UniformContinuousOn f (Icc (0 : ℝ≥0) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ, hδ, hc⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  refine ⟨δ, hδ, ?_⟩
  intro t u htu huT hwidth hsurv hlost
  have ht : t ∈ Icc (0 : ℝ≥0) T := ⟨zero_le, htu.trans huT⟩
  have hu : u ∈ Icc (0 : ℝ≥0) T := ⟨zero_le, huT⟩
  have htu' : (t : ℝ) ≤ (u : ℝ) := htu
  have hdist : dist u t < δ := by
    rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr htu')]
    exact hwidth
  have hct := hc u hu t ht hdist
  rw [Real.dist_eq] at hct
  have hnt : |f u| ≤ |f u - f t| + |f t| := by
    simpa only [sub_add_cancel] using abs_add_le (f u - f t) (f t)
  have htinside := hsurv t le_rfl
  push_neg at hlost
  obtain ⟨s, hsu, hsa⟩ := hlost
  have hts : t < s := lt_of_not_ge (fun hst => (not_lt_of_ge hsa) (hsurv s hst))
  have hs : s ∈ Icc (0 : ℝ≥0) T := ⟨zero_le, hsu.trans huT⟩
  have hsu' : (s : ℝ) ≤ (u : ℝ) := hsu
  have hts' : (t : ℝ) ≤ (s : ℝ) := hts.le
  have hdists : dist u s < δ := by
    rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr hsu')]
    linarith
  have hcs := hc u hu s hs hdists
  rw [Real.dist_eq] at hcs
  have hns : |f s| ≤ |f u - f s| + |f u| := by
    have hh := abs_add_le (f s - f u) (f u)
    rw [sub_add_cancel, abs_sub_comm (f s) (f u)] at hh
    exact hh
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem sine_first_loss_sums_bounded (a z H : ℝ) (ha : 0 < a) (hH : 0 < H) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (f : ℝ≥0 → ℝ) (N : ℕ) (τ : ℕ → ℝ≥0),
      Monotone τ → ∀ R : ℕ → ℝ, (∀ k : ℕ, H ≤ R k) →
      |∑ k ∈ Finset.range N,
        {k : ℕ | (∀ s : ℝ≥0, s ≤ τ k → |f s| < a) ∧
          ¬ (∀ s : ℝ≥0, s ≤ τ (k + 1) → |f s| < a)}.indicator
          (fun k => mixedSineSeries 0 0 a z (R k) (f (τ (k + 1)))) k| ≤ M := by
  obtain ⟨M, L, hM, hL, hb⟩ := sineSeries_uniform_wall_bound a z H ha hH
  refine ⟨M, hM, ?_⟩
  intro f N τ hτ R hR
  apply first_loss_sum_abs_le (fun k => ∀ s : ℝ≥0, s ≤ τ k → |f s| < a)
    (fun i j hij hj s hs => hj s (hs.trans (hτ hij))) N _ M hM
  intro k _hk _hloss
  exact (hb (R k) (hR k) (f (τ (k + 1)))).1

theorem sine_first_loss_sums_tendsto (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (a z H : ℝ) (ha : 0 < a) (hH : 0 < H) (T : ℝ≥0)
    (N : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (hτ : ∀ n : ℕ, Monotone (τ n))
    (hT : ∀ n k : ℕ, k ≤ N n → τ n k ≤ T)
    (R : ℕ → ℕ → ℝ) (hR : ∀ n k : ℕ, H ≤ R n k)
    (hmesh : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ k ∈ Finset.range (N n),
      (τ n (k + 1) : ℝ) - (τ n k : ℝ) < ε) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (N n),
      {k : ℕ | (∀ s : ℝ≥0, s ≤ τ n k → |f s| < a) ∧
        ¬ (∀ s : ℝ≥0, s ≤ τ n (k + 1) → |f s| < a)}.indicator
        (fun k => mixedSineSeries 0 0 a z (R n k) (f (τ n (k + 1)))) k)
      atTop (𝓝 0) := by
  obtain ⟨M, L, hM, hL, hb⟩ := sineSeries_uniform_wall_bound a z H ha hH
  rw [Metric.tendsto_nhds]
  intro ε hε
  let η : ℝ := ε / (L + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hsmall : L * η < ε := by
    dsimp only [η]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (show 0 < L + 1 by linarith)).mpr
    nlinarith
  obtain ⟨δ, hδ, hclose⟩ := continuous_first_loss_wall_close f hf a T η hη
  filter_upwards [hmesh δ hδ] with n hn
  have hh := first_loss_sum_abs_le
    (fun k => ∀ s : ℝ≥0, s ≤ τ n k → |f s| < a)
    (fun i j hij hj s hs => hj s (hs.trans (hτ n hij))) (N n)
    (fun k => mixedSineSeries 0 0 a z (R n k) (f (τ n (k + 1))))
    (L * η) (mul_nonneg hL hη.le) (fun k hk hloss => by
      have hc := hclose (τ n k) (τ n (k + 1)) (hτ n (by omega))
        (hT n (k + 1) (by have := Finset.mem_range.mp hk; omega)) (hn k hk) hloss.1 hloss.2
      exact (hb (R n k) (hR n k) (f (τ n (k + 1)))).2.trans
        (mul_le_mul_of_nonneg_left hc.le hL))
  simpa only [Real.dist_eq, sub_zero] using hh.trans_lt hsmall

end Shao.C2.SineFirstLossLimit
