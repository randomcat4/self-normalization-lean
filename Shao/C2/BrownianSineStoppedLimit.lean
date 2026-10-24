import Shao.C2.SineFirstLossLimit

noncomputable section
namespace Shao.C2.BrownianSineStoppedLimit
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
open Shao.C2.IntervalSineSeries Shao.C2.SineFirstLossLimit
open Shao.C2.BrownianSineMartingale Shao.C2.BrownianSineStoppedMesh
open Shao.C2.BrownianKilledKernel Shao.C2.BrownianKilledAction

def sineFirstLossTerm (f : ℝ≥0 → ℝ) (a z H : ℝ) (δ : ℝ≥0) (N k : ℕ) : ℝ :=
  {j : ℕ | (∀ s : ℝ≥0, s ≤ (j : ℝ≥0) * δ → |f s| < a) ∧
    ¬ (∀ s : ℝ≥0, s ≤ ((j + 1 : ℕ) : ℝ≥0) * δ → |f s| < a)}.indicator
    (fun j => mixedSineSeries 0 0 a z (H + ((N - (j + 1) : ℕ) : ℝ) * (δ : ℝ))
      (f (((j + 1 : ℕ) : ℝ≥0) * δ))) k

private theorem brownian_sine_endpoint_integrable {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a z H y : ℝ) (ha : 0 < a) (hH : 0 < H) (t : ℝ≥0) :
    Integrable (fun ω => mixedSineSeries 0 0 a z H (y + B t ω)) P := by
  have hh := brownian_sine_backward_weighted B P hB a z H y ha hH 0 t
    (fun _ => 1) measurable_const ⟨1, fun _ => by norm_num⟩
  simpa only [zero_add, one_mul] using hh.1

private theorem brownian_sine_loss_term_integrable {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a z H y : ℝ) (ha : 0 < a) (hH : 0 < H)
    (δ : ℝ≥0) (N k : ℕ) :
    Integrable (fun ω => sineFirstLossTerm (fun s => y + B s ω) a z H δ N k) P := by
  let U : ℝ := H + ((N - (k + 1) : ℕ) : ℝ) * (δ : ℝ)
  have hU : 0 < U := add_pos_of_pos_of_nonneg hH (mul_nonneg (Nat.cast_nonneg _) δ.property)
  let E : Set Ω := {ω | ∀ s : ℝ≥0, s ≤ (k : ℝ≥0) * δ → |y + B s ω| < a} \
    {ω | ∀ s : ℝ≥0, s ≤ ((k + 1 : ℕ) : ℝ≥0) * δ → |y + B s ω| < a}
  let F : Ω → ℝ := fun ω => mixedSineSeries 0 0 a z U (y + B (((k + 1 : ℕ) : ℝ≥0) * δ) ω)
  have hE : NullMeasurableSet E P :=
    (strict_survival_nullMeasurable B P hB a y ((k : ℝ≥0) * δ)).diff
      (strict_survival_nullMeasurable B P hB a y (((k + 1 : ℕ) : ℝ≥0) * δ))
  have hi : Integrable (E.indicator F) P := (integrable_indicator_iff₀ hE).mpr
    (brownian_sine_endpoint_integrable B P hB a z U y ha hU _).integrableOn
  change Integrable (E.indicator F) P
  exact hi

private theorem uniform_mesh_width_tendsto (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ((T / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hh := tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hn)
    (a := (T : ℝ))
  change Tendsto (fun n : ℕ => (T : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0)
  simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using hh

theorem brownian_sine_first_loss_error_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a z H y : ℝ) (ha : 0 < a) (hH : 0 < H) (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ ω,
      ∑ k ∈ Finset.range (n + 1), sineFirstLossTerm (fun s => y + B s ω)
        a z H (T / ((n + 1 : ℕ) : ℝ≥0)) (n + 1) k ∂P) atTop (𝓝 0) := by
  let δ (n : ℕ) : ℝ≥0 := T / ((n + 1 : ℕ) : ℝ≥0)
  let τ (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) * δ n
  let R (n k : ℕ) : ℝ := H + ((n + 1 - (k + 1) : ℕ) : ℝ) * (δ n : ℝ)
  have hτ (n : ℕ) : Monotone (τ n) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) (show (0 : ℝ≥0) ≤ δ n from zero_le)
  have hend (n : ℕ) : ((n + 1 : ℕ) : ℝ≥0) * δ n = T := by
    dsimp only [δ]
    field_simp
  have hT (n k : ℕ) (hk : k ≤ n + 1) : τ n k ≤ T :=
    (hτ n hk).trans_eq (hend n)
  have hR (n k : ℕ) : H ≤ R n k := le_add_of_nonneg_right
    (mul_nonneg (Nat.cast_nonneg _) (δ n).property)
  have hmesh : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ k ∈ Finset.range (n + 1),
      (τ n (k + 1) : ℝ) - (τ n k : ℝ) < ε := by
    intro ε hε
    have hh : ∀ᶠ n in atTop, (δ n : ℝ) < ε :=
      (uniform_mesh_width_tendsto T).eventually (gt_mem_nhds hε)
    filter_upwards [hh] with n hn k _hk
    change (((k + 1 : ℕ) : ℝ) * (δ n : ℝ)) - (k : ℝ) * (δ n : ℝ) < ε
    push_cast
    nlinarith
  obtain ⟨M, hM, hb⟩ := sine_first_loss_sums_bounded a z H ha hH
  have hi (n : ℕ) : Integrable (fun ω => ∑ k ∈ Finset.range (n + 1),
      sineFirstLossTerm (fun s => y + B s ω) a z H (δ n) (n + 1) k) P :=
    integrable_finsetSum _ (fun k _ => brownian_sine_loss_term_integrable B P hB a z H y ha hH _ _ _)
  have hbound (n : ℕ) : ∀ᵐ ω ∂P, ‖∑ k ∈ Finset.range (n + 1),
      sineFirstLossTerm (fun s => y + B s ω) a z H (δ n) (n + 1) k‖ ≤ M := by
    apply Eventually.of_forall
    intro ω
    simpa only [sineFirstLossTerm, τ, R, Real.norm_eq_abs] using
      hb (fun s => y + B s ω) (n + 1) (τ n) (hτ n) (R n) (hR n)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1),
      sineFirstLossTerm (fun s => y + B s ω) a z H (δ n) (n + 1) k) atTop (𝓝 0) := by
    filter_upwards [hB.cont] with ω hω
    simpa only [sineFirstLossTerm, τ, R] using sine_first_loss_sums_tendsto
      (fun s => y + B s ω) (continuous_const.add hω) a z H ha hH T
      (fun n => n + 1) τ hτ hT R hR hmesh
  have hh := tendsto_integral_of_dominated_convergence (μ := P) (f := fun _ : Ω => (0 : ℝ))
    (fun _ => M) (fun n => (hi n).aestronglyMeasurable) (integrable_const M) hbound hlim
  simpa only [integral_zero] using hh

theorem brownian_sine_survival_action {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a z H y : ℝ) (ha : 0 < a) (hH : 0 < H)
    (hy : |y| < a) (T : ℝ≥0) :
    Integrable (fun ω => mixedSineSeries 0 0 a z H (y + B T ω))
      (P.restrict {ω | ∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a}) ∧
    (∫ ω in {ω | ∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a},
      mixedSineSeries 0 0 a z H (y + B T ω) ∂P) =
        mixedSineSeries 0 0 a z (H + (T : ℝ)) y := by
  refine ⟨(brownian_sine_endpoint_integrable B P hB a z H y ha hH T).integrableOn, ?_⟩
  let A : ℝ := ∫ ω in {ω | ∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a},
    mixedSineSeries 0 0 a z H (y + B T ω) ∂P
  let C : ℝ := mixedSineSeries 0 0 a z (H + (T : ℝ)) y
  let δ (n : ℕ) : ℝ≥0 := T / ((n + 1 : ℕ) : ℝ≥0)
  let E (n : ℕ) : ℝ := ∫ ω, ∑ k ∈ Finset.range (n + 1),
    sineFirstLossTerm (fun s => y + B s ω) a z H (δ n) (n + 1) k ∂P
  have hend (n : ℕ) : ((n + 1 : ℕ) : ℝ≥0) * δ n = T := by
    dsimp only [δ]
    field_simp
  have heq (n : ℕ) : A = C - E n := by
    have hf := brownian_sine_finite_stopped_mesh B P hB a z H y ha hH hy (δ n) (n + 1)
    rw [hend n] at hf
    have hprod : ((n + 1 : ℕ) : ℝ) * (δ n : ℝ) = (T : ℝ) := by exact_mod_cast hend n
    rw [hprod] at hf
    have hsum : E n = ∑ k ∈ Finset.range (n + 1),
        ∫ ω in {ω | ∀ s : ℝ≥0, s ≤ (k : ℝ≥0) * δ n → |y + B s ω| < a} \
          {ω | ∀ s : ℝ≥0, s ≤ ((k + 1 : ℕ) : ℝ≥0) * δ n → |y + B s ω| < a},
        mixedSineSeries 0 0 a z (H + ((n + 1 - (k + 1) : ℕ) : ℝ) * (δ n : ℝ))
          (y + B (((k + 1 : ℕ) : ℝ≥0) * δ n) ω) ∂P := by
      dsimp only [E]
      rw [integral_finsetSum _ (fun k _ => brownian_sine_loss_term_integrable B P hB a z H y ha hH _ _ _)]
      apply Finset.sum_congr rfl
      intro k _hk
      let V : Set Ω := {ω | ∀ s : ℝ≥0, s ≤ (k : ℝ≥0) * δ n → |y + B s ω| < a} \
        {ω | ∀ s : ℝ≥0, s ≤ ((k + 1 : ℕ) : ℝ≥0) * δ n → |y + B s ω| < a}
      have hV : NullMeasurableSet V P :=
        (strict_survival_nullMeasurable B P hB a y _).diff
          (strict_survival_nullMeasurable B P hB a y _)
      change (∫ ω, V.indicator (fun ω => mixedSineSeries 0 0 a z
        (H + ((n + 1 - (k + 1) : ℕ) : ℝ) * (δ n : ℝ))
        (y + B (((k + 1 : ℕ) : ℝ≥0) * δ n) ω)) ω ∂P) = _
      exact integral_indicator₀ hV
    change A = C - _ at hf
    rw [hsum]
    exact hf
  have hlim : Tendsto E atTop (𝓝 0) :=
    brownian_sine_first_loss_error_tendsto B P hB a z H y ha hH T
  have hh : Tendsto (fun _n : ℕ => A) atTop (𝓝 C) := by
    have hc : Tendsto (fun n => C - E n) atTop (𝓝 (C - 0)) := tendsto_const_nhds.sub hlim
    simpa only [sub_zero] using hc.congr' (Eventually.of_forall (fun n => (heq n).symm))
  exact tendsto_nhds_unique tendsto_const_nhds hh

theorem actualIntervalKernel_sine_action {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a z H y : ℝ) (ha : 0 < a) (hH : 0 < H)
    (hy : |y| < a) (T : ℝ≥0) (hT : T ≠ 0) :
    Integrable (mixedSineSeries 0 0 a z H) (actualIntervalKernel B P a T y) ∧
    (∫ x : ℝ, mixedSineSeries 0 0 a z H x ∂actualIntervalKernel B P a T y) =
      mixedSineSeries 0 0 a z (H + (T : ℝ)) y := by
  have hm : Measurable (mixedSineSeries 0 0 a z H) :=
    (continuous_iff_continuousAt.mpr (fun x =>
      (mixedSineSeries_spatial_hasDerivAt 0 0 a z H x ha hH).continuousAt)).measurable
  obtain ⟨M, L, hM, hL, hb⟩ := Shao.C2.SineStoppedWallBound.sineSeries_uniform_wall_bound a z H ha hH
  have hh := actualIntervalKernel_action_bounded B P hB a y T hT
    (mixedSineSeries 0 0 a z H) hm ⟨M, fun x => (hb H le_rfl x).1⟩
  exact ⟨hh.1, hh.2.2.trans (brownian_sine_survival_action B P hB a z H y ha hH hy T).2⟩

end Shao.C2.BrownianSineStoppedLimit
