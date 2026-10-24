import Shao.C2.BrownianSineMartingale

noncomputable section
namespace Shao.C2.BrownianSineStoppedMesh
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
open Shao.C2.BridgeDomination Shao.C2.IntervalSineSeries Shao.C2.BrownianSineMartingale
open Shao.OQ4.PolygonalBrownianWeakLimit

private theorem physical_survival_ae_unitPath {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T : ℝ≥0) :
    {ω | ∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a} =ᵐ[P]
      (brownianUnitPath B T) ⁻¹'
        {p : C(BridgeTime, ℝ) | ‖ContinuousMap.const BridgeTime y + p‖ < a} := by
  filter_upwards [ae_brownianUnitPath_eq B T P hB] with ω hp
  apply propext
  change (∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a) ↔
    ‖ContinuousMap.const BridgeTime y + brownianUnitPath B T ω‖ < a
  rw [ContinuousMap.norm_lt_iff_of_nonempty]
  have hp' (t : BridgeTime) : brownianUnitPath B T ω t =
      B (T * ⟨(t : ℝ), t.property.1⟩) ω := hp t
  simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, Real.norm_eq_abs, hp']
  by_cases hT : T = 0
  · subst T
    constructor
    · intro h t
      let u : ℝ≥0 := ⟨(t : ℝ), t.property.1⟩
      change |y + B ((0 : ℝ≥0) * u) ω| < a
      rw [zero_mul]
      exact h 0 le_rfl
    · intro h s hs
      have he : s = 0 := le_antisymm hs zero_le
      subst s
      have ht := h (0 : BridgeTime)
      change |y + B ((0 : ℝ≥0) * 0) ω| < a at ht
      simpa only [zero_mul] using ht
  · have hTpos : 0 < (T : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hT : 0 < T)
    constructor
    · intro h t
      apply h
      let u : ℝ≥0 := ⟨(t : ℝ), t.property.1⟩
      change T * u ≤ T
      have hu : u ≤ 1 := by
        apply NNReal.coe_le_coe.mp
        exact t.property.2
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hu (show (0 : ℝ≥0) ≤ T from zero_le)
    · intro h s hsT
      let t : BridgeTime := ⟨(s : ℝ) / (T : ℝ), div_nonneg s.property T.property,
        (div_le_one hTpos).2 (by exact_mod_cast hsT)⟩
      let u : ℝ≥0 := ⟨(t : ℝ), t.property.1⟩
      have heq : T * u = s := by
        apply NNReal.eq
        change (T : ℝ) * ((s : ℝ) / (T : ℝ)) = (s : ℝ)
        field_simp
      have ht := h t
      change |y + B (T * u) ω| < a at ht
      simpa only [heq] using ht

theorem strict_survival_nullMeasurable {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T : ℝ≥0) :
    NullMeasurableSet {ω | ∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a} P := by
  have hN : MeasurableSet {p : C(BridgeTime, ℝ) |
      ‖ContinuousMap.const BridgeTime y + p‖ < a} :=
    (isOpen_lt (continuous_const.add continuous_id).norm continuous_const).measurableSet
  exact ((aemeasurable_brownianUnitPath B T P hB).nullMeasurableSet_preimage hN).congr
    (physical_survival_ae_unitPath B P hB a y T).symm

private theorem sine_restrict_integrable {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a z H y : ℝ) (ha : 0 < a) (hH : 0 < H)
    (t : ℝ≥0) (E : Set Ω) (hE : NullMeasurableSet E P) :
    Integrable (E.indicator (fun ω => mixedSineSeries 0 0 a z H (y + B t ω))) P := by
  have hi := (brownian_sine_backward_weighted B P hB a z H y ha hH 0 t
    (fun _ : C(BridgeTime, ℝ) => (1 : ℝ)) measurable_const ⟨1, fun _ => by norm_num⟩).1
  have hi' : Integrable (fun ω => mixedSineSeries 0 0 a z H (y + B t ω)) P := by
    simpa only [zero_add, one_mul] using hi
  exact (integrable_indicator_iff₀ hE).mpr hi'.integrableOn

theorem brownian_sine_survival_mask {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a z H y : ℝ) (ha : 0 < a) (hH : 0 < H) (T S : ℝ≥0) :
    (∫ ω in {ω | ∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a},
      mixedSineSeries 0 0 a z H (y + B (T + S) ω) ∂P) =
    ∫ ω in {ω | ∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a},
      mixedSineSeries 0 0 a z (H + (S : ℝ)) (y + B T ω) ∂P := by
  let E : Set Ω := {ω | ∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a}
  let V := brownianUnitPath B T
  let N : Set C(BridgeTime, ℝ) := {p | ‖ContinuousMap.const BridgeTime y + p‖ < a}
  let F : C(BridgeTime, ℝ) → ℝ := N.indicator (fun _ => 1)
  have hN : MeasurableSet N :=
    (isOpen_lt (continuous_const.add continuous_id).norm continuous_const).measurableSet
  have hF : Measurable F := measurable_const.indicator hN
  have hb : ∃ M : ℝ, ∀ p, |F p| ≤ M := by
    refine ⟨1, fun p => ?_⟩
    by_cases hp : p ∈ N
    · simp only [F, Set.indicator_of_mem hp, abs_one, le_refl]
    · simp only [F, Set.indicator_of_notMem hp, abs_zero, zero_le_one]
  have hE : NullMeasurableSet E P := strict_survival_nullMeasurable B P hB a y T
  have hAE : E =ᵐ[P] V ⁻¹' N := physical_survival_ae_unitPath B P hB a y T
  have hind (g : Ω → ℝ) : (fun ω => F (V ω) * g ω) =ᵐ[P] E.indicator g := by
    filter_upwards [hAE] with ω hω
    have hh : ω ∈ E ↔ V ω ∈ N := Iff.of_eq hω
    by_cases hp : V ω ∈ N
    · have he : ω ∈ E := hh.mpr hp
      change N.indicator (fun _ => (1 : ℝ)) (V ω) * g ω = E.indicator g ω
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem he, one_mul]
    · have he : ω ∉ E := fun h => hp (hh.mp h)
      change N.indicator (fun _ => (1 : ℝ)) (V ω) * g ω = E.indicator g ω
      rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem he, zero_mul]
  calc
    _ = ∫ ω, E.indicator (fun ω => mixedSineSeries 0 0 a z H (y + B (T + S) ω)) ω ∂P :=
      (integral_indicator₀ hE).symm
    _ = ∫ ω, F (V ω) * mixedSineSeries 0 0 a z H (y + B (T + S) ω) ∂P :=
      integral_congr_ae (hind _).symm
    _ = ∫ ω, F (V ω) * mixedSineSeries 0 0 a z (H + (S : ℝ)) (y + B T ω) ∂P :=
      (brownian_sine_backward_weighted B P hB a z H y ha hH T S F hF hb).2.2
    _ = ∫ ω, E.indicator (fun ω => mixedSineSeries 0 0 a z (H + (S : ℝ)) (y + B T ω)) ω ∂P :=
      integral_congr_ae (hind _)
    _ = _ := integral_indicator₀ hE

theorem brownian_sine_finite_stopped_mesh {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a z H y : ℝ) (ha : 0 < a) (hH : 0 < H)
    (hy : |y| < a) (δ : ℝ≥0) (N : ℕ) :
    (∫ ω in {ω | ∀ s : ℝ≥0, s ≤ (N : ℝ≥0) * δ → |y + B s ω| < a},
      mixedSineSeries 0 0 a z H (y + B ((N : ℝ≥0) * δ) ω) ∂P) =
      mixedSineSeries 0 0 a z (H + (N : ℝ) * (δ : ℝ)) y -
        ∑ k ∈ Finset.range N,
          ∫ ω in {ω | ∀ s : ℝ≥0, s ≤ (k : ℝ≥0) * δ → |y + B s ω| < a} \
              {ω | ∀ s : ℝ≥0, s ≤ ((k + 1 : ℕ) : ℝ≥0) * δ → |y + B s ω| < a},
            mixedSineSeries 0 0 a z (H + ((N - (k + 1) : ℕ) : ℝ) * (δ : ℝ))
              (y + B (((k + 1 : ℕ) : ℝ≥0) * δ) ω) ∂P := by
  let V (k : ℕ) : Set Ω := {ω | ∀ s : ℝ≥0, s ≤ (k : ℝ≥0) * δ → |y + B s ω| < a}
  let R (k : ℕ) (ω : Ω) : ℝ := mixedSineSeries 0 0 a z
    (H + ((N - k : ℕ) : ℝ) * (δ : ℝ)) (y + B ((k : ℝ≥0) * δ) ω)
  let A (k : ℕ) : ℝ := ∫ ω in V k, R k ω ∂P
  let D (k : ℕ) : ℝ := ∫ ω in V k \ V (k + 1), R (k + 1) ω ∂P
  have hV (k : ℕ) : NullMeasurableSet (V k) P :=
    strict_survival_nullMeasurable B P hB a y ((k : ℝ≥0) * δ)
  have hR (k : ℕ) : 0 < H + ((N - k : ℕ) : ℝ) * (δ : ℝ) :=
    add_pos_of_pos_of_nonneg hH (mul_nonneg (Nat.cast_nonneg _) δ.property)
  have hsub (k : ℕ) : V (k + 1) ⊆ V k := by
    intro ω hω s hs
    apply hω s
    apply hs.trans
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) (show (0 : ℝ≥0) ≤ δ from zero_le)
  have htime (k : ℕ) : (k : ℝ≥0) * δ + δ = ((k + 1 : ℕ) : ℝ≥0) * δ := by
    push_cast
    ring
  have hstep (k : ℕ) (hk : k < N) : A (k + 1) + D k = A k := by
    have hn : N - k = N - (k + 1) + 1 := by omega
    have hcut : H + ((N - (k + 1) : ℕ) : ℝ) * (δ : ℝ) + (δ : ℝ) =
        H + ((N - k : ℕ) : ℝ) * (δ : ℝ) := by
      rw [hn, Nat.cast_add, Nat.cast_one]
      ring
    have hm := brownian_sine_survival_mask B P hB a z
      (H + ((N - (k + 1) : ℕ) : ℝ) * (δ : ℝ)) y ha (hR (k + 1)) ((k : ℝ≥0) * δ) δ
    rw [htime k, hcut] at hm
    change (∫ ω in V k, R (k + 1) ω ∂P) = A k at hm
    have hi1 : Integrable ((V (k + 1)).indicator (R (k + 1))) P :=
      sine_restrict_integrable B P hB a z _ y ha (hR (k + 1)) _ _ (hV (k + 1))
    have hi2 : Integrable ((V k \ V (k + 1)).indicator (R (k + 1))) P :=
      sine_restrict_integrable B P hB a z _ y ha (hR (k + 1)) _ _ ((hV k).diff (hV (k + 1)))
    have hind (ω : Ω) : (V (k + 1)).indicator (R (k + 1)) ω +
        (V k \ V (k + 1)).indicator (R (k + 1)) ω = (V k).indicator (R (k + 1)) ω := by
      by_cases hn : ω ∈ V (k + 1)
      · have hp := hsub k hn
        simp [Set.indicator, hn, hp]
      · by_cases hp : ω ∈ V k <;> simp [Set.indicator, hn, hp]
    calc
      A (k + 1) + D k = (∫ ω, (V (k + 1)).indicator (R (k + 1)) ω ∂P) +
          ∫ ω, (V k \ V (k + 1)).indicator (R (k + 1)) ω ∂P :=
        congrArg₂ (· + ·) (integral_indicator₀ (hV (k + 1))).symm
          (integral_indicator₀ ((hV k).diff (hV (k + 1)))).symm
      _ = ∫ ω, (V (k + 1)).indicator (R (k + 1)) ω +
          (V k \ V (k + 1)).indicator (R (k + 1)) ω ∂P := (integral_add hi1 hi2).symm
      _ = ∫ ω, (V k).indicator (R (k + 1)) ω ∂P :=
        integral_congr_ae (Eventually.of_forall hind)
      _ = ∫ ω in V k, R (k + 1) ω ∂P := integral_indicator₀ (hV k)
      _ = A k := hm
  have htel (n : ℕ) (hn : n ≤ N) : A n + ∑ k ∈ Finset.range n, D k = A 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hs := hstep n (by omega)
      have hp := ih (by omega)
      linarith
  have hstart : A 0 = mixedSineSeries 0 0 a z (H + (N : ℝ) * (δ : ℝ)) y := by
    calc
      A 0 = ∫ ω, (V 0).indicator (R 0) ω ∂P := (integral_indicator₀ (hV 0)).symm
      _ = ∫ _ω : Ω, mixedSineSeries 0 0 a z (H + (N : ℝ) * (δ : ℝ)) y ∂P := by
        apply integral_congr_ae
        filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hzero
        have he : ω ∈ V 0 := by
          intro s hs
          have hs0 : s = 0 := le_antisymm (by simpa only [Nat.cast_zero, zero_mul] using hs) zero_le
          simpa only [hs0, hzero, add_zero] using hy
        rw [Set.indicator_of_mem he]
        simp only [R, Nat.sub_zero, Nat.cast_zero, zero_mul, hzero, add_zero]
      _ = _ := by simp
  have hh := htel N le_rfl
  rw [hstart] at hh
  have hfinal : A N = mixedSineSeries 0 0 a z (H + (N : ℝ) * (δ : ℝ)) y -
      ∑ k ∈ Finset.range N, D k := by linarith
  simpa only [A, R, V, D, Nat.sub_self, Nat.cast_zero, zero_mul, add_zero] using hfinal

end Shao.C2.BrownianSineStoppedMesh
