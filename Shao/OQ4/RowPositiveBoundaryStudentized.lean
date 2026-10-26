import Shao.OQ4.PositiveBoundaryStudentized
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.OQ4.RowPositiveBoundaryStudentized

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal Topology

universe uB
variable {ΩB : Type uB} [MeasurableSpace ΩB]

-- PRIVATE 1. E|Q/n-1| and finite-product variance factorization are proof-local.
-- No centering, no fourth moment, no strict positivity assumption on M.
private theorem finite_energy_truncation_bound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (M : ℝ) (hM : (∫ z : ℝ, |z| ^ 3 ∂ν) ≤ M)
    (n : ℕ) (hn : 0 < n) (K : ℝ) (hK : 0 < K)
    (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi (fun _ : Fin n => ν)).real
      (PositiveBoundaryStudentized.energyBad n δ) ≤
        (Real.sqrt (K / (n : ℝ)) + 2 * M / Real.sqrt K) / δ := by
  classical
  let μ : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ν)
  let Y : ℝ → ℝ := fun z => min (z ^ 2) K
  let c : ℝ := ∫ z, Y z ∂ν
  let S : Shao.Path n → ℝ := fun a => ∑ i, Y (a i)
  let f : Shao.Path n → ℝ := fun a => (S a - (n : ℝ) * c) / (n : ℝ)
  let R : Shao.Path n → ℝ := fun a => (Shao.energy a - S a) / (n : ℝ)
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hYmeas : Measurable Y := by dsimp only [Y]; fun_prop
  have hYnon (z : ℝ) : 0 ≤ Y z := le_min (sq_nonneg z) hK.le
  have hYle (z : ℝ) : Y z ≤ K := min_le_right _ _
  have hYsq (z : ℝ) : Y z ^ 2 ≤ K * z ^ 2 := by
    have h1 := min_le_left (z ^ 2) K
    have h2 := hYle z
    have h3z := hYnon z
    dsimp only [Y] at *
    nlinarith [mul_le_mul h2 h1 h3z hK.le]
  have hYlp : MemLp Y 2 ν :=
    (memLp_const K).mono' hYmeas.aestronglyMeasurable
      (Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hYnon z), abs_of_pos hK]
          using hYle z)
  have hYi : Integrable Y ν := hYlp.integrable (by norm_num)
  have hSq : Integrable (fun z : ℝ => z ^ 2) ν := by
    apply ((integrable_const (1 : ℝ)).add h3).mono' (by fun_prop)
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z)]
    change z ^ 2 ≤ 1 + |z| ^ 3
    have hz := abs_nonneg z
    have hz2 : |z| ^ 2 = z ^ 2 := sq_abs z
    by_cases h : |z| ≤ 1
    · nlinarith [mul_nonneg hz (sub_nonneg.mpr h), pow_nonneg hz 3]
    · have hh : 1 ≤ |z| := le_of_not_ge h
      nlinarith [sq_nonneg (|z| - 1),
        mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg |z|)]
  have hc0 : 0 ≤ c := integral_nonneg hYnon
  have hc1 : c ≤ 1 := by
    calc c ≤ ∫ z : ℝ, z ^ 2 ∂ν := integral_mono hYi hSq (fun z => min_le_left _ _)
         _ = 1 := hsecond
  have htail (z : ℝ) : z ^ 2 - Y z ≤ |z| ^ 3 / Real.sqrt K := by
    by_cases hz : z ^ 2 ≤ K
    · rw [show Y z = z ^ 2 from min_eq_left hz, sub_self]
      exact div_nonneg (pow_nonneg (abs_nonneg z) 3) hsK.le
    · have hzK : K < z ^ 2 := lt_of_not_ge hz
      have ha : Real.sqrt K ≤ |z| := by
        have hsq := Real.sq_sqrt hK.le
        nlinarith [sq_abs z, abs_nonneg z, Real.sqrt_nonneg K]
      rw [show Y z = K from min_eq_right hzK.le]
      apply (le_div_iff₀ hsK).mpr
      have hmul := mul_le_mul_of_nonneg_left ha (sq_nonneg z)
      have ha2 := sq_abs z
      have hz3 : |z| ^ 3 = z ^ 2 * |z| := by rw [pow_succ, sq_abs]
      nlinarith [mul_nonneg hK.le hsK.le]
  have hrbound : 1 - c ≤ M / Real.sqrt K := by
    calc
      1 - c = ∫ z : ℝ, z ^ 2 - Y z ∂ν := by rw [integral_sub hSq hYi, hsecond]
      _ ≤ ∫ z : ℝ, |z| ^ 3 / Real.sqrt K ∂ν :=
        integral_mono (hSq.sub hYi) (h3.div_const _) htail
      _ = (∫ z : ℝ, |z| ^ 3 ∂ν) / Real.sqrt K := integral_div _ _
      _ ≤ M / Real.sqrt K := div_le_div_of_nonneg_right hM hsK.le
  have hY2 : (∫ z, Y z ^ 2 ∂ν) ≤ K := by
    calc
      _ ≤ ∫ z : ℝ, K * z ^ 2 ∂ν :=
        integral_mono hYlp.integrable_sq (hSq.const_mul _) hYsq
      _ = K := by rw [integral_const_mul, hsecond, mul_one]
  have hSlp : MemLp S 2 μ := by
    exact memLp_finsetSum _ (fun i _ =>
      hYlp.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => ν) i))
  have hSi : Integrable S μ := hSlp.integrable (by norm_num)
  have hSmean : (∫ a, S a ∂μ) = (n : ℝ) * c := by
    dsimp only [S, μ]
    rw [integral_finsetSum _ (fun i _ => integrable_comp_eval (μ := fun _ : Fin n => ν) (i := i) hYi)]
    simp only [integral_comp_eval (μ := fun _ : Fin n => ν) hYi.aestronglyMeasurable, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, c]
  have hvar : variance S μ ≤ (n : ℝ) * K := by
    have heq : variance S μ = ∑ _i : Fin n, variance Y ν := by
      have hv := variance_sum_pi (μ := fun _ : Fin n => ν) (X := fun _ : Fin n => Y)
        (fun _ => hYlp)
      have he : (∑ i : Fin n, fun a : Shao.Path n => Y (a i)) = S := by
        funext a
        simp only [Finset.sum_apply, S]
      change variance (∑ i : Fin n, fun a : Shao.Path n => Y (a i)) μ = _ at hv
      rwa [he] at hv
    rw [heq]
    calc
      _ ≤ ∑ _i : Fin n, K := Finset.sum_le_sum fun _ _ =>
        (variance_le_expectation_sq hYi.aestronglyMeasurable).trans hY2
      _ = (n : ℝ) * K := by simp
  have hflp : MemLp f 2 μ := by
    simpa only [f, div_eq_mul_inv, Pi.sub_apply] using
      (hSlp.sub (memLp_const ((n : ℝ) * c))).mul_const (n : ℝ)⁻¹
  have hfi : Integrable f μ := hflp.integrable (by norm_num)
  have hf2 : (∫ a, f a ^ 2 ∂μ) ≤ K / (n : ℝ) := by
    have heq : (∫ a, f a ^ 2 ∂μ) = variance S μ / (n : ℝ) ^ 2 := by
      rw [variance_eq_integral hSlp.aemeasurable, hSmean]
      dsimp only [f]
      simp_rw [div_pow]
      exact integral_div _ _
    rw [heq]
    calc
      _ ≤ ((n : ℝ) * K) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hvar (sq_nonneg _)
      _ = K / (n : ℝ) := by field_simp [hn0] <;> ring
  have hfabs : (∫ a, |f a| ∂μ) ≤ Real.sqrt (K / (n : ℝ)) := by
    let d : ℝ := ∫ a, |f a| ∂μ
    have hd0 : 0 ≤ d := integral_nonneg (fun _ => abs_nonneg _)
    have hnon : 0 ≤ (∫ a, f a ^ 2 ∂μ) - d ^ 2 := by
      have he : 0 ≤ ∫ a, (|f a| - d) ^ 2 ∂μ :=
        integral_nonneg (fun a : Shao.Path n => sq_nonneg (|f a| - d))
      have heq : (∫ a, (|f a| - d) ^ 2 ∂μ) =
          (∫ a, f a ^ 2 ∂μ) - d ^ 2 := by
        have hpoint : (fun a => (|f a| - d) ^ 2) =
            (fun a => f a ^ 2 - (2 * d) * |f a| + d ^ 2) := by
          funext a; nlinarith [sq_abs (f a)]
        have hsubI : Integrable (fun a => f a ^ 2 - (2 * d) * |f a|) μ := by
          exact (hflp.integrable_sq.sub (hfi.abs.const_mul (2 * d))).congr
            (Eventually.of_forall fun a => by rfl)
        rw [hpoint, integral_add hsubI
          (integrable_const _), integral_sub hflp.integrable_sq (hfi.abs.const_mul _),
          integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul, smul_eq_mul]
        dsimp only [d] at *
        ring
      rwa [heq] at he
    have hs := Real.sq_sqrt (div_nonneg hK.le hnR.le)
    have hs0 := Real.sqrt_nonneg (K / (n : ℝ))
    dsimp only [d] at *
    nlinarith
  have hEnergyI : Integrable (fun a : Shao.Path n => Shao.energy a) μ := by
    exact integrable_finsetSum _ (fun i _ => integrable_comp_eval (μ := fun _ : Fin n => ν) (i := i) hSq)
  have hRi : Integrable R μ := (hEnergyI.sub hSi).div_const _
  have hR0 (a : Shao.Path n) : 0 ≤ R a := by
    apply div_nonneg _ hnR.le
    apply sub_nonneg.mpr
    exact Finset.sum_le_sum fun i _ => min_le_left _ _
  have hEnergyMean : (∫ a : Shao.Path n, Shao.energy a ∂μ) = (n : ℝ) := by
    dsimp only [Shao.energy, μ]
    rw [integral_finsetSum _ (fun i _ => integrable_comp_eval (μ := fun _ : Fin n => ν) (i := i) hSq)]
    simp only [integral_comp_eval (μ := fun _ : Fin n => ν) hSq.aestronglyMeasurable, hsecond,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hRmean : (∫ a, R a ∂μ) = 1 - c := by
    dsimp only [R]
    rw [integral_div, integral_sub hEnergyI hSi, hEnergyMean, hSmean]
    field_simp [hn0]
    <;> ring
  let g : Shao.Path n → ℝ := fun a => |Shao.energy a / (n : ℝ) - 1|
  have hgi : Integrable g μ := ((hEnergyI.div_const _).sub (integrable_const _)).abs
  have hgbound : (∫ a, g a ∂μ) ≤ Real.sqrt (K / (n : ℝ)) + 2 * M / Real.sqrt K := by
    have hpoint (a : Shao.Path n) : g a ≤ |f a| + R a + (1 - c) := by
      have hid : Shao.energy a / (n : ℝ) - 1 = f a + R a - (1 - c) := by
        dsimp only [f, R]; field_simp [hn0] <;> ring
      dsimp only [g]
      rw [hid]
      calc
        _ ≤ |f a + R a| + |1 - c| := abs_sub _ _
        _ ≤ |f a| + R a + (1 - c) := by
          rw [abs_of_nonneg (sub_nonneg.mpr hc1)]
          have hh := abs_add_le (f a) (R a)
          rw [abs_of_nonneg (hR0 a)] at hh
          linarith
    calc
      _ ≤ ∫ a, |f a| + R a + (1 - c) ∂μ :=
        integral_mono hgi ((hfi.abs.add hRi).add (integrable_const _)) hpoint
      _ = (∫ a, |f a| ∂μ) + 2 * (1 - c) := by
        have hsumI : Integrable (fun a => |f a| + R a) μ := by
          exact (hfi.abs.add hRi).congr (Eventually.of_forall fun a => by rfl)
        rw [integral_add hsumI (integrable_const _),
          integral_add hfi.abs hRi, hRmean]
        simp only [integral_const, probReal_univ, one_smul, smul_eq_mul]
        ring
      _ ≤ Real.sqrt (K / (n : ℝ)) + 2 * M / Real.sqrt K := by
        calc
          _ ≤ Real.sqrt (K / (n : ℝ)) + 2 * (M / Real.sqrt K) :=
            add_le_add hfabs (mul_le_mul_of_nonneg_left hrbound (by norm_num))
          _ = _ := by ring
  have hbad : PositiveBoundaryStudentized.energyBad n δ ⊆ {a | δ ≤ g a} := by
    intro a ha
    have hh : δ * (n : ℝ) < |Shao.energy a - (n : ℝ)| := ha
    have heq : Shao.energy a / (n : ℝ) - 1 =
        (Shao.energy a - (n : ℝ)) / (n : ℝ) := by field_simp [hn0] <;> ring
    change δ ≤ g a
    dsimp only [g]
    rw [heq, abs_div, abs_of_pos hnR]
    exact ((lt_div_iff₀ hnR).mpr hh).le
  apply (le_div_iff₀ hδ).mpr
  calc
    μ.real (PositiveBoundaryStudentized.energyBad n δ) * δ ≤
        μ.real {a | δ ≤ g a} * δ :=
      mul_le_mul_of_nonneg_right (measureReal_mono hbad) hδ.le
    _ = δ * μ.real {a | δ ≤ g a} := mul_comm _ _
    _ ≤ ∫ a, g a ∂μ := mul_meas_ge_le_integral_of_nonneg
      (Eventually.of_forall fun _ => abs_nonneg _) hgi δ
    _ ≤ _ := hgbound

-- PUBLIC 1. This head is strictly weaker than the row-window target.
theorem varying_row_energy_lln
    (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun z : ℝ => |z| ^ 3) (νSeq j))
    (hsecond : ∀ j, (∫ z : ℝ, z ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ z : ℝ, |z| ^ 3 ∂(νSeq j)) ≤ M)
    (nSeq : ℕ → ℕ) (hn : Tendsto nSeq atTop atTop)
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun j => (Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).real
      (PositiveBoundaryStudentized.energyBad (nSeq j) δ))
      atTop (𝓝 (0 : ℝ)) := by
  have hM0 : 0 ≤ M :=
    (integral_nonneg (fun z : ℝ => pow_nonneg (abs_nonneg z) 3)).trans (hM 0)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hbig : Tendsto (fun K : ℝ => (2 * M / Real.sqrt K) / δ) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_div] using
      ((tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop).div_const δ :
        Tendsto (fun K : ℝ => (2 * M / Real.sqrt K) / δ) atTop (𝓝 (0 / δ)))
  obtain ⟨K, hK1, hKb⟩ := (eventually_gt_atTop (0 : ℝ)).and
    (hbig.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by linarith))) |>.exists
  have hK : 0 < K := hK1
  have hnat : Tendsto (fun j => (nSeq j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hsmall : Tendsto (fun j => Real.sqrt (K / (nSeq j : ℝ)) / δ)
      atTop (𝓝 (0 : ℝ)) := by
    have hd : Tendsto (fun j => K / (nSeq j : ℝ)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.div_atTop hnat
    simpa only [Function.comp_def, Real.sqrt_zero, zero_div] using (Real.continuous_sqrt.tendsto 0 |>.comp hd).div_const δ
  filter_upwards [hn.eventually (eventually_gt_atTop (0 : ℕ)),
    hsmall.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by linarith))]
    with j hnj hj
  letI : IsProbabilityMeasure (νSeq j) := hprob j
  have hb := finite_energy_truncation_bound (νSeq j) (h3 j) (hsecond j)
    M (hM j) (nSeq j) hnj K hK δ hδ
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  have heq : (Real.sqrt (K / (nSeq j : ℝ)) + 2 * M / Real.sqrt K) / δ =
      Real.sqrt (K / (nSeq j : ℝ)) / δ + (2 * M / Real.sqrt K) / δ := add_div _ _ _
  linarith

-- PUBLIC 2. Uses the existing actual varying-row polygonal survival limit.
theorem varying_row_deterministic_positive_boundary_tendsto
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun z : ℝ => |z| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ z : ℝ, z ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ z : ℝ, z ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ z : ℝ, |z| ^ 3 ∂(νSeq j)) ≤ M)
    (nSeq : ℕ → ℕ) (hn : Tendsto nSeq atTop atTop)
    (rSeq : ℕ → ℝ) (r : ℝ) (hr : 0 < r)
    (hrSeq : Tendsto rSeq atTop (𝓝 r)) :
    Tendsto (fun j => (Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).real
      (@Shao.closedStrip (nSeq j) (rSeq j * Real.sqrt (nSeq j : ℝ))))
      atTop (𝓝 (Shao.Probability.BrownianSup.probability B P hB r)) := by
  have horizon_exact (r : ℝ) (hr : 0 < r) (n : ℕ) :
      (Real.toNNReal ((r ^ 2)⁻¹) : ℝ) * (r * Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) ∧
        PolygonalKilledFunctionalLimit.floorHorizon
          (Real.toNNReal ((r ^ 2)⁻¹)) (r * Real.sqrt (n : ℝ)) = n := by
    have he : (Real.toNNReal ((r ^ 2)⁻¹) : ℝ) *
        (r * Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := by
      rw [Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg r)), mul_pow,
        Real.sq_sqrt (Nat.cast_nonneg n)]
      field_simp [ne_of_gt hr]
    exact ⟨he, by simp only [PolygonalKilledFunctionalLimit.floorHorizon, he,
      Nat.floor_natCast]⟩
  have discrete_event_eq_closedStrip (n : ℕ) (h : ℝ) (hh : 0 < h) (b : ℝ≥0) :
      PolygonalKilledFunctionalLimit.discreteClosedSurvival n n h 0 b =
        (Shao.closedStrip ((b : ℝ) * h) : Set (Shao.Path n)) := by
    ext a
    change (∀ k : ℕ, k ≤ n → |0 + Shao.prefixSum a k / h| ≤ (b : ℝ)) ↔
      ∀ k : ℕ, k ≤ n → |Shao.prefixSum a k| ≤ (b : ℝ) * h
    simp only [zero_add, abs_div, abs_of_pos hh, div_le_iff₀ hh]
  let N : ℕ → ℕ := fun j => max (nSeq j) 1
  let T : ℝ≥0 := Real.toNNReal ((r ^ 2)⁻¹)
  let h : ℕ → ℝ := fun j => r * Real.sqrt (N j : ℝ)
  let b : ℕ → ℝ≥0 := fun j => Real.toNNReal (rSeq j / r)
  have hNpos (j : ℕ) : 0 < N j :=
    lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hN : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun j => le_max_left (nSeq j) 1) hn
  have hNeq : N =ᶠ[atTop] nSeq := by
    filter_upwards [hn.eventually (eventually_ge_atTop (1 : ℕ))] with j hj
    exact max_eq_left hj
  have hT : 0 < T := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos hr))
  have hpos (j : ℕ) : 0 < h j :=
    mul_pos hr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (hNpos j)))
  have hhor (j : ℕ) : (T : ℝ) * h j ^ 2 ≤ (N j : ℝ) :=
    (horizon_exact r hr (N j)).1.le
  have hinfty : Tendsto h atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)).const_mul_atTop hr
  have hb : Tendsto b atTop (𝓝 (1 : ℝ≥0)) := by
    have hd : Tendsto (fun j => rSeq j / r) atTop (𝓝 (1 : ℝ)) := by
      simpa only [div_self (ne_of_gt hr)] using hrSeq.div_const r
    simpa only [b, Real.toNNReal_one] using tendsto_real_toNNReal hd
  have hlim := PolygonalKilledFunctionalLimit.discrete_survival_tendsto_brownian
    B P hB T hT N h νSeq hprob
    hpos hhor h3 hmean hsecond M hM hinfty
    b hb (fun _ => 0) 0 tendsto_const_nhds (by norm_num)
  have htime : P.real (BrownianSurvivalBoundary.closedSurvival B T 0) =
      Shao.Probability.BrownianSup.probability B P hB r := by
    rw [BrownianPositiveCDF.survival_time_eq_probability B P hB T hT]
    congr 1
    simp only [T, Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg r)),
      Real.sqrt_inv, Real.sqrt_sq_eq_abs, abs_of_pos hr, one_div, inv_inv]
  rw [htime] at hlim
  apply hlim.congr'
  filter_upwards [hNeq, hrSeq.eventually (eventually_gt_nhds hr)] with j hNj hrj
  rw [(horizon_exact r hr (N j)).2,
    discrete_event_eq_closedStrip (N j) (h j) (hpos j) (b j)]
  have hwall : (b j : ℝ) * h j = rSeq j * Real.sqrt (N j : ℝ) := by
    dsimp only [b, h]
    rw [Real.coe_toNNReal _ (div_nonneg hrj.le hr.le)]
    field_simp [ne_of_gt hr] <;> ring
  rw [hwall, hNj]

-- PUBLIC 3. Literal actual weak multiplicative event; includes Q=0 and n=0.
theorem varying_row_studentized_positive_boundary_tendsto
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun z : ℝ => |z| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ z : ℝ, z ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ z : ℝ, z ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ z : ℝ, |z| ^ 3 ∂(νSeq j)) ≤ M)
    (nSeq : ℕ → ℕ) (hn : Tendsto nSeq atTop atTop)
    (xSeq : ℕ → ℝ) (x : ℝ) (hx : 0 < x)
    (hxSeq : Tendsto xSeq atTop (𝓝 x)) :
    Tendsto (fun j => (Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).real
      {a : Shao.Path (nSeq j) |
        a ∈ Shao.closedStrip (xSeq j * Real.sqrt (Shao.energy a))})
      atTop (𝓝 (Shao.Probability.BrownianSup.probability B P hB x)) := by
  let F := Shao.Probability.BrownianSup.probability B P hB
  let p : ℕ → ℝ := fun j => (Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).real
    {a : Shao.Path (nSeq j) | a ∈ Shao.closedStrip (xSeq j * Real.sqrt (Shao.energy a))}
  have hFc : ContinuousAt F x := BrownianPositiveCDF.probability_continuousAt B P hB x hx
  have hm : Tendsto (fun d : ℝ => F (x * Real.sqrt (1 - d))) (𝓝 (0 : ℝ)) (𝓝 (F x)) := by
    have ha : Tendsto (fun d : ℝ => x * Real.sqrt (1 - d)) (𝓝 (0 : ℝ)) (𝓝 x) := by
      simpa only [sub_zero, Real.sqrt_one, mul_one] using
        (show Continuous (fun d : ℝ => x * Real.sqrt (1 - d)) by fun_prop).tendsto 0
    exact hFc.tendsto.comp ha
  have hp : Tendsto (fun d : ℝ => F (x * Real.sqrt (1 + d))) (𝓝 (0 : ℝ)) (𝓝 (F x)) := by
    have ha : Tendsto (fun d : ℝ => x * Real.sqrt (1 + d)) (𝓝 (0 : ℝ)) (𝓝 x) := by
      simpa only [add_zero, Real.sqrt_one, mul_one] using
        (show Continuous (fun d : ℝ => x * Real.sqrt (1 + d)) by fun_prop).tendsto 0
    exact hFc.tendsto.comp ha
  change Tendsto p atTop (𝓝 (F x))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hquarter : 0 < ε / 4 := by linarith
  have hnear := ((Metric.tendsto_nhds.mp hm) (ε / 4) hquarter).and
    ((Metric.tendsto_nhds.mp hp) (ε / 4) hquarter)
  obtain ⟨η, hη, hηball⟩ := Metric.mem_nhds_iff.mp hnear
  let δ : ℝ := min η 1 / 2
  have hδ : 0 < δ := div_pos (lt_min hη zero_lt_one) (by norm_num)
  have hδ1 : δ < 1 := by
    have hh := min_le_right η (1 : ℝ)
    dsimp only [δ]
    linarith
  have hδη : δ < η := by
    have hh := min_le_left η (1 : ℝ)
    dsimp only [δ]
    linarith
  have hδball : δ ∈ Metric.ball (0 : ℝ) η := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδ] using hδη
  obtain ⟨hFm, hFp⟩ := hηball hδball
  let qminus : ℕ → ℝ := fun j => (Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).real
    (Shao.closedStrip (xSeq j * Real.sqrt (nSeq j : ℝ) * Real.sqrt (1 - δ)))
  let qplus : ℕ → ℝ := fun j => (Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).real
    (Shao.closedStrip (xSeq j * Real.sqrt (nSeq j : ℝ) * Real.sqrt (1 + δ)))
  let err : ℕ → ℝ := fun j => (Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).real
    (PositiveBoundaryStudentized.energyBad (nSeq j) δ)
  have hqm : Tendsto qminus atTop (𝓝 (F (x * Real.sqrt (1 - δ)))) := by
    have hh := varying_row_deterministic_positive_boundary_tendsto B P hB νSeq hprob h3 hmean hsecond M hM
      nSeq hn (fun j => xSeq j * Real.sqrt (1 - δ)) (x * Real.sqrt (1 - δ))
      (mul_pos hx (Real.sqrt_pos.mpr (sub_pos.mpr hδ1)))
      (hxSeq.mul_const (Real.sqrt (1 - δ)))
    simpa only [qminus, F, mul_assoc, mul_left_comm, mul_comm] using hh
  have hqp : Tendsto qplus atTop (𝓝 (F (x * Real.sqrt (1 + δ)))) := by
    have hh := varying_row_deterministic_positive_boundary_tendsto B P hB νSeq hprob h3 hmean hsecond M hM
      nSeq hn (fun j => xSeq j * Real.sqrt (1 + δ)) (x * Real.sqrt (1 + δ))
      (mul_pos hx (Real.sqrt_pos.mpr (by linarith : 0 < 1 + δ)))
      (hxSeq.mul_const (Real.sqrt (1 + δ)))
    simpa only [qplus, F, mul_assoc, mul_left_comm, mul_comm] using hh
  have he : Tendsto err atTop (𝓝 (0 : ℝ)) :=
    varying_row_energy_lln νSeq hprob h3 hsecond M hM nSeq hn δ hδ
  filter_upwards [(Metric.tendsto_nhds.mp hqm) (ε / 4) hquarter,
    (Metric.tendsto_nhds.mp hqp) (ε / 4) hquarter,
    (Metric.tendsto_nhds.mp he) (ε / 4) hquarter,
    hxSeq.eventually (eventually_gt_nhds hx)] with j hjm hjp hje hxj
  letI : IsProbabilityMeasure (νSeq j) := hprob j
  have hs := PositiveBoundaryStudentized.sandwich_probability (νSeq j) (nSeq j) (xSeq j) hxj.le δ hδ hδ1
  rw [PositiveBoundaryStudentized.randomDenominatorEvent_eq] at hs
  have hlo : qminus j - err j ≤ p j := hs.1
  have hup : p j ≤ qplus j + err j := hs.2
  have h1 : |qminus j - F (x * Real.sqrt (1 - δ))| < ε / 4 := by
    simpa only [Real.dist_eq] using hjm
  have h2 : |qplus j - F (x * Real.sqrt (1 + δ))| < ε / 4 := by
    simpa only [Real.dist_eq] using hjp
  have h3e : |err j| < ε / 4 := by simpa only [Real.dist_eq, sub_zero] using hje
  have h4 : |F (x * Real.sqrt (1 - δ)) - F x| < ε / 4 := by
    simpa only [Real.dist_eq] using hFm
  have h5 : |F (x * Real.sqrt (1 + δ)) - F x| < ε / 4 := by
    simpa only [Real.dist_eq] using hFp
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor
  · linarith [(abs_lt.mp h1).1, (abs_lt.mp h3e).2, (abs_lt.mp h4).1]
  · linarith [(abs_lt.mp h2).2, (abs_lt.mp h3e).2, (abs_lt.mp h5).2]

-- PUBLIC 4. Exact positive-limit consumer of the broader window contradiction.
theorem varying_row_studentized_positive_boundary_ratio_tendsto
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun z : ℝ => |z| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ z : ℝ, z ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ z : ℝ, z ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ z : ℝ, |z| ^ 3 ∂(νSeq j)) ≤ M)
    (nSeq : ℕ → ℕ) (hn : Tendsto nSeq atTop atTop)
    (xSeq : ℕ → ℝ) (x : ℝ) (hx : 0 < x)
    (hxSeq : Tendsto xSeq atTop (𝓝 x)) :
    Tendsto (fun j =>
      (Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).real
        {a : Shao.Path (nSeq j) |
          a ∈ Shao.closedStrip (xSeq j * Real.sqrt (Shao.energy a))} /
      Shao.Probability.BrownianSup.probability B P hB (xSeq j))
      atTop (𝓝 (1 : ℝ)) := by
  have hnum := varying_row_studentized_positive_boundary_tendsto B P hB
    νSeq hprob h3 hmean hsecond M hM nSeq hn xSeq x hx hxSeq
  have hden := BrownianPositiveCDF.probability_tendsto B P hB xSeq x hx hxSeq
  have hne := ne_of_gt (BrownianPositiveCDF.probability_pos B P hB x hx)
  have hdiv := hnum.div hden hne
  rw [div_self hne] at hdiv
  exact hdiv

end Shao.OQ4.RowPositiveBoundaryStudentized
end
