import Shao.OQ4.RandomDenominatorAsymptotic
import Shao.OQ4.RowUniformConditionalEnergy

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Shao.OQ4.RowRandomDenominatorAsymptotic

open MeasureTheory Filter Set
open RademacherScalarBounds (lambda)
open RandomDenominatorFarTail (randomDenominatorEvent farMainTerm)
open RandomDenominatorAsymptotic
  (centerHeight middleIndices middleHeight middleLayer middleEvent middleSumConstant)
open UniformConditionalEnergy (energyCoshExcessIntegral)
open scoped BigOperators Topology

-- PRIVATE 1. Original third-moment premise pays finite FAR's square integrability.
private theorem lower_moments_integrable
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν) :
    Integrable (fun x : ℝ => x) ν ∧
      Integrable (fun x : ℝ => x ^ 2) ν := by
  have hdom : Integrable (fun x : ℝ => 1 + |x| ^ 3) ν :=
    (integrable_const (1 : ℝ)).add h3
  have hsmall (r : ℝ) (hr : 0 ≤ r) : r ≤ 1 + r ^ 3 ∧ r ^ 2 ≤ 1 + r ^ 3 := by
    by_cases hr1 : r ≤ 1
    · have hp := mul_nonneg hr (sub_nonneg.mpr hr1)
      have hc : 0 ≤ r ^ 3 := pow_nonneg hr 3
      constructor <;> nlinarith
    · have hlarge : 1 ≤ r := (lt_of_not_ge hr1).le
      have hp := mul_nonneg hr (sub_nonneg.mpr hlarge)
      have hq := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hlarge)
      constructor <;> nlinarith
  constructor
  · exact hdom.mono' measurable_id.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, id_eq] using (hsmall |x| (abs_nonneg x)).1)
  · exact hdom.mono' (by fun_prop)
      (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_pow, id_eq] using (hsmall |x| (abs_nonneg x)).2)

-- PRIVATE 2. All finite signs and center/middle thresholds are derived on a tail.
private theorem eventual_finite_conditions
    (n : ℕ → ℕ) (h : ℕ → ℝ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, 0 < n j ∧ 0 < h j ∧
      2 * ε ≤ (n j : ℝ) / h j ^ 2 := by
  filter_upwards [hinfty.eventually_gt_atTop 0,
    hlong.eventually_ge_atTop (2 * ε)] with k hk ht
  have hn : 0 < n k := by
    by_contra hn
    have hz : n k = 0 := Nat.eq_zero_of_not_pos hn
    simp only [hz, Nat.cast_zero, zero_div] at ht
    linarith
  exact ⟨hn, hk, ht⟩

-- PRIVATE 3. Actual row strip over the exact existing literal main term.
private theorem closedStrip_relative_main_tendsto
    (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j =>
      (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (@Shao.closedStrip (n j) (h j)) / farMainTerm (n j) (h j))
      atTop (𝓝 (1 : ℝ)) := by
  have hm (N : ℕ) (b : ℝ) :
      (4 / Real.pi) * Real.exp (-lambda * (N : ℝ) / b ^ 2) = farMainTerm N b := by
    dsimp only [farMainTerm, lambda]
    congr 1
    congr 1
    ring
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hc := RowUniformConditionalEnergy.varying_row_uniform_closedStrip_energy_controls
    νSeq hprob h3 hmean hsecond M hM h n hinfty hlong hshort 1 (by norm_num) 1 (by norm_num) δ hδ
  filter_upwards [hc, hinfty.eventually_gt_atTop 0] with k hk hh
  have hB := hk (h k) (by linarith) (by simp)
  rw [Real.dist_eq]
  simpa only [hm] using hB.2.1

-- PRIVATE 4. Signed exponent difference, with only eventual admissibility.
private theorem centerHeight_tail_geometry
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (d : ℝ) :
    (∀ᶠ j in atTop, h j / 2 ≤ centerHeight (n j) (h j) d ∧
      centerHeight (n j) (h j) d ≤ 2 * h j) ∧
    Tendsto (fun j =>
      (n j : ℝ) / centerHeight (n j) (h j) d ^ 2 -
        (n j : ℝ) / h j ^ 2) atTop (𝓝 (-d)) := by
  have finite_window (n : ℕ) (hn : 0 < n) (h d : ℝ) (hh : 0 < h)
      (hd : 2 * |d| ≤ (n : ℝ) / h ^ 2) :
      h / 2 ≤ centerHeight n h d ∧ centerHeight n h d ≤ 2 * h := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have ht : 0 < (n : ℝ) / h ^ 2 := div_pos hnR (sq_pos_of_pos hh)
    have hdl : -((n : ℝ) / h ^ 2) / 2 ≤ d := by
      linarith [neg_abs_le d]
    have hdu : d ≤ ((n : ℝ) / h ^ 2) / 2 := by
      linarith [le_abs_self d]
    have hratio : (1 / 2 : ℝ) ≤ 1 + d / ((n : ℝ) / h ^ 2) ∧
        1 + d / ((n : ℝ) / h ^ 2) ≤ 3 / 2 := by
      constructor
      · have hquot : -(1 / 2 : ℝ) ≤ d / ((n : ℝ) / h ^ 2) :=
          (le_div_iff₀ ht).mpr (by linarith)
        linarith
      · have hquot : d / ((n : ℝ) / h ^ 2) ≤ (1 / 2 : ℝ) :=
          (div_le_iff₀ ht).mpr (by linarith)
        linarith
    have hc : 0 ≤ centerHeight n h d := mul_nonneg hh.le (Real.sqrt_nonneg _)
    have hsq : centerHeight n h d ^ 2 = h ^ 2 * (1 + d / ((n : ℝ) / h ^ 2)) := by
      dsimp only [centerHeight]
      rw [mul_pow, Real.sq_sqrt (show 0 ≤ 1 + d / ((n : ℝ) / h ^ 2) by linarith [hratio.1])]
    constructor
    · apply (sq_le_sq₀ (by positivity : 0 ≤ h / 2) hc).mp
      rw [hsq]
      have hp := mul_le_mul_of_nonneg_left hratio.1 (sq_nonneg h)
      nlinarith
    · apply (sq_le_sq₀ hc (by positivity : 0 ≤ 2 * h)).mp
      rw [hsq]
      have hp := mul_le_mul_of_nonneg_left hratio.2 (sq_nonneg h)
      nlinarith
  have hf := eventual_finite_conditions n h hinfty hlong (|d| + 1) (by positivity)
  have hwindow : ∀ᶠ k in atTop, h k / 2 ≤ centerHeight (n k) (h k) d ∧
      centerHeight (n k) (h k) d ≤ 2 * h k := by
    filter_upwards [hf] with k hk
    exact finite_window (n k) hk.1 (h k) d hk.2.1 (by linarith [hk.2.2])
  refine ⟨hwindow, ?_⟩
  have hdlim : Tendsto (fun k => d / ((n k : ℝ) / h k ^ 2))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Pi.inv_apply, Pi.mul_apply, div_eq_mul_inv, mul_zero] using hlong.inv_tendsto_atTop.const_mul d
  have hdenlim : Tendsto (fun k => 1 + d / ((n k : ℝ) / h k ^ 2))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hdlim
  have hscalar : Tendsto (fun k => -d / (1 + d / ((n k : ℝ) / h k ^ 2)))
      atTop (𝓝 (-d)) := by
    simpa only [Pi.div_def, div_one] using
      (tendsto_const_nhds.div hdenlim (by norm_num : (1 : ℝ) ≠ 0))
  apply hscalar.congr'
  filter_upwards [hf] with k hk
  have hnR : 0 < (n k : ℝ) := by exact_mod_cast hk.1
  have htpos : 0 < (n k : ℝ) / h k ^ 2 := div_pos hnR (sq_pos_of_pos hk.2.1)
  have hdlo : -(1 / 2 : ℝ) ≤ d / ((n k : ℝ) / h k ^ 2) := by
    apply (le_div_iff₀ htpos).mpr
    linarith [neg_abs_le d, hk.2.2]
  have hrad : 0 < 1 + d / ((n k : ℝ) / h k ^ 2) := by linarith
  have hsq : centerHeight (n k) (h k) d ^ 2 =
      h k ^ 2 * (1 + d / ((n k : ℝ) / h k ^ 2)) := by
    dsimp only [centerHeight]
    rw [mul_pow, Real.sq_sqrt hrad.le]
  rw [hsq, div_mul_eq_div_div]
  symm
  apply (eq_div_iff hrad.ne').mpr
  rw [sub_mul, div_mul_cancel₀ _ hrad.ne']
  have hmul : (1 + d / ((n k : ℝ) / h k ^ 2)) * ((n k : ℝ) / h k ^ 2) =
      (n k : ℝ) / h k ^ 2 + d := by
    rw [add_mul, one_mul, div_mul_cancel₀ _ htpos.ne']
  nlinarith [hmul]

-- PUBLIC 1. Every fixed signed center perturbation under actual changing laws.
theorem varying_row_center_probability_ratio_tendsto
    (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 (0 : ℝ)))
    (d : ℝ) :
    Tendsto (fun j =>
      (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (@Shao.closedStrip (n j) (centerHeight (n j) (h j) d)) /
        (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (@Shao.closedStrip (n j) (h j)))
      atTop (𝓝 (Real.exp (lambda * d))) := by
  let G : ℕ → ℝ → ℝ := fun k b =>
    (Measure.pi (fun _ : Fin (n k) => νSeq k)).real (@Shao.closedStrip (n k) b)
  let c : ℕ → ℝ := fun k => centerHeight (n k) (h k) d
  let E : ℕ → ℝ := fun k => Real.exp (lambda *
    ((n k : ℝ) / h k ^ 2 - (n k : ℝ) / c k ^ 2))
  have hm (N : ℕ) (b : ℝ) :
      (4 / Real.pi) * Real.exp (-lambda * (N : ℝ) / b ^ 2) = farMainTerm N b := by
    dsimp only [farMainTerm, lambda]
    congr 1
    congr 1
    ring
  have hq (b : ℕ → ℝ)
      (hb : ∀ᶠ k in atTop, h k / 2 ≤ b k ∧ b k ≤ 2 * h k) :
      Tendsto (fun k => G k (b k) / farMainTerm (n k) (b k)) atTop (𝓝 (1 : ℝ)) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    have hc := RowUniformConditionalEnergy.varying_row_uniform_closedStrip_energy_controls
      νSeq hprob h3 hmean hsecond M hM h n hinfty hlong hshort 2 (by norm_num) 1 (by norm_num) δ hδ
    filter_upwards [hc, hb] with k hk hbk
    have hB := hk (b k) hbk.1 hbk.2
    rw [Real.dist_eq]
    simpa only [hm] using hB.2.1
  have hgeo := centerHeight_tail_geometry h n hinfty hlong d
  have hcwin : ∀ᶠ k in atTop, h k / 2 ≤ c k ∧ c k ≤ 2 * h k := hgeo.1
  have hhwin : ∀ᶠ k in atTop, h k / 2 ≤ h k ∧ h k ≤ 2 * h k := by
    filter_upwards [hinfty.eventually_gt_atTop 0] with k hk
    constructor <;> linarith
  have hqc := hq c hcwin
  have hqh := hq h hhwin
  have harg : Tendsto (fun k => lambda *
      ((n k : ℝ) / h k ^ 2 - (n k : ℝ) / c k ^ 2)) atTop (𝓝 (lambda * d)) := by
    have ht := hgeo.2.const_mul (-lambda)
    change Tendsto (fun k => -lambda *
      ((n k : ℝ) / c k ^ 2 - (n k : ℝ) / h k ^ 2)) atTop
        (𝓝 (-lambda * -d)) at ht
    have heq : (fun k => -lambda *
        ((n k : ℝ) / c k ^ 2 - (n k : ℝ) / h k ^ 2)) =
        (fun k => lambda * ((n k : ℝ) / h k ^ 2 - (n k : ℝ) / c k ^ 2)) := by
      funext k
      ring
    rw [heq] at ht
    simpa only [neg_mul_neg] using ht
  have hE : Tendsto E atTop (𝓝 (Real.exp (lambda * d))) := harg.rexp
  have hlim := (hqc.div hqh (by norm_num : (1 : ℝ) ≠ 0)).mul hE
  have hlim' : Tendsto (fun k =>
      ((G k (c k) / farMainTerm (n k) (c k)) /
        (G k (h k) / farMainTerm (n k) (h k))) * E k)
      atTop (𝓝 (Real.exp (lambda * d))) := by
    simpa only [Pi.div_def, Pi.mul_def, one_div, inv_one, one_mul] using hlim
  have hpos := RowUniformConditionalEnergy.varying_row_uniform_closedStrip_boundary_ratio_bound
    νSeq hprob h3 hmean hsecond M hM h n hinfty hlong hshort 2 (by norm_num)
  apply hlim'.congr'
  filter_upwards [hpos] with k hk
  have hGh : 0 < G k (h k) := hk.1
  have hmh : 0 < farMainTerm (n k) (h k) :=
    RandomDenominatorFarTail.farMainTerm_pos _ _
  have hEk : 0 < E k := Real.exp_pos _
  have hexp : Real.exp (-lambda * (n k : ℝ) / c k ^ 2) =
      E k * Real.exp (-lambda * (n k : ℝ) / h k ^ 2) := by
    dsimp only [E]
    rw [← Real.exp_add]
    congr 1
    ring
  have hmain : farMainTerm (n k) (c k) = E k * farMainTerm (n k) (h k) := by
    rw [← hm (n k) (c k), ← hm (n k) (h k), hexp]
    ring
  change ((G k (c k) / farMainTerm (n k) (c k)) /
    (G k (h k) / farMainTerm (n k) (h k))) * E k = G k (c k) / G k (h k)
  rw [hmain]
  field_simp [hGh.ne', hmh.ne', hEk.ne']
  <;> ring

-- PRIVATE 5. Actual lower-center strict energy deviation, at original h_j² scale.
private theorem center_deviation_relative_tendsto_zero
    (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 (0 : ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun j =>
      (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          ((@Shao.closedStrip (n j) (centerHeight (n j) (h j) (-ε))) ∩
            {a : Shao.Path (n j) |
              ε * h j ^ 2 < |Shao.energy a - (n j : ℝ)|}) /
        (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (@Shao.closedStrip (n j) (h j)))
      atTop (𝓝 (0 : ℝ)) := by
  let c : ℕ → ℝ := fun k => centerHeight (n k) (h k) (-ε)
  let G : ℕ → ℝ → ℝ := fun k b =>
    (Measure.pi (fun _ : Fin (n k) => νSeq k)).real (@Shao.closedStrip (n k) b)
  let R : ℕ → ℝ := fun k =>
    (Measure.pi (fun _ : Fin (n k) => νSeq k)).real
      ((@Shao.closedStrip (n k) (c k)) ∩
        {a : Shao.Path (n k) | ε * h k ^ 2 < |Shao.energy a - (n k : ℝ)|})
  have hgeo := (centerHeight_tail_geometry h n hinfty hlong (-ε)).1
  have hR : Tendsto (fun k => R k / G k (c k)) atTop (𝓝 (0 : ℝ)) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    have hc := RowUniformConditionalEnergy.varying_row_uniform_energy_concentration
      νSeq hprob h3 hmean hsecond M hM h n hinfty hlong hshort 2 (by norm_num) ε hε δ hδ
    filter_upwards [hc, hgeo] with k hk hbk
    have hB := hk (c k) hbk.1 hbk.2
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hB.2.1]
    exact hB.2.2
  have hC := varying_row_center_probability_ratio_tendsto νSeq hprob h3 hmean hsecond M hM h n
    hinfty hlong hshort (-ε)
  have hprod : Tendsto (fun k => (R k / G k (c k)) * (G k (c k) / G k (h k)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using hR.mul hC
  have hpos := RowUniformConditionalEnergy.varying_row_uniform_closedStrip_boundary_ratio_bound
    νSeq hprob h3 hmean hsecond M hM h n hinfty hlong hshort 2 (by norm_num)
  apply hprod.congr'
  filter_upwards [hpos, hgeo] with k hk hbk
  have hGc : 0 < G k (c k) := (hk.2 (c k) hbk.1 hbk.2).1
  change (R k / G k (c k)) * (G k (c k) / G k (h k)) = R k / G k (h k)
  field_simp [hGc.ne', hk.1.ne']
  <;> ring

-- PUBLIC 2. Whole literal middle event and its growing finite layer collection.
theorem varying_row_middle_relative_tendsto_zero
    (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 (0 : ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun j =>
      (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (middleEvent (n j) (h j) ε) /
        (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (@Shao.closedStrip (n j) (h j)))
      atTop (𝓝 (0 : ℝ)) := by
  let s : ℝ := lambda + 1
  have hs : lambda < s := by dsimp only [s]; linarith
  have hs0 : 0 < s := by dsimp only [s, lambda]; positivity
  let B : ℝ := middleSumConstant s ε
  have hB : 0 < B := RandomDenominatorAsymptotic.middleSumConstant_pos s ε hs hε
  have hpos := RowUniformConditionalEnergy.varying_row_uniform_closedStrip_boundary_ratio_bound
    νSeq hprob h3 hmean hsecond M hM h n hinfty hlong hshort 2 (by norm_num)
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hpos] with k hk
    exact ha.trans_le (div_nonneg measureReal_nonneg hk.1.le)
  · intro τ hτ
    let η : ℝ := τ / (B + 1)
    have hη : 0 < η := div_pos hτ (by linarith)
    have hc := RowUniformConditionalEnergy.varying_row_uniform_closedStrip_energy_controls
      νSeq hprob h3 hmean hsecond M hM h n hinfty hlong hshort 2 (by norm_num) s hs0 η hη
    have hf := eventual_finite_conditions n h hinfty hlong ε hε
    filter_upwards [hc, hpos, hf] with k hk hpk hfk
    have hcontrols : ∀ j ∈ middleIndices (n k) (h k) ε,
        0 < (Measure.pi (fun _ : Fin (n k) => νSeq k)).real
            (@Shao.closedStrip (n k) (middleHeight (n k) (h k) ε j)) ∧
          energyCoshExcessIntegral (νSeq k) (n k) (middleHeight (n k) (h k) ε j) (h k) s /
              (Measure.pi (fun _ : Fin (n k) => νSeq k)).real
                (@Shao.closedStrip (n k) (middleHeight (n k) (h k) ε j)) ≤ η ∧
          (Measure.pi (fun _ : Fin (n k) => νSeq k)).real
                (@Shao.closedStrip (n k) (middleHeight (n k) (h k) ε j)) /
              (Measure.pi (fun _ : Fin (n k) => νSeq k)).real (@Shao.closedStrip (n k) (h k)) ≤
            4 * Real.exp (lambda * (((j : ℝ) + 1) * ε)) := by
      intro j hj
      have hg := RandomDenominatorAsymptotic.middleHeight_geometry (n k) hfk.1 (h k) ε hfk.2.1 hε
        (by linarith [hfk.2.2]) j hj
      have hlo : h k / 2 ≤ middleHeight (n k) (h k) ε j := by linarith [hg.1]
      have he := hk _ hlo hg.2.1
      have hr := hpk.2 _ hlo hg.2.1
      refine ⟨he.1, he.2.2.2.le, hr.2.trans ?_⟩
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hg.2.2.2 (by dsimp only [lambda]; positivity)
    letI := hprob k
    have hfinite := RandomDenominatorAsymptotic.middle_finite_bound (νSeq k) (n k) hfk.1 (h k) ε s η hfk.2.1 hε hs hη.le
      (by linarith [hfk.2.2]) hpk.1 hcontrols
    have hsmall : η * B < τ := by
      dsimp only [η]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (show 0 < B + 1 by linarith)).mpr
      nlinarith
    exact hfinite.trans_lt hsmall

-- PRIVATE 6. Pure scalar exponential payment for the new varying-row FAR limit.
private theorem time_mul_exp_neg_tendsto
    (t : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (ht : Tendsto t atTop atTop) :
    Tendsto (fun j => t j * Real.exp (-δ * t j)) atTop (𝓝 (0 : ℝ)) := by
  have hu : Tendsto (fun k => (4 / δ ^ 2) * (t k)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using (tendsto_inv_atTop_zero.comp ht).const_mul (4 / δ ^ 2)
  apply squeeze_zero' ?_ ?_ hu
  · filter_upwards [ht.eventually_ge_atTop 0] with k hk
    exact mul_nonneg hk (Real.exp_nonneg _)
  · filter_upwards [ht.eventually_ge_atTop 1] with k hk
    have htk : 0 < t k := by linarith
    have he : δ * t k / 2 ≤ Real.exp (δ * t k / 2) := by
      linarith [Real.add_one_le_exp (δ * t k / 2)]
    have hsq : δ ^ 2 * t k ^ 2 / 4 ≤ Real.exp (δ * t k) := by
      calc
        _ = (δ * t k / 2) ^ 2 := by ring
        _ ≤ Real.exp (δ * t k / 2) ^ 2 :=
          pow_le_pow_left₀ (by positivity) he 2
        _ = _ := by rw [← Real.exp_nat_mul]; congr 1 <;> norm_num <;> ring
    calc
      _ = t k / Real.exp (δ * t k) := by
        rw [show -δ * t k = -(δ * t k) by ring, Real.exp_neg]
        ring
      _ ≤ t k / (δ ^ 2 * t k ^ 2 / 4) :=
        div_le_div_of_nonneg_left htk.le (by positivity) hsq
      _ = _ := by field_simp [ne_of_gt hδ, ne_of_gt htk] <;> ring

-- PUBLIC 3. Entire actual FAR event, including Q=2n; s>4λ chosen body-locally.
theorem varying_row_far_relative_closedStrip_tendsto_zero
    (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j =>
      (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (randomDenominatorEvent (n j) (h j) ∩
            {a : Shao.Path (n j) | 2 * (n j : ℝ) ≤ Shao.energy a}) /
        (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (@Shao.closedStrip (n j) (h j)))
      atTop (𝓝 (0 : ℝ)) := by
  let s : ℝ := 4 * lambda + 1
  have hs0 : 0 < s := by dsimp only [s, lambda]; positivity
  let δ : ℝ := s / 4 - Real.pi ^ 2 / 8
  let D : ℝ := energyNormalizerErrorConstant s * M
  let C : ℝ := RandomDenominatorFarTail.farDifferenceConstant s
  let t : ℕ → ℝ := fun k => (n k : ℝ) / h k ^ 2
  let r : ℕ → ℝ := fun k => (n k : ℝ) / h k ^ 3
  have hδ : 0 < δ := by dsimp only [δ, s, lambda]; ring_nf; norm_num
  have htime := time_mul_exp_neg_tendsto t δ hδ hlong
  have hc0 : Tendsto (fun k => (D / 8) * r k) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hshort.const_mul (D / 8)
  have hce : Tendsto (fun k => Real.exp ((D / 8) * r k)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Real.exp_zero] using hc0.rexp
  have hmajor : Tendsto
      (fun k => (C * Real.pi / 4) * (t k * Real.exp (-δ * t k)) *
        Real.exp ((D / 8) * r k)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, zero_mul] using (htime.const_mul (C * Real.pi / 4)).mul hce
  have hratio (k : ℕ) : RandomDenominatorFarTail.farScalarBound s M (n k) (h k) /
        farMainTerm (n k) (h k) =
      (C * Real.pi / 4) * (t k * Real.exp (-δ * t k)) *
        Real.exp ((D / 8) * r k) := by
    have he : Real.exp (-s * t k / 4 + D * r k / 8) =
        Real.exp (-(Real.pi ^ 2 / 8) * t k) * Real.exp (-δ * t k) *
          Real.exp ((D / 8) * r k) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp only [δ]
      ring
    change (C * t k * Real.exp (-s * t k / 4 + D * r k / 8)) /
      ((4 / Real.pi) * Real.exp (-(Real.pi ^ 2 / 8) * t k)) = _
    rw [he]
    field_simp [ne_of_gt Real.pi_pos,
      ne_of_gt (Real.exp_pos (-(Real.pi ^ 2 / 8) * t k))]
    <;> ring
  have hfinite : ∀ᶠ k in atTop, 0 < n k ∧ 1 ≤ h k ∧
      Real.log 2 ≤ s * ((n k : ℝ) / h k ^ 2) / 2 := by
    filter_upwards [hinfty.eventually_ge_atTop 1,
      hlong.eventually_ge_atTop (max 1 (2 * Real.log 2 / s))] with k hk htk
    have ht1 : 1 ≤ (n k : ℝ) / h k ^ 2 := (le_max_left _ _).trans htk
    have hn : 0 < n k := by
      by_contra hn
      have hz : n k = 0 := Nat.eq_zero_of_not_pos hn
      simp only [hz, Nat.cast_zero, zero_div] at ht1
      linarith
    refine ⟨hn, hk, ?_⟩
    have hq : 2 * Real.log 2 / s ≤ (n k : ℝ) / h k ^ 2 := (le_max_right _ _).trans htk
    have hm := (div_le_iff₀ hs0).1 hq
    nlinarith
  have hfar : Tendsto (fun k =>
      (Measure.pi (fun _ : Fin (n k) => νSeq k)).real
          (randomDenominatorEvent (n k) (h k) ∩
            {a : Shao.Path (n k) | 2 * (n k : ℝ) ≤ Shao.energy a}) /
        farMainTerm (n k) (h k)) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero' (Eventually.of_forall fun k =>
      div_nonneg measureReal_nonneg (RandomDenominatorFarTail.farMainTerm_pos (n k) (h k)).le) ?_ hmajor
    filter_upwards [hfinite] with k hk
    letI := hprob k
    have hhpos : 0 < h k := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hk.2.1
    have hSq := (lower_moments_integrable (νSeq k) (h3 k)).2
    have hb := RandomDenominatorFarTail.far_tail_bound (νSeq k) (n k) hk.1 (h k) s
      hk.2.1 hs0 hk.2.2 hSq (h3 k) (hsecond k)
    have hE : 0 ≤ energyNormalizerErrorConstant s := by
      dsimp only [energyNormalizerErrorConstant]
      positivity
    have hr0 : 0 ≤ r k := div_nonneg (Nat.cast_nonneg _) (pow_pos hhpos 3).le
    have ht0 : 0 ≤ t k := div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hbeta : energyNormalizerErrorConstant s * (∫ x : ℝ, |x| ^ 3 ∂(νSeq k)) * r k / 8 ≤
        energyNormalizerErrorConstant s * M * r k / 8 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hM k) hE) hr0) (by norm_num)
    have hbound : RandomDenominatorFarTail.farScalarBound s (∫ x : ℝ, |x| ^ 3 ∂(νSeq k))
        (n k) (h k) ≤ RandomDenominatorFarTail.farScalarBound s M (n k) (h k) := by
      unfold RandomDenominatorFarTail.farScalarBound
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        change -s * t k / 4 + energyNormalizerErrorConstant s * (∫ x : ℝ, |x| ^ 3 ∂(νSeq k)) * r k / 8 ≤
          -s * t k / 4 + energyNormalizerErrorConstant s * M * r k / 8
        linarith [hbeta]
      · exact mul_nonneg (by dsimp only [RandomDenominatorFarTail.farDifferenceConstant]; positivity) ht0
    have hdiv := div_le_div_of_nonneg_right (hb.trans hbound)
      (RandomDenominatorFarTail.farMainTerm_pos (n k) (h k)).le
    rwa [hratio k] at hdiv
  have hK := closedStrip_relative_main_tendsto νSeq hprob h3 hmean hsecond M hM h n
    hinfty hlong hshort
  have hratio' := hfar.div hK (by norm_num : (1 : ℝ) ≠ 0)
  have hlim : Tendsto (fun k =>
      ((Measure.pi (fun _ : Fin (n k) => νSeq k)).real
          (randomDenominatorEvent (n k) (h k) ∩
            {a : Shao.Path (n k) | 2 * (n k : ℝ) ≤ Shao.energy a}) /
        farMainTerm (n k) (h k)) /
      ((Measure.pi (fun _ : Fin (n k) => νSeq k)).real
          (@Shao.closedStrip (n k) (h k)) / farMainTerm (n k) (h k)))
      atTop (𝓝 (0 : ℝ)) := by simpa only [Pi.div_def, zero_div] using hratio'
  have hpos := RowUniformConditionalEnergy.varying_row_uniform_closedStrip_boundary_ratio_bound
    νSeq hprob h3 hmean hsecond M hM h n hinfty hlong hshort 1 (by norm_num)
  apply hlim.congr'
  filter_upwards [hpos] with k hk
  have hm := (RandomDenominatorFarTail.farMainTerm_pos (n k) (h k)).ne'
  field_simp [hm, hk.1.ne']
  <;> ring

-- PUBLIC 4. Actual changing-row weak random denominator over actual closedStrip.
theorem varying_row_randomDenominator_relative_closedStrip_tendsto
    (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun j => (n j : ℝ) / h j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j =>
      (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (randomDenominatorEvent (n j) (h j)) /
        (Measure.pi (fun _ : Fin (n j) => νSeq j)).real
          (@Shao.closedStrip (n j) (h j)))
      atTop (𝓝 (1 : ℝ)) := by
  let μ : (k : ℕ) → Measure (Shao.Path (n k)) :=
    fun k => Measure.pi (fun _ : Fin (n k) => νSeq k)
  let G : ℕ → ℝ → ℝ := fun k b => (μ k).real (@Shao.closedStrip (n k) b)
  let R : ℝ → ℕ → ℝ := fun ε k => (μ k).real
    ((@Shao.closedStrip (n k) (centerHeight (n k) (h k) (-ε))) ∩
      {a : Shao.Path (n k) | ε * h k ^ 2 < |Shao.energy a - (n k : ℝ)|})
  let Mid : ℝ → ℕ → ℝ := fun ε k => (μ k).real (middleEvent (n k) (h k) ε)
  let F : ℕ → ℝ := fun k => (μ k).real
    (randomDenominatorEvent (n k) (h k) ∩
      {a : Shao.Path (n k) | 2 * (n k : ℝ) ≤ Shao.energy a})
  let f : ℕ → ℝ := fun k => (μ k).real (randomDenominatorEvent (n k) (h k)) / G k (h k)
  let L : ℝ → ℕ → ℝ := fun ε k =>
    G k (centerHeight (n k) (h k) (-ε)) / G k (h k) - R ε k / G k (h k)
  let U : ℝ → ℕ → ℝ := fun ε k =>
    G k (centerHeight (n k) (h k) ε) / G k (h k) +
      Mid ε k / G k (h k) + F k / G k (h k)
  have hL (ε : ℝ) (hε : 0 < ε) :
      Tendsto (L ε) atTop (𝓝 (Real.exp (-lambda * ε))) := by
    have hc := varying_row_center_probability_ratio_tendsto νSeq hprob h3 hmean hsecond M hM h n
      hinfty hlong hshort (-ε)
    have hd := center_deviation_relative_tendsto_zero νSeq hprob h3 hmean hsecond M hM h n
      hinfty hlong hshort ε hε
    simpa only [L, μ, G, R, sub_zero, mul_neg, neg_mul] using hc.sub hd
  have hU (ε : ℝ) (hε : 0 < ε) :
      Tendsto (U ε) atTop (𝓝 (Real.exp (lambda * ε))) := by
    have hc := varying_row_center_probability_ratio_tendsto νSeq hprob h3 hmean hsecond M hM h n
      hinfty hlong hshort ε
    have hm := varying_row_middle_relative_tendsto_zero νSeq hprob h3 hmean hsecond M hM h n
      hinfty hlong hshort ε hε
    have hf := varying_row_far_relative_closedStrip_tendsto_zero νSeq hprob h3 hmean hsecond M hM h n
      hinfty hlong hshort
    simpa only [U, μ, G, Mid, F, add_zero] using (hc.add hm).add hf
  have hpos := RowUniformConditionalEnergy.varying_row_uniform_closedStrip_boundary_ratio_bound
    νSeq hprob h3 hmean hsecond M hM h n hinfty hlong hshort 1 (by norm_num)
  have hcompare (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ k in atTop, L ε k ≤ f k ∧ f k ≤ U ε k := by
    have hfinite := eventual_finite_conditions n h hinfty hlong ε hε
    filter_upwards [hfinite, hpos] with k hk hpk
    letI := hprob k
    have hl := RandomDenominatorAsymptotic.center_lower_probability_bound (νSeq k) (n k) hk.1 (h k) ε
      hk.2.1 hε hk.2.2
    have hu := RandomDenominatorAsymptotic.randomDenominator_probability_upper_bound (νSeq k) (n k) hk.1 (h k) ε
      hk.2.1 hε hk.2.2
    have hl' := div_le_div_of_nonneg_right hl hpk.1.le
    have hu' := div_le_div_of_nonneg_right hu hpk.1.le
    constructor
    · simpa only [sub_div, L, f, μ, G, R] using hl'
    · simpa only [add_div, U, f, μ, G, Mid, F] using hu'
  change Tendsto f atTop (𝓝 (1 : ℝ))
  apply tendsto_order.2
  constructor
  · intro a ha
    have he : Tendsto (fun v : ℝ => Real.exp (-lambda * v⁻¹)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [mul_zero, Real.exp_zero] using
        ((tendsto_inv_atTop_zero : Tendsto (fun v : ℝ => v⁻¹) atTop (𝓝 (0 : ℝ))).const_mul
          (-lambda)).rexp
    obtain ⟨v, hv, hve⟩ := ((eventually_gt_atTop (0 : ℝ)).and
      (he.eventually (lt_mem_nhds ha))).exists
    have hε : 0 < v⁻¹ := inv_pos.mpr hv
    filter_upwards [hcompare v⁻¹ hε,
      (hL v⁻¹ hε).eventually (lt_mem_nhds hve)] with k hk hl
    exact hl.trans_le hk.1
  · intro b hb
    have he : Tendsto (fun v : ℝ => Real.exp (lambda * v⁻¹)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [mul_zero, Real.exp_zero] using
        ((tendsto_inv_atTop_zero : Tendsto (fun v : ℝ => v⁻¹) atTop (𝓝 (0 : ℝ))).const_mul
          lambda).rexp
    obtain ⟨v, hv, hve⟩ := ((eventually_gt_atTop (0 : ℝ)).and
      (he.eventually (gt_mem_nhds hb))).exists
    have hε : 0 < v⁻¹ := inv_pos.mpr hv
    filter_upwards [hcompare v⁻¹ hε,
      (hU v⁻¹ hε).eventually (gt_mem_nhds hve)] with k hk hu
    exact hk.2.trans_lt hu

end Shao.OQ4.RowRandomDenominatorAsymptotic
end
