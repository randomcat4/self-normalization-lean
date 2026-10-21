import Shao.Probability.TruncationIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Regularity of the genuine truncation budget

The measure and sample size are fixed in each assertion. An integrable square
is sufficient for continuity and the general normalized limit. Strict increase
also needs a positive square integral and a positive sample size. None of these
results requires a probability or finite-measure assumption.

The source normalization is `n ∫ z² dν = 1`, not `∫ z² dν = 1`. Consequently
the general limit is `n ∫ z² dν`, and the source limit is exactly one.
-/

set_option autoImplicit false

namespace Shao

open MeasureTheory Filter
open scoped Topology

theorem continuousOn_truncationBudget (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    ContinuousOn (truncationBudget ν n) (Set.Ici 0) := by
  intro t ht
  have ht0 : 0 ≤ t := ht
  have hmeas : ∀ᶠ s : ℝ in 𝓝[Set.Ici 0] t,
      AEStronglyMeasurable (fun z : ℝ => truncationF ((1 + s) * z)) ν :=
    Eventually.of_forall (fun s => (integrable_truncationF_mul ν h2 (1 + s)).aestronglyMeasurable)
  have hupper0 : ∀ᶠ s : ℝ in 𝓝 t, s < t + 1 :=
    Iio_mem_nhds (show t < t + 1 by linarith)
  have hupper : ∀ᶠ s : ℝ in 𝓝[Set.Ici 0] t, s < t + 1 :=
    hupper0.filter_mono nhdsWithin_le_nhds
  have hbound : ∀ᶠ s : ℝ in 𝓝[Set.Ici 0] t,
      ∀ᵐ z : ℝ ∂ν, ‖truncationF ((1 + s) * z)‖ ≤ (2 + t) ^ 2 * z ^ 2 := by
    filter_upwards [self_mem_nhdsWithin, hupper] with s hs hsupper
    have hs0 : 0 ≤ s := hs
    exact ae_of_all ν (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (truncationF_nonneg _)]
      have hsq : (1 + s) ^ 2 ≤ (2 + t) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      calc
        truncationF ((1 + s) * z) ≤ ((1 + s) * z) ^ 2 := truncationF_le_sq _
        _ = (1 + s) ^ 2 * z ^ 2 := mul_pow _ _ _
        _ ≤ (2 + t) ^ 2 * z ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg z))
  have hc (z : ℝ) : Continuous (fun s : ℝ => truncationF ((1 + s) * z)) :=
    continuous_truncationF.comp ((continuous_const.add continuous_id).mul continuous_const)
  have hI : ContinuousWithinAt (fun s : ℝ => ∫ z : ℝ, truncationF ((1 + s) * z) ∂ν)
      (Set.Ici 0) t :=
    continuousWithinAt_of_dominated hmeas hbound (h2.const_mul ((2 + t) ^ 2))
      (ae_of_all ν (fun z => (hc z).continuousAt.continuousWithinAt))
  exact (continuousWithinAt_const.mul hI : ContinuousWithinAt
    (fun s : ℝ => (n : ℝ) * ∫ z : ℝ, truncationF ((1 + s) * z) ∂ν) (Set.Ici 0) t)

theorem truncationBudget_pos (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (hn : 0 < n)
    (hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂ν) (t : ℝ) (ht : 0 ≤ t) :
    0 < truncationBudget ν n t := by
  have ha : 0 < 1 + t := by linarith
  have hFint := integrable_truncationF_mul ν h2 (1 + t)
  have hFnonneg : 0 ≤ (fun z : ℝ => truncationF ((1 + t) * z)) :=
    fun z => truncationF_nonneg _
  have hIpos : 0 < ∫ z : ℝ, truncationF ((1 + t) * z) ∂ν := by
    by_contra hnot
    have hIzero : (∫ z : ℝ, truncationF ((1 + t) * z) ∂ν) = 0 :=
      le_antisymm (le_of_not_gt hnot) (integral_nonneg hFnonneg)
    have hAE : (fun z : ℝ => truncationF ((1 + t) * z)) =ᵐ[ν] 0 :=
      (integral_eq_zero_iff_of_nonneg hFnonneg hFint).mp hIzero
    have hsqAE : (fun z : ℝ => z ^ 2) =ᵐ[ν] 0 := hAE.mono (fun z hz => by
      change truncationF ((1 + t) * z) = 0 at hz
      change z ^ 2 = 0
      by_cases hz0 : z = 0
      · simp [hz0]
      · have hprod : (1 + t) * z ≠ 0 := mul_ne_zero ha.ne' hz0
        have hFpos : 0 < truncationF ((1 + t) * z) :=
          mul_pos (sq_pos_of_ne_zero hprod)
            (lt_min (abs_pos.mpr hprod) zero_lt_one)
        exact False.elim ((ne_of_gt hFpos) hz))
    have hsecondzero : (∫ z : ℝ, z ^ 2 ∂ν) = 0 := by
      simpa using integral_congr_ae hsqAE
    linarith
  exact mul_pos (Nat.cast_pos.mpr hn) hIpos

theorem strictMonoOn_truncationBudget (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (hn : 0 < n)
    (hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂ν) :
    StrictMonoOn (truncationBudget ν n) (Set.Ici 0) := by
  intro s hs t ht hst
  have hs0 : 0 ≤ s := hs
  have hs1 : 0 < 1 + s := by linarith
  let c : ℝ := (1 + t) / (1 + s)
  have hc : 1 < c := by
    apply (lt_div_iff₀ hs1).mpr
    linarith
  have htime : c * (1 + s) - 1 = t := by
    dsimp [c]
    rw [div_mul_cancel₀ _ hs1.ne']
    ring
  have hbound := (truncationBudget_scale_one_le ν n h2 s c hc.le).1
  rw [htime] at hbound
  have hRpos := truncationBudget_pos ν n h2 hn hsecond s hs0
  have hc2 : 1 < c ^ 2 := by nlinarith
  calc
    truncationBudget ν n s < c ^ 2 * truncationBudget ν n s := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hc2 hRpos
    _ ≤ truncationBudget ν n t := hbound

theorem tendsto_truncationBudget_div_sq (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    Tendsto (fun t : ℝ => truncationBudget ν n t / (1 + t) ^ 2) atTop
      (𝓝 ((n : ℝ) * ∫ z : ℝ, z ^ 2 ∂ν)) := by
  let g : ℝ → ℝ → ℝ := fun t z => z ^ 2 * min ((1 + t) * |z|) 1
  have hgc (t : ℝ) : Continuous (g t) :=
    (continuous_id.pow 2).mul ((continuous_const.mul continuous_abs).min continuous_const)
  have hmeas : ∀ᶠ t : ℝ in atTop, AEStronglyMeasurable (g t) ν :=
    Eventually.of_forall (fun t => (hgc t).aestronglyMeasurable)
  have hbound : ∀ᶠ t : ℝ in atTop, ∀ᵐ z : ℝ ∂ν, ‖g t z‖ ≤ z ^ 2 := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact ae_of_all ν (fun z => by
      have hmin : 0 ≤ min ((1 + t) * |z|) 1 :=
        le_min (mul_nonneg (by linarith) (abs_nonneg z)) zero_le_one
      have hg0 : 0 ≤ g t z := mul_nonneg (sq_nonneg z) hmin
      rw [Real.norm_eq_abs, abs_of_nonneg hg0]
      calc
        g t z ≤ z ^ 2 * 1 := mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg z)
        _ = z ^ 2 := mul_one _)
  have hpointwise : ∀ᵐ z : ℝ ∂ν, Tendsto (fun t : ℝ => g t z) atTop (𝓝 (z ^ 2)) := by
    exact ae_of_all ν (fun z => by
      by_cases hz : z = 0
      · simp [g, hz]
      · have hu : 0 < |z| := abs_pos.mpr hz
        have heq : (fun t : ℝ => g t z) =ᶠ[atTop] (fun _t : ℝ => z ^ 2) := by
          filter_upwards [eventually_ge_atTop (1 / |z|)] with t ht
          have hlarge : 1 ≤ (1 + t) * |z| := by
            nlinarith [(div_le_iff₀ hu).mp ht]
          dsimp [g]
          rw [min_eq_right hlarge, mul_one]
        exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds)
  have hI : Tendsto (fun t : ℝ => ∫ z : ℝ, g t z ∂ν) atTop
      (𝓝 (∫ z : ℝ, z ^ 2 ∂ν)) :=
    tendsto_integral_filter_of_dominated_convergence (fun z : ℝ => z ^ 2)
      hmeas hbound h2 hpointwise
  have hmul : Tendsto (fun t : ℝ => (n : ℝ) * ∫ z : ℝ, g t z ∂ν) atTop
      (𝓝 ((n : ℝ) * ∫ z : ℝ, z ^ 2 ∂ν)) := tendsto_const_nhds.mul hI
  have heq : (fun t : ℝ => truncationBudget ν n t / (1 + t) ^ 2) =ᶠ[atTop]
      (fun t : ℝ => (n : ℝ) * ∫ z : ℝ, g t z ∂ν) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have ha : 0 < 1 + t := by linarith
    have hpoint (z : ℝ) : truncationF ((1 + t) * z) / (1 + t) ^ 2 = g t z := by
      apply (div_eq_iff (pow_ne_zero 2 ha.ne')).mpr
      dsimp [g]
      rw [truncationF, mul_pow, abs_mul, abs_of_nonneg ha.le]
      ring
    have hIeq : (∫ z : ℝ, truncationF ((1 + t) * z) ∂ν) / (1 + t) ^ 2 =
        ∫ z : ℝ, g t z ∂ν := by
      rw [← integral_div]
      exact integral_congr_ae (ae_of_all ν hpoint)
    unfold truncationBudget
    rw [mul_div_assoc, hIeq]
  exact Filter.Tendsto.congr' heq.symm hmul

theorem tendsto_truncationBudget_div_sq_of_normalized_second
    (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1) :
    Tendsto (fun t : ℝ => truncationBudget ν n t / (1 + t) ^ 2) atTop (𝓝 1) := by
  simpa only [hnorm] using tendsto_truncationBudget_div_sq ν n h2

end Shao
