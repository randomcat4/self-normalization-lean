import Shao.C2.IntervalImageTaylorSegment
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
namespace Shao.C2.IntervalImageJointDerivatives
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageMixedCandidate
open Shao.C2.IntervalImageMixedSpatialDerivatives Shao.C2.IntervalImageLocalRegularity
open Shao.C2.IntervalImageTaylorSegment

theorem mixedImageCandidate_hasStrictFDerivAt (j l : ℕ) (a z T y : ℝ) (hl : l ≤ 2)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    HasStrictFDerivAt (fun p : ℝ × ℝ => mixedImageCandidate j l a z p.2 p.1)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (mixedImageCandidate (j + 1) l a z T y)).coprod
        ((1 : ℝ →L[ℝ] ℝ).smulRight (mixedImageCandidate j (l + 1) a z T y))) (y, T) := by
  have hl3 : l ≤ 3 := by omega
  have hlp3 : l + 1 ≤ 3 := by omega
  let f : ℝ → ℝ → ℝ := fun w S => mixedImageCandidate j l a z S w
  let f₁ : ℝ → ℝ → (ℝ →L[ℝ] ℝ) := fun w S =>
    (1 : ℝ →L[ℝ] ℝ).smulRight (mixedImageCandidate (j + 1) l a z S w)
  let f₂ : ℝ → ℝ → (ℝ →L[ℝ] ℝ) := fun w S =>
    (1 : ℝ →L[ℝ] ℝ).smulRight (mixedImageCandidate j (l + 1) a z S w)
  have hN : Ioo (-a) a ×ˢ Ioi 0 ∈ 𝓝 (y, T) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod (isOpen_Ioo.mem_nhds (abs_lt.mp hy)) (isOpen_Ioi.mem_nhds hT)
  have df₁ : ∀ᶠ v : ℝ × ℝ in 𝓝 (y, T), HasFDerivAt (fun w => f w v.2) (f₁ v.1 v.2) v.1 := by
    filter_upwards [hN] with v hv
    exact (mixedImageCandidate_spatial_hasDerivAt j l a z v.2 v.1 hl3 ha hz hv.2
      (abs_lt.mpr hv.1)).hasFDerivAt
  have df₂ : ∀ᶠ v : ℝ × ℝ in 𝓝 (y, T), HasFDerivAt (f v.1) (f₂ v.1 v.2) v.2 := by
    filter_upwards [hN] with v hv
    exact (mixedImageCandidate_time_hasDerivAt j l a z v.2 v.1 hl ha hz hv.2
      (abs_lt.mpr hv.1).le).hasFDerivAt
  have cf₁ : ContinuousAt (fun v : ℝ × ℝ => f₁ v.1 v.2) (y, T) := by
    have hc := mixedImageCandidate_continuousAt (j + 1) l a z T y hl3 ha hz hT hy
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.comp hc
  have cf₂ : ContinuousAt (fun v : ℝ × ℝ => f₂ v.1 v.2) (y, T) := by
    have hc := mixedImageCandidate_continuousAt j (l + 1) a z T y hlp3 ha hz hT hy
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.comp hc
  exact hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := (y, T)) (f := f)
    (f₁ := f₁) (f₂ := f₂) df₁ df₂ cf₁ cf₂

theorem intervalImageCandidate_mixed_hasStrictFDerivAt (j l : ℕ) (a z T y : ℝ) (hl : l ≤ 2)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    HasStrictFDerivAt (fun p : ℝ × ℝ =>
      iteratedDeriv l (fun S => iteratedDeriv j (intervalImageCandidate a z S) p.1) p.2)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (mixedImageCandidate (j + 1) l a z T y)).coprod
        ((1 : ℝ →L[ℝ] ℝ).smulRight (mixedImageCandidate j (l + 1) a z T y))) (y, T) := by
  have hl3 : l ≤ 3 := by omega
  have hN : Ioo (-a) a ×ˢ Ioi 0 ∈ 𝓝 (y, T) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod (isOpen_Ioo.mem_nhds (abs_lt.mp hy)) (isOpen_Ioi.mem_nhds hT)
  have heq : (fun p : ℝ × ℝ => iteratedDeriv l
      (fun S => iteratedDeriv j (intervalImageCandidate a z S) p.1) p.2)
      =ᶠ[𝓝 (y, T)] (fun p => mixedImageCandidate j l a z p.2 p.1) := by
    filter_upwards [hN] with p hp
    exact intervalImageCandidate_mixed_iteratedDeriv j l a z p.2 p.1 hl3 ha hz hp.2 (abs_lt.mpr hp.1)
  exact (mixedImageCandidate_hasStrictFDerivAt j l a z T y hl ha hz hT hy).congr_of_eventuallyEq heq.symm

theorem mixedImageCandidate_path_hasDerivAt (j l : ℕ) (a z T y b θ : ℝ) (hl : l ≤ 2)
    (ha : 0 < a) (hz : |z| ≤ a) (hS : 0 < T - θ * b ^ 2) (hy : |y + θ * b| < a) :
    HasDerivAt (fun t => mixedImageCandidate j l a z (T - t * b ^ 2) (y + t * b))
      (b * mixedImageCandidate (j + 1) l a z (T - θ * b ^ 2) (y + θ * b) -
        b ^ 2 * mixedImageCandidate j (l + 1) a z (T - θ * b ^ 2) (y + θ * b)) θ := by
  have hY : HasDerivAt (fun t : ℝ => y + t * b) b θ := by
    simpa using (hasDerivAt_mul_const b (x := θ)).const_add y
  have hE : HasDerivAt (fun t : ℝ => T - t * b ^ 2) (-b ^ 2) θ := by
    simpa using (hasDerivAt_mul_const (b ^ 2) (x := θ)).const_sub T
  have hp := hY.hasFDerivAt.prodMk hE.hasFDerivAt
  have hd := (mixedImageCandidate_hasStrictFDerivAt j l a z (T - θ * b ^ 2) (y + θ * b) hl ha hz hS hy).hasFDerivAt.comp θ hp
  convert hd.hasDerivAt using 1 <;>
    simp only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply_one, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, smul_eq_mul] <;> ring

theorem intervalImageCandidate_mixed_path_hasDerivAt (j l : ℕ) (a z T y b θ : ℝ) (hl : l ≤ 2)
    (ha : 0 < a) (hz : |z| ≤ a) (hS : 0 < T - θ * b ^ 2) (hy : |y + θ * b| < a) :
    HasDerivAt (fun t => iteratedDeriv l
      (fun S => iteratedDeriv j (intervalImageCandidate a z S) (y + t * b)) (T - t * b ^ 2))
      (b * mixedImageCandidate (j + 1) l a z (T - θ * b ^ 2) (y + θ * b) -
        b ^ 2 * mixedImageCandidate j (l + 1) a z (T - θ * b ^ 2) (y + θ * b)) θ := by
  have hY : HasDerivAt (fun t : ℝ => y + t * b) b θ := by
    simpa using (hasDerivAt_mul_const b (x := θ)).const_add y
  have hE : HasDerivAt (fun t : ℝ => T - t * b ^ 2) (-b ^ 2) θ := by
    simpa using (hasDerivAt_mul_const (b ^ 2) (x := θ)).const_sub T
  have hp := hY.hasFDerivAt.prodMk hE.hasFDerivAt
  have hd := (intervalImageCandidate_mixed_hasStrictFDerivAt j l a z (T - θ * b ^ 2) (y + θ * b) hl ha hz hS hy).hasFDerivAt.comp θ hp
  convert hd.hasDerivAt using 1 <;>
    simp only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply_one, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, smul_eq_mul] <;> ring

end Shao.C2.IntervalImageJointDerivatives

