import Shao.C2.IntervalImageMixedTerms

noncomputable section
namespace Shao.C2.IntervalImageMixedConvergence
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageSpatialProfiles
open Shao.C2.IntervalImageSpatialConvergence Shao.C2.IntervalImageSpatialDerivatives
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageIntSeries
open Shao.C2.IntervalImageTimeDerivatives Shao.C2.IntervalImageCandidatePDE
open Shao.C2.IntervalImageTimeProfiles Shao.C2.IntervalImageHigherTime Shao.C2.IntervalImageMixedTerms

def mixedTailBlock (j l : ℕ) (a z T y : ℝ) (n : ℕ) : ℝ :=
  iteratedDeriv l (fun S => spatialImageA j a z S y ((n : ℤ) + 2)) T +
    iteratedDeriv l (fun S => spatialImageA j a z S y (-((n : ℤ) + 2))) T -
    iteratedDeriv l (fun S => spatialImageB j a z S y ((n : ℤ) + 1)) T -
    iteratedDeriv l (fun S => spatialImageB j a z S y (-((n : ℤ) + 2))) T

def mixedTailSum (j l : ℕ) (a z T y : ℝ) : ℝ :=
  ∑' n : ℕ, mixedTailBlock j l a z T y n

theorem mixedTailBlock_time_hasDerivAt (j l : ℕ) (a z T y : ℝ) (n : ℕ)
    (hl : l ≤ 2) (hT : 0 < T) :
    HasDerivAt (fun S => mixedTailBlock j l a z S y n)
      (mixedTailBlock j (l + 1) a z T y n) T := by
  exact (((spatialImageA_time_iterated_hasDerivAt j l a z T y ((n : ℤ) + 2) hl hT).add
    (spatialImageA_time_iterated_hasDerivAt j l a z T y (-((n : ℤ) + 2)) hl hT)).sub
    (spatialImageB_time_iterated_hasDerivAt j l a z T y ((n : ℤ) + 1) hl hT)).sub
    (spatialImageB_time_iterated_hasDerivAt j l a z T y (-((n : ℤ) + 2)) hl hT)

theorem mixedTailBlock_bound (j l : ℕ) (a z H U : ℝ) (n : ℕ) (p : StripPoint a H U)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hH : 0 < H) (hHU : H ≤ U) :
    ‖mixedTailBlock j l a z p.val.2 p.val.1 n‖ ≤
      (4 * spatialPrefactor j a H * mixedTimeConstant j l / H ^ l) * gaussianMajorant a U n := by
  have hT : 0 < p.val.2 := hH.trans_le p.property.2.1
  have hK : 0 ≤ spatialPrefactor j a H := by dsimp only [spatialPrefactor]; positivity
  have hC := mixedTimeConstant_nonneg j l
  have hb := spatial_prefactor_bound j a H p.val.2 p.val.1 z ha hH p.property.2.1 p.property.1 hz
  have hb0 : (4 / Real.sqrt p.val.2 * (1 + |z - p.val.1| / Real.sqrt p.val.2)) ^ j ≤
      (4 / Real.sqrt p.val.2 * (1 + |z - p.val.1| / Real.sqrt p.val.2)) ^ j *
        (1 + (2 : ℝ) ^ j * (Nat.factorial j : ℝ)) := by
    have hh : 0 ≤ (4 / Real.sqrt p.val.2 * (1 + |z - p.val.1| / Real.sqrt p.val.2)) ^ j *
        (2 : ℝ) ^ j * (Nat.factorial j : ℝ) := by positivity
    nlinarith only [hh]
  have hb' := hb0.trans hb
  have hcoef : (4 / Real.sqrt p.val.2 * (1 + |z - p.val.1| / Real.sqrt p.val.2)) ^ j *
      mixedTimeConstant j l / p.val.2 ^ l ≤ spatialPrefactor j a H * mixedTimeConstant j l / H ^ l := by
    calc
      _ ≤ spatialPrefactor j a H * mixedTimeConstant j l / p.val.2 ^ l :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb' hC) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hK hC) (pow_pos hH l)
        (pow_le_pow_left₀ hH.le p.property.2.1 l)
  have hCs := tail_exponent_lower_bounds a p.val.1 z n ha p.property.1 hz
  have hterm (f : ℝ → ℝ) (C : ℝ)
      (hp : |iteratedDeriv l f p.val.2| ≤
        (4 / Real.sqrt p.val.2 * (1 + |z - p.val.1| / Real.sqrt p.val.2)) ^ j *
          mixedTimeConstant j l / p.val.2 ^ l * Real.exp (-C / (2 * p.val.2)))
      (he : 8 * (n : ℝ) ^ 2 * a ^ 2 ≤ C) :
      ‖iteratedDeriv l f p.val.2‖ ≤
        (spatialPrefactor j a H * mixedTimeConstant j l / H ^ l) * gaussianMajorant a U n := by
    rw [Real.norm_eq_abs]
    exact hp.trans (mul_le_mul hcoef
      (exponent_half_le_majorant a C p.val.2 U n hT p.property.2.2 he)
      (Real.exp_pos _).le (by positivity))
  have hAp := hterm _ _ (spatialImageA_mixed_profile j l a z p.val.2 p.val.1
    ((n : ℤ) + 2) hl ha hz hT p.property.1) hCs.1
  have hAn := hterm _ _ (spatialImageA_mixed_profile j l a z p.val.2 p.val.1
    (-((n : ℤ) + 2)) hl ha hz hT p.property.1) hCs.2.1
  have hBp := hterm _ _ (spatialImageB_mixed_profile j l a z p.val.2 p.val.1
    ((n : ℤ) + 1) hl ha hz hT p.property.1) hCs.2.2.1
  have hBn := hterm _ _ (spatialImageB_mixed_profile j l a z p.val.2 p.val.1
    (-((n : ℤ) + 2)) hl ha hz hT p.property.1) hCs.2.2.2
  have htri (x1 x2 x3 x4 : ℝ) : ‖x1 + x2 - x3 - x4‖ ≤ ‖x1‖ + ‖x2‖ + ‖x3‖ + ‖x4‖ := by
    have h1 := norm_sub_le (x1 + x2 - x3) x4
    have h2 := norm_sub_le (x1 + x2) x3
    have h3 := norm_add_le x1 x2
    linarith only [h1, h2, h3]
  have hs : ‖mixedTailBlock j l a z p.val.2 p.val.1 n‖ ≤
      4 * (spatialPrefactor j a H * mixedTimeConstant j l / H ^ l) * gaussianMajorant a U n := by
    dsimp only [mixedTailBlock]
    have ht := htri
      (iteratedDeriv l (fun S => spatialImageA j a z S p.val.1 ((n : ℤ) + 2)) p.val.2)
      (iteratedDeriv l (fun S => spatialImageA j a z S p.val.1 (-((n : ℤ) + 2))) p.val.2)
      (iteratedDeriv l (fun S => spatialImageB j a z S p.val.1 ((n : ℤ) + 1)) p.val.2)
      (iteratedDeriv l (fun S => spatialImageB j a z S p.val.1 (-((n : ℤ) + 2))) p.val.2)
    linarith only [ht, hAp, hAn, hBp, hBn]
  calc
    _ ≤ _ := hs
    _ = _ := by ring

theorem mixedTailBlock_summable (j l : ℕ) (a z H U : ℝ) (p : StripPoint a H U)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hH : 0 < H) (hHU : H ≤ U) :
    Summable (fun n : ℕ => mixedTailBlock j l a z p.val.2 p.val.1 n) := by
  have hs := (gaussianMajorant_summable a U ha (hH.trans_le hHU)).mul_left
    (4 * spatialPrefactor j a H * mixedTimeConstant j l / H ^ l)
  exact hs.of_norm_bounded (fun n => mixedTailBlock_bound j l a z H U n p hl ha hz hH hHU)

theorem mixedTailBlock_uniformly_convergent (j l : ℕ) (a z H U : ℝ)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hH : 0 < H) (hHU : H ≤ U) :
    TendstoUniformly
      (fun N : ℕ => fun p : StripPoint a H U =>
        ∑ n ∈ Finset.range N, mixedTailBlock j l a z p.val.2 p.val.1 n)
      (fun p : StripPoint a H U => ∑' n : ℕ, mixedTailBlock j l a z p.val.2 p.val.1 n) atTop := by
  have hs := (gaussianMajorant_summable a U ha (hH.trans_le hHU)).mul_left
    (4 * spatialPrefactor j a H * mixedTimeConstant j l / H ^ l)
  exact tendstoUniformly_tsum_nat hs (fun n p => mixedTailBlock_bound j l a z H U n p hl ha hz hH hHU)

theorem mixedTailSum_zero (j : ℕ) (a z T y : ℝ) :
    mixedTailSum j 0 a z T y = spatialTailSum j a z T y := by
  dsimp only [mixedTailSum, spatialTailSum, mixedTailBlock, spatialTailBlock, spatialImageA, spatialImageB]
  simp only [iteratedDeriv_zero]

theorem mixedTailSum_time_hasDerivAt (j l : ℕ) (a z T y : ℝ) (hl : l ≤ 2)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    HasDerivAt (fun S => mixedTailSum j l a z S y)
      (mixedTailSum j (l + 1) a z T y) T := by
  have hH : 0 < T / 2 := by linarith only [hT]
  have hU : 0 < 2 * T := by positivity
  have hHU : T / 2 ≤ 2 * T := by linarith only [hT]
  have hTI : T ∈ Ioo (T / 2) (2 * T) := by constructor <;> linarith only [hT]
  have hl1 : l + 1 ≤ 3 := by omega
  have hu := (gaussianMajorant_summable a (2 * T) ha hU).mul_left
    (4 * spatialPrefactor j a (T / 2) * mixedTimeConstant j (l + 1) / (T / 2) ^ (l + 1))
  have hg : ∀ n S, S ∈ Ioo (T / 2) (2 * T) →
      HasDerivAt (fun V => mixedTailBlock j l a z V y n)
        (mixedTailBlock j (l + 1) a z S y n) S := by
    intro n S hS
    exact mixedTailBlock_time_hasDerivAt j l a z S y n hl (hH.trans hS.1)
  have hg' : ∀ n S, S ∈ Ioo (T / 2) (2 * T) →
      ‖mixedTailBlock j (l + 1) a z S y n‖ ≤
        (4 * spatialPrefactor j a (T / 2) * mixedTimeConstant j (l + 1) / (T / 2) ^ (l + 1)) *
          gaussianMajorant a (2 * T) n := by
    intro n S hS
    exact mixedTailBlock_bound j (l + 1) a z (T / 2) (2 * T) n
      ⟨(y, S), hy, hS.1.le, hS.2.le⟩ hl1 ha hz hH hHU
  have hg0 := mixedTailBlock_summable j l a z T T
    ⟨(y, T), hy, le_rfl, le_rfl⟩ (by omega) ha hz hT le_rfl
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hg hg' hTI hg0 hTI

theorem mixedTailSum_iteratedDeriv (j l : ℕ) (a z T y : ℝ) (hl : l ≤ 3)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    iteratedDeriv l (fun S => spatialTailSum j a z S y) T = mixedTailSum j l a z T y := by
  induction l generalizing T with
  | zero =>
    simpa only [iteratedDeriv_zero] using (mixedTailSum_zero j a z T y).symm
  | succ l ih =>
    have hl2 : l ≤ 2 := by omega
    have heq : iteratedDeriv l (fun S => spatialTailSum j a z S y) =ᶠ[𝓝 T]
        (fun S => mixedTailSum j l a z S y) := by
      filter_upwards [isOpen_Ioi.mem_nhds hT] with S hS
      exact ih S (by omega) hS
    rw [iteratedDeriv_succ]
    exact heq.deriv_eq.trans (mixedTailSum_time_hasDerivAt j l a z T y hl2 ha hz hT hy).deriv

end Shao.C2.IntervalImageMixedConvergence
