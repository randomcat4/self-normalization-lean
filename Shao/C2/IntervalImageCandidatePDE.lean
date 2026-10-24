import Shao.C2.IntervalImageTimeDerivatives

noncomputable section
namespace Shao.C2.IntervalImageCandidatePDE
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageSpatialProfiles
open Shao.C2.IntervalImageSpatialConvergence Shao.C2.IntervalImageSpatialDerivatives
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageIntSeries
open Shao.C2.IntervalImageTimeDerivatives

def spatialTailTimeSlope (j : ℕ) (a z T y : ℝ) (n : ℕ) : ℝ :=
  1 / 2 * spatialTailBlock (j + 2) a z T y n +
    (z - y) / T * spatialTailBlock (j + 1) a z T y n -
      (j : ℝ) / T * spatialTailBlock j a z T y n

def timeStripCoefficient (j : ℕ) (a H : ℝ) : ℝ :=
  2 * spatialPrefactor (j + 2) a H +
    (8 * a / H) * spatialPrefactor (j + 1) a H +
      (4 * (j : ℝ) / H) * spatialPrefactor j a H

theorem spatialTailTimeSlope_bound (j : ℕ) (a z H U : ℝ) (n : ℕ)
    (p : StripPoint a H U) (ha : 0 < a) (hz : |z| ≤ a) (hH : 0 < H) (hHU : H ≤ U) :
    ‖spatialTailTimeSlope j a z p.val.2 p.val.1 n‖ ≤
      timeStripCoefficient j a H * gaussianMajorant a U n := by
  have hT : 0 < p.val.2 := hH.trans_le p.property.2.1
  have hd : |z - p.val.1| ≤ 2 * a := by
    have hh := abs_add_le z (-p.val.1)
    rw [abs_neg] at hh
    change |z + -p.val.1| ≤ _
    linarith only [hh, hz, p.property.1]
  have hdq : ‖(z - p.val.1) / p.val.2‖ ≤ 2 * a / H := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hT]
    exact (div_le_div_of_nonneg_right hd hT.le).trans
      (div_le_div_of_nonneg_left (by positivity) hH p.property.2.1)
  have hjq : ‖(j : ℝ) / p.val.2‖ ≤ (j : ℝ) / H := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (j : ℝ) / p.val.2)]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg j) hH p.property.2.1
  have hb (r : ℕ) := spatialTailBlock_bound r a z H U n p ha hz hH hHU
  have htri (x1 x2 x3 : ℝ) : ‖x1 + x2 - x3‖ ≤ ‖x1‖ + ‖x2‖ + ‖x3‖ :=
    (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
  have ht := htri (1 / 2 * spatialTailBlock (j + 2) a z p.val.2 p.val.1 n)
    ((z - p.val.1) / p.val.2 * spatialTailBlock (j + 1) a z p.val.2 p.val.1 n)
    ((j : ℝ) / p.val.2 * spatialTailBlock j a z p.val.2 p.val.1 n)
  simp only [norm_mul] at ht
  have hhalf : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
  rw [hhalf] at ht
  calc
    _ ≤ _ := ht
    _ ≤ 1 / 2 * (4 * spatialPrefactor (j + 2) a H * gaussianMajorant a U n) +
        (2 * a / H) * (4 * spatialPrefactor (j + 1) a H * gaussianMajorant a U n) +
        ((j : ℝ) / H) * (4 * spatialPrefactor j a H * gaussianMajorant a U n) := by
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left (hb (j + 2)) (by norm_num))
          (mul_le_mul hdq (hb (j + 1)) (norm_nonneg _) (by positivity)))
        (mul_le_mul hjq (hb j) (norm_nonneg _) (by positivity))
    _ = _ := by dsimp only [timeStripCoefficient]; ring

theorem spatialTailSum_time_hasDerivAt (j : ℕ) (a z T y : ℝ) (ha : 0 < a)
    (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    HasDerivAt (fun S => spatialTailSum j a z S y)
      (1 / 2 * spatialTailSum (j + 2) a z T y +
        (z - y) / T * spatialTailSum (j + 1) a z T y -
          (j : ℝ) / T * spatialTailSum j a z T y) T := by
  have hH : 0 < T / 2 := by linarith only [hT]
  have hU : 0 < 2 * T := by positivity
  have hHU : T / 2 ≤ 2 * T := by linarith only [hT]
  have hTI : T ∈ Ioo (T / 2) (2 * T) := by constructor <;> linarith only [hT]
  have hu := (gaussianMajorant_summable a (2 * T) ha hU).mul_left
    (timeStripCoefficient j a (T / 2))
  have hg : ∀ n S, S ∈ Ioo (T / 2) (2 * T) →
      HasDerivAt (fun V => spatialTailBlock j a z V y n)
        (spatialTailTimeSlope j a z S y n) S := by
    intro n S hS
    exact spatialTailBlock_time_hasDerivAt j a z S y n (hH.trans hS.1)
  have hg' : ∀ n S, S ∈ Ioo (T / 2) (2 * T) →
      ‖spatialTailTimeSlope j a z S y n‖ ≤
        timeStripCoefficient j a (T / 2) * gaussianMajorant a (2 * T) n := by
    intro n S hS
    exact spatialTailTimeSlope_bound j a z (T / 2) (2 * T) n
      ⟨(y, S), hy, hS.1.le, hS.2.le⟩ ha hz hH hHU
  have hs (r : ℕ) := spatialTailBlock_summable r a z T T
    ⟨(y, T), hy, le_rfl, le_rfl⟩ ha hz hT le_rfl
  have hh := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    hg hg' hTI (hs j) hTI
  have he : (∑' n : ℕ, spatialTailTimeSlope j a z T y n) =
      1 / 2 * spatialTailSum (j + 2) a z T y +
        (z - y) / T * spatialTailSum (j + 1) a z T y -
          (j : ℝ) / T * spatialTailSum j a z T y := by
    dsimp only [spatialTailTimeSlope]
    rw [(((hs (j + 2)).mul_left (1 / 2)).add
      ((hs (j + 1)).mul_left ((z - y) / T))).tsum_sub ((hs j).mul_left ((j : ℝ) / T)),
      ((hs (j + 2)).mul_left (1 / 2)).tsum_add ((hs (j + 1)).mul_left ((z - y) / T)),
      (hs (j + 2)).tsum_mul_left (1 / 2),
      (hs (j + 1)).tsum_mul_left ((z - y) / T), (hs j).tsum_mul_left ((j : ℝ) / T)]
    rfl
  rw [he] at hh
  exact hh

theorem finiteSpatialImages_time_hasDerivAt (j : ℕ) (a z T y : ℝ) (hT : 0 < T) :
    HasDerivAt (fun S => finiteSpatialImages j a z S y)
      (1 / 2 * finiteSpatialImages (j + 2) a z T y +
        (z - y) / T * finiteSpatialImages (j + 1) a z T y -
          (j : ℝ) / T * finiteSpatialImages j a z T y) T := by
  have hf (r : ℕ) (S : ℝ) : finiteSpatialImages r a z S y =
      spatialImageA r a z S y 0 + spatialImageA r a z S y 1 + spatialImageA r a z S y (-1) -
        spatialImageB r a z S y 0 - spatialImageB r a z S y (-1) := by
    simp only [finiteSpatialImages, spatialImageA, spatialImageB, Int.cast_zero,
      Int.cast_one, Int.cast_neg]
  have hh := ((((spatialImageA_time_hasDerivAt j a z T y 0 hT).add
    (spatialImageA_time_hasDerivAt j a z T y 1 hT)).add
    (spatialImageA_time_hasDerivAt j a z T y (-1) hT)).sub
    (spatialImageB_time_hasDerivAt j a z T y 0 hT)).sub
    (spatialImageB_time_hasDerivAt j a z T y (-1) hT)
  convert hh using 1 <;> (try funext S) <;>
    (try simp only [hf, Pi.add_apply, Pi.sub_apply]) <;> ring

theorem imageCandidateSpatial_time_hasDerivAt (j : ℕ) (a z T y : ℝ) (ha : 0 < a)
    (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    HasDerivAt (fun S => imageCandidateSpatial j a z S y)
      (1 / 2 * imageCandidateSpatial (j + 2) a z T y +
        (z - y) / T * imageCandidateSpatial (j + 1) a z T y -
          (j : ℝ) / T * imageCandidateSpatial j a z T y) T := by
  have hh := (finiteSpatialImages_time_hasDerivAt j a z T y hT).add
    (spatialTailSum_time_hasDerivAt j a z T y ha hz hT hy)
  convert hh using 1 <;> (try funext S) <;>
    (try simp only [imageCandidateSpatial, Pi.add_apply]) <;> ring

theorem intervalImageCandidate_time_hasDerivAt (a z T y : ℝ) (ha : 0 < a)
    (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    HasDerivAt (fun S => intervalImageCandidate a z S y)
      (1 / 2 * iteratedDeriv 2 (intervalImageCandidate a z T) y +
        (z - y) / T * iteratedDeriv 1 (intervalImageCandidate a z T) y) T := by
  have hh := imageCandidateSpatial_time_hasDerivAt 0 a z T y ha hz hT (le_of_lt hy)
  change HasDerivAt (fun S => imageCandidateSpatial 0 a z S y) _ T
  rw [intervalImageCandidate_iteratedDeriv 2 a z T y ha hz hT hy,
    intervalImageCandidate_iteratedDeriv 1 a z T y ha hz hT hy]
  simpa only [Nat.zero_add, Nat.cast_zero, zero_div, zero_mul, sub_zero] using hh

end Shao.C2.IntervalImageCandidatePDE
