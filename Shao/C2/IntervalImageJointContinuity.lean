import Shao.C2.IntervalImageMixedTraces

noncomputable section
namespace Shao.C2.IntervalImageJointContinuity
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageSpatialProfiles
open Shao.C2.IntervalImageSpatialConvergence Shao.C2.IntervalImageSpatialDerivatives
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageIntSeries
open Shao.C2.IntervalImageTimeDerivatives Shao.C2.IntervalImageCandidatePDE
open Shao.C2.IntervalImageTimeProfiles Shao.C2.IntervalImageHigherTime Shao.C2.IntervalImageMixedTerms
open Shao.C2.IntervalImageMixedConvergence Shao.C2.IntervalImageMixedCandidate
open Shao.C2.IntervalImageMixedIntSeries Shao.C2.IntervalImageMixedTraces

local instance stripPointTopologicalSpace (a H U : ℝ) : TopologicalSpace (StripPoint a H U) :=
  inferInstanceAs (TopologicalSpace {p : ℝ × ℝ // |p.1| ≤ a ∧ H ≤ p.2 ∧ p.2 ≤ U})

theorem affineSpatial_mixed_strip_continuous (j l : ℕ) (a H U c k : ℝ)
    (hl : l ≤ 3) (hH : 0 < H) :
    Continuous (fun p : StripPoint a H U =>
      iteratedDeriv l (fun S => iteratedDeriv j (affineImageTerm c k S) p.val.1) p.val.2) := by
  have hT (p : StripPoint a H U) : 0 < p.val.2 := hH.trans_le p.property.2.1
  have hcases : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · simpa only [iteratedDeriv_zero, affineImageTerm_iteratedDeriv] using
      (show Continuous (fun p : StripPoint a H U =>
        (-c / p.val.2) ^ j * Real.exp (-(c * p.val.1 + k) / p.val.2)) by
        fun_prop (disch := intro p; have hp := hT p; positivity))
  · have he : (fun p : StripPoint a H U => iteratedDeriv 1
        (fun S => iteratedDeriv j (affineImageTerm c k S) p.val.1) p.val.2) =
        (fun p => affineSpatialTimeSlope j c k p.val.1 p.val.2) := by
      funext p
      rw [iteratedDeriv_succ, iteratedDeriv_zero]
      exact (affineSpatial_time_hasDerivAt j c k p.val.1 p.val.2 (hT p)).deriv
    rw [he]
    dsimp only [affineSpatialTimeSlope]
    fun_prop (disch := intro p; have hp := hT p; positivity)
  · have he : (fun p : StripPoint a H U => iteratedDeriv 2
        (fun S => iteratedDeriv j (affineImageTerm c k S) p.val.1) p.val.2) =
        (fun p => affineSpatialTimeSecond j c k p.val.1 p.val.2) := by
      funext p
      exact affineSpatial_time_iteratedDeriv_two j c k p.val.1 p.val.2 (hT p)
    rw [he]
    dsimp only [affineSpatialTimeSecond]
    fun_prop (disch := intro p; have hp := hT p; positivity)
  · have he : (fun p : StripPoint a H U => iteratedDeriv 3
        (fun S => iteratedDeriv j (affineImageTerm c k S) p.val.1) p.val.2) =
        (fun p => affineSpatialTimeThird j c k p.val.1 p.val.2) := by
      funext p
      exact affineSpatial_time_iteratedDeriv_three j c k p.val.1 p.val.2 (hT p)
    rw [he]
    dsimp only [affineSpatialTimeThird]
    fun_prop (disch := intro p; have hp := hT p; positivity)

theorem mixedImageA_strip_continuous (j l : ℕ) (a z H U : ℝ) (m : ℤ)
    (hl : l ≤ 3) (hH : 0 < H) :
    Continuous (fun p : StripPoint a H U => mixedImageA j l a z p.val.2 p.val.1 m) := by
  let c : ℝ := -4 * (m : ℝ) * a
  let k : ℝ := 8 * (m : ℝ) ^ 2 * a ^ 2 + 4 * (m : ℝ) * a * z
  have hf (S : ℝ) : (fun w => Real.exp (-imageA a w z (m : ℝ) / S)) =
      affineImageTerm c k S := by
    funext w
    dsimp only [affineImageTerm]
    congr 1
    dsimp only [imageA, c, k]
    ring
  have hwhole (y : ℝ) : (fun S => spatialImageA j a z S y m) =
      (fun S => iteratedDeriv j (affineImageTerm c k S) y) := by
    funext S
    rw [spatialImageA, hf]
  have he : (fun p : StripPoint a H U => mixedImageA j l a z p.val.2 p.val.1 m) =
      (fun p => iteratedDeriv l (fun S => iteratedDeriv j (affineImageTerm c k S) p.val.1) p.val.2) := by
    funext p
    rw [mixedImageA, hwhole]
  rw [he]
  exact affineSpatial_mixed_strip_continuous j l a H U c k hl hH

theorem mixedImageB_strip_continuous (j l : ℕ) (a z H U : ℝ) (m : ℤ)
    (hl : l ≤ 3) (hH : 0 < H) :
    Continuous (fun p : StripPoint a H U => mixedImageB j l a z p.val.2 p.val.1 m) := by
  let c : ℝ := 2 * (z + (2 * (m : ℝ) + 1) * a)
  let k : ℝ := 2 * ((2 * (m : ℝ) + 1) * a) * (z + (2 * (m : ℝ) + 1) * a)
  have hf (S : ℝ) : (fun w => Real.exp (-imageB a w z (m : ℝ) / S)) =
      affineImageTerm c k S := by
    funext w
    dsimp only [affineImageTerm]
    congr 1
    dsimp only [imageB, c, k]
    ring
  have hwhole (y : ℝ) : (fun S => spatialImageB j a z S y m) =
      (fun S => iteratedDeriv j (affineImageTerm c k S) y) := by
    funext S
    rw [spatialImageB, hf]
  have he : (fun p : StripPoint a H U => mixedImageB j l a z p.val.2 p.val.1 m) =
      (fun p => iteratedDeriv l (fun S => iteratedDeriv j (affineImageTerm c k S) p.val.1) p.val.2) := by
    funext p
    rw [mixedImageB, hwhole]
  rw [he]
  exact affineSpatial_mixed_strip_continuous j l a H U c k hl hH

theorem mixedTailBlock_strip_continuous (j l : ℕ) (a z H U : ℝ) (n : ℕ)
    (hl : l ≤ 3) (hH : 0 < H) :
    Continuous (fun p : StripPoint a H U => mixedTailBlock j l a z p.val.2 p.val.1 n) := by
  change Continuous (fun p : StripPoint a H U =>
    mixedImageA j l a z p.val.2 p.val.1 ((n : ℤ) + 2) +
    mixedImageA j l a z p.val.2 p.val.1 (-((n : ℤ) + 2)) -
    mixedImageB j l a z p.val.2 p.val.1 ((n : ℤ) + 1) -
    mixedImageB j l a z p.val.2 p.val.1 (-((n : ℤ) + 2)))
  exact (((mixedImageA_strip_continuous j l a z H U ((n : ℤ) + 2) hl hH).add
    (mixedImageA_strip_continuous j l a z H U (-((n : ℤ) + 2)) hl hH)).sub
    (mixedImageB_strip_continuous j l a z H U ((n : ℤ) + 1) hl hH)).sub
    (mixedImageB_strip_continuous j l a z H U (-((n : ℤ) + 2)) hl hH)

theorem mixedTailSum_strip_continuous (j l : ℕ) (a z H U : ℝ)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hH : 0 < H) (hHU : H ≤ U) :
    Continuous (fun p : StripPoint a H U => mixedTailSum j l a z p.val.2 p.val.1) := by
  apply continuous_tsum (f := fun (n : ℕ) (p : StripPoint a H U) => mixedTailBlock j l a z p.val.2 p.val.1 n)
    (u := fun n => (4 * spatialPrefactor j a H * mixedTimeConstant j l / H ^ l) * gaussianMajorant a U n)
  · intro n
    exact mixedTailBlock_strip_continuous j l a z H U n hl hH
  · exact (gaussianMajorant_summable a U ha (hH.trans_le hHU)).mul_left _
  · intro n p
    exact mixedTailBlock_bound j l a z H U n p hl ha hz hH hHU

theorem mixedFiniteImages_strip_continuous (j l : ℕ) (a z H U : ℝ)
    (hl : l ≤ 3) (hH : 0 < H) :
    Continuous (fun p : StripPoint a H U => mixedFiniteImages j l a z p.val.2 p.val.1) := by
  change Continuous (fun p : StripPoint a H U =>
    mixedImageA j l a z p.val.2 p.val.1 0 + mixedImageA j l a z p.val.2 p.val.1 1 +
    mixedImageA j l a z p.val.2 p.val.1 (-1) - mixedImageB j l a z p.val.2 p.val.1 0 -
    mixedImageB j l a z p.val.2 p.val.1 (-1))
  exact ((((mixedImageA_strip_continuous j l a z H U 0 hl hH).add
    (mixedImageA_strip_continuous j l a z H U 1 hl hH)).add
    (mixedImageA_strip_continuous j l a z H U (-1) hl hH)).sub
    (mixedImageB_strip_continuous j l a z H U 0 hl hH)).sub
    (mixedImageB_strip_continuous j l a z H U (-1) hl hH)

theorem mixedImageCandidate_strip_continuous (j l : ℕ) (a z H U : ℝ)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hH : 0 < H) (hHU : H ≤ U) :
    Continuous (fun p : StripPoint a H U => mixedImageCandidate j l a z p.val.2 p.val.1) := by
  exact (mixedFiniteImages_strip_continuous j l a z H U hl hH).add
    (mixedTailSum_strip_continuous j l a z H U hl ha hz hH hHU)

theorem mixedImageCandidate_joint_continuousOn (j l : ℕ) (a z H U : ℝ)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hH : 0 < H) (hHU : H ≤ U) :
    ContinuousOn (fun p : ℝ × ℝ => mixedImageCandidate j l a z p.2 p.1)
      (Icc (-a) a ×ˢ Icc H U) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun p : {p : ℝ × ℝ // p ∈ Icc (-a) a ×ˢ Icc H U} =>
    mixedImageCandidate j l a z p.val.2 p.val.1)
  let g : {p : ℝ × ℝ // p ∈ Icc (-a) a ×ˢ Icc H U} → StripPoint a H U :=
    fun p => ⟨p.val, abs_le.2 p.property.1, p.property.2⟩
  have hg : Continuous g := continuous_subtype_val.subtype_mk _
  have hc := (mixedImageCandidate_strip_continuous j l a z H U hl ha hz hH hHU).comp hg
  have he : ((fun p : StripPoint a H U => mixedImageCandidate j l a z p.val.2 p.val.1) ∘ g) =
      (fun p : {p : ℝ × ℝ // p ∈ Icc (-a) a ×ˢ Icc H U} =>
        mixedImageCandidate j l a z p.val.2 p.val.1) := by
    funext p
    rfl
  rw [he] at hc
  exact hc

end Shao.C2.IntervalImageJointContinuity

