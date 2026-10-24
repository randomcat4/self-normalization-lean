import Shao.C2.IntervalImageMixedSpatialDerivatives

noncomputable section
namespace Shao.C2.IntervalImageLocalRegularity
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageMixedTerms
open Shao.C2.IntervalImageMixedConvergence Shao.C2.IntervalImageMixedCandidate
open Shao.C2.IntervalImageJointContinuity Shao.C2.IntervalImageMixedSpatialDerivatives

theorem mixedImageCandidate_continuousAt (j l : ℕ) (a z T y : ℝ) (hl : l ≤ 3)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    ContinuousAt (fun p : ℝ × ℝ => mixedImageCandidate j l a z p.2 p.1) (y, T) := by
  have hH : 0 < T / 2 := by linarith only [hT]
  have hHU : T / 2 ≤ 2 * T := by linarith only [hT]
  have hc := mixedImageCandidate_joint_continuousOn j l a z (T / 2) (2 * T) hl ha hz hH hHU
  have hyN : Icc (-a) a ∈ 𝓝 y := Icc_mem_nhds (abs_lt.mp hy).1 (abs_lt.mp hy).2
  have hTN : Icc (T / 2) (2 * T) ∈ 𝓝 T :=
    Icc_mem_nhds (by linarith only [hT]) (by linarith only [hT])
  have hrect : Icc (-a) a ×ˢ Icc (T / 2) (2 * T) ∈ 𝓝 (y, T) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod hyN hTN
  exact (hc (y, T) ⟨abs_le.mp hy.le,
    by linarith only [hT], by linarith only [hT]⟩).continuousAt hrect

theorem intervalImageCandidate_mixed_continuousAt (j l : ℕ) (a z T y : ℝ) (hl : l ≤ 3)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    ContinuousAt (fun p : ℝ × ℝ =>
      iteratedDeriv l (fun S => iteratedDeriv j (intervalImageCandidate a z S) p.1) p.2) (y, T) := by
  have hN : Ioo (-a) a ×ˢ Ioi 0 ∈ 𝓝 (y, T) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod (isOpen_Ioo.mem_nhds (abs_lt.mp hy)) (isOpen_Ioi.mem_nhds hT)
  have heq : (fun p : ℝ × ℝ => iteratedDeriv l
      (fun S => iteratedDeriv j (intervalImageCandidate a z S) p.1) p.2)
      =ᶠ[𝓝 (y, T)] (fun p => mixedImageCandidate j l a z p.2 p.1) := by
    filter_upwards [hN] with p hp
    exact intervalImageCandidate_mixed_iteratedDeriv j l a z p.2 p.1 hl ha hz hp.2 (abs_lt.mpr hp.1)
  change Tendsto _ (𝓝 (y, T))
    (𝓝 (iteratedDeriv l (fun S => iteratedDeriv j (intervalImageCandidate a z S) y) T))
  rw [intervalImageCandidate_mixed_iteratedDeriv j l a z T y hl ha hz hT hy]
  exact (mixedImageCandidate_continuousAt j l a z T y hl ha hz hT hy).congr' heq.symm

theorem intervalImageCandidate_mixed_continuousOn (j l : ℕ) (a z : ℝ) (hl : l ≤ 3)
    (ha : 0 < a) (hz : |z| ≤ a) :
    ContinuousOn (fun p : ℝ × ℝ =>
      iteratedDeriv l (fun S => iteratedDeriv j (intervalImageCandidate a z S) p.1) p.2)
      (Ioo (-a) a ×ˢ Ioi 0) := by
  intro p hp
  exact (intervalImageCandidate_mixed_continuousAt j l a z p.2 p.1 hl ha hz hp.2
    (abs_lt.mpr hp.1)).continuousWithinAt

theorem intervalImageCandidate_mixed_time_hasDerivAt (j l : ℕ) (a z T y : ℝ) (hl : l ≤ 2)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    HasDerivAt (iteratedDeriv l (fun S => iteratedDeriv j (intervalImageCandidate a z S) y))
      (iteratedDeriv (l + 1) (fun S => iteratedDeriv j (intervalImageCandidate a z S) y) T) T := by
  have hl3 : l ≤ 3 := by omega
  have hlp3 : l + 1 ≤ 3 := by omega
  have heq : iteratedDeriv l (fun S => iteratedDeriv j (intervalImageCandidate a z S) y)
      =ᶠ[𝓝 T] (fun S => mixedImageCandidate j l a z S y) := by
    filter_upwards [isOpen_Ioi.mem_nhds hT] with S hS
    exact intervalImageCandidate_mixed_iteratedDeriv j l a z S y hl3 ha hz hS hy
  rw [intervalImageCandidate_mixed_iteratedDeriv j (l + 1) a z T y hlp3 ha hz hT hy]
  exact (mixedImageCandidate_time_hasDerivAt j l a z T y hl ha hz hT hy.le).congr_of_eventuallyEq heq

end Shao.C2.IntervalImageLocalRegularity

