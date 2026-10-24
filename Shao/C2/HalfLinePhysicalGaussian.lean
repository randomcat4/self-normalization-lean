import Shao.C2.HalfLineGaussianStep
import Shao.C2.HalfLineExtensionTaylor

noncomputable section
namespace Shao.C2.HalfLinePhysicalGaussian
open Shao.C2.HalfLineGaussianStep Shao.C2.HalfLineMixedProfiles
open Shao.C2.HalfLineSpatialExtension Shao.C2.HalfLineExtensionTaylor
open Shao.C2.GaussianWallEnvelope

def upperCompletion (a y T z : ℝ) : ℝ := completion (a - y) (a - z) T
def lowerCompletion (a y T z : ℝ) : ℝ := completion (a + y) (a + z) T

def upperRemainder (a y T z b : ℝ) : ℝ :=
  upperCompletion a (y + b) (T - b ^ 2) z - upperCompletion a y T z -
    (b - b ^ 2 * (z - y) / T) * deriv (fun w => upperCompletion a w T z) y

def lowerRemainder (a y T z b : ℝ) : ℝ :=
  lowerCompletion a (y + b) (T - b ^ 2) z - lowerCompletion a y T z -
    (b - b ^ 2 * (z - y) / T) * deriv (fun w => lowerCompletion a w T z) y

def upperRetainedRemainder (a y T z b : ℝ) : ℝ :=
  if b ^ 2 ≤ T / 2 ∧ a ≤ y + b then upperRemainder a y T z (a - y)
  else upperRemainder a y T z b

def lowerRetainedRemainder (a y T z b : ℝ) : ℝ :=
  if b ^ 2 ≤ T / 2 ∧ y + b ≤ -a then lowerRemainder a y T z (-a - y)
  else lowerRemainder a y T z b

theorem upperCompletion_eq_spatialExtension (a T z : ℝ) (ha : 0 < a)
    (hT : 0 < T) (hz : z < a) :
    (fun y => upperCompletion a y T z) = upperSpatialExtension a T z := by
  funext y
  by_cases hy : y < a
  · simp [upperCompletion, completion, sub_pos.mpr hy, sub_pos.mpr hz, hT,
      upperSpatialExtension, hy, Shao.C2.HalfLineReflectionFormula.upperReflection]
  · have hu : ¬0 < a - y := by linarith only [hy]
    simp [upperCompletion, completion, hu, upperSpatialExtension, hy]

theorem lowerCompletion_eq_spatialExtension (a T z : ℝ) (ha : 0 < a)
    (hT : 0 < T) (hz : -a < z) :
    (fun y => lowerCompletion a y T z) = lowerSpatialExtension a T z := by
  funext y
  have hv : 0 < a + z := by linarith only [hz]
  by_cases hy : -a < y
  · have hu : 0 < a + y := by linarith only [hy]
    simp [lowerCompletion, completion, hu, hv, hT,
      lowerSpatialExtension, hy, Shao.C2.HalfLineReflectionFormula.lowerReflection]
  · have hu : ¬0 < a + y := by linarith only [hy]
    simp [lowerCompletion, completion, hu, lowerSpatialExtension, hy]

theorem upperCompletion_hasDerivAt (a y T z : ℝ) (ha : 0 < a)
    (hy : y < a) (hT : 0 < T) (hz : z < a) :
    HasDerivAt (fun w => upperCompletion a w T z) (-slopeTime (a - y) (a - z) T) y := by
  rw [upperCompletion_eq_spatialExtension a T z ha hT hz]
  convert upperSpatialExtension_hasDerivAt_interior a T z y hy using 1
  dsimp only [slopeTime]
  ring

theorem lowerCompletion_hasDerivAt (a y T z : ℝ) (ha : 0 < a)
    (hy : -a < y) (hT : 0 < T) (hz : -a < z) :
    HasDerivAt (fun w => lowerCompletion a w T z) (slopeTime (a + y) (a + z) T) y := by
  rw [lowerCompletion_eq_spatialExtension a T z ha hT hz]
  exact lowerSpatialExtension_hasDerivAt_interior a T z y hy

theorem upper_remainder_identity (a y T z b : ℝ) (ha : 0 < a)
    (hy : y < a) (hT : 0 < T) (hz : z < a) :
    upperRemainder a y T z b = localRemainder (a - y) (a - z) T b := by
  rw [upperRemainder, (upperCompletion_hasDerivAt a y T z ha hy hT hz).deriv]
  dsimp only [upperCompletion, localRemainder]
  rw [show a - (y + b) = a - y - b by ring,
    show a - y - (a - z) = z - y by ring]

theorem lower_remainder_identity (a y T z b : ℝ) (ha : 0 < a)
    (hy : -a < y) (hT : 0 < T) (hz : -a < z) :
    lowerRemainder a y T z b = localRemainder (a + y) (a + z) T (-b) := by
  rw [lowerRemainder, (lowerCompletion_hasDerivAt a y T z ha hy hT hz).deriv]
  dsimp only [lowerCompletion, localRemainder]
  rw [show a + y - -b = a + (y + b) by ring, neg_sq,
    show a + y - (a + z) = -(z - y) by ring]
  ring

theorem upper_retained_identity (a y T z b : ℝ) (ha : 0 < a)
    (hy : y < a) (hT : 0 < T) (hz : z < a) :
    upperRetainedRemainder a y T z b = retainedRemainder (a - y) (a - z) T b := by
  have hc : (a ≤ y + b) = (a - y - b ≤ 0) := by
    apply propext
    constructor <;> intro h <;> linarith only [h]
  unfold upperRetainedRemainder retainedRemainder
  simp only [hc]
  split_ifs
  · exact upper_remainder_identity a y T z (a - y) ha hy hT hz
  · exact upper_remainder_identity a y T z b ha hy hT hz

theorem lower_retained_identity (a y T z b : ℝ) (ha : 0 < a)
    (hy : -a < y) (hT : 0 < T) (hz : -a < z) :
    lowerRetainedRemainder a y T z b = retainedRemainder (a + y) (a + z) T (-b) := by
  have hc : (y + b ≤ -a) = (a + y - -b ≤ 0) := by
    apply propext
    constructor <;> intro h <;> linarith only [h]
  unfold lowerRetainedRemainder retainedRemainder
  simp only [hc, neg_sq]
  split_ifs
  · rw [lower_remainder_identity a y T z (-a - y) ha hy hT hz,
      show -(-a - y) = a + y by ring]
  · exact lower_remainder_identity a y T z b ha hy hT hz

theorem upper_retained_gaussian_bound (a y T z b : ℝ) (ha : 0 < a)
    (hy : y < a) (hz : z < a) (hT : 0 < T) (hb : b ^ 2 ≤ T)
    (hzero : T - b ^ 2 = 0 → y + b = z) :
    |upperRetainedRemainder a y T z b| ≤
      8000100 * (|b| / Real.sqrt T) ^ 3 * (1 + |z - y| / Real.sqrt T) ^ 3 *
        Real.exp (-((max (a - y - (|b| + max (z - y) 0)) 0) ^ 2) / T) := by
  rw [upper_retained_identity a y T z b ha hy hT hz]
  have hu : 0 < a - y := sub_pos.mpr hy
  have hv : 0 < a - z := sub_pos.mpr hz
  have hreach : T - b ^ 2 = 0 → a - y - b = a - z := by
    intro h
    have he := hzero h
    linarith only [he]
  have hh := retained_envelope_bound (a - y) (a - z) T b hu hv hT hb hreach
  rw [show a - y - (a - z) = z - y by ring] at hh
  exact hh

theorem lower_retained_gaussian_bound (a y T z b : ℝ) (ha : 0 < a)
    (hy : -a < y) (hz : -a < z) (hT : 0 < T) (hb : b ^ 2 ≤ T)
    (hzero : T - b ^ 2 = 0 → y + b = z) :
    |lowerRetainedRemainder a y T z b| ≤
      8000100 * (|b| / Real.sqrt T) ^ 3 * (1 + |z - y| / Real.sqrt T) ^ 3 *
        Real.exp (-((max (a + y - (|b| + max (y - z) 0)) 0) ^ 2) / T) := by
  rw [lower_retained_identity a y T z b ha hy hT hz]
  have hu : 0 < a + y := by linarith only [hy]
  have hv : 0 < a + z := by linarith only [hz]
  have hb' : (-b) ^ 2 ≤ T := by simpa only [neg_sq] using hb
  have hreach : T - (-b) ^ 2 = 0 → a + y - -b = a + z := by
    intro h
    have he := hzero (by simpa only [neg_sq] using h)
    linarith only [he]
  have hh := retained_envelope_bound (a + y) (a + z) T (-b) hu hv hT hb' hreach
  rw [show a + y - (a + z) = y - z by ring, abs_sub_comm y z] at hh
  simpa only [wallEnvelope, abs_neg] using hh

end Shao.C2.HalfLinePhysicalGaussian
