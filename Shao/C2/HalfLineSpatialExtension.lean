import Shao.C2.HalfLineCompensatedBounds
import Shao.C2.HalfLineWallProfiles

noncomputable section
namespace Shao.C2.HalfLineSpatialExtension
open scoped Topology Classical
open Shao.C2.HalfLineReflectionFormula Shao.C2.CompletionFirstProfile
open Shao.C2.HalfLineSpatialProfiles Shao.C2.HalfLineWallProfiles

def upperSpatialExtension (a T z y : ℝ) : ℝ :=
  if y < a then upperReflection a y T z else 0
def lowerSpatialExtension (a T z y : ℝ) : ℝ :=
  if -a < y then lowerReflection a y T z else 0

theorem upperSpatialExtension_eq_closed (a T z y : ℝ) (hy : y ≤ a) :
    upperSpatialExtension a T z y = upperReflection a y T z := by
  rcases lt_or_eq_of_le hy with hlt | hyeq
  · exact if_pos hlt
  · subst y
    simp only [upperSpatialExtension, lt_self_iff_false, if_false, upperReflection,
      sub_self, mul_zero, zero_mul, zero_div, Real.exp_zero, sub_self]

theorem lowerSpatialExtension_eq_closed (a T z y : ℝ) (hy : -a ≤ y) :
    lowerSpatialExtension a T z y = lowerReflection a y T z := by
  rcases lt_or_eq_of_le hy with hlt | hyeq
  · exact if_pos hlt
  · subst y
    simp only [lowerSpatialExtension, lt_self_iff_false, if_false, lowerReflection,
      add_neg_cancel, mul_zero, zero_mul, zero_div, Real.exp_zero, sub_self]

theorem upperSpatialExtension_iteratedWithin_eq (j : ℕ) (a T z y : ℝ) (hy : y ≤ a) :
    iteratedDerivWithin j (fun x : ℝ => upperSpatialExtension a T z x - 1) (Set.Iic a) y =
      iteratedDeriv j (fun x : ℝ => upperReflection a x T z - 1) y := by
  have heq : Set.EqOn (fun x : ℝ => upperSpatialExtension a T z x - 1)
      (fun x : ℝ => upperReflection a x T z - 1) (Set.Iic a) := by
    intro x hx
    change upperSpatialExtension a T z x - 1 = upperReflection a x T z - 1
    rw [upperSpatialExtension_eq_closed a T z x hx]
  rw [(iteratedDerivWithin_congr (n := j) heq) hy]
  exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Iic a)
    (by dsimp only [upperReflection]; fun_prop) hy

theorem lowerSpatialExtension_iteratedWithin_eq (j : ℕ) (a T z y : ℝ) (hy : -a ≤ y) :
    iteratedDerivWithin j (fun x : ℝ => lowerSpatialExtension a T z x - 1) (Set.Ici (-a)) y =
      iteratedDeriv j (fun x : ℝ => lowerReflection a x T z - 1) y := by
  have heq : Set.EqOn (fun x : ℝ => lowerSpatialExtension a T z x - 1)
      (fun x : ℝ => lowerReflection a x T z - 1) (Set.Ici (-a)) := by
    intro x hx
    change lowerSpatialExtension a T z x - 1 = lowerReflection a x T z - 1
    rw [lowerSpatialExtension_eq_closed a T z x hx]
  rw [(iteratedDerivWithin_congr (n := j) heq) hy]
  exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici (-a))
    (by dsimp only [lowerReflection]; fun_prop) hy

theorem upperSpatialExtension_iteratedWithin_profile (j : ℕ) (hj : 0 < j)
    (a T z y : ℝ) (hT : 0 < T) (hy : y ≤ a) (hz : z < a) :
    |iteratedDerivWithin j (fun x : ℝ => upperSpatialExtension a T z x - 1) (Set.Iic a) y| ≤
      (8 * (j : ℝ) / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
        upperProfile a y T z := by
  rw [upperSpatialExtension_iteratedWithin_eq j a T z y hy]
  exact upperReflection_closed_iterated_profile j hj a y T z hT hy hz

theorem lowerSpatialExtension_iteratedWithin_profile (j : ℕ) (hj : 0 < j)
    (a T z y : ℝ) (hT : 0 < T) (hy : -a ≤ y) (hz : -a < z) :
    |iteratedDerivWithin j (fun x : ℝ => lowerSpatialExtension a T z x - 1) (Set.Ici (-a)) y| ≤
      (8 * (j : ℝ) / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
        lowerProfile a y T z := by
  rw [lowerSpatialExtension_iteratedWithin_eq j a T z y hy]
  exact lowerReflection_closed_iterated_profile j hj a y T z hT hy hz

theorem upperSpatialExtension_wall_hasDerivWithinAt (a T z : ℝ) (ha : 0 < a)
    (hT : 0 < T) (hz : z < a) :
    HasDerivWithinAt (upperSpatialExtension a T z) (-(2 * (a - z) / T)) (Set.Iic a) a := by
  have h : HasDerivWithinAt (fun x : ℝ => upperReflection a x T z)
      (-(2 * (a - z) / T)) (Set.Iic a) a := by
    simpa only [sub_self, mul_zero, zero_mul, zero_div, Real.exp_zero, mul_one] using
      (upperReflection_hasDerivAt a a T z).hasDerivWithinAt (s := Set.Iic a)
  exact h.congr_of_mem (f₁ := upperSpatialExtension a T z)
    (fun x hx => upperSpatialExtension_eq_closed a T z x hx) (by change (a : ℝ) ≤ a; exact le_refl a)

theorem lowerSpatialExtension_wall_hasDerivWithinAt (a T z : ℝ) (ha : 0 < a)
    (hT : 0 < T) (hz : -a < z) :
    HasDerivWithinAt (lowerSpatialExtension a T z) (2 * (a + z) / T) (Set.Ici (-a)) (-a) := by
  have h : HasDerivWithinAt (fun x : ℝ => lowerReflection a x T z)
      (2 * (a + z) / T) (Set.Ici (-a)) (-a) := by
    simpa only [add_neg_cancel, mul_zero, zero_mul, zero_div, Real.exp_zero, mul_one] using
      (lowerReflection_hasDerivAt a (-a) T z).hasDerivWithinAt (s := Set.Ici (-a))
  exact h.congr_of_mem (f₁ := lowerSpatialExtension a T z)
    (fun x hx => lowerSpatialExtension_eq_closed a T z x hx) (by change (-a : ℝ) ≤ -a; exact le_refl (-a))

end Shao.C2.HalfLineSpatialExtension
