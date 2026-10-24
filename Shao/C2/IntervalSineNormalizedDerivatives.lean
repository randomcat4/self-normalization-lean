import Shao.C2.IntervalReciprocalHighTime

noncomputable section
namespace Shao.C2.IntervalSineNormalizedDerivatives
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalReciprocalDerivatives Shao.C2.IntervalSineSeries

def normalizedSineCandidate (a z T y : ℝ) : ℝ :=
  reciprocalFreeDensity z T y * mixedSineSeries 0 0 a z T y

def normalizedMixedFamily (j l : ℕ) (a z T y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), ∑ k ∈ Finset.range (l + 1),
    (Nat.choose j i : ℝ) * (Nat.choose l k : ℝ) *
      reciprocalMixedFamily i k z T y * mixedSineSeries (j - i) (l - k) a z T y

theorem normalizedMixedFamily_zero (a z T y : ℝ) :
    normalizedMixedFamily 0 0 a z T y = normalizedSineCandidate a z T y := by
  norm_num [normalizedMixedFamily, normalizedSineCandidate, Finset.sum_range_succ,
    reciprocalMixedFamily, reciprocalCoefficient.eq_1]

theorem normalizedMixedFamily_spatial_hasDerivAt (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 2) (ha : 0 < a) (hT : 0 < T) :
    HasDerivAt (normalizedMixedFamily j l a z T)
      (normalizedMixedFamily (j + 1) l a z T y) y := by
  have cases : (j = 0 ∧ l = 0) ∨ (j = 1 ∧ l = 0) ∨ (j = 2 ∧ l = 0) ∨
      (j = 0 ∧ l = 1) ∨ (j = 1 ∧ l = 1) ∨ (j = 0 ∧ l = 2) := by omega
  rcases cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hg := ((reciprocalMixedFamily_spatial_hasDerivAt 0 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_spatial_hasDerivAt 0 0 a z T y ha hT))
    convert hg using 1 <;>
      (try funext w) <;>
      norm_num [normalizedMixedFamily, Finset.sum_range_succ, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;> ring
  · have hg := (((reciprocalMixedFamily_spatial_hasDerivAt 0 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_spatial_hasDerivAt 1 0 a z T y ha hT))).add (((reciprocalMixedFamily_spatial_hasDerivAt 1 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_spatial_hasDerivAt 0 0 a z T y ha hT)))
    convert hg using 1 <;>
      (try funext w) <;>
      norm_num [normalizedMixedFamily, Finset.sum_range_succ, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;> ring
  · have hg := ((((reciprocalMixedFamily_spatial_hasDerivAt 0 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_spatial_hasDerivAt 2 0 a z T y ha hT))).add (((hasDerivAt_const y (2 : ℝ))).mul (((reciprocalMixedFamily_spatial_hasDerivAt 1 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_spatial_hasDerivAt 1 0 a z T y ha hT))))).add (((reciprocalMixedFamily_spatial_hasDerivAt 2 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_spatial_hasDerivAt 0 0 a z T y ha hT)))
    convert hg using 1 <;>
      (try funext w) <;>
      norm_num [normalizedMixedFamily, Finset.sum_range_succ, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;> ring
  · have hg := (((reciprocalMixedFamily_spatial_hasDerivAt 0 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_spatial_hasDerivAt 0 1 a z T y ha hT))).add (((reciprocalMixedFamily_spatial_hasDerivAt 0 1 z T y (by norm_num) hT)).mul ((mixedSineSeries_spatial_hasDerivAt 0 0 a z T y ha hT)))
    convert hg using 1 <;>
      (try funext w) <;>
      norm_num [normalizedMixedFamily, Finset.sum_range_succ, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;> ring
  · have hg := (((((reciprocalMixedFamily_spatial_hasDerivAt 0 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_spatial_hasDerivAt 1 1 a z T y ha hT))).add (((reciprocalMixedFamily_spatial_hasDerivAt 0 1 z T y (by norm_num) hT)).mul ((mixedSineSeries_spatial_hasDerivAt 1 0 a z T y ha hT)))).add (((reciprocalMixedFamily_spatial_hasDerivAt 1 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_spatial_hasDerivAt 0 1 a z T y ha hT)))).add (((reciprocalMixedFamily_spatial_hasDerivAt 1 1 z T y (by norm_num) hT)).mul ((mixedSineSeries_spatial_hasDerivAt 0 0 a z T y ha hT)))
    convert hg using 1 <;>
      (try funext w) <;>
      norm_num [normalizedMixedFamily, Finset.sum_range_succ, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;> ring
  · have hg := ((((reciprocalMixedFamily_spatial_hasDerivAt 0 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_spatial_hasDerivAt 0 2 a z T y ha hT))).add (((hasDerivAt_const y (2 : ℝ))).mul (((reciprocalMixedFamily_spatial_hasDerivAt 0 1 z T y (by norm_num) hT)).mul ((mixedSineSeries_spatial_hasDerivAt 0 1 a z T y ha hT))))).add (((reciprocalMixedFamily_spatial_hasDerivAt 0 2 z T y (by norm_num) hT)).mul ((mixedSineSeries_spatial_hasDerivAt 0 0 a z T y ha hT)))
    convert hg using 1 <;>
      (try funext w) <;>
      norm_num [normalizedMixedFamily, Finset.sum_range_succ, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;> ring

theorem normalizedMixedFamily_time_hasDerivAt (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 2) (ha : 0 < a) (hT : 0 < T) :
    HasDerivAt (fun S => normalizedMixedFamily j l a z S y)
      (normalizedMixedFamily j (l + 1) a z T y) T := by
  have cases : (j = 0 ∧ l = 0) ∨ (j = 1 ∧ l = 0) ∨ (j = 2 ∧ l = 0) ∨
      (j = 0 ∧ l = 1) ∨ (j = 1 ∧ l = 1) ∨ (j = 0 ∧ l = 2) := by omega
  rcases cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hg := ((reciprocalMixedFamily_time_hasDerivAt 0 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_time_hasDerivAt 0 0 a z T y ha hT))
    convert hg using 1 <;>
      (try funext w) <;>
      norm_num [normalizedMixedFamily, Finset.sum_range_succ, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;> ring
  · have hg := (((reciprocalMixedFamily_time_hasDerivAt 0 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_time_hasDerivAt 1 0 a z T y ha hT))).add (((reciprocalMixedFamily_time_hasDerivAt 1 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_time_hasDerivAt 0 0 a z T y ha hT)))
    convert hg using 1 <;>
      (try funext w) <;>
      norm_num [normalizedMixedFamily, Finset.sum_range_succ, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;> ring
  · have hg := ((((reciprocalMixedFamily_time_hasDerivAt 0 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_time_hasDerivAt 2 0 a z T y ha hT))).add (((hasDerivAt_const T (2 : ℝ))).mul (((reciprocalMixedFamily_time_hasDerivAt 1 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_time_hasDerivAt 1 0 a z T y ha hT))))).add (((reciprocalMixedFamily_time_hasDerivAt 2 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_time_hasDerivAt 0 0 a z T y ha hT)))
    convert hg using 1 <;>
      (try funext w) <;>
      norm_num [normalizedMixedFamily, Finset.sum_range_succ, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;> ring
  · have hg := (((reciprocalMixedFamily_time_hasDerivAt 0 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_time_hasDerivAt 0 1 a z T y ha hT))).add (((reciprocalMixedFamily_time_hasDerivAt 0 1 z T y (by norm_num) hT)).mul ((mixedSineSeries_time_hasDerivAt 0 0 a z T y ha hT)))
    convert hg using 1 <;>
      (try funext w) <;>
      norm_num [normalizedMixedFamily, Finset.sum_range_succ, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;> ring
  · have hg := (((((reciprocalMixedFamily_time_hasDerivAt 0 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_time_hasDerivAt 1 1 a z T y ha hT))).add (((reciprocalMixedFamily_time_hasDerivAt 0 1 z T y (by norm_num) hT)).mul ((mixedSineSeries_time_hasDerivAt 1 0 a z T y ha hT)))).add (((reciprocalMixedFamily_time_hasDerivAt 1 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_time_hasDerivAt 0 1 a z T y ha hT)))).add (((reciprocalMixedFamily_time_hasDerivAt 1 1 z T y (by norm_num) hT)).mul ((mixedSineSeries_time_hasDerivAt 0 0 a z T y ha hT)))
    convert hg using 1 <;>
      (try funext w) <;>
      norm_num [normalizedMixedFamily, Finset.sum_range_succ, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;> ring
  · have hg := ((((reciprocalMixedFamily_time_hasDerivAt 0 0 z T y (by norm_num) hT)).mul ((mixedSineSeries_time_hasDerivAt 0 2 a z T y ha hT))).add (((hasDerivAt_const T (2 : ℝ))).mul (((reciprocalMixedFamily_time_hasDerivAt 0 1 z T y (by norm_num) hT)).mul ((mixedSineSeries_time_hasDerivAt 0 1 a z T y ha hT))))).add (((reciprocalMixedFamily_time_hasDerivAt 0 2 z T y (by norm_num) hT)).mul ((mixedSineSeries_time_hasDerivAt 0 0 a z T y ha hT)))
    convert hg using 1 <;>
      (try funext w) <;>
      norm_num [normalizedMixedFamily, Finset.sum_range_succ, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;> ring

theorem normalizedMixedFamily_spatial_iteratedDeriv (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 3) (ha : 0 < a) (hT : 0 < T) :
    iteratedDeriv j (normalizedMixedFamily 0 l a z T) y = normalizedMixedFamily j l a z T y := by
  induction j generalizing y with
  | zero => rfl
  | succ j ih =>
    have hjl2 : j + l ≤ 2 := by omega
    have heq : iteratedDeriv j (normalizedMixedFamily 0 l a z T) = normalizedMixedFamily j l a z T := by
      funext w
      exact ih w (by omega)
    rw [iteratedDeriv_succ, heq]
    exact (normalizedMixedFamily_spatial_hasDerivAt j l a z T y hjl2 ha hT).deriv

theorem normalizedSineCandidate_spatial_iteratedDeriv (j : ℕ) (a z T y : ℝ)
    (hj : j ≤ 3) (ha : 0 < a) (hT : 0 < T) :
    iteratedDeriv j (normalizedSineCandidate a z T) y = normalizedMixedFamily j 0 a z T y := by
  have heq : normalizedSineCandidate a z T = normalizedMixedFamily 0 0 a z T := by
    funext w
    exact (normalizedMixedFamily_zero a z T w).symm
  rw [heq]
  exact normalizedMixedFamily_spatial_iteratedDeriv j 0 a z T y (by omega) ha hT

theorem normalizedSineCandidate_mixed_iteratedDeriv (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 3) (ha : 0 < a) (hT : 0 < T) :
    iteratedDeriv l (fun S => iteratedDeriv j (normalizedSineCandidate a z S) y) T =
      normalizedMixedFamily j l a z T y := by
  induction l generalizing T with
  | zero =>
    simpa only [iteratedDeriv_zero] using
      normalizedSineCandidate_spatial_iteratedDeriv j a z T y (by omega) ha hT
  | succ l ih =>
    have hjl2 : j + l ≤ 2 := by omega
    have heq : iteratedDeriv l (fun S => iteratedDeriv j (normalizedSineCandidate a z S) y) =ᶠ[𝓝 T]
        (fun S => normalizedMixedFamily j l a z S y) := by
      filter_upwards [isOpen_Ioi.mem_nhds hT] with S hS
      exact ih S (by omega) hS
    rw [iteratedDeriv_succ]
    exact heq.deriv_eq.trans (normalizedMixedFamily_time_hasDerivAt j l a z T y hjl2 ha hT).deriv

theorem normalizedSineCandidate_mixed_commutation (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 3) (ha : 0 < a) (hT : 0 < T) :
    iteratedDeriv j (fun w => iteratedDeriv l (fun S => normalizedSineCandidate a z S w) T) y =
      iteratedDeriv l (fun S => iteratedDeriv j (normalizedSineCandidate a z S) y) T := by
  have heq : (fun w => iteratedDeriv l (fun S => normalizedSineCandidate a z S w) T) =
      normalizedMixedFamily 0 l a z T := by
    funext w
    simpa only [iteratedDeriv_zero] using
      normalizedSineCandidate_mixed_iteratedDeriv 0 l a z T w (by omega) ha hT
  rw [heq, normalizedMixedFamily_spatial_iteratedDeriv j l a z T y hjl ha hT,
    normalizedSineCandidate_mixed_iteratedDeriv j l a z T y hjl ha hT]

end Shao.C2.IntervalSineNormalizedDerivatives
