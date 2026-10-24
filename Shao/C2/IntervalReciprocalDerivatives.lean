import Shao.C2.IntervalSineHighTime
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
namespace Shao.C2.IntervalReciprocalDerivatives
open MeasureTheory Set Filter
open scoped BigOperators Topology

def reciprocalFreeDensity (z T y : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi) * Real.sqrt T * Real.exp ((z - y) ^ 2 / (2 * T))

def reciprocalCoefficient (j l : ℕ) (d T : ℝ) : ℝ :=
  match j, l with
  | 0, 0 => 1
  | 1, 0 => -d / T
  | 2, 0 => 1 / T + d ^ 2 / T ^ 2
  | 3, 0 => -(3 * d / T ^ 2 + d ^ 3 / T ^ 3)
  | 0, 1 => 1 / (2 * T) - d ^ 2 / (2 * T ^ 2)
  | 1, 1 => d / (2 * T ^ 2) + d ^ 3 / (2 * T ^ 3)
  | 2, 1 => -1 / (2 * T ^ 2) - 2 * d ^ 2 / T ^ 3 - d ^ 4 / (2 * T ^ 4)
  | 0, 2 => -1 / (4 * T ^ 2) + d ^ 2 / (2 * T ^ 3) + d ^ 4 / (4 * T ^ 4)
  | 1, 2 => -(3 * d / (4 * T ^ 3) + 3 * d ^ 3 / (2 * T ^ 4) + d ^ 5 / (4 * T ^ 5))
  | 0, 3 => 3 / (8 * T ^ 3) - 9 * d ^ 2 / (8 * T ^ 4) -
      9 * d ^ 4 / (8 * T ^ 5) - d ^ 6 / (8 * T ^ 6)
  | _, _ => 0

def reciprocalMixedFamily (j l : ℕ) (z T y : ℝ) : ℝ :=
  reciprocalCoefficient j l (z - y) T * reciprocalFreeDensity z T y

theorem reciprocalFreeDensity_mul_free (z T y : ℝ) (hT : 0 < T) :
    reciprocalFreeDensity z T y *
      ((1 / Real.sqrt (2 * Real.pi * T)) * Real.exp (-(z - y) ^ 2 / (2 * T))) = 1 := by
  have hR : 0 < Real.sqrt (2 * Real.pi) * Real.sqrt T := by positivity
  have he : -(z - y) ^ 2 / (2 * T) = -((z - y) ^ 2 / (2 * T)) := by ring
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi) T, he]
  dsimp only [reciprocalFreeDensity]
  calc
    _ = (Real.sqrt (2 * Real.pi) * Real.sqrt T *
        (1 / (Real.sqrt (2 * Real.pi) * Real.sqrt T))) *
        (Real.exp ((z - y) ^ 2 / (2 * T)) * Real.exp (-((z - y) ^ 2 / (2 * T)))) := by ring
    _ = 1 := by
      simp only [one_div, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      exact mul_inv_cancel₀ (ne_of_gt hR)

theorem reciprocalFreeDensity_spatial_hasDerivAt (z T y : ℝ) (hT : 0 < T) :
    HasDerivAt (reciprocalFreeDensity z T)
      ((-(z - y) / T) * reciprocalFreeDensity z T y) y := by
  have hd : HasDerivAt (fun w : ℝ => z - w) (-1) y := by
    simpa only [id_eq] using (hasDerivAt_id y).const_sub z
  have he := ((hd.pow 2).div_const (2 * T)).exp
  have hg := he.const_mul (Real.sqrt (2 * Real.pi) * Real.sqrt T)
  convert hg using 1 <;>
    (try funext w) <;>
    dsimp only [reciprocalFreeDensity, Pi.pow_apply, Pi.mul_apply,
      Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;>
    ring_nf <;> field_simp [ne_of_gt hT] <;> ring

theorem reciprocalFreeDensity_time_hasDerivAt (z T y : ℝ) (hT : 0 < T) :
    HasDerivAt (fun S => reciprocalFreeDensity z S y)
      ((1 / (2 * T) - (z - y) ^ 2 / (2 * T ^ 2)) * reciprocalFreeDensity z T y) T := by
  have hs : HasDerivAt Real.sqrt (Real.sqrt T / (2 * T)) T := by
    convert Real.hasDerivAt_sqrt (ne_of_gt hT) using 1
    field_simp [ne_of_gt hT, ne_of_gt (Real.sqrt_pos.mpr hT)]
    nlinarith only [Real.sq_sqrt hT.le]
  have hq := (hasDerivAt_const T ((z - y) ^ 2)).div
    ((hasDerivAt_id T).const_mul 2) (by simp only [Pi.mul_apply, id_eq]; positivity)
  have hg := (hs.mul hq.exp).const_mul (Real.sqrt (2 * Real.pi))
  convert hg using 1 <;>
    (try funext S) <;>
    dsimp only [reciprocalFreeDensity, Pi.pow_apply, Pi.mul_apply,
      Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;>
    ring_nf <;> field_simp [ne_of_gt hT] <;> ring

theorem reciprocalMixedFamily_spatial_hasDerivAt (j l : ℕ) (z T y : ℝ)
    (hjl : j + l ≤ 2) (hT : 0 < T) :
    HasDerivAt (reciprocalMixedFamily j l z T) (reciprocalMixedFamily (j + 1) l z T y) y := by
  have hd : HasDerivAt (fun w : ℝ => z - w) (-1) y := by
    simpa only [id_eq] using (hasDerivAt_id y).const_sub z
  have ht := hasDerivAt_const y T
  have hg := reciprocalFreeDensity_spatial_hasDerivAt z T y hT
  have cases : (j = 0 ∧ l = 0) ∨ (j = 1 ∧ l = 0) ∨ (j = 2 ∧ l = 0) ∨
      (j = 0 ∧ l = 1) ∨ (j = 1 ∧ l = 1) ∨ (j = 0 ∧ l = 2) := by omega
  rcases cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hc := (hasDerivAt_const y (1 : ℝ))
    convert hc.mul hg using 1 <;>
      (try funext w) <;>
      dsimp only [reciprocalMixedFamily, reciprocalCoefficient, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;>
      ring_nf <;> field_simp [ne_of_gt hT] <;> ring
  · have hc := (((hd).neg).div (ht) (by change (T : ℝ) ≠ 0; positivity))
    convert hc.mul hg using 1 <;>
      (try funext w) <;>
      dsimp only [reciprocalMixedFamily, reciprocalCoefficient, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;>
      ring_nf <;> field_simp [ne_of_gt hT] <;> ring
  · have hc := (((((hasDerivAt_const y (1 : ℝ))).div (ht) (by change (T : ℝ) ≠ 0; positivity))).add ((((hd).pow 2).div ((ht).pow 2) (by change ((T ^ 2) : ℝ) ≠ 0; positivity))))
    convert hc.mul hg using 1 <;>
      (try funext w) <;>
      dsimp only [reciprocalMixedFamily, reciprocalCoefficient, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;>
      ring_nf <;> field_simp [ne_of_gt hT] <;> ring
  · have hc := (((((hasDerivAt_const y (1 : ℝ))).div ((((hasDerivAt_const y (2 : ℝ))).mul (ht))) (by change ((2 * T) : ℝ) ≠ 0; positivity))).sub ((((hd).pow 2).div ((((hasDerivAt_const y (2 : ℝ))).mul ((ht).pow 2))) (by change ((2 * (T ^ 2)) : ℝ) ≠ 0; positivity))))
    convert hc.mul hg using 1 <;>
      (try funext w) <;>
      dsimp only [reciprocalMixedFamily, reciprocalCoefficient, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;>
      ring_nf <;> field_simp [ne_of_gt hT] <;> ring
  · have hc := ((((hd).div ((((hasDerivAt_const y (2 : ℝ))).mul ((ht).pow 2))) (by change ((2 * (T ^ 2)) : ℝ) ≠ 0; positivity))).add ((((hd).pow 3).div ((((hasDerivAt_const y (2 : ℝ))).mul ((ht).pow 3))) (by change ((2 * (T ^ 3)) : ℝ) ≠ 0; positivity))))
    convert hc.mul hg using 1 <;>
      (try funext w) <;>
      dsimp only [reciprocalMixedFamily, reciprocalCoefficient, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;>
      ring_nf <;> field_simp [ne_of_gt hT] <;> ring
  · have hc := ((((((((hasDerivAt_const y (1 : ℝ))).neg).div ((((hasDerivAt_const y (4 : ℝ))).mul ((ht).pow 2))) (by change ((4 * (T ^ 2)) : ℝ) ≠ 0; positivity))).add ((((hd).pow 2).div ((((hasDerivAt_const y (2 : ℝ))).mul ((ht).pow 3))) (by change ((2 * (T ^ 3)) : ℝ) ≠ 0; positivity))))).add ((((hd).pow 4).div ((((hasDerivAt_const y (4 : ℝ))).mul ((ht).pow 4))) (by change ((4 * (T ^ 4)) : ℝ) ≠ 0; positivity))))
    convert hc.mul hg using 1 <;>
      (try funext w) <;>
      dsimp only [reciprocalMixedFamily, reciprocalCoefficient, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;>
      ring_nf <;> field_simp [ne_of_gt hT] <;> ring

theorem reciprocalMixedFamily_time_hasDerivAt (j l : ℕ) (z T y : ℝ)
    (hjl : j + l ≤ 2) (hT : 0 < T) :
    HasDerivAt (fun S => reciprocalMixedFamily j l z S y)
      (reciprocalMixedFamily j (l + 1) z T y) T := by
  have hd := hasDerivAt_const T (z - y)
  have ht := hasDerivAt_id T
  have hg := reciprocalFreeDensity_time_hasDerivAt z T y hT
  have cases : (j = 0 ∧ l = 0) ∨ (j = 1 ∧ l = 0) ∨ (j = 2 ∧ l = 0) ∨
      (j = 0 ∧ l = 1) ∨ (j = 1 ∧ l = 1) ∨ (j = 0 ∧ l = 2) := by omega
  rcases cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hc := (hasDerivAt_const T (1 : ℝ))
    convert hc.mul hg using 1 <;>
      (try funext w) <;>
      dsimp only [reciprocalMixedFamily, reciprocalCoefficient, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;>
      ring_nf <;> field_simp [ne_of_gt hT] <;> ring
  · have hc := (((hd).neg).div (ht) (by change (T : ℝ) ≠ 0; positivity))
    convert hc.mul hg using 1 <;>
      (try funext w) <;>
      dsimp only [reciprocalMixedFamily, reciprocalCoefficient, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;>
      ring_nf <;> field_simp [ne_of_gt hT] <;> ring
  · have hc := (((((hasDerivAt_const T (1 : ℝ))).div (ht) (by change (T : ℝ) ≠ 0; positivity))).add ((((hd).pow 2).div ((ht).pow 2) (by change ((T ^ 2) : ℝ) ≠ 0; positivity))))
    convert hc.mul hg using 1 <;>
      (try funext w) <;>
      dsimp only [reciprocalMixedFamily, reciprocalCoefficient, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;>
      ring_nf <;> field_simp [ne_of_gt hT] <;> ring
  · have hc := (((((hasDerivAt_const T (1 : ℝ))).div ((((hasDerivAt_const T (2 : ℝ))).mul (ht))) (by change ((2 * T) : ℝ) ≠ 0; positivity))).sub ((((hd).pow 2).div ((((hasDerivAt_const T (2 : ℝ))).mul ((ht).pow 2))) (by change ((2 * (T ^ 2)) : ℝ) ≠ 0; positivity))))
    convert hc.mul hg using 1 <;>
      (try funext w) <;>
      dsimp only [reciprocalMixedFamily, reciprocalCoefficient, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;>
      ring_nf <;> field_simp [ne_of_gt hT] <;> ring
  · have hc := ((((hd).div ((((hasDerivAt_const T (2 : ℝ))).mul ((ht).pow 2))) (by change ((2 * (T ^ 2)) : ℝ) ≠ 0; positivity))).add ((((hd).pow 3).div ((((hasDerivAt_const T (2 : ℝ))).mul ((ht).pow 3))) (by change ((2 * (T ^ 3)) : ℝ) ≠ 0; positivity))))
    convert hc.mul hg using 1 <;>
      (try funext w) <;>
      dsimp only [reciprocalMixedFamily, reciprocalCoefficient, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;>
      ring_nf <;> field_simp [ne_of_gt hT] <;> ring
  · have hc := ((((((((hasDerivAt_const T (1 : ℝ))).neg).div ((((hasDerivAt_const T (4 : ℝ))).mul ((ht).pow 2))) (by change ((4 * (T ^ 2)) : ℝ) ≠ 0; positivity))).add ((((hd).pow 2).div ((((hasDerivAt_const T (2 : ℝ))).mul ((ht).pow 3))) (by change ((2 * (T ^ 3)) : ℝ) ≠ 0; positivity))))).add ((((hd).pow 4).div ((((hasDerivAt_const T (4 : ℝ))).mul ((ht).pow 4))) (by change ((4 * (T ^ 4)) : ℝ) ≠ 0; positivity))))
    convert hc.mul hg using 1 <;>
      (try funext w) <;>
      dsimp only [reciprocalMixedFamily, reciprocalCoefficient, Pi.pow_apply, Pi.mul_apply,
        Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;>
      ring_nf <;> field_simp [ne_of_gt hT] <;> ring

theorem reciprocalFreeDensity_spatial_iteratedDeriv (j : ℕ) (z T y : ℝ)
    (hj : j ≤ 3) (hT : 0 < T) :
    iteratedDeriv j (reciprocalFreeDensity z T) y = reciprocalMixedFamily j 0 z T y := by
  induction j generalizing y with
  | zero => simp only [iteratedDeriv_zero, reciprocalMixedFamily, reciprocalCoefficient, one_mul]
  | succ j ih =>
    have hj2 : j + 0 ≤ 2 := by omega
    have heq : iteratedDeriv j (reciprocalFreeDensity z T) = reciprocalMixedFamily j 0 z T := by
      funext w
      exact ih w (by omega)
    rw [iteratedDeriv_succ, heq]
    exact (reciprocalMixedFamily_spatial_hasDerivAt j 0 z T y hj2 hT).deriv

theorem reciprocalFreeDensity_mixed_iteratedDeriv (j l : ℕ) (z T y : ℝ)
    (hjl : j + l ≤ 3) (hT : 0 < T) :
    iteratedDeriv l (fun S => iteratedDeriv j (reciprocalFreeDensity z S) y) T =
      reciprocalMixedFamily j l z T y := by
  induction l generalizing T with
  | zero =>
    simpa only [iteratedDeriv_zero] using
      reciprocalFreeDensity_spatial_iteratedDeriv j z T y (by omega) hT
  | succ l ih =>
    have hjl2 : j + l ≤ 2 := by omega
    have heq : iteratedDeriv l (fun S => iteratedDeriv j (reciprocalFreeDensity z S) y) =ᶠ[𝓝 T]
        (fun S => reciprocalMixedFamily j l z S y) := by
      filter_upwards [isOpen_Ioi.mem_nhds hT] with S hS
      exact ih S (by omega) hS
    rw [iteratedDeriv_succ]
    exact heq.deriv_eq.trans (reciprocalMixedFamily_time_hasDerivAt j l z T y hjl2 hT).deriv

end Shao.C2.IntervalReciprocalDerivatives
