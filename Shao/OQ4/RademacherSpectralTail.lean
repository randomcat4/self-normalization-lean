import Shao.OQ4.RademacherSpectralPairing
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
PRIVATE_CHECKS_ONLY — v5.

This is an author private-source candidate for frozen U1, for no-o checks.
The target uses the certified Pair.remainder itself.
The frozen mathematical proof and every upstream implementation are unchanged.
-/

noncomputable section

open scoped BigOperators
open Set

namespace Shao.OQ4.RademacherSpectralTail

private def height (m : ℕ) : ℝ := (m : ℝ) + 1

private def baseAngle (m : ℕ) : ℝ := Real.pi / (4 * height m)

private def mainAngle (m : ℕ) : ℝ := Real.pi / (2 * height m)

private def frequency (ell : ℕ) : ℝ := 2 * (ell : ℝ) + 1

private def scaledTime (m n : ℕ) : ℝ := (n : ℝ) / height m ^ 2

def decayRatio : ℝ := Real.exp (-3 * Real.pi ^ 2 / 2)

/-- The constant is chosen before every lattice, cell and time parameter. -/
def absoluteC : ℝ := 2 / (3 * (1 - decayRatio))

private theorem height_pos (m : ℕ) : 0 < height m := by
  dsimp [height]
  positivity

private theorem height_ge_two {m : ℕ} (hm : 1 ≤ m) : 2 ≤ height m := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  dsimp [height]
  linarith

theorem decayRatio_pos : 0 < decayRatio := Real.exp_pos _

theorem decayRatio_lt_one : decayRatio < 1 := by
  unfold decayRatio
  apply Real.exp_lt_one_iff.mpr
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  nlinarith

theorem absoluteC_pos : 0 < absoluteC := by
  unfold absoluteC
  exact div_pos (by norm_num) (mul_pos (by norm_num) (sub_pos.mpr decayRatio_lt_one))

private theorem alpha_eq (m ell : ℕ) :
    RademacherSpectralPairing.alpha m ell = frequency ell * baseAngle m := by
  simp only [RademacherSpectralPairing.alpha, frequency, baseAngle, height,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

private theorem beta_eq (m ell : ℕ) :
    RademacherSpectralPairing.beta m ell = frequency ell * mainAngle m := by
  simp only [RademacherSpectralPairing.beta, frequency, mainAngle, height,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

private theorem rho_eq (m : ℕ) :
    RademacherSpectralPairing.rho m = Real.cos (mainAngle m) := rfl

private theorem baseAngle_bounds {m : ℕ} (hm : 1 ≤ m) :
    0 < baseAngle m ∧ baseAngle m < Real.pi / 4 := by
  have hH := height_pos m
  have hH2 := height_ge_two hm
  constructor
  · exact div_pos Real.pi_pos (mul_pos (by norm_num) hH)
  · dsimp only [baseAngle]
    apply (div_lt_div_iff₀ (by positivity : 0 < 4 * height m)
      (by norm_num : (0 : ℝ) < 4)).2
    have hp : 0 < Real.pi * (height m - 1) :=
      mul_pos Real.pi_pos (by linarith)
    nlinarith

private theorem mainAngle_eq (m : ℕ) : mainAngle m = 2 * baseAngle m := by
  dsimp [mainAngle, baseAngle]
  ring

private theorem mainAngle_bounds {m : ℕ} (hm : 1 ≤ m) :
    0 < mainAngle m ∧ mainAngle m < Real.pi / 2 := by
  rw [mainAngle_eq]
  have hx := baseAngle_bounds hm
  constructor <;> linarith

private theorem cos_pos_of_nonneg_of_lt_half_pi {u : ℝ}
    (hu : 0 ≤ u) (hu' : u < Real.pi / 2) : 0 < Real.cos u := by
  apply Real.cos_pos_of_mem_Ioo
  exact ⟨by linarith [Real.pi_pos], hu'⟩

/-! The tangent coefficient estimate is proved internally, via convexity. -/

private theorem tan_convex_Icc {y : ℝ} (hy : 0 ≤ y) (hy' : y < Real.pi / 2) :
    ConvexOn ℝ (Icc 0 y) Real.tan := by
  have hcos : ∀ u ∈ Icc (0 : ℝ) y, 0 < Real.cos u := by
    intro u hu
    exact cos_pos_of_nonneg_of_lt_half_pi hu.1 (lt_of_le_of_lt hu.2 hy')
  have hd : ∀ u ∈ Icc (0 : ℝ) y,
      HasDerivAt Real.tan (1 / Real.cos u ^ 2) u := by
    intro u hu
    exact Real.hasDerivAt_tan (ne_of_gt (hcos u hu))
  apply MonotoneOn.convexOn_of_deriv (convex_Icc (0 : ℝ) y)
  · intro u hu
    exact (hd u hu).continuousAt.continuousWithinAt
  · intro u hu
    exact (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
  · intro u hu v hv huv
    have hu' : u ∈ Icc (0 : ℝ) y := interior_subset hu
    have hv' : v ∈ Icc (0 : ℝ) y := interior_subset hv
    rw [Real.deriv_tan, Real.deriv_tan]
    apply one_div_le_one_div_of_le (sq_pos_of_pos (hcos v hv'))
    apply (sq_le_sq₀ (le_of_lt (hcos v hv')) (le_of_lt (hcos u hu'))).2
    exact Real.cos_le_cos_of_nonneg_of_le_pi hu'.1
      (by linarith [hv'.2, Real.pi_pos]) huv

private theorem tan_scale_le {x r : ℝ} (hx : 0 < x) (hr : 1 ≤ r)
    (hrx : r * x < Real.pi / 2) : Real.tan x ≤ (1 / r) * Real.tan (r * x) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hy0 : 0 ≤ r * x := le_of_lt (mul_pos hr0 hx)
  have hconv := tan_convex_Icc hy0 hrx
  have hw : (1 : ℝ) / r ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hr
  have hcancel : (1 / r) * (r * x) = x := by
    field_simp [ne_of_gt hr0]
  have h := hconv.2 (show (0 : ℝ) ∈ Icc 0 (r * x) from ⟨le_rfl, hy0⟩)
    (show r * x ∈ Icc 0 (r * x) from ⟨hy0, le_rfl⟩)
    (show 0 ≤ 1 - 1 / r by linarith)
    (show 0 ≤ (1 : ℝ) / r by positivity)
    (show (1 - 1 / r) + 1 / r = (1 : ℝ) by ring)
  simpa only [smul_eq_mul, mul_zero, zero_add, Real.tan_zero, hcancel] using h

private def pairedCoefficient (m n ell : ℕ) : ℝ :=
  (-1 : ℝ) ^ ell *
    ((RademacherFiniteS1.cotangent (RademacherSpectralPairing.alpha m ell) +
      RademacherSpectralPairing.epsilon m n *
        Real.tan (RademacherSpectralPairing.alpha m ell)) /
      RademacherFiniteS1.cotangent (baseAngle m))

private theorem normalizedTerm_eq (m n ell : ℕ) :
    RademacherSpectralPairing.normalizedTerm m n ell =
      pairedCoefficient m n ell *
        (Real.cos (RademacherSpectralPairing.beta m ell) /
          RademacherSpectralPairing.rho m) ^ n := rfl

private theorem tail_membership {m ell : ℕ}
    (hell : ell ∈ (RademacherSpectralPairing.lowerModes m).erase 0) :
    1 ≤ ell ∧ ell ≤ m ∧ ell ∈ RademacherSpectralPairing.lowerModes m := by
  have he := Finset.mem_erase.mp hell
  have hle := RademacherSpectralPairing.lowerModes_le he.2
  exact ⟨by omega, hle, he.2⟩

private theorem coefficient_abs_le {m n ell : ℕ} (hm : 1 ≤ m)
    (hell : ell ∈ (RademacherSpectralPairing.lowerModes m).erase 0) :
    |pairedCoefficient m n ell| ≤ 2 / frequency ell := by
  have ht := tail_membership hell
  have hy := RademacherSpectralPairing.lower_alpha_bounds ht.2.2
  have hx := baseAngle_bounds hm
  have hr3 : (3 : ℝ) ≤ frequency ell := by
    dsimp [frequency]
    exact_mod_cast (show 3 ≤ 2 * ell + 1 by omega)
  have hr0 : 0 < frequency ell := by linarith
  have hxy := alpha_eq m ell
  have hscale : Real.tan (baseAngle m) ≤
      (1 / frequency ell) * Real.tan (RademacherSpectralPairing.alpha m ell) := by
    rw [hxy]
    apply tan_scale_le hx.1 (by linarith)
    rw [← hxy]
    linarith [Real.pi_pos]
  have htx : 0 < Real.tan (baseAngle m) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hx.1 (by linarith [Real.pi_pos])
  have hty : 0 < Real.tan (RademacherSpectralPairing.alpha m ell) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hy.1 (by linarith [Real.pi_pos])
  have hty1 : Real.tan (RademacherSpectralPairing.alpha m ell) ≤ 1 := by
    simpa only [Real.tan_pi_div_four] using
      (Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two (le_of_lt hy.1)
        (show Real.pi / 4 < Real.pi / 2 by linarith [Real.pi_pos]) hy.2).le
  have htys : Real.tan (RademacherSpectralPairing.alpha m ell) ^ 2 ≤ 1 := by
    have hh := (sq_le_sq₀ (le_of_lt hty) (show (0 : ℝ) ≤ 1 by norm_num)).2 hty1
    simpa using hh
  have hden : 0 < RademacherFiniteS1.cotangent (baseAngle m) :=
    RademacherSpectralPairing.principal_cotangent_pos hm
  have hxcos := cos_pos_of_nonneg_of_lt_half_pi (le_of_lt hx.1)
    (show baseAngle m < Real.pi / 2 by linarith [Real.pi_pos])
  have hxsin := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [Real.pi_pos])
  have hyd := RademacherSpectralPairing.lower_trig_denominators ht.2.2
  have hcy : 0 < RademacherFiniteS1.cotangent
      (RademacherSpectralPairing.alpha m ell) := by
    exact div_pos hyd.2 hyd.1
  have hrat1 : RademacherFiniteS1.cotangent (RademacherSpectralPairing.alpha m ell) /
      RademacherFiniteS1.cotangent (baseAngle m) =
      Real.tan (baseAngle m) / Real.tan (RademacherSpectralPairing.alpha m ell) := by
    simp only [RademacherFiniteS1.cotangent, Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hxcos, ne_of_gt hxsin, ne_of_gt hyd.1, ne_of_gt hyd.2]
  have hrat2 : Real.tan (RademacherSpectralPairing.alpha m ell) /
      RademacherFiniteS1.cotangent (baseAngle m) =
      Real.tan (RademacherSpectralPairing.alpha m ell) * Real.tan (baseAngle m) := by
    simp only [RademacherFiniteS1.cotangent, Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hxcos, ne_of_gt hxsin, ne_of_gt hyd.1, ne_of_gt hyd.2]
  have hb1 : RademacherFiniteS1.cotangent (RademacherSpectralPairing.alpha m ell) /
      RademacherFiniteS1.cotangent (baseAngle m) ≤ 1 / frequency ell := by
    rw [hrat1]
    exact (div_le_iff₀ hty).2 hscale
  have hb2 : Real.tan (RademacherSpectralPairing.alpha m ell) /
      RademacherFiniteS1.cotangent (baseAngle m) ≤ 1 / frequency ell := by
    rw [hrat2]
    calc
      _ ≤ Real.tan (RademacherSpectralPairing.alpha m ell) *
          ((1 / frequency ell) * Real.tan (RademacherSpectralPairing.alpha m ell)) :=
        mul_le_mul_of_nonneg_left hscale (le_of_lt hty)
      _ = Real.tan (RademacherSpectralPairing.alpha m ell) ^ 2 / frequency ell := by ring
      _ ≤ 1 / frequency ell := div_le_div_of_nonneg_right htys (le_of_lt hr0)
  have heps : |RademacherSpectralPairing.epsilon m n| = 1 := by
    simp [RademacherSpectralPairing.epsilon, abs_pow]
  have hnum : |RademacherFiniteS1.cotangent (RademacherSpectralPairing.alpha m ell) +
      RademacherSpectralPairing.epsilon m n *
        Real.tan (RademacherSpectralPairing.alpha m ell)| ≤
      RademacherFiniteS1.cotangent (RademacherSpectralPairing.alpha m ell) +
        Real.tan (RademacherSpectralPairing.alpha m ell) := by
    calc
      _ ≤ |RademacherFiniteS1.cotangent (RademacherSpectralPairing.alpha m ell)| +
          |RademacherSpectralPairing.epsilon m n *
            Real.tan (RademacherSpectralPairing.alpha m ell)| := abs_add_le _ _
      _ = _ := by rw [abs_of_pos hcy, abs_mul, heps, abs_of_pos hty, one_mul]
  calc
    |pairedCoefficient m n ell| =
        |RademacherFiniteS1.cotangent (RademacherSpectralPairing.alpha m ell) +
          RademacherSpectralPairing.epsilon m n *
            Real.tan (RademacherSpectralPairing.alpha m ell)| /
          RademacherFiniteS1.cotangent (baseAngle m) := by
      simp [pairedCoefficient, abs_mul, abs_div, abs_pow, abs_of_pos hden]
    _ ≤ (RademacherFiniteS1.cotangent (RademacherSpectralPairing.alpha m ell) +
        Real.tan (RademacherSpectralPairing.alpha m ell)) /
          RademacherFiniteS1.cotangent (baseAngle m) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hden)
    _ = RademacherFiniteS1.cotangent (RademacherSpectralPairing.alpha m ell) /
          RademacherFiniteS1.cotangent (baseAngle m) +
        Real.tan (RademacherSpectralPairing.alpha m ell) /
          RademacherFiniteS1.cotangent (baseAngle m) := add_div _ _ _
    _ ≤ 1 / frequency ell + 1 / frequency ell := add_le_add hb1 hb2
    _ = 2 / frequency ell := by ring

private theorem coefficient_abs_le_two_thirds {m n ell : ℕ} (hm : 1 ≤ m)
    (hell : ell ∈ (RademacherSpectralPairing.lowerModes m).erase 0) :
    |pairedCoefficient m n ell| ≤ (2 : ℝ) / 3 := by
  apply (coefficient_abs_le hm hell).trans
  have he := (tail_membership hell).1
  have hr : (3 : ℝ) ≤ frequency ell := by
    dsimp [frequency]
    exact_mod_cast (show 3 ≤ 2 * ell + 1 by omega)
  apply (div_le_iff₀ (show 0 < frequency ell by linarith)).2
  nlinarith

/-! The relative log-cosine estimate is proved by first derivatives. -/

private theorem monotoneOn_Icc_of_nonneg_derivative {f f' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ u ∈ Icc a b, HasDerivAt f (f' u) u)
    (hpos : ∀ u ∈ Icc a b, 0 ≤ f' u) : MonotoneOn f (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
  · intro u hu
    exact (hd u hu).continuousAt.continuousWithinAt
  · intro u hu
    exact (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [(hd u (interior_subset hu)).deriv]
    exact hpos u (interior_subset hu)

private theorem antitoneOn_Icc_of_nonpos_derivative {f f' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ u ∈ Icc a b, HasDerivAt f (f' u) u)
    (hneg : ∀ u ∈ Icc a b, f' u ≤ 0) : AntitoneOn f (Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
  · intro u hu
    exact (hd u hu).continuousAt.continuousWithinAt
  · intro u hu
    exact (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [(hd u (interior_subset hu)).deriv]
    exact hneg u (interior_subset hu)

private theorem self_le_tan {u : ℝ} (hu : 0 ≤ u) (hu' : u < Real.pi / 2) :
    u ≤ Real.tan u := by
  have hcos : ∀ v ∈ Icc (0 : ℝ) u, 0 < Real.cos v := by
    intro v hv
    exact cos_pos_of_nonneg_of_lt_half_pi hv.1 (lt_of_le_of_lt hv.2 hu')
  have hd : ∀ v ∈ Icc (0 : ℝ) u,
      HasDerivAt (fun z : ℝ => Real.tan z - z) (1 / Real.cos v ^ 2 - 1) v := by
    intro v hv
    convert (Real.hasDerivAt_tan (ne_of_gt (hcos v hv))).sub (hasDerivAt_id v) using 1 <;>
      first | rfl | (funext z; rfl)
  have hp : ∀ v ∈ Icc (0 : ℝ) u, 0 ≤ 1 / Real.cos v ^ 2 - 1 := by
    intro v hv
    have hsq : Real.cos v ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq v, sq_nonneg (Real.sin v)]
    have hdiv := one_div_le_one_div_of_le (sq_pos_of_pos (hcos v hv)) hsq
    norm_num at hdiv
    simp only [one_div]
    linarith
  have hmono := monotoneOn_Icc_of_nonneg_derivative hd hp
  have h := hmono (show (0 : ℝ) ∈ Icc 0 u from ⟨le_rfl, hu⟩)
    (show u ∈ Icc 0 u from ⟨hu, le_rfl⟩) hu
  exact sub_nonneg.mp (show 0 ≤ Real.tan u - u by simpa using h)

private def logCosEnergy (u : ℝ) : ℝ := Real.log (Real.cos u) + u ^ 2 / 2

private theorem hasDerivAt_logCosEnergy {u : ℝ} (hu : Real.cos u ≠ 0) :
    HasDerivAt logCosEnergy (-Real.tan u + u) u := by
  unfold logCosEnergy
  convert ((Real.hasDerivAt_cos u).log hu).add
    (((hasDerivAt_id u).pow 2).div_const 2) using 1 <;>
    simp [Real.tan_eq_sin_div_cos]
  all_goals first | (funext z; rfl) | ring

private theorem relative_cosine_bound {v w : ℝ} (hv : 0 ≤ v)
    (hvw : v ≤ w) (hw : w < Real.pi / 2) :
    Real.cos w / Real.cos v ≤ Real.exp (-(w ^ 2 - v ^ 2) / 2) := by
  have hw0 : 0 ≤ w := hv.trans hvw
  have hcos : ∀ u ∈ Icc v w, 0 < Real.cos u := by
    intro u hu
    exact cos_pos_of_nonneg_of_lt_half_pi (hv.trans hu.1) (lt_of_le_of_lt hu.2 hw)
  have hd : ∀ u ∈ Icc v w,
      HasDerivAt logCosEnergy (-Real.tan u + u) u := by
    intro u hu
    exact hasDerivAt_logCosEnergy (ne_of_gt (hcos u hu))
  have hneg : ∀ u ∈ Icc v w, -Real.tan u + u ≤ 0 := by
    intro u hu
    have h := self_le_tan (hv.trans hu.1) (lt_of_le_of_lt hu.2 hw)
    linarith
  have hanti := antitoneOn_Icc_of_nonpos_derivative hd hneg
  have hE := hanti (show v ∈ Icc v w from ⟨le_rfl, hvw⟩)
    (show w ∈ Icc v w from ⟨hvw, le_rfl⟩) hvw
  have hcv := hcos v ⟨le_rfl, hvw⟩
  have hcw := hcos w ⟨hvw, le_rfl⟩
  apply (Real.log_le_iff_le_exp (div_pos hcw hcv)).mp
  rw [Real.log_div (ne_of_gt hcw) (ne_of_gt hcv)]
  dsimp [logCosEnergy] at hE
  linarith

private theorem spectral_ratio_pow_le {m ell : ℕ} (hm : 1 ≤ m)
    (hell : ell ∈ (RademacherSpectralPairing.lowerModes m).erase 0) (n : ℕ) :
    (Real.cos (RademacherSpectralPairing.beta m ell) /
      RademacherSpectralPairing.rho m) ^ n ≤
      Real.exp (-Real.pi ^ 2 * (frequency ell ^ 2 - 1) * scaledTime m n / 8) := by
  have ht := tail_membership hell
  have hv := mainAngle_bounds hm
  have hw := RademacherSpectralPairing.lower_beta_bounds ht.2.2
  have hr : (1 : ℝ) ≤ frequency ell := by
    dsimp [frequency]
    nlinarith [show (0 : ℝ) ≤ (ell : ℝ) from Nat.cast_nonneg ell]
  have hvw : mainAngle m ≤ RademacherSpectralPairing.beta m ell := by
    rw [beta_eq]
    have hmul := mul_le_mul_of_nonneg_right hr (le_of_lt hv.1)
    nlinarith
  have hc := relative_cosine_bound (le_of_lt hv.1) hvw hw.2
  have hratio : 0 ≤ Real.cos (RademacherSpectralPairing.beta m ell) /
      RademacherSpectralPairing.rho m := by
    exact le_of_lt (div_pos (RademacherSpectralPairing.cos_beta_pos ht.2.2)
      (RademacherSpectralPairing.rho_pos hm))
  have hpow : (Real.cos (RademacherSpectralPairing.beta m ell) /
      RademacherSpectralPairing.rho m) ^ n ≤
      Real.exp ((n : ℝ) *
        (-(RademacherSpectralPairing.beta m ell ^ 2 - mainAngle m ^ 2) / 2)) := by
    calc
      _ ≤ (Real.exp (-(RademacherSpectralPairing.beta m ell ^ 2 - mainAngle m ^ 2) / 2)) ^ n :=
        pow_le_pow_left₀ hratio (by simpa only [rho_eq] using hc) n
      _ = _ := (Real.exp_nat_mul _ n).symm
  have heq : (n : ℝ) *
      (-(RademacherSpectralPairing.beta m ell ^ 2 - mainAngle m ^ 2) / 2) =
      -Real.pi ^ 2 * (frequency ell ^ 2 - 1) * scaledTime m n / 8 := by
    rw [beta_eq]
    dsimp only [mainAngle, scaledTime]
    field_simp [ne_of_gt (height_pos m)]
    ring
  simpa only [heq] using hpow

private theorem exponential_frequency_le {ell : ℕ} (hell : 1 ≤ ell)
    {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-Real.pi ^ 2 * (frequency ell ^ 2 - 1) * t / 8) ≤
      Real.exp (-Real.pi ^ 2 * t) * decayRatio ^ (ell - 1) := by
  let k := ell - 1
  have he : ell = k + 1 := by dsimp [k]; omega
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hfreq : frequency ell = 2 * (k : ℝ) + 3 := by
    rw [he]
    simp only [frequency, Nat.cast_add, Nat.cast_one]
    ring
  have hgap : 12 * (k : ℝ) ≤ frequency ell ^ 2 - 9 := by
    rw [hfreq]
    nlinarith [sq_nonneg (k : ℝ)]
  have hgap0 : 0 ≤ frequency ell ^ 2 - 9 := by linarith
  have hgap_t : 12 * (k : ℝ) ≤ (frequency ell ^ 2 - 9) * t := by
    have hprod := mul_le_mul_of_nonneg_left ht hgap0
    nlinarith
  have hexponent : -Real.pi ^ 2 * (frequency ell ^ 2 - 1) * t / 8 ≤
      -Real.pi ^ 2 * t + (k : ℝ) * (-3 * Real.pi ^ 2 / 2) := by
    have hmul := mul_le_mul_of_nonneg_left hgap_t (sq_nonneg Real.pi)
    nlinarith
  calc
    _ ≤ Real.exp (-Real.pi ^ 2 * t + (k : ℝ) * (-3 * Real.pi ^ 2 / 2)) :=
      Real.exp_le_exp.mpr hexponent
    _ = _ := by rw [Real.exp_add, Real.exp_nat_mul]; rfl

private theorem normalizedTerm_abs_le {m n ell : ℕ} (hm : 1 ≤ m)
    (hell : ell ∈ (RademacherSpectralPairing.lowerModes m).erase 0)
    (ht : 1 ≤ scaledTime m n) :
    |RademacherSpectralPairing.normalizedTerm m n ell| ≤
      ((2 : ℝ) / 3 * Real.exp (-Real.pi ^ 2 * scaledTime m n)) *
        decayRatio ^ (ell - 1) := by
  have htmem := tail_membership hell
  have hr : 0 ≤ Real.cos (RademacherSpectralPairing.beta m ell) /
      RademacherSpectralPairing.rho m := by
    exact le_of_lt (div_pos (RademacherSpectralPairing.cos_beta_pos htmem.2.2)
      (RademacherSpectralPairing.rho_pos hm))
  have hc := coefficient_abs_le_two_thirds (n := n) hm hell
  have hs := spectral_ratio_pow_le hm hell n
  have he := exponential_frequency_le htmem.1 ht
  rw [normalizedTerm_eq, abs_mul, abs_of_nonneg (pow_nonneg hr n)]
  calc
    _ ≤ (2 : ℝ) / 3 *
        Real.exp (-Real.pi ^ 2 * (frequency ell ^ 2 - 1) * scaledTime m n / 8) :=
      mul_le_mul hc hs (pow_nonneg hr n) (by norm_num)
    _ ≤ (2 : ℝ) / 3 *
        (Real.exp (-Real.pi ^ 2 * scaledTime m n) * decayRatio ^ (ell - 1)) :=
      mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by ring

/-! A finite geometric identity covers every remaining odd frequency. -/

private theorem finite_geometric_sum_le {q : ℝ} (hq : 0 ≤ q) (hq' : q < 1) (M : ℕ) :
    (∑ k ∈ Finset.range M, q ^ k) ≤ 1 / (1 - q) := by
  have hgeom : ∀ N : ℕ, (1 - q) * (∑ k ∈ Finset.range N, q ^ k) = 1 - q ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith
  apply (le_div_iff₀ (sub_pos.mpr hq')).2
  have hpow := pow_nonneg hq M
  nlinarith [hgeom M]

private theorem tail_geometric_sum_le (m : ℕ) :
    (∑ ell ∈ (RademacherSpectralPairing.lowerModes m).erase 0,
      decayRatio ^ (ell - 1)) ≤ 1 / (1 - decayRatio) := by
  classical
  let s := (RademacherSpectralPairing.lowerModes m).erase 0
  have hinj : Set.InjOn (fun ell : ℕ => ell - 1) (↑s : Set ℕ) := by
    intro a ha b hb hab
    have ha' := (tail_membership (show a ∈ (RademacherSpectralPairing.lowerModes m).erase 0 from ha)).1
    have hb' := (tail_membership (show b ∈ (RademacherSpectralPairing.lowerModes m).erase 0 from hb)).1
    change a - 1 = b - 1 at hab
    omega
  have hsub : s.image (fun ell : ℕ => ell - 1) ⊆ Finset.range m := by
    intro k hk
    obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hk
    have he := tail_membership
      (show ell ∈ (RademacherSpectralPairing.lowerModes m).erase 0 from hell)
    apply Finset.mem_range.mpr
    omega
  change (∑ ell ∈ s, decayRatio ^ (ell - 1)) ≤ _
  calc
    _ = ∑ k ∈ s.image (fun ell : ℕ => ell - 1), decayRatio ^ k :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ k ∈ Finset.range m, decayRatio ^ k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro k _ _
        exact pow_nonneg (le_of_lt decayRatio_pos) k)
    _ ≤ _ := finite_geometric_sum_le (le_of_lt decayRatio_pos) decayRatio_lt_one m

/-! Positive time is obtained from the original threshold, before removing Z. -/

private theorem zeroMode_vanishes {n : ℕ} (m : ℕ) (hn : 1 ≤ n) :
    RademacherSpectralPairing.zeroMode m n = 0 := by
  have hn0 : n ≠ 0 := by omega
  simp [RademacherSpectralPairing.zeroMode, zero_pow hn0]

private theorem remainder_eq_sum {n : ℕ} (m : ℕ) (hn : 1 ≤ n) :
    RademacherSpectralPairing.remainder m n =
      ∑ ell ∈ (RademacherSpectralPairing.lowerModes m).erase 0,
        RademacherSpectralPairing.normalizedTerm m n ell := by
  unfold RademacherSpectralPairing.remainder
  rw [zeroMode_vanishes m hn]
  simp

theorem remainder_uniform {m n : ℕ} (hm : 1 ≤ m)
    (hn : ((m : ℝ) + 1) ^ 2 ≤ (n : ℝ)) :
    |RademacherSpectralPairing.remainder m n| ≤
      absoluteC * Real.exp (-Real.pi ^ 2 * (n : ℝ) / ((m : ℝ) + 1) ^ 2) := by
  have htime : 1 ≤ scaledTime m n := by
    apply (le_div_iff₀ (sq_pos_of_pos (height_pos m))).2
    simpa only [one_mul, height] using hn
  have hnreal : 0 < (n : ℝ) :=
    lt_of_lt_of_le (sq_pos_of_pos (height_pos m)) hn
  have hnNat : 1 ≤ n := by
    have hnpos : 0 < n := by exact_mod_cast hnreal
    omega
  have hnormalizer : 0 < RademacherSpectralPairing.amplitude m *
      RademacherSpectralPairing.rho m ^ n := RademacherSpectralPairing.normalizer_pos hm n
  rw [remainder_eq_sum m hnNat]
  calc
    _ ≤ ∑ ell ∈ (RademacherSpectralPairing.lowerModes m).erase 0,
        |RademacherSpectralPairing.normalizedTerm m n ell| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ell ∈ (RademacherSpectralPairing.lowerModes m).erase 0,
        ((2 : ℝ) / 3 * Real.exp (-Real.pi ^ 2 * scaledTime m n)) *
          decayRatio ^ (ell - 1) := by
      apply Finset.sum_le_sum
      intro ell hell
      exact normalizedTerm_abs_le hm hell htime
    _ = ((2 : ℝ) / 3 * Real.exp (-Real.pi ^ 2 * scaledTime m n)) *
        ∑ ell ∈ (RademacherSpectralPairing.lowerModes m).erase 0,
          decayRatio ^ (ell - 1) := by rw [Finset.mul_sum]
    _ ≤ ((2 : ℝ) / 3 * Real.exp (-Real.pi ^ 2 * scaledTime m n)) *
        (1 / (1 - decayRatio)) :=
      mul_le_mul_of_nonneg_left (tail_geometric_sum_le m) (by positivity)
    _ = absoluteC * Real.exp
        (-Real.pi ^ 2 * (n : ℝ) / ((m : ℝ) + 1) ^ 2) := by
      unfold absoluteC scaledTime height
      have he : -Real.pi ^ 2 * ((n : ℝ) / ((m : ℝ) + 1) ^ 2) =
          -Real.pi ^ 2 * (n : ℝ) / ((m : ℝ) + 1) ^ 2 := by ring
      rw [he]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- U1 on every weak lattice cell, with no parity or size restriction. -/
theorem remainder_uniform_weakCell {m : ℕ} (hm : 1 ≤ m) {h : ℝ}
    (_hmh : (m : ℝ) ≤ h) (_hhm : h < (m : ℝ) + 1) {n : ℕ}
    (hn : ((m : ℝ) + 1) ^ 2 ≤ (n : ℝ)) :
    |RademacherSpectralPairing.remainder m n| ≤
      absoluteC * Real.exp (-Real.pi ^ 2 * (n : ℝ) / ((m : ℝ) + 1) ^ 2) :=
  remainder_uniform hm hn

/-- The quantifier order of frozen U1, for the actual Pair remainder. -/
theorem exists_absolute_uniform_remainder_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ m : ℕ, 1 ≤ m →
      ∀ h : ℝ, (m : ℝ) ≤ h → h < (m : ℝ) + 1 →
      ∀ n : ℕ, ((m : ℝ) + 1) ^ 2 ≤ (n : ℝ) →
        |RademacherSpectralPairing.remainder m n| ≤
          C * Real.exp (-Real.pi ^ 2 * (n : ℝ) / ((m : ℝ) + 1) ^ 2) := by
  refine ⟨absoluteC, absoluteC_pos, ?_⟩
  intro m hm h hmh hhm n hn
  exact remainder_uniform_weakCell hm hmh hhm hn

theorem remainder_one_positive_time {n : ℕ} (_hn : 1 ≤ n) :
    RademacherSpectralPairing.remainder 1 n = 0 :=
  RademacherSpectralPairing.remainder_one n

theorem remainder_two_positive_time {n : ℕ} (hn : 1 ≤ n) :
    RademacherSpectralPairing.remainder 2 n = 0 :=
  RademacherSpectralPairing.remainder_two_positive_time hn

end Shao.OQ4.RademacherSpectralTail
