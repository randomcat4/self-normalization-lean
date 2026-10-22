import Shao.OQ4.RademacherFiniteS1

/-!
Exact finite reflection pairing of the fixed Rademacher S1.
All natural times, the weak closed strip, signed powers and the central zero mode
are retained. This module does not assert the uniform S2 remainder estimate.
-/

open scoped BigOperators
open MeasureTheory

namespace Shao.OQ4.RademacherSpectralPairing

noncomputable section

def lowerModes (m : ℕ) : Finset ℕ :=
  (Finset.range (m + 1)).filter (fun ell => 2 * ell < m)

def reflect (m ell : ℕ) : ℕ := m - ell

def centerModes (m : ℕ) : Finset ℕ :=
  (Finset.range (m + 1)).filter (fun ell => 2 * ell = m)

def alpha (m ell : ℕ) : ℝ := (2 * ell + 1 : ℕ) * Real.pi / (4 * ((m : ℝ) + 1))
def beta (m ell : ℕ) : ℝ := (2 * ell + 1 : ℕ) * Real.pi / (2 * ((m : ℝ) + 1))
def epsilon (m n : ℕ) : ℝ := (-1 : ℝ) ^ (n + m)
def amplitude (m : ℕ) : ℝ :=
  (1 / ((m : ℝ) + 1)) * RademacherFiniteS1.cotangent (Real.pi / (4 * ((m : ℝ) + 1)))
def rho (m : ℕ) : ℝ := Real.cos (Real.pi / (2 * ((m : ℝ) + 1)))
def zeroMode (m n : ℕ) : ℝ :=
  if Even m then ((-1 : ℝ) ^ (m / 2) / ((m : ℝ) + 1)) * (0 : ℝ) ^ n else 0

def rawTerm (m n ell : ℕ) : ℝ :=
  (-1 : ℝ) ^ ell * RademacherFiniteS1.cotangent (alpha m ell) *
    (Real.cos (beta m ell)) ^ n

def pairedTerm (m n ell : ℕ) : ℝ :=
  (-1 : ℝ) ^ ell *
    (RademacherFiniteS1.cotangent (alpha m ell) + epsilon m n * Real.tan (alpha m ell)) *
    (Real.cos (beta m ell)) ^ n

def normalizedTerm (m n ell : ℕ) : ℝ :=
  (-1 : ℝ) ^ ell *
    ((RademacherFiniteS1.cotangent (alpha m ell) + epsilon m n * Real.tan (alpha m ell)) /
      RademacherFiniteS1.cotangent (Real.pi / (4 * ((m : ℝ) + 1)))) *
    (Real.cos (beta m ell) / rho m) ^ n

def remainder (m n : ℕ) : ℝ :=
  (∑ ell ∈ (lowerModes m).erase 0, normalizedTerm m n ell) +
    zeroMode m n / (amplitude m * rho m ^ n)

theorem mem_lowerModes (m ell : ℕ) : ell ∈ lowerModes m ↔ 2 * ell < m := by
  simp only [lowerModes, Finset.mem_filter, Finset.mem_range]
  omega

theorem lowerModes_le {m ell : ℕ} (hell : ell ∈ lowerModes m) : ell ≤ m := by
  rw [mem_lowerModes] at hell
  omega

theorem reflect_involutive {m ell : ℕ} (hell : ell ≤ m) :
    reflect m (reflect m ell) = ell := by
  unfold reflect
  omega

theorem reflect_injective_on (m : ℕ) :
    Set.InjOn (reflect m) (↑(lowerModes m) : Set ℕ) := by
  intro i hi j hj he
  have hi' := lowerModes_le hi
  have hj' := lowerModes_le hj
  unfold reflect at he
  omega

theorem mem_reflectedModes (m ell : ℕ) :
    ell ∈ (lowerModes m).image (reflect m) ↔ ell ≤ m ∧ m < 2 * ell := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨k, hk, rfl⟩
    have hk' := (mem_lowerModes m k).mp hk
    unfold reflect
    omega
  · rintro ⟨hle, hgt⟩
    apply Finset.mem_image.mpr
    refine ⟨reflect m ell, ?_, reflect_involutive hle⟩
    rw [mem_lowerModes]
    unfold reflect
    omega

theorem mem_centerModes (m ell : ℕ) : ell ∈ centerModes m ↔ 2 * ell = m := by
  simp only [centerModes, Finset.mem_filter, Finset.mem_range]
  omega

theorem even_twice_half {m : ℕ} (hm : Even m) : 2 * (m / 2) = m := by
  have hmod : m % 2 = 0 := Nat.even_iff.mp hm
  omega

theorem centerModes_eq (m : ℕ) :
    centerModes m = if Even m then {m / 2} else ∅ := by
  classical
  ext ell
  by_cases hm : Even m
  · have hhalf := even_twice_half hm
    simp only [hm, ite_true, Finset.mem_singleton, mem_centerModes]
    omega
  · simp only [hm, ite_false, Finset.notMem_empty, iff_false, mem_centerModes]
    intro he
    apply hm
    exact ⟨ell, by omega⟩

theorem lower_reflected_disjoint (m : ℕ) :
    Disjoint (lowerModes m) ((lowerModes m).image (reflect m)) := by
  apply Finset.disjoint_left.mpr
  intro ell hl hr
  have hl' := (mem_lowerModes m ell).mp hl
  have hr' := (mem_reflectedModes m ell).mp hr
  omega

theorem paired_center_disjoint (m : ℕ) :
    Disjoint (lowerModes m ∪ (lowerModes m).image (reflect m)) (centerModes m) := by
  apply Finset.disjoint_left.mpr
  intro ell hp hc
  have hc' := (mem_centerModes m ell).mp hc
  rcases Finset.mem_union.mp hp with hl | hr
  · have hl' := (mem_lowerModes m ell).mp hl
    omega
  · have hr' := (mem_reflectedModes m ell).mp hr
    omega

theorem range_partition (m : ℕ) :
    Finset.range (m + 1) =
      (lowerModes m ∪ (lowerModes m).image (reflect m)) ∪ centerModes m := by
  ext ell
  simp only [Finset.mem_range, Finset.mem_union, mem_lowerModes,
    mem_reflectedModes, mem_centerModes]
  omega

theorem sum_reflection_partition (m : ℕ) (f : ℕ → ℝ) :
    ∑ ell ∈ Finset.range (m + 1), f ell =
      ∑ ell ∈ lowerModes m, (f ell + f (reflect m ell)) +
        if Even m then f (m / 2) else 0 := by
  classical
  rw [range_partition, Finset.sum_union (paired_center_disjoint m),
    Finset.sum_union (lower_reflected_disjoint m),
    Finset.sum_image (reflect_injective_on m), ← Finset.sum_add_distrib]
  congr 1
  rw [centerModes_eq]
  split_ifs <;> simp

theorem lower_frequency {m ell : ℕ} (hell : ell ∈ lowerModes m) :
    1 ≤ 2 * ell + 1 ∧ 2 * ell + 1 < m + 1 := by
  rw [mem_lowerModes] at hell
  omega

theorem reflected_frequency {m ell : ℕ} (hell : ell ≤ m) :
    2 * reflect m ell + 1 + (2 * ell + 1) = 2 * (m + 1) := by
  unfold reflect
  omega

theorem alpha_reflect {m ell : ℕ} (hell : ell ≤ m) :
    alpha m (reflect m ell) = Real.pi / 2 - alpha m ell := by
  have hH : (m : ℝ) + 1 ≠ 0 := by positivity
  unfold alpha reflect
  push_cast [Nat.cast_sub hell]
  field_simp
  ring

theorem beta_reflect {m ell : ℕ} (hell : ell ≤ m) :
    beta m (reflect m ell) = Real.pi - beta m ell := by
  have hH : (m : ℝ) + 1 ≠ 0 := by positivity
  unfold beta reflect
  push_cast [Nat.cast_sub hell]
  field_simp
  ring

theorem beta_eq_twice_alpha (m ell : ℕ) : beta m ell = 2 * alpha m ell := by
  have hH : (m : ℝ) + 1 ≠ 0 := by positivity
  unfold beta alpha
  field_simp [hH]
  ring

theorem alpha_bounds {m ell : ℕ} (hell : ell ∈ Finset.range (m + 1)) :
    0 < alpha m ell ∧ alpha m ell < Real.pi / 2 := by
  have helle : ell ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hell)
  have hr : ((2 * ell + 1 : ℕ) : ℝ) < 2 * ((m : ℝ) + 1) := by
    exact_mod_cast (show 2 * ell + 1 < 2 * (m + 1) by omega)
  constructor
  · unfold alpha
    positivity
  · unfold alpha
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * ((m : ℝ) + 1))).mpr
    nlinarith [mul_lt_mul_of_pos_right hr Real.pi_pos]

theorem sin_alpha_pos {m ell : ℕ} (hell : ell ∈ Finset.range (m + 1)) :
    0 < Real.sin (alpha m ell) := by
  have ha := alpha_bounds hell
  exact Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [Real.pi_pos])

theorem beta_bounds {m ell : ℕ} (hell : ell ∈ Finset.range (m + 1)) :
    0 < beta m ell ∧ beta m ell < Real.pi := by
  have ha := alpha_bounds hell
  rw [beta_eq_twice_alpha]
  constructor <;> linarith

theorem beta_strict_mono (m : ℕ) : StrictMono (beta m) := by
  intro i j hij
  unfold beta
  apply (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * ((m : ℝ) + 1))).mpr
  apply mul_lt_mul_of_pos_right _ Real.pi_pos
  exact_mod_cast (show 2 * i + 1 < 2 * j + 1 by omega)

theorem lower_alpha_bounds {m ell : ℕ} (hell : ell ∈ lowerModes m) :
    0 < alpha m ell ∧ alpha m ell < Real.pi / 4 := by
  have hr : ((2 * ell + 1 : ℕ) : ℝ) < (m : ℝ) + 1 := by
    exact_mod_cast (lower_frequency hell).2
  have hH : 0 < (m : ℝ) + 1 := by positivity
  constructor
  · unfold alpha
    positivity
  · unfold alpha
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * ((m : ℝ) + 1))).mpr
    nlinarith [mul_lt_mul_of_pos_right hr Real.pi_pos]

theorem lower_beta_bounds {m ell : ℕ} (hell : ell ∈ lowerModes m) :
    0 < beta m ell ∧ beta m ell < Real.pi / 2 := by
  have ha := lower_alpha_bounds hell
  rw [beta_eq_twice_alpha]
  constructor <;> linarith

theorem lower_trig_denominators {m ell : ℕ} (hell : ell ∈ lowerModes m) :
    0 < Real.sin (alpha m ell) ∧ 0 < Real.cos (alpha m ell) := by
  have ha := lower_alpha_bounds hell
  have hp := Real.pi_pos
  exact ⟨Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith),
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩⟩

theorem cos_beta_pos {m ell : ℕ} (hell : ell ∈ lowerModes m) :
    0 < Real.cos (beta m ell) := by
  have hb := lower_beta_bounds hell
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hb.2⟩

theorem cotangent_reflect {m ell : ℕ} (hell : ell ≤ m) :
    RademacherFiniteS1.cotangent (alpha m (reflect m ell)) = Real.tan (alpha m ell) := by
  rw [alpha_reflect hell]
  change Real.cos (Real.pi / 2 - alpha m ell) /
      Real.sin (Real.pi / 2 - alpha m ell) = Real.tan (alpha m ell)
  rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, Real.tan_eq_sin_div_cos]

theorem cos_beta_reflect {m ell : ℕ} (hell : ell ≤ m) :
    Real.cos (beta m (reflect m ell)) = - Real.cos (beta m ell) := by
  rw [beta_reflect hell, Real.cos_pi_sub]

theorem cos_beta_neg {m ell : ℕ}
    (hell : ell ∈ (lowerModes m).image (reflect m)) :
    Real.cos (beta m ell) < 0 := by
  rcases Finset.mem_image.mp hell with ⟨k, hk, rfl⟩
  rw [cos_beta_reflect (lowerModes_le hk)]
  exact neg_neg_of_pos (cos_beta_pos hk)

theorem eigenvalue_le_rho {m ell : ℕ} (hell : ell ∈ Finset.range (m + 1)) :
    Real.cos (beta m ell) ≤ rho m := by
  by_cases he : ell = 0
  · subst ell
    simp only [beta, rho, Nat.mul_zero, zero_add, Nat.cast_one, one_mul, le_refl]
  · have hb := beta_bounds hell
    have h0 : 0 ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
    have hb0 := beta_bounds h0
    have hlt := beta_strict_mono m (show 0 < ell by omega)
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hb0.1) (le_of_lt hb.2) hlt
    have hr : Real.cos (beta m 0) = rho m := by simp [beta, rho]
    rw [hr] at hc
    exact le_of_lt hc

theorem neg_rho_le_eigenvalue {m ell : ℕ} (hell : ell ∈ Finset.range (m + 1)) :
    -rho m ≤ Real.cos (beta m ell) := by
  have hle : ell ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hell)
  have hmem : reflect m ell ∈ Finset.range (m + 1) := by
    rw [Finset.mem_range]
    unfold reflect
    omega
  have he := eigenvalue_le_rho hmem
  rw [cos_beta_reflect hle] at he
  linarith

theorem alpha_center {m : ℕ} (hm : Even m) :
    alpha m (m / 2) = Real.pi / 4 := by
  have hhalf := even_twice_half hm
  have hr : ((2 * (m / 2) + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
    exact_mod_cast congrArg (fun x : ℕ => x + 1) hhalf
  have hH : (m : ℝ) + 1 ≠ 0 := by positivity
  unfold alpha
  rw [hr]
  field_simp

theorem beta_center {m : ℕ} (hm : Even m) :
    beta m (m / 2) = Real.pi / 2 := by
  rw [beta_eq_twice_alpha, alpha_center hm]
  ring

theorem cotangent_pi_div_four : RademacherFiniteS1.cotangent (Real.pi / 4) = 1 := by
  change Real.cos (Real.pi / 4) / Real.sin (Real.pi / 4) = 1
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  exact div_self (by positivity)

theorem cos_beta_zero_iff {m ell : ℕ} (hell : ell ∈ Finset.range (m + 1)) :
    Real.cos (beta m ell) = 0 ↔ 2 * ell = m := by
  constructor
  · intro hz
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hr
    · have hpos := cos_beta_pos ((mem_lowerModes m ell).mpr hl)
      linarith
    · have hle : ell ≤ m := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hell)
      have hneg := cos_beta_neg ((mem_reflectedModes m ell).mpr ⟨hle, hr⟩)
      linarith
  · intro he
    have hm : Even m := ⟨ell, by omega⟩
    have helleq : ell = m / 2 := by omega
    rw [helleq, beta_center hm, Real.cos_pi_div_two]

theorem zero_mem_lowerModes {m : ℕ} (hm : 1 ≤ m) : 0 ∈ lowerModes m := by
  rw [mem_lowerModes]
  omega

theorem amplitude_pos {m : ℕ} (hm : 1 ≤ m) : 0 < amplitude m := by
  have ht := lower_trig_denominators (zero_mem_lowerModes hm)
  simp only [alpha, Nat.mul_zero, zero_add, Nat.cast_one, one_mul] at ht
  change 0 < (1 / ((m : ℝ) + 1)) *
    (Real.cos (Real.pi / (4 * ((m : ℝ) + 1))) / Real.sin (Real.pi / (4 * ((m : ℝ) + 1))))
  exact mul_pos (by positivity) (div_pos ht.2 ht.1)

theorem rho_pos {m : ℕ} (hm : 1 ≤ m) : 0 < rho m := by
  simpa only [rho, beta, Nat.mul_zero, zero_add, Nat.cast_one, one_mul] using
    cos_beta_pos (zero_mem_lowerModes hm)

theorem rho_lt_one {m : ℕ} (hm : 1 ≤ m) : rho m < 1 := by
  have hb := lower_beta_bounds (zero_mem_lowerModes hm)
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := beta m 0)
    (by norm_num) (by linarith [Real.pi_pos]) hb.1
  simpa only [rho, beta, Nat.mul_zero, zero_add, Nat.cast_one, one_mul, Real.cos_zero] using hc

theorem normalizer_pos {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    0 < amplitude m * rho m ^ n := by
  exact mul_pos (amplitude_pos hm) (pow_pos (rho_pos hm) n)

theorem principal_cotangent_pos {m : ℕ} (hm : 1 ≤ m) :
    0 < RademacherFiniteS1.cotangent (Real.pi / (4 * ((m : ℝ) + 1))) := by
  have ht := lower_trig_denominators (zero_mem_lowerModes hm)
  simp only [alpha, Nat.mul_zero, zero_add, Nat.cast_one, one_mul] at ht
  exact div_pos ht.2 ht.1

theorem sign_reflect {m ell : ℕ} (hell : ell ≤ m) :
    (-1 : ℝ) ^ (reflect m ell) = (-1 : ℝ) ^ ell * (-1 : ℝ) ^ m := by
  have hsum : ell + reflect m ell = m := by unfold reflect; omega
  have hp : (-1 : ℝ) ^ m = (-1 : ℝ) ^ ell * (-1 : ℝ) ^ (reflect m ell) := by
    rw [← pow_add, hsum]
  have hs : (-1 : ℝ) ^ ell * (-1 : ℝ) ^ ell = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (-1 : ℝ) ^ (reflect m ell) =
        ((-1 : ℝ) ^ ell * (-1 : ℝ) ^ ell) * (-1 : ℝ) ^ (reflect m ell) := by rw [hs, one_mul]
    _ = (-1 : ℝ) ^ ell * ((-1 : ℝ) ^ ell * (-1 : ℝ) ^ (reflect m ell)) := by ring
    _ = (-1 : ℝ) ^ ell * (-1 : ℝ) ^ m := by rw [hp]

theorem pair_term {m ell : ℕ} (hell : ell ∈ lowerModes m) (n : ℕ) :
    rawTerm m n ell + rawTerm m n (reflect m ell) = pairedTerm m n ell := by
  unfold rawTerm pairedTerm epsilon
  rw [sign_reflect (lowerModes_le hell), cotangent_reflect (lowerModes_le hell),
    cos_beta_reflect (lowerModes_le hell), neg_pow, pow_add]
  ring

theorem full_sum_pairing (m n : ℕ) :
    ∑ ell ∈ Finset.range (m + 1), rawTerm m n ell =
      ∑ ell ∈ lowerModes m, pairedTerm m n ell +
        if Even m then (-1 : ℝ) ^ (m / 2) * (0 : ℝ) ^ n else 0 := by
  rw [sum_reflection_partition]
  congr 1
  · exact Finset.sum_congr rfl (fun ell hell => pair_term hell n)
  · by_cases hm : Even m
    · simp only [hm, ite_true, rawTerm, alpha_center hm, beta_center hm,
        cotangent_pi_div_four, Real.cos_pi_div_two, mul_one]
    · simp only [hm, ite_false]

theorem raw_spectral_pairing (m n : ℕ) :
    (1 / ((m : ℝ) + 1)) * ∑ ell ∈ Finset.range (m + 1), rawTerm m n ell =
      (1 / ((m : ℝ) + 1)) * ∑ ell ∈ lowerModes m, pairedTerm m n ell + zeroMode m n := by
  rw [full_sum_pairing, mul_add]
  congr 1
  by_cases hm : Even m
  · simp only [hm, ite_true, zeroMode]
    ring
  · simp only [hm, ite_false, zeroMode, mul_zero]

theorem killedMass_paired (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (n : ℕ) :
    killedMass RademacherCosine.law h n 0 =
      (1 / ((m : ℝ) + 1)) * ∑ ell ∈ lowerModes m, pairedTerm m n ell + zeroMode m n := by
  rw [RademacherFiniteS1.killedMass_finite_s1 m hm h hmh hhm n]
  exact raw_spectral_pairing m n

theorem closedStrip_probability_paired (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => RademacherCosine.law)).real (Shao.closedStrip h) =
      (1 / ((m : ℝ) + 1)) * ∑ ell ∈ lowerModes m, pairedTerm m n ell + zeroMode m n := by
  rw [RademacherFiniteS1.closedStrip_probability_finite_s1 m hm h hmh hhm n]
  exact raw_spectral_pairing m n

theorem closedStrip_probability_eq_killedMass (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => RademacherCosine.law)).real (Shao.closedStrip h) =
      killedMass RademacherCosine.law h n 0 := by
  rw [closedStrip_probability_paired m hm h hmh hhm n,
    killedMass_paired m hm h hmh hhm n]

theorem last_mode_coefficient (m : ℕ) :
    (-1 : ℝ) ^ m / ((m : ℝ) + 1) * RademacherFiniteS1.cotangent (alpha m m) =
      (-1 : ℝ) ^ m / ((m : ℝ) + 1) *
        Real.tan (Real.pi / (4 * ((m : ℝ) + 1))) := by
  have hr : reflect m 0 = m := by simp [reflect]
  have hc := cotangent_reflect (m := m) (ell := 0) (by omega)
  simpa only [hr, alpha, Nat.mul_zero, zero_add, Nat.cast_one, one_mul] using
    congrArg (fun x : ℝ => (-1 : ℝ) ^ m / ((m : ℝ) + 1) * x) hc

theorem last_mode_eigenvalue (m : ℕ) : Real.cos (beta m m) = -rho m := by
  have hc := cos_beta_reflect (m := m) (ell := 0) (by omega)
  simpa only [reflect, Nat.sub_zero, beta, rho, Nat.mul_zero, zero_add, Nat.cast_one, one_mul] using hc

theorem last_mode_contribution (m n : ℕ) :
    (1 / ((m : ℝ) + 1)) * rawTerm m n m =
      ((-1 : ℝ) ^ m / ((m : ℝ) + 1) *
        Real.tan (Real.pi / (4 * ((m : ℝ) + 1)))) * (-rho m) ^ n := by
  unfold rawTerm
  rw [last_mode_eigenvalue]
  calc
    (1 / ((m : ℝ) + 1)) *
        ((-1 : ℝ) ^ m * RademacherFiniteS1.cotangent (alpha m m) * (-rho m) ^ n) =
      ((-1 : ℝ) ^ m / ((m : ℝ) + 1) * RademacherFiniteS1.cotangent (alpha m m)) *
        (-rho m) ^ n := by ring
    _ = _ := by rw [last_mode_coefficient]

private theorem cotangent_pair_factor (x e : ℝ)
    (hs : Real.sin x ≠ 0) (hc : Real.cos x ≠ 0) :
    RademacherFiniteS1.cotangent x + e * Real.tan x =
      RademacherFiniteS1.cotangent x * (1 + e * (Real.tan x) ^ 2) := by
  have ht : RademacherFiniteS1.cotangent x * (Real.tan x) ^ 2 = Real.tan x := by
    change (Real.cos x / Real.sin x) * (Real.tan x) ^ 2 = Real.tan x
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hs, hc]
  calc
    _ = RademacherFiniteS1.cotangent x +
        e * (RademacherFiniteS1.cotangent x * (Real.tan x) ^ 2) := by rw [ht]
    _ = _ := by ring

private theorem normalization_factor (A C P s b q : ℝ) (hc : C ≠ 0) (hp : P ≠ 0) :
    (A * C) * P * (s * (b / C) * (q / P)) = A * (s * b * q) := by
  calc
    _ = A * s * (C * (b / C)) * (P * (q / P)) := by ring
    _ = _ := by rw [mul_div_cancel₀ _ hc, mul_div_cancel₀ _ hp]; ring

theorem first_pair (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (1 / ((m : ℝ) + 1)) * pairedTerm m n 0 =
      amplitude m * rho m ^ n *
        (1 + epsilon m n * (Real.tan (Real.pi / (4 * ((m : ℝ) + 1)))) ^ 2) := by
  have ht := lower_trig_denominators (zero_mem_lowerModes hm)
  simp only [alpha, Nat.mul_zero, zero_add, Nat.cast_one, one_mul] at ht
  have hs := ne_of_gt ht.1
  have hc := ne_of_gt ht.2
  unfold pairedTerm amplitude rho
  simp only [alpha, beta, Nat.mul_zero, zero_add, Nat.cast_one, one_mul, pow_zero]
  rw [cotangent_pair_factor _ _ hs hc]
  ring

theorem normalized_term (m : ℕ) (hm : 1 ≤ m) (n ell : ℕ) :
    amplitude m * rho m ^ n * normalizedTerm m n ell =
      (1 / ((m : ℝ) + 1)) * pairedTerm m n ell := by
  have hr := ne_of_gt (rho_pos hm)
  have hrn := ne_of_gt (pow_pos (rho_pos hm) n)
  have hc := ne_of_gt (principal_cotangent_pos hm)
  unfold normalizedTerm amplitude pairedTerm
  rw [div_pow]
  exact normalization_factor _ _ _ _ _ _ hc hrn

theorem paired_sum_normalized (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (1 / ((m : ℝ) + 1)) * ∑ ell ∈ lowerModes m, pairedTerm m n ell + zeroMode m n =
      amplitude m * rho m ^ n *
        (1 + epsilon m n * (Real.tan (Real.pi / (4 * ((m : ℝ) + 1)))) ^ 2 + remainder m n) := by
  classical
  have hsum := Finset.sum_erase_add (lowerModes m) (pairedTerm m n) (zero_mem_lowerModes hm)
  have hnorm : amplitude m * rho m ^ n * (zeroMode m n / (amplitude m * rho m ^ n)) =
      zeroMode m n := by
    exact mul_div_cancel₀ _ (ne_of_gt (normalizer_pos hm n))
  have heq : amplitude m * rho m ^ n *
      (∑ ell ∈ (lowerModes m).erase 0, normalizedTerm m n ell) =
      (1 / ((m : ℝ) + 1)) * ∑ ell ∈ (lowerModes m).erase 0, pairedTerm m n ell := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun ell _ => normalized_term m hm n ell)
  calc
    _ = (1 / ((m : ℝ) + 1)) *
          (∑ ell ∈ (lowerModes m).erase 0, pairedTerm m n ell) +
        amplitude m * rho m ^ n *
          (1 + epsilon m n * (Real.tan (Real.pi / (4 * ((m : ℝ) + 1)))) ^ 2) +
        zeroMode m n := by
      rw [← hsum, mul_add, first_pair m hm n]
    _ = amplitude m * rho m ^ n *
          (∑ ell ∈ (lowerModes m).erase 0, normalizedTerm m n ell) +
        amplitude m * rho m ^ n *
          (1 + epsilon m n * (Real.tan (Real.pi / (4 * ((m : ℝ) + 1)))) ^ 2) +
        amplitude m * rho m ^ n * (zeroMode m n / (amplitude m * rho m ^ n)) := by
      rw [heq, hnorm]
    _ = _ := by unfold remainder; ring

theorem killedMass_normalized (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (n : ℕ) :
    killedMass RademacherCosine.law h n 0 =
      amplitude m * rho m ^ n *
        (1 + epsilon m n * (Real.tan (Real.pi / (4 * ((m : ℝ) + 1)))) ^ 2 + remainder m n) := by
  rw [killedMass_paired m hm h hmh hhm n]
  exact paired_sum_normalized m hm n

theorem closedStrip_probability_normalized (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => RademacherCosine.law)).real (Shao.closedStrip h) =
      amplitude m * rho m ^ n *
        (1 + epsilon m n * (Real.tan (Real.pi / (4 * ((m : ℝ) + 1)))) ^ 2 + remainder m n) := by
  rw [closedStrip_probability_paired m hm h hmh hhm n]
  exact paired_sum_normalized m hm n

theorem zeroMode_positive_time (m : ℕ) {n : ℕ} (hn : 1 ≤ n) : zeroMode m n = 0 := by
  have hn0 : n ≠ 0 := by omega
  simp [zeroMode, zero_pow hn0]

theorem zeroMode_zero (m : ℕ) :
    zeroMode m 0 = if Even m then (-1 : ℝ) ^ (m / 2) / ((m : ℝ) + 1) else 0 := by
  simp [zeroMode]

theorem remainder_positive_time (m : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    remainder m n = ∑ ell ∈ (lowerModes m).erase 0, normalizedTerm m n ell := by
  simp only [remainder, zeroMode_positive_time m hn, zero_div, add_zero]

theorem remainder_frequency {m ell : ℕ} (hell : ell ∈ (lowerModes m).erase 0) :
    3 ≤ 2 * ell + 1 ∧ 2 * ell + 1 < m + 1 ∧ Odd (2 * ell + 1) := by
  have hp := Finset.mem_erase.mp hell
  have hf := lower_frequency hp.2
  refine ⟨by omega, hf.2, ?_⟩
  exact ⟨ell, by omega⟩

theorem normalized_zero (m : ℕ) (hm : 1 ≤ m) :
    amplitude m * (1 + (-1 : ℝ) ^ m *
      (Real.tan (Real.pi / (4 * ((m : ℝ) + 1)))) ^ 2 + remainder m 0) = 1 := by
  have hz := RademacherFiniteS1.finite_s1_zero m hm
  have hp := raw_spectral_pairing m 0
  have hn := paired_sum_normalized m hm 0
  have hraw : (1 / ((m : ℝ) + 1)) *
      ∑ ell ∈ Finset.range (m + 1), rawTerm m 0 ell = 1 := hz
  rw [hp, hn] at hraw
  simpa only [epsilon, Nat.zero_add, pow_zero, mul_one] using hraw

theorem closedStrip_probability_zero (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) :
    (Measure.pi (fun _ : Fin 0 => RademacherCosine.law)).real (Shao.closedStrip h) = 1 := by
  rw [RademacherFiniteS1.closedStrip_probability_finite_s1 m hm h hmh hhm 0]
  exact RademacherFiniteS1.finite_s1_zero m hm

theorem lowerModes_one : lowerModes 1 = {0} := by
  ext ell
  simp only [mem_lowerModes, Finset.mem_singleton]
  omega

theorem lowerModes_two : lowerModes 2 = {0} := by
  ext ell
  simp only [mem_lowerModes, Finset.mem_singleton]
  omega

theorem tail_one_empty : (lowerModes 1).erase 0 = ∅ := by
  rw [lowerModes_one]
  simp

theorem tail_two_empty : (lowerModes 2).erase 0 = ∅ := by
  rw [lowerModes_two]
  simp

theorem remainder_one (n : ℕ) : remainder 1 n = 0 := by
  simp [remainder, tail_one_empty, zeroMode]

theorem remainder_two_positive_time {n : ℕ} (hn : 1 ≤ n) : remainder 2 n = 0 := by
  rw [remainder_positive_time 2 hn, tail_two_empty, Finset.sum_empty]

theorem zeroMode_two_zero : zeroMode 2 0 = -(1 / 3 : ℝ) := by
  norm_num [zeroMode]

theorem remainder_two_zero : remainder 2 0 = -1 / (3 * amplitude 2) := by
  rw [remainder, tail_two_empty, Finset.sum_empty, zeroMode_two_zero]
  simp only [pow_zero, mul_one, zero_add]
  ring

end

end Shao.OQ4.RademacherSpectralPairing
