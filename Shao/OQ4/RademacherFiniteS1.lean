import Shao.OQ4.RademacherAllModes

/-!
# Explicit finite survival formula at the zero integer start

The finite lattice, modes, law and kernel are those of the certified upstream
modules. All time powers are natural powers in the real numbers.
-/

open scoped BigOperators
open MeasureTheory

namespace Shao.OQ4.RademacherFiniteS1

open RademacherFiniteBasis

/-- The cotangent is used only at the nonzero angles established below. -/
noncomputable def cotangent (x : ℝ) : ℝ := Real.cos x / Real.sin x

private theorem vector_zero_raw (m j : ℕ) :
    vector m j 0 = Real.sin ((j : ℝ) * Real.pi / 2) := by
  unfold vector phi theta RademacherCosine.angle
  norm_num only [Int.cast_zero, zero_add]
  congr 1
  have hH : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- Every source mode has its actual sine value at the zero start. -/
theorem vector_zero (m : ℕ) (_hm : 1 ≤ m) (j : ℕ) (_hj : j ∈ modes m) :
    vector m j 0 = Real.sin ((j : ℝ) * Real.pi / 2) :=
  vector_zero_raw m j

/-- The source interval is exactly the interval ending at twice H minus one. -/
theorem modes_eq (m : ℕ) :
    modes m = Finset.Icc 1 (2 * (m + 1) - 1) := by
  unfold modes
  congr 1

/-- The even source indices are precisely twice 1,...,m. -/
theorem even_mode_mem_iff (m k : ℕ) :
    2 * k ∈ modes m ↔ k ∈ Finset.Icc 1 m := by
  simp only [modes, Finset.mem_Icc]
  omega

/-- The odd source indices are precisely the image of range (m+1). -/
theorem odd_mode_mem_iff (m ell : ℕ) :
    2 * ell + 1 ∈ modes m ↔ ell ∈ Finset.range (m + 1) := by
  simp only [modes, Finset.mem_Icc, Finset.mem_range]
  omega

/-- Every source index belongs to exactly one of the displayed parity forms. -/
theorem mode_parity_partition (m j : ℕ) (hj : j ∈ modes m) :
    (∃ k ∈ Finset.Icc 1 m, j = 2 * k) ∨
      (∃ ell ∈ Finset.range (m + 1), j = 2 * ell + 1) := by
  simp only [modes, Finset.mem_Icc] at hj
  rcases Nat.mod_two_eq_zero_or_one j with he | ho
  · left
    refine ⟨j / 2, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · right
    refine ⟨j / 2, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega

/-- The inverse is natural division, applied only to a legal odd source mode. -/
theorem odd_mode_inverse (m j : ℕ) (hj : j ∈ modes m) (hodd : j % 2 = 1) :
    (j - 1) / 2 ∈ Finset.range (m + 1) ∧ 2 * ((j - 1) / 2) + 1 = j := by
  simp only [modes, Finset.mem_Icc] at hj
  simp only [Finset.mem_range]
  omega

theorem odd_mode_injective : Function.Injective (fun ell : ℕ => 2 * ell + 1) := by
  intro a b hab
  change 2 * a + 1 = 2 * b + 1 at hab
  omega

private theorem vector_even_zero_raw (m k : ℕ) : vector m (2 * k) 0 = 0 := by
  rw [vector_zero_raw]
  have he : ((2 * k : ℕ) : ℝ) * Real.pi / 2 = (k : ℝ) * Real.pi := by
    push_cast
    ring
  rw [he, Real.sin_nat_mul_pi]

/-- Every even mode in the source interval vanishes at the zero start. -/
theorem vector_even_zero (m : ℕ) (_hm : 1 ≤ m) (k : ℕ)
    (_hk : k ∈ Finset.Icc 1 m) : vector m (2 * k) 0 = 0 :=
  vector_even_zero_raw m k

private theorem vector_odd_zero_raw (m ell : ℕ) :
    vector m (2 * ell + 1) 0 = (-1 : ℝ) ^ ell := by
  rw [vector_zero_raw]
  have ho : ((2 * ell + 1 : ℕ) : ℝ) * Real.pi / 2 =
      (ell : ℝ) * Real.pi + Real.pi / 2 := by
    push_cast
    ring
  rw [ho, Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]

/-- Every legal odd mode has the signed value specified by its actual index. -/
theorem vector_odd_zero (m : ℕ) (_hm : 1 ≤ m) (ell : ℕ)
    (_hell : ell ∈ Finset.range (m + 1)) :
    vector m (2 * ell + 1) 0 = (-1 : ℝ) ^ ell :=
  vector_odd_zero_raw m ell

private theorem sum_states_range (m : ℕ) (F : ℤ → ℝ) :
    (∑ s ∈ states m, F s) =
      ∑ k ∈ Finset.range (2 * m + 1), F ((k : ℤ) - (m : ℤ)) := by
  classical
  refine Finset.sum_bij (fun s _ => (s + (m : ℤ)).toNat) ?_ ?_ ?_ ?_
  · intro s hs
    simp only [states, Finset.mem_Icc] at hs
    simp only [Finset.mem_range]
    omega
  · intro s hs t ht he
    simp only [states, Finset.mem_Icc] at hs ht
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    refine ⟨(k : ℤ) - (m : ℤ), ?_, ?_⟩
    · simp only [states, Finset.mem_Icc]
      omega
    · omega
  · intro s hs
    simp only [states, Finset.mem_Icc] at hs
    congr 1
    omega

private theorem sum_vector_range (m j : ℕ) :
    (∑ s ∈ states m, vector m j s) =
      ∑ k ∈ Finset.range (2 * m + 1),
        Real.sin (theta m j * ((k : ℝ) + 1)) := by
  rw [sum_states_range]
  apply Finset.sum_congr rfl
  intro k hk
  unfold vector phi
  push_cast
  congr 1
  ring

private theorem sine_sum_telescope (a : ℝ) (N : ℕ) :
    2 * Real.sin (a / 2) *
        (∑ k ∈ Finset.range N, Real.sin (a * ((k : ℝ) + 1))) =
      Real.cos (a / 2) - Real.cos (a * ((N : ℝ) + 1 / 2)) := by
  induction N with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, Nat.cast_zero, zero_add]
      ring_nf
  | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have hterm :
          Real.cos (a * ((N : ℝ) + 1 / 2)) -
              Real.cos (a * (((N : ℝ) + 1) + 1 / 2)) =
            2 * Real.sin (a / 2) * Real.sin (a * ((N : ℝ) + 1)) := by
        have hleft : a * ((N : ℝ) + 1 / 2) = a * ((N : ℝ) + 1) - a / 2 := by ring
        have hright : a * (((N : ℝ) + 1) + 1 / 2) =
            a * ((N : ℝ) + 1) + a / 2 := by ring
        rw [hleft, hright, Real.cos_sub, Real.cos_add]
        ring
      push_cast
      linarith

/-- Every cotangent angle used by the odd-mode formula lies strictly inside (0,pi/2). -/
theorem odd_half_angle_bounds (m : ℕ) (_hm : 1 ≤ m) (ell : ℕ)
    (hell : ell ∈ Finset.range (m + 1)) :
    0 < (((2 * ell + 1 : ℕ) : ℝ) * Real.pi / (4 * ((m : ℝ) + 1))) ∧
      (((2 * ell + 1 : ℕ) : ℝ) * Real.pi / (4 * ((m : ℝ) + 1))) < Real.pi / 2 := by
  simp only [Finset.mem_range] at hell
  constructor
  · positivity
  · have hj : (((2 * ell + 1 : ℕ) : ℝ)) < 2 * ((m : ℝ) + 1) := by
      push_cast
      exact_mod_cast (show 2 * ell + 1 < 2 * (m + 1) by omega)
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * ((m : ℝ) + 1))).2
    nlinarith [mul_lt_mul_of_pos_right hj Real.pi_pos]

/-- The displayed cotangent denominator never vanishes. -/
theorem odd_half_angle_sin_ne_zero (m : ℕ) (hm : 1 ≤ m) (ell : ℕ)
    (hell : ell ∈ Finset.range (m + 1)) :
    Real.sin (((2 * ell + 1 : ℕ) : ℝ) * Real.pi / (4 * ((m : ℝ) + 1))) ≠ 0 := by
  obtain ⟨hpos, hlt⟩ := odd_half_angle_bounds m hm ell hell
  apply ne_of_gt
  apply Real.sin_pos_of_pos_of_lt_pi hpos
  linarith [Real.pi_pos]


/-- The odd-mode finite counting sum is the indicated cotangent. -/
theorem sum_vector_odd (m : ℕ) (hm : 1 ≤ m) (ell : ℕ)
    (hell : ell ∈ Finset.range (m + 1)) :
    (∑ s ∈ states m, vector m (2 * ell + 1) s) =
      cotangent (((2 * ell + 1 : ℕ) : ℝ) * Real.pi / (4 * ((m : ℝ) + 1))) := by
  let j := 2 * ell + 1
  let t := (j : ℝ) * Real.pi / (4 * ((m : ℝ) + 1))
  have hH : (m : ℝ) + 1 ≠ 0 := by positivity
  have hhalf : theta m j / 2 = t := by
    dsimp [theta, RademacherCosine.angle, t]
    field_simp
    ring
  have hend :
      theta m j * (((2 * m + 1 : ℕ) : ℝ) + 1 / 2) =
        (j : ℝ) * Real.pi - t := by
    dsimp [theta, RademacherCosine.angle, t]
    push_cast
    field_simp
    ring
  have hsign : (-1 : ℝ) ^ j = -1 := by
    dsimp [j]
    simp [pow_add, pow_mul]
  have htel := sine_sum_telescope (theta m j) (2 * m + 1)
  rw [← sum_vector_range m j, hhalf, hend, Real.cos_sub,
    Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, hsign] at htel
  have hsin : Real.sin t ≠ 0 := odd_half_angle_sin_ne_zero m hm ell hell
  change (∑ s ∈ states m, vector m j s) = Real.cos t / Real.sin t
  apply (eq_div_iff hsin).2
  nlinarith [htel]

/-- The coefficient uses the upstream norm H and the same unnormalised finite sum. -/
theorem survivalCoefficient_odd (m : ℕ) (hm : 1 ≤ m) (ell : ℕ)
    (hell : ell ∈ Finset.range (m + 1)) :
    RademacherAllModes.survivalCoefficient m (2 * ell + 1) =
      (1 / ((m : ℝ) + 1)) *
        cotangent (((2 * ell + 1 : ℕ) : ℝ) * Real.pi / (4 * ((m : ℝ) + 1))) := by
  rw [RademacherAllModes.survivalCoefficient_eq, sum_vector_odd m hm ell hell]

private theorem sum_modes_odd (m : ℕ) (F : ℕ → ℝ)
    (heven : ∀ k ∈ Finset.Icc 1 m, F (2 * k) = 0) :
    (∑ j ∈ modes m, F j) =
      ∑ ell ∈ Finset.range (m + 1), F (2 * ell + 1) := by
  classical
  let odds := (Finset.range (m + 1)).image (fun ell => 2 * ell + 1)
  have hsub : odds ⊆ modes m := by
    intro j hj
    obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hj
    exact (odd_mode_mem_iff m ell).2 hell
  calc
    (∑ j ∈ modes m, F j) = ∑ j ∈ odds, F j := by
      symm
      apply Finset.sum_subset hsub
      intro j hj hjnot
      rcases mode_parity_partition m j hj with ⟨k, hk, rfl⟩ | ⟨ell, hell, rfl⟩
      · exact heven k hk
      · exact False.elim (hjnot (Finset.mem_image.mpr ⟨ell, hell, rfl⟩))
    _ = ∑ ell ∈ Finset.range (m + 1), F (2 * ell + 1) := by
      dsimp [odds]
      apply Finset.sum_image
      intro a ha b hb hab
      exact odd_mode_injective hab

private theorem theta_formula (m j : ℕ) :
    theta m j = (j : ℝ) * Real.pi / (2 * ((m : ℝ) + 1)) := by
  unfold theta RademacherCosine.angle
  ring

/-- Exact survival mass for all natural times, with signed real mode powers. -/
theorem killedMass_finite_s1 (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (n : ℕ) :
    killedMass RademacherCosine.law h n 0 =
      (1 / ((m : ℝ) + 1)) *
        ∑ ell ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ ell *
            cotangent (((2 * ell + 1 : ℕ) : ℝ) * Real.pi / (4 * ((m : ℝ) + 1))) *
            (Real.cos (((2 * ell + 1 : ℕ) : ℝ) * Real.pi /
              (2 * ((m : ℝ) + 1)))) ^ n := by
  have hzero : (0 : ℤ) ∈ states m := by simp [states]
  have hraw := RademacherAllModes.killedMass_spectrum m hm h hmh hhm 0 hzero n
  simp only [Int.cast_zero] at hraw
  rw [hraw, sum_modes_odd m
    (fun j => RademacherAllModes.survivalCoefficient m j * (mu m j) ^ n * vector m j 0)
    (by
      intro k hk
      rw [vector_even_zero_raw]
      ring)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  rw [survivalCoefficient_odd m hm ell hell, vector_odd_zero_raw]
  unfold mu
  rw [theta_formula]
  ring

/-- The same complete finite S1 is the actual product-law closed-strip probability. -/
theorem closedStrip_probability_finite_s1 (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => RademacherCosine.law)).real (Shao.closedStrip h) =
      (1 / ((m : ℝ) + 1)) *
        ∑ ell ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ ell *
            cotangent (((2 * ell + 1 : ℕ) : ℝ) * Real.pi / (4 * ((m : ℝ) + 1))) *
            (Real.cos (((2 * ell + 1 : ℕ) : ℝ) * Real.pi /
              (2 * ((m : ℝ) + 1)))) ^ n := by
  have hh : 0 ≤ h := le_trans (Nat.cast_nonneg m) hmh
  rw [← killedMass_eq_closedStrip_probability RademacherCosine.law n h hh]
  exact killedMass_finite_s1 m hm h hmh hhm n

/-- Zero time uses the same full sum, including zero to the zeroth power. -/
theorem finite_s1_zero (m : ℕ) (hm : 1 ≤ m) :
    (1 / ((m : ℝ) + 1)) *
        (∑ ell ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ ell *
            cotangent (((2 * ell + 1 : ℕ) : ℝ) * Real.pi / (4 * ((m : ℝ) + 1))) *
            (Real.cos (((2 * ell + 1 : ℕ) : ℝ) * Real.pi /
              (2 * ((m : ℝ) + 1)))) ^ 0) = 1 := by
  rw [← killedMass_finite_s1 m hm (m : ℝ) le_rfl (by linarith) 0]
  simp [killedMass, killedAction_zero]

/-- At a nonnegative threshold below one, the actual first-step row from zero is zero. -/
theorem killedKernel_zero_low (h : ℝ) (hh : 0 ≤ h) (hh1 : h < 1) :
    killedKernel RademacherCosine.law h 0 = 0 := by
  have hrow := RademacherCosine.killedKernel_row 0 h (by simpa using hh)
    (by simpa using hh1) 0
  simpa using hrow

/-- The independent low-threshold mass branch uses the actual kernel semigroup. -/
theorem killedMass_low (h : ℝ) (hh : 0 ≤ h) (hh1 : h < 1) (n : ℕ) :
    killedMass RademacherCosine.law h n 0 = if n = 0 then 1 else 0 := by
  cases n with
  | zero =>
      simp [killedMass, killedAction_zero]
  | succ k =>
      simp only [Nat.succ_ne_zero, ite_false]
      unfold killedMass
      rw [show k + 1 = 1 + k by omega]
      rw [killedAction_semigroup RademacherCosine.law h 1 k 0 (fun _ : ℝ => 1)
        measurable_const ⟨1, by intro w; norm_num⟩]
      change (∫ w, killedAction RademacherCosine.law h k (fun _ : ℝ => 1) w
        ∂killedIterKernel RademacherCosine.law h 1 0) = 0
      have hone : killedIterKernel RademacherCosine.law h 1 0 =
          killedKernel RademacherCosine.law h 0 := by
        simp [killedIterKernel]
      rw [hone, killedKernel_zero_low h hh hh1]
      simp

/-- All natural times of the actual product-law probability in the low branch. -/
theorem closedStrip_probability_low (h : ℝ) (hh : 0 ≤ h) (hh1 : h < 1) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => RademacherCosine.law)).real (Shao.closedStrip h) =
      if n = 0 then 1 else 0 := by
  rw [← killedMass_eq_closedStrip_probability RademacherCosine.law n h hh]
  exact killedMass_low h hh hh1 n
end Shao.OQ4.RademacherFiniteS1
