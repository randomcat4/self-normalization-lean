import Shao.OQ4.RademacherCosine

open scoped BigOperators
open Finset MeasureTheory

namespace Shao.OQ4.RademacherFiniteBasis

noncomputable def states (m : ℕ) : Finset ℤ := Finset.Icc (-(m : ℤ)) (m : ℤ)
noncomputable def modes (m : ℕ) : Finset ℕ := Finset.Icc 1 (2 * m + 1)
noncomputable def theta (m j : ℕ) : ℝ := (j : ℝ) * RademacherCosine.angle m
noncomputable def mu (m j : ℕ) : ℝ := Real.cos (theta m j)
noncomputable def phi (m j : ℕ) (w : ℝ) : ℝ :=
  Real.sin (theta m j * (w + ((m : ℝ) + 1)))
noncomputable def vector (m j : ℕ) (s : ℤ) : ℝ := phi m j (s : ℝ)
noncomputable def coefficient (m j : ℕ) (F : ℤ → ℝ) : ℝ :=
  (1 / ((m : ℝ) + 1)) * ∑ s ∈ states m, F s * vector m j s

@[simp] theorem theta_one (m : ℕ) : theta m 1 = RademacherCosine.angle m := by
  simp [theta]
@[simp] theorem mu_one (m : ℕ) : mu m 1 = RademacherCosine.rho m := by
  simp [mu, RademacherCosine.rho]

/-- B0: the first sine mode is the certified principal cosine on the whole real line. -/
theorem phi_one (m : ℕ) (hm : 1 ≤ m) (w : ℝ) :
    phi m 1 w = Real.cos (RademacherCosine.angle m * w) := by
  have hd : (m : ℝ) + 1 ≠ 0 := by positivity
  have he : RademacherCosine.angle m * (w + ((m : ℝ) + 1)) =
      RademacherCosine.angle m * w + Real.pi / 2 := by
    dsimp [RademacherCosine.angle]
    field_simp
  simp only [phi, theta_one, he, Real.sin_add, Real.sin_pi_div_two,
    Real.cos_pi_div_two, mul_one, mul_zero, zero_add]

private def stateIndex (m : ℕ) (s : ℤ) : ℕ := (s + ((m : ℤ) + 1)).toNat
private def stateAt (m j : ℕ) : ℤ := (j : ℤ) - ((m : ℤ) + 1)

private theorem index_mem (m : ℕ) (s : ℤ) (hs : s ∈ states m) :
    stateIndex m s ∈ modes m := by
  simp only [states, mem_Icc] at hs
  simp only [modes, mem_Icc, stateIndex]
  omega
private theorem at_mem (m j : ℕ) (hj : j ∈ modes m) : stateAt m j ∈ states m := by
  simp only [modes, mem_Icc] at hj
  simp only [states, mem_Icc, stateAt]
  omega
private theorem at_index (m : ℕ) (s : ℤ) (hs : s ∈ states m) :
    stateAt m (stateIndex m s) = s := by
  simp only [states, mem_Icc] at hs
  simp only [stateAt, stateIndex]
  omega
private theorem index_at (m j : ℕ) (hj : j ∈ modes m) :
    stateIndex m (stateAt m j) = j := by
  simp only [modes, mem_Icc] at hj
  simp only [stateIndex, stateAt]
  omega
private theorem sum_states (m : ℕ) (f : ℤ → ℝ) :
    ∑ s ∈ states m, f s = ∑ j ∈ modes m, f (stateAt m j) := by
  exact Finset.sum_bij' (fun s _ => stateIndex m s) (fun j _ => stateAt m j)
    (index_mem m) (at_mem m) (at_index m) (index_at m) (by
      intro s hs
      rw [at_index m s hs])
private theorem sum_modes (m : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ modes m, f j = ∑ q ∈ range (2 * m + 1), f (q + 1) := by
  rw [modes, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

private theorem vector_at (m j q : ℕ) :
    vector m j (stateAt m q) =
      Real.sin ((j : ℝ) * Real.pi / (2 * ((m : ℝ) + 1)) * (q : ℝ)) := by
  unfold vector phi theta RademacherCosine.angle stateAt
  push_cast
  congr 1
  ring

private theorem telescope_cos (n : ℕ) (x : ℝ) :
    2 * Real.sin (x / 2) * ∑ q ∈ range n, Real.cos (((q : ℝ) + 1) * x) =
      Real.sin (((n : ℝ) + 1 / 2) * x) - Real.sin (x / 2) := by
  induction n with
  | zero => simp [div_eq_mul_inv, mul_comm]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    have hid := Real.sin_add (((n : ℝ) + 1) * x) (x / 2)
    have hid' := Real.sin_sub (((n : ℝ) + 1) * x) (x / 2)
    have he1 : ((n : ℝ) + 1 + 1 / 2) * x = ((n : ℝ) + 1) * x + x / 2 := by ring
    have he2 : ((n : ℝ) + 1 / 2) * x = ((n : ℝ) + 1) * x - x / 2 := by ring
    rw [he1, he2]
    nlinarith [hid, hid']

private theorem sin_ne_zero_small (t : ℝ) (hl : -Real.pi < t) (hu : t < Real.pi)
    (ht : t ≠ 0) : Real.sin t ≠ 0 := by
  intro hz
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hz
  have hkl : (-1 : ℝ) < (k : ℝ) := by nlinarith [Real.pi_pos]
  have hku : (k : ℝ) < 1 := by nlinarith [Real.pi_pos]
  have hkl' : (-1 : ℤ) < k := by exact_mod_cast hkl
  have hku' : k < (1 : ℤ) := by exact_mod_cast hku
  have hk0 : k = 0 := by omega
  subst k
  simp only [Int.cast_zero, zero_mul] at hk
  exact ht hk.symm

private noncomputable def cosSum (m : ℕ) (n : ℤ) : ℝ :=
  ∑ q ∈ range (2 * m + 1),
    Real.cos (((q : ℝ) + 1) * ((n : ℝ) * Real.pi / (2 * ((m : ℝ) + 1))))

private theorem cosSum_zero (m : ℕ) : cosSum m 0 = (2 * m + 1 : ℕ) := by
  simp [cosSum]

private theorem cosSum_nonzero (m : ℕ) (n : ℤ) (hn : n ≠ 0)
    (hnl : -(4 * (m : ℤ) + 4) < n) (hnu : n < 4 * (m : ℤ) + 4) :
    cosSum m n = -(Real.cos ((n : ℝ) * Real.pi) + 1) / 2 := by
  let x := (n : ℝ) * Real.pi / (2 * ((m : ℝ) + 1))
  have hd : 0 < 2 * ((m : ℝ) + 1) := by positivity
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hx : x ≠ 0 := div_ne_zero (mul_ne_zero hnR Real.pi_ne_zero) hd.ne'
  have hnlR : -(4 * (m : ℝ) + 4) < (n : ℝ) := by exact_mod_cast hnl
  have hnuR : (n : ℝ) < 4 * (m : ℝ) + 4 := by exact_mod_cast hnu
  have hxl : -2 * Real.pi < x := by
    apply (lt_div_iff₀ hd).2
    nlinarith [mul_lt_mul_of_pos_right hnlR Real.pi_pos]
  have hxu : x < 2 * Real.pi := by
    apply (div_lt_iff₀ hd).2
    nlinarith [mul_lt_mul_of_pos_right hnuR Real.pi_pos]
  have hs : Real.sin (x / 2) ≠ 0 := sin_ne_zero_small (x / 2)
    (by linarith) (by linarith) (by exact div_ne_zero hx (by norm_num))
  have he : (((2 * m + 1 : ℕ) : ℝ) + 1 / 2) * x = (n : ℝ) * Real.pi - x / 2 := by
    dsimp [x]
    push_cast
    field_simp
    ring
  have hsum := telescope_cos (2 * m + 1) x
  rw [he, Real.sin_sub, Real.sin_int_mul_pi] at hsum
  change 2 * Real.sin (x / 2) * cosSum m n = _ at hsum
  apply mul_left_cancel₀ hs
  nlinarith [hsum]

private theorem table_orthogonal (m : ℕ) (j k : ℕ)
    (hj : j ∈ modes m) (hk : k ∈ modes m) :
    (∑ q ∈ modes m,
      Real.sin ((j : ℝ) * Real.pi / (2 * ((m : ℝ) + 1)) * (q : ℝ)) *
      Real.sin ((k : ℝ) * Real.pi / (2 * ((m : ℝ) + 1)) * (q : ℝ))) =
      if j = k then (m : ℝ) + 1 else 0 := by
  have hj' := (Finset.mem_Icc.mp hj : 1 ≤ j ∧ j ≤ 2 * m + 1)
  have hk' := (Finset.mem_Icc.mp hk : 1 ≤ k ∧ k ≤ 2 * m + 1)
  have hprod : (∑ q ∈ modes m,
      Real.sin ((j : ℝ) * Real.pi / (2 * ((m : ℝ) + 1)) * (q : ℝ)) *
      Real.sin ((k : ℝ) * Real.pi / (2 * ((m : ℝ) + 1)) * (q : ℝ))) =
      (cosSum m ((j : ℤ) - k) - cosSum m ((j : ℤ) + k)) / 2 := by
    rw [sum_modes]
    unfold cosSum
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q hq
    push_cast
    let A := (j : ℝ) * Real.pi / (2 * ((m : ℝ) + 1)) * ((q : ℝ) + 1)
    let B := (k : ℝ) * Real.pi / (2 * ((m : ℝ) + 1)) * ((q : ℝ) + 1)
    have he1 : ((q : ℝ) + 1) * (((j : ℝ) - k) * Real.pi / (2 * ((m : ℝ) + 1))) = A - B := by dsimp [A, B]; ring
    have he2 : ((q : ℝ) + 1) * (((j : ℝ) + k) * Real.pi / (2 * ((m : ℝ) + 1))) = A + B := by dsimp [A, B]; ring
    rw [he1, he2, Real.cos_sub, Real.cos_add]
    dsimp [A, B]
    ring
  rw [hprod]
  have hsum := cosSum_nonzero m ((j : ℤ) + k) (by omega) (by omega) (by omega)
  by_cases heq : j = k
  · subst k
    rw [ite_eq_left rfl, sub_self, cosSum_zero, hsum]
    have hc : Real.cos (((j : ℤ) + j : ℤ) * Real.pi) = 1 := by
      push_cast
      rw [add_mul, Real.cos_add]
      nlinarith [Real.sin_sq_add_cos_sq ((j : ℝ) * Real.pi), Real.sin_nat_mul_pi j]
    rw [hc]
    push_cast
    ring
  · rw [ite_eq_right heq, cosSum_nonzero m ((j : ℤ) - k) (by omega) (by omega) (by omega), hsum]
    have hc : Real.cos ((((j : ℤ) - k : ℤ) : ℝ) * Real.pi) =
        Real.cos ((((j : ℤ) + k : ℤ) : ℝ) * Real.pi) := by
      push_cast
      rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
      simp
    rw [hc]
    ring

/-- B1: counting-measure orthogonality with squared norm exactly `m + 1`. -/
theorem orthogonal (m : ℕ) (_hm : 1 ≤ m) (j k : ℕ)
    (hj : j ∈ modes m) (hk : k ∈ modes m) :
    ∑ s ∈ states m, vector m j s * vector m k s =
      if j = k then (m : ℝ) + 1 else 0 := by
  rw [sum_states]
  simp_rw [vector_at]
  exact table_orthogonal m j k hj hk

theorem square_norm (m : ℕ) (hm : 1 ≤ m) (j : ℕ) (hj : j ∈ modes m) :
    ∑ s ∈ states m, (vector m j s) ^ 2 = (m : ℝ) + 1 := by
  simpa [sq] using orthogonal m hm j j hj hj

private theorem vector_symmetry (m j : ℕ) (r : ℤ) (hr : r ∈ states m) :
    vector m j r = vector m (stateIndex m r) (stateAt m j) := by
  conv_lhs => rw [← at_index m r hr]
  rw [vector_at, vector_at]
  congr 1
  ring

theorem dual_orthogonal (m : ℕ) (hm : 1 ≤ m) (r s : ℤ)
    (hr : r ∈ states m) (hs : s ∈ states m) :
    (1 / ((m : ℝ) + 1)) * ∑ j ∈ modes m, vector m j r * vector m j s =
      if r = s then 1 else 0 := by
  have he : stateIndex m r = stateIndex m s ↔ r = s := by
    constructor
    · intro h
      have := congrArg (stateAt m) h
      simpa only [at_index m r hr, at_index m s hs] using this
    · exact congrArg (stateIndex m)
  have hh : (m : ℝ) + 1 ≠ 0 := by positivity
  have hsum : (∑ j ∈ modes m, vector m j r * vector m j s) =
      ∑ t ∈ states m, vector m (stateIndex m r) t * vector m (stateIndex m s) t := by
    rw [sum_states]
    apply Finset.sum_congr rfl
    intro j hj
    rw [vector_symmetry m j r hr, vector_symmetry m j s hs]
  rw [hsum, orthogonal m hm _ _ (index_mem m r hr) (index_mem m s hs)]
  simp only [he]
  split_ifs <;> simp [hh]

/-- B2: reconstruction of arbitrary integer data with the explicit Fourier coefficients. -/
theorem reconstruction (m : ℕ) (hm : 1 ≤ m) (F : ℤ → ℝ)
    (r : ℤ) (hr : r ∈ states m) :
    F r = ∑ j ∈ modes m, coefficient m j F * vector m j r := by
  symm
  calc
    (∑ j ∈ modes m, coefficient m j F * vector m j r) =
        ∑ s ∈ states m, F s * ((1 / ((m : ℝ) + 1)) *
          ∑ j ∈ modes m, vector m j s * vector m j r) := by
      unfold coefficient
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ s ∈ states m, F s * (if s = r then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [dual_orthogonal m hm s r hs hr]
    _ = F r := by simp [hr]

private theorem phi_integrable_finite (m j : ℕ) (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable (phi m j) ν := by
  have hc : Continuous (phi m j) := by unfold phi; fun_prop
  apply Integrable.of_bound hc.aestronglyMeasurable 1
  filter_upwards [] with w
  simpa only [Real.norm_eq_abs, phi] using Real.abs_sin_le_one (theta m j * (w + ((m : ℝ) + 1)))

private theorem phi_lower (m j : ℕ) : phi m j (-((m : ℝ) + 1)) = 0 := by
  simp [phi]
private theorem phi_upper (m j : ℕ) : phi m j ((m : ℝ) + 1) = 0 := by
  unfold phi theta RademacherCosine.angle
  convert Real.sin_nat_mul_pi j using 1
  congr 1
  field_simp
  ring

private theorem cut_phi (m j : ℕ) (t : ℤ) (ht : |t| ≤ (m : ℤ) + 1) :
    (if |t| ≤ (m : ℤ) then phi m j (t : ℝ) else 0) = phi m j (t : ℝ) := by
  by_cases hcut : |t| ≤ (m : ℤ)
  · simp [hcut]
  · have he : |t| = (m : ℤ) + 1 := by omega
    have hcases : t = (m : ℤ) + 1 ∨ t = -((m : ℤ) + 1) := by
      by_cases hpos : 0 ≤ t
      · left; simpa only [abs_of_nonneg hpos] using he
      · right
        rw [abs_of_neg (by omega)] at he
        omega
    have hv : phi m j (t : ℝ) = 0 := by
      rcases hcases with he | he
      · have heR : (t : ℝ) = (m : ℝ) + 1 := by exact_mod_cast he
        rw [heR, phi_upper]
      · have heR : (t : ℝ) = -((m : ℝ) + 1) := by exact_mod_cast he
        rw [heR, phi_lower]
    simp [hcut, hv]

/-- B3: genuine Bochner integrability under the actual killed kernel. -/
theorem killedKernel_integrable (m : ℕ) (_hm : 1 ≤ m) (h : ℝ)
    (_hmh : (m : ℝ) ≤ h) (_hhm : h < (m : ℝ) + 1)
    (j : ℕ) (_hj : j ∈ modes m) (r : ℤ) (_hr : r ∈ states m) :
    Integrable (phi m j) (killedKernel RademacherCosine.law h (r : ℝ)) := by
  exact phi_integrable_finite m j _

/-- B3: all modes satisfy the one-step identity for the actual killed kernel. -/
theorem killedKernel_integral (m : ℕ) (_hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1)
    (j : ℕ) (_hj : j ∈ modes m) (r : ℤ) (hr : r ∈ states m) :
    ∫ w : ℝ, phi m j w ∂killedKernel RademacherCosine.law h (r : ℝ) =
      mu m j * vector m j r := by
  have hhalf : RademacherCosine.halfENNReal.toReal = (1 : ℝ) / 2 := by
    norm_num [RademacherCosine.halfENNReal]
  have hint (t : ℤ) : Integrable (phi m j)
      (if |t| ≤ (m : ℤ) then RademacherCosine.halfENNReal • Measure.dirac (t : ℝ) else 0) := by
    split_ifs
    · exact (phi_integrable_finite m j (Measure.dirac (t : ℝ))).smul_measure (by
        norm_num [RademacherCosine.halfENNReal])
    · exact phi_integrable_finite m j _
  have heval (t : ℤ) :
      (∫ w, phi m j w ∂(if |t| ≤ (m : ℤ) then
          RademacherCosine.halfENNReal • Measure.dirac (t : ℝ) else 0)) =
        (1 / 2 : ℝ) * (if |t| ≤ (m : ℤ) then phi m j (t : ℝ) else 0) := by
    split_ifs <;> simp [integral_smul_measure, hhalf]
  have hr' := (Finset.mem_Icc.mp hr : -(m : ℤ) ≤ r ∧ r ≤ (m : ℤ))
  have hp : |r + 1| ≤ (m : ℤ) + 1 := by rw [abs_le]; omega
  have hn : |r - 1| ≤ (m : ℤ) + 1 := by rw [abs_le]; omega
  rw [RademacherCosine.killedKernel_row m h hmh hhm r,
    integral_add_measure (hint (r + 1)) (hint (r - 1)), heval, heval,
    cut_phi m j (r + 1) hp, cut_phi m j (r - 1) hn]
  unfold mu vector phi
  push_cast
  have he1 : theta m j * ((r : ℝ) + 1 + ((m : ℝ) + 1)) =
      theta m j * ((r : ℝ) + ((m : ℝ) + 1)) + theta m j := by ring
  have he2 : theta m j * ((r : ℝ) - 1 + ((m : ℝ) + 1)) =
      theta m j * ((r : ℝ) + ((m : ℝ) + 1)) - theta m j := by ring
  rw [he1, he2, Real.sin_add, Real.sin_sub]
  ring
end Shao.OQ4.RademacherFiniteBasis
