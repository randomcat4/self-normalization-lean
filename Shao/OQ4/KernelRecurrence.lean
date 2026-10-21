import Shao.OQ4.KilledIteration
import Shao.OQ4.AveragedResidual

/-!
# Conditional killed-kernel recurrence and exact normalization

The R3 and R4 block inequalities remain explicit hypotheses. Positivity
of the principal cosine is used only on the closed target interval.
-/

namespace Shao.OQ4

open MeasureTheory ProbabilityTheory

noncomputable def principalCosine (h w : ℝ) : ℝ := Real.cos ((Real.pi / (2 * h)) * w)

noncomputable def principalRate (ν : Measure ℝ) (h : ℝ) : ℝ :=
  cosineCoefficient ν (Real.pi / (2 * h))

variable (ν : Measure ℝ) [IsProbabilityMeasure ν] (h : ℝ)

noncomputable def kernelCosine (n : ℕ) (z : ℝ) : ℝ :=
  killedAction ν h n (principalCosine h) z

noncomputable def normalizedKernelCosine (n : ℕ) (z : ℝ) : ℝ :=
  (principalRate ν h ^ n)⁻¹ * kernelCosine ν h n z

noncomputable def normalizedKernelMass (n : ℕ) (z : ℝ) : ℝ :=
  (principalRate ν h ^ n)⁻¹ * killedMass ν h n z

theorem principalCosine_measurable : Measurable (principalCosine h) := by
  unfold principalCosine
  fun_prop

theorem principalCosine_abs_le_one (w : ℝ) : |principalCosine h w| ≤ 1 :=
  Real.abs_cos_le_one _

theorem principalCosine_nonneg (hh : 0 < h) (w : ℝ) (hw : |w| ≤ h) :
    0 ≤ principalCosine h w := by
  have ha : 0 ≤ Real.pi / (2 * h) := le_of_lt (div_pos Real.pi_pos (by positivity))
  have heq : (Real.pi / (2 * h)) * h = Real.pi / 2 := by
    field_simp [ne_of_gt hh]
  have hab : |(Real.pi / (2 * h)) * w| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left hw ha).trans_eq heq
  exact Real.cos_nonneg_of_mem_Icc (abs_le.mp hab)

theorem kernelCosine_measurable (n : ℕ) : Measurable (kernelCosine ν h n) :=
  killedAction_measurable ν h n _ (principalCosine_measurable h)

theorem kernelCosine_bounds (hh : 0 < h) (n : ℕ) (z : ℝ) (hz : |z| ≤ h) :
    0 ≤ kernelCosine ν h n z ∧
      kernelCosine ν h n z ≤ killedMass ν h n z ∧ killedMass ν h n z ≤ 1 := by
  have hnonneg : 0 ≤ kernelCosine ν h n z := by
    apply integral_nonneg_of_ae
    exact (killedIterKernel_ae_support ν h n z hz).mono
      fun w hw => principalCosine_nonneg h hh w hw
  have hbound := killedAction_bound_mass ν h n z _ (principalCosine_measurable h)
    1 (principalCosine_abs_le_one h)
  exact ⟨hnonneg, (le_abs_self _).trans (by simpa [kernelCosine] using hbound),
    killedMass_le_one ν h n z⟩

theorem principalKcos_eq_action (w : ℝ) :
    Kcos ν (Real.pi / (2 * h)) h w = killedAction ν h 1 (principalCosine h) w := by
  simpa [killedAction, killedIterKernel, principalCosine] using
    (killedKernel_integral_cos ν (Real.pi / (2 * h)) h w).symm

theorem principalResidual_measurable :
    Measurable (cosineResidual ν (Real.pi / (2 * h)) h) := by
  exact (measurable_Kcos ν _ h).sub (measurable_const.mul (by fun_prop))

theorem principalResidual_bound (w : ℝ) :
    |cosineResidual ν (Real.pi / (2 * h)) h w| ≤ 1 + |principalRate ν h| := by
  have hK := killedAction_bound ν h 1 w _ (principalCosine_measurable h)
    1 (principalCosine_abs_le_one h)
  rw [← principalKcos_eq_action] at hK
  change |Kcos ν (Real.pi / (2 * h)) h w - principalRate ν h * principalCosine h w| ≤ _
  calc
    |Kcos ν (Real.pi / (2 * h)) h w - principalRate ν h * principalCosine h w| ≤
        |Kcos ν (Real.pi / (2 * h)) h w| + |-(principalRate ν h * principalCosine h w)| :=
      abs_add_le _ _
    _ = |Kcos ν (Real.pi / (2 * h)) h w| + |principalRate ν h| * |principalCosine h w| := by
      rw [abs_neg, abs_mul]
    _ ≤ 1 + |principalRate ν h| * 1 :=
      add_le_add hK (mul_le_mul_of_nonneg_left (principalCosine_abs_le_one h w) (abs_nonneg _))
    _ = 1 + |principalRate ν h| := by ring

theorem principalResidual_integrable (n : ℕ) (z : ℝ) :
    Integrable (cosineResidual ν (Real.pi / (2 * h)) h) (killedIterKernel ν h n z) ∧
      Integrable (fun w => |cosineResidual ν (Real.pi / (2 * h)) h w|)
        (killedIterKernel ν h n z) := by
  have hi := killedAction_integrable ν h n z _ (principalResidual_measurable ν h)
    ⟨1 + |principalRate ν h|, principalResidual_bound ν h⟩
  exact ⟨hi, hi.abs⟩

/-- The genuine one-step defect, without moment or centering assumptions. -/
theorem kernelCosine_defect (k : ℕ) (z : ℝ) :
    kernelCosine ν h (k + 1) z - principalRate ν h * kernelCosine ν h k z =
      killedAction ν h k (cosineResidual ν (Real.pi / (2 * h)) h) z := by
  have hφ := killedAction_integrable ν h k z _ (principalCosine_measurable h)
    ⟨1, principalCosine_abs_le_one h⟩
  have hK := killedAction_iterated_integrable ν h k 1 z _ (principalCosine_measurable h)
    ⟨1, principalCosine_abs_le_one h⟩
  have hpoint : killedAction ν h 1 (principalCosine h) = Kcos ν (Real.pi / (2 * h)) h := by
    funext w
    exact (principalKcos_eq_action ν h w).symm
  rw [hpoint] at hK
  have hsemi := killedAction_semigroup ν h k 1 z _ (principalCosine_measurable h)
    ⟨1, principalCosine_abs_le_one h⟩
  rw [hpoint] at hsemi
  change killedAction ν h (k + 1) (principalCosine h) z -
      principalRate ν h * killedAction ν h k (principalCosine h) z =
    ∫ w, Kcos ν (Real.pi / (2 * h)) h w - principalRate ν h * principalCosine h w
      ∂killedIterKernel ν h k z
  rw [integral_sub hK (hφ.const_mul _), integral_const_mul, hsemi]
  rfl

/-- Conditional D0; the block hypothesis is the independent R3 input. -/
theorem kernelCosine_delayed_defect (_hh : 0 < h) (m k : ℕ) (hmk : m ≤ k)
    (z : ℝ) (hz : |z| ≤ h) (ε : ℝ) (hε : 0 ≤ ε)
    (hblock : ∀ w, |w| ≤ h →
      killedAction ν h m (fun v => |cosineResidual ν (Real.pi / (2 * h)) h v|) w ≤ ε) :
    |kernelCosine ν h (k + 1) z - principalRate ν h * kernelCosine ν h k z| ≤
      ε * killedMass ν h (k - m) z := by
  have hr : Measurable (fun w => |cosineResidual ν (Real.pi / (2 * h)) h w|) :=
    (by fun_prop : Measurable (fun x : ℝ => |x|)).comp (principalResidual_measurable ν h)
  have hbr : ∃ M : ℝ, ∀ w, |(|cosineResidual ν (Real.pi / (2 * h)) h w|)| ≤ M :=
    ⟨1 + |principalRate ν h|, fun w => by simpa only [abs_abs] using principalResidual_bound ν h w⟩
  have hsemi := killedAction_semigroup ν h (k - m) m z _ hr hbr
  rw [Nat.sub_add_cancel hmk] at hsemi
  rw [kernelCosine_defect]
  calc
    |killedAction ν h k (cosineResidual ν (Real.pi / (2 * h)) h) z| ≤
        killedAction ν h k (fun w => |cosineResidual ν (Real.pi / (2 * h)) h w|) z :=
      (killedAction_abs ν h k z _ (principalResidual_measurable ν h)
        ⟨1 + |principalRate ν h|, principalResidual_bound ν h⟩).2
    _ = killedAction ν h (k - m)
        (killedAction ν h m (fun w => |cosineResidual ν (Real.pi / (2 * h)) h w|)) z := hsemi
    _ ≤ killedAction ν h (k - m) (fun _ => ε) z :=
      killedAction_mono_closed ν h (k - m) z hz _ _
        (killedAction_measurable ν h m _ hr) measurable_const
        (killedAction_bounded ν h m _ hr hbr)
        ⟨ε, fun _ => by simp [abs_of_nonneg hε]⟩ hblock
    _ = ε * killedMass ν h (k - m) z := by
      simp [killedAction, killedMass_eq_real, mul_comm]

/-- Conditional D1; comparison is used only on the closed target interval. -/
theorem kernelMass_block (_hh : 0 < h) (m k : ℕ) (z : ℝ) (hz : |z| ≤ h)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hblock : ∀ w, |w| ≤ h → killedMass ν h m w ≤ A * principalCosine h w + B) :
    killedMass ν h (k + m) z ≤ A * kernelCosine ν h k z + B * killedMass ν h k z := by
  have hφ := killedAction_integrable ν h k z _ (principalCosine_measurable h)
    ⟨1, principalCosine_abs_le_one h⟩
  have hright : ∃ M : ℝ, ∀ w, |A * principalCosine h w + B| ≤ M := by
    refine ⟨A + B, fun w => ?_⟩
    calc
      |A * principalCosine h w + B| ≤ |A * principalCosine h w| + |B| := abs_add_le _ _
      _ = A * |principalCosine h w| + B := by
        rw [abs_mul, abs_of_nonneg hA, abs_of_nonneg hB]
      _ ≤ A * 1 + B := add_le_add (mul_le_mul_of_nonneg_left (principalCosine_abs_le_one h w) hA) le_rfl
      _ = A + B := by ring
  change killedAction ν h (k + m) (fun _ => 1) z ≤ _
  rw [killedAction_semigroup ν h k m z _ measurable_const ⟨1, by simp⟩]
  calc
    killedAction ν h k (killedAction ν h m (fun _ => 1)) z ≤
        killedAction ν h k (fun w => A * principalCosine h w + B) z :=
      killedAction_mono_closed ν h k z hz _ _
        (killedAction_measurable ν h m _ measurable_const)
        ((measurable_const.mul (principalCosine_measurable h)).add measurable_const)
        (killedAction_bounded ν h m _ measurable_const ⟨1, by simp⟩) hright hblock
    _ = A * kernelCosine ν h k z + B * killedMass ν h k z := by
      unfold killedAction kernelCosine
      rw [integral_add (hφ.const_mul A) (integrable_const B), integral_const_mul]
      simp [killedMass_eq_real, killedAction, mul_comm]

theorem normalizedKernelCosine_step (hρ : 0 < principalRate ν h) (k : ℕ) (z : ℝ) :
    normalizedKernelCosine ν h (k + 1) z - normalizedKernelCosine ν h k z =
      (principalRate ν h ^ (k + 1))⁻¹ *
        (kernelCosine ν h (k + 1) z - principalRate ν h * kernelCosine ν h k z) := by
  unfold normalizedKernelCosine
  rw [pow_succ]
  field_simp [ne_of_gt hρ]

/-- D2 retains exactly the factor ε times the reciprocal of ρ^(m+1). -/
theorem normalizedKernelCosine_delayed (hh : 0 < h) (hρ : 0 < principalRate ν h)
    (m k : ℕ) (hmk : m ≤ k) (z : ℝ) (hz : |z| ≤ h) (ε : ℝ) (hε : 0 ≤ ε)
    (hblock : ∀ w, |w| ≤ h →
      killedAction ν h m (fun v => |cosineResidual ν (Real.pi / (2 * h)) h v|) w ≤ ε) :
    |normalizedKernelCosine ν h (k + 1) z - normalizedKernelCosine ν h k z| ≤
      (ε * (principalRate ν h ^ (m + 1))⁻¹) * normalizedKernelMass ν h (k - m) z := by
  rw [normalizedKernelCosine_step ν h hρ, abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hρ _))]
  calc
    (principalRate ν h ^ (k + 1))⁻¹ *
        |kernelCosine ν h (k + 1) z - principalRate ν h * kernelCosine ν h k z| ≤
        (principalRate ν h ^ (k + 1))⁻¹ * (ε * killedMass ν h (k - m) z) :=
      mul_le_mul_of_nonneg_left
        (kernelCosine_delayed_defect ν h hh m k hmk z hz ε hε hblock)
        (le_of_lt (inv_pos.mpr (pow_pos hρ _)))
    _ = (ε * (principalRate ν h ^ (m + 1))⁻¹) * normalizedKernelMass ν h (k - m) z := by
      have hexp : k + 1 = (m + 1) + (k - m) := by omega
      unfold normalizedKernelMass
      rw [hexp, pow_add, mul_inv_rev]
      ring

/-- D3 retains exactly the separate factors A/ρ^m and B/ρ^m. -/
theorem normalizedKernelMass_block (hh : 0 < h) (hρ : 0 < principalRate ν h)
    (m k : ℕ) (z : ℝ) (hz : |z| ≤ h) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hblock : ∀ w, |w| ≤ h → killedMass ν h m w ≤ A * principalCosine h w + B) :
    normalizedKernelMass ν h (k + m) z ≤
      (A * (principalRate ν h ^ m)⁻¹) * normalizedKernelCosine ν h k z +
        (B * (principalRate ν h ^ m)⁻¹) * normalizedKernelMass ν h k z := by
  calc
    normalizedKernelMass ν h (k + m) z ≤ (principalRate ν h ^ (k + m))⁻¹ *
        (A * kernelCosine ν h k z + B * killedMass ν h k z) :=
      mul_le_mul_of_nonneg_left (kernelMass_block ν h hh m k z hz A B hA hB hblock)
        (le_of_lt (inv_pos.mpr (pow_pos hρ _)))
    _ = (A * (principalRate ν h ^ m)⁻¹) * normalizedKernelCosine ν h k z +
        (B * (principalRate ν h ^ m)⁻¹) * normalizedKernelMass ν h k z := by
      unfold normalizedKernelCosine normalizedKernelMass
      rw [pow_add, mul_inv_rev]
      ring

theorem normalizedKernelMass_nonneg (hρ : 0 < principalRate ν h) (n : ℕ) (z : ℝ) :
    0 ≤ normalizedKernelMass ν h n z :=
  mul_nonneg (le_of_lt (inv_pos.mpr (pow_pos hρ n))) (killedMass_nonneg ν h n z)

theorem normalizedKernelCosine_nonneg (hh : 0 < h) (hρ : 0 < principalRate ν h)
    (n : ℕ) (z : ℝ) (hz : |z| ≤ h) : 0 ≤ normalizedKernelCosine ν h n z :=
  mul_nonneg (le_of_lt (inv_pos.mpr (pow_pos hρ n))) (kernelCosine_bounds ν h hh n z hz).1

/-- D4 is only the stated finite-range bound, without uniform control in h. -/
theorem normalizedKernelMass_finite_bound (hρ : 0 < principalRate ν h)
    (hρ1 : principalRate ν h ≤ 1) (m n : ℕ) (hn : n ≤ 2 * m) (z : ℝ) :
    normalizedKernelMass ν h n z ≤ (principalRate ν h ^ (2 * m))⁻¹ := by
  calc
    normalizedKernelMass ν h n z ≤ (principalRate ν h ^ n)⁻¹ := by
      simpa [normalizedKernelMass] using mul_le_mul_of_nonneg_left (killedMass_le_one ν h n z)
        (le_of_lt (inv_pos.mpr (pow_pos hρ n)))
    _ ≤ (principalRate ν h ^ (2 * m))⁻¹ :=
      (inv_le_inv₀ (pow_pos hρ n) (pow_pos hρ (2 * m))).2
        (pow_le_pow_of_le_one (le_of_lt hρ) hρ1 hn)

end Shao.OQ4
