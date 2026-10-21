import Shao.OQ4.KilledKernel
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Finite powers of the genuine killed kernel

These are actual Mathlib kernel powers. Time zero is the identity kernel,
including for starting points outside the closed target interval.
-/

namespace Shao.OQ4

open MeasureTheory ProbabilityTheory

variable (ν : Measure ℝ) [IsProbabilityMeasure ν] (h : ℝ)

/-- The actual monoid power, with no additional killing at time zero. -/
noncomputable def killedIterKernel (n : ℕ) : Kernel ℝ ℝ := (killedKernel ν h) ^ n

/-- The real integral action of the finite kernel power. -/
noncomputable def killedAction (n : ℕ) (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ w, f w ∂killedIterKernel ν h n z

/-- The real row mass of the finite kernel power. -/
noncomputable def killedMass (n : ℕ) (z : ℝ) : ℝ :=
  killedAction ν h n (fun _ => 1) z

theorem killedIterKernel_zero (z : ℝ) : killedIterKernel ν h 0 z = Measure.dirac z := by
  rfl

theorem killedIterKernel_mass_le_one (n : ℕ) (z : ℝ) :
    killedIterKernel ν h n z Set.univ ≤ 1 := by
  induction n with
  | zero => simp [killedIterKernel_zero]
  | succ n ih =>
    change ((killedKernel ν h) ^ (n + 1)) z Set.univ ≤ 1
    rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ MeasurableSet.univ]
    calc
      ∫⁻ w, killedKernel ν h w Set.univ ∂((killedKernel ν h) ^ n) z ≤
          ∫⁻ _w, (1 : ENNReal) ∂((killedKernel ν h) ^ n) z :=
        lintegral_mono fun w => killedKernel_mass_le_one ν h w
      _ = killedIterKernel ν h n z Set.univ := by simp [killedIterKernel]
      _ ≤ 1 := ih

instance killedIterKernel_isFiniteKernel (n : ℕ) : IsFiniteKernel (killedIterKernel ν h n) :=
  ⟨⟨1, by simp, fun z => killedIterKernel_mass_le_one ν h n z⟩⟩

theorem killedIterKernel_real_mass_le_one (n : ℕ) (z : ℝ) :
    (killedIterKernel ν h n z).real Set.univ ≤ 1 := by
  simpa only [measureReal_def, ENNReal.toReal_one] using
    ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤)
      (killedIterKernel_mass_le_one ν h n z)

/-- Positive-time rows have closed support for every real starting point. -/
theorem killedIterKernel_ae_support_pos (n : ℕ) (hn : 0 < n) (z : ℝ) :
    ∀ᵐ w ∂killedIterKernel ν h n z, |w| ≤ h := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  unfold killedIterKernel
  change ∀ᵐ w ∂((killedKernel ν h) ^ (k + 1)) z, |w| ≤ h
  rw [show k + 1 = 1 + k by omega, Kernel.pow_add, pow_one]
  apply Kernel.ae_comp_of_ae_ae (measurableSet_le (by fun_prop) measurable_const)
  exact Filter.Eventually.of_forall fun w => killedKernel_ae_support ν h w

/-- A start in the closed interval gives closed support also at time zero. -/
theorem killedIterKernel_ae_support (n : ℕ) (z : ℝ) (hz : |z| ≤ h) :
    ∀ᵐ w ∂killedIterKernel ν h n z, |w| ≤ h := by
  cases n with
  | zero => simpa [killedIterKernel_zero] using hz
  | succ n => exact killedIterKernel_ae_support_pos ν h (n + 1) (by omega) z

theorem killedAction_integrable (n : ℕ) (z : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hbound : ∃ M : ℝ, ∀ w, |f w| ≤ M) : Integrable f (killedIterKernel ν h n z) := by
  obtain ⟨M, hM⟩ := hbound
  apply Integrable.of_bound hf.aestronglyMeasurable M
  exact Filter.Eventually.of_forall fun w => by simpa only [Real.norm_eq_abs] using hM w

theorem killedAction_measurable (n : ℕ) (f : ℝ → ℝ) (hf : Measurable f) :
    Measurable (killedAction ν h n f) :=
  hf.stronglyMeasurable.integral_kernel.measurable

theorem killedMass_eq_real (n : ℕ) (z : ℝ) :
    killedMass ν h n z = (killedIterKernel ν h n z).real Set.univ := by
  simp [killedMass, killedAction]

theorem killedMass_nonneg (n : ℕ) (z : ℝ) : 0 ≤ killedMass ν h n z := by
  rw [killedMass_eq_real]
  exact measureReal_nonneg

theorem killedMass_le_one (n : ℕ) (z : ℝ) : killedMass ν h n z ≤ 1 := by
  rw [killedMass_eq_real]
  exact killedIterKernel_real_mass_le_one ν h n z

/-- The mass-weighted bound retains the loss of probability from killing. -/
theorem killedAction_bound_mass (n : ℕ) (z : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : ∀ w, |f w| ≤ M) :
    |killedAction ν h n f z| ≤ M * killedMass ν h n z := by
  have hfi := killedAction_integrable ν h n z f hf ⟨M, hM⟩
  calc
    |killedAction ν h n f z| ≤ ∫ w, |f w| ∂killedIterKernel ν h n z := by
      simpa only [killedAction, Real.norm_eq_abs] using norm_integral_le_integral_norm f
    _ ≤ ∫ _w, M ∂killedIterKernel ν h n z :=
      integral_mono_ae hfi.abs (integrable_const M) (Filter.Eventually.of_forall hM)
    _ = M * killedMass ν h n z := by simp [killedMass_eq_real, mul_comm]

theorem killedAction_bound (n : ℕ) (z : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : ∀ w, |f w| ≤ M) : |killedAction ν h n f z| ≤ M := by
  have hM0 : 0 ≤ M := (abs_nonneg (f 0)).trans (hM 0)
  exact (killedAction_bound_mass ν h n z f hf M hM).trans
    (by simpa using mul_le_mul_of_nonneg_left (killedMass_le_one ν h n z) hM0)

theorem killedAction_bounded (n : ℕ) (f : ℝ → ℝ) (hf : Measurable f)
    (hbound : ∃ M : ℝ, ∀ w, |f w| ≤ M) :
    ∃ M : ℝ, ∀ z, |killedAction ν h n f z| ≤ M := by
  obtain ⟨M, hM⟩ := hbound
  exact ⟨M, fun z => killedAction_bound ν h n z f hf M hM⟩

theorem killedAction_zero (f : ℝ → ℝ) (z : ℝ) : killedAction ν h 0 f z = f z := by
  simp [killedAction, killedIterKernel_zero]

theorem killedAction_one (z : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hbound : ∃ M : ℝ, ∀ w, |f w| ≤ M) :
    Integrable (fun y : ℝ => if |z + y| ≤ h then f (z + y) else 0) ν ∧
      killedAction ν h 1 f z = ∫ y : ℝ, if |z + y| ≤ h then f (z + y) else 0 ∂ν := by
  simpa [killedAction, killedIterKernel] using
    (killedKernel_integral_bounded ν h z f hf hbound).2

/-- The inner action is a bounded Borel test, so the outer integral is genuine. -/
theorem killedAction_iterated_integrable (m n : ℕ) (z : ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) (hbound : ∃ M : ℝ, ∀ w, |f w| ≤ M) :
    Integrable (killedAction ν h n f) (killedIterKernel ν h m z) :=
  killedAction_integrable ν h m z _ (killedAction_measurable ν h n f hf)
    (killedAction_bounded ν h n f hf hbound)

theorem killedAction_semigroup (m n : ℕ) (z : ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) (hbound : ∃ M : ℝ, ∀ w, |f w| ≤ M) :
    killedAction ν h (m + n) f z = killedAction ν h m (killedAction ν h n f) z := by
  have heq : killedIterKernel ν h (m + n) =
      (killedIterKernel ν h n) ∘ₖ (killedIterKernel ν h m) := by
    unfold killedIterKernel
    rw [Nat.add_comm, Kernel.pow_add]
  have hi := killedAction_integrable ν h (m + n) z f hf hbound
  rw [heq] at hi
  unfold killedAction
  rw [heq]
  exact Kernel.integral_comp hi

theorem killedAction_add (n : ℕ) (z : ℝ) (f g : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hfb : ∃ M : ℝ, ∀ w, |f w| ≤ M) (hgb : ∃ M : ℝ, ∀ w, |g w| ≤ M) :
    killedAction ν h n (fun w => f w + g w) z =
      killedAction ν h n f z + killedAction ν h n g z :=
  integral_add (killedAction_integrable ν h n z f hf hfb)
    (killedAction_integrable ν h n z g hg hgb)

theorem killedAction_smul (n : ℕ) (z c : ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) (hfb : ∃ M : ℝ, ∀ w, |f w| ≤ M) :
    Integrable (fun w => c * f w) (killedIterKernel ν h n z) ∧
      killedAction ν h n (fun w => c * f w) z = c * killedAction ν h n f z := by
  refine ⟨(killedAction_integrable ν h n z f hf hfb).const_mul c, ?_⟩
  exact integral_const_mul c f

theorem killedAction_abs (n : ℕ) (z : ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) (hfb : ∃ M : ℝ, ∀ w, |f w| ≤ M) :
    Integrable (fun w => |f w|) (killedIterKernel ν h n z) ∧
      |killedAction ν h n f z| ≤ killedAction ν h n (fun w => |f w|) z := by
  refine ⟨(killedAction_integrable ν h n z f hf hfb).abs, ?_⟩
  simpa only [killedAction, Real.norm_eq_abs] using norm_integral_le_integral_norm f

theorem killedAction_mono (n : ℕ) (z : ℝ) (f g : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hfb : ∃ M : ℝ, ∀ w, |f w| ≤ M) (hgb : ∃ M : ℝ, ∀ w, |g w| ≤ M)
    (hfg : ∀ w, f w ≤ g w) : killedAction ν h n f z ≤ killedAction ν h n g z :=
  integral_mono_ae (killedAction_integrable ν h n z f hf hfb)
    (killedAction_integrable ν h n z g hg hgb) (Filter.Eventually.of_forall hfg)

theorem killedAction_mono_closed (n : ℕ) (z : ℝ) (hz : |z| ≤ h) (f g : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hfb : ∃ M : ℝ, ∀ w, |f w| ≤ M) (hgb : ∃ M : ℝ, ∀ w, |g w| ≤ M)
    (hfg : ∀ w, |w| ≤ h → f w ≤ g w) :
    killedAction ν h n f z ≤ killedAction ν h n g z := by
  apply integral_mono_ae (killedAction_integrable ν h n z f hf hfb)
    (killedAction_integrable ν h n z g hg hgb)
  exact (killedIterKernel_ae_support ν h n z hz).mono fun w hw => hfg w hw

end Shao.OQ4
