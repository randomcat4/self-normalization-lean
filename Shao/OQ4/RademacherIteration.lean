import Shao.OQ4.RademacherCosine
import Shao.OQ4.KilledIteration
import Mathlib.Data.Int.Interval

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Shao.OQ4.RademacherIteration

/-- The actual integer states retained by the closed threshold. -/
def grid (m : ℕ) : Set ℝ :=
  {w | ∃ s : ℤ, -(m : ℤ) ≤ s ∧ s ≤ (m : ℤ) ∧ w = (s : ℝ)}

theorem grid_finite (m : ℕ) : (grid m).Finite := by
  have hfinite : (Set.Icc (-(m : ℤ)) (m : ℤ)).Finite := Set.finite_Icc _ _
  have heq : grid m = (fun s : ℤ => (s : ℝ)) '' Set.Icc (-(m : ℤ)) (m : ℤ) := by
    ext w
    constructor
    · rintro ⟨s, hlo, hhi, rfl⟩
      exact ⟨s, ⟨hlo, hhi⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs.1, hs.2, rfl⟩
  rw [heq]
  exact hfinite.image _

theorem measurableSet_grid (m : ℕ) : MeasurableSet (grid m) :=
  (grid_finite m).measurableSet

private theorem killedKernel_grid_compl (m : ℕ) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (s : ℤ) :
    killedKernel RademacherCosine.law h (s : ℝ) (grid m)ᶜ = 0 := by
  have hplus (hp : |s + 1| ≤ (m : ℤ)) : (((s + 1 : ℤ) : ℝ)) ∈ grid m :=
    ⟨s + 1, (abs_le.mp hp).1, (abs_le.mp hp).2, rfl⟩
  have hminus (hn : |s - 1| ≤ (m : ℤ)) : (((s - 1 : ℤ) : ℝ)) ∈ grid m :=
    ⟨s - 1, (abs_le.mp hn).1, (abs_le.mp hn).2, rfl⟩
  have hplus' (hp : |s + 1| ≤ (m : ℤ)) : (s : ℝ) + 1 ∈ grid m := by
    simpa only [Int.cast_add, Int.cast_one] using hplus hp
  have hminus' (hn : |s - 1| ≤ (m : ℤ)) : (s : ℝ) - 1 ∈ grid m := by
    simpa only [Int.cast_sub, Int.cast_one] using hminus hn
  rw [RademacherCosine.killedKernel_row m h hmh hhm s, Measure.add_apply]
  have hplus_zero :
      (if |s + 1| ≤ (m : ℤ) then
        RademacherCosine.halfENNReal • Measure.dirac (((s + 1 : ℤ) : ℝ)) else 0)
          (grid m)ᶜ = 0 := by
    split_ifs with hp
    · simp [Measure.smul_apply, hplus' hp]
    · simp
  have hminus_zero :
      (if |s - 1| ≤ (m : ℤ) then
        RademacherCosine.halfENNReal • Measure.dirac (((s - 1 : ℤ) : ℝ)) else 0)
          (grid m)ᶜ = 0 := by
    split_ifs with hn
    · simp [Measure.smul_apply, hminus' hn]
    · simp
  rw [hplus_zero, hminus_zero, add_zero]

/-- Complement-mass form of preservation of the finite integer states. -/
theorem killedIterKernel_grid_compl (m : ℕ) (_hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (r : ℤ)
    (hrlo : -(m : ℤ) ≤ r) (hrhi : r ≤ (m : ℤ)) (n : ℕ) :
    killedIterKernel RademacherCosine.law h n (r : ℝ) (grid m)ᶜ = 0 := by
  induction n with
  | zero =>
      rw [killedIterKernel_zero]
      have hr : (r : ℝ) ∈ grid m := ⟨r, hrlo, hrhi, rfl⟩
      simp [hr]
  | succ n ih =>
      have hcomp : killedIterKernel RademacherCosine.law h (n + 1) =
          killedKernel RademacherCosine.law h ∘ₖ
            killedIterKernel RademacherCosine.law h n := by
        simp only [killedIterKernel, pow_succ']
        rfl
      rw [hcomp, Kernel.comp_apply' _ _ _ (measurableSet_grid m).compl]
      have hae : ∀ᵐ w ∂killedIterKernel RademacherCosine.law h n (r : ℝ),
          w ∈ grid m := by
        exact ae_iff.mpr ih
      calc
        (∫⁻ w, killedKernel RademacherCosine.law h w (grid m)ᶜ
            ∂killedIterKernel RademacherCosine.law h n (r : ℝ)) =
            ∫⁻ _w, (0 : ENNReal)
              ∂killedIterKernel RademacherCosine.law h n (r : ℝ) := by
          apply lintegral_congr_ae
          filter_upwards [hae] with w hw
          obtain ⟨s, _hslo, _hshi, rfl⟩ := hw
          exact killedKernel_grid_compl m h hmh hhm s
        _ = 0 := by simp

/-- The zero-step Dirac and every positive iterate are supported on `grid m`. -/
theorem killedIterKernel_ae_grid (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (r : ℤ)
    (hrlo : -(m : ℤ) ≤ r) (hrhi : r ≤ (m : ℤ)) (n : ℕ) :
    ∀ᵐ w ∂killedIterKernel RademacherCosine.law h n (r : ℝ), w ∈ grid m :=
  ae_iff.mpr (killedIterKernel_grid_compl m hm h hmh hhm r hrlo hrhi n)

/-- Boundedness supplies genuine integrability for the actual finite kernel. -/
theorem principal_integrable (m : ℕ) (h : ℝ) (n : ℕ) (z : ℝ) :
    Integrable (fun w : ℝ => Real.cos (RademacherCosine.angle m * w))
      (killedIterKernel RademacherCosine.law h n z) := by
  apply killedAction_integrable RademacherCosine.law h n z
  · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).measurable
  · exact ⟨1, fun w => Real.abs_cos_le_one _⟩

/-- Exact finite powers of the principal cosine, with every natural time included. -/
theorem killedAction_principal_power (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (r : ℤ)
    (hrlo : -(m : ℤ) ≤ r) (hrhi : r ≤ (m : ℤ)) (n : ℕ) :
    killedAction RademacherCosine.law h n
        (fun w : ℝ => Real.cos (RademacherCosine.angle m * w)) (r : ℝ) =
      RademacherCosine.rho m ^ n * Real.cos (RademacherCosine.angle m * (r : ℝ)) := by
  let f : ℝ → ℝ := fun w => Real.cos (RademacherCosine.angle m * w)
  have hf : Measurable f :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).measurable
  have hfb : ∃ M : ℝ, ∀ w, |f w| ≤ M := ⟨1, fun w => Real.abs_cos_le_one _⟩
  change killedAction RademacherCosine.law h n f (r : ℝ) =
    RademacherCosine.rho m ^ n * f (r : ℝ)
  induction n with
  | zero =>
      rw [killedAction_zero, pow_zero, one_mul]
  | succ n ih =>
      have hstep : ∀ᵐ w ∂killedIterKernel RademacherCosine.law h n (r : ℝ),
          killedAction RademacherCosine.law h 1 f w = RademacherCosine.rho m * f w := by
        filter_upwards [killedIterKernel_ae_grid m hm h hmh hhm r hrlo hrhi n] with w hw
        obtain ⟨s, hslo, hshi, rfl⟩ := hw
        change (∫ v : ℝ, Real.cos (RademacherCosine.angle m * v)
            ∂killedIterKernel RademacherCosine.law h 1 (s : ℝ)) =
          RademacherCosine.rho m * Real.cos (RademacherCosine.angle m * (s : ℝ))
        rw [show killedIterKernel RademacherCosine.law h 1 =
          killedKernel RademacherCosine.law h from pow_one _]
        exact RademacherCosine.killedKernel_integral_principal m hm h hmh hhm s hslo hshi
      have hinner : Integrable (killedAction RademacherCosine.law h 1 f)
          (killedIterKernel RademacherCosine.law h n (r : ℝ)) :=
        killedAction_iterated_integrable RademacherCosine.law h n 1 (r : ℝ) f hf hfb
      have hscaled : Integrable (fun w => RademacherCosine.rho m * f w)
          (killedIterKernel RademacherCosine.law h n (r : ℝ)) :=
        (principal_integrable m h n (r : ℝ)).const_mul _
      rw [killedAction_semigroup RademacherCosine.law h n 1 (r : ℝ) f hf hfb]
      change (∫ w, killedAction RademacherCosine.law h 1 f w
          ∂killedIterKernel RademacherCosine.law h n (r : ℝ)) = _
      calc
        (∫ w, killedAction RademacherCosine.law h 1 f w
            ∂killedIterKernel RademacherCosine.law h n (r : ℝ)) =
            ∫ w, RademacherCosine.rho m * f w
              ∂killedIterKernel RademacherCosine.law h n (r : ℝ) := integral_congr_ae hstep
        _ = RademacherCosine.rho m * killedAction RademacherCosine.law h n f (r : ℝ) := by
          rw [integral_const_mul]
          rfl
        _ = RademacherCosine.rho m ^ (n + 1) * f (r : ℝ) := by
          rw [ih, pow_succ]
          ring

/-- The principal power identity is an identity of actual kernel integrals. -/
theorem killedIterKernel_integral_principal_power (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (r : ℤ)
    (hrlo : -(m : ℤ) ≤ r) (hrhi : r ≤ (m : ℤ)) (n : ℕ) :
    (∫ w : ℝ, Real.cos (RademacherCosine.angle m * w)
        ∂killedIterKernel RademacherCosine.law h n (r : ℝ)) =
      RademacherCosine.rho m ^ n * Real.cos (RademacherCosine.angle m * (r : ℝ)) :=
  killedAction_principal_power m hm h hmh hhm r hrlo hrhi n

end Shao.OQ4.RademacherIteration
