import Shao.OQ4.RademacherFiniteBasis
import Shao.OQ4.RademacherIteration
import Shao.OQ4.KilledPathLaw

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false

namespace Shao.OQ4.RademacherAllModes

open RademacherFiniteBasis

/-- The coefficient of the constant-one datum, with the original counting normalization. -/
noncomputable def survivalCoefficient (m j : ℕ) : ℝ :=
  coefficient m j (fun _ => 1)

theorem survivalCoefficient_eq (m j : ℕ) :
    survivalCoefficient m j = (1 / ((m : ℝ) + 1)) *
      ∑ s ∈ states m, vector m j s := by
  simp only [survivalCoefficient, coefficient, one_mul]

private theorem phi_measurable (m j : ℕ) : Measurable (phi m j) := by
  unfold phi
  fun_prop

private theorem phi_bound (m j : ℕ) : ∀ w : ℝ, |phi m j w| ≤ 1 := by
  intro w
  exact Real.abs_sin_le_one _

/-- Genuine integrability for every frozen mode and every natural time, including zero. -/
theorem killedIterKernel_integrable (m : ℕ) (_hm : 1 ≤ m) (h : ℝ)
    (_hmh : (m : ℝ) ≤ h) (_hhm : h < (m : ℝ) + 1)
    (j : ℕ) (_hj : j ∈ modes m) (r : ℤ) (_hr : r ∈ states m) (n : ℕ) :
    Integrable (phi m j) (killedIterKernel RademacherCosine.law h n (r : ℝ)) := by
  exact killedAction_integrable RademacherCosine.law h n (r : ℝ) (phi m j)
    (phi_measurable m j) ⟨1, phi_bound m j⟩

private theorem action_one_on_grid (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1)
    (j : ℕ) (hj : j ∈ modes m) (w : ℝ)
    (hw : w ∈ RademacherIteration.grid m) :
    killedAction RademacherCosine.law h 1 (phi m j) w = mu m j * phi m j w := by
  rcases hw with ⟨s, hslo, hshi, rfl⟩
  have hs : s ∈ states m := by
    exact Finset.mem_Icc.mpr ⟨hslo, hshi⟩
  simpa only [killedAction, killedIterKernel, pow_one, vector] using
    RademacherFiniteBasis.killedKernel_integral m hm h hmh hhm j hj s hs

/-- All actual mode powers; no division by an eigenvalue is used. -/
theorem killedAction_eq_pow (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1)
    (j : ℕ) (hj : j ∈ modes m) (r : ℤ) (hr : r ∈ states m) (n : ℕ) :
    killedAction RademacherCosine.law h n (phi m j) (r : ℝ) =
      (mu m j) ^ n * vector m j r := by
  have hr' : -(m : ℤ) ≤ r ∧ r ≤ (m : ℤ) := Finset.mem_Icc.mp hr
  induction n with
  | zero =>
      simp only [killedAction_zero, pow_zero, one_mul, vector]
  | succ n ih =>
      rw [killedAction_semigroup RademacherCosine.law h n 1 (r : ℝ) (phi m j)
        (phi_measurable m j) ⟨1, phi_bound m j⟩]
      change (∫ w : ℝ, killedAction RademacherCosine.law h 1 (phi m j) w
        ∂killedIterKernel RademacherCosine.law h n (r : ℝ)) = _
      calc
        _ = ∫ w : ℝ, mu m j * phi m j w
              ∂killedIterKernel RademacherCosine.law h n (r : ℝ) := by
          apply integral_congr_ae
          filter_upwards [RademacherIteration.killedIterKernel_ae_grid
            m hm h hmh hhm r hr'.1 hr'.2 n] with w hw
          exact action_one_on_grid m hm h hmh hhm j hj w hw
        _ = mu m j * killedAction RademacherCosine.law h n (phi m j) (r : ℝ) := by
          rw [integral_const_mul]
          rfl
        _ = (mu m j) ^ (n + 1) * vector m j r := by
          rw [ih, pow_succ]
          ring

/-- Integral form of the same identity for the actual iterated killed kernel. -/
theorem killedIterKernel_integral (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1)
    (j : ℕ) (hj : j ∈ modes m) (r : ℤ) (hr : r ∈ states m) (n : ℕ) :
    (∫ w : ℝ, phi m j w ∂killedIterKernel RademacherCosine.law h n (r : ℝ)) =
      (mu m j) ^ n * vector m j r := by
  exact killedAction_eq_pow m hm h hmh hhm j hj r hr n

private theorem constant_reconstruction_ae (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1)
    (r : ℤ) (hr : r ∈ states m) (n : ℕ) :
    (fun _ : ℝ => (1 : ℝ)) =ᵐ[killedIterKernel RademacherCosine.law h n (r : ℝ)]
      (fun w => ∑ j ∈ modes m, survivalCoefficient m j * phi m j w) := by
  have hr' : -(m : ℤ) ≤ r ∧ r ≤ (m : ℤ) := Finset.mem_Icc.mp hr
  filter_upwards [RademacherIteration.killedIterKernel_ae_grid
    m hm h hmh hhm r hr'.1 hr'.2 n] with w hw
  rcases hw with ⟨s, hslo, hshi, rfl⟩
  have hs : s ∈ states m := Finset.mem_Icc.mpr ⟨hslo, hshi⟩
  simpa only [survivalCoefficient, vector] using
    reconstruction m hm (fun _ => 1) s hs

/-- The constant-one reconstruction integrated against the actual finite kernel. -/
theorem killedMass_spectrum (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1)
    (r : ℤ) (hr : r ∈ states m) (n : ℕ) :
    killedMass RademacherCosine.law h n (r : ℝ) =
      ∑ j ∈ modes m, survivalCoefficient m j * (mu m j) ^ n * vector m j r := by
  have hint (j : ℕ) (hj : j ∈ modes m) :
      Integrable (fun w : ℝ => survivalCoefficient m j * phi m j w)
        (killedIterKernel RademacherCosine.law h n (r : ℝ)) :=
    (killedIterKernel_integrable m hm h hmh hhm j hj r hr n).const_mul _
  change (∫ w : ℝ, (1 : ℝ) ∂killedIterKernel RademacherCosine.law h n (r : ℝ)) = _
  calc
    _ = ∫ w : ℝ, ∑ j ∈ modes m, survivalCoefficient m j * phi m j w
          ∂killedIterKernel RademacherCosine.law h n (r : ℝ) :=
      integral_congr_ae (constant_reconstruction_ae m hm h hmh hhm r hr n)
    _ = ∑ j ∈ modes m, ∫ w : ℝ, survivalCoefficient m j * phi m j w
          ∂killedIterKernel RademacherCosine.law h n (r : ℝ) :=
      integral_finsetSum (modes m) hint
    _ = ∑ j ∈ modes m, survivalCoefficient m j * (mu m j) ^ n * vector m j r := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul, killedIterKernel_integral m hm h hmh hhm j hj r hr n]
      ring

/-- The same unsimplified spectrum is the real total mass of the actual kernel. -/
theorem killedIterKernel_real_univ_spectrum (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1)
    (r : ℤ) (hr : r ∈ states m) (n : ℕ) :
    (killedIterKernel RademacherCosine.law h n (r : ℝ)).real Set.univ =
      ∑ j ∈ modes m, survivalCoefficient m j * (mu m j) ^ n * vector m j r := by
  rw [← killedMass_eq_real]
  exact killedMass_spectrum m hm h hmh hhm r hr n

/-- At an arbitrary allowed integer start this is the shifted survival probability. -/
theorem shiftedClosedSurvival_probability_spectrum (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1)
    (r : ℤ) (hr : r ∈ states m) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => RademacherCosine.law)).real
        (shiftedClosedSurvival (n := n) h (r : ℝ)) =
      ∑ j ∈ modes m, survivalCoefficient m j * (mu m j) ^ n * vector m j r := by
  rw [← killedMass_eq_path_probability]
  exact killedMass_spectrum m hm h hmh hhm r hr n

/-- The original closed-strip event is obtained only at zero, with its required nonnegative threshold. -/
theorem closedStrip_probability_spectrum (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => RademacherCosine.law)).real (Shao.closedStrip h) =
      ∑ j ∈ modes m, survivalCoefficient m j * (mu m j) ^ n * vector m j 0 := by
  have hh : 0 ≤ h := le_trans (by positivity : (0 : ℝ) ≤ (m : ℝ)) hmh
  rw [← killedMass_eq_closedStrip_probability RademacherCosine.law n h hh]
  have hzero : (0 : ℤ) ∈ states m := by
    simp [states]
  simpa only [Int.cast_zero] using killedMass_spectrum m hm h hmh hhm 0 hzero n

end Shao.OQ4.RademacherAllModes
