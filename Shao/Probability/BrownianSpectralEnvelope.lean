import Shao.Probability.RademacherGrid
import Shao.OQ4.RademacherScalarBounds
import Shao.OQ4.RademacherSpectralTail
import Mathlib.Topology.Algebra.Order.Floor

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Shao.Probability.BrownianSup
open Shao.OQ4

def firstTerm (x : ℝ) : ℝ :=
  (4 / Real.pi) * Real.exp (-(Real.pi ^ 2 / 8) / x ^ 2)

private theorem firstTerm_pos (x : ℝ) : 0 < firstTerm x := by
  exact mul_pos (div_pos (by norm_num) Real.pi_pos) (Real.exp_pos _)

private theorem amplitude_eq (m : ℕ) : RademacherSpectralPairing.amplitude m = RademacherScalarBounds.a m := by
  simp only [RademacherSpectralPairing.amplitude, RademacherScalarBounds.a, RademacherScalarBounds.u, RademacherScalarBounds.H,
    Shao.OQ4.RademacherFiniteS1.cotangent]

private theorem rho_eq (m : ℕ) : RademacherSpectralPairing.rho m = RademacherScalarBounds.rho m := by
  rfl

private theorem scaled_cell_limits (x : ℝ) (hx : 0 < x) :
    let H := fun n : ℕ => (⌊x * Real.sqrt (n : ℝ)⌋₊ : ℝ) + 1
    Tendsto H atTop atTop ∧
    Tendsto (fun n : ℕ => (n : ℝ) / (H n)^2) atTop (𝓝 (1 / x^2)) ∧
    Tendsto (fun n : ℕ => (n : ℝ) / (H n)^4) atTop (𝓝 0) := by
  dsimp only
  let H := fun n : ℕ => (⌊x * Real.sqrt (n : ℝ)⌋₊ : ℝ) + 1
  have hs : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hH : Tendsto H atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => (Nat.lt_floor_add_one _).le) (hs.const_mul_atTop hx)
  have hi := tendsto_inv_atTop_zero.comp hs
  have hratio : Tendsto (fun n : ℕ => H n / Real.sqrt (n : ℝ)) atTop (𝓝 x) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using tendsto_const_nhds.add hi)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      exact (le_div_iff₀ (Real.sqrt_pos.2 hnR)).2 (Nat.lt_floor_add_one _).le
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      apply (div_le_iff₀ (Real.sqrt_pos.2 hnR)).2
      have hf := Nat.floor_le (mul_nonneg hx.le (Real.sqrt_nonneg (n : ℝ)))
      dsimp [H]
      field_simp
      nlinarith
  have ht : Tendsto (fun n : ℕ => (n : ℝ) / (H n)^2) atTop (𝓝 (1 / x^2)) := by
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).div (hratio.pow 2) (pow_ne_zero _ hx.ne')
    apply Filter.Tendsto.congr' _ hh
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hs0 := (Real.sqrt_pos.2 hnR).ne'
    have hH0 : H n ≠ 0 := by dsimp [H]; positivity
    change (1 : ℝ) / (H n / Real.sqrt (n : ℝ))^2 = (n : ℝ) / H n^2
    field_simp [hs0, hH0]
    nlinarith [Real.sq_sqrt hnR.le]
  have hiH : Tendsto (fun n : ℕ => (H n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hH
  have ht4 : Tendsto (fun n : ℕ => (n : ℝ) / (H n)^4) atTop (𝓝 (0 : ℝ)) := by
    convert ht.mul (hiH.pow 2) using 1 <;> try simp
    funext n
    simp only [div_eq_mul_inv]
    ring
  exact ⟨hH, ht, ht4⟩

 theorem rademacher_eventual_firstTerm_envelope
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      |radSurvival n x - firstTerm x| ≤
        firstTerm x * (RademacherSpectralTail.absoluteC * Real.exp (-Real.pi^2 / x^2)) + η := by
  let m := fun n : ℕ => ⌊x * Real.sqrt (n : ℝ)⌋₊
  let H := fun n : ℕ => (m n : ℝ) + 1
  let t := fun n : ℕ => (n : ℝ) / (H n)^2
  let D := fun n : ℕ => RademacherSpectralPairing.amplitude (m n) * RademacherSpectralPairing.rho (m n)^n
  let q := fun n : ℕ => (Real.tan (Real.pi / (4 * H n)))^2
  rcases scaled_cell_limits x hx with ⟨hH, ht, ht4⟩
  change Tendsto H atTop atTop at hH
  change Tendsto t atTop (𝓝 (1 / x^2)) at ht
  change Tendsto (fun n : ℕ => (n : ℝ) / (H n)^4) atTop (𝓝 0) at ht4
  have hm : ∀ᶠ n in atTop, 1 ≤ m n := by
    filter_upwards [hH.eventually (eventually_ge_atTop (2 : ℝ))] with n hn
    dsimp [H] at hn
    exact_mod_cast (show (1 : ℝ) ≤ (m n : ℝ) by linarith)
  have hiH : Tendsto (fun n : ℕ => (H n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hH
  have ha : Tendsto (fun n : ℕ => RademacherSpectralPairing.amplitude (m n)) atTop (𝓝 (4 / Real.pi)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq]
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
    · filter_upwards [hm] with n hn
      simpa only [amplitude_eq, RademacherScalarBounds.H] using RademacherScalarBounds.SCA1 hn
    · have hh := (hiH.pow 2).const_mul RademacherScalarBounds.C_a
      simpa [div_eq_mul_inv, inv_pow] using hh
  have hrlog : Tendsto (fun n : ℕ => (n : ℝ) * Real.log (RademacherSpectralPairing.rho (m n)))
      atTop (𝓝 (-(Real.pi^2/8) / x^2)) := by
    have he : Tendsto
        (fun n : ℕ => |(n : ℝ) * Real.log (RademacherSpectralPairing.rho (m n)) +
          (Real.pi^2/8) * t n|) atTop (𝓝 (0 : ℝ)) := by
      apply squeeze_zero' (g := fun n : ℕ => RademacherScalarBounds.C_rho * ((n : ℝ) / H n ^ 4)) (Eventually.of_forall (fun _ => abs_nonneg _))
      · filter_upwards [hm] with n hn
        have hh := mul_le_mul_of_nonneg_left (RademacherScalarBounds.SCA2 hn) (Nat.cast_nonneg n : (0:ℝ) ≤ n)
        calc
          _ = |(n : ℝ) * (Real.log (RademacherScalarBounds.rho (m n)) +
              RademacherScalarBounds.lambda / RademacherScalarBounds.H (m n)^2)| := by
            congr 1
            rw [rho_eq]
            dsimp [RademacherScalarBounds.lambda, RademacherScalarBounds.H, H, t]
            ring
          _ = (n : ℝ) * |Real.log (RademacherScalarBounds.rho (m n)) +
              RademacherScalarBounds.lambda / RademacherScalarBounds.H (m n)^2| := by
            rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
          _ ≤ (n : ℝ) * (RademacherScalarBounds.C_rho / RademacherScalarBounds.H (m n)^4) := hh
          _ = _ := by dsimp [RademacherScalarBounds.H, H]; ring
      · simpa [mul_div_assoc] using ht4.const_mul RademacherScalarBounds.C_rho
    have he' : Tendsto
        (fun n : ℕ => (n : ℝ) * Real.log (RademacherSpectralPairing.rho (m n)) + (Real.pi^2/8) * t n)
        atTop (𝓝 (0 : ℝ)) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      simpa [Real.dist_eq] using he
    have hh := he'.sub (ht.const_mul (Real.pi^2/8))
    convert hh using 1 <;> (try funext n) <;> ring
  have hD : Tendsto D atTop (𝓝 (firstTerm x)) := by
    have he := ha.mul (Real.continuous_exp.tendsto _ |>.comp hrlog)
    apply Filter.Tendsto.congr' _ he
    filter_upwards [hm] with n hn
    dsimp [D, firstTerm]
    rw [Real.exp_nat_mul, Real.exp_log (RademacherSpectralPairing.rho_pos hn)]
  have hq : Tendsto q atTop (𝓝 (0 : ℝ)) := by
    have hu : Tendsto (fun n : ℕ => Real.pi / (4 * H n)) atTop (𝓝 (0 : ℝ)) := by
      simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hiH.const_mul (Real.pi/4)
    have htan := (Real.continuousAt_tan.mpr (by simp : Real.cos (0:ℝ) ≠ 0)).tendsto.comp hu
    simpa [q] using htan.pow 2
  have hE : Tendsto (fun n : ℕ => RademacherSpectralTail.absoluteC * Real.exp (-Real.pi^2 * t n))
      atTop (𝓝 (RademacherSpectralTail.absoluteC * Real.exp (-Real.pi^2 / x^2))) := by
    simpa [div_eq_mul_inv, mul_assoc] using
      ((Real.continuous_exp.tendsto _).comp (ht.const_mul (-Real.pi^2))).const_mul RademacherSpectralTail.absoluteC
  have hbound : Tendsto
      (fun n : ℕ => |D n - firstTerm x| +
        D n * (q n + RademacherSpectralTail.absoluteC * Real.exp (-Real.pi^2 * t n))) atTop
      (𝓝 (firstTerm x * (RademacherSpectralTail.absoluteC * Real.exp (-Real.pi^2 / x^2)))) := by
    simpa using ((hD.sub (tendsto_const_nhds (x := firstTerm x))).abs).add (hD.mul (hq.add hE))
  have htime : ∀ᶠ n in atTop, H n ^2 ≤ (n : ℝ) := by
    have htx : (1 : ℝ) < 1/x^2 := by
      apply (lt_div_iff₀ (sq_pos_of_pos hx)).2
      nlinarith
    filter_upwards [ht.eventually (eventually_gt_nhds htx)] with n hn
    have hp : 0 < H n^2 := by dsimp [H]; positivity
    simpa only [one_mul] using ((lt_div_iff₀ hp).1 hn).le
  filter_upwards [hm, htime, hbound.eventually (eventually_lt_nhds (lt_add_of_pos_right _ hη))] with n hmn htn hbn
  have hcell : radSurvival n x = D n *
      (1 + RademacherSpectralPairing.epsilon (m n) n * q n + RademacherSpectralPairing.remainder (m n) n) := by
    exact RademacherSpectralPairing.closedStrip_probability_normalized (m n) hmn (x * Real.sqrt (n : ℝ))
      (Nat.floor_le (mul_nonneg hx.le (Real.sqrt_nonneg _))) (Nat.lt_floor_add_one _) n
  have hr := RademacherSpectralTail.remainder_uniform hmn htn
  have heps : |RademacherSpectralPairing.epsilon (m n) n| = 1 := by
    simp [RademacherSpectralPairing.epsilon, abs_pow]
  have hd : 0 ≤ D n := (RademacherSpectralPairing.normalizer_pos hmn n).le
  have hq0 : 0 ≤ q n := sq_nonneg _
  have hdiff : |radSurvival n x - D n| ≤
      D n * (q n + RademacherSpectralTail.absoluteC * Real.exp (-Real.pi^2 * t n)) := by
    rw [hcell]
    have hid : D n * (1 + RademacherSpectralPairing.epsilon (m n) n * q n + RademacherSpectralPairing.remainder (m n) n) - D n =
        D n * (RademacherSpectralPairing.epsilon (m n) n * q n + RademacherSpectralPairing.remainder (m n) n) := by ring
    rw [hid, abs_mul, abs_of_nonneg hd]
    apply mul_le_mul_of_nonneg_left _ hd
    calc
      _ ≤ |RademacherSpectralPairing.epsilon (m n) n * q n| + |RademacherSpectralPairing.remainder (m n) n| := abs_add_le _ _
      _ ≤ q n + RademacherSpectralTail.absoluteC * Real.exp (-Real.pi^2 * t n) := by
        rw [abs_mul, heps, one_mul, abs_of_nonneg hq0]
        exact add_le_add le_rfl (by simpa [t, H, div_eq_mul_inv, mul_assoc] using hr)
  have htri := abs_add_le (radSurvival n x - D n) (D n - firstTerm x)
  have heq : radSurvival n x - D n + (D n - firstTerm x) = radSurvival n x - firstTerm x := by ring
  rw [heq] at htri
  linarith

end Shao.Probability.BrownianSup
