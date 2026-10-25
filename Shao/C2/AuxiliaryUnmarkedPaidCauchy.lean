import Shao.C2.AuxiliaryUnmarkedDampedMoments
import Shao.C2.AuxiliaryThirdMomentTruncation
import Shao.C2.AuxiliaryUnmarkedBlockRealCauchy

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryUnmarkedPaidCauchy
open MeasureTheory ProbabilityTheory

theorem auxiliary_actual_unmarked_decaying_moments :
    let c : ℝ := (1 - Real.exp (-2)) / 8
    ∀ p : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
        Integrable (fun z : ℝ => z ^ 2) nu →
        Integrable (fun z : ℝ => |z| ^ 3) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ (n : ℕ) (s : ℝ), 0 < s →
          s * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 ≤ 1 / 2 →
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          Integrable (fun v : Shao.Path n =>
            |Shao.prefixSum v n| ^ p * Real.exp (-s * Shao.energy v)) P ∧
            (∫ v : Shao.Path n,
              |Shao.prefixSum v n| ^ p * Real.exp (-s * Shao.energy v) ∂P) ≤
              C * Real.rpow s (-(p : ℝ) / 2) *
                Real.exp (-c * s * (n : ℝ)) := by
  intro c p
  obtain ⟨C, hC, hMoment⟩ :=
    Shao.C2.AuxiliaryUnmarkedDampedMoments.auxiliary_actual_unmarked_gaussian_damped_moments p
  refine ⟨C, hC, ?_⟩
  intro nu _ h2 h3 hMean hNorm n s hs hSmall P
  let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
  have hRetained :=
    Shao.C2.AuxiliaryThirdMomentTruncation.auxiliary_actual_third_moment_retains_half
      nu h2 h3 hNorm
  change 0 < 4 * beta ^ 2 ∧
    (1 / 2 : ℝ) ≤ ∫ z : ℝ, if z ^ 2 ≤ 4 * beta ^ 2 then z ^ 2 else 0 ∂nu at hRetained
  have hsb : s ≤ 2 / (4 * beta ^ 2) := by
    apply (le_div_iff₀ hRetained.1).2
    change s * beta ^ 2 ≤ 1 / 2 at hSmall
    nlinarith [hSmall]
  have hm := hMoment nu h2 hMean hNorm n (4 * beta ^ 2) s hRetained.1 hs hsb
  dsimp only at hm
  rw [if_pos hRetained.2] at hm
  exact hm

theorem auxiliary_actual_unmarked_cauchy_paid :
    let c : ℝ := (1 - Real.exp (-2)) / 8
    ∀ p : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
        Integrable (fun z : ℝ => z ^ 2) nu →
        Integrable (fun z : ℝ => |z| ^ 3) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ (n : ℕ) (s : ℝ), 0 < s →
          s * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 ≤ 1 / 2 →
          ∀ A : Set (Shao.Path n), MeasurableSet A →
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
            let W : Shao.Path n → ℝ := fun v => Real.exp (-s * Shao.energy v)
            let D : Shao.Path n → ℝ := fun v => Real.rpow |Shao.prefixSum v n| (p : ℝ) * W v
            Integrable (A.indicator D) P ∧
              (∫ v : Shao.Path n, A.indicator D v ∂P) ≤
                C * Real.rpow s (-(p : ℝ) / 2) *
                  Real.exp (-(c / 2) * s * (n : ℝ)) *
                  Real.sqrt (∫ v : Shao.Path n, A.indicator W v ∂P) := by
  intro c p
  obtain ⟨C2, hC2, hMoment⟩ := auxiliary_actual_unmarked_decaying_moments (2 * p)
  refine ⟨Real.sqrt C2, Real.sqrt_pos.2 hC2, ?_⟩
  intro nu _ h2 h3 hMean hNorm n s hs hSmall A hA P W D
  have hm := hMoment nu h2 h3 hMean hNorm n s hs hSmall
  have hCast (v : Shao.Path n) :
      Real.rpow |Shao.prefixSum v n| (2 * (p : ℝ)) = |Shao.prefixSum v n| ^ (2 * p) := by
    calc
      _ = Real.rpow |Shao.prefixSum v n| ((2 * p : ℕ) : ℝ) :=
        congrArg (fun u : ℝ => Real.rpow |Shao.prefixSum v n| u) (by push_cast; ring)
      _ = _ := Real.rpow_natCast _ (2 * p)
  have hDampedFun :
      (fun v : Shao.Path n => Real.rpow |Shao.prefixSum v n| (2 * (p : ℝ)) * W v) =
        (fun v => |Shao.prefixSum v n| ^ (2 * p) * Real.exp (-s * Shao.energy v)) := by
    funext v
    rw [hCast]
  have hDamped : Integrable
      (fun v : Shao.Path n => Real.rpow |Shao.prefixSum v n| (2 * (p : ℝ)) * W v) P := by
    rw [hDampedFun]
    exact hm.1
  have hCauchy :=
    Shao.C2.AuxiliaryUnmarkedBlockRealCauchy.auxiliary_actual_unmarked_block_real_cauchy
      nu n (p : ℝ) s (Nat.cast_nonneg p) hs.le A hA hDamped
  refine ⟨hCauchy.1, ?_⟩
  let R : ℝ := Real.sqrt C2 * Real.rpow s (-(p : ℝ) / 2) *
    Real.exp (-(c / 2) * s * (n : ℝ))
  have hR : 0 ≤ R := mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg C2) (Real.rpow_nonneg hs.le _)) (Real.exp_pos _).le
  have hPower : (Real.rpow s (-(p : ℝ) / 2)) ^ 2 =
      Real.rpow s (-((2 * p : ℕ) : ℝ) / 2) := by
    calc
      _ = Real.rpow (Real.rpow s (-(p : ℝ) / 2)) (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = Real.rpow s ((-(p : ℝ) / 2) * 2) :=
        (Real.rpow_mul hs.le _ 2).symm
      _ = _ := congrArg (fun u : ℝ => Real.rpow s u) (by push_cast; ring)
  have hExp : (Real.exp (-(c / 2) * s * (n : ℝ))) ^ 2 =
      Real.exp (-c * s * (n : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hSquare : R ^ 2 = C2 * Real.rpow s (-((2 * p : ℕ) : ℝ) / 2) *
      Real.exp (-c * s * (n : ℝ)) := by
    dsimp only [R]
    rw [mul_pow, mul_pow, Real.sq_sqrt hC2.le, hPower, hExp]
  have hRoot : Real.sqrt (C2 * Real.rpow s (-((2 * p : ℕ) : ℝ) / 2) *
      Real.exp (-c * s * (n : ℝ))) = R := by
    rw [← hSquare, Real.sqrt_sq_eq_abs, abs_of_nonneg hR]
  have hRootBound :
      Real.sqrt (∫ v : Shao.Path n,
        Real.rpow |Shao.prefixSum v n| (2 * (p : ℝ)) * W v ∂P) ≤ R := by
    rw [hDampedFun]
    exact (Real.sqrt_le_sqrt hm.2).trans_eq hRoot
  exact hCauchy.2.trans
    (mul_le_mul_of_nonneg_right hRootBound (Real.sqrt_nonneg _))

end Shao.C2.AuxiliaryUnmarkedPaidCauchy
