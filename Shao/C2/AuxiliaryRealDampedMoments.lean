import Shao.C2.AuxiliaryUnmarkedDampedMoments
import Shao.C2.AuxiliaryHigherMarkDamped
import Shao.C2.AuxiliaryThirdMomentTruncation
import Shao.C2.AuxiliaryUnmarkedBlockRealCauchy
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Shao.C2.AuxiliaryRealDampedMoments
open MeasureTheory ProbabilityTheory

private theorem scaled_real_power_le
    (x a s : ℝ) (k : ℕ) (hx : 0 ≤ x) (ha : 0 ≤ a) (hs : 0 < s) (hk : a ≤ (k : ℝ)) :
    Real.rpow x a ≤ Real.rpow s (-a / 2) *
      (1 + Real.rpow s ((k : ℝ) / 2) * x ^ k) := by
  let y : ℝ := Real.rpow s (1 / 2 : ℝ) * x
  have hy : 0 ≤ y := mul_nonneg (Real.rpow_nonneg hs.le _) hx
  have hNat : y ^ k = Real.rpow s ((k : ℝ) / 2) * x ^ k := by
    have hScale : (Real.rpow s (1 / 2 : ℝ)) ^ k = Real.rpow s ((k : ℝ) / 2) := by
      calc
        _ = Real.rpow (Real.rpow s (1 / 2 : ℝ)) (k : ℝ) :=
          (Real.rpow_natCast _ k).symm
        _ = Real.rpow s ((1 / 2 : ℝ) * (k : ℝ)) :=
          (Real.rpow_mul hs.le _ _).symm
        _ = _ := congrArg (fun u : ℝ => Real.rpow s u) (by ring)
    dsimp only [y]
    rw [mul_pow, hScale]
  have hSmall : Real.rpow y a ≤ 1 + y ^ k := by
    by_cases hOne : y ≤ 1
    · exact (Real.rpow_le_one hy hOne ha).trans (le_add_of_nonneg_right (pow_nonneg hy k))
    · have hCompare := Real.rpow_le_rpow_of_exponent_le (lt_of_not_ge hOne).le hk
      have hNatCast := Real.rpow_natCast y k
      exact hCompare.trans (by rw [hNatCast]; linarith)
  have hFactor : Real.rpow s (-a / 2) * Real.rpow y a = Real.rpow x a := by
    change s ^ (-a / 2) * ((s ^ (1 / 2 : ℝ) * x) ^ a) = x ^ a
    rw [Real.mul_rpow (Real.rpow_nonneg hs.le _) hx, ← Real.rpow_mul hs.le,
      ← mul_assoc, ← Real.rpow_add hs]
    rw [show -a / 2 + (1 / 2 : ℝ) * a = 0 by ring, Real.rpow_zero, one_mul]
  calc
    _ = Real.rpow s (-a / 2) * Real.rpow y a := hFactor.symm
    _ ≤ Real.rpow s (-a / 2) * (1 + y ^ k) :=
      mul_le_mul_of_nonneg_left hSmall (Real.rpow_nonneg hs.le _)
    _ = _ := by rw [hNat]

theorem auxiliary_actual_unmarked_real_gaussian_damped_moments :
    let c : ℝ := (1 - Real.exp (-2)) / 8
    ∀ a : ℝ, 0 ≤ a → ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ (n : ℕ) (b s : ℝ), 0 < b → 0 < s → s ≤ 2 / b →
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          let retained : ℝ := ∫ z : ℝ, if z ^ 2 ≤ b then z ^ 2 else 0 ∂nu
          let gamma : ℝ := if (1 / 2 : ℝ) ≤ retained then -c else 1
          Integrable (fun v : Shao.Path n =>
            Real.rpow |Shao.prefixSum v n| a * Real.exp (-s * Shao.energy v)) P ∧
            (∫ v : Shao.Path n,
              Real.rpow |Shao.prefixSum v n| a * Real.exp (-s * Shao.energy v) ∂P) ≤
              C * Real.rpow s (-a / 2) * Real.exp (gamma * s * (n : ℝ)) := by
  intro c a ha
  let k : ℕ := Nat.ceil a
  have hka : a ≤ (k : ℝ) := Nat.le_ceil a
  obtain ⟨C0, hC0, hMoment0⟩ :=
    Shao.C2.AuxiliaryUnmarkedDampedMoments.auxiliary_actual_unmarked_gaussian_damped_moments 0
  obtain ⟨Ck, hCk, hMomentk⟩ :=
    Shao.C2.AuxiliaryUnmarkedDampedMoments.auxiliary_actual_unmarked_gaussian_damped_moments k
  refine ⟨C0 + Ck, add_pos hC0 hCk, ?_⟩
  intro nu _ h2 hMean hNorm n b s hb hs hsb P retained gamma
  let W : Shao.Path n → ℝ := fun v => Real.exp (-s * Shao.energy v)
  let Fk : Shao.Path n → ℝ := fun v => |Shao.prefixSum v n| ^ k * W v
  let A : ℝ := Real.rpow s (-a / 2)
  let B : ℝ := Real.rpow s ((k : ℝ) / 2)
  let E : ℝ := Real.exp (gamma * s * (n : ℝ))
  let U : Shao.Path n → ℝ := fun v => A * (W v + B * Fk v)
  have hRpowZero : Real.rpow s 0 = 1 := Real.rpow_zero s
  have h0 : Integrable W P ∧ (∫ v : Shao.Path n, W v ∂P) ≤ C0 * E := by
    simpa only [pow_zero, one_mul, Nat.cast_zero, neg_zero, zero_div,
      hRpowZero, mul_one] using hMoment0 nu h2 hMean hNorm n b s hb hs hsb
  have hkMoment := hMomentk nu h2 hMean hNorm n b s hb hs hsb
  have hU : Integrable U P := (h0.1.add (hkMoment.1.const_mul B)).const_mul A
  have hPoint (v : Shao.Path n) : Real.rpow |Shao.prefixSum v n| a * W v ≤ U v := by
    calc
      _ ≤ (A * (1 + B * |Shao.prefixSum v n| ^ k)) * W v :=
        mul_le_mul_of_nonneg_right
          (scaled_real_power_le |Shao.prefixSum v n| a s k (abs_nonneg _) ha hs hka)
          (Real.exp_pos _).le
      _ = _ := by dsimp only [U, Fk]; ring
  have hMeas : Continuous (fun v : Shao.Path n => Real.rpow |Shao.prefixSum v n| a * W v) :=
    ((Shao.continuous_prefixSum n).abs.rpow_const (fun _ => Or.inr ha)).mul
      (Real.continuous_exp.comp (continuous_const.mul Shao.continuous_energy))
  have hInt : Integrable (fun v : Shao.Path n => Real.rpow |Shao.prefixSum v n| a * W v) P := by
    refine hU.mono' hMeas.aestronglyMeasurable (ae_of_all _ fun v => ?_)
    have hNonneg : 0 ≤ Real.rpow |Shao.prefixSum v n| a * W v :=
      mul_nonneg (Real.rpow_nonneg (abs_nonneg _) a) (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
    exact hPoint v
  have hCancel : B * Real.rpow s (-(k : ℝ) / 2) = 1 := by
    change s ^ ((k : ℝ) / 2) * s ^ (-(k : ℝ) / 2) = 1
    rw [← Real.rpow_add hs, show (k : ℝ) / 2 + -(k : ℝ) / 2 = 0 by ring, Real.rpow_zero]
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ v : Shao.Path n, U v ∂P := integral_mono hInt hU hPoint
    _ = A * ((∫ v : Shao.Path n, W v ∂P) + B * ∫ v : Shao.Path n, Fk v ∂P) := by
      dsimp only [U]
      rw [integral_const_mul, integral_add h0.1 (hkMoment.1.const_mul B), integral_const_mul]
    _ ≤ A * (C0 * E + B * (Ck * Real.rpow s (-(k : ℝ) / 2) * E)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add h0.2 (mul_le_mul_of_nonneg_left hkMoment.2 (Real.rpow_nonneg hs.le _)))
        (Real.rpow_nonneg hs.le _)
    _ = (C0 + Ck * (B * Real.rpow s (-(k : ℝ) / 2))) * A * E := by ring
    _ = _ := by rw [hCancel]; ring

theorem auxiliary_actual_higher_real_mark_damped :
    ∀ a : ℝ, 0 ≤ a → ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
        Integrable (fun z : ℝ => z ^ 2) nu →
        Integrable (fun z : ℝ => |z| ^ 3) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ s : ℝ, 0 < s →
          Integrable (fun z : ℝ => |z| ^ 3 * Real.rpow |z| a * Real.exp (-s * z ^ 2)) nu ∧
            (∫ z : ℝ, |z| ^ 3 * Real.rpow |z| a * Real.exp (-s * z ^ 2) ∂nu) ≤
              C * Real.rpow s (-a / 2) * (∫ z : ℝ, |z| ^ 3 ∂nu) := by
  intro a ha
  let k : ℕ := Nat.ceil a
  have hka : a ≤ (k : ℝ) := Nat.le_ceil a
  obtain ⟨Ck, hCk, hMomentk⟩ :=
    Shao.C2.AuxiliaryHigherMarkDamped.auxiliary_actual_higher_mark_damped k
  refine ⟨1 + Ck, by linarith, ?_⟩
  intro nu _ h2 h3 hMean hNorm s hs
  let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
  let f0 : ℝ → ℝ := fun z => |z| ^ 3 * Real.exp (-s * z ^ 2)
  let Fk : ℝ → ℝ := fun z => |z| ^ (3 + k) * Real.exp (-s * z ^ 2)
  let A : ℝ := Real.rpow s (-a / 2)
  let B : ℝ := Real.rpow s ((k : ℝ) / 2)
  let U : ℝ → ℝ := fun z => A * (f0 z + B * Fk z)
  have hf0Bound (z : ℝ) : f0 z ≤ |z| ^ 3 := by
    exact (mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (sq_nonneg z)))
      (pow_nonneg (abs_nonneg z) 3)).trans_eq (mul_one _)
  have hf0 : Integrable f0 nu := by
    refine h3.mono' (by dsimp only [f0]; fun_prop) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (abs_nonneg z) 3) (Real.exp_pos _).le)]
    exact hf0Bound z
  have h0 : (∫ z : ℝ, f0 z ∂nu) ≤ beta := integral_mono hf0 h3 hf0Bound
  have hkMoment := hMomentk nu h2 h3 hMean hNorm s hs
  have hU : Integrable U nu := (hf0.add (hkMoment.1.const_mul B)).const_mul A
  have hPoint (z : ℝ) : |z| ^ 3 * Real.rpow |z| a * Real.exp (-s * z ^ 2) ≤ U z := by
    calc
      _ = Real.rpow |z| a * (|z| ^ 3 * Real.exp (-s * z ^ 2)) := by ring
      _ ≤ (A * (1 + B * |z| ^ k)) * (|z| ^ 3 * Real.exp (-s * z ^ 2)) :=
        mul_le_mul_of_nonneg_right (scaled_real_power_le |z| a s k (abs_nonneg _) ha hs hka)
          (mul_nonneg (pow_nonneg (abs_nonneg z) 3) (Real.exp_pos _).le)
      _ = _ := by dsimp only [U, f0, Fk]; rw [pow_add]; ring
  have hAbs : Continuous (fun z : ℝ => |z|) := continuous_abs
  have hMeas : Continuous (fun z : ℝ => |z| ^ 3 * Real.rpow |z| a * Real.exp (-s * z ^ 2)) :=
    ((hAbs.pow 3).mul (hAbs.rpow_const (fun _ => Or.inr ha))).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2)))
  have hInt : Integrable (fun z : ℝ => |z| ^ 3 * Real.rpow |z| a * Real.exp (-s * z ^ 2)) nu := by
    refine hU.mono' hMeas.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    have hNonneg : 0 ≤ |z| ^ 3 * Real.rpow |z| a * Real.exp (-s * z ^ 2) :=
      mul_nonneg (mul_nonneg (pow_nonneg (abs_nonneg z) 3)
        (Real.rpow_nonneg (abs_nonneg z) a)) (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
    exact hPoint z
  have hCancel : B * Real.rpow s (-(k : ℝ) / 2) = 1 := by
    change s ^ ((k : ℝ) / 2) * s ^ (-(k : ℝ) / 2) = 1
    rw [← Real.rpow_add hs, show (k : ℝ) / 2 + -(k : ℝ) / 2 = 0 by ring, Real.rpow_zero]
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ z : ℝ, U z ∂nu := integral_mono hInt hU hPoint
    _ = A * ((∫ z : ℝ, f0 z ∂nu) + B * ∫ z : ℝ, Fk z ∂nu) := by
      dsimp only [U]
      rw [integral_const_mul, integral_add hf0 (hkMoment.1.const_mul B), integral_const_mul]
    _ ≤ A * (beta + B * (Ck * Real.rpow s (-(k : ℝ) / 2) * beta)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add h0 (mul_le_mul_of_nonneg_left hkMoment.2 (Real.rpow_nonneg hs.le _)))
        (Real.rpow_nonneg hs.le _)
    _ = (1 + Ck * (B * Real.rpow s (-(k : ℝ) / 2))) * A * beta := by ring
    _ = _ := by rw [hCancel]; ring

theorem auxiliary_actual_unmarked_real_cauchy_paid :
    let c : ℝ := (1 - Real.exp (-2)) / 8
    ∀ a : ℝ, 0 ≤ a → ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
        Integrable (fun z : ℝ => z ^ 2) nu →
        Integrable (fun z : ℝ => |z| ^ 3) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ (n : ℕ) (s : ℝ), 0 < s →
          s * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 ≤ 1 / 2 →
          ∀ A : Set (Shao.Path n), MeasurableSet A →
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
            let W : Shao.Path n → ℝ := fun v => Real.exp (-s * Shao.energy v)
            let D : Shao.Path n → ℝ := fun v => Real.rpow |Shao.prefixSum v n| a * W v
            Integrable (A.indicator D) P ∧
              (∫ v : Shao.Path n, A.indicator D v ∂P) ≤
                C * Real.rpow s (-a / 2) * Real.exp (-(c / 2) * s * (n : ℝ)) *
                  Real.sqrt (∫ v : Shao.Path n, A.indicator W v ∂P) := by
  intro c a ha
  obtain ⟨C2, hC2, hMoment⟩ := auxiliary_actual_unmarked_real_gaussian_damped_moments (2 * a)
    (mul_nonneg (by norm_num) ha)
  refine ⟨Real.sqrt C2, Real.sqrt_pos.2 hC2, ?_⟩
  intro nu _ h2 h3 hMean hNorm n s hs hSmall A hA P W D
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
  have hCauchy :=
    Shao.C2.AuxiliaryUnmarkedBlockRealCauchy.auxiliary_actual_unmarked_block_real_cauchy
      nu n a s ha hs.le A hA hm.1
  refine ⟨hCauchy.1, ?_⟩
  let R : ℝ := Real.sqrt C2 * Real.rpow s (-a / 2) * Real.exp (-(c / 2) * s * (n : ℝ))
  have hR : 0 ≤ R := mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg C2) (Real.rpow_nonneg hs.le _)) (Real.exp_pos _).le
  have hPower : (Real.rpow s (-a / 2)) ^ 2 = Real.rpow s (-(2 * a) / 2) := by
    calc
      _ = Real.rpow (Real.rpow s (-a / 2)) (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = Real.rpow s ((-a / 2) * 2) := (Real.rpow_mul hs.le _ 2).symm
      _ = _ := congrArg (fun u : ℝ => Real.rpow s u) (by ring)
  have hExp : (Real.exp (-(c / 2) * s * (n : ℝ))) ^ 2 =
      Real.exp (-c * s * (n : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hSquare : R ^ 2 = C2 * Real.rpow s (-(2 * a) / 2) *
      Real.exp (-c * s * (n : ℝ)) := by
    dsimp only [R]
    rw [mul_pow, mul_pow, Real.sq_sqrt hC2.le, hPower, hExp]
  have hRoot : Real.sqrt (C2 * Real.rpow s (-(2 * a) / 2) *
      Real.exp (-c * s * (n : ℝ))) = R := by
    rw [← hSquare, Real.sqrt_sq_eq_abs, abs_of_nonneg hR]
  have hRootBound : Real.sqrt (∫ v : Shao.Path n,
      Real.rpow |Shao.prefixSum v n| (2 * a) * W v ∂P) ≤ R :=
    (Real.sqrt_le_sqrt hm.2).trans_eq hRoot
  exact hCauchy.2.trans (mul_le_mul_of_nonneg_right hRootBound (Real.sqrt_nonneg _))

end Shao.C2.AuxiliaryRealDampedMoments
