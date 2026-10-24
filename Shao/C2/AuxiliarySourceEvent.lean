import Shao.C2.AuxiliaryCenteredEvent

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.C2.AuxiliarySourceEvent

theorem auxiliary_rare_thresholds (x : ℝ) (hx : 1 ≤ x) :
    let a : ℝ := Real.sqrt ((9 / 4) * x ^ 2 - 1)
    let y : ℝ := a - 1 / (100 * (1 + x))
    1 ≤ y ∧ y ≤ 2 * x ∧ a - y = 1 / (100 * (1 + x)) := by
  intro a y
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hRad : 0 ≤ (9 / 4 : ℝ) * x ^ 2 - 1 := by
    nlinarith [sq_nonneg (x - 1)]
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have haSq : a ^ 2 = (9 / 4 : ℝ) * x ^ 2 - 1 := Real.sq_sqrt hRad
  have hLower : (11 / 10 : ℝ) ≤ a := by
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 11 / 10) ha0).1
    rw [haSq]
    nlinarith [sq_nonneg (x - 1)]
  have hUpper : a ≤ (3 / 2 : ℝ) * x := by
    apply (sq_le_sq₀ ha0 (mul_nonneg (by norm_num) hx0)).1
    rw [haSq]
    nlinarith
  have hDelta0 : 0 ≤ 1 / (100 * (1 + x)) := by positivity
  have hDelta : 1 / (100 * (1 + x)) ≤ (1 / 100 : ℝ) := by
    apply (div_le_iff₀ (show 0 < 100 * (1 + x) by positivity)).2
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · dsimp [y]
    linarith
  · dsimp [y]
    linarith
  · dsimp [y]
    ring

theorem auxiliary_centered_source_weak_event
    {n : ℕ} (v : Shao.Path n) (mu x : ℝ) (hx : 1 ≤ x)
    (hRank : 4 * x ^ 2 ≤ (n : ℝ))
    (hEnergy : (n : ℝ) / 8 ≤ Shao.energy v)
    (hDrift : Real.sqrt (n : ℝ) * |mu| ≤ 1 / (1000 * (1 + x)))
    (hCross : Real.sqrt ((9 / 4) * x ^ 2 - 1) * Real.sqrt (Shao.energy v) ≤
      |Shao.prefixSum v n|) :
    let a : ℝ := Real.sqrt ((9 / 4) * x ^ 2 - 1)
    let y : ℝ := a - 1 / (100 * (1 + x))
    y * Real.sqrt (Shao.energy (fun i => v i - mu)) ≤
      |Shao.prefixSum (fun i => v i - mu) n| := by
  intro a y
  rcases auxiliary_rare_thresholds x hx with ⟨hy1, hy2, hGap⟩
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hyN : y ≤ Real.sqrt (n : ℝ) := by
    apply hy2.trans
    apply (sq_le_sq₀ (show 0 ≤ 2 * x by positivity) (Real.sqrt_nonneg _)).1
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    nlinarith
  have hRootEnergy : Real.sqrt (n : ℝ) ≤ 4 * Real.sqrt (Shao.energy v) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (show 0 ≤ 4 * Real.sqrt (Shao.energy v) by positivity)).1
    rw [Real.sq_sqrt (Nat.cast_nonneg n), mul_pow, Real.sq_sqrt (Shao.energy_nonneg v)]
    nlinarith [(show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)]
  let delta : ℝ := 1 / (100 * (1 + x))
  have hDelta0 : 0 ≤ delta := by dsimp [delta]; positivity
  have hScale : 1 / (1000 * (1 + x)) = delta / 10 := by
    dsimp [delta]
    field_simp [show (1 + x) ≠ 0 by linarith]
    <;> ring
  have hDriftDelta : Real.sqrt (n : ℝ) * |mu| ≤ delta / 10 := hDrift.trans_eq hScale
  apply Shao.C2.AuxiliaryCenteredEvent.auxiliary_centered_weak_event v mu a y
    (zero_le_one.trans hy1) ?_ hCross
  rw [hGap]
  change (Real.sqrt (n : ℝ) + y) * Real.sqrt (n : ℝ) * |mu| ≤
    delta * Real.sqrt (Shao.energy v)
  calc
    (Real.sqrt (n : ℝ) + y) * Real.sqrt (n : ℝ) * |mu| =
        (Real.sqrt (n : ℝ) + y) * (Real.sqrt (n : ℝ) * |mu|) := by ring
    _ ≤ (2 * Real.sqrt (n : ℝ)) * (Real.sqrt (n : ℝ) * |mu|) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    _ ≤ (2 * Real.sqrt (n : ℝ)) * (delta / 10) :=
      mul_le_mul_of_nonneg_left hDriftDelta (by positivity)
    _ = (delta / 5) * Real.sqrt (n : ℝ) := by ring
    _ ≤ (delta / 5) * (4 * Real.sqrt (Shao.energy v)) :=
      mul_le_mul_of_nonneg_left hRootEnergy (div_nonneg hDelta0 (by norm_num))
    _ ≤ delta * Real.sqrt (Shao.energy v) := by
      have hh := mul_nonneg hDelta0 (Real.sqrt_nonneg (Shao.energy v))
      nlinarith

end Shao.C2.AuxiliarySourceEvent
