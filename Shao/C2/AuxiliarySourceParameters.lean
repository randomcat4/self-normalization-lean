import Shao.C2.AuxiliarySourceEvent

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.C2.AuxiliarySourceParameters
open MeasureTheory ProbabilityTheory

theorem auxiliary_rare_parameter_payment
    (beta L s : ℝ) (hBeta : 1 ≤ beta) (hL : 0 ≤ L) (hs : 0 ≤ s)
    (n : ℕ) (x : ℝ) (hx : 1 ≤ x)
    (hTime : s * (n : ℝ) ≤ L * x ^ 2)
    (hRank : 4000000 * (1 + L) ^ 2 * beta ^ 2 * (1 + x) ^ 6 ≤ (n : ℝ)) :
    0 < n ∧ 4 * x ^ 2 ≤ (n : ℝ) ∧ s * beta ^ 2 ≤ 1 / 128 ∧
      Real.sqrt (n : ℝ) * (2 * s * beta) ≤ 1 / (1000 * (1 + x)) := by
  let c : ℝ := 1 + L
  let d : ℝ := 1 + x
  have hc : 0 < c := by dsimp [c]; linarith
  have hd : 0 < d := by dsimp [d]; linarith
  have hb : 0 < beta := by linarith
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  change 4000000 * c ^ 2 * beta ^ 2 * d ^ 6 ≤ (n : ℝ) at hRank
  have hRoot : 2000 * c * beta * d ^ 3 ≤ Real.sqrt (n : ℝ) := by
    apply (sq_le_sq₀ (show 0 ≤ 2000 * c * beta * d ^ 3 by positivity)
      (Real.sqrt_nonneg _)).1
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    calc
      (2000 * c * beta * d ^ 3) ^ 2 = 4000000 * c ^ 2 * beta ^ 2 * d ^ 6 := by ring
      _ ≤ _ := hRank
  have hNpos : 0 < (n : ℝ) := Real.sqrt_pos.mp
    (lt_of_lt_of_le (show 0 < 2000 * c * beta * d ^ 3 by positivity) hRoot)
  have hc2 : 1 ≤ c ^ 2 := by dsimp [c]; nlinarith [sq_nonneg L]
  have hb2 : 1 ≤ beta ^ 2 := by nlinarith
  have hCB : 1 ≤ c ^ 2 * beta ^ 2 := by
    simpa only [one_mul] using mul_le_mul hc2 hb2 (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg c)
  have hX6 : x ^ 2 ≤ d ^ 6 := by
    dsimp [d]
    nlinarith [sq_nonneg x, pow_nonneg hx0 3, pow_nonneg hx0 4,
      pow_nonneg hx0 5, pow_nonneg hx0 6]
  have hXB : x ^ 2 ≤ c ^ 2 * beta ^ 2 * d ^ 6 :=
    hX6.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hCB (pow_nonneg hd.le 6))
  have hN4 : 4 * x ^ 2 ≤ (n : ℝ) := by
    calc
      4 * x ^ 2 ≤ 4 * (c ^ 2 * beta ^ 2 * d ^ 6) :=
        mul_le_mul_of_nonneg_left hXB (by norm_num)
      _ ≤ 4000000 * c ^ 2 * beta ^ 2 * d ^ 6 := by
        have hh : 0 ≤ c ^ 2 * beta ^ 2 * d ^ 6 := by positivity
        nlinarith
      _ ≤ _ := hRank
  have hLc2 : L ≤ c ^ 2 := by dsimp [c]; nlinarith [sq_nonneg L]
  have hLX : L * x ^ 2 ≤ c ^ 2 * d ^ 6 :=
    mul_le_mul hLc2 hX6 (sq_nonneg x) (sq_nonneg c)
  have hN128 : 128 * beta ^ 2 * (L * x ^ 2) ≤ (n : ℝ) := by
    calc
      128 * beta ^ 2 * (L * x ^ 2) ≤ 128 * beta ^ 2 * (c ^ 2 * d ^ 6) :=
        mul_le_mul_of_nonneg_left hLX (by positivity)
      _ ≤ 4000000 * c ^ 2 * beta ^ 2 * d ^ 6 := by
        have hh : 0 ≤ c ^ 2 * beta ^ 2 * d ^ 6 := by positivity
        nlinarith
      _ ≤ _ := hRank
  have hSmallScaled : (128 * s * beta ^ 2) * (n : ℝ) ≤ (n : ℝ) := by
    calc
      (128 * s * beta ^ 2) * (n : ℝ) = (128 * beta ^ 2) * (s * (n : ℝ)) := by ring
      _ ≤ (128 * beta ^ 2) * (L * x ^ 2) :=
        mul_le_mul_of_nonneg_left hTime (by positivity)
      _ ≤ _ := hN128
  have hSmallUnit : 128 * s * beta ^ 2 ≤ 1 := by
    apply (mul_le_mul_iff_of_pos_right hNpos).mp
    simpa only [one_mul] using hSmallScaled
  have hSmall : s * beta ^ 2 ≤ 1 / 128 := by nlinarith
  have hScale : (c * d ^ 2) * (1000 * d * (Real.sqrt (n : ℝ) * (2 * s * beta))) ≤
      s * (n : ℝ) := by
    calc
      _ = (2000 * c * beta * d ^ 3) * (s * Real.sqrt (n : ℝ)) := by ring
      _ ≤ Real.sqrt (n : ℝ) * (s * Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hRoot (mul_nonneg hs (Real.sqrt_nonneg _))
      _ = s * (Real.sqrt (n : ℝ)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  have hLc : L ≤ c := by dsimp [c]; linarith
  have hX2 : x ^ 2 ≤ d ^ 2 := by dsimp [d]; nlinarith
  have hLX2 : L * x ^ 2 ≤ c * d ^ 2 :=
    mul_le_mul hLc hX2 (sq_nonneg x) hc.le
  have hDriftUnit : 1000 * d * (Real.sqrt (n : ℝ) * (2 * s * beta)) ≤ 1 := by
    apply (mul_le_mul_iff_of_pos_left (show 0 < c * d ^ 2 by positivity)).mp
    simpa only [mul_one] using hScale.trans (hTime.trans hLX2)
  have hDrift : Real.sqrt (n : ℝ) * (2 * s * beta) ≤ 1 / (1000 * (1 + x)) := by
    apply (le_div_iff₀ (show 0 < 1000 * (1 + x) by dsimp [d] at hd; positivity)).2
    change (Real.sqrt (n : ℝ) * (2 * s * beta)) * (1000 * d) ≤ 1
    simpa only [mul_comm] using hDriftUnit
  exact ⟨Nat.cast_pos.mp hNpos, hN4, hSmall, hDrift⟩

theorem auxiliary_source_mean_and_weak_event
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (L s : ℝ) (hL : 0 ≤ L) (hs : 0 ≤ s)
    (n : ℕ) (x : ℝ) (hx : 1 ≤ x)
    (hTime : s * (n : ℝ) ≤ L * x ^ 2)
    (hRank : 4000000 * (1 + L) ^ 2 * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 *
      (1 + x) ^ 6 ≤ (n : ℝ)) :
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
    let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
    let mu : ℝ := ∫ z : ℝ, z ∂rho
    let a : ℝ := Real.sqrt ((9 / 4) * x ^ 2 - 1)
    let y : ℝ := a - 1 / (100 * (1 + x))
    0 < n ∧ 4 * x ^ 2 ≤ (n : ℝ) ∧ s * beta ^ 2 ≤ 1 / 128 ∧
      Real.sqrt (n : ℝ) * |mu| ≤ 1 / (1000 * (1 + x)) ∧
      ∀ v : Shao.Path n, (n : ℝ) / 8 ≤ Shao.energy v →
        a * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v n| →
        y * Real.sqrt (Shao.energy (fun i => v i - mu)) ≤
          |Shao.prefixSum (fun i => v i - mu) n| := by
  intro beta rho mu a y
  have hBeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one nu h2 h3 hnorm
  rcases auxiliary_rare_parameter_payment beta L s hBeta hL hs n x hx hTime hRank with
    ⟨hn, hN4, hSmall, hBound⟩
  rcases Shao.C2.AuxiliaryEnergyCentered.auxiliary_energy_tilt_small_parameter
      nu h2 h3 hmean hnorm s hs hSmall with
    ⟨_hRho, _hId, _hCentered, _hZero, _hSquare, _hCube, hMean, _hVarLow, _hVarUp, _hThird⟩
  have hDrift : Real.sqrt (n : ℝ) * |mu| ≤ 1 / (1000 * (1 + x)) :=
    (mul_le_mul_of_nonneg_left hMean (Real.sqrt_nonneg _)).trans hBound
  refine ⟨hn, hN4, hSmall, hDrift, ?_⟩
  intro v hEnergy hCross
  exact Shao.C2.AuxiliarySourceEvent.auxiliary_centered_source_weak_event
    v mu x hx hN4 hEnergy hDrift hCross

end Shao.C2.AuxiliarySourceParameters
