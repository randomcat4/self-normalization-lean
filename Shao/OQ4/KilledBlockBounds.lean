import Shao.OQ4.BoundaryOccupation
import Shao.OQ4.KernelAbsorption

/-! Actual killed blocks and finite D8 from explicit all-time S/AC probabilities. -/

namespace Shao.OQ4

open MeasureTheory

/-- Exactly the all-positive-time closed unit-interval product-law input. -/
def iidIntervalConcentration (ν : Measure ℝ) (β Cq : ℝ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → ∀ x : ℝ,
    (Measure.pi (fun _ : Fin t => ν)).real {a | Shao.prefixSum a t ∈ Set.Icc x (x + 1)} ≤
      Cq * β / Real.sqrt (t : ℝ)

/-- Exactly both all-positive-time, nonnegative-wall product survival inputs. -/
def iidOneSidedSurvival (ν : Measure ℝ) (β Cs : ℝ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → ∀ d : ℝ, 0 ≤ d →
    (Measure.pi (fun _ : Fin t => ν)).real (Shao.closedUpper d) ≤ Cs * (d + β) / Real.sqrt (t : ℝ) ∧
    (Measure.pi (fun _ : Fin t => ν)).real (lowerBlockSurvival d) ≤ Cs * (d + β) / Real.sqrt (t : ℝ)

noncomputable def killedLayerConstant (M Cq Cs : ℝ) : ℝ := 12 * Cq * Cs * M * (1 + M)

noncomputable def killedResidualConstant (M Cq Cs : ℝ) : ℝ :=
  Real.pi ^ 3 * M / 48 + 2 * Real.pi * killedLayerConstant M Cq Cs * (1 + 2 * M)

theorem hsq_block_parameters (h : ℝ) (hh3 : 3 ≤ h) :
    6 ≤ ⌊h ^ 2⌋₊ ∧ 1 ≤ ⌊h ^ 2⌋₊ / 2 ∧ 1 ≤ ⌊h ^ 2⌋₊ - ⌊h ^ 2⌋₊ / 2 ∧
      h ≤ 2 * Real.sqrt (⌊h ^ 2⌋₊ : ℝ) := by
  have hsq : 9 ≤ h ^ 2 := by nlinarith
  have ht := Nat.lt_floor_add_one (h ^ 2)
  have hmreal : (6 : ℝ) ≤ (⌊h ^ 2⌋₊ : ℝ) := by linarith
  have hm : 6 ≤ ⌊h ^ 2⌋₊ := by exact_mod_cast hmreal
  have hmhalf : h ^ 2 ≤ 2 * (⌊h ^ 2⌋₊ : ℝ) := by linarith
  obtain ⟨hl, hr, _⟩ := half_blocks_sqrt_bound ⌊h ^ 2⌋₊ hm
  have hsqrt : h ≤ 2 * Real.sqrt (⌊h ^ 2⌋₊ : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg ⌊h ^ 2⌋₊), Real.sqrt_nonneg (⌊h ^ 2⌋₊ : ℝ)]
  exact ⟨hm, hl, hr, hsqrt⟩

/-- The cosine chord bound is asserted only on the actual closed source interval. -/
theorem principalCosine_depth_lower_bound (h z : ℝ) (hh : 0 < h) (hz : |z| ≤ h) :
    (h - |z|) / h ≤ principalCosine h z := by
  have ha : 0 < Real.pi / (2 * h) := div_pos Real.pi_pos (by positivity)
  have harg : Real.pi / (2 * h) * |z| ≤ Real.pi / 2 := by
    calc
      _ ≤ Real.pi / (2 * h) * h := mul_le_mul_of_nonneg_left hz ha.le
      _ = _ := by field_simp
  have hc := Real.one_sub_mul_le_cos (mul_nonneg ha.le (abs_nonneg z)) harg
  have hleft : 1 - 2 / Real.pi * (Real.pi / (2 * h) * |z|) = (h - |z|) / h := by
    field_simp
  have hright : Real.cos (Real.pi / (2 * h) * |z|) = principalCosine h z := by
    by_cases hz0 : 0 ≤ z
    · simp [principalCosine, abs_of_nonneg hz0]
    · simp [principalCosine, abs_of_neg (lt_of_not_ge hz0)]
  rw [hleft, hright] at hc
  exact hc

variable (ν : Measure ℝ) [IsProbabilityMeasure ν]

/-- Actual kernel layer mass; every required half-block input comes from all-time S/AC. -/
theorem killed_block_layer_bound (h z : ℝ) (hh3 : 3 ≤ h) (hz : |z| ≤ h) (j : ℕ)
    (β M Cq Cs : ℝ) (hβ : 0 ≤ β) (hM : 0 ≤ M) (hβM : β ≤ M)
    (hCq : 0 ≤ Cq) (hCs : 0 ≤ Cs)
    (hAC : iidIntervalConcentration ν β Cq) (hS : iidOneSidedSurvival ν β Cs) :
    (killedIterKernel ν h ⌊h ^ 2⌋₊ z).real (boundaryLayer (fun w : ℝ => h - |w|) j) ≤
      (killedLayerConstant M Cq Cs / h ^ 2) * ((j : ℝ) + 1) := by
  have hp := hsq_block_parameters h hh3
  exact boundary_occupation_hsq_bound ν h z hh3 hz j β M Cq Cs hβ hM hβM hCq hCs
    (hAC _ hp.2.1) (hS _ hp.2.2.1 ((j : ℝ) + 1) (by positivity)).1
    (hS _ hp.2.2.1 ((j : ℝ) + 1) (by positivity)).2

/-- Actual R3, including true residual integrability under the actual kernel row. -/
theorem killed_block_residual_bound (M h Cq Cs : ℝ) (hh3 : 3 ≤ h)
    (hId : Integrable (fun y : ℝ => y) ν)
    (hSq : Integrable (fun y : ℝ => y ^ 2) ν)
    (hCube : Integrable (fun y : ℝ => |y| ^ 3) ν)
    (hmean : (∫ y : ℝ, y ∂ν) = 0) (hsecond : (∫ y : ℝ, y ^ 2 ∂ν) = 1)
    (hM : 0 ≤ M) (hβM : (∫ y : ℝ, |y| ^ 3 ∂ν) ≤ M) (hCq : 0 ≤ Cq) (hCs : 0 ≤ Cs)
    (hAC : iidIntervalConcentration ν (∫ y : ℝ, |y| ^ 3 ∂ν) Cq)
    (hS : iidOneSidedSurvival ν (∫ y : ℝ, |y| ^ 3 ∂ν) Cs)
    (z : ℝ) (hz : |z| ≤ h) :
    Integrable (fun w => |cosineResidual ν (Real.pi / (2 * h)) h w|)
      (killedIterKernel ν h ⌊h ^ 2⌋₊ z) ∧
      killedAction ν h ⌊h ^ 2⌋₊ (fun w => |cosineResidual ν (Real.pi / (2 * h)) h w|) z ≤
        killedResidualConstant M Cq Cs / h ^ 3 := by
  have hh : 0 < h := by linarith
  have hβ0 : 0 ≤ ∫ y : ℝ, |y| ^ 3 ∂ν := integral_nonneg fun y => pow_nonneg (abs_nonneg y) 3
  have hC : 0 ≤ killedLayerConstant M Cq Cs := by unfold killedLayerConstant; positivity
  have hlayers : ∀ j, j < ⌊h⌋₊ + 1 →
      (killedIterKernel ν h ⌊h ^ 2⌋₊ z).real (boundaryLayer (fun w : ℝ => h - |w|) j) ≤
        (killedLayerConstant M Cq Cs / h ^ 2) * ((j : ℝ) + 1) := by
    intro j _hj
    exact killed_block_layer_bound ν h z hh3 hz j _ M Cq Cs hβ0 hM hβM hCq hCs hAC hS
  have ht := averaged_cosine_residual_bound ν (killedIterKernel ν h ⌊h ^ 2⌋₊ z) h
    (killedLayerConstant M Cq Cs) hh hC (killedIterKernel_real_mass_le_one ν h _ z)
    (killedIterKernel_ae_support ν h _ z hz) hId hSq hCube hmean hsecond hlayers
  refine ⟨ht.1, ht.2.2.trans ?_⟩
  apply div_le_div_of_nonneg_right _ (le_of_lt (pow_pos hh 3))
  unfold killedResidualConstant
  exact add_le_add
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hβM (by positivity)) (by norm_num))
    (mul_le_mul_of_nonneg_left (by linarith : 1 + 2 * (∫ y : ℝ, |y| ^ 3 ∂ν) ≤ 1 + 2 * M)
      (by positivity : 0 ≤ 2 * Real.pi * killedLayerConstant M Cq Cs))

/-- Actual R4, paid by a one-sided survival event chosen from the sign of the start. -/
theorem killed_block_mass_bound (h z β M Cs : ℝ) (hh3 : 3 ≤ h) (hz : |z| ≤ h)
    (hβ : 0 ≤ β) (_hM : 0 ≤ M) (hβM : β ≤ M) (hCs : 0 ≤ Cs)
    (hS : iidOneSidedSurvival ν β Cs) :
    killedMass ν h ⌊h ^ 2⌋₊ z ≤ (2 * Cs) * principalCosine h z + (2 * Cs * M) / h := by
  have hh : 0 < h := by linarith
  have hp := hsq_block_parameters h hh3
  have hm : 1 ≤ ⌊h ^ 2⌋₊ := by omega
  have hd : 0 ≤ h - |z| := sub_nonneg.mpr hz
  have hs := hS ⌊h ^ 2⌋₊ hm (h - |z|) hd
  have hraw : killedMass ν h ⌊h ^ 2⌋₊ z ≤
      Cs * (h - |z| + β) / Real.sqrt (⌊h ^ 2⌋₊ : ℝ) := by
    rw [killedMass_eq_path_probability]
    by_cases hz0 : 0 ≤ z
    · apply (measureReal_mono (show shiftedClosedSurvival (n := ⌊h ^ 2⌋₊) h z ⊆
          Shao.closedUpper (h - |z|) from ?_)).trans hs.1
      intro a ha k hkn
      by_cases hk : k = 0
      · simpa [hk] using hd
      · have ht := (abs_le.mp (ha k (by omega) hkn)).2
        rw [abs_of_nonneg hz0]
        linarith
    · apply (measureReal_mono (show shiftedClosedSurvival (n := ⌊h ^ 2⌋₊) h z ⊆
          lowerBlockSurvival (h - |z|) from ?_)).trans hs.2
      intro a ha k hkn
      rw [Shao.prefixSum_neg]
      by_cases hk : k = 0
      · simpa [hk] using hd
      · have ht := (abs_le.mp (ha k (by omega) hkn)).1
        rw [abs_of_neg (lt_of_not_ge hz0)]
        linarith
  have hroot : 0 < Real.sqrt (⌊h ^ 2⌋₊ : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < ⌊h ^ 2⌋₊ by omega))
  have hnum : 0 ≤ Cs * (h - |z| + β) := mul_nonneg hCs (add_nonneg hd hβ)
  calc
    _ ≤ Cs * (h - |z| + β) / Real.sqrt (⌊h ^ 2⌋₊ : ℝ) := hraw
    _ ≤ 2 * Cs * (h - |z| + β) / h := by
      apply (div_le_div_iff₀ hroot hh).2
      convert mul_le_mul_of_nonneg_left hp.2.2.2 hnum using 1; ring
    _ = (2 * Cs) * ((h - |z|) / h) + (2 * Cs) * β / h := by ring
    _ ≤ (2 * Cs) * principalCosine h z + (2 * Cs) * M / h :=
      add_le_add (mul_le_mul_of_nonneg_left (principalCosine_depth_lower_bound h z hh hz) (by positivity))
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hβM (by positivity)) hh.le)
    _ = _ := by ring

/-- Finite D8 from S/AC and moments; R3/R4 are supplied by the preceding actual block results. -/
theorem killed_block_finite_absorption (M h Cq Cs : ℝ) (hh3 : 3 ≤ h)
    (hId : Integrable (fun y : ℝ => y) ν)
    (hSq : Integrable (fun y : ℝ => y ^ 2) ν)
    (hCube : Integrable (fun y : ℝ => |y| ^ 3) ν)
    (hmean : (∫ y : ℝ, y ∂ν) = 0) (hsecond : (∫ y : ℝ, y ^ 2 ∂ν) = 1)
    (hM : 0 ≤ M) (hβM : (∫ y : ℝ, |y| ^ 3 ∂ν) ≤ M) (hCq : 0 ≤ Cq) (hCs : 0 ≤ Cs)
    (hAC : iidIntervalConcentration ν (∫ y : ℝ, |y| ^ 3 ∂ν) Cq)
    (hS : iidOneSidedSurvival ν (∫ y : ℝ, |y| ^ 3 ∂ν) Cs)
    (hlarge : Real.pi * (1 + M) ≤ h) (N : ℕ) (hmN : ⌊h ^ 2⌋₊ ≤ N)
    (hsmall : ((2 * Cs) * Real.exp (Real.pi ^ 2)) *
      (killedResidualConstant M Cq Cs * Real.exp (Real.pi ^ 2) / h ^ 3) * (N : ℝ) +
      (2 * Cs * M) * Real.exp (Real.pi ^ 2) / h ≤ (1 / 2 : ℝ))
    (z : ℝ) (hz : |z| ≤ h) :
    let R : ℝ := Real.exp (Real.pi ^ 2)
    let H : ℝ := 2 * (1 + (2 * Cs) * R) * R
    (∀ k, k ≤ N → 0 ≤ normalizedKernelMass ν h k z ∧ normalizedKernelMass ν h k z ≤ H) ∧
      (∀ k, ⌊h ^ 2⌋₊ ≤ k → k ≤ N →
        |normalizedKernelCosine ν h k z - normalizedKernelCosine ν h ⌊h ^ 2⌋₊ z| ≤
          (killedResidualConstant M Cq Cs * R / h ^ 3) * ((k - ⌊h ^ 2⌋₊ : ℕ) : ℝ) * H) := by
  have hβ0 : 0 ≤ ∫ y : ℝ, |y| ^ 3 ∂ν := integral_nonneg fun y => pow_nonneg (abs_nonneg y) 3
  have hE : 0 ≤ killedResidualConstant M Cq Cs := by
    unfold killedResidualConstant killedLayerConstant
    positivity
  exact kernel_finite_absorption ν M h hId hSq hCube hmean hsecond hM hβM (by linarith) hlarge
    N hmN z hz (2 * Cs) (2 * Cs * M) (killedResidualConstant M Cq Cs)
    (by positivity) (by positivity) hE
    (fun w hw => (killed_block_residual_bound ν M h Cq Cs hh3 hId hSq hCube hmean hsecond
      hM hβM hCq hCs hAC hS w hw).2)
    (fun w hw => killed_block_mass_bound ν h w _ M Cs hh3 hw hβ0 hM hβM hCs hS) hsmall

end Shao.OQ4
