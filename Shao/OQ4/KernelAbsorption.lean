import Shao.OQ4.KernelRecurrence
import Shao.OQ4.CosinePowers
import Shao.OQ4.DelayedRecurrence

/-! Conditional finite absorption from actual killed-kernel block inputs. -/

namespace Shao.OQ4

open MeasureTheory

/-- The actual finite D8 bridge, retaining both independent block hypotheses. -/
theorem kernel_finite_absorption (ν : Measure ℝ) [IsProbabilityMeasure ν] (M h : ℝ)
    (hId : Integrable (fun y : ℝ => y) ν)
    (hSq : Integrable (fun y : ℝ => y ^ 2) ν)
    (hCube : Integrable (fun y : ℝ => |y| ^ 3) ν)
    (hmean : (∫ y : ℝ, y ∂ν) = 0) (hsecond : (∫ y : ℝ, y ^ 2 ∂ν) = 1)
    (hM : 0 ≤ M) (hβ : (∫ y : ℝ, |y| ^ 3 ∂ν) ≤ M)
    (hh1 : 1 ≤ h) (hlarge : Real.pi * (1 + M) ≤ h)
    (N : ℕ) (hmN : ⌊h ^ 2⌋₊ ≤ N) (z : ℝ) (hz : |z| ≤ h)
    (A B E : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hresblock : ∀ w, |w| ≤ h →
      killedAction ν h ⌊h ^ 2⌋₊ (fun v => |cosineResidual ν (Real.pi / (2 * h)) h v|) w ≤ E / h ^ 3)
    (hmassblock : ∀ w, |w| ≤ h →
      killedMass ν h ⌊h ^ 2⌋₊ w ≤ A * principalCosine h w + B / h)
    (hsmall : (A * Real.exp (Real.pi ^ 2)) * (E * Real.exp (Real.pi ^ 2) / h ^ 3) * (N : ℝ) +
      B * Real.exp (Real.pi ^ 2) / h ≤ (1 / 2 : ℝ)) :
    let R : ℝ := Real.exp (Real.pi ^ 2)
    let H : ℝ := 2 * (1 + A * R) * R
    (∀ k, k ≤ N → 0 ≤ normalizedKernelMass ν h k z ∧ normalizedKernelMass ν h k z ≤ H) ∧
      (∀ k, ⌊h ^ 2⌋₊ ≤ k → k ≤ N →
        |normalizedKernelCosine ν h k z - normalizedKernelCosine ν h ⌊h ^ 2⌋₊ z| ≤
          (E * R / h ^ 3) * ((k - ⌊h ^ 2⌋₊ : ℕ) : ℝ) * H) := by
  let m : ℕ := ⌊h ^ 2⌋₊
  let R : ℝ := Real.exp (Real.pi ^ 2)
  let f : ℕ → ℝ := fun k => normalizedKernelCosine ν h k z
  let g : ℕ → ℝ := fun k => normalizedKernelMass ν h k z
  have hh : 0 < h := by linarith
  have hR : 0 < R := Real.exp_pos _
  have hsq : 1 ≤ h ^ 2 := by nlinarith
  have hmreal : (m : ℝ) ≤ h ^ 2 := Nat.floor_le (sq_nonneg h)
  have hm : 1 ≤ m := by
    have ht := Nat.lt_floor_add_one (h ^ 2)
    have hmposreal : 0 < (m : ℝ) := by dsimp [m]; linarith
    have hmpos : 0 < m := by exact_mod_cast hmposreal
    omega
  have hb := cosineCoefficient_large_h_bounds ν M h hId hSq hCube hmean hsecond hM hβ hh1 hlarge
  have hρ : 0 < principalRate ν h := by
    change 0 < cosineCoefficient ν (Real.pi / (2 * h))
    linarith [hb.2.2.1]
  have hρ1 : principalRate ν h ≤ 1 := hb.2.2.2.le
  have hfloor : (principalRate ν h ^ (m + 1))⁻¹ ≤ R ∧
      (principalRate ν h ^ (2 * m))⁻¹ ≤ R := by
    simpa only [principalRate, m, R] using
      cosineCoefficient_floor_inverse_bounds ν M h hId hSq hCube hmean hsecond hM hβ hh1 hlarge
  have hminv : (principalRate ν h ^ m)⁻¹ ≤ R := by
    exact cosineCoefficient_inverse_pow_uniform ν M h hId hSq hCube hmean hsecond hM hβ hh1 hlarge
      m (by nlinarith [sq_nonneg h])
  have hg0 (k : ℕ) : 0 ≤ g k := normalizedKernelMass_nonneg ν h hρ k z
  have hf0 (k : ℕ) : 0 ≤ f k := normalizedKernelCosine_nonneg ν h hh hρ k z hz
  have hinit : ∀ k, k ≤ N → k ≤ 2 * m → g k ≤ R := by
    intro k _hkN hk
    exact (normalizedKernelMass_finite_bound ν h hρ hρ1 m k hk z).trans hfloor.2
  have hfm : f m ≤ R := by
    have hfg : f m ≤ g m :=
      mul_le_mul_of_nonneg_left (kernelCosine_bounds ν h hh m z hz).2.1
        (le_of_lt (inv_pos.mpr (pow_pos hρ m)))
    exact hfg.trans (hinit m hmN (by omega))
  have hincrement : ∀ k, m ≤ k → k < N →
      |f (k + 1) - f k| ≤ (E * R / h ^ 3) * g (k - m) := by
    intro k hmk _hkN
    have hi := normalizedKernelCosine_delayed ν h hh hρ m k hmk z hz
      (E / h ^ 3) (by positivity) hresblock
    have hc : (E / h ^ 3) * (principalRate ν h ^ (m + 1))⁻¹ ≤ E * R / h ^ 3 := by
      calc
        _ ≤ (E / h ^ 3) * R := mul_le_mul_of_nonneg_left hfloor.1 (by positivity)
        _ = _ := by ring
    exact hi.trans (mul_le_mul_of_nonneg_right hc (hg0 (k - m)))
  have hdelay : ∀ k, k + m ≤ N →
      g (k + m) ≤ (A * R) * f k + (B * R / h) * g k := by
    intro k _hkN
    have hi := normalizedKernelMass_block ν h hh hρ m k z hz A (B / h) hA (by positivity) hmassblock
    have hcA : A * (principalRate ν h ^ m)⁻¹ ≤ A * R :=
      mul_le_mul_of_nonneg_left hminv hA
    have hcB : (B / h) * (principalRate ν h ^ m)⁻¹ ≤ B * R / h := by
      calc
        _ ≤ (B / h) * R := mul_le_mul_of_nonneg_left hminv (by positivity)
        _ = _ := by ring
    exact hi.trans (add_le_add (mul_le_mul_of_nonneg_right hcA (hf0 k))
      (mul_le_mul_of_nonneg_right hcB (hg0 k)))
  have hs := delayed_recurrence_bound f g m N (A * R) (B * R / h) (E * R / h ^ 3) R
    hm hmN (by positivity) (by positivity) (by positivity) (le_of_lt hR)
    (fun k _hk => hg0 k) hinit hfm hincrement hdelay hsmall
  change (∀ k, k ≤ N → 0 ≤ g k ∧ g k ≤ 2 * (1 + A * R) * R) ∧
    (∀ k, m ≤ k → k ≤ N → |f k - f m| ≤
      (E * R / h ^ 3) * ((k - m : ℕ) : ℝ) * (2 * (1 + A * R) * R))
  exact ⟨fun k hk => ⟨hg0 k, hs.1 k hk⟩, hs.2⟩

end Shao.OQ4
