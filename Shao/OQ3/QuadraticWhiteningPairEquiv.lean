import Shao.OQ3.QuadraticWhiteningSpectralData
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace Shao.OQ3
open scoped Matrix Topology
noncomputable section

theorem matrix_pair_continuous_linear_equiv_of_inverse
    (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    let F : Matrix (Fin 2) (Fin 2) ℝ → (ℝ × ℝ) → (ℝ × ℝ) := fun M w =>
      (M 0 0 * w.1 + M 0 1 * w.2, M 1 0 * w.1 + M 1 1 * w.2)
    ∃ E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      (E : (ℝ × ℝ) → (ℝ × ℝ)) = F A ∧
      (E.symm : (ℝ × ℝ) → (ℝ × ℝ)) = F B ∧
      (∀ c : ℝ, 0 ≤ c → (∀ i j : Fin 2, |A i j| ≤ c) →
        ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 2 * c) ∧
      (∀ c : ℝ, 0 ≤ c → (∀ i j : Fin 2, |B i j| ≤ c) →
        ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 2 * c) := by
  classical
  let F : Matrix (Fin 2) (Fin 2) ℝ → (ℝ × ℝ) → (ℝ × ℝ) := fun M w =>
    (M 0 0 * w.1 + M 0 1 * w.2, M 1 0 * w.1 + M 1 1 * w.2)
  change ∃ E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
    (E : (ℝ × ℝ) → (ℝ × ℝ)) = F A ∧
    (E.symm : (ℝ × ℝ) → (ℝ × ℝ)) = F B ∧
    (∀ c : ℝ, 0 ≤ c → (∀ i j : Fin 2, |A i j| ≤ c) →
      ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 2 * c) ∧
    (∀ c : ℝ, 0 ≤ c → (∀ i j : Fin 2, |B i j| ≤ c) →
      ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 2 * c)
  have hcompose (M N : Matrix (Fin 2) (Fin 2) ℝ) (w : ℝ × ℝ) :
      F M (F N w) = F (M * N) w := by
    apply Prod.ext
    · simp only [F, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    · simp only [F, Matrix.mul_apply, Fin.sum_univ_two]
      ring
  have hid (w : ℝ × ℝ) : F (1 : Matrix (Fin 2) (Fin 2) ℝ) w = w := by
    apply Prod.ext <;> simp [F]
  let e : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := F A
      invFun := F B
      left_inv := by intro w; rw [hcompose, hBA]; exact hid w
      right_inv := by intro w; rw [hcompose, hAB]; exact hid w
      map_add' := by
        intro w z
        apply Prod.ext
        · change A 0 0 * (w.1 + z.1) + A 0 1 * (w.2 + z.2) =
            (A 0 0 * w.1 + A 0 1 * w.2) + (A 0 0 * z.1 + A 0 1 * z.2)
          ring
        · change A 1 0 * (w.1 + z.1) + A 1 1 * (w.2 + z.2) =
            (A 1 0 * w.1 + A 1 1 * w.2) + (A 1 0 * z.1 + A 1 1 * z.2)
          ring
      map_smul' := by
        intro c w
        apply Prod.ext
        · change A 0 0 * (c * w.1) + A 0 1 * (c * w.2) =
            c * (A 0 0 * w.1 + A 0 1 * w.2)
          ring
        · change A 1 0 * (c * w.1) + A 1 1 * (c * w.2) =
            c * (A 1 0 * w.1 + A 1 1 * w.2)
          ring }
  let E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) := e.toContinuousLinearEquiv
  have hbound (M : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) (hc : 0 ≤ c)
      (hM : ∀ i j : Fin 2, |M i j| ≤ c) (w : ℝ × ℝ) :
      ‖F M w‖ ≤ (2 * c) * ‖w‖ := by
    have hx0 : |w.1| ≤ ‖w‖ := by
      change |w.1| ≤ max |w.1| |w.2|
      exact le_max_left _ _
    have hx1 : |w.2| ≤ ‖w‖ := by
      change |w.2| ≤ max |w.1| |w.2|
      exact le_max_right _ _
    have hrow (i : Fin 2) :
        |M i 0 * w.1 + M i 1 * w.2| ≤ (2 * c) * ‖w‖ := by
      calc
        |M i 0 * w.1 + M i 1 * w.2| ≤ |M i 0 * w.1| + |M i 1 * w.2| :=
          abs_add_le _ _
        _ = |M i 0| * |w.1| + |M i 1| * |w.2| := by rw [abs_mul, abs_mul]
        _ ≤ c * ‖w‖ + c * ‖w‖ := add_le_add
          (mul_le_mul (hM i 0) hx0 (abs_nonneg _) hc)
          (mul_le_mul (hM i 1) hx1 (abs_nonneg _) hc)
        _ = (2 * c) * ‖w‖ := by ring
    change max |M 0 0 * w.1 + M 0 1 * w.2|
      |M 1 0 * w.1 + M 1 1 * w.2| ≤ (2 * c) * ‖w‖
    exact max_le (hrow 0) (hrow 1)
  refine ⟨E, rfl, rfl, ?_, ?_⟩
  · intro c hc hA
    apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
    intro w
    change ‖F A w‖ ≤ (2 * c) * ‖w‖
    exact hbound A c hc hA w
  · intro c hc hB
    apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
    intro w
    change ‖F B w‖ ≤ (2 * c) * ‖w‖
    exact hbound B c hc hB w

theorem quadratic_whitening_pair_equiv
    (D : Matrix (Fin 2) (Fin 2) ℝ) (hsym : D 1 0 = D 0 1)
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (hspec : ∀ xi eta : ℝ,
      lo * (xi ^ 2 + eta ^ 2) ≤
        xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ∧
      xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ≤
        hi * (xi ^ 2 + eta ^ 2)) :
    let s : ℝ := Real.sqrt (D 0 0 * D 1 1 - (D 0 1) ^ 2)
    let t : ℝ := Real.sqrt (D 0 0 + D 1 1 + 2 * s)
    let A : Matrix (Fin 2) (Fin 2) ℝ :=
      ![![(D 1 1 + s) / (s * t), -(D 0 1) / (s * t)],
        ![-(D 0 1) / (s * t), (D 0 0 + s) / (s * t)]]
    let B : Matrix (Fin 2) (Fin 2) ℝ := D * A
    A * D * A = 1 ∧
      ∃ E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
        (∀ w : ℝ × ℝ, E w =
          (A 0 0 * w.1 + A 0 1 * w.2, A 1 0 * w.1 + A 1 1 * w.2)) ∧
        (∀ w : ℝ × ℝ, E.symm w =
          (B 0 0 * w.1 + B 0 1 * w.2, B 1 0 * w.1 + B 1 1 * w.2)) ∧
        ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 2 * (1 / Real.sqrt lo) ∧
        ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤
          4 * hi * (1 / Real.sqrt lo) := by
  classical
  let s : ℝ := Real.sqrt (D 0 0 * D 1 1 - (D 0 1) ^ 2)
  let t : ℝ := Real.sqrt (D 0 0 + D 1 1 + 2 * s)
  let A : Matrix (Fin 2) (Fin 2) ℝ :=
    ![![(D 1 1 + s) / (s * t), -(D 0 1) / (s * t)],
      ![-(D 0 1) / (s * t), (D 0 0 + s) / (s * t)]]
  let B : Matrix (Fin 2) (Fin 2) ℝ := D * A
  change A * D * A = 1 ∧ ∃ E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
    (∀ w : ℝ × ℝ, E w =
      (A 0 0 * w.1 + A 0 1 * w.2, A 1 0 * w.1 + A 1 1 * w.2)) ∧
    (∀ w : ℝ × ℝ, E.symm w =
      (B 0 0 * w.1 + B 0 1 * w.2, B 1 0 * w.1 + B 1 1 * w.2)) ∧
    ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 2 * (1 / Real.sqrt lo) ∧
    ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 4 * hi * (1 / Real.sqrt lo)
  obtain ⟨hs, ht, hAsym, hADA, hpos, hfreq, hAentry⟩ :=
    quadratic_whitening_spectral_data D hsym lo hi hlo hhi hspec
  have hAB : A * B = 1 := by
    change A * (D * A) = 1
    rw [← Matrix.mul_assoc]
    exact hADA
  have hBA : B * A = 1 := mul_eq_one_comm.mp hAB
  have hd0 := hspec 1 0
  have hd1 := hspec 0 1
  have hp := hspec 1 1
  have hm := hspec 1 (-1)
  norm_num at hd0 hd1 hp hm
  have hD01 : |D 0 1| ≤ hi := abs_le.mpr
    ⟨by linarith [hd0.1, hd1.1, hm.2], by linarith [hd0.1, hd1.1, hp.2]⟩
  have hDentry : ∀ i j : Fin 2, |D i j| ≤ hi := by
    intro i j
    fin_cases i <;> fin_cases j
    · change |D 0 0| ≤ hi
      exact abs_le.mpr ⟨by linarith [hd0.1], hd0.2⟩
    · change |D 0 1| ≤ hi
      exact hD01
    · change |D 1 0| ≤ hi
      simpa only [hsym] using hD01
    · change |D 1 1| ≤ hi
      exact abs_le.mpr ⟨by linarith [hd1.1], hd1.2⟩
  let U : ℝ := 1 / Real.sqrt lo
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hBentry : ∀ i j : Fin 2, |B i j| ≤ 2 * hi * U := by
    intro i j
    change |(D * A) i j| ≤ 2 * hi * U
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    calc
      |D i 0 * A 0 j + D i 1 * A 1 j| ≤
          |D i 0 * A 0 j| + |D i 1 * A 1 j| := abs_add_le _ _
      _ = |D i 0| * |A 0 j| + |D i 1| * |A 1 j| := by rw [abs_mul, abs_mul]
      _ ≤ hi * U + hi * U := add_le_add
        (mul_le_mul (hDentry i 0) (hAentry 0 j) (abs_nonneg _) hhi.le)
        (mul_le_mul (hDentry i 1) (hAentry 1 j) (abs_nonneg _) hhi.le)
      _ = 2 * hi * U := by ring
  obtain ⟨E, hEA, hEB, hEbound, hInvBound⟩ :=
    matrix_pair_continuous_linear_equiv_of_inverse A B hAB hBA
  refine ⟨hADA, E, ?_, ?_, hEbound U hU hAentry, ?_⟩
  · intro w
    exact congrFun hEA w
  · intro w
    exact congrFun hEB w
  · have hbound := hInvBound (2 * hi * U) (by positivity) hBentry
    calc
      ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 2 * (2 * hi * U) := hbound
      _ = 4 * hi * (1 / Real.sqrt lo) := by dsimp only [U]; ring

end
end Shao.OQ3
