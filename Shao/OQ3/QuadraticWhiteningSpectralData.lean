import Shao.OQ3.CovarianceWhitening

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix BigOperators
noncomputable section

/-- Numeric positive symmetric whitening argument reproduced from the accepted
private proof in CovarianceWhitening.lean (curated source SHA256 d1f90abf2ecd59032dc5f934dbedbe9c3ab9e468f73b0d4f40b24b4a7851eec8).
Original scope: R2report53–59,83–92. This exports the complete checked matrix interface
for the generic actual-law consumer and additionally proves uniform entry bounds. -/
private theorem open_domain_whitening_algebra
    (D : Matrix (Fin 2) (Fin 2) ℝ) (hsym : D 1 0 = D 0 1)
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (hspec : ∀ xi eta : ℝ,
      lo * (xi ^ 2 + eta ^ 2) ≤
        xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ∧
      xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ≤
        hi * (xi ^ 2 + eta ^ 2)) :
    let s := Real.sqrt (D 0 0 * D 1 1 - (D 0 1) ^ 2)
    let t := Real.sqrt (D 0 0 + D 1 1 + 2 * s)
    let A : Matrix (Fin 2) (Fin 2) ℝ :=
      ![![(D 1 1 + s) / (s * t), -(D 0 1) / (s * t)],
        ![-(D 0 1) / (s * t), (D 0 0 + s) / (s * t)]]
    0 < s ∧ 0 < t ∧ Aᵀ = A ∧ A * D * A = 1 ∧
      (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
        0 < xi * (A *ᵥ ![xi, eta]) 0 + eta * (A *ᵥ ![xi, eta]) 1) ∧
      ∀ xi eta : ℝ,
        (1 / Real.sqrt hi) * Real.sqrt (xi ^ 2 + eta ^ 2) ≤
          Real.sqrt ((xi * A 0 0 + eta * A 1 0) ^ 2 +
            (xi * A 0 1 + eta * A 1 1) ^ 2) ∧
        Real.sqrt ((xi * A 0 0 + eta * A 1 0) ^ 2 +
            (xi * A 0 1 + eta * A 1 1) ^ 2) ≤
          (1 / Real.sqrt lo) * Real.sqrt (xi ^ 2 + eta ^ 2) := by
  let a := D 0 0
  let b := D 0 1
  let d := D 1 1
  let delta := a * d - b ^ 2
  let s := Real.sqrt delta
  let t := Real.sqrt (a + d + 2 * s)
  let den := s * t
  let N : Matrix (Fin 2) (Fin 2) ℝ := ![![d + s, -b], ![-b, a + s]]
  let A : Matrix (Fin 2) (Fin 2) ℝ :=
    ![![(d + s) / den, -b / den], ![-b / den, (a + s) / den]]
  have ha : 0 < a := by
    have h := (hspec 1 0).1
    norm_num at h
    exact lt_of_lt_of_le hlo h
  have hd : 0 < d := by
    have h := (hspec 0 1).1
    norm_num at h
    exact lt_of_lt_of_le hlo h
  have hdelta : 0 < delta := by
    have h := (hspec (-b) a).1
    have hnorm : 0 < b ^ 2 + a ^ 2 := by nlinarith [sq_pos_of_pos ha, sq_nonneg b]
    have hprod : 0 < a * delta := by
      have hpos := mul_pos hlo hnorm
      dsimp [delta]
      nlinarith only [h, hpos]
    exact (mul_pos_iff.mp hprod).resolve_right (by rintro ⟨hn, _⟩; linarith)
      |>.2
  have hs : 0 < s := Real.sqrt_pos.2 hdelta
  have htarg : 0 < a + d + 2 * s := by positivity
  have ht : 0 < t := Real.sqrt_pos.2 htarg
  have hs2 : s ^ 2 = delta := Real.sq_sqrt hdelta.le
  have ht2 : t ^ 2 = a + d + 2 * s := Real.sq_sqrt htarg.le
  have hden : den ≠ 0 := ne_of_gt (mul_pos hs ht)
  have hD : D = ![![a, b], ![b, d]] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a, b, d, hsym]
  have hnum00 : ((d + s) * a + (-b) * b) * (d + s) +
      ((d + s) * b + (-b) * d) * (-b) = (s * t) ^ 2 := by
    calc
      _ = (a - t ^ 2) * (s ^ 2 - delta) -
          delta * (t ^ 2 - (a + d + 2 * s)) + (s * t) ^ 2 := by dsimp [delta]; ring
      _ = (s * t) ^ 2 := by rw [hs2, ht2]; ring
  have hnum01 : ((d + s) * a + (-b) * b) * (-b) +
      ((d + s) * b + (-b) * d) * (a + s) = 0 := by
    calc
      _ = b * (s ^ 2 - delta) := by dsimp [delta]; ring
      _ = 0 := by rw [hs2]; ring
  have hnum10 : ((-b) * a + (a + s) * b) * (d + s) +
      ((-b) * b + (a + s) * d) * (-b) = 0 := by
    calc
      _ = b * (s ^ 2 - delta) := by dsimp [delta]; ring
      _ = 0 := by rw [hs2]; ring
  have hnum11 : ((-b) * a + (a + s) * b) * (-b) +
      ((-b) * b + (a + s) * d) * (a + s) = (s * t) ^ 2 := by
    calc
      _ = (d - t ^ 2) * (s ^ 2 - delta) -
          delta * (t ^ 2 - (a + d + 2 * s)) + (s * t) ^ 2 := by dsimp [delta]; ring
      _ = (s * t) ^ 2 := by rw [hs2, ht2]; ring
  have hN : N * D * N = (s * t) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    change (∑ k : Fin 2, (∑ l : Fin 2, N i l * D l k) * N k j) =
      (s * t) ^ 2 * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j
    simp only [Fin.sum_univ_two]
    fin_cases i <;> fin_cases j
    · simpa [N, a, b, d, hsym] using hnum00
    · simpa [N, a, b, d, hsym] using hnum01
    · simpa [N, a, b, d, hsym] using hnum10
    · simpa [N, a, b, d, hsym] using hnum11
  have hA : A = den⁻¹ • N := by
    ext i j
    change A i j = den⁻¹ * N i j
    fin_cases i <;> fin_cases j <;> simp [A, N, div_eq_mul_inv, mul_comm]
  have hAsym : Aᵀ = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hcoef : den⁻¹ * den⁻¹ * den ^ 2 = 1 := by field_simp [hden]
  have hwhite : A * D * A = 1 := by
    calc
      _ = (den⁻¹ * den⁻¹ * den ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
        rw [hA]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hN, den, mul_assoc]
      _ = 1 := by rw [hcoef, one_smul]
  have hpositive : ∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
      0 < xi * (A *ᵥ ![xi, eta]) 0 + eta * (A *ᵥ ![xi, eta]) 1 := by
    intro xi eta hne
    have hr : 0 < xi ^ 2 + eta ^ 2 := by
      rcases hne with hx | hy
      · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg eta]
      · nlinarith [sq_pos_of_ne_zero hy, sq_nonneg xi]
    have hrot := (hspec (-eta) xi).1
    have hq : 0 < a * eta ^ 2 - 2 * b * xi * eta + d * xi ^ 2 := by
      have hp := mul_pos hlo hr
      dsimp [a, b, d]
      nlinarith only [hrot, hp]
    have hid : xi * (A *ᵥ ![xi, eta]) 0 + eta * (A *ᵥ ![xi, eta]) 1 =
        (s * (xi ^ 2 + eta ^ 2) +
          (a * eta ^ 2 - 2 * b * xi * eta + d * xi ^ 2)) / den := by
      simp only [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp [hden]
      <;> ring
    rw [hid]
    exact div_pos (add_pos (mul_pos hs hr) hq) (mul_pos hs ht)
  have hquad (xi eta : ℝ) :
      let v : Fin 2 → ℝ := Aᵀ *ᵥ ![xi, eta]
      (v 0) ^ 2 * a + 2 * v 0 * v 1 * b + (v 1) ^ 2 * d = xi ^ 2 + eta ^ 2 := by
    let u : Fin 2 → ℝ := ![xi, eta]
    have hh : dotProduct (Aᵀ *ᵥ u) (D *ᵥ (Aᵀ *ᵥ u)) = dotProduct u u := by
      rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec,
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAsym, hwhite, Matrix.one_mulVec]
    rw [hD] at hh
    dsimp only [u] at hh
    dsimp only
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at hh ⊢
    nlinarith only [hh]
  change 0 < s ∧ 0 < t ∧ Aᵀ = A ∧ A * D * A = 1 ∧
    (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
      0 < xi * (A *ᵥ ![xi, eta]) 0 + eta * (A *ᵥ ![xi, eta]) 1) ∧ _
  refine ⟨hs, ht, hAsym, hwhite, hpositive, ?_⟩
  intro xi eta
  let v : Fin 2 → ℝ := Aᵀ *ᵥ ![xi, eta]
  let r := Real.sqrt (xi ^ 2 + eta ^ 2)
  let rA := Real.sqrt ((v 0) ^ 2 + (v 1) ^ 2)
  have hv0 : v 0 = xi * A 0 0 + eta * A 1 0 := by
    simp [v, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  have hv1 : v 1 = xi * A 0 1 + eta * A 1 1 := by
    simp [v, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  have hq := hquad xi eta
  have hl := (hspec (v 0) (v 1)).1
  have hu := (hspec (v 0) (v 1)).2
  change lo * ((v 0) ^ 2 + (v 1) ^ 2) ≤
    (v 0) ^ 2 * a + 2 * v 0 * v 1 * b + (v 1) ^ 2 * d at hl
  change (v 0) ^ 2 * a + 2 * v 0 * v 1 * b + (v 1) ^ 2 * d ≤
    hi * ((v 0) ^ 2 + (v 1) ^ 2) at hu
  rw [hq] at hl hu
  have hr2 : r ^ 2 = xi ^ 2 + eta ^ 2 := Real.sq_sqrt (by positivity)
  have hrA2 : rA ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := Real.sq_sqrt (by positivity)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrA : 0 ≤ rA := Real.sqrt_nonneg _
  have hslo : 0 < Real.sqrt lo := Real.sqrt_pos.2 hlo
  have hshi : 0 < Real.sqrt hi := Real.sqrt_pos.2 hhi
  have hlow : r ≤ Real.sqrt hi * rA := by
    apply (sq_le_sq₀ hr (mul_nonneg hshi.le hrA)).mp
    rw [mul_pow, Real.sq_sqrt hhi.le, hrA2, hr2]
    exact hu
  have hupp : Real.sqrt lo * rA ≤ r := by
    apply (sq_le_sq₀ (mul_nonneg hslo.le hrA) hr).mp
    rw [mul_pow, Real.sq_sqrt hlo.le, hrA2, hr2]
    exact hl
  have hL : (1 / Real.sqrt hi) * r ≤ rA := by
    calc
      _ = r / Real.sqrt hi := by ring
      _ ≤ rA := (div_le_iff₀ hshi).mpr (by simpa [mul_comm] using hlow)
  have hU : rA ≤ (1 / Real.sqrt lo) * r := by
    calc
      _ ≤ r / Real.sqrt lo := (le_div_iff₀ hslo).mpr (by simpa [mul_comm] using hupp)
      _ = _ := by ring
  simpa only [r, rA, hv0, hv1] using And.intro hL hU

theorem quadratic_whitening_spectral_data
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
    0 < s ∧ 0 < t ∧ Aᵀ = A ∧ A * D * A = 1 ∧
      (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
        0 < xi * (A *ᵥ ![xi, eta]) 0 + eta * (A *ᵥ ![xi, eta]) 1) ∧
      (∀ xi eta : ℝ,
        (1 / Real.sqrt hi) * Real.sqrt (xi ^ 2 + eta ^ 2) ≤
          Real.sqrt ((xi * A 0 0 + eta * A 1 0) ^ 2 +
            (xi * A 0 1 + eta * A 1 1) ^ 2) ∧
        Real.sqrt ((xi * A 0 0 + eta * A 1 0) ^ 2 +
            (xi * A 0 1 + eta * A 1 1) ^ 2) ≤
          (1 / Real.sqrt lo) * Real.sqrt (xi ^ 2 + eta ^ 2)) ∧
      ∀ i j : Fin 2, |A i j| ≤ 1 / Real.sqrt lo := by
  let s : ℝ := Real.sqrt (D 0 0 * D 1 1 - (D 0 1) ^ 2)
  let t : ℝ := Real.sqrt (D 0 0 + D 1 1 + 2 * s)
  let A : Matrix (Fin 2) (Fin 2) ℝ :=
    ![![(D 1 1 + s) / (s * t), -(D 0 1) / (s * t)],
      ![-(D 0 1) / (s * t), (D 0 0 + s) / (s * t)]]
  let U : ℝ := 1 / Real.sqrt lo
  obtain ⟨hs, ht, hAsym, hwhite, hpositive, hfrequency⟩ :=
    open_domain_whitening_algebra D hsym lo hi hlo hhi hspec
  refine ⟨hs, ht, hAsym, hwhite, hpositive, hfrequency, ?_⟩
  have hU : 0 < U := one_div_pos.mpr (Real.sqrt_pos.mpr hlo)
  have hrow (i : Fin 2) : Real.sqrt ((A i 0) ^ 2 + (A i 1) ^ 2) ≤ U := by
    fin_cases i
    · simpa [A, s, t, U] using (hfrequency 1 0).2
    · simpa [A, s, t, U] using (hfrequency 0 1).2
  intro i j
  have hh := (sq_le_sq₀ (Real.sqrt_nonneg _) hU.le).2 (hrow i)
  rw [Real.sq_sqrt (by positivity)] at hh
  apply (sq_le_sq₀ (abs_nonneg _) hU.le).mp
  rw [sq_abs]
  fin_cases j
  · change (A i 0) ^ 2 ≤ U ^ 2
    nlinarith only [hh, sq_nonneg (A i 1)]
  · change (A i 1) ^ 2 ≤ U ^ 2
    nlinarith only [hh, sq_nonneg (A i 0)]

end
end Shao.OQ3
