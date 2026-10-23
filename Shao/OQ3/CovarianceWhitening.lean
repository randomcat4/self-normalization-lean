import Shao.OQ3.AffineWeakCramer
import Shao.OQ3.RegularCovariance
import Mathlib.Probability.Moments.Covariance

namespace Shao.OQ3

open MeasureTheory
open scoped Matrix BigOperators

noncomputable section

private theorem whitening_map_continuous
    (A : Matrix (Fin 2) (Fin 2) ℝ) (m : Fin 2 → ℝ) :
    Continuous (fun x : ℝ => A *ᵥ (![x, x ^ 2] - m)) := by
  apply continuous_pi
  intro i
  change Continuous (fun x : ℝ => ∑ j : Fin 2,
    A i j * ((![x, x ^ 2] : Fin 2 → ℝ) j - m j))
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  fun_prop

private theorem euclidean_radius_le_abs (x y : ℝ) :
    Real.sqrt (x ^ 2 + y ^ 2) ≤ |x| + |y| := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).mp
  rw [Real.sq_sqrt (by positivity)]
  nlinarith [mul_nonneg (abs_nonneg x) (abs_nonneg y), sq_abs x, sq_abs y]

private theorem whitening_spectral_data
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

theorem centered_affine_parabola_mean_covariance
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (h1 : MemLp (fun x : ℝ => x) 2 mu)
    (h2 : MemLp (fun x : ℝ => x ^ 2) 2 mu)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    let m : Fin 2 → ℝ := ![∫ x, x ∂mu, ∫ x, x ^ 2 ∂mu]
    let Y : ℝ → (Fin 2 → ℝ) := fun x => A *ᵥ (![x, x ^ 2] - m)
    let nu : Measure (Fin 2 → ℝ) := mu.map Y
    IsProbabilityMeasure nu ∧
      (∀ i : Fin 2, MemLp (fun y : Fin 2 → ℝ => y i) 2 nu ∧
        (∫ y : Fin 2 → ℝ, y i ∂nu) = 0) ∧
      ∀ i j : Fin 2,
        ProbabilityTheory.covariance (fun y : Fin 2 → ℝ => y i)
          (fun y : Fin 2 → ℝ => y j) nu =
            (A * parabolaCovariance mu * Aᵀ) i j := by
  let m : Fin 2 → ℝ := ![∫ x, x ∂mu, ∫ x, x ^ 2 ∂mu]
  let Y : ℝ → (Fin 2 → ℝ) := fun x => A *ᵥ (![x, x ^ 2] - m)
  let nu : Measure (Fin 2 → ℝ) := mu.map Y
  let W : Fin 2 → ℝ → ℝ := fun i x => (![x, x ^ 2] : Fin 2 → ℝ) i
  let Z : Fin 2 → ℝ → ℝ := fun i x => W i x - m i
  have hW (i : Fin 2) : MemLp (W i) 2 mu := by
    fin_cases i
    · simpa [W] using h1
    · simpa [W] using h2
  have hZ (i : Fin 2) : MemLp (Z i) 2 mu := (hW i).sub (memLp_const (m i))
  have hmi (i : Fin 2) : (∫ x, W i x ∂mu) = m i := by fin_cases i <;> rfl
  have hZmean (i : Fin 2) : (∫ x, Z i x ∂mu) = 0 := by
    dsimp only [Z]
    rw [integral_sub ((hW i).integrable (by norm_num)) (integrable_const (m i))]
    simp [hmi i]
  have hcoord (i : Fin 2) : (fun x => Y x i) = fun x => ∑ k : Fin 2, A i k * Z k x := by
    rfl
  have hYlp (i : Fin 2) : MemLp (fun x => Y x i) 2 mu := by
    rw [hcoord]
    have hadd : ((fun x => A i 0 * Z 0 x) + (fun x => A i 1 * Z 1 x)) =
        (fun x => ∑ k : Fin 2, A i k * Z k x) := by
      funext x
      simp only [Fin.sum_univ_two, Pi.add_apply]
    exact hadd ▸ ((hZ 0).const_mul (A i 0)).add ((hZ 1).const_mul (A i 1))
  have hY : Continuous Y := whitening_map_continuous A m
  have hproj (i : Fin 2) : Continuous (fun y : Fin 2 → ℝ => y i) := continuous_apply i
  have hnu : IsProbabilityMeasure nu :=
    (Measure.isProbabilityMeasure_map_iff hY.measurable.aemeasurable).mpr inferInstance
  have hZcov (i j : Fin 2) : ProbabilityTheory.covariance (Z i) (Z j) mu =
      parabolaCovariance mu i j := by
    dsimp only [Z]
    rw [ProbabilityTheory.covariance_sub_const_left ((hW i).integrable (by norm_num)),
      ProbabilityTheory.covariance_sub_const_right ((hW j).integrable (by norm_num))]
    fin_cases i <;> fin_cases j
    · simpa [W, parabolaCovariance] using
        (ProbabilityTheory.covariance_self (μ := mu) (X := fun x : ℝ => x) measurable_id.aemeasurable)
    · rfl
    · simpa [W, parabolaCovariance] using
        (ProbabilityTheory.covariance_comm (fun x : ℝ => x ^ 2) (fun x : ℝ => x) (μ := mu))
    · simpa [W, parabolaCovariance] using
        (ProbabilityTheory.covariance_self (μ := mu) (X := fun x : ℝ => x ^ 2) (by fun_prop))
  change IsProbabilityMeasure nu ∧
    (∀ i : Fin 2, MemLp (fun y : Fin 2 → ℝ => y i) 2 nu ∧
      (∫ y : Fin 2 → ℝ, y i ∂nu) = 0) ∧ _
  refine ⟨hnu, ?_, ?_⟩
  · intro i
    refine ⟨(memLp_map_measure_iff (hproj i).aestronglyMeasurable
      hY.measurable.aemeasurable).mpr (hYlp i), ?_⟩
    rw [integral_map hY.measurable.aemeasurable (hproj i).aestronglyMeasurable, hcoord]
    simp only [Fin.sum_univ_two]
    rw [integral_add (((hZ 0).const_mul (A i 0)).integrable (by norm_num))
      (((hZ 1).const_mul (A i 1)).integrable (by norm_num)),
      integral_const_mul, integral_const_mul, hZmean 0, hZmean 1]
    simp
  · intro i j
    rw [ProbabilityTheory.covariance_map_fun (hproj i).aestronglyMeasurable
      (hproj j).aestronglyMeasurable hY.measurable.aemeasurable, hcoord, hcoord]
    rw [ProbabilityTheory.covariance_fun_sum_fun_sum
      (fun k => (hZ k).const_mul (A i k)) (fun k => (hZ k).const_mul (A j k))]
    simp_rw [ProbabilityTheory.covariance_const_mul_left,
      ProbabilityTheory.covariance_const_mul_right, hZcov]
    simp only [Fin.sum_univ_two, Matrix.mul_apply, Matrix.transpose_apply]
    ring

theorem uniform_covariance_whitened_moments_weakCramer
    {ι : Type*} (K : Set ι) (mu : ι → Measure ℝ)
    (hprob : ∀ p ∈ K, IsProbabilityMeasure (mu p))
    (M lambdaMin lambdaMax beta c R : ℝ)
    (hM : 0 ≤ M) (hmin : 0 < lambdaMin) (hmax : 0 < lambdaMax)
    (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hbound : ∀ p ∈ K, ∀ᵐ x ∂mu p, |x| ≤ M)
    (hspec : ∀ p ∈ K, ∀ xi eta : ℝ,
      lambdaMin * (xi ^ 2 + eta ^ 2) ≤
          xi ^ 2 * parabolaCovariance (mu p) 0 0 +
            2 * xi * eta * parabolaCovariance (mu p) 0 1 +
            eta ^ 2 * parabolaCovariance (mu p) 1 1 ∧
        xi ^ 2 * parabolaCovariance (mu p) 0 0 +
            2 * xi * eta * parabolaCovariance (mu p) 0 1 +
            eta ^ 2 * parabolaCovariance (mu p) 1 1 ≤
          lambdaMax * (xi ^ 2 + eta ^ 2))
    (hWC : ∀ p ∈ K, ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu p) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    let D : ι → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (mu p)
    let s : ι → ℝ := fun p => Real.sqrt (D p 0 0 * D p 1 1 - (D p 0 1) ^ 2)
    let t : ι → ℝ := fun p => Real.sqrt (D p 0 0 + D p 1 1 + 2 * s p)
    let A : ι → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
      ![![(D p 1 1 + s p) / (s p * t p), -(D p 0 1) / (s p * t p)],
        ![-(D p 0 1) / (s p * t p), (D p 0 0 + s p) / (s p * t p)]]
    let m : ι → (Fin 2 → ℝ) := fun p => ![∫ x, x ∂mu p, ∫ x, x ^ 2 ∂mu p]
    let Y : ι → ℝ → (Fin 2 → ℝ) := fun p x => A p *ᵥ (![x, x ^ 2] - m p)
    let nu : ι → Measure (Fin 2 → ℝ) := fun p => (mu p).map (Y p)
    let Phi : ι → ℝ → ℝ → ℂ := fun p xi eta =>
      ∫ y : Fin 2 → ℝ,
        Complex.exp (((xi * y 0 + eta * y 1 : ℝ) : ℂ) * Complex.I) ∂nu p
    let L : ℝ := 1 / Real.sqrt lambdaMax
    let U : ℝ := 1 / Real.sqrt lambdaMin
    let Q : ℝ := 4 * U * (M + M ^ 2)
    let cA : ℝ := c * Real.rpow U (-beta)
    let RA : ℝ := R / L
    0 < L ∧ 0 < U ∧ 0 ≤ Q ∧ 0 < cA ∧ 0 ≤ RA ∧
      ∀ p ∈ K,
        0 < s p ∧ 0 < t p ∧ (A p)ᵀ = A p ∧ A p * D p * A p = 1 ∧
        (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
          0 < xi * (A p *ᵥ ![xi, eta]) 0 + eta * (A p *ᵥ ![xi, eta]) 1) ∧
        IsProbabilityMeasure (nu p) ∧
        (∀ i : Fin 2, MemLp (fun y : Fin 2 → ℝ => y i) 2 (nu p) ∧
          (∫ y : Fin 2 → ℝ, y i ∂nu p) = 0) ∧
        (∀ i j : Fin 2,
          ProbabilityTheory.covariance (fun y : Fin 2 → ℝ => y i)
            (fun y : Fin 2 → ℝ => y j) (nu p) = if i = j then 1 else 0) ∧
        (∀ᵐ y : Fin 2 → ℝ ∂nu p, Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2) ≤ Q) ∧
        (∀ k : ℕ,
          Integrable (fun y : Fin 2 → ℝ => (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k)
            (nu p) ∧
          (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k ∂nu p) ≤ Q ^ k) ∧
        ∀ xi eta : ℝ, RA < Real.sqrt (xi ^ 2 + eta ^ 2) →
          ‖Phi p xi eta‖ ≤
            1 - cA * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta) := by
  let D : ι → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (mu p)
  let s : ι → ℝ := fun p => Real.sqrt (D p 0 0 * D p 1 1 - (D p 0 1) ^ 2)
  let t : ι → ℝ := fun p => Real.sqrt (D p 0 0 + D p 1 1 + 2 * s p)
  let A : ι → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
    ![![(D p 1 1 + s p) / (s p * t p), -(D p 0 1) / (s p * t p)],
      ![-(D p 0 1) / (s p * t p), (D p 0 0 + s p) / (s p * t p)]]
  let m : ι → (Fin 2 → ℝ) := fun p => ![∫ x, x ∂mu p, ∫ x, x ^ 2 ∂mu p]
  let Y : ι → ℝ → (Fin 2 → ℝ) := fun p x => A p *ᵥ (![x, x ^ 2] - m p)
  let nu : ι → Measure (Fin 2 → ℝ) := fun p => (mu p).map (Y p)
  let Phi : ι → ℝ → ℝ → ℂ := fun p xi eta =>
    ∫ y : Fin 2 → ℝ,
      Complex.exp (((xi * y 0 + eta * y 1 : ℝ) : ℂ) * Complex.I) ∂nu p
  let L : ℝ := 1 / Real.sqrt lambdaMax
  let U : ℝ := 1 / Real.sqrt lambdaMin
  let Q : ℝ := 4 * U * (M + M ^ 2)
  let cA : ℝ := c * Real.rpow U (-beta)
  let RA : ℝ := R / L
  change 0 < L ∧ 0 < U ∧ 0 ≤ Q ∧ 0 < cA ∧ 0 ≤ RA ∧
    ∀ p ∈ K,
      0 < s p ∧ 0 < t p ∧ (A p)ᵀ = A p ∧ A p * D p * A p = 1 ∧
      (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
        0 < xi * (A p *ᵥ ![xi, eta]) 0 + eta * (A p *ᵥ ![xi, eta]) 1) ∧
      IsProbabilityMeasure (nu p) ∧
      (∀ i : Fin 2, MemLp (fun y : Fin 2 → ℝ => y i) 2 (nu p) ∧
        (∫ y : Fin 2 → ℝ, y i ∂nu p) = 0) ∧
      (∀ i j : Fin 2,
        ProbabilityTheory.covariance (fun y : Fin 2 → ℝ => y i)
          (fun y : Fin 2 → ℝ => y j) (nu p) = if i = j then 1 else 0) ∧
      (∀ᵐ y : Fin 2 → ℝ ∂nu p, Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2) ≤ Q) ∧
      (∀ k : ℕ,
        Integrable (fun y : Fin 2 → ℝ => (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k)
          (nu p) ∧
        (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k ∂nu p) ≤ Q ^ k) ∧
      ∀ xi eta : ℝ, RA < Real.sqrt (xi ^ 2 + eta ^ 2) →
        ‖Phi p xi eta‖ ≤
          1 - cA * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)
  have hL : 0 < L := one_div_pos.mpr (Real.sqrt_pos.2 hmax)
  have hU : 0 < U := one_div_pos.mpr (Real.sqrt_pos.2 hmin)
  have hQ : 0 ≤ Q := mul_nonneg (mul_nonneg (by norm_num) hU.le)
    (add_nonneg hM (sq_nonneg M))
  have hdata (p : ι) (hp : p ∈ K) :
      0 < s p ∧ 0 < t p ∧ (A p)ᵀ = A p ∧ A p * D p * A p = 1 ∧
      (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
        0 < xi * (A p *ᵥ ![xi, eta]) 0 + eta * (A p *ᵥ ![xi, eta]) 1) ∧
      ∀ xi eta : ℝ,
        L * Real.sqrt (xi ^ 2 + eta ^ 2) ≤
          Real.sqrt ((xi * A p 0 0 + eta * A p 1 0) ^ 2 +
            (xi * A p 0 1 + eta * A p 1 1) ^ 2) ∧
        Real.sqrt ((xi * A p 0 0 + eta * A p 1 0) ^ 2 +
            (xi * A p 0 1 + eta * A p 1 1) ^ 2) ≤
          U * Real.sqrt (xi ^ 2 + eta ^ 2) :=
    whitening_spectral_data (D p) (by rfl) lambdaMin lambdaMax hmin hmax (hspec p hp)
  have hfreq : ∀ p ∈ K, ∀ xi eta : ℝ,
      L * Real.sqrt (xi ^ 2 + eta ^ 2) ≤
        Real.sqrt ((xi * A p 0 0 + eta * A p 1 0) ^ 2 +
          (xi * A p 0 1 + eta * A p 1 1) ^ 2) ∧
      Real.sqrt ((xi * A p 0 0 + eta * A p 1 0) ^ 2 +
          (xi * A p 0 1 + eta * A p 1 1) ^ 2) ≤
        U * Real.sqrt (xi ^ 2 + eta ^ 2) := by
    intro p hp
    exact (hdata p hp).2.2.2.2.2
  obtain ⟨hcA, hRA, htrans⟩ :=
    uniform_weakCramer_of_affine_frequency_bounds K mu hprob A m L U beta c R
      hL hU hbeta hc hR hfreq hWC
  refine ⟨hL, hU, hQ, hcA, hRA, ?_⟩
  intro p hp
  letI : IsProbabilityMeasure (mu p) := hprob p hp
  obtain ⟨hs, ht, hsym, hwhite, hpositive, hfrequency⟩ := hdata p hp
  have hx : MemLp (fun x : ℝ => x) 2 (mu p) :=
    MemLp.of_bound continuous_id.aestronglyMeasurable M
      (by simpa only [Real.norm_eq_abs] using hbound p hp)
  have hx2bound : ∀ᵐ x ∂mu p, |x ^ 2| ≤ M ^ 2 := (hbound p hp).mono fun x hx => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hx2 : MemLp (fun x : ℝ => x ^ 2) 2 (mu p) :=
    MemLp.of_bound (by fun_prop) (M ^ 2) (by simpa only [Real.norm_eq_abs] using hx2bound)
  obtain ⟨hnu, hmeans, hcov⟩ := centered_affine_parabola_mean_covariance (mu p) hx hx2 (A p)
  letI : IsProbabilityMeasure (nu p) := hnu
  have hunit (i j : Fin 2) : ProbabilityTheory.covariance
      (fun y : Fin 2 → ℝ => y i) (fun y : Fin 2 → ℝ => y j) (nu p) =
        if i = j then 1 else 0 := by
    rw [hcov, hsym, hwhite]
    exact Matrix.one_apply
  have hm0 : |m p 0| ≤ M := by
    simpa [m] using (norm_integral_le_of_norm_le_const
      (show ∀ᵐ x ∂mu p, ‖x‖ ≤ M by simpa only [Real.norm_eq_abs] using hbound p hp))
  have hm1 : |m p 1| ≤ M ^ 2 := by
    simpa [m] using (norm_integral_le_of_norm_le_const
      (show ∀ᵐ x ∂mu p, ‖x ^ 2‖ ≤ M ^ 2 by simpa only [Real.norm_eq_abs] using hx2bound))
  have hrow (i : Fin 2) : Real.sqrt ((A p i 0) ^ 2 + (A p i 1) ^ 2) ≤ U := by
    fin_cases i
    · simpa using (hfrequency 1 0).2
    · simpa using (hfrequency 0 1).2
  have hentry (i j : Fin 2) : |A p i j| ≤ U := by
    have hh := (sq_le_sq₀ (Real.sqrt_nonneg _) hU.le).2 (hrow i)
    rw [Real.sq_sqrt (by positivity)] at hh
    apply (sq_le_sq₀ (abs_nonneg _) hU.le).mp
    rw [sq_abs]
    fin_cases j
    · change (A p i 0) ^ 2 ≤ U ^ 2
      nlinarith only [hh, sq_nonneg (A p i 1)]
    · change (A p i 1) ^ 2 ≤ U ^ 2
      nlinarith only [hh, sq_nonneg (A p i 0)]
  have hY : Continuous (Y p) := whitening_map_continuous (A p) (m p)
  have hsource : ∀ᵐ x ∂mu p, Real.sqrt ((Y p x 0) ^ 2 + (Y p x 1) ^ 2) ≤ Q := by
    filter_upwards [hbound p hp, hx2bound] with x hxb hxb2
    have hcenter0 : |x - m p 0| ≤ 2 * M :=
      (abs_sub _ _).trans (by linarith only [hxb, hm0])
    have hcenter1 : |x ^ 2 - m p 1| ≤ 2 * M ^ 2 :=
      (abs_sub _ _).trans (by linarith only [hxb2, hm1])
    have hYi (i : Fin 2) : |Y p x i| ≤ 2 * U * (M + M ^ 2) := by
      change |∑ j : Fin 2, A p i j * ((![x, x ^ 2] : Fin 2 → ℝ) j - m p j)| ≤ _
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      calc
        _ ≤ |A p i 0| * |x - m p 0| + |A p i 1| * |x ^ 2 - m p 1| := by
          have hh := abs_add_le
            (A p i 0 * (x - m p 0)) (A p i 1 * (x ^ 2 - m p 1))
          rw [abs_mul (A p i 0) (x - m p 0), abs_mul (A p i 1) (x ^ 2 - m p 1)] at hh
          exact hh
        _ ≤ U * (2 * M) + U * (2 * M ^ 2) := add_le_add
          (mul_le_mul (hentry i 0) hcenter0 (abs_nonneg _) hU.le)
          (mul_le_mul (hentry i 1) hcenter1 (abs_nonneg _) hU.le)
        _ = _ := by ring
    calc
      _ ≤ |Y p x 0| + |Y p x 1| := euclidean_radius_le_abs _ _
      _ ≤ Q := by dsimp [Q]; linarith only [hYi 0, hYi 1]
  have hsupport : ∀ᵐ y : Fin 2 → ℝ ∂nu p,
      Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2) ≤ Q :=
    (ae_map_iff hY.measurable.aemeasurable
      (measurableSet_le (by fun_prop) measurable_const)).mpr hsource
  have hmom (k : ℕ) :
      Integrable (fun y : Fin 2 → ℝ => (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k) (nu p) ∧
      (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k ∂nu p) ≤ Q ^ k := by
    have hbnd : ∀ᵐ y : Fin 2 → ℝ ∂nu p,
        ‖(Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k‖ ≤ Q ^ k := by
      filter_upwards [hsupport] with y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hy k
    refine ⟨Integrable.of_bound (by fun_prop) (Q ^ k) hbnd, ?_⟩
    have hnorm := norm_integral_le_of_norm_le_const hbnd
    have habs : |∫ y : Fin 2 → ℝ,
        (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k ∂nu p| ≤ Q ^ k := by simpa using hnorm
    exact (le_abs_self _).trans habs
  exact ⟨hs, ht, hsym, hwhite, hpositive, hnu, hmeans, hunit,
    hsupport, hmom, (htrans p hp).2⟩

end

end Shao.OQ3
