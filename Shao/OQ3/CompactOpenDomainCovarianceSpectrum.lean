import Shao.OQ3.OpenDomainCompactMoments
import Shao.OQ3.OpenDomainCovarianceAmplitude

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem quadratic_form_bounds_of_det_trace
    (a b d delta T : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hdelta : 0 < delta) (hdet : delta ≤ a * d - b ^ 2)
    (hT : 0 < T) (htrace : a + d ≤ T) (xi eta : ℝ) :
    delta / T * (xi ^ 2 + eta ^ 2) ≤
        a * xi ^ 2 + 2 * b * xi * eta + d * eta ^ 2 ∧
      a * xi ^ 2 + 2 * b * xi * eta + d * eta ^ 2 ≤
        T * (xi ^ 2 + eta ^ 2)
 := by
  let q := a * xi ^ 2 + 2 * b * xi * eta + d * eta ^ 2
  let qa := d * xi ^ 2 - 2 * b * xi * eta + a * eta ^ 2
  let z := xi ^ 2 + eta ^ 2
  have hz : 0 ≤ z := add_nonneg (sq_nonneg xi) (sq_nonneg eta)
  have hdet0 : 0 ≤ a * d - b ^ 2 := le_trans hdelta.le hdet
  have htr : 0 < a + d := by nlinarith [sq_nonneg b]
  have hid : (a + d) * q - (a * d - b ^ 2) * z =
      (a * xi + b * eta) ^ 2 + (b * xi + d * eta) ^ 2 := by
    dsimp [q, z]
    ring
  have hbase : (a * d - b ^ 2) * z ≤ (a + d) * q := by
    nlinarith [sq_nonneg (a * xi + b * eta), sq_nonneg (b * xi + d * eta)]
  have hq : 0 ≤ q := by nlinarith [mul_nonneg hdet0 hz]
  have hida : (a + d) * qa - (a * d - b ^ 2) * z =
      (d * xi - b * eta) ^ 2 + (-b * xi + a * eta) ^ 2 := by
    dsimp [qa, z]
    ring
  have hbasea : (a * d - b ^ 2) * z ≤ (a + d) * qa := by
    nlinarith [sq_nonneg (d * xi - b * eta), sq_nonneg (-b * xi + a * eta)]
  have hqa : 0 ≤ qa := by nlinarith [mul_nonneg hdet0 hz]
  have hsum : q + qa = (a + d) * z := by dsimp [q, qa, z]; ring
  have hupper : q ≤ (a + d) * z := by linarith
  constructor
  · change delta / T * z ≤ q
    calc
      delta / T * z = (delta * z) / T := by ring
      _ ≤ q := (div_le_iff₀ hT).2 <| calc
        delta * z ≤ (a * d - b ^ 2) * z := mul_le_mul_of_nonneg_right hdet hz
        _ ≤ (a + d) * q := hbase
        _ ≤ T * q := mul_le_mul_of_nonneg_right htrace hq
        _ = q * T := mul_comm _ _
  · exact hupper.trans (mul_le_mul_of_nonneg_right htrace hz)

theorem compact_open_domain_covariance_spectral_bounds
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : ∀ p ∈ Theta, 0 < (parabolaCovariance
      (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))).det) :
    let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
      parabolaCovariance (nu p)
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ∀ p ∈ Theta, ∀ xi eta : ℝ,
      lo * (xi ^ 2 + eta ^ 2) ≤
          D p 0 0 * xi ^ 2 + 2 * D p 0 1 * xi * eta + D p 1 1 * eta ^ 2 ∧
        D p 0 0 * xi ^ 2 + 2 * D p 0 1 * xi * eta + D p 1 1 * eta ^ 2 ≤
          hi * (xi ^ 2 + eta ^ 2) := by
  dsimp only
  let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
    mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
    parabolaCovariance (nu p)
  have hc : ContinuousOn (fun p => (D p).det) Theta :=
    (open_domain_quadratic_covariance_det_contDiffOn mu).continuousOn.mono hTheta
  obtain ⟨delta, hdelta, hdeltaBound⟩ := hcompact.exists_forall_le' hc hdet
  have hm := compact_open_domain_uniform_tilted_moments mu Theta hcompact hTheta
  obtain ⟨C2, hC2pos, hC2⟩ := hm.2 2
  obtain ⟨C4, hC4pos, hC4⟩ := hm.2 4
  let T := C2 + C4 + 1
  have hT : 0 < T := by dsimp [T]; linarith
  refine ⟨delta / T, T, div_pos hdelta hT, hT, ?_⟩
  intro p hp xi eta
  letI : IsProbabilityMeasure (nu p) := hm.1 p hp
  have hi2 : Integrable (fun x : ℝ => x ^ 2) (nu p) := by
    simpa only [sq_abs] using (hC2 p hp).1
  have hi4 : Integrable (fun x : ℝ => (x ^ 2) ^ 2) (nu p) := by
    simpa only [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs] using (hC4 p hp).1
  have hx : MemLp (fun x : ℝ => x) 2 (nu p) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hi2
  have hx2 : MemLp (fun x : ℝ => x ^ 2) 2 (nu p) :=
    (memLp_two_iff_integrable_sq
      (measurable_id.pow_const 2).aestronglyMeasurable).2 hi4
  have hraw2 : (∫ x : ℝ, x ^ 2 ∂nu p) ≤ C2 := by
    simpa only [sq_abs] using (hC2 p hp).2.2
  have hraw4 : (∫ x : ℝ, (x ^ 2) ^ 2 ∂nu p) ≤ C4 := by
    simpa only [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs] using (hC4 p hp).2.2
  have h00 : D p 0 0 ≤ C2 := by
    change variance (fun x : ℝ => x) (nu p) ≤ C2
    rw [variance_eq_sub hx]
    simp only [Pi.pow_apply]
    nlinarith [sq_nonneg (∫ x : ℝ, x ∂nu p)]
  have h11 : D p 1 1 ≤ C4 := by
    change variance (fun x : ℝ => x ^ 2) (nu p) ≤ C4
    rw [variance_eq_sub hx2]
    simp only [Pi.pow_apply]
    nlinarith [sq_nonneg (∫ x : ℝ, x ^ 2 ∂nu p)]
  have htrace : D p 0 0 + D p 1 1 ≤ T := by dsimp [T]; linarith
  have hsym : D p 1 0 = D p 0 1 := rfl
  have hd : delta ≤ D p 0 0 * D p 1 1 - D p 0 1 ^ 2 := by
    have h := hdeltaBound p hp
    simpa only [Matrix.det_fin_two, hsym, pow_two] using h
  exact quadratic_form_bounds_of_det_trace (D p 0 0) (D p 0 1) (D p 1 1) delta T
    (variance_nonneg (fun x : ℝ => x) (nu p))
    (variance_nonneg (fun x : ℝ => x ^ 2) (nu p)) hdelta hd hT htrace xi eta

end
end Shao.OQ3
