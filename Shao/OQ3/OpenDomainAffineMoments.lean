import Shao.OQ3.OpenDomainCompactMoments
import Shao.OQ3.CovarianceWhitening

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

private theorem affine_radius_le_abs (a b : ℝ) : Real.sqrt (a ^ 2 + b ^ 2) ≤ |a| + |b| := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).mp
  rw [Real.sq_sqrt (by positivity)]
  nlinarith [mul_nonneg (abs_nonneg a) (abs_nonneg b), sq_abs a, sq_abs b]

private theorem quadratic_power_growth (x : ℝ) (k : ℕ) :
    (1 + x ^ 2) ^ k ≤ (2 : ℝ) ^ k * (1 + |x| ^ (2 * k)) := by
  have heven : 0 ≤ x ^ (2 * k) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) k
  have habs : |x| ^ (2 * k) = x ^ (2 * k) := by rw [← abs_pow, abs_of_nonneg heven]
  rw [habs]
  by_cases hx : x ^ 2 ≤ 1
  · calc
      (1 + x ^ 2) ^ k ≤ (2 : ℝ) ^ k :=
        pow_le_pow_left₀ (by positivity) (by linarith) k
      _ ≤ (2 : ℝ) ^ k * (1 + x ^ (2 * k)) := by
        nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k) heven]
  · have hx' : 1 ≤ x ^ 2 := le_of_lt (lt_of_not_ge hx)
    calc
      (1 + x ^ 2) ^ k ≤ (2 * x ^ 2) ^ k :=
        pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = (2 : ℝ) ^ k * x ^ (2 * k) := by rw [mul_pow, pow_mul]
      _ ≤ (2 : ℝ) ^ k * (1 + x ^ (2 * k)) := by
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k]

theorem compact_open_domain_affine_parabola_moments
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (A : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hA : ∀ theta ∈ Theta, ∀ i j : Fin 2, |A theta i j| ≤ U) :
    let tilt : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let means : (ℝ × ℝ) → (Fin 2 → ℝ) := fun p =>
      ![∫ x : ℝ, x ∂tilt p, ∫ x : ℝ, x ^ 2 ∂tilt p]
    let Y : (ℝ × ℝ) → ℝ → (Fin 2 → ℝ) := fun p x =>
      A p *ᵥ (![x, x ^ 2] - means p)
    let laws : (ℝ × ℝ) → Measure (Fin 2 → ℝ) := fun p => (tilt p).map (Y p)
    (∀ theta ∈ Theta, IsProbabilityMeasure (laws theta)) ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ theta ∈ Theta,
        Integrable (fun y : Fin 2 → ℝ => (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k)
          (laws theta) ∧
        0 ≤ (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k ∂laws theta) ∧
        (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k ∂laws theta) ≤ C := by
  let tilt : (ℝ × ℝ) → Measure ℝ := fun p =>
    mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  let means : (ℝ × ℝ) → (Fin 2 → ℝ) := fun p =>
    ![∫ x : ℝ, x ∂tilt p, ∫ x : ℝ, x ^ 2 ∂tilt p]
  let Y : (ℝ × ℝ) → ℝ → (Fin 2 → ℝ) := fun p x => A p *ᵥ (![x, x ^ 2] - means p)
  let laws : (ℝ × ℝ) → Measure (Fin 2 → ℝ) := fun p => (tilt p).map (Y p)
  let radius : (Fin 2 → ℝ) → ℝ := fun y => Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)
  have hradius : Continuous radius := by dsimp [radius]; fun_prop
  have hY (p : ℝ × ℝ) : Continuous (Y p) := by
    apply continuous_pi
    intro i
    change Continuous (fun x : ℝ => ∑ j : Fin 2, A p i j * ((![x, x ^ 2] : Fin 2 → ℝ) j - means p j))
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    fun_prop
  have hraw := compact_open_domain_uniform_tilted_moments mu Theta hcompact hTheta
  have hpush (p : ℝ × ℝ) (hp : p ∈ Theta) : IsProbabilityMeasure (laws p) := by
    letI : IsProbabilityMeasure (tilt p) := hraw.1 p hp
    exact (Measure.isProbabilityMeasure_map_iff (hY p).measurable.aemeasurable).mpr inferInstance
  obtain ⟨C1, hC1, hraw1⟩ := hraw.2 1
  obtain ⟨C2, hC2, hraw2⟩ := hraw.2 2
  let B : ℝ := C1 + C2 + 2
  let Q : ℝ := 2 * U * B
  have hQ : 0 ≤ Q := by dsimp [Q, B]; positivity
  have hR (p : ℝ × ℝ) (hp : p ∈ Theta) (x : ℝ) : radius (Y p x) ≤ Q * (1 + x ^ 2) := by
    have hm0 : |means p 0| ≤ C1 := by
      change |∫ x : ℝ, x ∂tilt p| ≤ C1
      calc
        _ ≤ ∫ x : ℝ, |x| ∂tilt p := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := tilt p) (fun x : ℝ => x)
        _ ≤ C1 := by simpa only [pow_one] using (hraw1 p hp).2.2
    have hm1 : |means p 1| ≤ C2 := by
      change |∫ x : ℝ, x ^ 2 ∂tilt p| ≤ C2
      calc
        _ ≤ ∫ x : ℝ, |x| ^ 2 ∂tilt p := by
          have hh := norm_integral_le_integral_norm (μ := tilt p) (fun x : ℝ => x ^ 2)
          have hf : (fun x : ℝ => ‖x ^ 2‖) = (fun x => |x| ^ 2) := by
            funext x
            rw [Real.norm_eq_abs, abs_pow]
          rw [hf] at hh
          simpa only [Real.norm_eq_abs] using hh
        _ ≤ C2 := (hraw2 p hp).2.2
    have hc0 : |x - means p 0| ≤ |x| + C1 := by linarith [abs_sub x (means p 0)]
    have hc1 : |x ^ 2 - means p 1| ≤ x ^ 2 + C2 := by
      have hh := abs_sub (x ^ 2) (means p 1)
      rw [abs_of_nonneg (sq_nonneg x)] at hh
      linarith
    have hYi (i : Fin 2) : |Y p x i| ≤ U * (|x| + x ^ 2 + C1 + C2) := by
      change |∑ j : Fin 2, A p i j * ((![x, x ^ 2] : Fin 2 → ℝ) j - means p j)| ≤ _
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      calc
        _ ≤ |A p i 0| * |x - means p 0| + |A p i 1| * |x ^ 2 - means p 1| := by
          have hh := abs_add_le
            (A p i 0 * (x - means p 0)) (A p i 1 * (x ^ 2 - means p 1))
          rw [abs_mul (A p i 0) (x - means p 0), abs_mul (A p i 1) (x ^ 2 - means p 1)] at hh
          exact hh
        _ ≤ U * (|x| + C1) + U * (x ^ 2 + C2) := add_le_add
          (mul_le_mul (hA p hp i 0) hc0 (abs_nonneg _) hU)
          (mul_le_mul (hA p hp i 1) hc1 (abs_nonneg _) hU)
        _ = _ := by ring
    have hx : |x| ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
    have hbase : |x| + x ^ 2 + C1 + C2 ≤ B * (1 + x ^ 2) := by
      dsimp [B]
      nlinarith [mul_nonneg (add_nonneg hC1.le hC2.le) (sq_nonneg x)]
    calc
      radius (Y p x) ≤ |Y p x 0| + |Y p x 1| := affine_radius_le_abs _ _
      _ ≤ 2 * U * (|x| + x ^ 2 + C1 + C2) := by linarith [hYi 0, hYi 1]
      _ ≤ (2 * U) * (B * (1 + x ^ 2)) :=
        mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = Q * (1 + x ^ 2) := by dsimp [Q]; ring
  refine ⟨hpush, ?_⟩
  intro k
  obtain ⟨Ck, hCk, hrawk⟩ := hraw.2 (2 * k)
  let W : ℝ := (2 * Q) ^ k
  have hW : 0 ≤ W := by dsimp [W]; positivity
  refine ⟨W * (1 + Ck) + 1, by positivity, ?_⟩
  intro p hp
  letI : IsProbabilityMeasure (tilt p) := hraw.1 p hp
  have hpoint (x : ℝ) : radius (Y p x) ^ k ≤ W * (1 + |x| ^ (2 * k)) := by
    calc
      radius (Y p x) ^ k ≤ (Q * (1 + x ^ 2)) ^ k :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) (hR p hp x) k
      _ = Q ^ k * (1 + x ^ 2) ^ k := mul_pow _ _ _
      _ ≤ Q ^ k * ((2 : ℝ) ^ k * (1 + |x| ^ (2 * k))) :=
        mul_le_mul_of_nonneg_left (quadratic_power_growth x k) (pow_nonneg hQ k)
      _ = W * (1 + |x| ^ (2 * k)) := by
        change Q ^ k * ((2 : ℝ) ^ k * (1 + |x| ^ (2 * k))) =
          (2 * Q) ^ k * (1 + |x| ^ (2 * k))
        rw [mul_pow (2 : ℝ) Q k]
        ring
  have hdom : Integrable (fun x : ℝ => W * (1 + |x| ^ (2 * k))) (tilt p) :=
    ((integrable_const 1).add (hrawk p hp).1).const_mul W
  have hi : Integrable (fun x : ℝ => radius (Y p x) ^ k) (tilt p) := by
    apply hdom.mono' ((hradius.pow k).comp (hY p)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      change ‖radius (Y p x) ^ k‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) k)]
      exact hpoint x
  have hilaw : Integrable (fun y : Fin 2 → ℝ => radius y ^ k) (laws p) :=
    (integrable_map_measure (hradius.pow k).aestronglyMeasurable (hY p).measurable.aemeasurable).mpr hi
  have heq : (∫ y : Fin 2 → ℝ, radius y ^ k ∂laws p) = ∫ x : ℝ, radius (Y p x) ^ k ∂tilt p :=
    integral_map (hY p).measurable.aemeasurable (hradius.pow k).aestronglyMeasurable
  refine ⟨hilaw, integral_nonneg (fun y => pow_nonneg (Real.sqrt_nonneg _) k), ?_⟩
  rw [heq]
  calc
    (∫ x : ℝ, radius (Y p x) ^ k ∂tilt p) ≤ ∫ x : ℝ, W * (1 + |x| ^ (2 * k)) ∂tilt p :=
      integral_mono hi hdom hpoint
    _ = W * (1 + ∫ x : ℝ, |x| ^ (2 * k) ∂tilt p) := by
      rw [integral_const_mul, integral_add (integrable_const 1) (hrawk p hp).1]
      rw [show (∫ _x : ℝ, (1 : ℝ) ∂tilt p) = 1 by simp]
    _ ≤ W * (1 + Ck) := mul_le_mul_of_nonneg_left (by linarith [(hrawk p hp).2.2]) hW
    _ ≤ W * (1 + Ck) + 1 := by linarith

end
end Shao.OQ3
