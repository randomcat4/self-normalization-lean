import Shao.Probability.SourceSuffixScalarInterfaces
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryUnmarkedDampedMoments
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem auxiliary_actual_unmarked_gaussian_damped_moments :
    let c : ℝ := (1 - Real.exp (-2)) / 8
    ∀ p : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ (n : ℕ) (b s : ℝ), 0 < b → 0 < s → s ≤ 2 / b →
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          let retained : ℝ := ∫ z : ℝ, if z ^ 2 ≤ b then z ^ 2 else 0 ∂nu
          let gamma : ℝ := if (1 / 2 : ℝ) ≤ retained then -c else 1
          Integrable (fun v : Shao.Path n =>
            |Shao.prefixSum v n| ^ p * Real.exp (-s * Shao.energy v)) P ∧
            (∫ v : Shao.Path n,
              |Shao.prefixSum v n| ^ p * Real.exp (-s * Shao.energy v) ∂P) ≤
              C * Real.rpow s (-(p : ℝ) / 2) *
                Real.exp (gamma * s * (n : ℝ)) := by
  intro c p
  let lambda : ℝ := (1 - Real.exp (-2)) / 16
  have hLambda : 0 < lambda :=
    Shao.Probability.raw_gaussian_damped_coordinate_factors.1
  let C : ℝ := 2 * ((p.factorial : ℝ) / lambda ^ p)
  have hFactorial : 0 < (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos p
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro nu _ h2 hMean hNorm n b s hb hs hsb P retained gamma
  classical
  let J : ℝ → Shao.Path n → ℝ := fun epsilon v =>
    Real.exp (-s * Shao.energy v + epsilon * lambda * Real.sqrt s * Shao.prefixSum v n)
  let g : ℝ → ℝ → ℝ := fun epsilon z =>
    Real.exp (-s * z ^ 2 + epsilon * lambda * Real.sqrt s * z)
  let A : ℝ := ((p.factorial : ℝ) / lambda ^ p) * Real.rpow s (-(p : ℝ) / 2)
  let B : ℝ := Real.exp (gamma * s * (n : ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hRaw := Shao.Probability.raw_gaussian_damped_coordinate_factors.2.2
    nu h2 hMean hNorm b s hb hs hsb
  have hProd (epsilon : ℝ) (he : epsilon = 1 ∨ epsilon = -1) :
      Integrable (J epsilon) P ∧
        (∫ v : Shao.Path n, J epsilon v ∂P) = (∫ z : ℝ, g epsilon z ∂nu) ^ n := by
    have hgi : Integrable (g epsilon) nu := (hRaw.2 epsilon he).1
    let f : Fin n → ℝ → ℝ := fun _ => g epsilon
    have hPoint (v : Shao.Path n) : (∏ i : Fin n, f i (v i)) = J epsilon v := by
      dsimp only [f, g, J]
      rw [← Real.exp_sum]
      congr 1
      simp only [Shao.energy, Shao.prefixSum_length, Finset.mul_sum, Finset.sum_add_distrib]
    have hInt : Integrable (fun v : Shao.Path n => ∏ i : Fin n, f i (v i)) P :=
      Integrable.fintype_prod (fun _ => hgi)
    refine ⟨hInt.congr (ae_of_all _ hPoint), ?_⟩
    calc
      _ = ∫ v : Shao.Path n, ∏ i : Fin n, f i (v i) ∂P :=
        integral_congr_ae (ae_of_all _ fun v => (hPoint v).symm)
      _ = ∏ i : Fin n, ∫ z : ℝ, f i z ∂nu := integral_fintype_prod_eq_prod f
      _ = _ := by simp only [f, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hJBound (epsilon : ℝ) (he : epsilon = 1 ∨ epsilon = -1) :
      (∫ v : Shao.Path n, J epsilon v ∂P) ≤ B := by
    have hIntegral : (∫ z : ℝ, g epsilon z ∂nu) ≤ Real.exp (gamma * s) :=
      (hRaw.2 epsilon he).2.2.1
    have hIntegral0 : 0 ≤ ∫ z : ℝ, g epsilon z ∂nu :=
      integral_nonneg (fun _ => (Real.exp_pos _).le)
    have hPow := pow_le_pow_left₀ hIntegral0 hIntegral n
    have hExp : (Real.exp (gamma * s)) ^ n = B := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc
      _ = (∫ z : ℝ, g epsilon z ∂nu) ^ n := (hProd epsilon he).2
      _ ≤ (Real.exp (gamma * s)) ^ n := hPow
      _ = B := hExp
  have hPoint (v : Shao.Path n) :
      |Shao.prefixSum v n| ^ p * Real.exp (-s * Shao.energy v) ≤
        A * (J 1 v + J (-1) v) := by
    have hScalar :=
      Shao.Probability.SourceSuffixScalarInterfaces.scaled_polynomial_exponentials
        p lambda s (Shao.prefixSum v n) hLambda hs
    calc
      _ = Real.exp (-s * Shao.energy v) * |Shao.prefixSum v n| ^ p := by ring
      _ ≤ Real.exp (-s * Shao.energy v) * (A *
          (Real.exp (lambda * Real.sqrt s * Shao.prefixSum v n) +
            Real.exp (-lambda * Real.sqrt s * Shao.prefixSum v n))) :=
        mul_le_mul_of_nonneg_left hScalar (Real.exp_pos _).le
      _ = _ := by dsimp only [J]; simp only [one_mul, neg_one_mul, Real.exp_add]; ring
  have hBoundInt : Integrable (fun v : Shao.Path n => A * (J 1 v + J (-1) v)) P :=
    ((hProd 1 (Or.inl rfl)).1.add (hProd (-1) (Or.inr rfl)).1).const_mul A
  have hMeas : Continuous (fun v : Shao.Path n =>
      |Shao.prefixSum v n| ^ p * Real.exp (-s * Shao.energy v)) :=
    ((Shao.continuous_prefixSum n).abs.pow p).mul
      (Real.continuous_exp.comp (continuous_const.mul Shao.continuous_energy))
  have hTarget : Integrable (fun v : Shao.Path n =>
      |Shao.prefixSum v n| ^ p * Real.exp (-s * Shao.energy v)) P := by
    refine hBoundInt.mono' hMeas.aestronglyMeasurable (ae_of_all _ fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (abs_nonneg _) p) (Real.exp_pos _).le)]
    exact hPoint v
  refine ⟨hTarget, ?_⟩
  have hIntegral := integral_mono hTarget hBoundInt hPoint
  rw [integral_const_mul, integral_add (hProd 1 (Or.inl rfl)).1
    (hProd (-1) (Or.inr rfl)).1] at hIntegral
  calc
    _ ≤ A * ((∫ v : Shao.Path n, J 1 v ∂P) + ∫ v : Shao.Path n, J (-1) v ∂P) := hIntegral
    _ ≤ A * (B + B) := mul_le_mul_of_nonneg_left
      (add_le_add (hJBound 1 (Or.inl rfl)) (hJBound (-1) (Or.inr rfl))) hA
    _ = _ := by dsimp only [C, A, B]; ring

end Shao.C2.AuxiliaryUnmarkedDampedMoments
