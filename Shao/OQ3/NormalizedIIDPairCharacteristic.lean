import Shao.OQ3.ParabolaIIDStandardizedLaw
import Shao.Probability.QuadraticCharacteristic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
noncomputable section

theorem normalized_iid_pair_characteristic_factor
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law]
    (n : ℕ) (hn : 1 ≤ n) (xi eta : ℝ) :
    let Q : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
    let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun z =>
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, z i
    let rho : Measure (ℝ × ℝ) := Q.map S
    let Phi : ℝ → ℝ → ℂ := fun u v =>
      ∫ w : ℝ × ℝ, Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law
    (∫ w : ℝ × ℝ,
      Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho) =
        (Phi (xi / Real.sqrt (n : ℝ)) (eta / Real.sqrt (n : ℝ))) ^ n := by
  dsimp only
  let s : ℝ := Real.sqrt (n : ℝ)
  let Q : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
  let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun z =>
    s⁻¹ • ∑ i : Fin n, z i
  let K : (ℝ × ℝ) → ℂ := fun w =>
    Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I)
  let f : (ℝ × ℝ) → ℂ := fun w =>
    Complex.exp ((((xi / s) * w.1 + (eta / s) * w.2 : ℝ) : ℂ) * Complex.I)
  have hS : Continuous S := by
    dsimp [S]
    fun_prop
  have hK : Continuous K := by
    dsimp [K]
    fun_prop
  have hKint : Integrable K (Q.map S) :=
    (integrable_const (μ := Q.map S) (1 : ℝ)).mono' hK.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => by
        dsimp [K]
        rw [Complex.norm_exp_ofReal_mul_I])
  have hpoint : ∀ z : Fin n → (ℝ × ℝ), K (S z) = ∏ i : Fin n, f (z i) := by
    intro z
    have hphase : xi * (S z).1 + eta * (S z).2 =
        ∑ i : Fin n, ((xi / s) * (z i).1 + (eta / s) * (z i).2) := by
      change xi * (s⁻¹ * (∑ i : Fin n, z i).1) +
        eta * (s⁻¹ * (∑ i : Fin n, z i).2) = _
      simp only [Prod.fst_sum, Prod.snd_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    change Complex.exp (((xi * (S z).1 + eta * (S z).2 : ℝ) : ℂ) * Complex.I) = _
    rw [hphase]
    simp only [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    rfl
  change (∫ w, K w ∂Q.map S) = (∫ w, f w ∂law) ^ n
  rw [integral_map hS.measurable.aemeasurable hKint.aestronglyMeasurable]
  rw [show (fun z => K (S z)) = (fun z => ∏ i : Fin n, f (z i)) from funext hpoint]
  simpa only [Fintype.card_fin] using
    (integral_fintype_prod_eq_pow (ι := Fin n) (μ := law) f)

theorem iid_parabola_standardized_characteristic_factor
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 1 ≤ n)
    (y : ℝ × ℝ) (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (xi eta : ℝ) :
    let Y : ℝ → (ℝ × ℝ) := fun x => E ((x, x ^ 2) - y)
    let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    let T : Shao.Path n → (ℝ × ℝ) := fun z =>
      Real.sqrt (n : ℝ) • E (M z - y)
    let rho : Measure (ℝ × ℝ) := Q.map T
    let Phi : ℝ → ℝ → ℂ := fun u v =>
      ∫ x : ℝ, Complex.exp (((u * (Y x).1 + v * (Y x).2 : ℝ) : ℂ) * Complex.I) ∂nu
    (∫ w : ℝ × ℝ,
      Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho) =
        (Phi (xi / Real.sqrt (n : ℝ)) (eta / Real.sqrt (n : ℝ))) ^ n := by
  dsimp only
  let Y : ℝ → (ℝ × ℝ) := fun x => E ((x, x ^ 2) - y)
  let law : Measure (ℝ × ℝ) := nu.map Y
  obtain ⟨hlaw, _, _, hnormalized⟩ := iid_parabola_affine_standardized_law nu n hn y E
  letI : IsProbabilityMeasure law := hlaw
  have hY : Continuous Y := by
    dsimp [Y]
    fun_prop
  have hphi : ∀ u v : ℝ,
      (∫ w : ℝ × ℝ,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law) =
      ∫ x : ℝ,
        Complex.exp (((u * (Y x).1 + v * (Y x).2 : ℝ) : ℂ) * Complex.I) ∂nu := by
    intro u v
    have hk : Continuous (fun w : ℝ × ℝ =>
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I)) := by
      fun_prop
    exact integral_map hY.measurable.aemeasurable hk.aestronglyMeasurable
  have hfactor := normalized_iid_pair_characteristic_factor law n hn xi eta
  dsimp only at hfactor
  rw [hnormalized]
  simpa only [hphi] using hfactor

theorem normalized_iid_pair_weak_cramer_exponential_bound
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law]
    (n : ℕ) (hn : 1 ≤ n) (beta c R : ℝ)
    (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤
          1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta))
    (xi eta : ℝ)
    (hfreq : R < Real.sqrt
      ((xi / Real.sqrt (n : ℝ)) ^ 2 + (eta / Real.sqrt (n : ℝ)) ^ 2)) :
    let Q : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
    let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun z =>
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, z i
    let rho : Measure (ℝ × ℝ) := Q.map S
    ‖(∫ w : ℝ × ℝ,
      Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ ≤
        Real.exp (-(n : ℝ) * c * Real.rpow (Real.sqrt
          ((xi / Real.sqrt (n : ℝ)) ^ 2 + (eta / Real.sqrt (n : ℝ)) ^ 2)) (-beta)) := by
  dsimp only
  let phi : ℂ := ∫ w : ℝ × ℝ,
    Complex.exp ((((xi / Real.sqrt (n : ℝ)) * w.1 +
      (eta / Real.sqrt (n : ℝ)) * w.2 : ℝ) : ℂ) * Complex.I) ∂law
  let a : ℝ := c * Real.rpow (Real.sqrt
    ((xi / Real.sqrt (n : ℝ)) ^ 2 + (eta / Real.sqrt (n : ℝ)) ^ 2)) (-beta)
  have hbound : ‖phi‖ ≤ 1 - a :=
    hWC (xi / Real.sqrt (n : ℝ)) (eta / Real.sqrt (n : ℝ)) hfreq
  have hnorm : ‖phi‖ ≤ Real.exp (-a) := hbound.trans (by
    linarith [Real.add_one_le_exp (-a)])
  have hfactor := normalized_iid_pair_characteristic_factor law n hn xi eta
  dsimp only at hfactor
  rw [hfactor, norm_pow]
  change ‖phi‖ ^ n ≤ _
  calc
    ‖phi‖ ^ n ≤ (Real.exp (-a)) ^ n := pow_le_pow_left₀ (norm_nonneg _) hnorm n
    _ = Real.exp (-(n : ℝ) * c * Real.rpow (Real.sqrt
        ((xi / Real.sqrt (n : ℝ)) ^ 2 + (eta / Real.sqrt (n : ℝ)) ^ 2)) (-beta)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      dsimp [a]
      ring

end
end Shao.OQ3
