import Shao.OQ3.JointNonlattice
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Shao.OQ3

open MeasureTheory
open scoped Matrix BigOperators

noncomputable section

private theorem affine_parabola_continuous
    (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) :
    Continuous (fun x : ℝ => A *ᵥ (![x, x ^ 2] - b)) := by
  apply continuous_pi
  intro i
  change Continuous (fun x : ℝ => ∑ j : Fin 2,
    A i j * ((![x, x ^ 2] : Fin 2 → ℝ) j - b j))
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  fun_prop

theorem affine_parabola_characteristic_factor (mu : Measure ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) (xi eta : ℝ) :
    let Y : ℝ → (Fin 2 → ℝ) := fun x => A *ᵥ (![x, x ^ 2] - b)
    let nu : Measure (Fin 2 → ℝ) := mu.map Y
    let xiA : ℝ := xi * A 0 0 + eta * A 1 0
    let etaA : ℝ := xi * A 0 1 + eta * A 1 1
    let phi : ℂ := ∫ y : Fin 2 → ℝ,
      Complex.exp (((xi * y 0 + eta * y 1 : ℝ) : ℂ) * Complex.I) ∂nu
    phi = Complex.exp (((-(xiA * b 0 + etaA * b 1) : ℝ) : ℂ) * Complex.I) *
      jointCharacteristic mu xiA etaA ∧
      ‖phi‖ = ‖jointCharacteristic mu xiA etaA‖ := by
  let Y : ℝ → (Fin 2 → ℝ) := fun x => A *ᵥ (![x, x ^ 2] - b)
  let nu : Measure (Fin 2 → ℝ) := mu.map Y
  let xiA : ℝ := xi * A 0 0 + eta * A 1 0
  let etaA : ℝ := xi * A 0 1 + eta * A 1 1
  let f : (Fin 2 → ℝ) → ℂ := fun y =>
    Complex.exp (((xi * y 0 + eta * y 1 : ℝ) : ℂ) * Complex.I)
  let phi : ℂ := ∫ y, f y ∂nu
  let k : ℂ :=
    Complex.exp (((-(xiA * b 0 + etaA * b 1) : ℝ) : ℂ) * Complex.I)
  change phi = k * jointCharacteristic mu xiA etaA ∧
    ‖phi‖ = ‖jointCharacteristic mu xiA etaA‖
  have hY : Continuous Y := affine_parabola_continuous A b
  have hf : Continuous f := by fun_prop
  have hmap : phi = ∫ x, f (Y x) ∂mu :=
    integral_map hY.measurable.aemeasurable hf.aestronglyMeasurable
  have hfun : (fun x => f (Y x)) = fun x => k * jointPhase xiA etaA x := by
    funext x
    have hlinear : xi * Y x 0 + eta * Y x 1 =
        xiA * x + etaA * x ^ 2 - (xiA * b 0 + etaA * b 1) := by
      dsimp [Y, xiA, etaA]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.sub_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      ring
    dsimp only [f, k, jointPhase]
    rw [hlinear, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfactor : phi = k * jointCharacteristic mu xiA etaA := by
    rw [hmap, hfun, integral_const_mul]
    rfl
  refine ⟨hfactor, ?_⟩
  rw [hfactor, norm_mul]
  have hk : ‖k‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  rw [hk, one_mul]

theorem uniform_weakCramer_of_affine_frequency_bounds
    {ι : Type*} (K : Set ι) (mu : ι → Measure ℝ)
    (hprob : ∀ p ∈ K, IsProbabilityMeasure (mu p))
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (b : ι → (Fin 2 → ℝ))
    (L U beta c R : ℝ) (hL : 0 < L) (hU : 0 < U) (hbeta : 0 ≤ beta)
    (hc : 0 < c) (hR : 0 ≤ R)
    (hfreq : ∀ p ∈ K, ∀ xi eta : ℝ,
      L * Real.sqrt (xi ^ 2 + eta ^ 2) ≤
          Real.sqrt ((xi * A p 0 0 + eta * A p 1 0) ^ 2 +
            (xi * A p 0 1 + eta * A p 1 1) ^ 2) ∧
        Real.sqrt ((xi * A p 0 0 + eta * A p 1 0) ^ 2 +
            (xi * A p 0 1 + eta * A p 1 1) ^ 2) ≤
          U * Real.sqrt (xi ^ 2 + eta ^ 2))
    (hWC : ∀ p ∈ K, ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu p) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    let Y : ι → ℝ → (Fin 2 → ℝ) := fun p x => A p *ᵥ (![x, x ^ 2] - b p)
    let nu : ι → Measure (Fin 2 → ℝ) := fun p => (mu p).map (Y p)
    let Phi : ι → ℝ → ℝ → ℂ := fun p xi eta =>
      ∫ y : Fin 2 → ℝ,
        Complex.exp (((xi * y 0 + eta * y 1 : ℝ) : ℂ) * Complex.I) ∂nu p
    let cA : ℝ := c * Real.rpow U (-beta)
    let RA : ℝ := R / L
    0 < cA ∧ 0 ≤ RA ∧
      ∀ p ∈ K, IsProbabilityMeasure (nu p) ∧
        ∀ xi eta : ℝ, RA < Real.sqrt (xi ^ 2 + eta ^ 2) →
          ‖Phi p xi eta‖ ≤
            1 - cA * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta) := by
  let Y : ι → ℝ → (Fin 2 → ℝ) := fun p x => A p *ᵥ (![x, x ^ 2] - b p)
  let nu : ι → Measure (Fin 2 → ℝ) := fun p => (mu p).map (Y p)
  let Phi : ι → ℝ → ℝ → ℂ := fun p xi eta =>
    ∫ y : Fin 2 → ℝ,
      Complex.exp (((xi * y 0 + eta * y 1 : ℝ) : ℂ) * Complex.I) ∂nu p
  let cA : ℝ := c * Real.rpow U (-beta)
  let RA : ℝ := R / L
  change 0 < cA ∧ 0 ≤ RA ∧ ∀ p ∈ K, IsProbabilityMeasure (nu p) ∧
    ∀ xi eta : ℝ, RA < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖Phi p xi eta‖ ≤
        1 - cA * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)
  have hcA : 0 < cA := mul_pos hc (Real.rpow_pos_of_pos hU _)
  have hRA : 0 ≤ RA := div_nonneg hR hL.le
  refine ⟨hcA, hRA, ?_⟩
  intro p hp
  letI : IsProbabilityMeasure (mu p) := hprob p hp
  have hY : Continuous (Y p) := affine_parabola_continuous (A p) (b p)
  have hnu : IsProbabilityMeasure (nu p) :=
    (Measure.isProbabilityMeasure_map_iff hY.measurable.aemeasurable).mpr
      inferInstance
  refine ⟨hnu, ?_⟩
  intro xi eta hout
  let r : ℝ := Real.sqrt (xi ^ 2 + eta ^ 2)
  let xiA : ℝ := xi * A p 0 0 + eta * A p 1 0
  let etaA : ℝ := xi * A p 0 1 + eta * A p 1 1
  let rA : ℝ := Real.sqrt (xiA ^ 2 + etaA ^ 2)
  have hr : 0 < r := lt_of_le_of_lt hRA hout
  have hRr : R < L * r := by
    have hh := (div_lt_iff₀ hL).mp (show R / L < r from hout)
    simpa [mul_comm] using hh
  have hbounds : L * r ≤ rA ∧ rA ≤ U * r := hfreq p hp xi eta
  have hRrA : R < rA := lt_of_lt_of_le hRr hbounds.1
  have hrA : 0 < rA := lt_of_le_of_lt hR hRrA
  have hpow : Real.rpow (U * r) (-beta) ≤ Real.rpow rA (-beta) :=
    Real.rpow_le_rpow_of_nonpos hrA hbounds.2 (neg_nonpos.mpr hbeta)
  have hcost : cA * Real.rpow r (-beta) ≤ c * Real.rpow rA (-beta) := by
    calc
      cA * Real.rpow r (-beta) = c * Real.rpow (U * r) (-beta) := by
        have hm : Real.rpow (U * r) (-beta) =
            Real.rpow U (-beta) * Real.rpow r (-beta) :=
          Real.mul_rpow hU.le hr.le
        rw [hm]
        simp only [cA, mul_assoc]
      _ ≤ c * Real.rpow rA (-beta) := mul_le_mul_of_nonneg_left hpow hc.le
  have hnorm : ‖Phi p xi eta‖ = ‖jointCharacteristic (mu p) xiA etaA‖ :=
    (affine_parabola_characteristic_factor (mu p) (A p) (b p) xi eta).2
  calc
    ‖Phi p xi eta‖ = ‖jointCharacteristic (mu p) xiA etaA‖ := hnorm
    _ ≤ 1 - c * Real.rpow rA (-beta) := hWC p hp xiA etaA hRrA
    _ ≤ 1 - cA * Real.rpow r (-beta) := sub_le_sub_left hcost 1

end

end Shao.OQ3
