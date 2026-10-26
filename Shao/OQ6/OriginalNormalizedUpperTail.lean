import Shao.OQ6.OriginalSelfNormalizedTail
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.NormCast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Shao.OQ6.OriginalNormalizedUpperTail

noncomputable section

open MeasureTheory

theorem original_normalized_upper_tail
    (n : ℕ) (hn : 0 < n) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o : Ω, g o ∂μ) = 0)
    (hgsecond : (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1)
    (y : ℝ) (hy : (1 : ℝ) ≤ y) :
    (Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ).real
      {x : Fin n → Ω |
        Real.sqrt y * Real.rpow (n : ℝ) ((1 : ℝ) / 4) *
            ((4 : ℝ) + Real.sqrt
              (Shao.OQ6.OriginalGhostGoodEvent.sampleEnergy n g x / (n : ℝ))) <
          |Shao.OQ6.OriginalGhostGoodEvent.sampleSum n g x /
            Real.sqrt (n : ℝ)|} ≤
      (4 : ℝ) * Real.exp (-(y * Real.sqrt (n : ℝ)) / (2 : ℝ)) := by
  let M : Measure (Fin n → Ω) := Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ
  let r : ℝ := Real.sqrt (n : ℝ)
  let q : ℝ := Real.rpow (n : ℝ) ((1 : ℝ) / 4)
  let t : ℝ := Real.sqrt y * q
  let E : (Fin n → Ω) → ℝ := fun (x : Fin n → Ω) => Shao.OQ6.OriginalGhostGoodEvent.sampleEnergy n g x
  let S : (Fin n → Ω) → ℝ := fun (x : Fin n → Ω) => Shao.OQ6.OriginalGhostGoodEvent.sampleSum n g x
  let A : Set (Fin n → Ω) := {x : Fin n → Ω | t * ((4 : ℝ) + Real.sqrt (E x / (n : ℝ))) < |S x / r|}
  let B : Set (Fin n → Ω) := {x : Fin n → Ω | t * (Real.sqrt (E x) + (4 : ℝ) * r) < |S x|}
  have hNatOne : (1 : ℕ) ≤ n := by
    omega
  have hNpos : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hNnonneg : 0 ≤ (n : ℝ) := le_of_lt hNpos
  have hNge1 : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hNatOne
  have hy_nonneg : 0 ≤ y := by
    linarith only [hy]
  have hysqrt_ge_one : (1 : ℝ) ≤ Real.sqrt y := Real.one_le_sqrt.mpr hy
  have hq_ge_one : (1 : ℝ) ≤ q := by
    dsimp only [q]
    exact Real.one_le_rpow hNge1 (by norm_num)
  have ht : (1 : ℝ) ≤ t := by
    dsimp only [t]
    exact one_le_mul_of_one_le_of_one_le hysqrt_ge_one hq_ge_one
  have hrpos : 0 < r := by
    dsimp only [r]
    exact Real.sqrt_pos.mpr hNpos
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hq_square : q ^ (2 : ℕ) = r := by
    dsimp only [q, r]
    calc
      (Real.rpow (n : ℝ) ((1 : ℝ) / 4)) ^ (2 : ℕ) =
          Real.rpow (n : ℝ) (((1 : ℝ) / 4) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast hNnonneg ((1 : ℝ) / 4) 2).symm
      _ = Real.rpow (n : ℝ) ((1 : ℝ) / 2) := by norm_num
      _ = Real.sqrt (n : ℝ) := (Real.sqrt_eq_rpow (n : ℝ)).symm
  have hy_square : (Real.sqrt y) ^ (2 : ℕ) = y := Real.sq_sqrt hy_nonneg
  have ht_square : t ^ (2 : ℕ) = y * r := by
    dsimp only [t]
    calc
      (Real.sqrt y * q) ^ (2 : ℕ) =
          (Real.sqrt y) ^ (2 : ℕ) * q ^ (2 : ℕ) := by ring
      _ = y * r := by rw [hy_square, hq_square]
  have hE_div : ∀ (x : Fin n → Ω), Real.sqrt (E x / (n : ℝ)) = Real.sqrt (E x) / r := by
    intro x
    dsimp only [r]
    exact Real.sqrt_div' (E x) hNnonneg
  have hAbs_div : ∀ (x : Fin n → Ω), |S x / r| = |S x| / r := by
    intro x
    rw [abs_div, abs_of_pos hrpos]
  have hscale : ∀ (x : Fin n → Ω), (t * ((4 : ℝ) + Real.sqrt (E x) / r)) * r = t * (Real.sqrt (E x) + (4 : ℝ) * r) := by
    intro x
    field_simp [hrne] <;> ring
  have hpoint : ∀ (x : Fin n → Ω), x ∈ A ↔ x ∈ B := by
    intro x
    change t * ((4 : ℝ) + Real.sqrt (E x / (n : ℝ))) < |S x / r| ↔
      t * (Real.sqrt (E x) + (4 : ℝ) * r) < |S x|
    rw [hE_div x, hAbs_div x, lt_div_iff₀ hrpos, hscale x]
  have hevents : A = B := by
    ext x
    exact hpoint x
  have hmeasure : M.real A = M.real B :=
    congrArg (fun (a : Set (Fin n → Ω)) => M.real a) hevents
  have hproducer : M.real B ≤ (4 : ℝ) * Real.exp (-(t ^ (2 : ℕ)) / (2 : ℝ)) := by
    simpa only [M, B, E, S, r] using
      (Shao.OQ6.OriginalSelfNormalizedTail.original_selfnormalized_tail
        n μ g hg hg2 hgmean hgsecond t ht)
  have hexponent : -(t ^ (2 : ℕ)) / (2 : ℝ) = -(y * r) / (2 : ℝ) := by
    rw [ht_square]
  have hrhs : (4 : ℝ) * Real.exp (-(t ^ (2 : ℕ)) / (2 : ℝ)) = (4 : ℝ) * Real.exp (-(y * r) / (2 : ℝ)) := by
    rw [hexponent]
  change M.real A ≤ (4 : ℝ) * Real.exp (-(y * r) / (2 : ℝ))
  calc
    M.real A = M.real B := hmeasure
    _ ≤ (4 : ℝ) * Real.exp (-(t ^ (2 : ℕ)) / (2 : ℝ)) := hproducer
    _ = (4 : ℝ) * Real.exp (-(y * r) / (2 : ℝ)) := hrhs

end

end Shao.OQ6.OriginalNormalizedUpperTail
