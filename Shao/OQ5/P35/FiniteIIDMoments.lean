import Shao.OQ5.P35.RowIdentity
import Shao.Probability.FiniteIIDMoments

/-!
# Compatibility entry point for finite iid second-moment identities

The original definitions and theorem signatures are retained. Generic proofs
are implemented in `Shao.Probability.FiniteIIDMoments`.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

def finiteFeatureSum {m : ℕ} {Ω : Type*} (Z : Fin m → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin m, Z i ω

def finiteLeaveOwnSquareSum {m : ℕ} {Ω : Type*} (Z : Fin m → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin m, Z i ω ^ 2 * (finiteFeatureSum Z ω - Z i ω) ^ 2

def finitePairProductSum {m : ℕ} {Ω : Type*} (Z : Fin m → Ω → ℝ) (ω : Ω) : ℝ :=
  unorderedPairSum (fun i l => Z i ω * Z l ω)

section IID

variable {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [hμ : IsProbabilityMeasure μ]
variable {ν : Measure ℝ} [hν : IsProbabilityMeasure ν]
variable {Z : Fin m → Ω → ℝ}

include hμ hν

omit hμ hν in
theorem finite_iid_leaveOwnSquare_integrable
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) :
    Integrable (finiteLeaveOwnSquareSum Z) μ :=
  Shao.Probability.finite_iid_leaveOwnSquare_integrable hZ hIndep hLaw hν2

omit hμ hν in
theorem finite_iid_leaveOwnSquare_integral
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) :
    (∫ ω, finiteLeaveOwnSquareSum Z ω ∂μ) =
      (m : ℝ) * (∫ z, z ^ 2 ∂ν) *
        (((m - 1 : ℕ) : ℝ) * (∫ z, z ^ 2 ∂ν) +
          ((m - 1 : ℕ) : ℝ) * ((m - 2 : ℕ) : ℝ) * (∫ z, z ∂ν) ^ 2) :=
  Shao.Probability.finite_iid_leaveOwnSquare_integral hZ hIndep hLaw hν2

omit hμ hν in
theorem finite_iid_pairProduct_memLp_two
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) :
    MemLp (finitePairProductSum Z) 2 μ :=
  Shao.Probability.finite_iid_pairProduct_memLp_two hZ hIndep hLaw hν2

omit hμ hν in
theorem finite_iid_sumSquare_integral
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) :
    (∫ ω, finiteFeatureSum Z ω ^ 2 ∂μ) =
      (m : ℝ) * (∫ z, z ^ 2 ∂ν) +
        (m : ℝ) * ((m - 1 : ℕ) : ℝ) * (∫ z, z ∂ν) ^ 2 :=
  Shao.Probability.finite_iid_sumSquare_integral hZ hIndep hLaw hν2

omit hμ hν in
theorem finite_iid_pairProduct_integral
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) :
    (∫ ω, finitePairProductSum Z ω ∂μ) = (m.choose 2 : ℝ) * (∫ z, z ∂ν) ^ 2 :=
  Shao.Probability.finite_iid_pairProduct_integral hZ hIndep hLaw hν2

omit hμ hν in
theorem finite_iid_pairProduct_variance
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
    (hν2 : MemLp (id : ℝ → ℝ) 2 ν) :
    variance (finitePairProductSum Z) μ =
      (m.choose 2 : ℝ) * (variance (id : ℝ → ℝ) ν) ^ 2 +
        (m : ℝ) * (((m - 1 : ℕ) : ℝ) ^ 2) *
          (∫ z, z ∂ν) ^ 2 * variance (id : ℝ → ℝ) ν :=
  Shao.Probability.finite_iid_pairProduct_variance hZ hIndep hLaw hν2

end IID

end

end Shao.OQ5.P35
