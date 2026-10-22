# Frozen complete declarations and original-source translation

CORRECT / LEAN_FULLY_CHECKED for all exact component contracts below.

Exactly8 complete public theorem types and2 exact definition bodies.

## Unit75

Exact pre-code freeze SHA2565d0cea718f2a52c0efe886a2153571c51ae048ef0f59912ef218fc7bdbbfeb79; never-author ORIGINAL-source CORRECT
report SHA256b5d13f6efbefd9708e8fda9dfe57a636ee880c75beab4be6fb8e6133d9f3c6b5, fully lead-read BEFORE implementation.

```lean
import Shao.OQ5.P52.FixedLayerErasedEdgeMoments
import Shao.OQ5.P52.FixedLayerErasedNoise

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem fixedErasedSampleNoise_memLp_two (j n : ℕ) (i : Fin n) :
    MemLp (fun x : Fin n → LayerObs => (x i).1) 2
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j))

theorem integral_fixedErasedSampleNoise_eq_zero (j n : ℕ) (i : Fin n) :
    (∫ x : Fin n → LayerObs, (x i).1
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0

theorem integral_fixedErasedSampleNoise_mul (j n : ℕ) (i k : Fin n) :
    (∫ x : Fin n → LayerObs, (x i).1 * (x k).1
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      if i = k then (1 / 3 : ℝ) else 0

theorem integrable_fixedErasedSampleNoise_mul_residualEdge
    (j n : ℕ) (i a b : Fin n) (hab : a ≠ b) :
    Integrable (fun x : Fin n → LayerObs =>
      (x i).1 * fixedResidualKernel (x a, x b))
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j))

theorem integral_fixedErasedSampleNoise_mul_residualEdge
    (j n : ℕ) (i a b : Fin n) (hab : a ≠ b) :
    (∫ x : Fin n → LayerObs,
      (x i).1 * fixedResidualKernel (x a, x b)
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0

end
end Shao.OQ5.P52
```

## Unit76

Exact pre-code freeze SHA256090ff78b5de0ad41d8daf61bd93fa01c0acf73550f6318277001b6a1d19f2792; never-author ORIGINAL-source CORRECT
report SHA2562768a5e585a36c8b3c88eafa04c84c1515275bd32867c34e39764b5da324e663, fully lead-read BEFORE implementation.

```lean
import Shao.OQ5.P52.FixedLayerErasedRowMoments
import Shao.OQ5.P52.FixedLayerErasedPairMoments
import Shao.OQ6.FiniteRows

open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

def fixedSampleU {n : ℕ} (x : Fin n → LayerObs) : ℝ :=
  Shao.OQ6.FiniteRows.uStatistic (fun i k => fixedKernel (x i, x k))

def fixedSampleStudentizerSq {n : ℕ} (x : Fin n → LayerObs) : ℝ :=
  Shao.OQ6.FiniteRows.jackknifeSq (fun i k => fixedKernel (x i, x k))

theorem fixedSampleU_eq_noise_add_residual
    (n : ℕ) (hn : 3 ≤ n) (x : Fin n → LayerObs) :
    fixedSampleU x = (2 / (n : ℝ)) * (∑ i : Fin n, (x i).1) +
      (n.choose 2 : ℝ)⁻¹ * fixedErasedResidualPairSum x

theorem fixedSampleStudentizerSq_nonneg
    (n : ℕ) (hn : 3 ≤ n) (x : Fin n → LayerObs) :
    0 ≤ fixedSampleStudentizerSq x

theorem fixedSampleStudentizerSq_eq_centered_residual_rows
    (n : ℕ) (hn : 3 ≤ n) (x : Fin n → LayerObs) :
    fixedSampleStudentizerSq x = (4 / ((n : ℝ) - 1)) *
      ∑ i : Fin n,
        (Shao.OQ5.P35.center
          (fun k : Fin n =>
            (x k).1 + fixedErasedResidualRow k x / ((n : ℝ) - 2)) i) ^ 2

end
end Shao.OQ5.P52
```

Unit75 uses the honest finite-beta-product law, genuine scalar/edge L2 and
Holder L1 before integral calculations. Full grouped independence handles
outside indices; both endpoints use actual canonical rows and honest Fubini.
Unit76 preserves original unordered U and actual sample-centered jackknife R²,
all-sample/off-mask scope, exact n>=3 and real cast-before-subtraction factors.
Only generic P35 counting/center is reused. No diagonal L2, fourth moment,
independent residual rows, PSD/rank or positive variance assumption is added.

Original p50 SHA256de553dc827eeadbc1e863c1778caa9bdeb00bca84110b4666b06cab053d7b768;
p52 SHA256615209f8501e14a6bfaee220899c30891510fef5987c9abf7f74ac52b6538b45.
Actual conditional U/R moments, selected-layer cancellation, strictR positivity,
ratios/tails, real coding and fullp52/p53/OQ6/RS2 remain OPEN.
