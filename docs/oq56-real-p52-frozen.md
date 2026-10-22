# Same fixed real p52 root — complete frozen interfaces

All nine exact interfaces have full independent and lead acceptance. Packaging uses the existing evidence without replaying Lean gates.

Stack base: frozen PR122 /67e965b45856e9a21866126517584995bea3ece7. Only 9 new Lean sources and 3 new documentation files are intended.96 is excluded.

| Unit | Module | Source SHA256 | Bytes | Theorems | Definitions |
|---:|---|---|---:|---:|---:|
| 87 | `FixedLayerRealSample` | `a4096138aa180a6bc58e9bcde855048d564caec803de6bc901bc8abbae89b7bb` | 5818 | 13 | 4 |
| 88 | `FixedLayerRealStatistics` | `c62c79c4500c9227d383eb1d1dc60bfa8cbac097502085355210e73bc2d909b1` | 7178 | 13 | 5 |
| 89 | `FixedLayerRealProjection` | `a0cc319d92504180479bf156ee5fab4b626ee412a0ec8567c90e5a37bc4e8870` | 11140 | 16 | 1 |
| 90 | `FixedLayerRealMoments` | `6d0c17327b57f80abcb5e884f80d2541efffd85c7d9a810f14301f4e07cdc51c` | 4657 | 4 | 0 |
| 91 | `FixedLayerRealCanonical` | `cc947859493d456305973bda7281d6dc58653cf158ab833f63516a825cafc3c8` | 9527 | 11 | 2 |
| 92 | `FixedLayerRealNormalization` | `e001096fc0a940e6ec44e7f5af8742600cacd674c2bdca759addef104c37a137` | 12810 | 22 | 3 |
| 93 | `FixedLayerNormalizedRealStatistics` | `bcd938f83aa37b0c46bb2e9577e38f099056049cc245effa8c802f90801befc7` | 9480 | 16 | 6 |
| 94 | `FixedLayerNormalizedRealTailLimits` | `fa8694daaa6dcd0ed13d50b5751f629bfecd3be78711c7c876e2a2d5d98a3ea4` | 3340 | 7 | 0 |
| 95 | `FixedLayerRealCounterexample` | `a84167ac661a3ef33d34499502f42ed0535f105c978ddfd1d5e46f30728e77ac` | 15831 | 2 | 1 |

Each source is the exact stopped source already quoted in its full review. The complete frozen types/bodies and transitive-axiom evidence belong to the frozen unit artifacts; the source files provide the reviewable implementations. The98conjuncts of FixedP52Counterexample remain one public Prop definition.

## Unit87 public declarations

Definitions: `fixedRealObservationLaw`, `fixedRealKernel`, `fixedRealSampleLaw`, `fixedRealSampleCoordinate`.

Theorems: `fixedRealObservationLaw_isProbabilityMeasure`, `measurable_fixedRealKernel`, `fixedRealKernel_symmetric`, `fixedRealKernel_encode`, `fixedRealObservationLaw_decode`, `fixedRealSampleLaw_isProbabilityMeasure`, `measurable_fixedRealSampleCoordinate`, `map_fixedRealSampleCoordinate`, `iIndepFun_fixedRealSampleCoordinate`, `map_fixedRealSampleCoordinate_pair`, `map_fixedRealSamplePrefix`, `fixedRealSampleLaw_decode`, `fixedRealSampleLaw_ae_image`.

## Unit88 public declarations

Definitions: `fixedRealSampleU`, `fixedRealSampleStudentizerSq`, `fixedRealSampleStudentizer`, `fixedRealSampleStudentized`, `fixedRealSampleStudentizedTailProbability`.

Theorems: `measurable_fixedRealSampleU`, `measurable_fixedRealSampleStudentizerSq`, `measurable_fixedRealSampleStudentizer`, `measurable_fixedRealSampleStudentized`, `measurable_fixedRealSampleStudentized_sample`, `fixedRealSampleU_encode`, `fixedRealSampleStudentizerSq_encode`, `fixedRealSampleStudentizer_encode`, `fixedRealSampleStudentized_encode`, `fixedRealSampleStudentizer_prefix_pos_ae`, `fixedRealSampleStudentizedTailProbability_eq`, `fixedRealSampleStudentizedTailProbability_nonneg`, `fixedRealSampleStudentizedTailProbability_le_one`.

## Unit89 public declarations

Definitions: `fixedRealFirstProjection`.

Theorems: `measurable_fixedRealFirstProjection`, `fixedRealKernel_memLp`, `integrable_fixedRealKernel`, `integrable_fixedRealKernel_sq`, `integrable_fixedRealKernel_row_ae`, `fixedRealFirstProjection_encode_ae`, `fixedRealFirstProjection_ae_eq_decoded_first`, `integral_fixedRealKernel_eq_zero`, `fixedRealFirstProjection_memLp_two`, `integrable_fixedRealFirstProjection`, `integrable_fixedRealFirstProjection_sq`, `integral_fixedRealFirstProjection_eq_zero`, `integral_fixedRealFirstProjection_sq`, `map_fixedRealFirstProjection`, `fixedRealFirstProjection_abs_le_one_ae`, `fixedRealFirstProjection_indep_categories`.

## Unit90 public declarations

Definitions: none.

Theorems: `integrable_fixedRealKernel_abs_pow`, `integrable_fixedRealKernel_subcritical_exp`, `lintegral_fixedRealKernel_critical_exp_eq_top`, `not_integrable_fixedRealKernel_critical_exp`.

## Unit91 public declarations

Definitions: `fixedRealCanonicalResidual`, `fixedCategoryResidualKernel`.

Theorems: `measurable_fixedRealCanonicalResidual`, `measurable_fixedCategoryResidualKernel`, `fixedCategoryResidualKernel_symmetric`, `fixedResidualKernel_eq_categoryResidual`, `fixedRealCanonicalResidual_symmetric`, `fixedRealKernel_hoeffding`, `fixedRealCanonicalResidual_memLp_two`, `integrable_fixedRealCanonicalResidual`, `integrable_fixedRealCanonicalResidual_row_ae`, `integral_fixedRealCanonicalResidual_row_eq_zero_ae`, `fixedRealCanonicalResidual_ae_eq_categoryResidual`.

## Unit92 public declarations

Definitions: `fixedNormalizedRealKernel`, `fixedNormalizedRealFirstProjection`, `fixedNormalizedRealCanonicalResidual`.

Theorems: `measurable_fixedNormalizedRealKernel`, `fixedNormalizedRealKernel_symmetric`, `fixedNormalizedRealKernel_memLp`, `integrable_fixedNormalizedRealKernel`, `integral_fixedNormalizedRealKernel_eq_zero`, `fixedNormalizedRealFirstProjection_eq`, `measurable_fixedNormalizedRealFirstProjection`, `fixedNormalizedRealFirstProjection_memLp_two`, `integral_fixedNormalizedRealFirstProjection_eq_zero`, `integral_fixedNormalizedRealFirstProjection_sq`, `fixedNormalizedRealFirstProjection_abs_le_sqrt_three_ae`, `map_fixedNormalizedRealFirstProjection`, `fixedNormalizedRealFirstProjection_indep_categories`, `fixedNormalizedRealCanonicalResidual_eq`, `fixedNormalizedRealCanonicalResidual_memLp_two`, `integrable_fixedNormalizedRealCanonicalResidual_row_ae`, `integral_fixedNormalizedRealCanonicalResidual_row_eq_zero_ae`, `fixedNormalizedRealCanonicalResidual_ae_eq_categoryResidual`, `integrable_fixedNormalizedRealKernel_abs_pow`, `integrable_fixedNormalizedRealKernel_subcritical_exp`, `lintegral_fixedNormalizedRealKernel_critical_exp_eq_top`, `not_integrable_fixedNormalizedRealKernel_critical_exp`.

## Unit93 public declarations

Definitions: `fixedNormalizedRealSampleU`, `fixedNormalizedRealSampleRowMean`, `fixedNormalizedRealSampleStudentizerSq`, `fixedNormalizedRealSampleStudentizer`, `fixedNormalizedRealSampleStudentized`, `fixedNormalizedRealSampleStudentizedTailProbability`.

Theorems: `measurable_fixedNormalizedRealSampleU`, `measurable_fixedNormalizedRealSampleRowMean`, `measurable_fixedNormalizedRealSampleStudentizerSq`, `measurable_fixedNormalizedRealSampleStudentizer`, `measurable_fixedNormalizedRealSampleStudentized`, `measurable_fixedNormalizedRealSampleStudentized_sample`, `fixedNormalizedRealSampleU_eq`, `fixedNormalizedRealSampleRowMean_eq`, `fixedNormalizedRealSampleStudentizerSq_eq`, `fixedNormalizedRealSampleStudentizer_eq`, `fixedNormalizedRealSampleStudentized_eq`, `fixedNormalizedRealSampleStudentizer_prefix_pos_ae`, `fixedNormalizedRealSampleStudentizedTailProbability_eq_real`, `fixedNormalizedRealSampleStudentizedTailProbability_eq`, `fixedNormalizedRealSampleStudentizedTailProbability_nonneg`, `fixedNormalizedRealSampleStudentizedTailProbability_le_one`.

## Unit94 public declarations

Definitions: none.

Theorems: `fixedNormalizedRealSampleStudentizedTailProbability_ge_quarter_exp_eventually`, `fixedNormalizedRealSampleStudentizedTailProbability_eventually_pos`, `fixedNormalizedRealLayer_log_tail_ratio_tendsto_zero`, `fixedNormalizedRealLayer_relative_tail_ratio_tendsto_atTop`, `fixedNormalizedRealLayer_full_log_tail_ratio_not_tendsto_one`, `fixedNormalizedRealLayer_full_relative_tail_ratio_not_tendsto_one`, `fixedNormalizedRealLayer_uniform_relative_tail_window_fails`.

## Unit95 public declarations

Definitions: `FixedP52Counterexample`.

Theorems: `fixedP52Counterexample`, `exists_fixedP52Counterexample`.


## Complete frozen interfaces

These are the exact complete definition bodies and theorem types frozen before implementation. Theorem entries are interface transcripts; their implementations are in the nine Lean source files. Context imports, namespaces and local notation are reproduced with each interface.

### Unit 87

```lean
import Shao.OQ5.P52.FixedLayerSample
import Shao.OQ5.P50.LayeredRealTransport

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

def fixedRealObservationLaw : Measure ℝ :=
  Shao.OQ5.P50.layerRealLaw fixedObservationLaw

def fixedRealKernel : ℝ × ℝ → ℝ :=
  Shao.OQ5.P50.layerRealKernel fixedKernel

def fixedRealSampleLaw : Measure (ℕ → ℝ) :=
  fixedSampleLaw.map
    (fun ω : ℕ → LayerObs => fun i : ℕ => Shao.OQ5.P50.layerEncode (ω i))

def fixedRealSampleCoordinate (i : ℕ) (ξ : ℕ → ℝ) : ℝ := ξ i

theorem fixedRealObservationLaw_isProbabilityMeasure :
    IsProbabilityMeasure fixedRealObservationLaw

theorem measurable_fixedRealKernel : Measurable fixedRealKernel

theorem fixedRealKernel_symmetric (x y : ℝ) :
    fixedRealKernel (x, y) = fixedRealKernel (y, x)

theorem fixedRealKernel_encode (o o' : LayerObs) :
    fixedRealKernel
      (Shao.OQ5.P50.layerEncode o, Shao.OQ5.P50.layerEncode o') =
        fixedKernel (o, o')

theorem fixedRealObservationLaw_decode :
    fixedRealObservationLaw.map Shao.OQ5.P50.layerDecode = fixedObservationLaw

theorem fixedRealSampleLaw_isProbabilityMeasure :
    IsProbabilityMeasure fixedRealSampleLaw

theorem measurable_fixedRealSampleCoordinate (i : ℕ) :
    Measurable (fixedRealSampleCoordinate i)

theorem map_fixedRealSampleCoordinate (i : ℕ) :
    fixedRealSampleLaw.map (fixedRealSampleCoordinate i) = fixedRealObservationLaw

theorem iIndepFun_fixedRealSampleCoordinate :
    ProbabilityTheory.iIndepFun fixedRealSampleCoordinate fixedRealSampleLaw

theorem map_fixedRealSampleCoordinate_pair (i j : ℕ) (hij : i ≠ j) :
    fixedRealSampleLaw.map
      (fun ξ => (fixedRealSampleCoordinate i ξ, fixedRealSampleCoordinate j ξ)) =
        fixedRealObservationLaw.prod fixedRealObservationLaw

theorem map_fixedRealSamplePrefix (n : ℕ) :
    fixedRealSampleLaw.map
      (fun ξ (i : Fin n) => fixedRealSampleCoordinate i.val ξ) =
        Measure.pi (fun _ : Fin n => fixedRealObservationLaw)

theorem fixedRealSampleLaw_decode :
    fixedRealSampleLaw.map
      (fun ξ : ℕ → ℝ => fun i : ℕ => Shao.OQ5.P50.layerDecode (ξ i)) =
        fixedSampleLaw

theorem fixedRealSampleLaw_ae_image :
    ∀ᵐ ξ ∂fixedRealSampleLaw,
      ∀ i : ℕ, ξ i ∈ Shao.OQ5.P50.layerEncodedSet

end
end Shao.OQ5.P52
```

### Unit 88

```lean
import Shao.OQ5.P52.FixedLayerRealSample
import Shao.OQ5.P52.FixedLayerStudentizedTail

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

def fixedRealSampleU {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Shao.OQ6.FiniteRows.uStatistic (fun i k => fixedRealKernel (x i, x k))

def fixedRealSampleStudentizerSq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Shao.OQ6.FiniteRows.jackknifeSq (fun i k => fixedRealKernel (x i, x k))

def fixedRealSampleStudentizer {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (fixedRealSampleStudentizerSq x)

def fixedRealSampleStudentized {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (n : ℝ) * fixedRealSampleU x / fixedRealSampleStudentizer x

def fixedRealSampleStudentizedTailProbability (n : ℕ) (x : ℝ) : ℝ :=
  fixedRealSampleLaw.real
    {ξ : ℕ → ℝ |
      x ≤ fixedRealSampleStudentized
        (fun i : Fin n => fixedRealSampleCoordinate i.val ξ)}

theorem measurable_fixedRealSampleU (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => fixedRealSampleU x)

theorem measurable_fixedRealSampleStudentizerSq (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => fixedRealSampleStudentizerSq x)

theorem measurable_fixedRealSampleStudentizer (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => fixedRealSampleStudentizer x)

theorem measurable_fixedRealSampleStudentized (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => fixedRealSampleStudentized x)

theorem measurable_fixedRealSampleStudentized_sample (n : ℕ) :
    Measurable (fun ξ : ℕ → ℝ =>
      fixedRealSampleStudentized
        (fun i : Fin n => fixedRealSampleCoordinate i.val ξ))

theorem fixedRealSampleU_encode (n : ℕ) (x : Fin n → LayerObs) :
    fixedRealSampleU (fun i => Shao.OQ5.P50.layerEncode (x i)) = fixedSampleU x

theorem fixedRealSampleStudentizerSq_encode (n : ℕ) (x : Fin n → LayerObs) :
    fixedRealSampleStudentizerSq (fun i => Shao.OQ5.P50.layerEncode (x i)) =
      fixedSampleStudentizerSq x

theorem fixedRealSampleStudentizer_encode (n : ℕ) (x : Fin n → LayerObs) :
    fixedRealSampleStudentizer (fun i => Shao.OQ5.P50.layerEncode (x i)) =
      fixedSampleStudentizer x

theorem fixedRealSampleStudentized_encode (n : ℕ) (x : Fin n → LayerObs) :
    fixedRealSampleStudentized (fun i => Shao.OQ5.P50.layerEncode (x i)) =
      fixedSampleStudentized x

theorem fixedRealSampleStudentizer_prefix_pos_ae (n : ℕ) (hn : 3 ≤ n) :
    ∀ᵐ ξ ∂fixedRealSampleLaw,
      0 < fixedRealSampleStudentizer
        (fun i : Fin n => fixedRealSampleCoordinate i.val ξ)

theorem fixedRealSampleStudentizedTailProbability_eq (n : ℕ) (x : ℝ) :
    fixedRealSampleStudentizedTailProbability n x =
      fixedSampleStudentizedTailProbability n x

theorem fixedRealSampleStudentizedTailProbability_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ fixedRealSampleStudentizedTailProbability n x

theorem fixedRealSampleStudentizedTailProbability_le_one (n : ℕ) (x : ℝ) :
    fixedRealSampleStudentizedTailProbability n x ≤ 1

end
end Shao.OQ5.P52
```

### Unit 89

```lean
import Shao.OQ5.P52.FixedLayerRealSample
import Shao.OQ5.P52.FixedLayerProjection

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

def fixedRealFirstProjection (x : ℝ) : ℝ :=
  ∫ y : ℝ, fixedRealKernel (x, y) ∂fixedRealObservationLaw

theorem measurable_fixedRealFirstProjection :
    Measurable fixedRealFirstProjection

theorem fixedRealKernel_memLp (ν : ℝ) (hν : 1 ≤ ν) :
    MemLp fixedRealKernel (ENNReal.ofReal ν)
      (fixedRealObservationLaw.prod fixedRealObservationLaw)

theorem integrable_fixedRealKernel :
    Integrable fixedRealKernel
      (fixedRealObservationLaw.prod fixedRealObservationLaw)

theorem integrable_fixedRealKernel_sq :
    Integrable (fun z : ℝ × ℝ => fixedRealKernel z ^ 2)
      (fixedRealObservationLaw.prod fixedRealObservationLaw)

theorem integrable_fixedRealKernel_row_ae :
    ∀ᵐ x : ℝ ∂fixedRealObservationLaw,
      Integrable (fun y : ℝ => fixedRealKernel (x, y)) fixedRealObservationLaw

theorem fixedRealFirstProjection_encode_ae :
    ∀ᵐ o : LayerObs ∂fixedObservationLaw,
      fixedRealFirstProjection (Shao.OQ5.P50.layerEncode o) = fixedFirstProjection o

theorem fixedRealFirstProjection_ae_eq_decoded_first :
    fixedRealFirstProjection =ᵐ[fixedRealObservationLaw]
      (fun x : ℝ => (Shao.OQ5.P50.layerDecode x).1)

theorem integral_fixedRealKernel_eq_zero :
    (∫ z : ℝ × ℝ, fixedRealKernel z
      ∂fixedRealObservationLaw.prod fixedRealObservationLaw) = 0

theorem fixedRealFirstProjection_memLp_two :
    MemLp fixedRealFirstProjection 2 fixedRealObservationLaw

theorem integrable_fixedRealFirstProjection :
    Integrable fixedRealFirstProjection fixedRealObservationLaw

theorem integrable_fixedRealFirstProjection_sq :
    Integrable (fun x : ℝ => fixedRealFirstProjection x ^ 2) fixedRealObservationLaw

theorem integral_fixedRealFirstProjection_eq_zero :
    (∫ x : ℝ, fixedRealFirstProjection x ∂fixedRealObservationLaw) = 0

theorem integral_fixedRealFirstProjection_sq :
    (∫ x : ℝ, fixedRealFirstProjection x ^ 2 ∂fixedRealObservationLaw) = (1 / 3 : ℝ)

theorem map_fixedRealFirstProjection :
    fixedRealObservationLaw.map fixedRealFirstProjection = Shao.OQ5.P50.layerNoiseLaw

theorem fixedRealFirstProjection_abs_le_one_ae :
    ∀ᵐ x : ℝ ∂fixedRealObservationLaw, |fixedRealFirstProjection x| ≤ 1

theorem fixedRealFirstProjection_indep_categories :
    ProbabilityTheory.IndepFun fixedRealFirstProjection
      (fun x : ℝ => (Shao.OQ5.P50.layerDecode x).2) fixedRealObservationLaw

end
end Shao.OQ5.P52
```

### Unit 90

```lean
import Shao.OQ5.P52.FixedLayerRealProjection
import Shao.OQ5.P52.FixedLayerCriticalDivergence

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

theorem integrable_fixedRealKernel_abs_pow (m : ℕ) :
    Integrable (fun z : ℝ × ℝ => |fixedRealKernel z| ^ m)
      (fixedRealObservationLaw.prod fixedRealObservationLaw)

theorem integrable_fixedRealKernel_subcritical_exp (η lambda : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 5) (hlambda : 0 < lambda) :
    Integrable (fun z : ℝ × ℝ => Real.exp (lambda * |fixedRealKernel z| ^ η))
      (fixedRealObservationLaw.prod fixedRealObservationLaw)

theorem lintegral_fixedRealKernel_critical_exp_eq_top
    (lambda : ℝ) (hlambda : 0 < lambda) :
    (∫⁻ z : ℝ × ℝ,
      ENNReal.ofReal (Real.exp (lambda * |fixedRealKernel z| ^ (1 / 5 : ℝ)))
      ∂fixedRealObservationLaw.prod fixedRealObservationLaw) = ⊤

theorem not_integrable_fixedRealKernel_critical_exp
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ¬ Integrable (fun z : ℝ × ℝ =>
      Real.exp (lambda * |fixedRealKernel z| ^ (1 / 5 : ℝ)))
      (fixedRealObservationLaw.prod fixedRealObservationLaw)

end
end Shao.OQ5.P52
```

### Unit 91

```lean
import Shao.OQ5.P52.FixedLayerRealProjection

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

def fixedRealCanonicalResidual (z : ℝ × ℝ) : ℝ :=
  fixedRealKernel z - fixedRealFirstProjection z.1 - fixedRealFirstProjection z.2

def fixedCategoryResidualKernel (z : (ℕ → Fin 3) × (ℕ → Fin 3)) : ℝ :=
  fixedResidualKernel ((0, z.1), (0, z.2))

theorem measurable_fixedRealCanonicalResidual :
    Measurable fixedRealCanonicalResidual

theorem measurable_fixedCategoryResidualKernel :
    Measurable fixedCategoryResidualKernel

theorem fixedCategoryResidualKernel_symmetric (c d : ℕ → Fin 3) :
    fixedCategoryResidualKernel (c, d) = fixedCategoryResidualKernel (d, c)

theorem fixedResidualKernel_eq_categoryResidual (o o' : LayerObs) :
    fixedResidualKernel (o, o') = fixedCategoryResidualKernel (o.2, o'.2)

theorem fixedRealCanonicalResidual_symmetric (x y : ℝ) :
    fixedRealCanonicalResidual (x, y) = fixedRealCanonicalResidual (y, x)

theorem fixedRealKernel_hoeffding (x y : ℝ) :
    fixedRealKernel (x, y) = fixedRealFirstProjection x +
      fixedRealFirstProjection y + fixedRealCanonicalResidual (x, y)

theorem fixedRealCanonicalResidual_memLp_two :
    MemLp fixedRealCanonicalResidual 2
      (fixedRealObservationLaw.prod fixedRealObservationLaw)

theorem integrable_fixedRealCanonicalResidual :
    Integrable fixedRealCanonicalResidual
      (fixedRealObservationLaw.prod fixedRealObservationLaw)

theorem integrable_fixedRealCanonicalResidual_row_ae :
    ∀ᵐ x : ℝ ∂fixedRealObservationLaw,
      Integrable (fun y : ℝ => fixedRealCanonicalResidual (x, y))
        fixedRealObservationLaw

theorem integral_fixedRealCanonicalResidual_row_eq_zero_ae :
    ∀ᵐ x : ℝ ∂fixedRealObservationLaw,
      (∫ y : ℝ, fixedRealCanonicalResidual (x, y)
        ∂fixedRealObservationLaw) = 0

theorem fixedRealCanonicalResidual_ae_eq_categoryResidual :
    fixedRealCanonicalResidual =ᵐ[fixedRealObservationLaw.prod fixedRealObservationLaw]
      (fun z : ℝ × ℝ => fixedCategoryResidualKernel
        ((Shao.OQ5.P50.layerDecode z.1).2,
          (Shao.OQ5.P50.layerDecode z.2).2))

end
end Shao.OQ5.P52
```

### Unit 92

```lean
import Shao.OQ5.P52.FixedLayerRealMoments
import Shao.OQ5.P52.FixedLayerRealCanonical

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

def fixedNormalizedRealKernel (z : ℝ × ℝ) : ℝ :=
  Real.sqrt 3 * fixedRealKernel z

def fixedNormalizedRealFirstProjection (x : ℝ) : ℝ :=
  ∫ y : ℝ, fixedNormalizedRealKernel (x, y) ∂fixedRealObservationLaw

def fixedNormalizedRealCanonicalResidual (z : ℝ × ℝ) : ℝ :=
  fixedNormalizedRealKernel z - fixedNormalizedRealFirstProjection z.1 -
    fixedNormalizedRealFirstProjection z.2

theorem measurable_fixedNormalizedRealKernel :
    Measurable fixedNormalizedRealKernel

theorem fixedNormalizedRealKernel_symmetric (x y : ℝ) :
    fixedNormalizedRealKernel (x, y) = fixedNormalizedRealKernel (y, x)

theorem fixedNormalizedRealKernel_memLp (ν : ℝ) (hν : 1 ≤ ν) :
    MemLp fixedNormalizedRealKernel (ENNReal.ofReal ν)
      (fixedRealObservationLaw.prod fixedRealObservationLaw)

theorem integrable_fixedNormalizedRealKernel :
    Integrable fixedNormalizedRealKernel
      (fixedRealObservationLaw.prod fixedRealObservationLaw)

theorem integral_fixedNormalizedRealKernel_eq_zero :
    (∫ z : ℝ × ℝ, fixedNormalizedRealKernel z
      ∂fixedRealObservationLaw.prod fixedRealObservationLaw) = 0

theorem fixedNormalizedRealFirstProjection_eq (x : ℝ) :
    fixedNormalizedRealFirstProjection x = Real.sqrt 3 * fixedRealFirstProjection x

theorem measurable_fixedNormalizedRealFirstProjection :
    Measurable fixedNormalizedRealFirstProjection

theorem fixedNormalizedRealFirstProjection_memLp_two :
    MemLp fixedNormalizedRealFirstProjection 2 fixedRealObservationLaw

theorem integral_fixedNormalizedRealFirstProjection_eq_zero :
    (∫ x : ℝ, fixedNormalizedRealFirstProjection x ∂fixedRealObservationLaw) = 0

theorem integral_fixedNormalizedRealFirstProjection_sq :
    (∫ x : ℝ, fixedNormalizedRealFirstProjection x ^ 2
      ∂fixedRealObservationLaw) = 1

theorem fixedNormalizedRealFirstProjection_abs_le_sqrt_three_ae :
    ∀ᵐ x : ℝ ∂fixedRealObservationLaw,
      |fixedNormalizedRealFirstProjection x| ≤ Real.sqrt 3

theorem map_fixedNormalizedRealFirstProjection :
    fixedRealObservationLaw.map fixedNormalizedRealFirstProjection =
      Shao.OQ5.P50.layerNoiseLaw.map (fun t : ℝ => Real.sqrt 3 * t)

theorem fixedNormalizedRealFirstProjection_indep_categories :
    ProbabilityTheory.IndepFun fixedNormalizedRealFirstProjection
      (fun x : ℝ => (Shao.OQ5.P50.layerDecode x).2) fixedRealObservationLaw

theorem fixedNormalizedRealCanonicalResidual_eq (z : ℝ × ℝ) :
    fixedNormalizedRealCanonicalResidual z = Real.sqrt 3 * fixedRealCanonicalResidual z

theorem fixedNormalizedRealCanonicalResidual_memLp_two :
    MemLp fixedNormalizedRealCanonicalResidual 2
      (fixedRealObservationLaw.prod fixedRealObservationLaw)

theorem integrable_fixedNormalizedRealCanonicalResidual_row_ae :
    ∀ᵐ x : ℝ ∂fixedRealObservationLaw,
      Integrable (fun y : ℝ => fixedNormalizedRealCanonicalResidual (x, y))
        fixedRealObservationLaw

theorem integral_fixedNormalizedRealCanonicalResidual_row_eq_zero_ae :
    ∀ᵐ x : ℝ ∂fixedRealObservationLaw,
      (∫ y : ℝ, fixedNormalizedRealCanonicalResidual (x, y)
        ∂fixedRealObservationLaw) = 0

theorem fixedNormalizedRealCanonicalResidual_ae_eq_categoryResidual :
    fixedNormalizedRealCanonicalResidual =ᵐ[fixedRealObservationLaw.prod fixedRealObservationLaw]
      (fun z : ℝ × ℝ => Real.sqrt 3 * fixedCategoryResidualKernel
        ((Shao.OQ5.P50.layerDecode z.1).2,
          (Shao.OQ5.P50.layerDecode z.2).2))

theorem integrable_fixedNormalizedRealKernel_abs_pow (m : ℕ) :
    Integrable (fun z : ℝ × ℝ => |fixedNormalizedRealKernel z| ^ m)
      (fixedRealObservationLaw.prod fixedRealObservationLaw)

theorem integrable_fixedNormalizedRealKernel_subcritical_exp (η lambda : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 5) (hlambda : 0 < lambda) :
    Integrable (fun z : ℝ × ℝ =>
      Real.exp (lambda * |fixedNormalizedRealKernel z| ^ η))
      (fixedRealObservationLaw.prod fixedRealObservationLaw)

theorem lintegral_fixedNormalizedRealKernel_critical_exp_eq_top
    (lambda : ℝ) (hlambda : 0 < lambda) :
    (∫⁻ z : ℝ × ℝ,
      ENNReal.ofReal (Real.exp (lambda * |fixedNormalizedRealKernel z| ^ (1 / 5 : ℝ)))
      ∂fixedRealObservationLaw.prod fixedRealObservationLaw) = ⊤

theorem not_integrable_fixedNormalizedRealKernel_critical_exp
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ¬ Integrable (fun z : ℝ × ℝ =>
      Real.exp (lambda * |fixedNormalizedRealKernel z| ^ (1 / 5 : ℝ)))
      (fixedRealObservationLaw.prod fixedRealObservationLaw)

end
end Shao.OQ5.P52
```

### Unit 93

```lean
import Shao.OQ5.P52.FixedLayerRealStatistics
import Shao.OQ5.P52.FixedLayerRealNormalization

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

def fixedNormalizedRealSampleU {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Shao.OQ6.FiniteRows.uStatistic (fun i k => fixedNormalizedRealKernel (x i, x k))

def fixedNormalizedRealSampleRowMean {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  Shao.OQ6.FiniteRows.rowMean (fun a b => fixedNormalizedRealKernel (x a, x b)) i

def fixedNormalizedRealSampleStudentizerSq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Shao.OQ6.FiniteRows.jackknifeSq (fun i k => fixedNormalizedRealKernel (x i, x k))

def fixedNormalizedRealSampleStudentizer {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (fixedNormalizedRealSampleStudentizerSq x)

def fixedNormalizedRealSampleStudentized {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (n : ℝ) *
    (fixedNormalizedRealSampleU x -
      ∫ z : ℝ × ℝ, fixedNormalizedRealKernel z
        ∂fixedRealObservationLaw.prod fixedRealObservationLaw) /
    fixedNormalizedRealSampleStudentizer x

def fixedNormalizedRealSampleStudentizedTailProbability (n : ℕ) (x : ℝ) : ℝ :=
  fixedRealSampleLaw.real
    {ξ : ℕ → ℝ |
      x ≤ fixedNormalizedRealSampleStudentized
        (fun i : Fin n => fixedRealSampleCoordinate i.val ξ)}

theorem measurable_fixedNormalizedRealSampleU (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => fixedNormalizedRealSampleU x)

theorem measurable_fixedNormalizedRealSampleRowMean (n : ℕ) (i : Fin n) :
    Measurable (fun x : Fin n → ℝ => fixedNormalizedRealSampleRowMean x i)

theorem measurable_fixedNormalizedRealSampleStudentizerSq (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => fixedNormalizedRealSampleStudentizerSq x)

theorem measurable_fixedNormalizedRealSampleStudentizer (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => fixedNormalizedRealSampleStudentizer x)

theorem measurable_fixedNormalizedRealSampleStudentized (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => fixedNormalizedRealSampleStudentized x)

theorem measurable_fixedNormalizedRealSampleStudentized_sample (n : ℕ) :
    Measurable (fun ξ : ℕ → ℝ =>
      fixedNormalizedRealSampleStudentized
        (fun i : Fin n => fixedRealSampleCoordinate i.val ξ))

theorem fixedNormalizedRealSampleU_eq (n : ℕ) (x : Fin n → ℝ) :
    fixedNormalizedRealSampleU x = Real.sqrt 3 * fixedRealSampleU x

theorem fixedNormalizedRealSampleRowMean_eq (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    fixedNormalizedRealSampleRowMean x i = Real.sqrt 3 *
      Shao.OQ6.FiniteRows.rowMean (fun a b => fixedRealKernel (x a, x b)) i

theorem fixedNormalizedRealSampleStudentizerSq_eq (n : ℕ) (x : Fin n → ℝ) :
    fixedNormalizedRealSampleStudentizerSq x = 3 * fixedRealSampleStudentizerSq x

theorem fixedNormalizedRealSampleStudentizer_eq (n : ℕ) (x : Fin n → ℝ) :
    fixedNormalizedRealSampleStudentizer x = Real.sqrt 3 * fixedRealSampleStudentizer x

theorem fixedNormalizedRealSampleStudentized_eq (n : ℕ) (x : Fin n → ℝ) :
    fixedNormalizedRealSampleStudentized x = fixedRealSampleStudentized x

theorem fixedNormalizedRealSampleStudentizer_prefix_pos_ae (n : ℕ) (hn : 3 ≤ n) :
    ∀ᵐ ξ ∂fixedRealSampleLaw,
      0 < fixedNormalizedRealSampleStudentizer
        (fun i : Fin n => fixedRealSampleCoordinate i.val ξ)

theorem fixedNormalizedRealSampleStudentizedTailProbability_eq_real (n : ℕ) (x : ℝ) :
    fixedNormalizedRealSampleStudentizedTailProbability n x =
      fixedRealSampleStudentizedTailProbability n x

theorem fixedNormalizedRealSampleStudentizedTailProbability_eq (n : ℕ) (x : ℝ) :
    fixedNormalizedRealSampleStudentizedTailProbability n x =
      fixedSampleStudentizedTailProbability n x

theorem fixedNormalizedRealSampleStudentizedTailProbability_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ fixedNormalizedRealSampleStudentizedTailProbability n x

theorem fixedNormalizedRealSampleStudentizedTailProbability_le_one (n : ℕ) (x : ℝ) :
    fixedNormalizedRealSampleStudentizedTailProbability n x ≤ 1

end
end Shao.OQ5.P52
```

### Unit 94

```lean
import Shao.OQ5.P52.FixedLayerNormalizedRealStatistics
import Shao.OQ5.P52.FixedLayerTailLimits

open MeasureTheory Filter
open scoped Topology

namespace Shao.OQ5.P52

noncomputable section

theorem fixedNormalizedRealSampleStudentizedTailProbability_ge_quarter_exp_eventually :
    ∀ᶠ j : ℕ in atTop,
      (1 / 4 : ℝ) * Real.exp
        (-2 * (fixedLayerN j : ℝ) ^ fixedLayerTau j) ≤
        fixedNormalizedRealSampleStudentizedTailProbability
          (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j))

theorem fixedNormalizedRealSampleStudentizedTailProbability_eventually_pos :
    ∀ᶠ j : ℕ in atTop,
      0 < fixedNormalizedRealSampleStudentizedTailProbability
        (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j))

theorem fixedNormalizedRealLayer_log_tail_ratio_tendsto_zero :
    Tendsto (fun j : ℕ =>
      Real.log (fixedNormalizedRealSampleStudentizedTailProbability
          (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j))) /
        (-((fixedLayerTailThreshold (fixedLayerN j)) ^ 2) / 2))
      atTop (nhds 0)

theorem fixedNormalizedRealLayer_relative_tail_ratio_tendsto_atTop :
    Tendsto (fun j : ℕ =>
      fixedNormalizedRealSampleStudentizedTailProbability
          (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j)) /
        Shao.OQ5.P35.standardNormalUpperTail
          (fixedLayerTailThreshold (fixedLayerN j)))
      atTop atTop

theorem fixedNormalizedRealLayer_full_log_tail_ratio_not_tendsto_one :
    ¬ Tendsto (fun n : ℕ =>
      Real.log (fixedNormalizedRealSampleStudentizedTailProbability
          n (fixedLayerTailThreshold n)) /
        (-((fixedLayerTailThreshold n) ^ 2) / 2))
      atTop (nhds 1)

theorem fixedNormalizedRealLayer_full_relative_tail_ratio_not_tendsto_one :
    ¬ Tendsto (fun n : ℕ =>
      fixedNormalizedRealSampleStudentizedTailProbability n (fixedLayerTailThreshold n) /
        Shao.OQ5.P35.standardNormalUpperTail (fixedLayerTailThreshold n))
      atTop (nhds 1)

theorem fixedNormalizedRealLayer_uniform_relative_tail_window_fails :
    ¬ (∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        ∀ x : ℝ, 0 ≤ x → x ≤ 2 * fixedLayerTailThreshold n →
          |fixedNormalizedRealSampleStudentizedTailProbability n x /
            Shao.OQ5.P35.standardNormalUpperTail x - 1| ≤ ε)

end
end Shao.OQ5.P52
```

### Unit 95

```lean
def FixedP52Counterexample (μ : Measure ℝ) (P : Measure (ℕ → ℝ))
    (H : ℝ × ℝ → ℝ) (c : ℝ → (ℕ → Fin 3))
    (K : (ℕ → Fin 3) × (ℕ → Fin 3) → ℝ) : Prop :=
  let a : ℝ := Real.sqrt 3
  let h : ℝ × ℝ → ℝ := fun z => a * H z
  let g0 : ℝ → ℝ := fun x => ∫ y : ℝ, H (x, y) ∂μ
  let r0 : ℝ × ℝ → ℝ := fun z => H z - g0 z.1 - g0 z.2
  let g : ℝ → ℝ := fun x => ∫ y : ℝ, h (x, y) ∂μ
  let r : ℝ × ℝ → ℝ := fun z => h z - g z.1 - g z.2
  let U : (ℝ × ℝ → ℝ) → (n : ℕ) → (Fin n → ℝ) → ℝ :=
    fun A n z => (n.choose 2 : ℝ)⁻¹ *
      ∑ i : Fin n, ∑ k : Fin n, if i < k then A (z i, z k) else 0
  let q : (ℝ × ℝ → ℝ) → (n : ℕ) → (Fin n → ℝ) → Fin n → ℝ :=
    fun A n z i => ((n : ℝ) - 1)⁻¹ *
      ∑ k ∈ Finset.univ.erase i, A (z i, z k)
  let Sq : (ℝ × ℝ → ℝ) → (n : ℕ) → (Fin n → ℝ) → ℝ :=
    fun A n z => (4 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2) *
      ∑ i : Fin n, (q A n z i - U A n z) ^ 2
  let R : (ℝ × ℝ → ℝ) → (n : ℕ) → (Fin n → ℝ) → ℝ :=
    fun A n z => Real.sqrt (Sq A n z)
  let T : (ℝ × ℝ → ℝ) → (n : ℕ) → (Fin n → ℝ) → ℝ :=
    fun A n z => Real.sqrt (n : ℝ) *
      (U A n z - ∫ w : ℝ × ℝ, A w ∂μ.prod μ) / R A n z
  let tail : (ℝ × ℝ → ℝ) → ℕ → ℝ → ℝ :=
    fun A n t => P.real {ξ : ℕ → ℝ | t ≤ T A n (fun i : Fin n => ξ i.val)}
  let x : ℕ → ℝ := fun n => (n : ℝ) ^ (1 / 6 : ℝ) / Real.log (n : ℝ)
  let N : ℕ → ℕ := fun j => 2 ^ (3 * (j + 6) ^ 3)
  IsProbabilityMeasure μ ∧
  IsProbabilityMeasure P ∧
  (∀ i : ℕ, Measurable (fun ξ : ℕ → ℝ => ξ i)) ∧
  (∀ i : ℕ, P.map (fun ξ : ℕ → ℝ => ξ i) = μ) ∧
  ProbabilityTheory.iIndepFun (fun (i : ℕ) (ξ : ℕ → ℝ) => ξ i) P ∧
  (∀ n : ℕ, P.map (fun (ξ : ℕ → ℝ) (i : Fin n) => ξ i.val) =
    Measure.pi (fun _ : Fin n => μ)) ∧
  Measurable c ∧
  Measurable K ∧
  (∀ u v : ℕ → Fin 3, K (u, v) = K (v, u)) ∧
  Measurable H ∧
  (∀ u v : ℝ, H (u, v) = H (v, u)) ∧
  Integrable H (μ.prod μ) ∧
  Integrable (fun z : ℝ × ℝ => H z ^ 2) (μ.prod μ) ∧
  (∀ ν : ℝ, 1 ≤ ν → MemLp H (ENNReal.ofReal ν) (μ.prod μ)) ∧
  (∫ z : ℝ × ℝ, H z ∂μ.prod μ) = 0 ∧
  (∀ᵐ u : ℝ ∂μ, Integrable (fun v : ℝ => H (u, v)) μ) ∧
  Measurable g0 ∧
  MemLp g0 2 μ ∧
  Integrable g0 μ ∧
  Integrable (fun u : ℝ => g0 u ^ 2) μ ∧
  (∫ u : ℝ, g0 u ∂μ) = 0 ∧
  (∫ u : ℝ, g0 u ^ 2 ∂μ) = (1 / 3 : ℝ) ∧
  μ.map g0 = Shao.OQ5.P50.layerNoiseLaw ∧
  (∀ᵐ u : ℝ ∂μ, |g0 u| ≤ 1) ∧
  ProbabilityTheory.IndepFun g0 c μ ∧
  Measurable r0 ∧
  (∀ u v : ℝ, r0 (u, v) = r0 (v, u)) ∧
  (∀ u v : ℝ, H (u, v) = g0 u + g0 v + r0 (u, v)) ∧
  MemLp r0 2 (μ.prod μ) ∧
  Integrable r0 (μ.prod μ) ∧
  (∀ᵐ u : ℝ ∂μ, Integrable (fun v : ℝ => r0 (u, v)) μ) ∧
  (∀ᵐ u : ℝ ∂μ, (∫ v : ℝ, r0 (u, v) ∂μ) = 0) ∧
  (r0 =ᵐ[μ.prod μ] fun z : ℝ × ℝ => K (c z.1, c z.2)) ∧
  0 < a ∧
  Measurable h ∧
  (∀ u v : ℝ, h (u, v) = h (v, u)) ∧
  Integrable h (μ.prod μ) ∧
  MemLp h 2 (μ.prod μ) ∧
  Integrable (fun z : ℝ × ℝ => h z ^ 2) (μ.prod μ) ∧
  (∀ ν : ℝ, 1 ≤ ν → MemLp h (ENNReal.ofReal ν) (μ.prod μ)) ∧
  (∫ z : ℝ × ℝ, h z ∂μ.prod μ) = 0 ∧
  (∀ᵐ u : ℝ ∂μ, Integrable (fun v : ℝ => h (u, v)) μ) ∧
  Measurable g ∧
  (∀ u : ℝ, g u = a * g0 u) ∧
  MemLp g 2 μ ∧
  Integrable g μ ∧
  Integrable (fun u : ℝ => g u ^ 2) μ ∧
  (∫ u : ℝ, g u ∂μ) = 0 ∧
  (∫ u : ℝ, g u ^ 2 ∂μ) = 1 ∧
  μ.map g = Shao.OQ5.P50.layerNoiseLaw.map (fun t : ℝ => a * t) ∧
  (∀ᵐ u : ℝ ∂μ, |g u| ≤ a) ∧
  ProbabilityTheory.IndepFun g c μ ∧
  Measurable r ∧
  (∀ u v : ℝ, r (u, v) = r (v, u)) ∧
  (∀ u v : ℝ, h (u, v) = g u + g v + r (u, v)) ∧
  (∀ z : ℝ × ℝ, r z = a * r0 z) ∧
  MemLp r 2 (μ.prod μ) ∧
  Integrable r (μ.prod μ) ∧
  (∀ᵐ u : ℝ ∂μ, Integrable (fun v : ℝ => r (u, v)) μ) ∧
  (∀ᵐ u : ℝ ∂μ, (∫ v : ℝ, r (u, v) ∂μ) = 0) ∧
  (r =ᵐ[μ.prod μ] fun z : ℝ × ℝ => a * K (c z.1, c z.2)) ∧
  (∀ m : ℕ, Integrable (fun z : ℝ × ℝ => |H z| ^ m) (μ.prod μ)) ∧
  (∀ m : ℕ, Integrable (fun z : ℝ × ℝ => |h z| ^ m) (μ.prod μ)) ∧
  (∀ η lambda : ℝ, 0 < η → η < 1 / 5 → 0 < lambda →
    Integrable (fun z : ℝ × ℝ => Real.exp (lambda * |H z| ^ η)) (μ.prod μ)) ∧
  (∀ η lambda : ℝ, 0 < η → η < 1 / 5 → 0 < lambda →
    Integrable (fun z : ℝ × ℝ => Real.exp (lambda * |h z| ^ η)) (μ.prod μ)) ∧
  (∀ lambda : ℝ, 0 < lambda →
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal
      (Real.exp (lambda * |H z| ^ (1 / 5 : ℝ))) ∂μ.prod μ) = ⊤) ∧
  (∀ lambda : ℝ, 0 < lambda →
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal
      (Real.exp (lambda * |h z| ^ (1 / 5 : ℝ))) ∂μ.prod μ) = ⊤) ∧
  (∀ lambda : ℝ, 0 < lambda →
    ¬ Integrable (fun z : ℝ × ℝ =>
      Real.exp (lambda * |H z| ^ (1 / 5 : ℝ))) (μ.prod μ)) ∧
  (∀ lambda : ℝ, 0 < lambda →
    ¬ Integrable (fun z : ℝ × ℝ =>
      Real.exp (lambda * |h z| ^ (1 / 5 : ℝ))) (μ.prod μ)) ∧
  (∀ n : ℕ, Measurable (U h n)) ∧
  (∀ (n : ℕ) (i : Fin n), Measurable (fun z : Fin n → ℝ => q h n z i)) ∧
  (∀ n : ℕ, Measurable (Sq h n)) ∧
  (∀ n : ℕ, Measurable (R h n)) ∧
  (∀ n : ℕ, Measurable (T h n)) ∧
  (∀ n : ℕ, Measurable
    (fun ξ : ℕ → ℝ => T h n (fun i : Fin n => ξ i.val))) ∧
  (∀ (n : ℕ) (z : Fin n → ℝ), U h n z = a * U H n z) ∧
  (∀ (n : ℕ) (z : Fin n → ℝ) (i : Fin n), q h n z i = a * q H n z i) ∧
  (∀ (n : ℕ) (z : Fin n → ℝ), Sq h n z = 3 * Sq H n z) ∧
  (∀ (n : ℕ) (z : Fin n → ℝ), R h n z = a * R H n z) ∧
  (∀ (n : ℕ) (z : Fin n → ℝ), T h n z = T H n z) ∧
  (∀ (n : ℕ) (t : ℝ), tail h n t = tail H n t) ∧
  (∀ n : ℕ, 3 ≤ n → ∀ᵐ ξ : ℕ → ℝ ∂P,
    0 < R H n (fun i : Fin n => ξ i.val)) ∧
  (∀ n : ℕ, 3 ≤ n → ∀ᵐ ξ : ℕ → ℝ ∂P,
    0 < R h n (fun i : Fin n => ξ i.val)) ∧
  (∀ n : ℕ, 2 ≤ n → 0 < x n) ∧
  Tendsto x atTop atTop ∧
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ (1 / 6 : ℝ)) atTop (nhds 0) ∧
  Tendsto (fun n : ℕ => x n / Real.sqrt (n : ℝ)) atTop (nhds 0) ∧
  Tendsto (fun n : ℕ => 2 * x n / (n : ℝ) ^ (1 / 6 : ℝ)) atTop (nhds 0) ∧
  StrictMono N ∧
  Tendsto N atTop atTop ∧
  (∀ j : ℕ, 8 ≤ N j) ∧
  (∀ᶠ j : ℕ in atTop, (1 / 4 : ℝ) * Real.exp
    (-2 * (N j : ℝ) ^ fixedLayerTau j) ≤ tail h (N j) (x (N j))) ∧
  (∀ᶠ j : ℕ in atTop, 0 < tail h (N j) (x (N j))) ∧
  Tendsto (fun j : ℕ => Real.log (tail h (N j) (x (N j))) /
    (-(x (N j) ^ 2) / 2)) atTop (nhds 0) ∧
  Tendsto (fun j : ℕ => tail h (N j) (x (N j)) /
    Shao.OQ5.P35.standardNormalUpperTail (x (N j))) atTop atTop ∧
  (¬ Tendsto (fun n : ℕ => Real.log (tail h n (x n)) /
    (-(x n ^ 2) / 2)) atTop (nhds 1)) ∧
  (¬ Tendsto (fun n : ℕ => tail h n (x n) /
    Shao.OQ5.P35.standardNormalUpperTail (x n)) atTop (nhds 1)) ∧
  ¬ (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∀ t : ℝ, 0 ≤ t → t ≤ 2 * x n →
      |tail h n t / Shao.OQ5.P35.standardNormalUpperTail t - 1| ≤ ε)

theorem fixedP52Counterexample :
    FixedP52Counterexample fixedRealObservationLaw fixedRealSampleLaw fixedRealKernel
      (fun u : ℝ => (Shao.OQ5.P50.layerDecode u).2) fixedCategoryResidualKernel

theorem exists_fixedP52Counterexample :
    ∃ (μ : Measure ℝ) (P : Measure (ℕ → ℝ)) (H : ℝ × ℝ → ℝ)
      (c : ℝ → (ℕ → Fin 3)) (K : (ℕ → Fin 3) × (ℕ → Fin 3) → ℝ),
      FixedP52Counterexample μ P H c K
```
