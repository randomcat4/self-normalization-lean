# Exact source-bound primary API contexts

Stage1 only. These are exact current curated project declaration heads and definition bodies, with proof bodies omitted. Existing qualified proofs are API evidence, not reviewed again or re-executed. Parent238 remains prospective/unqualified; its frozen head appears in full below. No external theorem is assumed.

## Scalar generator: complete actual definitions and public specifications

C:/game/shao lean/library/Shao/OQ6/ScalarObservationCoding.lean
SHA256 78ba58ee64238fdff51a026d86ab939d34ac66787f804c562c4f0984dc96057c; 14428 bytes.

```lean
noncomputable def baseFourIndicatorCode
    {X : Type*} (A : ℕ → Set X) (x : X) : ℝ :=
  ∑' k : ℕ,
    (if x ∈ A k then (2 : ℝ) else 1) / (4 : ℝ) ^ (k + 1)
```

```lean
def baseFourOneSet (k : ℕ) : Set ℝ :=
  ⋃ m : ℤ,
    Set.Ico
      (((4 : ℝ) * (m : ℝ) + 2) / (4 : ℝ) ^ (k + 1))
      (((4 : ℝ) * (m : ℝ) + 3) / (4 : ℝ) ^ (k + 1))
```

```lean
theorem base_four_indicator_code_spec
    {X : Type*} [mX : MeasurableSpace X]
    (A : ℕ → Set X)
    (hA : ∀ k : ℕ, MeasurableSet (A k))
    (hgen : MeasurableSpace.generateFrom (Set.range A) = mX) :
    let c : X → ℝ := baseFourIndicatorCode A
    (∀ x : X,
      Summable (fun k : ℕ =>
        (if x ∈ A k then (2 : ℝ) else 1) / (4 : ℝ) ^ (k + 1))) ∧
    (∀ x : X, (1 / 3 : ℝ) ≤ c x ∧ c x ≤ (2 / 3 : ℝ)) ∧
    Measurable c ∧
    (∀ k : ℕ, MeasurableSet (baseFourOneSet k)) ∧
    (∀ k : ℕ, A k = c ⁻¹' baseFourOneSet k) ∧
    MeasurableSpace.comap c (borel ℝ) = mX
```

```lean
theorem countable_uniform_augmented_base_four_code
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    let H : ℕ → Set (Ω × ℝ) :=
      MeasurableSpace.natGeneratingSequence (Ω × ℝ)
    let c : (Ω × ℝ) → ℝ := baseFourIndicatorCode H
    let lambda01 : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
    let ν : Measure (Ω × ℝ) := μ.prod lambda01
    IsProbabilityMeasure lambda01 ∧
    IsProbabilityMeasure ν ∧
    (∀ z : Ω × ℝ,
      Summable (fun k : ℕ =>
        (if z ∈ H k then (2 : ℝ) else 1) / (4 : ℝ) ^ (k + 1))) ∧
    (∀ z : Ω × ℝ, (1 / 3 : ℝ) ≤ c z ∧ c z ≤ (2 / 3 : ℝ)) ∧
    Measurable c ∧
    (∀ k : ℕ, MeasurableSet (baseFourOneSet k)) ∧
    (∀ k : ℕ, H k = c ⁻¹' baseFourOneSet k) ∧
    MeasurableSpace.comap c (borel ℝ) =
      (inferInstance : MeasurableSpace (Ω × ℝ)) ∧
    (∀ z z' : Ω × ℝ, c z = c z' → z.2 = z'.2) ∧
    (∀ t : ℝ, ν ({z : Ω × ℝ | c z = t}) = 0)
```

## Quantization and affine recovery: complete actual definitions and public specifications

C:/game/shao lean/library/Shao/OQ6/QuantizedObservationCoding.lean
SHA256 c755dcb72b58931c797416f23ce4f13b383cd17b1b6ef5b2bd5b86b368290062; 6921 bytes.

```lean
noncomputable def quantizedObservation
    {X : Type*} (ε : ℝ) (ξ c : X → ℝ) (x : X) : ℝ :=
  ε * ((Int.floor (ξ x / ε) : ℝ) + c x)
```

```lean
def deterministicAffineObservation
    {X : Type*} (a s : ℝ) (Y : X → ℝ) (x : X) : ℝ :=
  (Y x - a) / s
```

```lean
theorem quantized_observation_spec
    {X : Type*} [mX : MeasurableSpace X]
    (ξ c : X → ℝ) (hξ : Measurable ξ) (hc : Measurable c)
    (hrange : ∀ x : X, (1 / 3 : ℝ) ≤ c x ∧ c x ≤ (2 / 3 : ℝ))
    (hcomap : MeasurableSpace.comap c (borel ℝ) = mX)
    (ε : ℝ) (hε : 0 < ε) :
    let Y : X → ℝ := quantizedObservation ε ξ c
    let D : ℝ → ℝ := fun y : ℝ => y / ε - (Int.floor (y / ε) : ℝ)
    Measurable Y ∧
    Measurable D ∧
    (∀ x : X, |Y x - ξ x| ≤ ε) ∧
    (∀ x : X, Int.floor (Y x / ε) = Int.floor (ξ x / ε)) ∧
    (∀ x : X, D (Y x) = c x) ∧
    MeasurableSpace.comap Y (borel ℝ) = mX ∧
    (∀ (ν : Measure X),
      (∀ t : ℝ, ν ({x : X | c x = t}) = 0) →
      ∀ t : ℝ, ν ({x : X | Y x = t}) = 0)
```

```lean
theorem deterministic_affine_observation_spec
    {X : Type*} [mX : MeasurableSpace X]
    (Y : X → ℝ) (hY : Measurable Y)
    (hcomap : MeasurableSpace.comap Y (borel ℝ) = mX)
    (a s : ℝ) (hs : 0 < s) :
    let η : X → ℝ := deterministicAffineObservation a s Y
    let R : ℝ → ℝ := fun t : ℝ => s * t + a
    Measurable η ∧
    Measurable R ∧
    (∀ x : X, R (η x) = Y x) ∧
    MeasurableSpace.comap η (borel ℝ) = mX ∧
    (∀ (ν : Measure X),
      (∀ t : ℝ, ν ({x : X | Y x = t}) = 0) →
      ∀ t : ℝ, ν ({x : X | η x = t}) = 0)
```

## Coordinate and deleted factorization: complete actual definitions and public specifications

C:/game/shao lean/library/Shao/OQ6/CoordinateBorelFactorization.lean
SHA256 d245e4f1495972f54a1a823ca075afa526a3f82759fd2030141c0badab780c5c; 7334 bytes.

```lean
def coordinateCodeTuple
    {I : Type*} {X : I → Type*}
    (c : ∀ i : I, X i → ℝ) (x : ∀ i : I, X i) : I → ℝ :=
  fun i : I => c i (x i)
```

```lean
def deleteCoordinateTuple
    {I : Type*} {X : I → Type*}
    (i : I) (x : ∀ j : I, X j) :
    ∀ j : {j : I // j ≠ i}, X j.1 :=
  fun j : {j : I // j ≠ i} => x j.1
```

```lean
theorem real_borel_factorization_of_comap
    {X S : Type*} [mX : MeasurableSpace X] [mS : MeasurableSpace S]
    (t : X → S)
    (hcomap : MeasurableSpace.comap t mS = mX)
    (h : X → ℝ) (hh : Measurable h) :
    ∃ F : S → ℝ, Measurable F ∧ ∀ x : X, h x = F (t x)
```

```lean
theorem finite_coordinate_code_tuple_spec
    {I : Type*} [Fintype I] {X : I → Type*}
    [mX : ∀ i : I, MeasurableSpace (X i)]
    (c : ∀ i : I, X i → ℝ)
    (hcomap : ∀ i : I,
      MeasurableSpace.comap (c i) (borel ℝ) = mX i) :
    let C : (∀ i : I, X i) → (I → ℝ) := coordinateCodeTuple c
    Measurable[(inferInstance : MeasurableSpace (∀ i : I, X i)),
      borel (I → ℝ)] C ∧
    MeasurableSpace.comap C (borel (I → ℝ)) =
      (inferInstance : MeasurableSpace (∀ i : I, X i)) ∧
    (∀ (h : (∀ i : I, X i) → ℝ), Measurable h →
      ∃ F : (I → ℝ) → ℝ,
        Measurable[borel (I → ℝ), borel ℝ] F ∧
        ∀ x : (∀ i : I, X i), h x = F (C x))
```

```lean
theorem finite_deleted_code_factorization
    {n : ℕ} {X : Fin n → Type*}
    [mX : ∀ j : Fin n, MeasurableSpace (X j)]
    (c : ∀ j : Fin n, X j → ℝ)
    (hcomap : ∀ j : Fin n,
      MeasurableSpace.comap (c j) (borel ℝ) = mX j)
    (i : Fin n) :
    let J : Type := {j : Fin n // j ≠ i}
    let C : (∀ j : Fin n, X j) → (Fin n → ℝ) := coordinateCodeTuple c
    let Cdel : (∀ j : J, X j.1) → (J → ℝ) :=
      coordinateCodeTuple (fun j : J => c j.1)
    let pX : (∀ j : Fin n, X j) → (∀ j : J, X j.1) :=
      deleteCoordinateTuple (X := X) i
    let pR : (Fin n → ℝ) → (J → ℝ) :=
      deleteCoordinateTuple (X := fun _ : Fin n => ℝ) i
    Measurable pX ∧
    Measurable[borel (Fin n → ℝ), borel (J → ℝ)] pR ∧
    Measurable[(inferInstance : MeasurableSpace (∀ j : J, X j.1)),
      borel (J → ℝ)] Cdel ∧
    MeasurableSpace.comap Cdel (borel (J → ℝ)) =
      (inferInstance : MeasurableSpace (∀ j : J, X j.1)) ∧
    (∀ x : (∀ j : Fin n, X j), pR (C x) = Cdel (pX x)) ∧
    MeasurableSpace.comap (fun x : (∀ j : Fin n, X j) => pR (C x))
        (borel (J → ℝ)) =
      MeasurableSpace.comap pX
        (inferInstance : MeasurableSpace (∀ j : J, X j.1)) ∧
    (∀ (d : (∀ j : J, X j.1) → ℝ), Measurable d →
      ∃ F : (J → ℝ) → ℝ,
        Measurable[borel (J → ℝ), borel ℝ] F ∧
        (∀ y : (∀ j : J, X j.1), d y = F (Cdel y)) ∧
        Measurable[borel (Fin n → ℝ), borel ℝ]
          (fun z : Fin n → ℝ => F (pR z)) ∧
        ∀ x : (∀ j : Fin n, X j), d (pX x) = F (pR (C x)))
```

## Literal normalized family: complete actual definitions

C:/game/shao lean/library/Shao/OQ6/ActualMomentNormalization.lean
SHA256 7e781dc929166b43c69dd6ffe463c62e2d1508fa5283451852ea50afed18c237; 22137 bytes.

```lean
noncomputable def actualCoordinateMean
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {n : ℕ} (Y : Fin n → Ω → ℝ) (i : Fin n) : ℝ :=
  ∫ ω, Y i ω ∂ν
```

```lean
noncomputable def actualCenteredFamily
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {n : ℕ} (Y : Fin n → Ω → ℝ)
    (i : Fin n) (ω : Ω) : ℝ :=
  Y i ω - actualCoordinateMean ν Y i
```

```lean
noncomputable def actualNormalizationScale
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {n : ℕ} (Y : Fin n → Ω → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∫ ω, (actualCenteredFamily ν Y i ω) ^ 2 ∂ν)
```

```lean
noncomputable def actualNormalizedFamily
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {n : ℕ} (Y : Fin n → Ω → ℝ)
    (i : Fin n) (ω : Ω) : ℝ :=
  Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation
    (actualCoordinateMean ν Y i) (actualNormalizationScale ν Y) (Y i) ω
```

## Alternate finite normalization packet: not used by the preferred route

C:/game/shao lean/library/Shao/OQ6/FiniteUniformCodingAssembly.lean
SHA256 f07e3f6fe31854f8fc69e568e36c132902f67303b67a2efbe1d1ce485ebd7fa6; 22157 bytes.

```lean
theorem actual_finite_normalized_coding_spec
    (n : ℕ) (hn : 1 ≤ n) {Ω : Fin n → Type*}
    [mΩ : ∀ i : Fin n, MeasurableSpace (Ω i)]
    [∀ i : Fin n, MeasurableSpace.CountablyGenerated (Ω i)]
    (μ : ∀ i : Fin n, Measure (Ω i))
    [hμ : ∀ i : Fin n, IsProbabilityMeasure (μ i)]
    (g : ∀ i : Fin n, Ω i → ℝ)
    (hg : ∀ i : Fin n, Measurable (g i))
    (hg2 : ∀ i : Fin n, MemLp (g i) 2 (μ i))
    (hgmean : ∀ i : Fin n, (∫ o, g i o ∂(μ i)) = 0)
    (hgenergy : (∑ i : Fin n, ∫ o, (g i o) ^ 2 ∂(μ i)) = 1)
    (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε < 1 / (4 * Real.sqrt (n : ℝ))) :
    let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
    let νlocal : ∀ i : Fin n, Measure (Ω i × ℝ) := fun i => (μ i).prod lambda01
    let ν : Measure (∀ i : Fin n, Ω i × ℝ) := Measure.pi νlocal
    let c : ∀ i : Fin n, (Ω i × ℝ) → ℝ := fun i => Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode (MeasurableSpace.natGeneratingSequence (Ω i × ℝ))
    let ξlocal : ∀ i : Fin n, (Ω i × ℝ) → ℝ := fun i z => g i z.1
    let Ylocal : ∀ i : Fin n, (Ω i × ℝ) → ℝ := fun i => Shao.OQ6.QuantizedObservationCoding.quantizedObservation ε (ξlocal i) (c i)
    let ξ : Fin n → (∀ i : Fin n, Ω i × ℝ) → ℝ := fun i x => g i (x i).1
    let Y : Fin n → (∀ i : Fin n, Ω i × ℝ) → ℝ := fun i x => Ylocal i (x i)
    let a : Fin n → ℝ := Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν Y
    let s : ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν Y
    let ηlocal : ∀ i : Fin n, (Ω i × ℝ) → ℝ := fun i => Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a i) s (Ylocal i)
    let η : Fin n → (∀ i : Fin n, Ω i × ℝ) → ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
    let Vη : (∀ i : Fin n, Ω i × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (η i x) ^ 2)
    IsProbabilityMeasure ν ∧
    (∀ i : Fin n, MeasurePreserving (fun x : (∀ j : Fin n, Ω j × ℝ) => (x i).1) ν (μ i)) ∧
    (∀ i : Fin n, Measurable (ξ i)) ∧
    (∀ i : Fin n, MemLp (ξ i) 2 ν) ∧
    (∀ i : Fin n, (∫ x, ξ i x ∂ν) = ∫ o, g i o ∂(μ i)) ∧
    (∀ i : Fin n, (∫ x, (ξ i x) ^ 2 ∂ν) = ∫ o, (g i o) ^ 2 ∂(μ i)) ∧
    (∀ i : Fin n, (∫ x, ξ i x ∂ν) = 0) ∧
    (∑ i : Fin n, ∫ x, (ξ i x) ^ 2 ∂ν) = 1 ∧
    (∀ i : Fin n, Measurable (Ylocal i)) ∧
    (∀ i : Fin n, Measurable (Y i)) ∧
    (∀ (i : Fin n) (x : ∀ j : Fin n, Ω j × ℝ), |Y i x - ξ i x| ≤ ε) ∧
    (∀ i : Fin n, MemLp (Ylocal i) 2 (νlocal i)) ∧
    (∀ i : Fin n, Integrable (Ylocal i) (νlocal i)) ∧
    (∀ i : Fin n, a i = ∫ z, Ylocal i z ∂(νlocal i)) ∧
    (∀ i : Fin n, |a i| ≤ ε) ∧
    (1 / 2 : ℝ) < s ∧
    (∀ i : Fin n, Measurable (ηlocal i)) ∧
    (∀ i : Fin n, MeasurableSpace.comap (ηlocal i) (borel ℝ) = (inferInstance : MeasurableSpace (Ω i × ℝ))) ∧
    (∀ (i : Fin n) (t : ℝ), νlocal i ({z : Ω i × ℝ | ηlocal i z = t}) = 0) ∧
    (∀ (i : Fin n) (x : ∀ j : Fin n, Ω j × ℝ), η i x = ηlocal i (x i)) ∧
    iIndepFun η ν ∧
    (∀ i : Fin n, Measurable (η i)) ∧
    (∀ i : Fin n, MemLp (η i) 2 ν) ∧
    (∀ i : Fin n, Integrable (η i) ν) ∧
    (∀ i : Fin n, Integrable (fun x => (η i x) ^ 2) ν) ∧
    (∀ i : Fin n, (∫ x, η i x ∂ν) = 0) ∧
    (∑ i : Fin n, ∫ x, (η i x) ^ 2 ∂ν) = 1 ∧
    (∀ (i : Fin n) (t : ℝ), ν ({x : (∀ j : Fin n, Ω j × ℝ) | η i x = t}) = 0) ∧
    ν ({x : (∀ j : Fin n, Ω j × ℝ) | Vη x = 0}) = 0 ∧
    (∀ᵐ x ∂ν, 0 < Vη x)
```

## External attribution boundary and exact future consumer

C:/game/shao lean/library/Shao/OQ6/NormalizedIntegrableTailAssembly.lean
SHA256 c868ca007153fdc15ff29077702cbb64e8fac5d66ebd9821171ae38454ae5916; 24094 bytes.

```lean
def ScalarShaoZhouFiniteCostTailInput
    (cSZ C1 C2 C3 C4 : ℝ) : Prop :=
  0 < cSZ ∧ 0 < C1 ∧ 0 < C2 ∧ 0 < C3 ∧ 0 < C4 ∧
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ζ : Fin n → Ω → ℝ)
    (F1 F2 FA FB : (Fin n → ℝ) → ℝ)
    (FAdelete FBdelete : ∀ i : Fin n, ({j : Fin n // j ≠ i} → ℝ) → ℝ)
    (hζ : ∀ i : Fin n, Measurable (ζ i))
    (hζindep : iIndepFun ζ ν)
    (hζ2 : ∀ i : Fin n, MemLp (ζ i) 2 ν)
    (hζmean : ∀ i : Fin n, (∫ ω, ζ i ω ∂ν) = 0)
    (hζenergy : (∑ i : Fin n, ∫ ω, (ζ i ω) ^ 2 ∂ν) = 1)
    (hF1 : Measurable[borel (Fin n → ℝ), borel ℝ] F1)
    (hF2 : Measurable[borel (Fin n → ℝ), borel ℝ] F2)
    (hFA : Measurable[borel (Fin n → ℝ), borel ℝ] FA)
    (hFB : Measurable[borel (Fin n → ℝ), borel ℝ] FB)
    (hFAdelete : ∀ i : Fin n,
      Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FAdelete i))
    (hFBdelete : ∀ i : Fin n,
      Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FBdelete i))
    (x : ℝ),
    let C : Ω → (Fin n → ℝ) := fun ω i => ζ i ω
    let D1 : Ω → ℝ := fun ω => F1 (C ω)
    let D2 : Ω → ℝ := fun ω => F2 (C ω)
    let A : Ω → ℝ := fun ω => FA (C ω)
    let B : Ω → ℝ := fun ω => FB (C ω)
    let Adelete : Fin n → Ω → ℝ := fun i ω => FAdelete i (fun j => ζ j.1 ω)
    let Bdelete : Fin n → Ω → ℝ := fun i ω => FBdelete i (fun j => ζ j.1 ω)
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ζ i ω
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ζ i ω) ^ 2)
    let S : Ω → ℝ := fun ω => ∑ i : Fin n, (x * ζ i ω - (x * ζ i ω) ^ 2 / 2)
    let Sminus : Fin n → Ω → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, (x * ζ j ω - (x * ζ j ω) ^ 2 / 2)
    let I : ℝ := ∫ ω, Real.exp (S ω) ∂ν
    let δ : Fin n → ℝ := fun i => ∫ ω, (x * ζ i ω) ^ 2 * min |x * ζ i ω| 1 ∂ν
    let L : ℝ := ∑ i : Fin n, δ i
    let full : Ω → ℝ := fun ω => (x * A ω + x ^ 2 * B ω) * Real.exp (S ω)
    let deleted : Fin n → Ω → ℝ := fun i ω => (min |x * ζ i ω| 1 * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)) * Real.exp (Sminus i ω)
    let R : ℝ := ((∫ ω, full ω ∂ν) + ∑ i : Fin n, ∫ ω, deleted i ω ∂ν) / I
    let T : Ω → ℝ := fun ω => (W ω + D1 ω) / (V ω * Real.sqrt (1 + D2 ω))
    (∀ ω : Ω, 0 ≤ A ω ∧ 0 ≤ B ω) →
    (∀ (i : Fin n) (ω : Ω), 0 ≤ Adelete i ω ∧ 0 ≤ Bdelete i ω) →
    (∀ᵐ ω ∂ν, |D1 ω| ≤ A ω ∧ |D2 ω| ≤ B ω) →
    (∀ᵐ ω ∂ν, 0 < 1 + D2 ω) →
    (∀ᵐ ω ∂ν, 0 < V ω) →
    Integrable (fun ω => Real.exp (S ω)) ν →
    0 < I → Integrable full ν →
    (∀ i : Fin n, Integrable (deleted i) ν) →
    1 ≤ x → (∀ i : Fin n, δ i ≤ 1) → L ≤ cSZ * x ^ 2 →
    Shao.standardNormalTail x * Real.exp (-C1 * L) * (1 - C2 * R) ≤
      ν.real {ω : Ω | x ≤ T ω} ∧
    ν.real {ω : Ω | x ≤ T ω} ≤
      Shao.standardNormalTail x * Real.exp (C3 * L) * (1 + C4 * R) +
        ν.real {ω : Ω | x * |D1 ω| > V ω / 4} +
        ν.real {ω : Ω | x ^ 2 * |D2 ω| > (1 / 4 : ℝ)}
```

```lean
theorem actual_normalized_integrable_tail_assembly
    {Ω : Type u} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (hξmean : ∀ i : Fin n, (∫ ω, ξ i ω ∂ν) = 0)
    (hξenergy : (∑ i : Fin n, ∫ ω, (ξ i ω) ^ 2 ∂ν) = 1)
    (Y : ℕ → Fin n → Ω → ℝ)
    (hY : ∀ (k : ℕ) (i : Fin n), Measurable (Y k i))
    (ε : ℕ → ℝ) (hε : ∀ k : ℕ, 0 < ε k)
    (hεsmall : ∀ k : ℕ, ε k < 1 / (4 * Real.sqrt (n : ℝ)))
    (hεlim : Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ)))
    (herr : ∀ (k : ℕ) (i : Fin n) (ω : Ω), |Y k i ω - ξ i ω| ≤ ε k)
    (hηindep : ∀ k : ℕ, iIndepFun
      (Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)) ν)
    (hηpos : ∀ k : ℕ, ∀ᵐ ω ∂ν, 0 < Real.sqrt (∑ i : Fin n,
      (Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k) i ω) ^ 2))
    (hFullFactor : ∀ (k : ℕ) (h : Ω → ℝ), Measurable h →
      ∃ F : (Fin n → ℝ) → ℝ,
        Measurable[borel (Fin n → ℝ), borel ℝ] F ∧
        ∀ ω : Ω, h ω = F (fun i =>
          Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k) i ω))
    (D1 D2 κ A B : Ω → ℝ) (Adelete Bdelete : Fin n → Ω → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2) (hκ : Measurable κ)
    (hA : Measurable A) (hB : Measurable B)
    (hAdelete : ∀ i : Fin n, Measurable (Adelete i))
    (hBdelete : ∀ i : Fin n, Measurable (Bdelete i))
    (hAnonneg : ∀ ω : Ω, 0 ≤ A ω)
    (hBnonneg : ∀ ω : Ω, 0 ≤ B ω)
    (hAdeletenonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Adelete i ω)
    (hBdeletenonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Bdelete i ω)
    (hD1A : ∀ ω : Ω, |D1 ω| ≤ A ω)
    (hD2B : ∀ ω : Ω, |D2 ω| ≤ B ω)
    (hD2pos : ∀ᵐ ω ∂ν, 0 < 1 + D2 ω)
    (hAint : Integrable A ν) (hBint : Integrable B ν)
    (hAdeleteint : ∀ i : Fin n, Integrable (Adelete i) ν)
    (hBdeleteint : ∀ i : Fin n, Integrable (Bdelete i) ν)
    (hAdeleteFactor : ∀ (k : ℕ) (i : Fin n),
      ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
        ∀ ω : Ω, Adelete i ω = F (fun j =>
          Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k) j.1 ω))
    (hBdeleteFactor : ∀ (k : ℕ) (i : Fin n),
      ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
        ∀ ω : Ω, Bdelete i ω = F (fun j =>
          Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k) j.1 ω))
    (cSZ C1 C2 C3 C4 : ℝ)
    (hSZ : ScalarShaoZhouFiniteCostTailInput.{u} cSZ C1 C2 C3 C4)
    (x : ℝ) (hx : 1 ≤ x)
    (hδ : ∀ i : Fin n,
      (∫ ω, (x * ξ i ω) ^ 2 * min |x * ξ i ω| 1 ∂ν) ≤ (1 / 2 : ℝ))
    (hL : (∑ i : Fin n, ∫ ω, (x * ξ i ω) ^ 2 * min |x * ξ i ω| 1 ∂ν) ≤
      (cSZ / 2) * x ^ 2) :
    let η : ℕ → Fin n → Ω → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
    let Wη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, η k i ω
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let Vη : ℕ → Ω → ℝ := fun k ω => Real.sqrt (∑ i : Fin n, (η k i ω) ^ 2)
    let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
    let Dη : ℕ → Ω → ℝ := fun k ω => D1 ω + W ω - Wη k ω + x * b ω * (Vη k ω - V ω)
    let H : Ω → ℝ := fun ω => (1 + V ω) * (Real.sqrt (n : ℝ) + x * Real.sqrt (1 + B ω))
    let ρ : ℕ → ℝ := fun k => 4 * ε k * Real.sqrt (n : ℝ)
    let Aε : ℕ → Ω → ℝ := fun k ω => A ω + ρ k * H ω
    let T : Ω → ℝ := fun ω => if V ω = 0 then κ ω else (W ω + D1 ω) / (V ω * b ω)
    let Tη : ℕ → Ω → ℝ := fun k ω => (Wη k ω + Dη k ω) / (Vη k ω * b ω)
    let F : Set Ω := {ω : Ω | x * V ω * b ω ≤ W ω + D1 ω}
    let Z : Set Ω := {ω : Ω | V ω = 0}
    let p0 : ℝ := ν.real Z
    let δ : Fin n → ℝ := fun i => ∫ ω, (x * ξ i ω) ^ 2 * min |x * ξ i ω| 1 ∂ν
    let δη : ℕ → Fin n → ℝ := fun k i => ∫ ω, (x * η k i ω) ^ 2 * min |x * η k i ω| 1 ∂ν
    let L : ℝ := ∑ i : Fin n, δ i
    let Lη : ℕ → ℝ := fun k => ∑ i : Fin n, δη k i
    let S : Ω → ℝ := fun ω => ∑ i : Fin n, (x * ξ i ω - (x * ξ i ω) ^ 2 / 2)
    let Sη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, (x * η k i ω - (x * η k i ω) ^ 2 / 2)
    let Sminus : Fin n → Ω → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, (x * ξ j ω - (x * ξ j ω) ^ 2 / 2)
    let Sηminus : ℕ → Fin n → Ω → ℝ := fun k i ω => ∑ j ∈ Finset.univ.erase i, (x * η k j ω - (x * η k j ω) ^ 2 / 2)
    let I : ℝ := ∫ ω, Real.exp (S ω) ∂ν
    let Iη : ℕ → ℝ := fun k => ∫ ω, Real.exp (Sη k ω) ∂ν
    let full : Ω → ℝ := fun ω => (x * A ω + x ^ 2 * B ω) * Real.exp (S ω)
    let fullη : ℕ → Ω → ℝ := fun k ω => (x * Aε k ω + x ^ 2 * B ω) * Real.exp (Sη k ω)
    let deleted : Fin n → Ω → ℝ := fun i ω => (min |x * ξ i ω| 1 * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)) * Real.exp (Sminus i ω)
    let deletedη : ℕ → Fin n → Ω → ℝ := fun k i ω => (min |x * η k i ω| 1 * (|Aε k ω - Adelete i ω| + x * |B ω - Bdelete i ω|)) * Real.exp (Sηminus k i ω)
    let R : ℝ := ((∫ ω, full ω ∂ν) + ∑ i : Fin n, ∫ ω, deleted i ω ∂ν) / I
    let Rη : ℕ → ℝ := fun k => ((∫ ω, fullη k ω ∂ν) + ∑ i : Fin n, ∫ ω, deletedη k i ω ∂ν) / Iη k
    let lower : ℝ := Shao.standardNormalTail x * Real.exp (-C1 * L) * (1 - C2 * R)
    let lowerη : ℕ → ℝ := fun k => Shao.standardNormalTail x * Real.exp (-C1 * Lη k) * (1 - C2 * Rη k)
    let upper : ℝ := Shao.standardNormalTail x * Real.exp (C3 * L) * (1 + C4 * R)
    let upperη : ℕ → ℝ := fun k => Shao.standardNormalTail x * Real.exp (C3 * Lη k) * (1 + C4 * Rη k)
    let numeratorBad : Set Ω := {ω : Ω | x * |D1 ω| > V ω / 8}
    let numeratorBadη : ℕ → Set Ω := fun k => {ω : Ω | x * |Dη k ω| > Vη k ω / 4}
    let denominatorBad : Set Ω := {ω : Ω | x ^ 2 * |D2 ω| > (1 / 4 : ℝ)}
    (∀ᶠ k : ℕ in Filter.atTop, (∀ i : Fin n, δη k i ≤ 1) ∧ Lη k ≤ cSZ * x ^ 2) ∧
    Filter.Tendsto lowerη Filter.atTop (nhds lower) ∧
    Filter.Tendsto upperη Filter.atTop (nhds upper) ∧
    (∀ k : ℕ, ν.real {ω : Ω | x ≤ Tη k ω} = ν.real F) ∧
    lower ≤ ν.real F ∧
    ν.real F ≤ upper + ν.real numeratorBad + ν.real denominatorBad + p0 ∧
    lower - p0 ≤ ν.real {ω : Ω | x ≤ T ω} ∧
    ν.real {ω : Ω | x ≤ T ω} ≤
      upper + ν.real numeratorBad + ν.real denominatorBad + 2 * p0
```

## Exact prospective parent238 interface

This is a frozen statement, not a qualified theorem at this Stage1 checkpoint. It cannot be invoked in an implementation until the lead binds qualified exact238 evidence. Frozen namespace: Shao.OQ6.OriginalSameWitnessUpperErrorPayment; imports/namespace context exactly as FROZEN-PREAMBLE.txt. FROZEN-HEAD SHA256 74ddb2d0afd658979240388cdd9c38b435a64dd05000d373726c3b188eeb387a,28778B.

```lean
import Shao.OQ6.OriginalSingleWitnessAnalyticStrictFrontier
import Shao.OQ6.NormalizedUpperErrorGoodsetPayment
import Shao.OQ6.P54ActualGoodsetFrontier
import Shao.OQ6.ActualQuadraticTiltMoments
import Shao.OQ6.OriginalLiteralWeightedConsumer
import Shao.OQ6.NormalizedStrictMomentBudgets
import Shao.OQ6.IIDSourceStrictMomentBudgets

set_option autoImplicit false
universe u
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology MeasureTheory
open Shao.OQ5.P51
namespace Shao.OQ6.OriginalSameWitnessUpperErrorPayment
noncomputable section

theorem actual_original_same_witness_upper_error_payment
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond : (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (hgp : Integrable (fun o : Ω => Real.rpow |∫ y, h o y ∂μ| p) μ)
    (cBudget : ℝ) (hcBudget : 0 < cBudget) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω mΩ mΩ μ μ)
    let rho : ℝ := Real.sqrt v
    let β : ℝ := ∫ o : Ω, Real.rpow |g o| p ∂μ
    let cWindow : ℝ := Real.rpow (min (1 / 2 : ℝ) cBudget / 2) (1 / p)
    Measurable[mΩ, borel ℝ] g ∧ MemLp g 2 μ ∧
    0 ≤ β ∧ 0 < cWindow ∧
    Real.rpow cWindow p = min (1 / 2 : ℝ) cBudget / 2 ∧
    Real.rpow cWindow p < min (1 / 2 : ℝ) cBudget ∧
    ∃ cg : ℝ, 0 < cg ∧
    ∃ (m₀ : MeasurableSpace Ω) (hm₀ : m₀ ≤ mΩ)
        (hcg : @MeasurableSpace.CountablyGenerated Ω m₀),
      let μ₀ : @Measure Ω m₀ := μ.trim hm₀
      letI : MeasurableSpace Ω := m₀
      letI : MeasurableSpace.CountablyGenerated Ω := hcg
      IsProbabilityMeasure μ₀ ∧
      (∀ (n : ℕ) (hn : 4 ≤ n) (C0 : ℝ) (hC0 : 0 ≤ C0)
          (z : ℝ) (hz : 0 ≤ z),
        let mN : MeasurableSpace (Fin n → Ω) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ)
        let mN₀ : MeasurableSpace (Fin n → Ω) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => m₀)
        let P : @Measure (Fin n → Ω) mN :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mΩ) (fun _ : Fin n => μ)
        let P₀ : @Measure (Fin n → Ω) mN₀ :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => m₀) (fun _ : Fin n => μ₀)
        let N : ℝ := Real.sqrt (n : ℝ)
        let K : ℝ := 4 * Real.sqrt (n : ℝ)
        let ε : ℕ → ℝ := fun k => 1 / (8 * Real.sqrt (n : ℝ) * ((k : ℝ) + 1))
        let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
        let D1 : (Fin n → Ω) → ℝ := residualStatisticD n r
        let D2 : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r C0 rho 1
        let T0 : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r C0 rho 1
        let A0 : (Fin n → Ω) → ℝ := fun ζ => |D1 ζ|
        let B0 : (Fin n → Ω) → ℝ := studentizerClipBudget n r C0 rho 1
        let A0delete : Fin n → (Fin n → Ω) → ℝ :=
          fun i ζ => |residualStatisticDDeleted n r ζ i|
        let B0delete : Fin n → (Fin n → Ω) → ℝ :=
          fun i ζ => studentizerClipBudgetDeleted n r C0 rho 1 ζ i
        let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
        let mAugLocal : MeasurableSpace (Ω × ℝ) := m₀.prod (borel ℝ)
        let mAug : MeasurableSpace (Fin n → Ω × ℝ) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (fun _ : Fin n => mAugLocal)
        let νlocal : Fin n → @Measure (Ω × ℝ) mAugLocal :=
          fun _ => @Measure.prod Ω ℝ m₀ (borel ℝ) μ₀ lambda01
        let ν : @Measure (Fin n → Ω × ℝ) mAug :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (inferInstance : Fintype (Fin n)) (fun _ : Fin n => mAugLocal) νlocal
        let q : (Fin n → Ω × ℝ) → (Fin n → Ω) := fun x i => (x i).1
        let c : Fin n → (Ω × ℝ) → ℝ := fun _ =>
          Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode
            (MeasurableSpace.natGeneratingSequence (Ω × ℝ))
        let ξlocal : Fin n → (Ω × ℝ) → ℝ := fun i t => g t.1 / N
        let Ylocal : ℕ → Fin n → (Ω × ℝ) → ℝ := fun k i =>
          Shao.OQ6.QuantizedObservationCoding.quantizedObservation (ε k) (ξlocal i) (c i)
        let ξ : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => ξlocal i (x i)
        let Y : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x => Ylocal k i (x i)
        let a : ℕ → Fin n → ℝ := fun k =>
          Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν (Y k)
        let s : ℕ → ℝ := fun k =>
          Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν (Y k)
        let ηlocal : ℕ → Fin n → (Ω × ℝ) → ℝ := fun k i =>
          Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a k i) (s k) (Ylocal k i)
        let η : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k =>
          Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
        let C : ℕ → (Fin n → Ω × ℝ) → (Fin n → ℝ) := fun k x i => η k i x
        let W : (Fin n → Ω × ℝ) → ℝ := fun x => ∑ i : Fin n, ξ i x
        let V : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (ξ i x) ^ 2)
        let Wη : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => ∑ i : Fin n, η k i x
        let Vη : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => Real.sqrt (∑ i : Fin n, (η k i x) ^ 2)
        let b : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (1 + D2 (q x))
        let Qε : ℕ → (Fin n → Ω × ℝ) → ℝ :=
          fun k x => W x - Wη k x + z * b x * (Vη k x - V x)
        let Dη : ℕ → (Fin n → Ω × ℝ) → ℝ :=
          fun k x => D1 (q x) + W x - Wη k x + z * b x * (Vη k x - V x)
        let Tη : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => (Wη k x + Dη k x) / (Vη k x * b x)
        let A : (Fin n → Ω × ℝ) → ℝ := fun x => A0 (q x)
        let B : (Fin n → Ω × ℝ) → ℝ := fun x => B0 (q x)
        let Adelete : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => A0delete i (q x)
        let Bdelete : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => B0delete i (q x)
        let Vdelete : Fin n → (Fin n → Ω × ℝ) → ℝ :=
          fun i x => Real.sqrt (∑ j ∈ Finset.univ.erase i, (ξ j x) ^ 2)
        let H : (Fin n → Ω × ℝ) → ℝ :=
          fun x => (1 + V x) * (N + z * Real.sqrt (1 + B x))
        let Hdelete : Fin n → (Fin n → Ω × ℝ) → ℝ :=
          fun i x => (1 + Vdelete i x) * (N + z * Real.sqrt (1 + Bdelete i x))
        let M : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => K * ε k * H x
        let Mdelete : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x => K * ε k * Hdelete i x
        let Anew : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => A x + M k x
        let AdeleteNew : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x => Adelete i x + Mdelete k i x
        let Δ : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ :=
          fun k i x => (Anew k x - AdeleteNew k i x) - (A x - Adelete i x)
        let ℓ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => z * ξ0 i ζ - (z * ξ0 i ζ) ^ 2 / 2
        let ℓη : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x => z * η k i x - (z * η k i x) ^ 2 / 2
        let S0 : (Fin n → Ω) → ℝ := fun ζ => ∑ i : Fin n, ℓ0 i ζ
        let Sη : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => ∑ i : Fin n, ℓη k i x
        let S0minus : Fin n → (Fin n → Ω) → ℝ := fun i ζ => ∑ j ∈ Finset.univ.erase i, ℓ0 j ζ
        let Sηminus : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x => ∑ j ∈ Finset.univ.erase i, ℓη k j x
        let I0 : ℝ := ∫ ζ, Real.exp (S0 ζ) ∂P
        let Iη : ℕ → ℝ := fun k => ∫ x, Real.exp (Sη k x) ∂ν
        let fullTest0 : (Fin n → Ω) → ℝ := fun ζ => z * A0 ζ + z ^ 2 * B0 ζ
        let fullTestη : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => z * Anew k x + z ^ 2 * B x
        let deletedTest0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ =>
          min |z * ξ0 i ζ| 1 * (|A0 ζ - A0delete i ζ| + z * |B0 ζ - B0delete i ζ|)
        let deletedTestη : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x =>
          min |z * η k i x| 1 * (|Anew k x - AdeleteNew k i x| + z * |B x - Bdelete i x|)
        let compactDeletedTest0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ =>
          min |ξ0 i ζ| (1 + z)⁻¹ * (|A0 ζ - A0delete i ζ| + z * |B0 ζ - B0delete i ζ|)
        let compactDeletedTestη : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x =>
          min |η k i x| (1 + z)⁻¹ * (|Anew k x - AdeleteNew k i x| + z * |B x - Bdelete i x|)
        let Lcompact0 : ℝ := ∑ i : Fin n,
          ∫ ζ, ((1 + z) * ξ0 i ζ) ^ 2 * min |(1 + z) * ξ0 i ζ| 1 ∂P
        let Lcompactη : ℕ → ℝ := fun k => ∑ i : Fin n,
          ∫ x, ((1 + z) * η k i x) ^ 2 * min |(1 + z) * η k i x| 1 ∂ν
        let sourceCost0 : ℝ :=
          ((∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P) +
            ∑ i : Fin n, ∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P) / I0
        let sourceCostη : ℕ → ℝ := fun k =>
          ((∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) +
            ∑ i : Fin n, ∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k
        let compactCost0 : ℝ := Lcompact0 + (∫ ζ, A0 ζ ∂P) + z * (∫ ζ, B0 ζ ∂P) +
          ∑ i : Fin n, ∫ ζ, compactDeletedTest0 i ζ ∂P
        let compactCostη : ℕ → ℝ := fun k => Lcompactη k + (∫ x, Anew k x ∂ν) +
          z * (∫ x, B x ∂ν) + ∑ i : Fin n, ∫ x, compactDeletedTestη k i x ∂ν
        let Fz : ℝ → ℝ := fun t => (z * t) ^ 2 * min |z * t| 1
        let δ0 : Fin n → ℝ := fun i => ∫ ζ, Fz (ξ0 i ζ) ∂P
        let δreduced : Fin n → ℝ := fun i => ∫ ζ, Fz (ξ0 i ζ) ∂P₀
        let δν : Fin n → ℝ := fun i => ∫ x, Fz (ξ i x) ∂ν
        let δη : ℕ → Fin n → ℝ := fun k i => ∫ x, Fz (η k i x) ∂ν
        let L0 : ℝ := ∑ i : Fin n, δ0 i
        let Lν : ℝ := ∑ i : Fin n, δν i
        let Lη : ℕ → ℝ := fun k => ∑ i : Fin n, δη k i
        let scalarBudget : ℝ := ∫ o : Ω, Fz (g o / N) ∂μ
        @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ ∧
        P₀ = @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P ∧
        IsProbabilityMeasure ν ∧ MeasurePreserving q ν P₀ ∧
        (∀ k : ℕ, 0 < ε k ∧ ε k < 1 / (4 * Real.sqrt (n : ℝ))) ∧
        Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ)) ∧
        (∀ i : Fin n, Measurable[mAug, borel ℝ] (ξ i) ∧ MemLp (ξ i) 2 ν ∧
          (∫ x, ξ i x ∂ν) = 0) ∧
        (∑ i : Fin n, ∫ x, (ξ i x) ^ 2 ∂ν) = 1 ∧
        (∀ (k : ℕ) (i : Fin n), Measurable[mAugLocal, borel ℝ] (Ylocal k i) ∧
          Measurable[mAug, borel ℝ] (Y k i) ∧ ∀ x : Fin n → Ω × ℝ, |Y k i x - ξ i x| ≤ ε k) ∧
        (∀ ζ : Fin n → Ω, (1 / 2 : ℝ) ≤ 1 + D2 ζ ∧ |D2 ζ| ≤ B0 ζ) ∧
        (∀ ζ : Fin n → Ω, projectionV n g ζ = 0 → T0 ζ = 0) ∧
        (∀ (k : ℕ) (x : Fin n → Ω × ℝ), Vη k x = 0 → Tη k x = 0) ∧
        (∀ k : ℕ, (1 / 2 : ℝ) < s k ∧
          (∀ (i : Fin n) (x : Fin n → Ω × ℝ), η k i x = ηlocal k i (x i)) ∧
          iIndepFun (η k) ν ∧
          (∀ i : Fin n, Measurable[mAug, borel ℝ] (η k i) ∧ MemLp (η k i) 2 ν ∧
            (∫ x, η k i x ∂ν) = 0) ∧
          (∑ i : Fin n, ∫ x, (η k i x) ^ 2 ∂ν) = 1 ∧
          ν {x : Fin n → Ω × ℝ | Vη k x = 0} = 0 ∧
          (∀ᵐ x ∂ν, 0 < Vη k x ∧ 0 < b x ∧ 0 < Vη k x * b x)) ∧
        (∀ (k : ℕ) (x : Fin n → Ω × ℝ),
          Dη k x = D1 (q x) + Qε k x ∧
          Wη k x + Dη k x - z * Vη k x * b x = W x + D1 (q x) - z * V x * b x ∧
          |Qε k x| ≤ M k x ∧ |Dη k x| ≤ Anew k x) ∧
        Measurable[mAug, borel ℝ] H ∧ Integrable[mAug] H ν ∧
        (∀ i : Fin n, Measurable[mAug, borel ℝ] (Hdelete i) ∧ Integrable[mAug] (Hdelete i) ν) ∧
        (∀ k : ℕ, Measurable[mAug, borel ℝ] (Qε k) ∧ Integrable[mAug] (Qε k) ν ∧
          Integrable[mAug] (fun x => |Qε k x|) ν ∧
          (∫ x, |Qε k x| ∂ν) ≤ K * ε k * (∫ x, H x ∂ν)) ∧
        Filter.Tendsto (fun k => ∫ x, |Qε k x| ∂ν) Filter.atTop (nhds (0 : ℝ)) ∧
        (∀ k : ℕ, Measurable[mAug, borel ℝ] (Anew k) ∧ Integrable[mAug] (Anew k) ν ∧
          ∀ x : Fin n → Ω × ℝ, 0 ≤ Anew k x) ∧
        (∀ (k : ℕ) (i : Fin n), Measurable[mAug, borel ℝ] (AdeleteNew k i) ∧
          Integrable[mAug] (AdeleteNew k i) ν ∧ ∀ x : Fin n → Ω × ℝ, 0 ≤ AdeleteNew k i x) ∧
        (∀ k : ℕ, Integrable[mAug] (fun x => |Anew k x - A x|) ν ∧
          (∫ x, |Anew k x - A x| ∂ν) = ε k * (K * (∫ x, H x ∂ν))) ∧
        (∀ (k : ℕ) (i : Fin n), Integrable[mAug] (fun x => |AdeleteNew k i x - Adelete i x|) ν ∧
          (∫ x, |AdeleteNew k i x - Adelete i x| ∂ν) = ε k * (K * (∫ x, Hdelete i x ∂ν))) ∧
        Filter.Tendsto (fun k => ∫ x, |Anew k x - A x| ∂ν) Filter.atTop (nhds (0 : ℝ)) ∧
        (∀ i : Fin n, Filter.Tendsto (fun k => ∫ x, |AdeleteNew k i x - Adelete i x| ∂ν)
          Filter.atTop (nhds (0 : ℝ))) ∧
        (∀ (k : ℕ) (i : Fin n) (x : Fin n → Ω × ℝ),
          Δ k i x = M k x - Mdelete k i x ∧ |Δ k i x| ≤ M k x + Mdelete k i x) ∧
        (∀ (k : ℕ) (i : Fin n), Integrable[mAug] (fun x => |Δ k i x|) ν ∧
          (∫ x, |Δ k i x| ∂ν) ≤ ε k * (K * ((∫ x, H x ∂ν) + (∫ x, Hdelete i x ∂ν)))) ∧
        (∀ k : ℕ, ∃ Ffull : (Fin n → ℝ) → ℝ × ℝ × ℝ,
          Measurable[borel (Fin n → ℝ), borel (ℝ × ℝ × ℝ)] Ffull ∧
          ∀ x : Fin n → Ω × ℝ, (M k x, Anew k x, B x) = Ffull (C k x)) ∧
        (∀ (k : ℕ) (i : Fin n), ∃ Fdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
          Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdelete ∧
          ∀ x : Fin n → Ω × ℝ,
            (Mdelete k i x, AdeleteNew k i x, Bdelete i x) =
              Fdelete (fun j : {j : Fin n // j ≠ i} => η k j.val x)) ∧
        (∀ k : ℕ, ∃ G1 G2 : (Fin n → ℝ) → ℝ,
          Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
          Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
          ∀ x : Fin n → Ω × ℝ, Dη k x = G1 (C k x) ∧ D2 (q x) = G2 (C k x)) ∧
        Integrable[mN] (fun ζ => fullTest0 ζ * Real.exp (S0 ζ)) P ∧
        (∀ k : ℕ, Integrable[mAug] (fun x => fullTestη k x * Real.exp (Sη k x)) ν) ∧
        (∀ i : Fin n, Integrable[mN] (fun ζ => deletedTest0 i ζ * Real.exp (S0minus i ζ)) P) ∧
        (∀ (k : ℕ) (i : Fin n), Integrable[mAug] (fun x => deletedTestη k i x * Real.exp (Sηminus k i x)) ν) ∧
        (∀ i : Fin n, Integrable[mN] (compactDeletedTest0 i) P) ∧
        (∀ (k : ℕ) (i : Fin n), Integrable[mAug] (compactDeletedTestη k i) ν) ∧
        0 < I0 ∧ (∀ k : ℕ, 0 < Iη k) ∧
        Filter.Tendsto Iη Filter.atTop (nhds I0) ∧
        Filter.Tendsto (fun k => ∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν)
          Filter.atTop (nhds (∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P)) ∧
        (∀ i : Fin n, Filter.Tendsto (fun k => ∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν)
          Filter.atTop (nhds (∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P))) ∧
        Filter.Tendsto (fun k => (∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) / Iη k)
          Filter.atTop (nhds ((∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P) / I0)) ∧
        (∀ i : Fin n, Filter.Tendsto (fun k => (∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k)
          Filter.atTop (nhds ((∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P) / I0))) ∧
        (∀ i : Fin n, Filter.Tendsto (fun k => ∫ x, compactDeletedTestη k i x ∂ν)
          Filter.atTop (nhds (∫ ζ, compactDeletedTest0 i ζ ∂P))) ∧
        Filter.Tendsto sourceCostη Filter.atTop (nhds sourceCost0) ∧
        Filter.Tendsto compactCostη Filter.atTop (nhds compactCost0) ∧
        (1 ≤ z →
          Integrable[mΩ] (fun o : Ω => Fz (g o / N)) μ ∧
          (∀ i : Fin n,
            Measurable[mN₀, borel ℝ] (fun ζ => Fz (ξ0 i ζ)) ∧
            Integrable[mN] (fun ζ => Fz (ξ0 i ζ)) P ∧
            Integrable[mN₀] (fun ζ => Fz (ξ0 i ζ)) P₀ ∧
            Integrable[mAug] (fun x => Fz (ξ i x)) ν ∧
            δreduced i = δ0 i ∧ δν i = δ0 i ∧ δ0 i = scalarBudget) ∧
          L0 = (n : ℝ) * scalarBudget ∧
          (∀ i : Fin n, L0 = (n : ℝ) * δ0 i) ∧
          (∀ i : Fin n, 0 ≤ δ0 i) ∧ 0 ≤ L0 ∧ Lν = L0 ∧
          L0 ≤ β * Real.rpow z p / Real.rpow (n : ℝ) ((p - 2) / 2) ∧
          (β = 0 → L0 = 0 ∧ (∀ i : Fin n, δ0 i = 0)) ∧
          ((β = 0 ∨
              (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                Real.rpow (n : ℝ) ((p - 2) / (2 * p)))) →
            L0 ≤ Real.rpow cWindow p ∧
            (∀ i : Fin n, δ0 i < (1 / 2 : ℝ)) ∧
            L0 < cBudget * z ^ 2 ∧
            (∀ (k : ℕ) (i : Fin n),
              Integrable[mAug] (fun x => Fz (η k i x)) ν) ∧
            (∀ i : Fin n,
              Filter.Tendsto (fun k : ℕ => δη k i) Filter.atTop (nhds (δ0 i))) ∧
            Filter.Tendsto Lη Filter.atTop (nhds L0) ∧
            (∀ (τ : ℝ), 0 < τ →
              ∃ k0 : ℕ, ∀ (k : ℕ), k0 ≤ k →
                (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧
                Lη k < cBudget * z ^ 2 ∧
                (∀ i : Fin n, |δη k i - δ0 i| < τ) ∧
                |Lη k - L0| < τ ∧
                (∫ x, |Qε k x| ∂ν) < τ ∧
                (∫ x, |Anew k x - A x| ∂ν) < τ ∧
                (∀ i : Fin n, (∫ x, |AdeleteNew k i x - Adelete i x| ∂ν) < τ) ∧
                |Iη k - I0| < τ ∧
                |(∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) -
                  (∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P)| < τ ∧
                (∀ i : Fin n,
                  |(∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν) -
                    (∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P)| < τ) ∧
                |((∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) / Iη k) -
                  ((∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P) / I0)| < τ ∧
                (∀ i : Fin n,
                  |((∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k) -
                    ((∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P) / I0)| < τ) ∧
                (∀ i : Fin n,
                  |(∫ x, compactDeletedTestη k i x ∂ν) -
                    (∫ ζ, compactDeletedTest0 i ζ ∂P)| < τ) ∧
                |sourceCostη k - sourceCost0| < τ ∧
                |compactCostη k - compactCost0| < τ)))) ∧
      (∀ (Cenv aenv t0 Menv : ℝ)
          (hCenv : 0 ≤ Cenv) (haenv : 0 ≤ aenv)
          (ht0 : 0 < t0) (hMenv : 0 ≤ Menv),
        ∀ᶠ n : ℕ in Filter.atTop,
          4 ≤ n ∧
          ∀ (w : Ω → ℝ)
            (hW : ∀ᵐ o : Ω ∂μ, 0 ≤ w o)
            (hWR : ∀ᵐ o : Ω ∂μ,
              w o ≤ boundedPolylogHeight Cenv aenv n)
            (hSq : Integrable[mΩ] (fun o : Ω => (w o) ^ (2 : ℕ)) μ)
            (hSqBound : (∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ≤ Menv)
            (hEnv : ∀ᵐ t : Ω × Ω ∂(@Measure.prod Ω Ω mΩ mΩ μ μ),
              |r t.1 t.2| ≤ w t.1 * w t.2)
            (z : ℝ) (hz : (1 : ℝ) ≤ z)
            (hzWindow : z ≤ remainderWindowScale
              (Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv) t0 *
                Real.rpow (n : ℝ) (1 / 6 : ℝ)),
        let mN : MeasurableSpace (Fin n → Ω) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ)
        let mN₀ : MeasurableSpace (Fin n → Ω) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => m₀)
        let P : @Measure (Fin n → Ω) mN :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mΩ) (fun _ : Fin n => μ)
        let P₀ : @Measure (Fin n → Ω) mN₀ :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => m₀) (fun _ : Fin n => μ₀)
        let N : ℝ := Real.sqrt (n : ℝ)
        let ε : ℕ → ℝ := fun k => 1 / (8 * Real.sqrt (n : ℝ) * ((k : ℝ) + 1))
        let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
        let D1 : (Fin n → Ω) → ℝ := residualStatisticD n r
        let D2 : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho 1
        let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
        let mAugLocal : MeasurableSpace (Ω × ℝ) := m₀.prod (borel ℝ)
        let mAug : MeasurableSpace (Fin n → Ω × ℝ) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (fun _ : Fin n => mAugLocal)
        let νlocal : Fin n → @Measure (Ω × ℝ) mAugLocal :=
          fun _ => @Measure.prod Ω ℝ m₀ (borel ℝ) μ₀ lambda01
        let ν : @Measure (Fin n → Ω × ℝ) mAug :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (inferInstance : Fintype (Fin n)) (fun _ : Fin n => mAugLocal) νlocal
        let q : (Fin n → Ω × ℝ) → (Fin n → Ω) := fun x i => (x i).1
        let c : Fin n → (Ω × ℝ) → ℝ := fun _ =>
          Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode
            (MeasurableSpace.natGeneratingSequence (Ω × ℝ))
        let ξlocal : Fin n → (Ω × ℝ) → ℝ := fun i t => g t.1 / N
        let Ylocal : ℕ → Fin n → (Ω × ℝ) → ℝ := fun k i =>
          Shao.OQ6.QuantizedObservationCoding.quantizedObservation (ε k) (ξlocal i) (c i)
        let ξ : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => ξlocal i (x i)
        let Y : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x => Ylocal k i (x i)
        let a : ℕ → Fin n → ℝ := fun k =>
          Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν (Y k)
        let s : ℕ → ℝ := fun k =>
          Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν (Y k)
        let ηlocal : ℕ → Fin n → (Ω × ℝ) → ℝ := fun k i =>
          Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a k i) (s k) (Ylocal k i)
        let η : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k =>
          Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
        let C : ℕ → (Fin n → Ω × ℝ) → (Fin n → ℝ) := fun k x i => η k i x
        let W : (Fin n → Ω × ℝ) → ℝ := fun x => ∑ i : Fin n, ξ i x
        let V : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (ξ i x) ^ 2)
        let Wη : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => ∑ i : Fin n, η k i x
        let Vη : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => Real.sqrt (∑ i : Fin n, (η k i x) ^ 2)
        let b : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (1 + D2 (q x))
        let Qε : ℕ → (Fin n → Ω × ℝ) → ℝ :=
          fun k x => W x - Wη k x + z * b x * (Vη k x - V x)
        let Dη : ℕ → (Fin n → Ω × ℝ) → ℝ :=
          fun k x => D1 (q x) + W x - Wη k x + z * b x * (Vη k x - V x)
        let V0 : (Fin n → Ω) → ℝ := projectionV n g
        let qOrder : ℝ := boundedPolylogMomentOrder t0 n
        let Ktail : ℝ := Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv
        let Gsource : Set (Fin n → Ω) := projectionGood n g z
        let C2source : Set (Fin n → Ω) :=
          {ζ : Fin n → Ω |
            |Shao.OQ6.CanonicalDoubleGhostScalarMoments.originalUpper n r ζ| ≤
              Ktail * (n : ℝ) * qOrder ∧
            ‖Shao.OQ6.CanonicalDoubleGhostRowMoments.originalRows n r ζ‖ ^ (2 : ℕ) ≤
              Ktail * (n : ℝ) ^ (2 : ℕ) * qOrder}
        let Hsource : Set (Fin n → Ω) := Gsource ∩ C2source
        let Ssafe : Set (Fin n → Ω) :=
          {ζ : Fin n → Ω |
            0 < V0 ζ ∧ z * |D1 ζ| ≤ V0 ζ / 8 ∧
              z ^ (2 : ℕ) * |D2 ζ| ≤ (1 / 8 : ℝ)}
        let Jsafe : Set (Fin n → Ω × ℝ) := q ⁻¹' Ssafe
        let E : ℕ → Set (Fin n → Ω × ℝ) := fun k =>
          {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4}
        let E2 : Set (Fin n → Ω × ℝ) :=
          {x : Fin n → Ω × ℝ |
            z ^ (2 : ℕ) * |D2 (q x)| > (1 / 4 : ℝ)}
        let Z : Set (Fin n → Ω × ℝ) :=
          {x : Fin n → Ω × ℝ | V x = 0}
        let payment : ℝ :=
          (3 : ℝ) * Real.exp (-qOrder) + Real.exp (-cg * (n : ℝ)) +
            (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ))
        Measurable[mN₀, borel ℝ] V0 ∧
        Measurable[mN₀, borel ℝ] D1 ∧
        Measurable[mN₀, borel ℝ] D2 ∧
        Measurable[mAug, borel ℝ] (fun x => D1 (q x)) ∧
        Measurable[mAug, borel ℝ] (fun x => D2 (q x)) ∧
        (∀ x : Fin n → Ω × ℝ,
          W x = projectionW n g (q x) ∧ V x = V0 (q x)) ∧
        @MeasurableSet (Fin n → Ω) mN Hsource ∧
        @MeasurableSet (Fin n → Ω) mN₀ Ssafe ∧
        @MeasurableSet (Fin n → Ω) mN Ssafe ∧
        @MeasurableSet (Fin n → Ω × ℝ) mAug Jsafe ∧
        Hsource ⊆ Ssafe ∧
        (∀ x : Fin n → Ω × ℝ, x ∈ Jsafe →
          0 < V x ∧ z * |D1 (q x)| ≤ V x / 8 ∧
            z ^ (2 : ℕ) * |D2 (q x)| ≤ (1 / 8 : ℝ)) ∧
        ν.real Jsafeᶜ = P₀.real Ssafeᶜ ∧
        P₀.real Ssafeᶜ = P.real Ssafeᶜ ∧
        P.real Ssafeᶜ ≤ P.real Hsourceᶜ ∧
        P.real Hsourceᶜ ≤ payment ∧
        ν.real Jsafeᶜ ≤ payment ∧
        (({ζ : Fin n → Ω | V0 ζ = 0} ∪
          {ζ : Fin n → Ω | Real.sqrt (centeredSq n g r ζ) = 0}) ⊆
            Hsourceᶜ) ∧
        (∀ (k : ℕ) (i : Fin n),
          Measurable[mAug, borel ℝ] (η k i)) ∧
        (∀ k : ℕ, Measurable[mAug, borel ℝ] (Qε k) ∧
          Measurable[mAug, borel ℝ] (Dη k) ∧
          @MeasurableSet (Fin n → Ω × ℝ) mAug (E k)) ∧
        (@MeasurableSet (Fin n → Ω × ℝ) mAug E2 ∧
          @MeasurableSet (Fin n → Ω × ℝ) mAug Z) ∧
        (∀ (i : Fin n) (x : Fin n → Ω × ℝ),
          Filter.Tendsto (fun k : ℕ => η k i x)
            Filter.atTop (nhds (ξ i x))) ∧
        (∀ x : Fin n → Ω × ℝ,
          Filter.Tendsto (fun k : ℕ => Wη k x)
            Filter.atTop (nhds (W x))) ∧
        (∀ x : Fin n → Ω × ℝ,
          Filter.Tendsto (fun k : ℕ => Vη k x)
            Filter.atTop (nhds (V x))) ∧
        (∀ x : Fin n → Ω × ℝ,
          Filter.Tendsto (fun k : ℕ => Qε k x)
            Filter.atTop (nhds (0 : ℝ))) ∧
        (∀ x : Fin n → Ω × ℝ,
          Filter.Tendsto (fun k : ℕ => Dη k x)
            Filter.atTop (nhds (D1 (q x)))) ∧
        (∀ x : Fin n → Ω × ℝ, x ∈ Jsafe →
          (7 / 8 : ℝ) ≤ 1 + D2 (q x) ∧ 0 < b x) ∧
        (∀ x : Fin n → Ω × ℝ, x ∈ Jsafe →
          ∀ᶠ k : ℕ in Filter.atTop,
            0 < Vη k x ∧ z * |Dη k x| ≤ Vη k x / 4) ∧
        E2 ⊆ Jsafeᶜ ∧ Z ⊆ Jsafeᶜ ∧
        ν.real E2 ≤ ν.real Jsafeᶜ ∧
        ν.real Z ≤ ν.real Jsafeᶜ ∧
        ν.real E2 ≤ payment ∧ ν.real Z ≤ payment ∧
        (∀ δ : ℝ, 0 < δ →
          ∀ᶠ k : ℕ in Filter.atTop,
            ν.real (E k) ≤ ν.real Jsafeᶜ + δ) ∧
        Filter.limsup (fun k : ℕ => ν.real (E k))
          Filter.atTop ≤ ν.real Jsafeᶜ ∧
        (∀ δ : ℝ, 0 < δ →
          ∀ᶠ k : ℕ in Filter.atTop,
            ν.real (E k) ≤ payment + δ) ∧
        Filter.limsup (fun k : ℕ => ν.real (E k))
          Filter.atTop ≤ payment)
```

## Current project applications supporting the ordinary measurable-map route

The complete CoordinateBorelFactorization source uses `Measurable.of_eval` with `measurable_pi_apply` to construct full and deleted product maps, converts the real finite Pi measurable structure with `BorelSpace.measurable_eq`, and uses `MeasurableSpace.comap_comp`. Those exact project applications were inspected. For the new diagonal, each coordinate is the identity on the same mAugLocal, so `Measurable.of_eval` supplies its product measurability; composition with each exported238 measurable global xi yields local xi. No measure-preserving property is asserted for the diagonal.

The direct route invokes `countable_uniform_augmented_base_four_code` with the SAME m0 and trimmed probability mu0, then `quantized_observation_spec` at the SAME epsilon k, local xi and c. Its scalar comap equality feeds `deterministic_affine_observation_spec` at the literal actual coordinate mean a k i and scale s k. The required strict positivity follows from retained238 s k>1/2. No new local L2/mean/energy premise is needed by this route.

FiniteUniformCodingAssembly is an alternate interface only. It requires local reduced-coordinate measurable/L2/mean/energy data that238 does not export in that literal form. The preferred route avoids reconstructing those moments. OriginalClippedCanonicalCoding has a separately existentially selected m0; no application of it is authorized as an identity of model witnesses.

For `actual_normalized_integrable_tail_assembly`, substitute the carrier Fin n -> Omega x Real, measurable space mAug, law nu and the existing xi/Y/epsilon/eta. The new all-functions full factorization supplies hFullFactor exactly, and the new literal Adelete/Bdelete scalar factors supply hAdeleteFactor/hBdeleteFactor exactly. This does not establish any other missing premise or apply the assembly. In particular its hSZ remains an explicit external mathematical boundary. Its deleted eta cost uses the unperturbed Adelete; retained238 analytic sourceCosteta uses AdeleteNew. No equality of those costs is asserted here.

## Source availability and certification level

Pinned Lean is leanprover/lean4:v4.36.0-rc1; pinned mathlib is 807d3836b165983210ee2ecf3cd28f239436949c. They were read from the local curated version files. No local Lean executable, server, network, or actual elaborator was used. No external Mathlib source tree was inspected; the project APIs and the exact observed project applications above are the inspected primary context. Instance elaboration of the proposed new statement and proof remains for the authorized later server gate. The candidate is INCOMPLETE as a theorem and carries no new machine or independent-review certificate.
