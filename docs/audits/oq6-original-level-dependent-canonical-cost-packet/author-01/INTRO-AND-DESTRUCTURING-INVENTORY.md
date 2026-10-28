# 第255单元全部引入与拆解绑定

所列类型为完整源码依赖表达式；实际 elaborated TYPE 尚待服务器。

## intro — 第296行

```lean
  intro g r v rho
```

`g`
```lean
Ω → ℝ
:= fun o => ∫ y, h o y ∂μ
```

`r`
```lean
Ω → Ω → ℝ
:= fun o y => h o y - g o - g y
```

`v`
```lean
ℝ
:= ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω mΩ mΩ μ μ)
```

`rho`
```lean
ℝ
:= Real.sqrt v
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## rcases — 第301行

```lean
  rcases hcanonical with ⟨m₀, hm₀, hcg, hbase⟩
```

`m₀`
```lean
MeasurableSpace Ω
```

`hm₀`
```lean
m₀ ≤ mΩ
```

`hcg`
```lean
@MeasurableSpace.CountablyGenerated Ω m₀
```

`hbase`
```lean
      let μ₀ : @Measure Ω m₀ := μ.trim hm₀
      letI : MeasurableSpace Ω := m₀
      letI : MeasurableSpace.CountablyGenerated Ω := hcg
      IsProbabilityMeasure μ₀ ∧
      ∀ (n : ℕ) (hn : 4 ≤ n)
          (y : ℝ) (hy : 1 ≤ y)
          (hywindow : y ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ)))
          (ε : ℝ) (hε : 0 < ε)
          (hεsmall : ε < 1 / (4 * Real.sqrt (n : ℝ))),
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
        let O : Fin n → (Fin n → Ω) → Ω := fun i ξ => ξ i
        let gcoord : Fin n → Ω → ℝ := fun _ o => g o / N
        let Q : (Fin n → Ω) → (Fin n → Ω) := fun ξ i => O i ξ
        let D1 : (Fin n → Ω) → ℝ := residualStatisticD n r
        let D2 : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho y
        let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho y
        let Ddel : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
        let Jdel : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
        let Bdelete : (Fin n → Ω) → Fin n → ℝ := studentizerClipBudgetDeleted n r 512 rho y
        let κ : (Fin n → Ω) → ℝ := fun _ => 0
        let W0 : (Fin n → Ω) → ℝ := fun ξ => ∑ i : Fin n, gcoord i (O i ξ)
        let V0 : (Fin n → Ω) → ℝ :=
          fun ξ => Real.sqrt (∑ i : Fin n, (gcoord i (O i ξ)) ^ 2)
        let T0 : (Fin n → Ω) → ℝ := fun ξ =>
          if V0 ξ = 0 then κ ξ else
            (W0 ξ + D1 (Q ξ)) / (V0 ξ * Real.sqrt (1 + D2 (Q ξ)))
        let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
        let mAugLocal : MeasurableSpace (Ω × ℝ) := m₀.prod (borel ℝ)
        let mAug : MeasurableSpace (Fin n → Ω × ℝ) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (fun _ : Fin n => mAugLocal)
        let νlocal : Fin n → @Measure (Ω × ℝ) mAugLocal :=
          fun _ => @Measure.prod Ω ℝ m₀ (borel ℝ) μ₀ lambda01
        let ν : @Measure (Fin n → Ω × ℝ) mAug :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mAugLocal) νlocal
        let q : (Fin n → Ω × ℝ) → (Fin n → Ω) := fun x i => (x i).1
        let c : Fin n → (Ω × ℝ) → ℝ := fun _ =>
          Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode
            (MeasurableSpace.natGeneratingSequence (Ω × ℝ))
        let ξlocal : Fin n → (Ω × ℝ) → ℝ := fun i t => gcoord i t.1
        let Ylocal : Fin n → (Ω × ℝ) → ℝ := fun i =>
          Shao.OQ6.QuantizedObservationCoding.quantizedObservation ε (ξlocal i) (c i)
        let ξ : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => gcoord i (x i).1
        let Y : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => Ylocal i (x i)
        let a : Fin n → ℝ := Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν Y
        let s : ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν Y
        let ηlocal : Fin n → (Ω × ℝ) → ℝ := fun i =>
          Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a i) s (Ylocal i)
        let η : Fin n → (Fin n → Ω × ℝ) → ℝ :=
          Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
        let C : (Fin n → Ω × ℝ) → (Fin n → ℝ) := fun x i => η i x
        let W : (Fin n → Ω × ℝ) → ℝ := fun x => ∑ i : Fin n, ξ i x
        let V : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (ξ i x) ^ 2)
        let Wη : (Fin n → Ω × ℝ) → ℝ := fun x => ∑ i : Fin n, η i x
        let Vη : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (η i x) ^ 2)
        let b : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (1 + D2 (q x))
        let Dη : ℝ → (Fin n → Ω × ℝ) → ℝ :=
          fun z x => D1 (q x) + W x - Wη x + z * b x * (Vη x - V x)
        let Tη : ℝ → (Fin n → Ω × ℝ) → ℝ :=
          fun z x => (Wη x + Dη z x) / (Vη x * b x)
        let Z0 : Set (Fin n → Ω) := {ξ | projectionV n g ξ = 0}
        let Z : Set (Fin n → Ω × ℝ) := {x | V x = 0}
        let p0 : ℝ := P.real Z0
        let comparisons : Set (ℝ → ℝ → Prop) :=
          {R | R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
            R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
            R = (fun a b : ℝ => a = b)}
        let F0 : (ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω) := fun R z =>
          {ξ | R (projectionW n g ξ + D1 ξ)
            (z * projectionV n g ξ * Real.sqrt (1 + D2 ξ))}
        let A0 : (ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω) :=
          fun R z => {ξ | R (Tclip ξ) z}
        let Eη : (ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω × ℝ) :=
          fun R z => {x | R (Tη z x) z}
        @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ ∧
        P₀ = @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P ∧
        (∀ i : Fin n, Measurable (O i) ∧ MeasurePreserving (O i) P₀ μ₀) ∧
        iIndepFun O P₀ ∧
        (∀ i : Fin n, Measurable (gcoord i) ∧
          MemLp (fun ξ => gcoord i (O i ξ)) 2 P₀ ∧
          (∫ ξ, gcoord i (O i ξ) ∂P₀) = 0 ∧
          (∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1 / (n : ℝ)) ∧
        (∑ i : Fin n, ∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1 ∧
        Q = id ∧ W0 = projectionW n g ∧ V0 = projectionV n g ∧ T0 = Tclip ∧
        Measurable D1 ∧ Measurable D2 ∧
        (∀ ξ : Fin n → Ω, (1 / 2 : ℝ) ≤ 1 + D2 ξ) ∧
        Measurable[mN₀, borel ℝ] Tclip ∧ Measurable[mN, borel ℝ] Tclip ∧
        @Measure.map (Fin n → Ω) ℝ mN₀ (borel ℝ) Tclip P₀ =
          @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) Tclip P ∧
        IsProbabilityMeasure ν ∧ MeasurePreserving q ν P₀ ∧
        (1 / 2 : ℝ) < s ∧
        (∀ (i : Fin n) (x : Fin n → Ω × ℝ), η i x = ηlocal i (x i)) ∧
        iIndepFun η ν ∧
        (∀ i : Fin n, Measurable (η i) ∧ MemLp (η i) 2 ν) ∧
        (∀ i : Fin n, Integrable (η i) ν ∧ Integrable (fun x => (η i x) ^ 2) ν) ∧
        (∀ i : Fin n, (∫ x, η i x ∂ν) = 0) ∧
        (∑ i : Fin n, ∫ x, (η i x) ^ 2 ∂ν) = 1 ∧
        (∀ (i : Fin n) (t : ℝ), ν {x : Fin n → Ω × ℝ | η i x = t} = 0) ∧
        ν {x : Fin n → Ω × ℝ | Vη x = 0} = 0 ∧
        (∀ᵐ x ∂ν, 0 < Vη x ∧ 0 < b x ∧ 0 < Vη x * b x) ∧
        Measurable[mAug, borel (Fin n → ℝ)] C ∧
        MeasurableSpace.comap C (borel (Fin n → ℝ)) = mAug ∧
        (∀ (H : (Fin n → Ω × ℝ) → ℝ), Measurable H →
          ∃ F : (Fin n → ℝ) → ℝ, Measurable[borel (Fin n → ℝ), borel ℝ] F ∧
            ∀ x : Fin n → Ω × ℝ, H x = F (C x)) ∧
        (∀ (i : Fin n) (d : ({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ), Measurable d →
          ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
            (∀ y : {j : Fin n // j ≠ i} → Ω × ℝ,
              d y = F (fun j => ηlocal j.val (y j))) ∧
            Measurable[borel (Fin n → ℝ), borel ℝ]
              (fun t : Fin n → ℝ => F (fun j => t j.val)) ∧
            ∀ x : Fin n → Ω × ℝ, d (fun j => x j.val) = F (fun j => η j.val x)) ∧
        (∃ G2 : (Fin n → ℝ) → ℝ,
          Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
          (∀ x : Fin n → Ω × ℝ, D2 (q x) = G2 (C x)) ∧
          ∀ z : ℝ, ∃ G1 : (Fin n → ℝ) → ℝ,
            Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
            ∀ x : Fin n → Ω × ℝ, Dη z x = G1 (C x)) ∧
        (∀ i : Fin n,
          ∃ Fdel : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdel ∧
            ∀ x : Fin n → Ω × ℝ,
              (Ddel (q x) i, Jdel (q x) i, Bdelete (q x) i) =
                Fdel (fun j : {j : Fin n // j ≠ i} => η j.val x)) ∧
        (∀ z : ℝ, Measurable (Dη z) ∧ Measurable (Tη z)) ∧
        MeasurableSet[mN₀] Z0 ∧ MeasurableSet[mN] Z0 ∧ MeasurableSet Z ∧
        ν Z = P₀ Z0 ∧ P₀ Z0 = P Z0 ∧ ν.real Z = p0 ∧
        (∀ (z : ℝ) (x : Fin n → Ω × ℝ),
          Wη x + Dη z x - z * Vη x * b x = W x + D1 (q x) - z * V x * b x) ∧
        (∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
          MeasurableSet[mN₀] (A0 R z) ∧ MeasurableSet[mN] (A0 R z) ∧
          MeasurableSet[mN₀] (F0 R z) ∧ MeasurableSet[mN] (F0 R z) ∧
          MeasurableSet (Eη R z) ∧
          ν (Eη R z) = P₀ (F0 R z) ∧ P₀ (F0 R z) = P (F0 R z) ∧
          (∀ ξ : Fin n → Ω, ξ ∈ (A0 R z ∆ F0 R z) → ξ ∈ Z0) ∧
          P (A0 R z ∆ F0 R z) ≤ P Z0 ∧
          |P.real (A0 R z) - ν.real (Eη R z)| ≤ p0)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## intro — 第303行

```lean
  intro μ₀
```

`μ₀`
```lean
@Measure Ω m₀
:= μ.trim hm₀
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## rcases — 第306行

```lean
  rcases hbase with ⟨hμ₀prob, hfor⟩
```

`hμ₀prob`
```lean
IsProbabilityMeasure μ₀
```

`hfor`
```lean
∀ (n : ℕ) (hn : 4 ≤ n)
          (y : ℝ) (hy : 1 ≤ y)
          (hywindow : y ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ)))
          (ε : ℝ) (hε : 0 < ε)
          (hεsmall : ε < 1 / (4 * Real.sqrt (n : ℝ))),
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
        let O : Fin n → (Fin n → Ω) → Ω := fun i ξ => ξ i
        let gcoord : Fin n → Ω → ℝ := fun _ o => g o / N
        let Q : (Fin n → Ω) → (Fin n → Ω) := fun ξ i => O i ξ
        let D1 : (Fin n → Ω) → ℝ := residualStatisticD n r
        let D2 : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho y
        let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho y
        let Ddel : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
        let Jdel : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
        let Bdelete : (Fin n → Ω) → Fin n → ℝ := studentizerClipBudgetDeleted n r 512 rho y
        let κ : (Fin n → Ω) → ℝ := fun _ => 0
        let W0 : (Fin n → Ω) → ℝ := fun ξ => ∑ i : Fin n, gcoord i (O i ξ)
        let V0 : (Fin n → Ω) → ℝ :=
          fun ξ => Real.sqrt (∑ i : Fin n, (gcoord i (O i ξ)) ^ 2)
        let T0 : (Fin n → Ω) → ℝ := fun ξ =>
          if V0 ξ = 0 then κ ξ else
            (W0 ξ + D1 (Q ξ)) / (V0 ξ * Real.sqrt (1 + D2 (Q ξ)))
        let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
        let mAugLocal : MeasurableSpace (Ω × ℝ) := m₀.prod (borel ℝ)
        let mAug : MeasurableSpace (Fin n → Ω × ℝ) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (fun _ : Fin n => mAugLocal)
        let νlocal : Fin n → @Measure (Ω × ℝ) mAugLocal :=
          fun _ => @Measure.prod Ω ℝ m₀ (borel ℝ) μ₀ lambda01
        let ν : @Measure (Fin n → Ω × ℝ) mAug :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mAugLocal) νlocal
        let q : (Fin n → Ω × ℝ) → (Fin n → Ω) := fun x i => (x i).1
        let c : Fin n → (Ω × ℝ) → ℝ := fun _ =>
          Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode
            (MeasurableSpace.natGeneratingSequence (Ω × ℝ))
        let ξlocal : Fin n → (Ω × ℝ) → ℝ := fun i t => gcoord i t.1
        let Ylocal : Fin n → (Ω × ℝ) → ℝ := fun i =>
          Shao.OQ6.QuantizedObservationCoding.quantizedObservation ε (ξlocal i) (c i)
        let ξ : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => gcoord i (x i).1
        let Y : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => Ylocal i (x i)
        let a : Fin n → ℝ := Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν Y
        let s : ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν Y
        let ηlocal : Fin n → (Ω × ℝ) → ℝ := fun i =>
          Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a i) s (Ylocal i)
        let η : Fin n → (Fin n → Ω × ℝ) → ℝ :=
          Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
        let C : (Fin n → Ω × ℝ) → (Fin n → ℝ) := fun x i => η i x
        let W : (Fin n → Ω × ℝ) → ℝ := fun x => ∑ i : Fin n, ξ i x
        let V : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (ξ i x) ^ 2)
        let Wη : (Fin n → Ω × ℝ) → ℝ := fun x => ∑ i : Fin n, η i x
        let Vη : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (η i x) ^ 2)
        let b : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (1 + D2 (q x))
        let Dη : ℝ → (Fin n → Ω × ℝ) → ℝ :=
          fun z x => D1 (q x) + W x - Wη x + z * b x * (Vη x - V x)
        let Tη : ℝ → (Fin n → Ω × ℝ) → ℝ :=
          fun z x => (Wη x + Dη z x) / (Vη x * b x)
        let Z0 : Set (Fin n → Ω) := {ξ | projectionV n g ξ = 0}
        let Z : Set (Fin n → Ω × ℝ) := {x | V x = 0}
        let p0 : ℝ := P.real Z0
        let comparisons : Set (ℝ → ℝ → Prop) :=
          {R | R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
            R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
            R = (fun a b : ℝ => a = b)}
        let F0 : (ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω) := fun R z =>
          {ξ | R (projectionW n g ξ + D1 ξ)
            (z * projectionV n g ξ * Real.sqrt (1 + D2 ξ))}
        let A0 : (ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω) :=
          fun R z => {ξ | R (Tclip ξ) z}
        let Eη : (ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω × ℝ) :=
          fun R z => {x | R (Tη z x) z}
        @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ ∧
        P₀ = @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P ∧
        (∀ i : Fin n, Measurable (O i) ∧ MeasurePreserving (O i) P₀ μ₀) ∧
        iIndepFun O P₀ ∧
        (∀ i : Fin n, Measurable (gcoord i) ∧
          MemLp (fun ξ => gcoord i (O i ξ)) 2 P₀ ∧
          (∫ ξ, gcoord i (O i ξ) ∂P₀) = 0 ∧
          (∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1 / (n : ℝ)) ∧
        (∑ i : Fin n, ∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1 ∧
        Q = id ∧ W0 = projectionW n g ∧ V0 = projectionV n g ∧ T0 = Tclip ∧
        Measurable D1 ∧ Measurable D2 ∧
        (∀ ξ : Fin n → Ω, (1 / 2 : ℝ) ≤ 1 + D2 ξ) ∧
        Measurable[mN₀, borel ℝ] Tclip ∧ Measurable[mN, borel ℝ] Tclip ∧
        @Measure.map (Fin n → Ω) ℝ mN₀ (borel ℝ) Tclip P₀ =
          @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) Tclip P ∧
        IsProbabilityMeasure ν ∧ MeasurePreserving q ν P₀ ∧
        (1 / 2 : ℝ) < s ∧
        (∀ (i : Fin n) (x : Fin n → Ω × ℝ), η i x = ηlocal i (x i)) ∧
        iIndepFun η ν ∧
        (∀ i : Fin n, Measurable (η i) ∧ MemLp (η i) 2 ν) ∧
        (∀ i : Fin n, Integrable (η i) ν ∧ Integrable (fun x => (η i x) ^ 2) ν) ∧
        (∀ i : Fin n, (∫ x, η i x ∂ν) = 0) ∧
        (∑ i : Fin n, ∫ x, (η i x) ^ 2 ∂ν) = 1 ∧
        (∀ (i : Fin n) (t : ℝ), ν {x : Fin n → Ω × ℝ | η i x = t} = 0) ∧
        ν {x : Fin n → Ω × ℝ | Vη x = 0} = 0 ∧
        (∀ᵐ x ∂ν, 0 < Vη x ∧ 0 < b x ∧ 0 < Vη x * b x) ∧
        Measurable[mAug, borel (Fin n → ℝ)] C ∧
        MeasurableSpace.comap C (borel (Fin n → ℝ)) = mAug ∧
        (∀ (H : (Fin n → Ω × ℝ) → ℝ), Measurable H →
          ∃ F : (Fin n → ℝ) → ℝ, Measurable[borel (Fin n → ℝ), borel ℝ] F ∧
            ∀ x : Fin n → Ω × ℝ, H x = F (C x)) ∧
        (∀ (i : Fin n) (d : ({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ), Measurable d →
          ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
            (∀ y : {j : Fin n // j ≠ i} → Ω × ℝ,
              d y = F (fun j => ηlocal j.val (y j))) ∧
            Measurable[borel (Fin n → ℝ), borel ℝ]
              (fun t : Fin n → ℝ => F (fun j => t j.val)) ∧
            ∀ x : Fin n → Ω × ℝ, d (fun j => x j.val) = F (fun j => η j.val x)) ∧
        (∃ G2 : (Fin n → ℝ) → ℝ,
          Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
          (∀ x : Fin n → Ω × ℝ, D2 (q x) = G2 (C x)) ∧
          ∀ z : ℝ, ∃ G1 : (Fin n → ℝ) → ℝ,
            Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
            ∀ x : Fin n → Ω × ℝ, Dη z x = G1 (C x)) ∧
        (∀ i : Fin n,
          ∃ Fdel : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdel ∧
            ∀ x : Fin n → Ω × ℝ,
              (Ddel (q x) i, Jdel (q x) i, Bdelete (q x) i) =
                Fdel (fun j : {j : Fin n // j ≠ i} => η j.val x)) ∧
        (∀ z : ℝ, Measurable (Dη z) ∧ Measurable (Tη z)) ∧
        MeasurableSet[mN₀] Z0 ∧ MeasurableSet[mN] Z0 ∧ MeasurableSet Z ∧
        ν Z = P₀ Z0 ∧ P₀ Z0 = P Z0 ∧ ν.real Z = p0 ∧
        (∀ (z : ℝ) (x : Fin n → Ω × ℝ),
          Wη x + Dη z x - z * Vη x * b x = W x + D1 (q x) - z * V x * b x) ∧
        (∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
          MeasurableSet[mN₀] (A0 R z) ∧ MeasurableSet[mN] (A0 R z) ∧
          MeasurableSet[mN₀] (F0 R z) ∧ MeasurableSet[mN] (F0 R z) ∧
          MeasurableSet (Eη R z) ∧
          ν (Eη R z) = P₀ (F0 R z) ∧ P₀ (F0 R z) = P (F0 R z) ∧
          (∀ ξ : Fin n → Ω, ξ ∈ (A0 R z ∆ F0 R z) → ξ ∈ Z0) ∧
          P (A0 R z ∆ F0 R z) ≤ P Z0 ∧
          |P.real (A0 R z) - ν.real (Eη R z)| ≤ p0)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## intro — 第308行

```lean
  intro n hn y hy hywindow ε hε hεsmall
```

`n`
```lean
ℕ
```

`hn`
```lean
4 ≤ n
```

`y`
```lean
ℝ
```

`hy`
```lean
1 ≤ y
```

`hywindow`
```lean
y ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ))
```

`ε`
```lean
ℝ
```

`hε`
```lean
0 < ε
```

`hεsmall`
```lean
ε < 1 / (4 * Real.sqrt (n : ℝ))
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## intro — 第309行

```lean
  intro mN mN₀ P P₀ N O gcoord Q D1 D2 Tclip Ddel Jdel Bdelete κ W0 V0 T0
    lambda01 mAugLocal mAug νlocal ν q c ξlocal Ylocal ξ Y a s ηlocal η C W V
    Wη Vη b Dη Tη Z0 Z p0 comparisons F0 A0 Eη
    J A Adel B deletionMass deletionTotal
    ξ0 S0 S0delete Sν Sνdelete fullTest0 deleteTest0 fullTestν deleteTestν
    Ioriginal Ireduced Icoded costOriginal costReduced costCoded
```

`mN`
```lean
MeasurableSpace (Fin n → Ω)
:= @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ)
```

`mN₀`
```lean
MeasurableSpace (Fin n → Ω)
:= @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => m₀)
```

`P`
```lean
@Measure (Fin n → Ω) mN
:= @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mΩ) (fun _ : Fin n => μ)
```

`P₀`
```lean
@Measure (Fin n → Ω) mN₀
:= @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => m₀) (fun _ : Fin n => μ₀)
```

`N`
```lean
ℝ
:= Real.sqrt (n : ℝ)
```

`O`
```lean
Fin n → (Fin n → Ω) → Ω
:= fun i ξ => ξ i
```

`gcoord`
```lean
Fin n → Ω → ℝ
:= fun _ o => g o / N
```

`Q`
```lean
(Fin n → Ω) → (Fin n → Ω)
:= fun ξ i => O i ξ
```

`D1`
```lean
(Fin n → Ω) → ℝ
:= residualStatisticD n r
```

`D2`
```lean
(Fin n → Ω) → ℝ
:= clippedCenteredDelta n g r 512 rho y
```

`Tclip`
```lean
(Fin n → Ω) → ℝ
:= clippedCenteredStatistic n g r 512 rho y
```

`Ddel`
```lean
(Fin n → Ω) → Fin n → ℝ
:= residualStatisticDDeleted n r
```

`Jdel`
```lean
(Fin n → Ω) → Fin n → ℝ
:= residualEnergyJDeleted n r
```

`Bdelete`
```lean
(Fin n → Ω) → Fin n → ℝ
:= studentizerClipBudgetDeleted n r 512 rho y
```

`κ`
```lean
(Fin n → Ω) → ℝ
:= fun _ => 0
```

`W0`
```lean
(Fin n → Ω) → ℝ
:= fun ξ => ∑ i : Fin n, gcoord i (O i ξ)
```

`V0`
```lean
(Fin n → Ω) → ℝ
:= fun ξ => Real.sqrt (∑ i : Fin n, (gcoord i (O i ξ)) ^ 2)
```

`T0`
```lean
(Fin n → Ω) → ℝ
:= fun ξ =>
          if V0 ξ = 0 then κ ξ else
            (W0 ξ + D1 (Q ξ)) / (V0 ξ * Real.sqrt (1 + D2 (Q ξ)))
```

`lambda01`
```lean
Measure ℝ
:= (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
```

`mAugLocal`
```lean
MeasurableSpace (Ω × ℝ)
:= m₀.prod (borel ℝ)
```

`mAug`
```lean
MeasurableSpace (Fin n → Ω × ℝ)
:= @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (fun _ : Fin n => mAugLocal)
```

`νlocal`
```lean
Fin n → @Measure (Ω × ℝ) mAugLocal
:= fun _ => @Measure.prod Ω ℝ m₀ (borel ℝ) μ₀ lambda01
```

`ν`
```lean
@Measure (Fin n → Ω × ℝ) mAug
:= @Measure.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mAugLocal) νlocal
```

`q`
```lean
(Fin n → Ω × ℝ) → (Fin n → Ω)
:= fun x i => (x i).1
```

`c`
```lean
Fin n → (Ω × ℝ) → ℝ
:= fun _ =>
          Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode
            (MeasurableSpace.natGeneratingSequence (Ω × ℝ))
```

`ξlocal`
```lean
Fin n → (Ω × ℝ) → ℝ
:= fun i t => gcoord i t.1
```

`Ylocal`
```lean
Fin n → (Ω × ℝ) → ℝ
:= fun i =>
          Shao.OQ6.QuantizedObservationCoding.quantizedObservation ε (ξlocal i) (c i)
```

`ξ`
```lean
Fin n → (Fin n → Ω × ℝ) → ℝ
:= fun i x => gcoord i (x i).1
```

`Y`
```lean
Fin n → (Fin n → Ω × ℝ) → ℝ
:= fun i x => Ylocal i (x i)
```

`a`
```lean
Fin n → ℝ
:= Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν Y
```

`s`
```lean
ℝ
:= Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν Y
```

`ηlocal`
```lean
Fin n → (Ω × ℝ) → ℝ
:= fun i =>
          Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a i) s (Ylocal i)
```

`η`
```lean
Fin n → (Fin n → Ω × ℝ) → ℝ
:= Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
```

`C`
```lean
(Fin n → Ω × ℝ) → (Fin n → ℝ)
:= fun x i => η i x
```

`W`
```lean
(Fin n → Ω × ℝ) → ℝ
:= fun x => ∑ i : Fin n, ξ i x
```

`V`
```lean
(Fin n → Ω × ℝ) → ℝ
:= fun x => Real.sqrt (∑ i : Fin n, (ξ i x) ^ 2)
```

`Wη`
```lean
(Fin n → Ω × ℝ) → ℝ
:= fun x => ∑ i : Fin n, η i x
```

`Vη`
```lean
(Fin n → Ω × ℝ) → ℝ
:= fun x => Real.sqrt (∑ i : Fin n, (η i x) ^ 2)
```

`b`
```lean
(Fin n → Ω × ℝ) → ℝ
:= fun x => Real.sqrt (1 + D2 (q x))
```

`Dη`
```lean
ℝ → (Fin n → Ω × ℝ) → ℝ
:= fun z x => D1 (q x) + W x - Wη x + z * b x * (Vη x - V x)
```

`Tη`
```lean
ℝ → (Fin n → Ω × ℝ) → ℝ
:= fun z x => (Wη x + Dη z x) / (Vη x * b x)
```

`Z0`
```lean
Set (Fin n → Ω)
:= {ξ | projectionV n g ξ = 0}
```

`Z`
```lean
Set (Fin n → Ω × ℝ)
:= {x | V x = 0}
```

`p0`
```lean
ℝ
:= P.real Z0
```

`comparisons`
```lean
Set (ℝ → ℝ → Prop)
:= {R | R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
            R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
            R = (fun a b : ℝ => a = b)}
```

`F0`
```lean
(ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω)
:= fun R z =>
          {ξ | R (projectionW n g ξ + D1 ξ)
            (z * projectionV n g ξ * Real.sqrt (1 + D2 ξ))}
```

`A0`
```lean
(ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω)
:= fun R z => {ξ | R (Tclip ξ) z}
```

`Eη`
```lean
(ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω × ℝ)
:= fun R z => {x | R (Tη z x) z}
```

`J`
```lean
(Fin n → Ω) → ℝ
:= residualEnergyJ n r
```

`A`
```lean
(Fin n → Ω) → ℝ
:= fun ξ : Fin n → Ω => |D1 ξ|
```

`Adel`
```lean
(Fin n → Ω) → Fin n → ℝ
:= fun (ξ : Fin n → Ω) (i : Fin n) => |Ddel ξ i|
```

`B`
```lean
(Fin n → Ω) → ℝ
:= studentizerClipBudget n r 512 rho y
```

`deletionMass`
```lean
(Fin n → Ω) → Fin n → ℝ
:= fun (ξ : Fin n → Ω) (i : Fin n) =>
            |A ξ - Adel ξ i| + |B ξ - Bdelete ξ i|
```

`deletionTotal`
```lean
(Fin n → Ω) → ℝ
:= fun ξ : Fin n → Ω => ∑ i : Fin n, deletionMass ξ i
```

`ξ0`
```lean
Fin n → (Fin n → Ω) → ℝ
:= fun i ζ => gcoord i (O i ζ)
```

`S0`
```lean
(Fin n → Ω) → ℝ
:= fun ζ =>
          ∑ j : Fin n, (y * ξ0 j ζ - (y * ξ0 j ζ) ^ 2 / 2)
```

`S0delete`
```lean
(Fin n → Ω) → Fin n → ℝ
:= fun ζ i =>
          ∑ j ∈ Finset.univ.erase i, (y * ξ0 j ζ - (y * ξ0 j ζ) ^ 2 / 2)
```

`Sν`
```lean
(Fin n → Ω × ℝ) → ℝ
:= fun x =>
          ∑ j : Fin n, (y * ξ j x - (y * ξ j x) ^ 2 / 2)
```

`Sνdelete`
```lean
(Fin n → Ω × ℝ) → Fin n → ℝ
:= fun x i =>
          ∑ j ∈ Finset.univ.erase i, (y * ξ j x - (y * ξ j x) ^ 2 / 2)
```

`fullTest0`
```lean
(Fin n → Ω) → ℝ
:= fun ζ => y * A ζ + y ^ 2 * B ζ
```

`deleteTest0`
```lean
(Fin n → Ω) → Fin n → ℝ
:= fun ζ i =>
          min |y * ξ0 i ζ| 1 * (|A ζ - Adel ζ i| + y * |B ζ - Bdelete ζ i|)
```

`fullTestν`
```lean
(Fin n → Ω × ℝ) → ℝ
:= fun x => fullTest0 (q x)
```

`deleteTestν`
```lean
(Fin n → Ω × ℝ) → Fin n → ℝ
:= fun x i => deleteTest0 (q x) i
```

`Ioriginal`
```lean
ℝ
:= ∫ ζ : Fin n → Ω, Real.exp (S0 ζ) ∂P
```

`Ireduced`
```lean
ℝ
:= ∫ ζ : Fin n → Ω, Real.exp (S0 ζ) ∂P₀
```

`Icoded`
```lean
ℝ
:= ∫ x : Fin n → Ω × ℝ, Real.exp (Sν x) ∂ν
```

`costOriginal`
```lean
ℝ
:= ((∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P) +
            ∑ i : Fin n, ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P) / Ioriginal
```

`costReduced`
```lean
ℝ
:= ((∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P₀) +
            ∑ i : Fin n, ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P₀) / Ireduced
```

`costCoded`
```lean
ℝ
:= ((∫ x, fullTestν x * Real.exp (Sν x) ∂ν) +
            ∑ i : Fin n, ∫ x, deleteTestν x i * Real.exp (Sνdelete x i) ∂ν) / Icoded
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## rcases — 第316行

```lean
  rcases hcan with
    ⟨hP₀prob, hP₀map, hO, hOindep, hgcoord, hgenergy,
      hQid, hW0eq, hV0eq, hT0eq, hD1m, hD2m, hhalf,
      hTclipm, hTclipOriginal, hTcliplaw, hνprob, hqpres,
      hs, hηeval, hηindep, hηL2, hηInts, hηmean, hηenergy,
      hηnull, hVηnull, hpositiveDenominator, hCmeas, hCcomap,
      hfactor, hretained, hscalar, hdeletedFactor, hTηmeas,
      hZ0m, hZ0Original, hZmeas, hZcodedlaw, hZ0law,
      hZcodedreal, hsigned, hcomparison⟩
```

`hP₀prob`
```lean
@IsProbabilityMeasure (Fin n → Ω) mN₀ P₀
```

`hP₀map`
```lean
P₀ = @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P
```

`hO`
```lean
(∀ i : Fin n, Measurable (O i) ∧ MeasurePreserving (O i) P₀ μ₀)
```

`hOindep`
```lean
iIndepFun O P₀
```

`hgcoord`
```lean
(∀ i : Fin n, Measurable (gcoord i) ∧
          MemLp (fun ξ => gcoord i (O i ξ)) 2 P₀ ∧
          (∫ ξ, gcoord i (O i ξ) ∂P₀) = 0 ∧
          (∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1 / (n : ℝ))
```

`hgenergy`
```lean
(∑ i : Fin n, ∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1
```

`hQid`
```lean
Q = id
```

`hW0eq`
```lean
W0 = projectionW n g
```

`hV0eq`
```lean
V0 = projectionV n g
```

`hT0eq`
```lean
T0 = Tclip
```

`hD1m`
```lean
Measurable D1
```

`hD2m`
```lean
Measurable D2
```

`hhalf`
```lean
(∀ ξ : Fin n → Ω, (1 / 2 : ℝ) ≤ 1 + D2 ξ)
```

`hTclipm`
```lean
Measurable[mN₀, borel ℝ] Tclip
```

`hTclipOriginal`
```lean
Measurable[mN, borel ℝ] Tclip
```

`hTcliplaw`
```lean
@Measure.map (Fin n → Ω) ℝ mN₀ (borel ℝ) Tclip P₀ =
          @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) Tclip P
```

`hνprob`
```lean
IsProbabilityMeasure ν
```

`hqpres`
```lean
MeasurePreserving q ν P₀
```

`hs`
```lean
(1 / 2 : ℝ) < s
```

`hηeval`
```lean
(∀ (i : Fin n) (x : Fin n → Ω × ℝ), η i x = ηlocal i (x i))
```

`hηindep`
```lean
iIndepFun η ν
```

`hηL2`
```lean
(∀ i : Fin n, Measurable (η i) ∧ MemLp (η i) 2 ν)
```

`hηInts`
```lean
(∀ i : Fin n, Integrable (η i) ν ∧ Integrable (fun x => (η i x) ^ 2) ν)
```

`hηmean`
```lean
(∀ i : Fin n, (∫ x, η i x ∂ν) = 0)
```

`hηenergy`
```lean
(∑ i : Fin n, ∫ x, (η i x) ^ 2 ∂ν) = 1
```

`hηnull`
```lean
(∀ (i : Fin n) (t : ℝ), ν {x : Fin n → Ω × ℝ | η i x = t} = 0)
```

`hVηnull`
```lean
ν {x : Fin n → Ω × ℝ | Vη x = 0} = 0
```

`hpositiveDenominator`
```lean
(∀ᵐ x ∂ν, 0 < Vη x ∧ 0 < b x ∧ 0 < Vη x * b x)
```

`hCmeas`
```lean
Measurable[mAug, borel (Fin n → ℝ)] C
```

`hCcomap`
```lean
MeasurableSpace.comap C (borel (Fin n → ℝ)) = mAug
```

`hfactor`
```lean
(∀ (H : (Fin n → Ω × ℝ) → ℝ), Measurable H →
          ∃ F : (Fin n → ℝ) → ℝ, Measurable[borel (Fin n → ℝ), borel ℝ] F ∧
            ∀ x : Fin n → Ω × ℝ, H x = F (C x))
```

`hretained`
```lean
(∀ (i : Fin n) (d : ({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ), Measurable d →
          ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
            (∀ y : {j : Fin n // j ≠ i} → Ω × ℝ,
              d y = F (fun j => ηlocal j.val (y j))) ∧
            Measurable[borel (Fin n → ℝ), borel ℝ]
              (fun t : Fin n → ℝ => F (fun j => t j.val)) ∧
            ∀ x : Fin n → Ω × ℝ, d (fun j => x j.val) = F (fun j => η j.val x))
```

`hscalar`
```lean
(∃ G2 : (Fin n → ℝ) → ℝ,
          Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
          (∀ x : Fin n → Ω × ℝ, D2 (q x) = G2 (C x)) ∧
          ∀ z : ℝ, ∃ G1 : (Fin n → ℝ) → ℝ,
            Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
            ∀ x : Fin n → Ω × ℝ, Dη z x = G1 (C x))
```

`hdeletedFactor`
```lean
(∀ i : Fin n,
          ∃ Fdel : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdel ∧
            ∀ x : Fin n → Ω × ℝ,
              (Ddel (q x) i, Jdel (q x) i, Bdelete (q x) i) =
                Fdel (fun j : {j : Fin n // j ≠ i} => η j.val x))
```

`hTηmeas`
```lean
(∀ z : ℝ, Measurable (Dη z) ∧ Measurable (Tη z))
```

`hZ0m`
```lean
MeasurableSet[mN₀] Z0
```

`hZ0Original`
```lean
MeasurableSet[mN] Z0
```

`hZmeas`
```lean
MeasurableSet Z
```

`hZcodedlaw`
```lean
ν Z = P₀ Z0
```

`hZ0law`
```lean
P₀ Z0 = P Z0
```

`hZcodedreal`
```lean
ν.real Z = p0
```

`hsigned`
```lean
(∀ (z : ℝ) (x : Fin n → Ω × ℝ),
          Wη x + Dη z x - z * Vη x * b x = W x + D1 (q x) - z * V x * b x)
```

`hcomparison`
```lean
(∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
          MeasurableSet[mN₀] (A0 R z) ∧ MeasurableSet[mN] (A0 R z) ∧
          MeasurableSet[mN₀] (F0 R z) ∧ MeasurableSet[mN] (F0 R z) ∧
          MeasurableSet (Eη R z) ∧
          ν (Eη R z) = P₀ (F0 R z) ∧ P₀ (F0 R z) = P (F0 R z) ∧
          (∀ ξ : Fin n → Ω, ξ ∈ (A0 R z ∆ F0 R z) → ξ ∈ Z0) ∧
          P (A0 R z ∆ F0 R z) ≤ P Z0 ∧
          |P.real (A0 R z) - ν.real (Eη R z)| ≤ p0)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## rcases — 第335行

```lean
  rcases hcost with
    ⟨_, _, _, _, hAIP, hAdelIP, hBIP, hBdeleteIP, heIP,
      hFullBounds, hDeletedBounds, _⟩
```

`_discard1`
```lean
MemLp (D1) 2 (P)
```

`_discard2`
```lean
(∀ i : Fin n, MemLp (fun ζ => (Ddel) ζ i) 2 (P))
```

`_discard3`
```lean
Integrable (J) (P)
```

`_discard4`
```lean
(∀ i : Fin n, Integrable (fun ζ => (Jdel) ζ i) (P))
```

`hAIP`
```lean
Integrable (A) (P)
```

`hAdelIP`
```lean
(∀ i : Fin n, Integrable ((fun i ζ => Adel ζ i) i) (P))
```

`hBIP`
```lean
Integrable (B) (P)
```

`hBdeleteIP`
```lean
(∀ i : Fin n, Integrable ((fun i ζ => Bdelete ζ i) i) (P))
```

`heIP`
```lean
Integrable (D2) (P)
```

`hFullBounds`
```lean
(∀ ζ : Fin n → Ω, 0 ≤ (A) ζ ∧ 0 ≤ (B) ζ ∧ |(D2) ζ| ≤ (B) ζ)
```

`hDeletedBounds`
```lean
(∀ (i : Fin n) (ζ : Fin n → Ω), 0 ≤ (fun i ζ => Adel ζ i) i ζ ∧ 0 ≤ (fun i ζ => Bdelete ζ i) i ζ)
```

`_discard_remaining`
```lean
(∀ i : Fin n, Measurable ((ξ0) i) ∧ MemLp ((ξ0) i) 2 (P) ∧ (∫ ζ, (ξ0) i ζ ∂(P)) = 0) ∧
(∑ i : Fin n, ∫ ζ, ((ξ0) i ζ) ^ 2 ∂(P)) = 1 ∧
(∀ ζ : Fin n → Ω, (V0) ζ = projectionV n (g) ζ) ∧
Measurable (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ∧
Integrable (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) (P) ∧
(∀ i : Fin n, Measurable ((fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i) ∧ Integrable ((fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i) (P)) ∧
(∀ ζ : Fin n → Ω, 0 < (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ) ∧
(∀ (i : Fin n) (ζ : Fin n → Ω), 0 < (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ) ∧
(∀ ε : ℝ, Measurable ((fun ε ζ => 4 * ε * (N) * (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ) ε) ∧ Integrable ((fun ε ζ => 4 * ε * (N) * (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ) ε) (P) ∧
      Integrable (fun ζ => |(fun ε ζ => 4 * ε * (N) * (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ) ε ζ|) (P)) ∧
(∀ (ε : ℝ) (i : Fin n), Measurable ((fun ε i ζ =>
      4 * ε * (N) * (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ) ε i) ∧ Integrable ((fun ε i ζ =>
      4 * ε * (N) * (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ) ε i) (P) ∧
      Integrable (fun ζ => |(fun ε i ζ =>
      4 * ε * (N) * (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ) ε i ζ|) (P)) ∧
(∀ ε : ℝ, 0 ≤ ε → ∀ ζ : Fin n → Ω,
      0 ≤ (fun ε ζ => 4 * ε * (N) * (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ) ε ζ ∧ ∀ i : Fin n, 0 ≤ (fun ε i ζ =>
      4 * ε * (N) * (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ) ε i ζ) ∧
(∀ i : Fin n, 0 ≤ (fun i =>
      4 * (N) * ((∫ ζ, (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ ∂(P)) + (∫ ζ, (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ ∂(P)))) i) ∧
(∀ (ε : ℝ) (i : Fin n),
      (∫ ζ, (fun ε ζ => 4 * ε * (N) * (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ) ε ζ ∂(P)) + (∫ ζ, (fun ε i ζ =>
      4 * ε * (N) * (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ) ε i ζ ∂(P)) = ε * (fun i =>
      4 * (N) * ((∫ ζ, (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ ∂(P)) + (∫ ζ, (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ ∂(P)))) i) ∧
(∀ (ε : ℝ) (i : Fin n),
      (∫ ζ, |(fun ε ζ => 4 * ε * (N) * (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ) ε ζ| ∂(P)) + (∫ ζ, |(fun ε i ζ =>
      4 * ε * (N) * (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ) ε i ζ| ∂(P)) = |ε| * (fun i =>
      4 * (N) * ((∫ ζ, (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ ∂(P)) + (∫ ζ, (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ ∂(P)))) i) ∧
(∀ (ε : ℝ) (i : Fin n) (ζ : Fin n → Ω),
      (fun ε i ζ =>
      ((A) ζ + (fun ε ζ => 4 * ε * (N) * (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ) ε ζ) - ((fun i ζ => Adel ζ i) i ζ + (fun ε i ζ =>
      4 * ε * (N) * (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ) ε i ζ) - ((A) ζ - (fun i ζ => Adel ζ i) i ζ)) ε i ζ = (fun ε ζ => 4 * ε * (N) * (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ) ε ζ - (fun ε i ζ =>
      4 * ε * (N) * (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ) ε i ζ) ∧
(∀ (ε : ℝ) (i : Fin n) (ζ : Fin n → Ω),
      |(fun ε i ζ =>
      ((A) ζ + (fun ε ζ => 4 * ε * (N) * (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ) ε ζ) - ((fun i ζ => Adel ζ i) i ζ + (fun ε i ζ =>
      4 * ε * (N) * (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ) ε i ζ) - ((A) ζ - (fun i ζ => Adel ζ i) i ζ)) ε i ζ| ≤ |(fun ε ζ => 4 * ε * (N) * (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ) ε ζ| + |(fun ε i ζ =>
      4 * ε * (N) * (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ) ε i ζ|) ∧
(∀ (ε : ℝ) (i : Fin n), Measurable ((fun ε i ζ =>
      ((A) ζ + (fun ε ζ => 4 * ε * (N) * (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ) ε ζ) - ((fun i ζ => Adel ζ i) i ζ + (fun ε i ζ =>
      4 * ε * (N) * (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ) ε i ζ) - ((A) ζ - (fun i ζ => Adel ζ i) i ζ)) ε i) ∧ Integrable ((fun ε i ζ =>
      ((A) ζ + (fun ε ζ => 4 * ε * (N) * (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ) ε ζ) - ((fun i ζ => Adel ζ i) i ζ + (fun ε i ζ =>
      4 * ε * (N) * (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ) ε i ζ) - ((A) ζ - (fun i ζ => Adel ζ i) i ζ)) ε i) (P) ∧
      Integrable (fun ζ => |(fun ε i ζ =>
      ((A) ζ + (fun ε ζ => 4 * ε * (N) * (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ) ε ζ) - ((fun i ζ => Adel ζ i) i ζ + (fun ε i ζ =>
      4 * ε * (N) * (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ) ε i ζ) - ((A) ζ - (fun i ζ => Adel ζ i) i ζ)) ε i ζ|) (P) ∧
      (∫ ζ, |(fun ε i ζ =>
      ((A) ζ + (fun ε ζ => 4 * ε * (N) * (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ) ε ζ) - ((fun i ζ => Adel ζ i) i ζ + (fun ε i ζ =>
      4 * ε * (N) * (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ) ε i ζ) - ((A) ζ - (fun i ζ => Adel ζ i) i ζ)) ε i ζ| ∂(P)) ≤ |ε| * (fun i =>
      4 * (N) * ((∫ ζ, (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ ∂(P)) + (∫ ζ, (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ ∂(P)))) i) ∧
(∀ i : Fin n, Filter.Tendsto (fun ε : ℝ => ∫ ζ, |(fun ε i ζ =>
      ((A) ζ + (fun ε ζ => 4 * ε * (N) * (fun ζ => (1 + (V0) ζ) * ((N) + (y) * Real.sqrt (1 + (B) ζ))) ζ) ε ζ) - ((fun i ζ => Adel ζ i) i ζ + (fun ε i ζ =>
      4 * ε * (N) * (fun i ζ =>
      (1 + (fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, ((ξ0) j ζ) ^ 2)) i ζ) * ((N) + (y) * Real.sqrt (1 + (fun i ζ => Bdelete ζ i) i ζ))) i ζ) ε i ζ) - ((A) ζ - (fun i ζ => Adel ζ i) i ζ)) ε i ζ| ∂(P))
      (nhds (0 : ℝ)) (nhds (0 : ℝ)))
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## intro — 第356行

```lean
    intro i
```

`i`
```lean
Fin n
```

词法范围：{"enclosing": "proof of hτm", "contextFromLine": 354, "visibleThroughLine": 357, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## funext — 第359行

```lean
    funext i
```

`i`
```lean
Fin n
```

词法范围：{"enclosing": "proof of hqτ", "contextFromLine": 358, "visibleThroughLine": 360, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## rcases — 第368行

```lean
    rcases hdeletedFactor i with ⟨Fdel, hFdel, hFdelpoint⟩
```

`Fdel`
```lean
({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ
```

`hFdel`
```lean
Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdel
```

`hFdelpoint`
```lean
∀ x : Fin n → Ω × ℝ, (Ddel (q x) i, Jdel (q x) i, Bdelete (q x) i) = Fdel (fun j : {j : Fin n // j ≠ i} => η j.val x)
```

词法范围：{"enclosing": "proof of hDeletedMeasurable", "contextFromLine": 364, "visibleThroughLine": 391, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## intro — 第375行

```lean
      intro j
```

`j`
```lean
{j : Fin n // j ≠ i}
```

词法范围：{"enclosing": "proof of hRdel", "contextFromLine": 372, "visibleThroughLine": 376, "declarationIndent": 6, "coordinateConvention": "1-based inclusive"}

## funext — 第380行

```lean
      funext ζ
```

`ζ`
```lean
Fin n → Ω
```

词法范围：{"enclosing": "proof of hTriplePoint", "contextFromLine": 377, "visibleThroughLine": 381, "declarationIndent": 6, "coordinateConvention": "1-based inclusive"}

## funext — 第421行

```lean
      funext ζ
```

`ζ`
```lean
Fin n → Ω
```

词法范围：{"enclosing": "proof of hEq", "contextFromLine": 419, "visibleThroughLine": 422, "declarationIndent": 6, "coordinateConvention": "1-based inclusive"}

## funext — 第428行

```lean
      funext ζ
```

`ζ`
```lean
Fin n → Ω
```

词法范围：{"enclosing": "proof of hEq", "contextFromLine": 426, "visibleThroughLine": 429, "declarationIndent": 6, "coordinateConvention": "1-based inclusive"}

## intro — 第451行

```lean
    intro i
```

`i`
```lean
Fin n
```

词法范围：{"enclosing": "proof of hidN", "contextFromLine": 448, "visibleThroughLine": 454, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## rcases — 第508行

```lean
    rcases hDiff i with ⟨hADm, hBDm, hMassm, hADi, hBDi, hMassi⟩
```

`hADm`
```lean
Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => |A ζ - Adel ζ i|)
```

`hBDm`
```lean
Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => |B ζ - Bdelete ζ i|)
```

`hMassm`
```lean
Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => deletionMass ζ i)
```

`hADi`
```lean
Integrable (fun ζ : Fin n → Ω => |A ζ - Adel ζ i|) P₀
```

`hBDi`
```lean
Integrable (fun ζ : Fin n → Ω => |B ζ - Bdelete ζ i|) P₀
```

`hMassi`
```lean
Integrable (fun ζ : Fin n → Ω => deletionMass ζ i) P₀
```

词法范围：{"enclosing": "proof of hAugDeleted", "contextFromLine": 497, "visibleThroughLine": 517, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## rcases — 第523行

```lean
  rcases hweighted with ⟨hIoriginalPos, hFullOriginalI, hDeleteOriginalI,
    hCostOriginalNonneg, hCostOriginalBound⟩
```

`hIoriginalPos`
```lean
0 < (Ioriginal)
```

`hFullOriginalI`
```lean
Integrable (fun ζ => (fullTest0) ζ * Real.exp ((S0) ζ)) (P)
```

`hDeleteOriginalI`
```lean
(∀ i : Fin n,
      Integrable (fun ζ => (deleteTest0) ζ i * Real.exp ((S0delete) ζ i)) (P))
```

`hCostOriginalNonneg`
```lean
0 ≤ (costOriginal)
```

`hCostOriginalBound`
```lean
(costOriginal) ≤
      64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * ((512 : ℝ))) * (1 + (rho)) *
        (1 + (y)) ^ 3 / Real.sqrt (n : ℝ)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}
