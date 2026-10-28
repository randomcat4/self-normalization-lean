# 第254单元全部引入与产生绑定

完整依赖上下文由冻结声明与 SOURCE-INVENTORY 的精确源码坐标共同给出；以下无省略类型。

## intro — 第185行

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

## rcases — 第190行

```lean
  rcases hmodel with ⟨m₀, hm₀, hcg, hh₀, hf₀, hbase⟩
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

`hh₀`
```lean
Measurable[m₀.prod m₀, borel ℝ] (fun t : Ω × Ω => h t.1 t.2)
```

`hf₀`
```lean
∀ k : ℕ, Measurable[m₀, borel ℝ] (fun _o : Ω => (0 : ℝ))
```

`hbase`
```lean
      let μ₀ : @Measure Ω m₀ := μ.trim hm₀
      letI : MeasurableSpace Ω := m₀
      let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
      let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
      let v₀ : ℝ :=
        ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
      let rho₀ : ℝ := Real.sqrt v₀
      IsProbabilityMeasure μ₀ ∧
      μ₀ = @Measure.map Ω Ω mΩ m₀ id μ ∧
      g₀ = g ∧ r₀ = r ∧ v₀ = v ∧ rho₀ = rho ∧
      (∀ o : Ω, Integrable (h o) μ₀ ↔ rowIntegrable o) ∧
      MemLp (fun t : Ω × Ω => h t.1 t.2) 2
        (@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀) ∧
      (∫ t : Ω × Ω, h t.1 t.2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)) = 0 ∧
      Measurable g₀ ∧ MemLp g₀ 2 μ₀ ∧
      (∫ o, g₀ o ∂μ₀) = 0 ∧ (∫ o, g₀ o ^ 2 ∂μ₀) = 1 ∧
      Measurable (fun t : Ω × Ω => r₀ t.1 t.2) ∧
      MemLp (fun t : Ω × Ω => r₀ t.1 t.2) 2
        (@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀) ∧
      (∀ o y : Ω, r₀ o y = r₀ y o) ∧
      (∀ᵐ o ∂μ₀, (∫ y, r₀ o y ∂μ₀) = 0) ∧
      @Measure.map Ω ℝ m₀ (borel ℝ) g₀ μ₀ = projectionLaw ∧
      (∀ p : ℝ≥0∞, MemLp g₀ p μ₀ ↔ gLp p) ∧
      @Measure.prod Ω Ω m₀ m₀ μ₀ μ₀ =
        @Measure.map (Ω × Ω) (Ω × Ω)
          (mΩ.prod mΩ) (m₀.prod m₀) id pairLaw ∧
      (∀ (J : Type) (instJ : Fintype J),
        let mJ : MeasurableSpace (J → Ω) :=
          @MeasurableSpace.pi J (fun _ : J => Ω) (fun _ : J => mΩ)
        let mJ₀ : MeasurableSpace (J → Ω) :=
          @MeasurableSpace.pi J (fun _ : J => Ω) (fun _ : J => m₀)
        let P : @Measure (J → Ω) mJ :=
          @Measure.pi J (fun _ : J => Ω) instJ
            (fun _ : J => mΩ) (fun _ : J => μ)
        let P₀ : @Measure (J → Ω) mJ₀ :=
          @Measure.pi J (fun _ : J => Ω) instJ
            (fun _ : J => m₀) (fun _ : J => μ₀)
        @IsProbabilityMeasure (J → Ω) mJ₀ P₀ ∧
        Measurable[mJ, mJ₀] (id : (J → Ω) → J → Ω) ∧
        P₀ = @Measure.map (J → Ω) (J → Ω) mJ mJ₀ id P ∧
        ∀ (B : Type) (mB : MeasurableSpace B) (T : (J → Ω) → B),
          Measurable[mJ₀, mB] T →
          @Measure.map (J → Ω) B mJ₀ mB T P₀ =
            @Measure.map (J → Ω) B mJ mB T P) ∧
      (∀ (n : ℕ) (hn : 4 ≤ n)
          (z : ℝ) (hz : 1 ≤ z)
          (hwindow : z ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ))),
        (
            let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
            let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
            let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ₀.prod μ₀)
            let rho : ℝ := Real.sqrt v
            let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ₀)
            let N : ℝ := Real.sqrt (n : ℝ)
            let W : (Fin n → Ω) → ℝ := projectionW n g
            let V : (Fin n → Ω) → ℝ := projectionV n g
            let D : (Fin n → Ω) → ℝ := residualStatisticD n r
            let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
            let Ddelete : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
            let Jdelete : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
            let A : (Fin n → Ω) → ℝ := fun ζ => |D ζ|
            let Adelete : (Fin n → Ω) → Fin n → ℝ := fun ζ i => |Ddelete ζ i|
            let B : (Fin n → Ω) → ℝ := studentizerClipBudget n r 512 rho z
            let Bdelete : (Fin n → Ω) → Fin n → ℝ :=
              studentizerClipBudgetDeleted n r 512 rho z
            let d : (Fin n → Ω) → ℝ := centeredDelta n g r
            let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho z
            let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho z
            let s : (Fin n → Ω) → ℝ := fun ζ => Real.sqrt (centeredSq n g r ζ)
            let Tphysical : (Fin n → Ω) → ℝ := fun ζ =>
              if s ζ = 0 then 0 else (W ζ + D ζ) / s ζ
            let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
            let cap : (Fin n → Ω) → Fin n → ℝ := fun ζ i => min |z * ξ0 i ζ| 1
            let S : (Fin n → Ω) → ℝ := fun ζ =>
              ∑ j : Fin n, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)
            let Sdelete : (Fin n → Ω) → Fin n → ℝ := fun ζ i =>
              ∑ j ∈ Finset.univ.erase i, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)
            let fullTest : (Fin n → Ω) → ℝ := fun ζ => z * A ζ + z ^ 2 * B ζ
            let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ζ i =>
              cap ζ i * (|A ζ - Adelete ζ i| + z * |B ζ - Bdelete ζ i|)
            let I : ℝ := ∫ ζ, Real.exp (S ζ) ∂P
            let sourceCost : ℝ :=
              ((∫ ζ, fullTest ζ * Real.exp (S ζ) ∂P) +
                ∑ i : Fin n, ∫ ζ, deletedTest ζ i * Real.exp (Sdelete ζ i) ∂P) / I
            Measurable W ∧ Measurable V ∧ Measurable D ∧ Measurable J ∧
            Measurable A ∧ Measurable B ∧ Measurable d ∧ Measurable e ∧
            Measurable s ∧ Measurable Tclip ∧ Measurable Tphysical ∧
            Measurable fullTest ∧
            MeasurableSet {ζ : Fin n → Ω | V ζ = 0} ∧
            MeasurableSet {ζ : Fin n → Ω | s ζ = 0} ∧
            (∀ ζ : Fin n → Ω,
              (1 / 2 : ℝ) ≤ 1 + e ζ ∧ |e ζ| ≤ B ζ ∧ |e ζ| ≤ |d ζ| ∧
              (0 < V ζ → 0 < V ζ * Real.sqrt (1 + e ζ))) ∧
            (∀ ζ : Fin n → Ω, V ζ = 0 → d ζ = 0 ∧ e ζ = 0 ∧ Tclip ζ = 0) ∧
            (∀ ζ : Fin n → Ω, s ζ = 0 → Tphysical ζ = 0) ∧
            (∀ i : Fin n,
              Measurable (fun ζ : Fin n → Ω => cap ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => Ddelete ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => Jdelete ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => Adelete ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => Bdelete ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => deletedTest ζ i) ∧
              ∃ E : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ,
                Measurable E ∧ ∀ ζ : Fin n → Ω,
                  (Ddelete ζ i, Jdelete ζ i, Bdelete ζ i) =
                    E (fun j : {j : Fin n // j ≠ i} => ζ j.val)) ∧
            ((1 + rho) * z ≤ N →
              (∀ ζ : Fin n → Ω, ζ ∈ projectionGood n g z →
                -(1 / 2 : ℝ) ≤ d ζ →
                e ζ = d ζ ∧ 0 < V ζ * Real.sqrt (1 + e ζ) ∧
                0 < s ζ ∧ V ζ * Real.sqrt (1 + e ζ) = s ζ ∧
                Tclip ζ = Tphysical ζ) ∧
              {ζ : Fin n → Ω | Tclip ζ ≠ Tphysical ζ} ⊆
                (projectionGood n g z)ᶜ ∪ lowerStudentizerBad n g r z) ∧
            0 < I ∧
            Integrable (fun ζ => fullTest ζ * Real.exp (S ζ)) P ∧
            (∀ i : Fin n,
              Integrable (fun ζ => deletedTest ζ i * Real.exp (Sdelete ζ i)) P) ∧
            0 ≤ sourceCost ∧
            sourceCost ≤
              64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
                (1 + z) ^ 3 / Real.sqrt (n : ℝ)
        ) ∧
        (
            let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
            let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
            let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ₀.prod μ₀)
            let rho : ℝ := Real.sqrt v
            let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ₀)
            let N : ℝ := Real.sqrt (n : ℝ)
            let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
            let D : (Fin n → Ω) → ℝ := residualStatisticD n r
            let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
            let Ddelete : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
            let Jdelete : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
            let A : (Fin n → Ω) → ℝ := fun ζ => |D ζ|
            let Adelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ => |Ddelete ζ i|
            let B : (Fin n → Ω) → ℝ := studentizerClipBudget n r 512 rho z
            let Bdelete : Fin n → (Fin n → Ω) → ℝ :=
              fun i ζ => studentizerClipBudgetDeleted n r 512 rho z ζ i
            let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho z
            let V : (Fin n → Ω) → ℝ := fun ζ => Real.sqrt (∑ j : Fin n, (ξ0 j ζ) ^ 2)
            let Vdelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ =>
              Real.sqrt (∑ j ∈ Finset.univ.erase i, (ξ0 j ζ) ^ 2)
            let H : (Fin n → Ω) → ℝ := fun ζ => (1 + V ζ) * (N + z * Real.sqrt (1 + B ζ))
            let Hdelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ =>
              (1 + Vdelete i ζ) * (N + z * Real.sqrt (1 + Bdelete i ζ))
            let M : ℝ → (Fin n → Ω) → ℝ := fun ε ζ => 4 * ε * N * H ζ
            let Mdelete : ℝ → Fin n → (Fin n → Ω) → ℝ := fun ε i ζ =>
              4 * ε * N * Hdelete i ζ
            let κ : Fin n → ℝ := fun i =>
              4 * N * ((∫ ζ, H ζ ∂P) + (∫ ζ, Hdelete i ζ ∂P))
            let Δ : ℝ → Fin n → (Fin n → Ω) → ℝ := fun ε i ζ =>
              (A ζ + M ε ζ) - (Adelete i ζ + Mdelete ε i ζ) - (A ζ - Adelete i ζ)
            MemLp D 2 P ∧
            (∀ i : Fin n, MemLp (fun ζ => Ddelete ζ i) 2 P) ∧
            Integrable J P ∧ (∀ i : Fin n, Integrable (fun ζ => Jdelete ζ i) P) ∧
            Integrable A P ∧ (∀ i : Fin n, Integrable (Adelete i) P) ∧
            Integrable B P ∧ (∀ i : Fin n, Integrable (Bdelete i) P) ∧ Integrable e P ∧
            (∀ ζ : Fin n → Ω, 0 ≤ A ζ ∧ 0 ≤ B ζ ∧ |e ζ| ≤ B ζ) ∧
            (∀ (i : Fin n) (ζ : Fin n → Ω), 0 ≤ Adelete i ζ ∧ 0 ≤ Bdelete i ζ) ∧
            (∀ i : Fin n, Measurable (ξ0 i) ∧ MemLp (ξ0 i) 2 P ∧ (∫ ζ, ξ0 i ζ ∂P) = 0) ∧
            (∑ i : Fin n, ∫ ζ, (ξ0 i ζ) ^ 2 ∂P) = 1 ∧
            (∀ ζ : Fin n → Ω, V ζ = projectionV n g ζ) ∧
            Measurable H ∧ Integrable H P ∧
            (∀ i : Fin n, Measurable (Hdelete i) ∧ Integrable (Hdelete i) P) ∧
            (∀ ζ : Fin n → Ω, 0 < H ζ) ∧
            (∀ (i : Fin n) (ζ : Fin n → Ω), 0 < Hdelete i ζ) ∧
            (∀ ε : ℝ, Measurable (M ε) ∧ Integrable (M ε) P ∧
              Integrable (fun ζ => |M ε ζ|) P) ∧
            (∀ (ε : ℝ) (i : Fin n), Measurable (Mdelete ε i) ∧ Integrable (Mdelete ε i) P ∧
              Integrable (fun ζ => |Mdelete ε i ζ|) P) ∧
            (∀ ε : ℝ, 0 ≤ ε → ∀ ζ : Fin n → Ω,
              0 ≤ M ε ζ ∧ ∀ i : Fin n, 0 ≤ Mdelete ε i ζ) ∧
            (∀ i : Fin n, 0 ≤ κ i) ∧
            (∀ (ε : ℝ) (i : Fin n),
              (∫ ζ, M ε ζ ∂P) + (∫ ζ, Mdelete ε i ζ ∂P) = ε * κ i) ∧
            (∀ (ε : ℝ) (i : Fin n),
              (∫ ζ, |M ε ζ| ∂P) + (∫ ζ, |Mdelete ε i ζ| ∂P) = |ε| * κ i) ∧
            (∀ (ε : ℝ) (i : Fin n) (ζ : Fin n → Ω),
              Δ ε i ζ = M ε ζ - Mdelete ε i ζ) ∧
            (∀ (ε : ℝ) (i : Fin n) (ζ : Fin n → Ω),
              |Δ ε i ζ| ≤ |M ε ζ| + |Mdelete ε i ζ|) ∧
            (∀ (ε : ℝ) (i : Fin n), Measurable (Δ ε i) ∧ Integrable (Δ ε i) P ∧
              Integrable (fun ζ => |Δ ε i ζ|) P ∧
              (∫ ζ, |Δ ε i ζ| ∂P) ≤ |ε| * κ i) ∧
            (∀ i : Fin n, Filter.Tendsto (fun ε : ℝ => ∫ ζ, |Δ ε i ζ| ∂P)
              (nhds (0 : ℝ)) (nhds (0 : ℝ)))
        ))
```

## intro — 第192行

```lean
  intro μ₀
```

`μ₀`
```lean
@Measure Ω m₀
:= μ.trim hm₀
```

## rcases — 第195行

```lean
  rcases hbase with
    ⟨hμ₀prob, hμ₀map, hgpoint, hrpoint, hvpoint, hrhopoint, hrow,
      hh₂₀, hcenter₀, hgmeas₀, hg₂₀, hgmean₀, hgsecond₀,
      hrmeas₀, hr₂₀, hrsymm₀, hrcanonical₀, hglaw₀, hglp₀,
      hpair₀, hfinite, hstatistics⟩
```

`hμ₀prob`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
IsProbabilityMeasure μ₀
```

`hμ₀map`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
μ₀ = @Measure.map Ω Ω mΩ m₀ id μ
```

`hgpoint`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
g₀ = g
```

`hrpoint`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
r₀ = r
```

`hvpoint`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
v₀ = v
```

`hrhopoint`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
rho₀ = rho
```

`hrow`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
(∀ o : Ω, Integrable (h o) μ₀ ↔ rowIntegrable o)
```

`hh₂₀`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
MemLp (fun t : Ω × Ω => h t.1 t.2) 2
        (@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
```

`hcenter₀`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
(∫ t : Ω × Ω, h t.1 t.2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)) = 0
```

`hgmeas₀`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
Measurable g₀
```

`hg₂₀`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
MemLp g₀ 2 μ₀
```

`hgmean₀`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
(∫ o, g₀ o ∂μ₀) = 0
```

`hgsecond₀`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
(∫ o, g₀ o ^ 2 ∂μ₀) = 1
```

`hrmeas₀`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
Measurable (fun t : Ω × Ω => r₀ t.1 t.2)
```

`hr₂₀`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
MemLp (fun t : Ω × Ω => r₀ t.1 t.2) 2
        (@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
```

`hrsymm₀`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
(∀ o y : Ω, r₀ o y = r₀ y o)
```

`hrcanonical₀`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
(∀ᵐ o ∂μ₀, (∫ y, r₀ o y ∂μ₀) = 0)
```

`hglaw₀`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
@Measure.map Ω ℝ m₀ (borel ℝ) g₀ μ₀ = projectionLaw
```

`hglp₀`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
(∀ p : ℝ≥0∞, MemLp g₀ p μ₀ ↔ gLp p)
```

`hpair₀`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀ =
        @Measure.map (Ω × Ω) (Ω × Ω)
          (mΩ.prod mΩ) (m₀.prod m₀) id pairLaw
```

`hfinite`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
(∀ (J : Type) (instJ : Fintype J),
        let mJ : MeasurableSpace (J → Ω) :=
          @MeasurableSpace.pi J (fun _ : J => Ω) (fun _ : J => mΩ)
        let mJ₀ : MeasurableSpace (J → Ω) :=
          @MeasurableSpace.pi J (fun _ : J => Ω) (fun _ : J => m₀)
        let P : @Measure (J → Ω) mJ :=
          @Measure.pi J (fun _ : J => Ω) instJ
            (fun _ : J => mΩ) (fun _ : J => μ)
        let P₀ : @Measure (J → Ω) mJ₀ :=
          @Measure.pi J (fun _ : J => Ω) instJ
            (fun _ : J => m₀) (fun _ : J => μ₀)
        @IsProbabilityMeasure (J → Ω) mJ₀ P₀ ∧
        Measurable[mJ, mJ₀] (id : (J → Ω) → J → Ω) ∧
        P₀ = @Measure.map (J → Ω) (J → Ω) mJ mJ₀ id P ∧
        ∀ (B : Type) (mB : MeasurableSpace B) (T : (J → Ω) → B),
          Measurable[mJ₀, mB] T →
          @Measure.map (J → Ω) B mJ₀ mB T P₀ =
            @Measure.map (J → Ω) B mJ mB T P)
```

`hstatistics`
```lean
letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
(∀ (n : ℕ) (hn : 4 ≤ n)
          (z : ℝ) (hz : 1 ≤ z)
          (hwindow : z ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ))),
        (
            let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
            let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
            let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ₀.prod μ₀)
            let rho : ℝ := Real.sqrt v
            let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ₀)
            let N : ℝ := Real.sqrt (n : ℝ)
            let W : (Fin n → Ω) → ℝ := projectionW n g
            let V : (Fin n → Ω) → ℝ := projectionV n g
            let D : (Fin n → Ω) → ℝ := residualStatisticD n r
            let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
            let Ddelete : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
            let Jdelete : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
            let A : (Fin n → Ω) → ℝ := fun ζ => |D ζ|
            let Adelete : (Fin n → Ω) → Fin n → ℝ := fun ζ i => |Ddelete ζ i|
            let B : (Fin n → Ω) → ℝ := studentizerClipBudget n r 512 rho z
            let Bdelete : (Fin n → Ω) → Fin n → ℝ :=
              studentizerClipBudgetDeleted n r 512 rho z
            let d : (Fin n → Ω) → ℝ := centeredDelta n g r
            let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho z
            let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho z
            let s : (Fin n → Ω) → ℝ := fun ζ => Real.sqrt (centeredSq n g r ζ)
            let Tphysical : (Fin n → Ω) → ℝ := fun ζ =>
              if s ζ = 0 then 0 else (W ζ + D ζ) / s ζ
            let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
            let cap : (Fin n → Ω) → Fin n → ℝ := fun ζ i => min |z * ξ0 i ζ| 1
            let S : (Fin n → Ω) → ℝ := fun ζ =>
              ∑ j : Fin n, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)
            let Sdelete : (Fin n → Ω) → Fin n → ℝ := fun ζ i =>
              ∑ j ∈ Finset.univ.erase i, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)
            let fullTest : (Fin n → Ω) → ℝ := fun ζ => z * A ζ + z ^ 2 * B ζ
            let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ζ i =>
              cap ζ i * (|A ζ - Adelete ζ i| + z * |B ζ - Bdelete ζ i|)
            let I : ℝ := ∫ ζ, Real.exp (S ζ) ∂P
            let sourceCost : ℝ :=
              ((∫ ζ, fullTest ζ * Real.exp (S ζ) ∂P) +
                ∑ i : Fin n, ∫ ζ, deletedTest ζ i * Real.exp (Sdelete ζ i) ∂P) / I
            Measurable W ∧ Measurable V ∧ Measurable D ∧ Measurable J ∧
            Measurable A ∧ Measurable B ∧ Measurable d ∧ Measurable e ∧
            Measurable s ∧ Measurable Tclip ∧ Measurable Tphysical ∧
            Measurable fullTest ∧
            MeasurableSet {ζ : Fin n → Ω | V ζ = 0} ∧
            MeasurableSet {ζ : Fin n → Ω | s ζ = 0} ∧
            (∀ ζ : Fin n → Ω,
              (1 / 2 : ℝ) ≤ 1 + e ζ ∧ |e ζ| ≤ B ζ ∧ |e ζ| ≤ |d ζ| ∧
              (0 < V ζ → 0 < V ζ * Real.sqrt (1 + e ζ))) ∧
            (∀ ζ : Fin n → Ω, V ζ = 0 → d ζ = 0 ∧ e ζ = 0 ∧ Tclip ζ = 0) ∧
            (∀ ζ : Fin n → Ω, s ζ = 0 → Tphysical ζ = 0) ∧
            (∀ i : Fin n,
              Measurable (fun ζ : Fin n → Ω => cap ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => Ddelete ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => Jdelete ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => Adelete ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => Bdelete ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => deletedTest ζ i) ∧
              ∃ E : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ,
                Measurable E ∧ ∀ ζ : Fin n → Ω,
                  (Ddelete ζ i, Jdelete ζ i, Bdelete ζ i) =
                    E (fun j : {j : Fin n // j ≠ i} => ζ j.val)) ∧
            ((1 + rho) * z ≤ N →
              (∀ ζ : Fin n → Ω, ζ ∈ projectionGood n g z →
                -(1 / 2 : ℝ) ≤ d ζ →
                e ζ = d ζ ∧ 0 < V ζ * Real.sqrt (1 + e ζ) ∧
                0 < s ζ ∧ V ζ * Real.sqrt (1 + e ζ) = s ζ ∧
                Tclip ζ = Tphysical ζ) ∧
              {ζ : Fin n → Ω | Tclip ζ ≠ Tphysical ζ} ⊆
                (projectionGood n g z)ᶜ ∪ lowerStudentizerBad n g r z) ∧
            0 < I ∧
            Integrable (fun ζ => fullTest ζ * Real.exp (S ζ)) P ∧
            (∀ i : Fin n,
              Integrable (fun ζ => deletedTest ζ i * Real.exp (Sdelete ζ i)) P) ∧
            0 ≤ sourceCost ∧
            sourceCost ≤
              64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
                (1 + z) ^ 3 / Real.sqrt (n : ℝ)
        ) ∧
        (
            let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
            let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
            let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ₀.prod μ₀)
            let rho : ℝ := Real.sqrt v
            let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ₀)
            let N : ℝ := Real.sqrt (n : ℝ)
            let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
            let D : (Fin n → Ω) → ℝ := residualStatisticD n r
            let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
            let Ddelete : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
            let Jdelete : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
            let A : (Fin n → Ω) → ℝ := fun ζ => |D ζ|
            let Adelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ => |Ddelete ζ i|
            let B : (Fin n → Ω) → ℝ := studentizerClipBudget n r 512 rho z
            let Bdelete : Fin n → (Fin n → Ω) → ℝ :=
              fun i ζ => studentizerClipBudgetDeleted n r 512 rho z ζ i
            let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho z
            let V : (Fin n → Ω) → ℝ := fun ζ => Real.sqrt (∑ j : Fin n, (ξ0 j ζ) ^ 2)
            let Vdelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ =>
              Real.sqrt (∑ j ∈ Finset.univ.erase i, (ξ0 j ζ) ^ 2)
            let H : (Fin n → Ω) → ℝ := fun ζ => (1 + V ζ) * (N + z * Real.sqrt (1 + B ζ))
            let Hdelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ =>
              (1 + Vdelete i ζ) * (N + z * Real.sqrt (1 + Bdelete i ζ))
            let M : ℝ → (Fin n → Ω) → ℝ := fun ε ζ => 4 * ε * N * H ζ
            let Mdelete : ℝ → Fin n → (Fin n → Ω) → ℝ := fun ε i ζ =>
              4 * ε * N * Hdelete i ζ
            let κ : Fin n → ℝ := fun i =>
              4 * N * ((∫ ζ, H ζ ∂P) + (∫ ζ, Hdelete i ζ ∂P))
            let Δ : ℝ → Fin n → (Fin n → Ω) → ℝ := fun ε i ζ =>
              (A ζ + M ε ζ) - (Adelete i ζ + Mdelete ε i ζ) - (A ζ - Adelete i ζ)
            MemLp D 2 P ∧
            (∀ i : Fin n, MemLp (fun ζ => Ddelete ζ i) 2 P) ∧
            Integrable J P ∧ (∀ i : Fin n, Integrable (fun ζ => Jdelete ζ i) P) ∧
            Integrable A P ∧ (∀ i : Fin n, Integrable (Adelete i) P) ∧
            Integrable B P ∧ (∀ i : Fin n, Integrable (Bdelete i) P) ∧ Integrable e P ∧
            (∀ ζ : Fin n → Ω, 0 ≤ A ζ ∧ 0 ≤ B ζ ∧ |e ζ| ≤ B ζ) ∧
            (∀ (i : Fin n) (ζ : Fin n → Ω), 0 ≤ Adelete i ζ ∧ 0 ≤ Bdelete i ζ) ∧
            (∀ i : Fin n, Measurable (ξ0 i) ∧ MemLp (ξ0 i) 2 P ∧ (∫ ζ, ξ0 i ζ ∂P) = 0) ∧
            (∑ i : Fin n, ∫ ζ, (ξ0 i ζ) ^ 2 ∂P) = 1 ∧
            (∀ ζ : Fin n → Ω, V ζ = projectionV n g ζ) ∧
            Measurable H ∧ Integrable H P ∧
            (∀ i : Fin n, Measurable (Hdelete i) ∧ Integrable (Hdelete i) P) ∧
            (∀ ζ : Fin n → Ω, 0 < H ζ) ∧
            (∀ (i : Fin n) (ζ : Fin n → Ω), 0 < Hdelete i ζ) ∧
            (∀ ε : ℝ, Measurable (M ε) ∧ Integrable (M ε) P ∧
              Integrable (fun ζ => |M ε ζ|) P) ∧
            (∀ (ε : ℝ) (i : Fin n), Measurable (Mdelete ε i) ∧ Integrable (Mdelete ε i) P ∧
              Integrable (fun ζ => |Mdelete ε i ζ|) P) ∧
            (∀ ε : ℝ, 0 ≤ ε → ∀ ζ : Fin n → Ω,
              0 ≤ M ε ζ ∧ ∀ i : Fin n, 0 ≤ Mdelete ε i ζ) ∧
            (∀ i : Fin n, 0 ≤ κ i) ∧
            (∀ (ε : ℝ) (i : Fin n),
              (∫ ζ, M ε ζ ∂P) + (∫ ζ, Mdelete ε i ζ ∂P) = ε * κ i) ∧
            (∀ (ε : ℝ) (i : Fin n),
              (∫ ζ, |M ε ζ| ∂P) + (∫ ζ, |Mdelete ε i ζ| ∂P) = |ε| * κ i) ∧
            (∀ (ε : ℝ) (i : Fin n) (ζ : Fin n → Ω),
              Δ ε i ζ = M ε ζ - Mdelete ε i ζ) ∧
            (∀ (ε : ℝ) (i : Fin n) (ζ : Fin n → Ω),
              |Δ ε i ζ| ≤ |M ε ζ| + |Mdelete ε i ζ|) ∧
            (∀ (ε : ℝ) (i : Fin n), Measurable (Δ ε i) ∧ Integrable (Δ ε i) P ∧
              Integrable (fun ζ => |Δ ε i ζ|) P ∧
              (∫ ζ, |Δ ε i ζ| ∂P) ≤ |ε| * κ i) ∧
            (∀ i : Fin n, Filter.Tendsto (fun ε : ℝ => ∫ ζ, |Δ ε i ζ| ∂P)
              (nhds (0 : ℝ)) (nhds (0 : ℝ)))
        ))
```

## intro — 第223行

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

## intro — 第224行

```lean
  intro mN mN₀ P P₀ N O gcoord Q D1 D2 Tclip Ddel Jdel Bdelete κ W0 V0 T0
    lambda01 mAugLocal mAug νlocal ν q c ξlocal Ylocal ξ Y a s ηlocal η C W V
    Wη Vη b Dη Tη Z0 Z p0 comparisons F0 A0 Eη
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

## rcases — 第228行

```lean
  rcases hfiniteN with ⟨hP₀prob, hidmeas, hP₀map, hfiniteLaw⟩
```

`hP₀prob`
```lean
@IsProbabilityMeasure (Fin n → Ω) mN₀ P₀
```

`hidmeas`
```lean
Measurable[mN, mN₀] (id : (Fin n → Ω) → Fin n → Ω)
```

`hP₀map`
```lean
P₀ = @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P
```

`hfiniteLaw`
```lean
∀ (B : Type) (mB : MeasurableSpace B) (T : (Fin n → Ω) → B), Measurable[mN₀, mB] T → @Measure.map (Fin n → Ω) B mN₀ mB T P₀ = @Measure.map (Fin n → Ω) B mN mB T P
```

## rcases — 第234行

```lean
  rcases hstatisticsCurrent with
    ⟨hWm, hVm, hD1m, hJm, hAm, hBm, hdm, hD2m, hsm,
      hTclipm, hTactualm, hfullTestm, hZ0m, hZsm, hglobal,
      hzero, hphysicalzero, hdeleted, hcurrentTail⟩
```

`hWm`
```lean
Measurable (projectionW n (g₀))
```

`hVm`
```lean
Measurable (projectionV n (g₀))
```

`hD1m`
```lean
Measurable (residualStatisticD n (r₀))
```

`hJm`
```lean
Measurable (residualEnergyJ n (r₀))
```

`hAm`
```lean
Measurable (fun ζ => |(residualStatisticD n (r₀)) ζ|)
```

`hBm`
```lean
Measurable (studentizerClipBudget n (r₀) 512 (rho₀) y)
```

`hdm`
```lean
Measurable (centeredDelta n (g₀) (r₀))
```

`hD2m`
```lean
Measurable (clippedCenteredDelta n (g₀) (r₀) 512 (rho₀) y)
```

`hsm`
```lean
Measurable (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ))
```

`hTclipm`
```lean
Measurable (clippedCenteredStatistic n (g₀) (r₀) 512 (rho₀) y)
```

`hTactualm`
```lean
Measurable (fun ζ =>
      if (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ = 0 then 0 else ((projectionW n (g₀)) ζ + (residualStatisticD n (r₀)) ζ) / (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ)
```

`hfullTestm`
```lean
Measurable (fun ζ => y * (fun ζ => |(residualStatisticD n (r₀)) ζ|) ζ + y ^ 2 * (studentizerClipBudget n (r₀) 512 (rho₀) y) ζ)
```

`hZ0m`
```lean
MeasurableSet {ζ : Fin n → Ω | (projectionV n (g₀)) ζ = 0}
```

`hZsm`
```lean
MeasurableSet {ζ : Fin n → Ω | (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ = 0}
```

`hglobal`
```lean
(∀ ζ : Fin n → Ω,
      (1 / 2 : ℝ) ≤ 1 + (clippedCenteredDelta n (g₀) (r₀) 512 (rho₀) y) ζ ∧ |(clippedCenteredDelta n (g₀) (r₀) 512 (rho₀) y) ζ| ≤ (studentizerClipBudget n (r₀) 512 (rho₀) y) ζ ∧ |(clippedCenteredDelta n (g₀) (r₀) 512 (rho₀) y) ζ| ≤ |(centeredDelta n (g₀) (r₀)) ζ| ∧
      (0 < (projectionV n (g₀)) ζ → 0 < (projectionV n (g₀)) ζ * Real.sqrt (1 + (clippedCenteredDelta n (g₀) (r₀) 512 (rho₀) y) ζ)))
```

`hzero`
```lean
(∀ ζ : Fin n → Ω, (projectionV n (g₀)) ζ = 0 → (centeredDelta n (g₀) (r₀)) ζ = 0 ∧ (clippedCenteredDelta n (g₀) (r₀) 512 (rho₀) y) ζ = 0 ∧ (clippedCenteredStatistic n (g₀) (r₀) 512 (rho₀) y) ζ = 0)
```

`hphysicalzero`
```lean
(∀ ζ : Fin n → Ω, (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ = 0 → (fun ζ =>
      if (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ = 0 then 0 else ((projectionW n (g₀)) ζ + (residualStatisticD n (r₀)) ζ) / (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ) ζ = 0)
```

`hdeleted`
```lean
(∀ i : Fin n,
      Measurable (fun ζ : Fin n → Ω => (fun ζ i => min |y * (fun i ζ => (g₀) (ζ i) / (N)) i ζ| 1) ζ i) ∧
      Measurable (fun ζ : Fin n → Ω => (residualStatisticDDeleted n (r₀)) ζ i) ∧
      Measurable (fun ζ : Fin n → Ω => (residualEnergyJDeleted n (r₀)) ζ i) ∧
      Measurable (fun ζ : Fin n → Ω => (fun ζ i => |(residualStatisticDDeleted n (r₀)) ζ i|) ζ i) ∧
      Measurable (fun ζ : Fin n → Ω => (studentizerClipBudgetDeleted n (r₀) 512 (rho₀) y) ζ i) ∧
      Measurable (fun ζ : Fin n → Ω => (fun ζ i =>
      (fun ζ i => min |y * (fun i ζ => (g₀) (ζ i) / (N)) i ζ| 1) ζ i * (|(fun ζ => |(residualStatisticD n (r₀)) ζ|) ζ - (fun ζ i => |(residualStatisticDDeleted n (r₀)) ζ i|) ζ i| + y * |(studentizerClipBudget n (r₀) 512 (rho₀) y) ζ - (studentizerClipBudgetDeleted n (r₀) 512 (rho₀) y) ζ i|)) ζ i) ∧
      ∃ E : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ,
        Measurable E ∧ ∀ ζ : Fin n → Ω,
          ((residualStatisticDDeleted n (r₀)) ζ i, (residualEnergyJDeleted n (r₀)) ζ i, (studentizerClipBudgetDeleted n (r₀) 512 (rho₀) y) ζ i) =
            E (fun j : {j : Fin n // j ≠ i} => ζ j.val))
```

`hcurrentTail`
```lean
((1 + (rho₀)) * y ≤ (N) →
      (∀ ζ : Fin n → Ω, ζ ∈ projectionGood n (g₀) y →
        -(1 / 2 : ℝ) ≤ (centeredDelta n (g₀) (r₀)) ζ →
        (clippedCenteredDelta n (g₀) (r₀) 512 (rho₀) y) ζ = (centeredDelta n (g₀) (r₀)) ζ ∧ 0 < (projectionV n (g₀)) ζ * Real.sqrt (1 + (clippedCenteredDelta n (g₀) (r₀) 512 (rho₀) y) ζ) ∧
        0 < (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ ∧ (projectionV n (g₀)) ζ * Real.sqrt (1 + (clippedCenteredDelta n (g₀) (r₀) 512 (rho₀) y) ζ) = (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ ∧
        (clippedCenteredStatistic n (g₀) (r₀) 512 (rho₀) y) ζ = (fun ζ =>
      if (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ = 0 then 0 else ((projectionW n (g₀)) ζ + (residualStatisticD n (r₀)) ζ) / (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ) ζ) ∧
      {ζ : Fin n → Ω | (clippedCenteredStatistic n (g₀) (r₀) 512 (rho₀) y) ζ ≠ (fun ζ =>
      if (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ = 0 then 0 else ((projectionW n (g₀)) ζ + (residualStatisticD n (r₀)) ζ) / (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ) ζ} ⊆
        (projectionGood n (g₀) y)ᶜ ∪ lowerStudentizerBad n (g₀) (r₀) y) ∧
0 < (∫ ζ, Real.exp ((fun ζ =>
      ∑ j : Fin n, (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ - (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ) ^ 2 / 2)) ζ) ∂(P₀)) ∧
Integrable (fun ζ => (fun ζ => y * (fun ζ => |(residualStatisticD n (r₀)) ζ|) ζ + y ^ 2 * (studentizerClipBudget n (r₀) 512 (rho₀) y) ζ) ζ * Real.exp ((fun ζ =>
      ∑ j : Fin n, (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ - (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ) ^ 2 / 2)) ζ)) (P₀) ∧
(∀ i : Fin n,
      Integrable (fun ζ => (fun ζ i =>
      (fun ζ i => min |y * (fun i ζ => (g₀) (ζ i) / (N)) i ζ| 1) ζ i * (|(fun ζ => |(residualStatisticD n (r₀)) ζ|) ζ - (fun ζ i => |(residualStatisticDDeleted n (r₀)) ζ i|) ζ i| + y * |(studentizerClipBudget n (r₀) 512 (rho₀) y) ζ - (studentizerClipBudgetDeleted n (r₀) 512 (rho₀) y) ζ i|)) ζ i * Real.exp ((fun ζ i =>
      ∑ j ∈ Finset.univ.erase i, (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ - (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ) ^ 2 / 2)) ζ i)) (P₀)) ∧
0 ≤ (((∫ ζ, (fun ζ => y * (fun ζ => |(residualStatisticD n (r₀)) ζ|) ζ + y ^ 2 * (studentizerClipBudget n (r₀) 512 (rho₀) y) ζ) ζ * Real.exp ((fun ζ =>
      ∑ j : Fin n, (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ - (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ) ^ 2 / 2)) ζ) ∂(P₀)) +
        ∑ i : Fin n, ∫ ζ, (fun ζ i =>
      (fun ζ i => min |y * (fun i ζ => (g₀) (ζ i) / (N)) i ζ| 1) ζ i * (|(fun ζ => |(residualStatisticD n (r₀)) ζ|) ζ - (fun ζ i => |(residualStatisticDDeleted n (r₀)) ζ i|) ζ i| + y * |(studentizerClipBudget n (r₀) 512 (rho₀) y) ζ - (studentizerClipBudgetDeleted n (r₀) 512 (rho₀) y) ζ i|)) ζ i * Real.exp ((fun ζ i =>
      ∑ j ∈ Finset.univ.erase i, (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ - (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ) ^ 2 / 2)) ζ i) ∂(P₀)) / (∫ ζ, Real.exp ((fun ζ =>
      ∑ j : Fin n, (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ - (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ) ^ 2 / 2)) ζ) ∂(P₀))) ∧
(((∫ ζ, (fun ζ => y * (fun ζ => |(residualStatisticD n (r₀)) ζ|) ζ + y ^ 2 * (studentizerClipBudget n (r₀) 512 (rho₀) y) ζ) ζ * Real.exp ((fun ζ =>
      ∑ j : Fin n, (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ - (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ) ^ 2 / 2)) ζ) ∂(P₀)) +
        ∑ i : Fin n, ∫ ζ, (fun ζ i =>
      (fun ζ i => min |y * (fun i ζ => (g₀) (ζ i) / (N)) i ζ| 1) ζ i * (|(fun ζ => |(residualStatisticD n (r₀)) ζ|) ζ - (fun ζ i => |(residualStatisticDDeleted n (r₀)) ζ i|) ζ i| + y * |(studentizerClipBudget n (r₀) 512 (rho₀) y) ζ - (studentizerClipBudgetDeleted n (r₀) 512 (rho₀) y) ζ i|)) ζ i * Real.exp ((fun ζ i =>
      ∑ j ∈ Finset.univ.erase i, (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ - (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ) ^ 2 / 2)) ζ i) ∂(P₀)) / (∫ ζ, Real.exp ((fun ζ =>
      ∑ j : Fin n, (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ - (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ) ^ 2 / 2)) ζ) ∂(P₀))) ≤
      64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + (rho₀)) *
        (1 + y) ^ 3 / Real.sqrt (n : ℝ)
```

## funext — 第277行

```lean
    funext ξ i
```

`ξ`
```lean
Fin n → Ω
```

`i`
```lean
Fin n
```

## funext — 第288行

```lean
    funext i
```

`i`
```lean
Fin n
```

## funext — 第319行

```lean
    funext ξ
```

`ξ`
```lean
Fin n → Ω
```

## funext — 第323行

```lean
    funext ξ
```

`ξ`
```lean
Fin n → Ω
```

## funext — 第330行

```lean
    funext ξ
```

`ξ`
```lean
Fin n → Ω
```

## rcases — 第348行

```lean
  rcases hcanonical with
    ⟨hνprob, hQpres, hqpres, hs, hηeval, hηindep, hηL2, hηInts,
      hηmean, hηenergy, hηnull, hVηnull, hVηpos, hCmeas, hCcomap,
      hfactor, hretained, hscalar, hT0meas, hTηmeas, hZambientmeas,
      hZmeas, hZlaw, hZreal, hsigned, hcompare⟩
```

`hνprob`
```lean
IsProbabilityMeasure ν
```

`hQpres`
```lean
MeasurePreserving Q P₀ P₀
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

`hVηpos`
```lean
∀ᵐ x ∂ν, 0 < Vη x
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

`hT0meas`
```lean
Measurable T0
```

`hTηmeas`
```lean
∀ z : ℝ, Measurable (Tη z)
```

`hZambientmeas`
```lean
MeasurableSet[mN₀] {ξ : Fin n → Ω | V0 ξ = 0}
```

`hZmeas`
```lean
MeasurableSet Z
```

`hZlaw`
```lean
ν Z = P₀ {ξ : Fin n → Ω | V0 ξ = 0}
```

`hZreal`
```lean
ν.real Z = P₀.real {ξ : Fin n → Ω | V0 ξ = 0}
```

`hsigned`
```lean
(∀ (z : ℝ) (x : Fin n → Ω × ℝ),
          Wη x + Dη z x - z * Vη x * b x = W x + D1 (q x) - z * V x * b x)
```

`hcompare`
```lean
∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
MeasurableSet[mN₀] {ξ : Fin n → Ω | R (T0 ξ) z} ∧
MeasurableSet[mN₀] {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ)) (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))} ∧
MeasurableSet (Eη R z) ∧
ν (Eη R z) = P₀ {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ)) (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))} ∧
(∀ᵐ ξ ∂P₀, ξ ∈ ({ξ : Fin n → Ω | R (T0 ξ) z} ∆ {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ)) (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))}) → V0 ξ = 0) ∧
P₀ ({ξ : Fin n → Ω | R (T0 ξ) z} ∆ {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ)) (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))}) ≤ P₀ {ξ : Fin n → Ω | V0 ξ = 0} ∧
|P₀.real {ξ : Fin n → Ω | R (T0 ξ) z} - ν.real (Eη R z)| ≤ P₀.real {ξ : Fin n → Ω | V0 ξ = 0}
```

## filter_upwards — 第354行

```lean
    filter_upwards [hVηpos] with x hx
```

`x`
```lean
Fin n → Ω × ℝ
```

`hx`
```lean
0 < Vη x
```

## rcases — 第369行

```lean
    rcases hdeleted i with
      ⟨hcapi, hDdi, hJdi, hAdi, hBdi, htesti, E_i, hEmeas, hEpoint⟩
```

`hcapi`
```lean
Measurable (fun ζ : Fin n → Ω => min |y * (g₀ (ζ i) / N)| 1)
```

`hDdi`
```lean
Measurable (fun ζ : Fin n → Ω => residualStatisticDDeleted n r₀ ζ i)
```

`hJdi`
```lean
Measurable (fun ζ : Fin n → Ω => residualEnergyJDeleted n r₀ ζ i)
```

`hAdi`
```lean
Measurable (fun ζ : Fin n → Ω => |residualStatisticDDeleted n r₀ ζ i|)
```

`hBdi`
```lean
Measurable (fun ζ : Fin n → Ω => studentizerClipBudgetDeleted n r₀ 512 rho₀ y ζ i)
```

`htesti`
```lean
Measurable (fun ζ : Fin n → Ω => (fun ζ : Fin n → Ω => min |y * (g₀ (ζ i) / N)| 1) ζ * (|(fun ζ : Fin n → Ω => |residualStatisticD n r₀ ζ|) ζ - (fun ζ : Fin n → Ω => |residualStatisticDDeleted n r₀ ζ i|) ζ| + y * |(studentizerClipBudget n r₀ 512 rho₀ y) ζ - studentizerClipBudgetDeleted n r₀ 512 rho₀ y ζ i|))
```

`E_i`
```lean
({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ
```

`hEmeas`
```lean
Measurable E_i
```

`hEpoint`
```lean
∀ ζ : Fin n → Ω, (residualStatisticDDeleted n r₀ ζ i, residualEnergyJDeleted n r₀ ζ i, studentizerClipBudgetDeleted n r₀ 512 rho₀ y ζ i) = E_i (fun j : {j : Fin n // j ≠ i} => ζ j.val)
```

## intro — 第386行

```lean
      intro j
```

`j`
```lean
{j : Fin n // j ≠ i}
```

## rcases — 第404行

```lean
    rcases hretained i dD hdD with ⟨FD, hFDm, hFDpoint, hFDlift, hFDfull⟩
```

`FD`
```lean
({j : Fin n // j ≠ i} → ℝ) → ℝ
```

`hFDm`
```lean
Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] FD
```

`hFDpoint`
```lean
∀ y : {j : Fin n // j ≠ i} → Ω × ℝ, dD y = FD (fun j => ηlocal j.val (y j))
```

`hFDlift`
```lean
Measurable[borel (Fin n → ℝ), borel ℝ] (fun t : Fin n → ℝ => FD (fun j => t j.val))
```

`hFDfull`
```lean
∀ x : Fin n → Ω × ℝ, dD (fun j => x j.val) = FD (fun j => η j.val x)
```

## rcases — 第405行

```lean
    rcases hretained i dJ hdJ with ⟨FJ, hFJm, hFJpoint, hFJlift, hFJfull⟩
```

`FJ`
```lean
({j : Fin n // j ≠ i} → ℝ) → ℝ
```

`hFJm`
```lean
Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] FJ
```

`hFJpoint`
```lean
∀ y : {j : Fin n // j ≠ i} → Ω × ℝ, dJ y = FJ (fun j => ηlocal j.val (y j))
```

`hFJlift`
```lean
Measurable[borel (Fin n → ℝ), borel ℝ] (fun t : Fin n → ℝ => FJ (fun j => t j.val))
```

`hFJfull`
```lean
∀ x : Fin n → Ω × ℝ, dJ (fun j => x j.val) = FJ (fun j => η j.val x)
```

## rcases — 第406行

```lean
    rcases hretained i dB hdB with ⟨FB, hFBm, hFBpoint, hFBlift, hFBfull⟩
```

`FB`
```lean
({j : Fin n // j ≠ i} → ℝ) → ℝ
```

`hFBm`
```lean
Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] FB
```

`hFBpoint`
```lean
∀ y : {j : Fin n // j ≠ i} → Ω × ℝ, dB y = FB (fun j => ηlocal j.val (y j))
```

`hFBlift`
```lean
Measurable[borel (Fin n → ℝ), borel ℝ] (fun t : Fin n → ℝ => FB (fun j => t j.val))
```

`hFBfull`
```lean
∀ x : Fin n → Ω × ℝ, dB (fun j => x j.val) = FB (fun j => η j.val x)
```

## intro — 第415行

```lean
    intro x
```

`x`
```lean
Fin n → Ω × ℝ
```

## intro — 第471行

```lean
  · intro z R hR
```

`z`
```lean
ℝ
```

`R`
```lean
ℝ → ℝ → Prop
```

`hR`
```lean
R ∈ comparisons
```

## rcases — 第472行

```lean
    rcases hcomparison0 z R hR with ⟨hA0m, hF0m, hEηm, hEηlaw, hAFae, hAF₀, hreal₀⟩
```

`hA0m`
```lean
MeasurableSet[mN₀] (A0 R z)
```

`hF0m`
```lean
MeasurableSet[mN₀] (F0 R z)
```

`hEηm`
```lean
MeasurableSet (Eη R z)
```

`hEηlaw`
```lean
ν (Eη R z) = P₀ (F0 R z)
```

`hAFae`
```lean
(∀ᵐ ξ ∂P₀, ξ ∈ (A0 R z ∆ F0 R z) → ξ ∈ Z0)
```

`hAF₀`
```lean
P₀ (A0 R z ∆ F0 R z) ≤ P₀ Z0
```

`hreal₀`
```lean
|P₀.real (A0 R z) - ν.real (Eη R z)| ≤ P₀.real Z0
```

## intro — 第485行

```lean
      intro ξ hdiff
```

`ξ`
```lean
Fin n → Ω
```

`hdiff`
```lean
ξ ∈ (A0 R z ∆ F0 R z)
```

## by_contra — 第486行

```lean
      by_contra hnot
```

`hnot`
```lean
ξ ∉ Z0
```

## rcases — 第502行

```lean
        rcases hR with rfl | rfl | rfl | rfl | rfl
```

`rfl branch 1`
```lean
R = (fun a b : ℝ => a ≤ b)
```

`rfl branch 2`
```lean
R = (fun a b : ℝ => a < b)
```

`rfl branch 3`
```lean
R = (fun a b : ℝ => b ≤ a)
```

`rfl branch 4`
```lean
R = (fun a b : ℝ => b < a)
```

`rfl branch 5`
```lean
R = (fun a b : ℝ => a = b)
```

## intro — 第508行

```lean
          · intro heq
```

`heq`
```lean
(projectionW n g ξ + D1 ξ) / (projectionV n g ξ * Real.sqrt (1 + D2 ξ)) = z
```

## intro — 第512行

```lean
          · intro heq
```

`heq`
```lean
(projectionW n g ξ + D1 ξ) = z * (projectionV n g ξ * Real.sqrt (1 + D2 ξ))
```

## rcases — 第517行

```lean
      rcases Set.mem_symmDiff.mp hdiff with ⟨ha, hf⟩ | ⟨hf, ha⟩
```

`ha@left`
```lean
ξ ∈ A0 R z
```

`hf@left`
```lean
ξ ∉ F0 R z
```

`hf@right`
```lean
ξ ∈ F0 R z
```

`ha@right`
```lean
ξ ∉ A0 R z
```
