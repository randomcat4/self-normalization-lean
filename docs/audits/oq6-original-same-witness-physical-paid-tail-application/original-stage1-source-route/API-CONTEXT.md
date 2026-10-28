# Unit248 Stage1 exact source API context

PROSPECTIVE ONLY. No Lean elaboration, proof, kernel or axiom check was performed. The input is pinned Lean4.36.0-rc1 / mathlib807d3836b165983210ee2ecf3cd28f239436949c. Existing successful source-qualified evidence is reused; unchanged proofs were not reopened or replayed.

## Whole247 producer

Exact public head below is the sealed6f64 source interface, still awaiting247 qualification. It supplies the sole cg/m₀/trim and literal augmented ν/a/s/η. Its entire71 universal and39 payment clauses are retained.

```lean
theorem actual_original_same_witness_clipped_paid_scalar_tail_application :
  ∀
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
    (cBudget : ℝ) (hcBudget : 0 < cBudget),
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
        let deletedTestUnperturbedη : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x =>
          min |z * η k i x| 1 * (|Anew k x - Adelete i x| + z * |B x - Bdelete i x|)
        let unperturbedSourceCostη : ℕ → ℝ := fun k =>
          ((∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) +
            ∑ i : Fin n, ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k
        (∀ i : Fin n, Measurable[mAugLocal, borel ℝ] (ξlocal i)) ∧
        (∀ (k : ℕ) (i : Fin n),
          Measurable[mAugLocal, borel ℝ] (ηlocal k i) ∧
          MeasurableSpace.comap (ηlocal k i) (borel ℝ) = mAugLocal) ∧
        (∀ k : ℕ,
          Measurable[mAug, borel (Fin n → ℝ)] (C k) ∧
          MeasurableSpace.comap (C k) (borel (Fin n → ℝ)) = mAug ∧
          ∀ (f : (Fin n → Ω × ℝ) → ℝ), Measurable[mAug, borel ℝ] f →
            ∃ F : (Fin n → ℝ) → ℝ,
              Measurable[borel (Fin n → ℝ), borel ℝ] F ∧
              ∀ x : Fin n → Ω × ℝ, f x = F (C k x)) ∧
        (∀ (k : ℕ) (i : Fin n),
          let J : Type := {j : Fin n // j ≠ i}
          let mDel : MeasurableSpace (J → Ω × ℝ) :=
            @MeasurableSpace.pi J (fun _ : J => Ω × ℝ) (fun _ : J => mAugLocal)
          let Cdel : (J → Ω × ℝ) → (J → ℝ) :=
            fun y j => ηlocal k j.val (y j)
          let pX : (Fin n → Ω × ℝ) → (J → Ω × ℝ) := fun x j => x j.val
          let pR : (Fin n → ℝ) → (J → ℝ) := fun t j => t j.val
          Measurable[mAug, mDel] pX ∧
          Measurable[borel (Fin n → ℝ), borel (J → ℝ)] pR ∧
          Measurable[mDel, borel (J → ℝ)] Cdel ∧
          MeasurableSpace.comap Cdel (borel (J → ℝ)) = mDel ∧
          (∀ x : Fin n → Ω × ℝ, pR (C k x) = Cdel (pX x)) ∧
          MeasurableSpace.comap (fun x : Fin n → Ω × ℝ => pR (C k x))
              (borel (J → ℝ)) = MeasurableSpace.comap pX mDel ∧
          ∀ (d : (J → Ω × ℝ) → ℝ), Measurable[mDel, borel ℝ] d →
            ∃ F : (J → ℝ) → ℝ,
              Measurable[borel (J → ℝ), borel ℝ] F ∧
              (∀ y : J → Ω × ℝ, d y = F (Cdel y)) ∧
              Measurable[borel (Fin n → ℝ), borel ℝ] (fun t => F (pR t)) ∧
              ∀ x : Fin n → Ω × ℝ, d (pX x) = F (pR (C k x))) ∧
        (∀ (k : ℕ) (i : Fin n),
          ∃ FAdelete FBdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] FAdelete ∧
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] FBdelete ∧
            ∀ x : Fin n → Ω × ℝ,
              Adelete i x = FAdelete (fun j : {j : Fin n // j ≠ i} => η k j.val x) ∧
              Bdelete i x = FBdelete (fun j : {j : Fin n // j ≠ i} => η k j.val x)) ∧
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
        (∀ (k : ℕ) (x : Fin n → Ω × ℝ),
          A x + (4 * ε k * Real.sqrt (n : ℝ)) * H x = Anew k x) ∧
        (∀ (k : ℕ) (i : Fin n),
          Measurable[mAug, borel ℝ] (fun x =>
            deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
              deletedTestη k i x * Real.exp (Sηminus k i x)) ∧
          Integrable[mAug] (fun x =>
            deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
              deletedTestη k i x * Real.exp (Sηminus k i x)) ν ∧
          Integrable[mAug] (fun x =>
            |deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
              deletedTestη k i x * Real.exp (Sηminus k i x)|) ν ∧
          Integrable[mAug] (fun x =>
            deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x)) ν ∧
          (∫ x, |deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
            deletedTestη k i x * Real.exp (Sηminus k i x)| ∂ν) ≤
              |ε k| * (Real.exp ((n : ℝ) / 2) * (K * (∫ x, Hdelete i x ∂ν))) ∧
          |(∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
            (∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν)| ≤
              |ε k| * (Real.exp ((n : ℝ) / 2) * (K * (∫ x, Hdelete i x ∂ν)))) ∧
        (∀ i : Fin n,
          Filter.Tendsto (fun k : ℕ =>
            ∫ x, |deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
              deletedTestη k i x * Real.exp (Sηminus k i x)| ∂ν)
            Filter.atTop (nhds (0 : ℝ)) ∧
          Filter.Tendsto (fun k : ℕ =>
            (∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
              (∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν))
            Filter.atTop (nhds (0 : ℝ)) ∧
          Filter.Tendsto (fun k : ℕ =>
            ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν)
            Filter.atTop (nhds (∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P)) ∧
          Filter.Tendsto (fun k : ℕ =>
            (∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k)
            Filter.atTop (nhds ((∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P) / I0))) ∧
        (∀ k : ℕ,
          |(∑ i : Fin n, ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
            (∑ i : Fin n, ∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν)| ≤
              |ε k| * ∑ i : Fin n,
                Real.exp ((n : ℝ) / 2) * (K * (∫ x, Hdelete i x ∂ν))) ∧
        Filter.Tendsto (fun k : ℕ =>
          (∑ i : Fin n, ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
            (∑ i : Fin n, ∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν))
          Filter.atTop (nhds (0 : ℝ)) ∧
        Filter.Tendsto (fun k : ℕ => unperturbedSourceCostη k - sourceCostη k)
          Filter.atTop (nhds (0 : ℝ)) ∧
        Filter.Tendsto unperturbedSourceCostη Filter.atTop (nhds sourceCost0) ∧
        (∀ (cSZ C1 C2 C3 C4 : ℝ)
            (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
              cSZ C1 C2 C3 C4)
            (k : ℕ) (hz1 : 1 ≤ z)
            (hδη : ∀ i : Fin n, δη k i ≤ 1)
            (hLη : Lη k ≤ cSZ * z ^ 2),
          Shao.standardNormalTail z * Real.exp (-C1 * Lη k) *
              (1 - C2 * unperturbedSourceCostη k) ≤
            ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ∧
          ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ≤
            Shao.standardNormalTail z * Real.exp (C3 * Lη k) *
                (1 + C4 * unperturbedSourceCostη k) +
              ν.real {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4} +
              ν.real {x : Fin n → Ω × ℝ |
                z ^ 2 * |D2 (q x)| > (1 / 4 : ℝ)}) ∧
        (∀ (C1 C2 C3 C4 : ℝ)
            (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
              cBudget C1 C2 C3 C4)
            (hz1 : 1 ≤ z)
            (hzWindow : β = 0 ∨
              (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                Real.rpow (n : ℝ) ((p - 2) / (2 * p))))
            (τ : ℝ) (hτ : 0 < τ),
          ∃ k0 : ℕ, ∀ (k : ℕ), k0 ≤ k →
            (∀ i : Fin n, δη k i ≤ 1) ∧
            Lη k ≤ cBudget * z ^ 2 ∧
            |unperturbedSourceCostη k - sourceCost0| < τ ∧
            Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                (1 - C2 * sourceCost0) - τ ≤
              ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ∧
            ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ≤
              Shao.standardNormalTail z * Real.exp (C3 * L0) *
                  (1 + C4 * sourceCost0) +
                ν.real {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4} +
                ν.real {x : Fin n → Ω × ℝ |
                  z ^ 2 * |D2 (q x)| > (1 / 4 : ℝ)} + τ) ∧
        @MeasurableSet (Fin n → Ω) mN₀
          {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
        @MeasurableSet (Fin n → Ω) mN
          {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
        @MeasurableSet (Fin n → Ω × ℝ) mAug
          {x : Fin n → Ω × ℝ | z ≤ T0 (q x)} ∧
        @MeasurableSet (Fin n → Ω) mN₀
          {ζ : Fin n → Ω | projectionV n g ζ = 0} ∧
        @MeasurableSet (Fin n → Ω) mN
          {ζ : Fin n → Ω | projectionV n g ζ = 0} ∧
        @MeasurableSet (Fin n → Ω × ℝ) mAug
          {x : Fin n → Ω × ℝ | V x = 0} ∧
        ν.real {x : Fin n → Ω × ℝ | z ≤ T0 (q x)} =
          P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
        ν.real {x : Fin n → Ω × ℝ | V x = 0} =
          P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} ∧
        (∀ k : ℕ,
          @MeasurableSet (Fin n → Ω × ℝ) mAug
            {x : Fin n → Ω × ℝ | z ≤ Tη k x} ∧
          ν ({x : Fin n → Ω × ℝ | z ≤ Tη k x} ∆
            {x : Fin n → Ω × ℝ | z ≤ T0 (q x)}) ≤
              ν {x : Fin n → Ω × ℝ | V x = 0} ∧
          |ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} -
            P.real {ζ : Fin n → Ω | z ≤ T0 ζ}| ≤
              P.real {ζ : Fin n → Ω | projectionV n g ζ = 0}) ∧
        (∀ (C1 C2 C3 C4 : ℝ)
            (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
              cBudget C1 C2 C3 C4)
            (hz1 : 1 ≤ z)
            (hzWindow : β = 0 ∨
              (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
          Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                (1 - C2 * sourceCost0) -
            P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} ≤
            P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
          ∀ (τ : ℝ) (hτ : 0 < τ),
            ∃ k0 : ℕ, ∀ (k : ℕ), k0 ≤ k →
              (∀ i : Fin n, δη k i ≤ 1) ∧
              Lη k ≤ cBudget * z ^ 2 ∧
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
              |compactCostη k - compactCost0| < τ ∧
              |unperturbedSourceCostη k - sourceCost0| < τ ∧
              Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                              (1 - C2 * sourceCost0) - τ -
                            P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} ≤
                            P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
              P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ≤
                            Shao.standardNormalTail z * Real.exp (C3 * L0) *
                                (1 + C4 * sourceCost0) +
                              ν.real {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4} +
                              ν.real {x : Fin n → Ω × ℝ |
                                z ^ 2 * |D2 (q x)| > (1 / 4 : ℝ)} +
                              P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} + τ) ∧
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
        let T0 : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho 1
        let L0 : ℝ := ∑ i : Fin n,
          ∫ ζ, (z * ξ0 i ζ) ^ 2 * min |z * ξ0 i ζ| 1 ∂P
        let sourceCost0 : ℝ :=
          ((∫ ζ,
              (z * |D1 ζ| + z ^ 2 * studentizerClipBudget n r 512 rho 1 ζ) *
                Real.exp (∑ j : Fin n, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) +
            ∑ i : Fin n, ∫ ζ,
              (min |z * ξ0 i ζ| 1 *
                (|(|D1 ζ|) - (|residualStatisticDDeleted n r ζ i|)| +
                  z * |studentizerClipBudget n r 512 rho 1 ζ -
                    studentizerClipBudgetDeleted n r 512 rho 1 ζ i|)) *
                Real.exp (∑ j ∈ Finset.univ.erase i,
                  (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) /
            (∫ ζ, Real.exp (∑ j : Fin n,
              (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P)
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
        (∀ (C1 C2 C3 C4 : ℝ)
            (hSZcBudget : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
              cBudget C1 C2 C3 C4)
            (hzMomentWindow : β = 0 ∨
              (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
          Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                (1 - C2 * sourceCost0) - payment ≤
            P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
          P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ≤
            Shao.standardNormalTail z * Real.exp (C3 * L0) *
                (1 + C4 * sourceCost0) + 3 * payment) ∧
        Filter.limsup (fun k : ℕ => ν.real (E k))
          Filter.atTop ≤ payment)
```

## bounded_remainder_small_window

Source binding: {"path":"C:/game/shao lean/library/Shao/OQ5/P51/BoundedRemainderPayments.lean","sha256":"c0102fa13835fb22b01148e42d66cf8ff5704d682b9a6142eb508d7172d95cc9","bytes":28173}

```lean
/- Source-bound unit197 implementation of the eleven parent-frozen declarations.
   Qualification remains pending the designated server and independent review. -/

import Shao.OQ5.P51.BoundedPolylogConcentration
import Shao.OQ5.P51.BoundedStudentizerGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Real
set_option autoImplicit false
universe u
open Filter MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ6.BoundedProductEnvelopeTails (tailScale)
open Shao.OQ6.CanonicalDoubleGhostRowMoments (sampleLaw originalRows)
open Shao.OQ6.CanonicalDoubleGhostScalarMoments (originalUpper)
namespace Shao.OQ5.P51
noncomputable section

theorem bounded_remainder_small_window
    (n : ℕ) {Ω : Type u} (g : Ω → ℝ) (r : Ω → Ω → ℝ)
    (x : Fin n → Ω) (K t0 y : ℝ)
    (hsym : ∀ a b : Ω, r a b = r b a) (hn : 4 ≤ n)
    (hK : 0 ≤ K) (ht0 : 0 < t0) (hy : (1 : ℝ) ≤ y)
    (hyWindow : y ≤ remainderWindowScale K t0 * Real.rpow (n : ℝ) (1 / 6 : ℝ))
    (hF : |originalUpper n r x| ≤ K * (n : ℝ) * boundedPolylogMomentOrder t0 n)
    (hRows : ‖originalRows n r x‖ ^ (2 : ℕ) ≤
      K * (n : ℝ) ^ (2 : ℕ) * boundedPolylogMomentOrder t0 n)
    (hGood : x ∈ projectionGood n g y) :
    0 < projectionV n g x ∧
      y * |residualStatisticD n r x| / projectionV n g x ≤ (1 / 8 : ℝ) ∧
      y ^ (2 : ℕ) * |centeredDelta n g r x| ≤ (1 / 32 : ℝ) ∧
      |centeredDelta n g r x| ≤ (1 / 32 : ℝ)
```

## literal_clippedCentered_comparison_on_projectionGood

Source binding: {"path":"C:/game/shao lean/library/Shao/OQ5/P51/LiteralClippedComparison.lean","sha256":"8d601a1496ca1a330fb7f96a2ff5cdab6f0d3b37c125a710735d9123c5be1f14","bytes":2614}

```lean
import Shao.OQ5.P51.ClippedStudentizer
import Shao.OQ5.P51.LiteralStudentizerBudgetDomination
set_option autoImplicit false
universe u
namespace Shao.OQ5.P51

theorem literal_clippedCentered_comparison_on_projectionGood (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (rho y : ℝ)
    (x : Fin n → Ω) (hn : 4 ≤ n) (hy : (1 : ℝ) ≤ y)
    (hsym : ∀ a b : Ω, r a b = r b a) (hrho : 0 ≤ rho)
    (hwindow : (1 + rho) * y ≤ Real.sqrt (n : ℝ))
    (hGood : x ∈ projectionGood n g y)
    (hLower : -(1 / 2 : ℝ) ≤ centeredDelta n g r x) :
    clippedCenteredDelta n g r 512 rho y x = centeredDelta n g r x ∧
    0 < projectionV n g x *
      Real.sqrt (1 + clippedCenteredDelta n g r 512 rho y x) ∧
    0 < Real.sqrt (centeredSq n g r x) ∧
    projectionV n g x * Real.sqrt (1 + clippedCenteredDelta n g r 512 rho y x) =
      Real.sqrt (centeredSq n g r x) ∧
    clippedCenteredStatistic n g r 512 rho y x =
      (if Real.sqrt (centeredSq n g r x) = 0 then 0 else
        (projectionW n g x + residualStatisticD n r x) /
          Real.sqrt (centeredSq n g r x))
```

## actual_normalized_compact_clipped_observables

Source binding: {"path":"C:/game/shao lean/drafts/oq56/unit220/author-01/repair-02/OriginalClippedStatisticMeasurable.lean","sha256":"052fb7eb6bb1d17218bf47c6c4f5b6715561da68b022bdacf6835fee5d667103","bytes":15983}

```lean
import Shao.OQ6.ActualQuadraticTiltMoments
import Shao.OQ5.P51.ClippedDeletionEnvelope

set_option autoImplicit false

universe u

open MeasureTheory
open scoped BigOperators MeasureTheory ENNReal
open Shao.OQ5.P51

namespace Shao.OQ6.OriginalClippedStatisticMeasurable

noncomputable section

theorem actual_normalized_compact_clipped_observables
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 4 ≤ n)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (C0 : ℝ) (hC0 : 0 ≤ C0) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
    let rho : ℝ := Real.sqrt v
    let N : ℝ := Real.sqrt (n : ℝ)
    let W : (Fin n → Ω) → ℝ := projectionW n g
    let V : (Fin n → Ω) → ℝ := projectionV n g
    let D : (Fin n → Ω) → ℝ := residualStatisticD n r
    let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
    let Ddel : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
    let Jdel : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
    let A : (Fin n → Ω) → ℝ := fun ξ => |D ξ|
    let Adel : (Fin n → Ω) → Fin n → ℝ := fun ξ i => |Ddel ξ i|
    let B1 : (Fin n → Ω) → ℝ := studentizerClipBudget n r C0 rho 1
    let B1del : (Fin n → Ω) → Fin n → ℝ := studentizerClipBudgetDeleted n r C0 rho 1
    let s2 : (Fin n → Ω) → ℝ := centeredSq n g r
    let s : (Fin n → Ω) → ℝ := fun ξ => Real.sqrt (s2 ξ)
    let d : (Fin n → Ω) → ℝ := centeredDelta n g r
    let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r C0 rho 1
    let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r C0 rho 1
    let Tactual : (Fin n → Ω) → ℝ := fun ξ => if s ξ = 0 then 0 else (W ξ + D ξ) / s ξ
    let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i => min (|g (ξ i)| / N) (1 / (1 + z))
    let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ξ i => cap ξ i * (|A ξ - Adel ξ i| + z * |B1 ξ - B1del ξ i|)
    Measurable W ∧ Measurable V ∧ Measurable D ∧ Measurable J ∧
      Measurable A ∧ Measurable B1 ∧
      Measurable s2 ∧ Measurable s ∧ Measurable d ∧ Measurable e ∧
      Measurable Tclip ∧ Measurable Tactual ∧
      MeasurableSet {ξ : Fin n → Ω | V ξ = 0} ∧
      MeasurableSet {ξ : Fin n → Ω | s ξ = 0} ∧
      (∀ ξ : Fin n → Ω, (1 / 2 : ℝ) ≤ 1 + e ξ) ∧
      (∀ ξ : Fin n → Ω, V ξ = 0 →
        d ξ = 0 ∧ e ξ = 0 ∧ Tclip ξ = 0) ∧
      (∀ i : Fin n,
        Measurable (fun ξ : Fin n → Ω => cap ξ i) ∧
        Measurable (fun ξ : Fin n → Ω => Ddel ξ i) ∧
        Measurable (fun ξ : Fin n → Ω => Jdel ξ i) ∧
        Measurable (fun ξ : Fin n → Ω => Adel ξ i) ∧
        Measurable (fun ξ : Fin n → Ω => B1del ξ i) ∧
        Measurable (fun ξ : Fin n → Ω => deletedTest ξ i) ∧
        ∃ E : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ,
          Measurable E ∧
          ∀ ξ : Fin n → Ω,
            (Ddel ξ i, Jdel ξ i, B1del ξ i) =
              E (fun j : {j : Fin n // j ≠ i} => ξ j.val))
```

## Actual definitions and ambient namespaces

Binding {"path":"C:/game/shao lean/library/Shao/OQ5/P51/BoundedStudentizerGeometry.lean","sha256":"bc64d3e11a64f62ad654305ce579c1779546d4df37b5593090105af910502edc","bytes":33066}, lines1-107.

```lean
/- Exact frozen unit196 finite studentizer geometry.
Author implementation candidate; not machine checked. -/

import Shao.OQ6.FiniteRows

import Shao.OQ6.CanonicalDoubleGhostRowMoments

import Shao.OQ6.CanonicalDoubleGhostScalarMoments

import Mathlib.Analysis.Real.Sqrt

import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

universe u

open scoped BigOperators

open Shao.OQ6.CanonicalDoubleGhostRowMoments (originalRows)

open Shao.OQ6.CanonicalDoubleGhostScalarMoments (originalUpper)

namespace Shao.OQ5.P51

noncomputable section

-- D01

def sampledKernel
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω) : Fin n → Fin n → ℝ :=
  fun (i j : Fin n) => g (x i) + g (x j) + r (x i) (x j)

-- D02

def projectionEnergy
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  (∑ i : Fin n, (g (x i)) ^ (2 : ℕ)) / (n : ℝ)

-- D03

def projectionV
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  Real.sqrt (projectionEnergy n g x)

-- D04

def projectionW
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  (∑ i : Fin n, g (x i)) / Real.sqrt (n : ℝ)

-- D05

def residualStatisticD
    (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  originalUpper n r x / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))

-- D06

def residualU
    (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (x : Fin n → Ω) : Fin n → ℝ :=
  fun i : Fin n => originalRows n r x i / ((n : ℝ) - 2)

-- D07

def residualEnergyJ
    (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  ∑ i : Fin n, (residualU n r x i) ^ (2 : ℕ)

-- D08

def centeredSq
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  Shao.OQ6.FiniteRows.jackknifeSq (sampledKernel n g r x) / 4

-- D09

def centeredDelta
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  @ite ℝ (projectionV n g x = 0)
    (Classical.propDecidable (projectionV n g x = 0))
    (0 : ℝ) (centeredSq n g r x / (projectionV n g x) ^ (2 : ℕ) - 1)

-- D10

def projectionGood
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (y : ℝ) : Set (Fin n → Ω) :=
  {x : Fin n → Ω | (1 / 2 : ℝ) ≤ projectionEnergy n g x ∧
    |projectionW n g x| ≤ Real.sqrt y * Real.sqrt (Real.sqrt (n : ℝ)) * (4 + projectionV n g x)}

-- D11

def studentizerGeometryScale (K : ℝ) : ℝ :=
  (200 : ℝ) * (1 + K + Real.sqrt K)

-- D12

```

Binding {"path":"C:/game/shao lean/library/Shao/OQ5/P51/ClippedStudentizer.lean","sha256":"a8bffbabb649cdc788b58517a89185691f72de92776a882f3b9ffdcddc0b748b","bytes":11786}, lines1-33.

```lean
import Shao.OQ5.P51.BoundedRemainderPayments

set_option autoImplicit false

universe u

noncomputable section
open scoped Classical

namespace Shao.OQ5.P51

def studentizerClip (B d : ℝ) : ℝ :=
  max (-(min B (1 / 2 : ℝ))) (min d B)

def studentizerClipBudget (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (C0 rho y : ℝ) (x : Fin n → Ω) : ℝ :=
  C0 * (((1 + rho) * y) / Real.sqrt (n : ℝ) +
    residualEnergyJ n r x / ((1 + rho) * y * Real.sqrt (n : ℝ)))

def clippedCenteredDelta (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (C0 rho y : ℝ)
    (x : Fin n → Ω) : ℝ :=
  if projectionV n g x = 0 then 0 else
    studentizerClip (studentizerClipBudget n r C0 rho y x)
      (centeredDelta n g r x)

def clippedCenteredStatistic (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (C0 rho y : ℝ)
    (x : Fin n → Ω) : ℝ :=
  if projectionV n g x = 0 then 0 else
    (projectionW n g x + residualStatisticD n r x) /
      (projectionV n g x *
        Real.sqrt (1 + clippedCenteredDelta n g r C0 rho y x))
```

Binding {"path":"C:/game/shao lean/library/Shao/OQ5/P51/BoundedPolylogWindow.lean","sha256":"1d2ad2ca13be7c987c8e0520c5687dba60669af0db6e0dd01edcbc3105043b7e","bytes":9803}, lines1-34.

```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
# Deterministic polylogarithmic admissibility window for original p51 S16

This file implements the seven declarations frozen in unit194 parent-freeze-v1.
It supplies only the deterministic growth prerequisite at p51 lines197-204.
The full natural sequences include zero; sign-sensitive identities are used
on the eventual set `1 < n`. No statistical or desired-window premise is added.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace Shao.OQ5.P51

noncomputable section

def boundedPolylogHeight (C a : ℝ) (n : ℕ) : ℝ :=
  C * Real.rpow (Real.log (n : ℝ)) a

def boundedPolylogMomentOrder (t0 : ℝ) (n : ℕ) : ℝ :=
  t0 * Real.rpow (n : ℝ) (1 / 3 : ℝ)

```

Binding {"path":"C:/game/shao lean/library/Shao/OQ6/BoundedProductEnvelopeTails.lean","sha256":"43367b3ce14f174a8c8e3db4152e3db3b553ab0dbc9c4521565a1db8ddac1b14","bytes":40651}, lines1-67.

```lean
/- Unit193 original bounded-product statistics. Author source; server validation pending. -/

import Shao.OQ6.BoundedMeanSumMoments
import Shao.OQ6.CanonicalDoubleGhostRowMoments
import Shao.OQ6.CanonicalDoubleGhostScalarMoments
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false
universe u
namespace Shao.OQ6.BoundedProductEnvelopeTails
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ6.StretchedExponentialSumMoments (coordinateSum)
open Shao.OQ6.DoubleGhostSignInvariance (pairedLaw)
open Shao.OQ6.CanonicalDoubleGhostRowMoments (pairedEnergy sampleLaw originalRows)
open Shao.OQ6.CanonicalDoubleGhostScalarMoments (originalUpper)

private def pairSquare
    {Ω : Type u}
    (v : Ω → ℝ)
    (p : Ω × Ω) :
  ℝ :=
  (v p.1 + v p.2) ^ 2

def squareSum
    (n : ℕ)
    {Ω : Type u}
    (w : Ω → ℝ)
    (x : Fin n → Ω) :
  ℝ :=
  ∑ i : Fin n, (w (x i)) ^ 2

def commonMomentScale
    (M : ℝ) :
  ℝ :=
  64 * (M + 1)

def envelopeTailScale
    (M : ℝ) :
  ℝ :=
  4 * M + 8

def squareTailScale
    (M : ℝ) :
  ℝ :=
  Real.exp 1 * (M + 1)

def scalarTailScale
    (M : ℝ) :
  ℝ :=
  8 * Real.exp 1 * envelopeTailScale M

def rowTailScale
    (M : ℝ) :
  ℝ :=
  8 * (Real.exp 1) ^ 2 * (envelopeTailScale M) ^ 2

def tailScale
    (M : ℝ) :
  ℝ :=
  max (squareTailScale M) (max (scalarTailScale M) (rowTailScale M))

private theorem aestronglyMeasurable_of_square_integrable
```

Binding {"path":"C:/game/shao lean/library/Shao/OQ6/CanonicalDoubleGhostRowMoments.lean","sha256":"0b7f38c8840ffefb15fc9185c8f54c2c6907da96cc49bd5e7ee3c5ed512250fc","bytes":38651}, lines1-24.

```lean
import Shao.OQ6.DoubleGhostSignInvariance
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

set_option autoImplicit false

namespace Shao.OQ6.CanonicalDoubleGhostRowMoments

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ6.FiniteHilbertSignMoments
open Shao.OQ6.FiniteMatrixSignEnergy
open Shao.OQ6.DoubleGhostSignInvariance

def sampleLaw (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (ν : Measure Ω) : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => ν)

def pairSamples (n : ℕ) {Ω : Type*} (p : (Fin n → Ω) × (Fin n → Ω)) : Fin n → Ω × Ω := fun i : Fin n => (p.1 i, p.2 i)

def originalRows (n : ℕ) {Ω : Type*} (r : Ω → Ω → ℝ) (x : Fin n → Ω) : EuclideanSpace ℝ (Fin n) := WithLp.toLp (2 : ℝ≥0∞) (V := Fin n → ℝ) (fun i : Fin n => ∑ j : Fin n, if i = j then 0 else r (x i) (x j))

```

Binding {"path":"C:/game/shao lean/library/Shao/OQ6/CanonicalDoubleGhostScalarMoments.lean","sha256":"17790c480efcab2d11cb5d00ccd215a6853e289fb078b5b041ae3bba972ab68c","bytes":32159}, lines1-35.

```lean
import Shao.OQ6.CanonicalDoubleGhostRowMoments
import Shao.OQ6.FiniteQuadraticSignChaos
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

set_option autoImplicit false

namespace Shao.OQ6.CanonicalDoubleGhostScalarMoments

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ6.FiniteHilbertSignMoments
open Shao.OQ6.FiniteMatrixSignEnergy
open Shao.OQ6.DoubleGhostSignInvariance
open Shao.OQ6.FiniteQuadraticSignChaos
open Shao.OQ6.CanonicalDoubleGhostRowMoments

def halfSumCLM (n : ℕ) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ∑ i : Fin n,
    (PiLp.proj (𝕜 := ℝ) (2 : ℝ≥0∞) (fun _ : Fin n => ℝ) i)

def originalHalf (n : ℕ) {Ω : Type*} (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else r (x i) (x j)) / 2

def ghostHalf (n : ℕ) {Ω : Type*} (r : Ω → Ω → ℝ) (z : Fin n → Ω × Ω) : ℝ :=
  quadratic n (ghostMatrix n r z) (fun _ : Fin n => (1 : ℝ)) / 2

def originalUpper (n : ℕ) {Ω : Type*} (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then r (x i) (x j) else 0

theorem halfSumCLM_apply (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
  halfSumCLM n v = (∑ i : Fin n, v i) / 2 := by
```

Binding {"path":"C:/game/shao lean/library/Shao/OQ6/FiniteRows.lean","sha256":"bb4dc865f5ab96ce57814f0721fbd31a2885d6fce7a9facd150941c4c2f91930","bytes":3837}, lines1-34.

```lean
import Shao.OQ5.P35.RowIdentity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Arbitrary symmetric finite rows

Finite deterministic algebra from original p39, lines 59–72. The U-statistic
counts each unordered off-diagonal pair once. The centered jackknife and the
uncentered row square retain their original coefficients. Square roots,
event conversion and probability are separate later units.
-/

set_option autoImplicit false

namespace Shao.OQ6.FiniteRows

noncomputable section

open scoped BigOperators

variable {n : ℕ}

/-- Average every unordered off-diagonal pair exactly once. -/
def uStatistic (H : Fin n → Fin n → ℝ) : ℝ :=
  (n.choose 2 : ℝ)⁻¹ * Shao.OQ5.P35.unorderedPairSum H

/-- Mean of row i excluding the diagonal entry. -/
def rowMean (H : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  ((n : ℝ) - 1)⁻¹ * ∑ j ∈ Finset.univ.erase i, H i j

/-- The original centered-row jackknife square. -/
def jackknifeSq (H : Fin n → Fin n → ℝ) : ℝ :=
  (4 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2) *
    ∑ i : Fin n, (rowMean H i - uStatistic H) ^ 2
```

## Pinned primary measurable and real finite measure context

These are exact embedded primary source ranges and chronological ambient contexts from the bound PRIMARY-API-CONTEXT input. MeasureReal finite side conditions are explicit. Threshold measurability may use the literal Measurable preimage definition with Ici/Iic, without needing a new comparison callback.

```json
[
  {
    "module": "Mathlib.MeasureTheory.Measure.Real",
    "path": "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Real.lean",
    "sha256": "1b9d1490fa5acbffc570eac67f465d3d6ab0520aa3e54464f7520d60d6619b8d",
    "literalContextMarkers": [
      {
        "line": 33,
        "text": "open MeasureTheory Measure Set"
      },
      {
        "line": 34,
        "text": "open scoped ENNReal NNReal Function symmDiff"
      },
      {
        "line": 36,
        "text": "namespace MeasureTheory"
      },
      {
        "line": 38,
        "text": "variable {α β ι : Type*} {_ : MeasurableSpace α} {μ : Measure α} {s s₁ s₂ s₃ t t₁ t₂ u : Set α}"
      }
    ],
    "windows": [
      {
        "first": 1,
        "last": 55,
        "source": "/-\nCopyright (c) 2025 Sébastien Gouëzel. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Sébastien Gouëzel\n-/\nmodule\n\npublic import Mathlib.MeasureTheory.Measure.Typeclasses.Probability\npublic import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite\n\n/-!\n# Measures as real-valued functions\n\nGiven a measure `μ`, we have defined `μ.real` as the function sending a set `s` to `(μ s).toReal`.\nIn this file, we develop a basic API around this notion.\n\nWe essentially copy relevant lemmas from the files `MeasureSpaceDef.lean`, `NullMeasurable.lean` and\n`MeasureSpace.lean`, and adapt them by replacing in their name `measure` with `measureReal`.\n\nMany lemmas require an assumption that some set has finite measure. These assumptions are written\nin the form `(h : μ s ≠ ∞ := by finiteness)`, where `finiteness` is a tactic for goals of\nthe form `≠ ∞`.\n\nThere are certainly many missing lemmas. The missing ones should be added as they are needed.\n\nThere are no lemmas on infinite sums, as summability issues are really\nmore painful with reals than nonnegative extended reals. They should probably be added in the long\nrun.\n-/\n\npublic section\n\nopen MeasureTheory Measure Set\nopen scoped ENNReal NNReal Function symmDiff\n\nnamespace MeasureTheory\n\nvariable {α β ι : Type*} {_ : MeasurableSpace α} {μ : Measure α} {s s₁ s₂ s₃ t t₁ t₂ u : Set α}\n\ntheorem measureReal_eq_zero_iff (h : μ s ≠ ∞ := by finiteness) :\n    μ.real s = 0 ↔ μ s = 0 := by\n  rw [Measure.real, ENNReal.toReal_eq_zero_iff]\n  exact or_iff_left h\n\ntheorem measureReal_ne_zero_iff (h : μ s ≠ ∞ := by finiteness) :\n    μ.real s ≠ 0 ↔ μ s ≠ 0 := by\n  simp [measureReal_eq_zero_iff, h]\n\n@[simp] theorem measureReal_zero : (0 : Measure α).real = 0 := rfl\n\ntheorem measureReal_zero_apply (s : Set α) : (0 : Measure α).real s = 0 := rfl\n\n@[simp] theorem measureReal_nonneg : 0 ≤ μ.real s := ENNReal.toReal_nonneg\n\n@[simp] theorem measureReal_empty : μ.real ∅ = 0 := by simp [Measure.real]"
      },
      {
        "first": 75,
        "last": 99,
        "source": "@[simp] theorem measureReal_nnreal_smul_apply (c : ℝ≥0) :\n    (c • μ).real s = c * μ.real s := by\n  simp [measureReal_def]\n\ntheorem map_measureReal_apply_of_aemeasurable [MeasurableSpace β] {f : α → β}\n    (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) :\n    (μ.map f).real s = μ.real (f ⁻¹' s) := by\n  simp_rw [measureReal_def, map_apply_of_aemeasurable hf hs]\n\ntheorem map_measureReal_apply [MeasurableSpace β] {f : α → β} (hf : Measurable f)\n    {s : Set β} (hs : MeasurableSet s) : (μ.map f).real s = μ.real (f ⁻¹' s) :=\n  map_measureReal_apply_of_aemeasurable hf.aemeasurable hs\n\n@[gcongr] theorem measureReal_mono (h : s₁ ⊆ s₂) (h₂ : μ s₂ ≠ ∞ := by finiteness) :\n    μ.real s₁ ≤ μ.real s₂ :=\n  ENNReal.toReal_mono h₂ (measure_mono h)\n\ntheorem measureReal_eq_measureReal_iff {m : MeasurableSpace β} {ν : Measure β} {t : Set β}\n    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : ν t ≠ ∞ := by finiteness) :\n    μ.real s = ν.real t ↔ μ s = ν t := by\n  simp [measureReal_def, ENNReal.toReal_eq_toReal_iff' h₁ h₂]\n\ntheorem measureReal_restrict_apply₀ (ht : NullMeasurableSet t (μ.restrict s)) :\n    (μ.restrict s).real t = μ.real (t ∩ s) := by\n  simp only [measureReal_def, restrict_apply₀ ht]"
      },
      {
        "first": 128,
        "last": 184,
        "source": "  rcases eq_top_or_lt_top (μ s) with hs | hs\n  · simp [Measure.real, hs]\n  · exact measureReal_mono subset_union_left (measure_union_lt_top hs h.lt_top).ne\n\ntheorem measureReal_le_measureReal_union_right (h : μ s ≠ ∞ := by finiteness) :\n    μ.real t ≤ μ.real (s ∪ t) := by\n  rw [union_comm]\n  exact measureReal_le_measureReal_union_left h\n\ntheorem measureReal_union_le (s₁ s₂ : Set α) : μ.real (s₁ ∪ s₂) ≤ μ.real s₁ + μ.real s₂ := by\n  rcases eq_top_or_lt_top (μ (s₁ ∪ s₂)) with h | h\n  · simp only [Measure.real, h, ENNReal.toReal_top]\n    exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg\n  · have A : μ s₁ ≠ ∞ := measure_ne_top_of_subset subset_union_left h.ne\n    have B : μ s₂ ≠ ∞ := measure_ne_top_of_subset subset_union_right h.ne\n    simp only [Measure.real, ← ENNReal.toReal_add A B]\n    exact ENNReal.toReal_mono (by simp [A, B]) (measure_union_le _ _)\n\ntheorem measureReal_biUnion_finset_le (s : Finset β) (f : β → Set α) :\n    μ.real (⋃ b ∈ s, f b) ≤ ∑ p ∈ s, μ.real (f p) := by\n  classical\n  induction s using Finset.induction_on with\n  | empty => simp\n  | insert _ _ hx IH =>\n    simp only [hx, Finset.mem_insert, iUnion_iUnion_eq_or_left, not_false_eq_true,\n      Finset.sum_insert]\n    exact (measureReal_union_le _ _).trans (by gcongr)\n\ntheorem measureReal_iUnion_fintype_le [Fintype β] (f : β → Set α) :\n    μ.real (⋃ b, f b) ≤ ∑ p, μ.real (f p) := by\n  convert! measureReal_biUnion_finset_le Finset.univ f\n  simp\n\ntheorem measureReal_iUnion_fintype [Fintype β] {f : β → Set α} (hn : Pairwise (Disjoint on f))\n    (h : ∀ i, MeasurableSet (f i)) (h' : ∀ i, μ (f i) ≠ ∞ := by finiteness) :\n    μ.real (⋃ b, f b) = ∑ p, μ.real (f p) := by\n  simp_rw [measureReal_def, measure_iUnion hn h, tsum_fintype,\n    ENNReal.toReal_sum (fun i _hi ↦ h' i)]\n\ntheorem measureReal_union_null (h₁ : μ.real s₁ = 0) (h₂ : μ.real s₂ = 0) :\n    μ.real (s₁ ∪ s₂) = 0 :=\n  le_antisymm ((measureReal_union_le s₁ s₂).trans (by simp [h₁, h₂])) measureReal_nonneg\n\n@[simp]\ntheorem measureReal_union_null_iff\n    (h₁ : μ s₁ ≠ ∞ := by finiteness) (h₂ : μ s₂ ≠ ∞ := by finiteness) :\n    μ.real (s₁ ∪ s₂) = 0 ↔ μ.real s₁ = 0 ∧ μ.real s₂ = 0 :=\n  ⟨fun h ↦ ⟨measureReal_mono_null subset_union_left h (by finiteness),\n      measureReal_mono_null subset_union_right h (by finiteness)⟩,\n  fun h ↦ measureReal_union_null h.1 h.2⟩\n\n/-- If two sets are equal modulo a set of measure zero, then `μ.real s = μ.real t`. -/\ntheorem measureReal_congr (H : s =ᵐ[μ] t) : μ.real s = μ.real t := by\n  simp [Measure.real, measure_congr H]\n\ntheorem measureReal_inter_add_sdiff₀ (ht : NullMeasurableSet t μ)\n    (h : μ s ≠ ∞ := by finiteness) :"
      }
    ],
    "bindingPath": "C:/game/shao lean/drafts/oq56/next-source/oq6-eta-event-transport-frontier-01/parent-api-01/comparison-probability-pinned-api-01.json"
  },
  {
    "module": "Mathlib.MeasureTheory.Measure.Typeclasses.Finite",
    "path": "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean",
    "sha256": "a8ef0ba0a9b953a5aae9fb16188cd7ad93e0e8d5767c564d02e9f2e8c57eedf2",
    "literalContextMarkers": [
      {
        "line": 21,
        "text": "open scoped NNReal Topology"
      },
      {
        "line": 22,
        "text": "open Set MeasureTheory Measure Filter Function MeasurableSpace ENNReal"
      },
      {
        "line": 24,
        "text": "variable {α β δ ι : Type*}"
      },
      {
        "line": 26,
        "text": "namespace MeasureTheory"
      },
      {
        "line": 28,
        "text": "variable {m0 : MeasurableSpace α} [mβ : MeasurableSpace β] {μ ν ν₁ ν₂ : Measure α}"
      },
      {
        "line": 31,
        "text": "section IsFiniteMeasure"
      },
      {
        "line": 211,
        "text": "open scoped symmDiff"
      }
    ],
    "windows": [
      {
        "first": 1,
        "last": 57,
        "source": "/-\nCopyright (c) 2017 Johannes Hölzl. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Johannes Hölzl, Mario Carneiro\n-/\nmodule\n\npublic import Mathlib.MeasureTheory.Measure.Restrict\n\n/-!\n# Classes for finite measures\n\nWe introduce the following typeclasses for measures:\n\n* `IsFiniteMeasure μ`: `μ univ < ∞`;\n* `IsLocallyFiniteMeasure μ` : `∀ x, ∃ s ∈ 𝓝 x, μ s < ∞`.\n-/\n\n@[expose] public section\n\nopen scoped NNReal Topology\nopen Set MeasureTheory Measure Filter Function MeasurableSpace ENNReal\n\nvariable {α β δ ι : Type*}\n\nnamespace MeasureTheory\n\nvariable {m0 : MeasurableSpace α} [mβ : MeasurableSpace β] {μ ν ν₁ ν₂ : Measure α}\n  {s t : Set α}\n\nsection IsFiniteMeasure\n\n/-- A measure `μ` is called finite if `μ univ < ∞`. -/\n@[mk_iff]\nclass IsFiniteMeasure (μ : Measure α) : Prop where\n  measure_univ_lt_top : μ univ < ∞\n\nlemma not_isFiniteMeasure_iff : ¬IsFiniteMeasure μ ↔ μ univ = ∞ := by simp [isFiniteMeasure_iff]\n\nlemma isFiniteMeasure_restrict : IsFiniteMeasure (μ.restrict s) ↔ μ s ≠ ∞ := by\n  simp [isFiniteMeasure_iff, lt_top_iff_ne_top]\n\ninstance Restrict.isFiniteMeasure (μ : Measure α) [hs : Fact (μ s < ∞)] :\n    IsFiniteMeasure (μ.restrict s) :=\n  ⟨by simpa using hs.elim⟩\n\n@[simp]\ntheorem measure_lt_top (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) : μ s < ∞ :=\n  (measure_mono (subset_univ s)).trans_lt IsFiniteMeasure.measure_univ_lt_top\n\ninstance isFiniteMeasureRestrict (μ : Measure α) (s : Set α) [h : IsFiniteMeasure μ] :\n    IsFiniteMeasure (μ.restrict s) := ⟨by simp⟩\n\n@[simp, aesop (rule_sets := [finiteness]) safe apply]\ntheorem measure_ne_top (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) : μ s ≠ ∞ :=\n  ne_of_lt (measure_lt_top μ s)\n"
      },
      {
        "first": 202,
        "last": 235,
        "source": "    obtain ⟨j, _, x_in_Es_j⟩ := hx 0\n    obtain ⟨k, k_gt_j, x_in_Es_k⟩ := hx (j + 1)\n    have oops := (Es_disj (Nat.ne_of_lt k_gt_j)).ne_of_mem x_in_Es_j x_in_Es_k\n    contradiction\n  have key := tendsto_measure_iInter_atTop (μ := μ) (fun n ↦ by measurability)\n    decr ⟨0, measure_ne_top _ _⟩\n  simp only [nothing, measure_empty] at key\n  convert key\n\nopen scoped symmDiff\n\ntheorem abs_measureReal_sub_le_measureReal_symmDiff'\n    (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) (hs' : μ s ≠ ∞) (ht' : μ t ≠ ∞) :\n    |μ.real s - μ.real t| ≤ μ.real (s ∆ t) := by\n  simp only [Measure.real]\n  have hst : μ (s \\ t) ≠ ∞ := (measure_lt_top_of_subset sdiff_subset hs').ne\n  have hts : μ (t \\ s) ≠ ∞ := (measure_lt_top_of_subset sdiff_subset ht').ne\n  suffices (μ s).toReal - (μ t).toReal = (μ (s \\ t)).toReal - (μ (t \\ s)).toReal by\n    rw [this, measure_symmDiff_eq hs ht, ENNReal.toReal_add hst hts]\n    convert abs_sub (μ (s \\ t)).toReal (μ (t \\ s)).toReal <;> simp\n  rw [measure_sdiff' s ht ht', measure_sdiff' t hs hs',\n    ENNReal.toReal_sub_of_le measure_le_measure_union_right (by finiteness),\n    ENNReal.toReal_sub_of_le measure_le_measure_union_right (by finiteness),\n    union_comm t s]\n  abel\n\ntheorem abs_measureReal_sub_le_measureReal_symmDiff [IsFiniteMeasure μ]\n    (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :\n    |μ.real s - μ.real t| ≤ μ.real (s ∆ t) :=\n  abs_measureReal_sub_le_measureReal_symmDiff' hs ht (by finiteness) (by finiteness)\n\ninstance {s : Finset ι} {μ : ι → Measure α} [∀ i, IsFiniteMeasure (μ i)] :\n    IsFiniteMeasure (∑ i ∈ s, μ i) where measure_univ_lt_top := by simp [measure_lt_top]\n"
      }
    ],
    "bindingPath": "C:/game/shao lean/drafts/oq56/next-source/oq6-eta-event-transport-frontier-01/parent-api-01/comparison-probability-pinned-api-01.json"
  },
  {
    "binding": {
      "path": "C:/game/shao lean/drafts/oq56/next-source/oq6-log-cutoff-low-energy-180/lead-primary-api-01/real-measure-mono-and-strict-measurability-source-packet.json",
      "sha256": "cbcec91bda629b87758eec4180508b6b07859d7380a5f252cb437ec9e008ac79",
      "bytes": 16828,
      "readScope": "pinned primary contexts only; no execution"
    },
    "mathlibHEAD": "807d3836b165983210ee2ecf3cd28f239436949c",
    "files": [
      {
        "sourcePath": "Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean",
        "sourceSHA256": "b00231965385b4be92c215dff1d287910ee096833b96b4589d716fe7e9b5ad2e",
        "sourceBytes": 55079,
        "requestedDeclaration": "measurableSet_lt",
        "declarationLine1": 245,
        "firstLine1": 1,
        "lastLine1": 267,
        "completePrefixRaw": "/-\nCopyright (c) 2017 Johannes Hölzl. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Johannes Hölzl, Yury Kudryashov, Kexing Ying\n-/\nmodule\n\npublic import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic\npublic import Mathlib.MeasureTheory.Function.AEMeasurableSequence\npublic import Mathlib.MeasureTheory.Measure.Interval\npublic import Mathlib.MeasureTheory.Order.Lattice\npublic import Mathlib.Topology.Order.Lattice\n\n/-!\n# Borel sigma algebras on spaces with orders\n\n## Main statements\n\n* `borel_eq_generateFrom_Ixx` (where Ixx is one of `{Iio, Ioi, Iic, Ici, Ico, Ioc}`):\n  The Borel sigma algebra of a linear order topology is generated by intervals of the given kind.\n* `Dense.borel_eq_generateFrom_Ico_mem`, `Dense.borel_eq_generateFrom_Ioc_mem`:\n  The Borel sigma algebra of a dense linear order topology is generated by intervals of a given\n  kind, with endpoints from dense subsets.\n* `ext_of_Ico`, `ext_of_Ioc`:\n  A locally finite Borel measure on a second countable conditionally complete linear order is\n  characterized by the measures of intervals of the given kind.\n* `ext_of_Iic`, `ext_of_Ici`:\n  A finite Borel measure on a second countable linear order is characterized by the measures of\n  intervals of the given kind.\n* `UpperSemicontinuous.measurable`, `LowerSemicontinuous.measurable`:\n  Semicontinuous functions are measurable.\n* `Measurable.iSup`, `Measurable.iInf`, `Measurable.sSup`, `Measurable.sInf`:\n  Countable supremums and infimums of measurable functions to conditionally complete linear orders\n  are measurable.\n* `Measurable.liminf`, `Measurable.limsup`:\n  Countable liminfs and limsups of measurable functions to conditionally complete linear orders\n  are measurable.\n\n-/\n\npublic section\n\nopen Set Filter MeasureTheory MeasurableSpace TopologicalSpace\n\nopen scoped Topology NNReal ENNReal MeasureTheory\n\nuniverse u v w x y\n\nvariable {α β γ δ : Type*} {ι : Sort y} {s t u : Set α}\n\nsection OrderTopology\n\nvariable (α)\nvariable [TopologicalSpace α] [SecondCountableTopology α] [LinearOrder α] [OrderTopology α]\n\ntheorem borel_eq_generateFrom_Iio : borel α = .generateFrom (range Iio) := by\n  refine le_antisymm ?_ (generateFrom_le ?_)\n  · rw [borel_eq_generateFrom_of_subbasis (@OrderTopology.topology_eq_generate_intervals α _ _ _)]\n    let : MeasurableSpace α := MeasurableSpace.generateFrom (range Iio)\n    have H : ∀ a : α, MeasurableSet (Iio a) := fun a => GenerateMeasurable.basic _ ⟨_, rfl⟩\n    refine generateFrom_le ?_\n    rintro _ ⟨a, rfl | rfl⟩\n    · rcases em (∃ b, a ⋖ b) with ⟨b, hb⟩ | hcovBy\n      · rw [hb.Ioi_eq, ← compl_Iio]\n        exact (H _).compl\n      · rcases isOpen_biUnion_countable (Ioi a) Ioi fun _ _ ↦ isOpen_Ioi with ⟨t, hat, htc, htU⟩\n        have : Ioi a = ⋃ b ∈ t, Ici b := by\n          refine Subset.antisymm ?_ <| iUnion₂_subset fun b hb ↦ Ici_subset_Ioi.2 (hat hb)\n          refine Subset.trans ?_ <| iUnion₂_mono fun _ _ ↦ Ioi_subset_Ici_self\n          simpa [CovBy, htU, subset_def] using hcovBy\n        simp only [this, ← compl_Iio]\n        exact .biUnion htc <| fun _ _ ↦ (H _).compl\n    · apply H\n  · rw [forall_mem_range]\n    intro a\n    exact GenerateMeasurable.basic _ isOpen_Iio\n\ntheorem borel_eq_generateFrom_Ioi : borel α = .generateFrom (range Ioi) :=\n  @borel_eq_generateFrom_Iio αᵒᵈ _ (by infer_instance : SecondCountableTopology α) _ _\n\ntheorem borel_eq_generateFrom_Iic :\n    borel α = MeasurableSpace.generateFrom (range Iic) := by\n  rw [borel_eq_generateFrom_Ioi]\n  refine le_antisymm ?_ ?_\n  · refine MeasurableSpace.generateFrom_le fun t ht => ?_\n    obtain ⟨u, rfl⟩ := ht\n    rw [← compl_Iic]\n    exact (MeasurableSpace.measurableSet_generateFrom (mem_range.mpr ⟨u, rfl⟩)).compl\n  · refine MeasurableSpace.generateFrom_le fun t ht => ?_\n    obtain ⟨u, rfl⟩ := ht\n    rw [← compl_Ioi]\n    exact (MeasurableSpace.measurableSet_generateFrom (mem_range.mpr ⟨u, rfl⟩)).compl\n\ntheorem borel_eq_generateFrom_Ici : borel α = MeasurableSpace.generateFrom (range Ici) :=\n  @borel_eq_generateFrom_Iic αᵒᵈ _ _ _ _\n\nend OrderTopology\n\nsection Orders\n\nvariable [TopologicalSpace α] {mα : MeasurableSpace α} [OpensMeasurableSpace α]\nvariable {mδ : MeasurableSpace δ}\n\nsection Preorder\n\nvariable [Preorder α] {a b x : α} {μ : Measure α}\n\n@[simp, measurability]\ntheorem measurableSet_Ici [ClosedIciTopology α] : MeasurableSet (Ici a) :=\n  isClosed_Ici.measurableSet\n\ntheorem nullMeasurableSet_Ici [ClosedIciTopology α] : NullMeasurableSet (Ici a) μ :=\n  measurableSet_Ici.nullMeasurableSet\n\n@[simp, measurability]\ntheorem measurableSet_Iic [ClosedIicTopology α] : MeasurableSet (Iic a) :=\n  isClosed_Iic.measurableSet\n\ntheorem nullMeasurableSet_Iic [ClosedIicTopology α] : NullMeasurableSet (Iic a) μ :=\n  measurableSet_Iic.nullMeasurableSet\n\n@[simp, measurability]\ntheorem measurableSet_Icc [OrderClosedTopology α] : MeasurableSet (Icc a b) :=\n  isClosed_Icc.measurableSet\n\ntheorem nullMeasurableSet_Icc [OrderClosedTopology α] : NullMeasurableSet (Icc a b) μ :=\n  measurableSet_Icc.nullMeasurableSet\n\ninstance nhdsWithin_Ici_isMeasurablyGenerated [ClosedIciTopology α] :\n    (𝓝[Ici b] a).IsMeasurablyGenerated :=\n  measurableSet_Ici.nhdsWithin_isMeasurablyGenerated _\n\ninstance nhdsWithin_Iic_isMeasurablyGenerated [ClosedIicTopology α] :\n    (𝓝[Iic b] a).IsMeasurablyGenerated :=\n  measurableSet_Iic.nhdsWithin_isMeasurablyGenerated _\n\ninstance nhdsWithin_Icc_isMeasurablyGenerated [OrderClosedTopology α] :\n    IsMeasurablyGenerated (𝓝[Icc a b] x) := by\n  rw [← Ici_inter_Iic, nhdsWithin_inter]\n  infer_instance\n\ninstance atTop_isMeasurablyGenerated [ClosedIciTopology α] :\n    (Filter.atTop : Filter α).IsMeasurablyGenerated :=\n  @Filter.iInf_isMeasurablyGenerated _ _ _ _ fun a =>\n    (measurableSet_Ici : MeasurableSet (Ici a)).principal_isMeasurablyGenerated\n\ninstance atBot_isMeasurablyGenerated [ClosedIicTopology α] :\n    (Filter.atBot : Filter α).IsMeasurablyGenerated :=\n  @Filter.iInf_isMeasurablyGenerated _ _ _ _ fun a =>\n    (measurableSet_Iic : MeasurableSet (Iic a)).principal_isMeasurablyGenerated\n\ninstance [R1Space α] : IsMeasurablyGenerated (cocompact α) where\n  exists_measurable_subset := by\n    intro _ hs\n    obtain ⟨t, ht, hts⟩ := mem_cocompact.mp hs\n    exact ⟨(closure t)ᶜ, ht.closure.compl_mem_cocompact, isClosed_closure.measurableSet.compl,\n      (compl_subset_compl.2 subset_closure).trans hts⟩\n\nend Preorder\n\nsection PartialOrder\n\nvariable [PartialOrder α] [OrderClosedTopology α] [SecondCountableTopology α] {a : α}\n\ntheorem measurableSet_le' : MeasurableSet { p : α × α | p.1 ≤ p.2 } :=\n  OrderClosedTopology.isClosed_le'.measurableSet\n\n@[fun_prop]\ntheorem measurable_le : Measurable fun p : α × α => p.1 ≤ p.2 :=\n  measurableSet_setOfPred.mp measurableSet_le'\n\ntheorem measurableSet_le {f g : δ → α} (hf : Measurable f) (hg : Measurable g) :\n    MeasurableSet { a | f a ≤ g a } :=\n  hf.prodMk hg measurableSet_le'\n\ntheorem Measurable.le' {f g : δ → α} (hf : Measurable f) (hg : Measurable g) :\n    Measurable fun a => f a ≤ g a := by\n  fun_prop\n\nend PartialOrder\n\nsection LinearOrder\n\nvariable [LinearOrder α] {a b x : α} {μ : Measure α}\n\n-- we open this scope only here to avoid issues with list being treated as intervals above\nopen scoped Interval\n\n@[simp, measurability]\ntheorem measurableSet_Iio [ClosedIciTopology α] : MeasurableSet (Iio a) :=\n  isOpen_Iio.measurableSet\n\ntheorem nullMeasurableSet_Iio [ClosedIciTopology α] : NullMeasurableSet (Iio a) μ :=\n  measurableSet_Iio.nullMeasurableSet\n\n@[simp, measurability]\ntheorem measurableSet_Ioi [ClosedIicTopology α] : MeasurableSet (Ioi a) :=\n  isOpen_Ioi.measurableSet\n\ntheorem nullMeasurableSet_Ioi [ClosedIicTopology α] : NullMeasurableSet (Ioi a) μ :=\n  measurableSet_Ioi.nullMeasurableSet\n\n@[simp, measurability]\ntheorem measurableSet_Ioo [OrderClosedTopology α] : MeasurableSet (Ioo a b) :=\n  isOpen_Ioo.measurableSet\n\ntheorem nullMeasurableSet_Ioo [OrderClosedTopology α] : NullMeasurableSet (Ioo a b) μ :=\n  measurableSet_Ioo.nullMeasurableSet\n\n@[simp, measurability]\ntheorem measurableSet_Ioc [ClosedIicTopology α] : MeasurableSet (Ioc a b) :=\n  measurableSet_Ioi.inter measurableSet_Iic\n\ntheorem nullMeasurableSet_Ioc [ClosedIicTopology α] : NullMeasurableSet (Ioc a b) μ :=\n  measurableSet_Ioc.nullMeasurableSet\n\n@[simp, measurability]\ntheorem measurableSet_Ico [ClosedIciTopology α] : MeasurableSet (Ico a b) :=\n  measurableSet_Ici.inter measurableSet_Iio\n\ntheorem nullMeasurableSet_Ico [ClosedIciTopology α] : NullMeasurableSet (Ico a b) μ :=\n  measurableSet_Ico.nullMeasurableSet\n\ninstance nhdsWithin_Ioi_isMeasurablyGenerated [ClosedIicTopology α] :\n    (𝓝[Ioi b] a).IsMeasurablyGenerated :=\n  measurableSet_Ioi.nhdsWithin_isMeasurablyGenerated _\n\ninstance nhdsWithin_Iio_isMeasurablyGenerated [ClosedIciTopology α] :\n    (𝓝[Iio b] a).IsMeasurablyGenerated :=\n  measurableSet_Iio.nhdsWithin_isMeasurablyGenerated _\n\ninstance nhdsWithin_uIcc_isMeasurablyGenerated [OrderClosedTopology α] :\n    IsMeasurablyGenerated (𝓝[[[a, b]]] x) :=\n  nhdsWithin_Icc_isMeasurablyGenerated\n\ntheorem measurableSet_lt' [SecondCountableTopology α] [OrderClosedTopology α] :\n    MeasurableSet { p : α × α | p.1 < p.2 } :=\n  (isOpen_lt continuous_fst continuous_snd).measurableSet\n\n@[fun_prop]\ntheorem measurable_lt [SecondCountableTopology α] [OrderClosedTopology α] :\n    Measurable fun p : α × α => p.1 < p.2 :=\n  measurableSet_setOfPred.mp measurableSet_lt'\n\ntheorem measurableSet_lt [SecondCountableTopology α] [OrderClosedTopology α]\n    {f g : δ → α} (hf : Measurable f) (hg : Measurable g) :\n    MeasurableSet { a | f a < g a } :=\n  hf.prodMk hg measurableSet_lt'\n\ntheorem Measurable.lt [SecondCountableTopology α] [OrderClosedTopology α] {f g : δ → α}\n    (hf : Measurable f) (hg : Measurable g) :\n    Measurable fun a => f a < g a := by\n  fun_prop\n\ntheorem nullMeasurableSet_lt [SecondCountableTopology α] [OrderClosedTopology α] {μ : Measure δ}\n    {f g : δ → α} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :\n    NullMeasurableSet { a | f a < g a } μ :=\n  (hf.prodMk hg).nullMeasurable measurableSet_lt'\n\ntheorem nullMeasurableSet_lt' [SecondCountableTopology α] [OrderClosedTopology α]\n    {μ : Measure (α × α)} :\n    NullMeasurableSet { p : α × α | p.1 < p.2 } μ :=\n  measurableSet_lt'.nullMeasurableSet\n\ntheorem nullMeasurableSet_le [SecondCountableTopology α] [OrderClosedTopology α] {μ : Measure δ}\n    {f g : δ → α} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :\n    NullMeasurableSet { a | f a ≤ g a } μ :=\n",
        "contextMethod": "Completefileprefixfromline1includingallmulti-linevariables/namespaces/sections/instances beforefullrequestedlemma;no truncatedstructuraldeclarations"
      }
    ]
  },
  {
    "binding": {
      "path": "C:/game/shao lean/drafts/oq56/next-source/oq6-conditional-low-energy-frontier-01/lead-primary-api-01/finite-product-probability-coordinate-source-packet.json",
      "sha256": "6bb1b7440d9dd2e0a1fcb921c6b7201d1d7e535823a2fc6638ea8686bf988b65",
      "bytes": 9350,
      "readScope": "pinned primary contexts only; no execution"
    },
    "mathlibHEAD": "807d3836b165983210ee2ecf3cd28f239436949c",
    "files": [
      {
        "sourcePath": "Mathlib/MeasureTheory/Constructions/Pi.lean",
        "sourceSHA256": "bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef",
        "sourceBytes": 47126,
        "firstLine1": 303,
        "lastLine1": 313,
        "raw": "instance pi.instIsFiniteMeasure [∀ i, IsFiniteMeasure (μ i)] :\n    IsFiniteMeasure (Measure.pi μ) :=\n  ⟨Measure.pi_univ μ ▸ ENNReal.prod_lt_top (fun i _ ↦ measure_lt_top (μ i) _)⟩\n\ninstance {α : ι → Type*} [∀ i, MeasureSpace (α i)] [∀ i, IsFiniteMeasure (volume : Measure (α i))] :\n    IsFiniteMeasure (volume : Measure (∀ i, α i)) :=\n  pi.instIsFiniteMeasure _\n\ninstance pi.instIsProbabilityMeasure [∀ i, IsProbabilityMeasure (μ i)] :\n    IsProbabilityMeasure (Measure.pi μ) :=\n  ⟨by simp only [Measure.pi_univ, measure_univ, Finset.prod_const_one]⟩\n",
        "rawSHA256": "cc4d09d6b31c9d5bbeabbb89248aa011c35720ea4bd858561b8c68b647a9a076",
        "chronologicalStructuralContext": [
          {
            "firstLine1": 58,
            "lastLine1": 58,
            "raw": "noncomputable section\n"
          },
          {
            "firstLine1": 60,
            "lastLine1": 60,
            "raw": "open Function Set MeasureTheory.OuterMeasure Filter MeasurableSpace Encodable\n"
          },
          {
            "firstLine1": 62,
            "lastLine1": 62,
            "raw": "open scoped Topology ENNReal\n"
          },
          {
            "firstLine1": 66,
            "lastLine1": 67,
            "raw": "variable {ι ι' : Type*} {α : ι → Type*}\n\n"
          },
          {
            "firstLine1": 68,
            "lastLine1": 68,
            "raw": "namespace MeasureTheory\n"
          },
          {
            "firstLine1": 70,
            "lastLine1": 71,
            "raw": "variable [Fintype ι] {m : ∀ i, OuterMeasure (α i)}\n\n"
          },
          {
            "firstLine1": 100,
            "lastLine1": 100,
            "raw": "namespace OuterMeasure\n"
          },
          {
            "firstLine1": 123,
            "lastLine1": 123,
            "raw": "end OuterMeasure\n"
          },
          {
            "firstLine1": 125,
            "lastLine1": 125,
            "raw": "namespace Measure\n"
          },
          {
            "firstLine1": 127,
            "lastLine1": 128,
            "raw": "variable [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))\n\n"
          },
          {
            "firstLine1": 129,
            "lastLine1": 129,
            "raw": "section Tprod\n"
          },
          {
            "firstLine1": 131,
            "lastLine1": 131,
            "raw": "open List\n"
          },
          {
            "firstLine1": 133,
            "lastLine1": 134,
            "raw": "variable {δ : Type*} {X : δ → Type*} [∀ i, MeasurableSpace (X i)]\n\n"
          },
          {
            "firstLine1": 169,
            "lastLine1": 169,
            "raw": "end Tprod\n"
          },
          {
            "firstLine1": 171,
            "lastLine1": 171,
            "raw": "section Encodable\n"
          },
          {
            "firstLine1": 173,
            "lastLine1": 173,
            "raw": "open List\n"
          },
          {
            "firstLine1": 175,
            "lastLine1": 176,
            "raw": "variable [Encodable ι]\n\n"
          },
          {
            "firstLine1": 177,
            "lastLine1": 177,
            "raw": "open scoped Classical in\n"
          },
          {
            "firstLine1": 193,
            "lastLine1": 193,
            "raw": "end Encodable\n"
          },
          {
            "firstLine1": 232,
            "lastLine1": 233,
            "raw": "variable {μ}\n\n"
          },
          {
            "firstLine1": 285,
            "lastLine1": 286,
            "raw": "variable (μ)\n\n"
          }
        ]
      },
      {
        "sourcePath": "Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean",
        "sourceSHA256": "03bdd1fd16c69f61acf8ae50d684f54c9b565d03c6fa880fc338fcbd3bbebadb",
        "sourceBytes": 49519,
        "firstLine1": 579,
        "lastLine1": 585,
        "raw": "theorem measurable_pi_iff {g : α → ∀ a, X a} : Measurable g ↔ ∀ a, Measurable fun x => g x a := by\n  simp_rw [measurable_iff_comap_le, MeasurableSpace.pi, MeasurableSpace.comap_iSup,\n    MeasurableSpace.comap_comp, Function.comp_def, iSup_le_iff]\n\n@[fun_prop]\ntheorem measurable_pi_apply (a : δ) : Measurable fun f : ∀ a, X a => f a :=\n  measurable_pi_iff.1 measurable_id a\n",
        "rawSHA256": "b7189c866b674a9e185c10d51e0737f3a799cacd47d2816480a7c4e3cb684954",
        "chronologicalStructuralContext": [
          {
            "firstLine1": 27,
            "lastLine1": 27,
            "raw": "open Set Function MeasureTheory\n"
          },
          {
            "firstLine1": 31,
            "lastLine1": 32,
            "raw": "variable {α β γ δ δ' : Type*} {ι : Sort uι} {s : Set α}\n\n"
          },
          {
            "firstLine1": 60,
            "lastLine1": 60,
            "raw": "section ULift\n"
          },
          {
            "firstLine1": 61,
            "lastLine1": 62,
            "raw": "variable [MeasurableSpace α]\n\n"
          },
          {
            "firstLine1": 74,
            "lastLine1": 74,
            "raw": "end ULift\n"
          },
          {
            "firstLine1": 76,
            "lastLine1": 76,
            "raw": "section Nat\n"
          },
          {
            "firstLine1": 78,
            "lastLine1": 79,
            "raw": "variable {mα : MeasurableSpace α}\n\n"
          },
          {
            "firstLine1": 123,
            "lastLine1": 123,
            "raw": "end Nat\n"
          },
          {
            "firstLine1": 125,
            "lastLine1": 125,
            "raw": "section Quotient\n"
          },
          {
            "firstLine1": 127,
            "lastLine1": 128,
            "raw": "variable [MeasurableSpace α] [MeasurableSpace β]\n\n"
          },
          {
            "firstLine1": 180,
            "lastLine1": 180,
            "raw": "end Quotient\n"
          },
          {
            "firstLine1": 182,
            "lastLine1": 182,
            "raw": "section Subtype\n"
          },
          {
            "firstLine1": 188,
            "lastLine1": 188,
            "raw": "section\n"
          },
          {
            "firstLine1": 190,
            "lastLine1": 191,
            "raw": "variable [MeasurableSpace α]\n\n"
          },
          {
            "firstLine1": 201,
            "lastLine1": 201,
            "raw": "end\n"
          },
          {
            "firstLine1": 203,
            "lastLine1": 204,
            "raw": "variable {m : MeasurableSpace α} {mβ : MeasurableSpace β}\n\n"
          },
          {
            "firstLine1": 290,
            "lastLine1": 290,
            "raw": "end Subtype\n"
          },
          {
            "firstLine1": 292,
            "lastLine1": 292,
            "raw": "section Atoms\n"
          },
          {
            "firstLine1": 294,
            "lastLine1": 295,
            "raw": "variable [MeasurableSpace β]\n\n"
          },
          {
            "firstLine1": 365,
            "lastLine1": 365,
            "raw": "end Atoms\n"
          },
          {
            "firstLine1": 367,
            "lastLine1": 367,
            "raw": "section Prod\n"
          },
          {
            "firstLine1": 387,
            "lastLine1": 388,
            "raw": "variable {m : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}\n\n"
          },
          {
            "firstLine1": 568,
            "lastLine1": 568,
            "raw": "end Prod\n"
          },
          {
            "firstLine1": 570,
            "lastLine1": 570,
            "raw": "section Pi\n"
          },
          {
            "firstLine1": 572,
            "lastLine1": 573,
            "raw": "variable {X : δ → Type*} [MeasurableSpace α]\n\n"
          },
          {
            "firstLine1": 577,
            "lastLine1": 578,
            "raw": "variable [∀ a, MeasurableSpace (X a)] [MeasurableSpace γ]\n\n"
          }
        ]
      }
    ]
  },
  {
    "binding": {
      "path": "C:/game/shao lean/drafts/oq56/unit218/parent-pinned-interfaces01/pinned-mathlib-source-query11.json",
      "sha256": "bd87d8456ff087986fdab013f2e8c2eaaba444f3e09660d0f5062686f13b83d3",
      "bytes": 25947
    },
    "pinnedMathlibHEAD": "807d3836b165983210ee2ecf3cd28f239436949c",
    "sourceRanges": [
      {
        "path": "Mathlib/MeasureTheory/MeasurableSpace/Defs.lean",
        "fileSHA256": "bbb025056bb49e962516e9d495bbda6356251a19fde31544d820ecbe50894ecf",
        "startLine": 40,
        "endLine": 67,
        "source": "assert_not_exists Covariant MonoidWithZero\n\nopen Set Function\n\nvariable {α β γ δ : Type*} {ι : Sort*} {s t u : Set α}\n\n/-- A measurable space is a space equipped with a σ-algebra. -/\n@[class, wikidata Q3058218] structure MeasurableSpace (α : Type*) where\n  /-- Predicate saying that a given set is measurable. Use `MeasurableSet` in the root namespace\n  instead. -/\n  MeasurableSet' : Set α → Prop\n  /-- The empty set is a measurable set. Use `MeasurableSet.empty` instead. -/\n  measurableSet_empty : MeasurableSet' ∅\n  /-- The complement of a measurable set is a measurable set. Use `MeasurableSet.compl` instead. -/\n  measurableSet_compl : ∀ s, MeasurableSet' s → MeasurableSet' sᶜ\n  /-- The union of a sequence of measurable sets is a measurable set. Use a more general\n  `MeasurableSet.iUnion` instead. -/\n  measurableSet_iUnion : ∀ f : ℕ → Set α, (∀ i, MeasurableSet' (f i)) → MeasurableSet' (⋃ i, f i)\n\ninstance [h : MeasurableSpace α] : MeasurableSpace αᵒᵈ := h\n\n/-- `MeasurableSet s` means that `s` is measurable (in the ambient measure space on `α`) -/\n@[wikidata Q3054889]\ndef MeasurableSet [MeasurableSpace α] (s : Set α) : Prop :=\n  ‹MeasurableSpace α›.MeasurableSet' s\n\n/-- Notation for `MeasurableSet` with respect to a non-standard σ-algebra. -/\nscoped[MeasureTheory] notation \"MeasurableSet[\" m \"]\" => @MeasurableSet _ m\n",
        "excerptSHA256": "e018857c4d9023ed7f90a9e5f5657c0c44329bc3baa02bb5e963faf4dc45c5c1"
      },
      {
        "path": "Mathlib/MeasureTheory/MeasurableSpace/Defs.lean",
        "fileSHA256": "bbb025056bb49e962516e9d495bbda6356251a19fde31544d820ecbe50894ecf",
        "startLine": 55,
        "endLine": 82,
        "source": "  /-- The union of a sequence of measurable sets is a measurable set. Use a more general\n  `MeasurableSet.iUnion` instead. -/\n  measurableSet_iUnion : ∀ f : ℕ → Set α, (∀ i, MeasurableSet' (f i)) → MeasurableSet' (⋃ i, f i)\n\ninstance [h : MeasurableSpace α] : MeasurableSpace αᵒᵈ := h\n\n/-- `MeasurableSet s` means that `s` is measurable (in the ambient measure space on `α`) -/\n@[wikidata Q3054889]\ndef MeasurableSet [MeasurableSpace α] (s : Set α) : Prop :=\n  ‹MeasurableSpace α›.MeasurableSet' s\n\n/-- Notation for `MeasurableSet` with respect to a non-standard σ-algebra. -/\nscoped[MeasureTheory] notation \"MeasurableSet[\" m \"]\" => @MeasurableSet _ m\n\nopen scoped MeasureTheory\n\nsection\n\nopen scoped symmDiff\n\n@[simp, measurability]\ntheorem MeasurableSet.empty [MeasurableSpace α] : MeasurableSet (∅ : Set α) :=\n  MeasurableSpace.measurableSet_empty _\n\nvariable {m : MeasurableSpace α}\n\n@[measurability]\nprotected theorem MeasurableSet.compl : MeasurableSet s → MeasurableSet sᶜ :=\n",
        "excerptSHA256": "75e5f898dd332a23059308ee44986fb15e25aedda1249d8ab3fe018ea6e5bf84"
      },
      {
        "path": "Mathlib/MeasureTheory/MeasurableSpace/Defs.lean",
        "fileSHA256": "bbb025056bb49e962516e9d495bbda6356251a19fde31544d820ecbe50894ecf",
        "startLine": 65,
        "endLine": 92,
        "source": "\n/-- Notation for `MeasurableSet` with respect to a non-standard σ-algebra. -/\nscoped[MeasureTheory] notation \"MeasurableSet[\" m \"]\" => @MeasurableSet _ m\n\nopen scoped MeasureTheory\n\nsection\n\nopen scoped symmDiff\n\n@[simp, measurability]\ntheorem MeasurableSet.empty [MeasurableSpace α] : MeasurableSet (∅ : Set α) :=\n  MeasurableSpace.measurableSet_empty _\n\nvariable {m : MeasurableSpace α}\n\n@[measurability]\nprotected theorem MeasurableSet.compl : MeasurableSet s → MeasurableSet sᶜ :=\n  MeasurableSpace.measurableSet_compl _ s\n\nprotected theorem MeasurableSet.of_compl (h : MeasurableSet sᶜ) : MeasurableSet s :=\n  compl_compl s ▸ h.compl\n\n@[simp]\ntheorem MeasurableSet.compl_iff : MeasurableSet sᶜ ↔ MeasurableSet s :=\n  ⟨.of_compl, .compl⟩\n\n@[simp, measurability]\n",
        "excerptSHA256": "c8c6bdb9cd2449f49b62d950ca7ea537d787027d9ff45868f4422d243d218142"
      },
      {
        "path": "Mathlib/MeasureTheory/MeasurableSpace/Defs.lean",
        "fileSHA256": "bbb025056bb49e962516e9d495bbda6356251a19fde31544d820ecbe50894ecf",
        "startLine": 492,
        "endLine": 519,
        "source": "def Measurable [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Prop :=\n  ∀ ⦃t : Set β⦄, MeasurableSet t → MeasurableSet (f ⁻¹' t)\n\nadd_aesop_rules safe tactic\n  (rule_sets := [Measurable])\n  (index := [target @Measurable ..])\n  (by fun_prop (disch := measurability))\n\nnamespace MeasureTheory\n\nset_option quotPrecheck false in\n/-- Notation for `Measurable` with respect to a non-standard σ-algebra in the domain. -/\nscoped notation \"Measurable[\" m \"]\" => @Measurable _ _ m _\n/-- Notation for `Measurable` with respect to a non-standard σ-algebra in the domain and codomain.\n-/\nscoped notation \"Measurable[\" mα \", \" mβ \"]\" => @Measurable _ _ mα mβ\n\nend MeasureTheory\n\nsection MeasurableFunctions\nvariable {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {p : Prop}\n\ntheorem measurable_id : Measurable (@id α) := fun _ => id\n\n@[fun_prop]\ntheorem measurable_id' : Measurable fun a : α => a := measurable_id\n\n-- Allow `to_fun` to eta-expand `g ∘ f`. Ideally, `Function.comp_def` would be a global pull lemma\n",
        "excerptSHA256": "1515ccbda093ae7fbdc2cfa74fd462b6bae04b538f2d74787a9436dc67d8ee3d"
      },
      {
        "path": "Mathlib/MeasureTheory/MeasurableSpace/Defs.lean",
        "fileSHA256": "bbb025056bb49e962516e9d495bbda6356251a19fde31544d820ecbe50894ecf",
        "startLine": 495,
        "endLine": 522,
        "source": "add_aesop_rules safe tactic\n  (rule_sets := [Measurable])\n  (index := [target @Measurable ..])\n  (by fun_prop (disch := measurability))\n\nnamespace MeasureTheory\n\nset_option quotPrecheck false in\n/-- Notation for `Measurable` with respect to a non-standard σ-algebra in the domain. -/\nscoped notation \"Measurable[\" m \"]\" => @Measurable _ _ m _\n/-- Notation for `Measurable` with respect to a non-standard σ-algebra in the domain and codomain.\n-/\nscoped notation \"Measurable[\" mα \", \" mβ \"]\" => @Measurable _ _ mα mβ\n\nend MeasureTheory\n\nsection MeasurableFunctions\nvariable {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {p : Prop}\n\ntheorem measurable_id : Measurable (@id α) := fun _ => id\n\n@[fun_prop]\ntheorem measurable_id' : Measurable fun a : α => a := measurable_id\n\n-- Allow `to_fun` to eta-expand `g ∘ f`. Ideally, `Function.comp_def` would be a global pull lemma\n-- instead, which is not supported yet: see https://github.com/leanprover-community/mathlib4/issues/40183.\nattribute [local push ←] Function.comp_def\n@[to_fun]\n",
        "excerptSHA256": "9bed31bf40f01523f2a26736f1069512f34f96cb7b7e17140c26c5ec652493d1"
      }
    ],
    "selectedUse": "Use the literal defining preimage predicate for composition if the convenience Measurable.comp head is not separately supplied. No extra mathematical interface is needed."
  }
]
```

## Approved consumption

1. bounded_remainder_small_window: set y=1,K=Ktail; same originalRows/originalUpper C2source bounds, original r symmetry derived from hhsymm; use n>=4 from SAME247 eventual point and window1 derived from current z. Its last conclusion gives |delta|<=1/32 and hence delta>=-1/2.
2. literal_clippedCentered_comparison_on_projectionGood: set512/rho/y=1; rho>=0 is sqrt nonneg, and the only new studentizer condition is the explicit conditional1+rho<=sqrt n. This gives the true centeredSq sqrt denominator and literal zero branch.
3. actual_normalized_compact_clipped_observables: use original μ/h assumptions, same n, source z=0,C0=512. Take Measurable Tclip/Tactual only, exact returned physical RHS. There is no new model/measure/cg selection.
4. abs_measureReal_sub_le_measureReal_symmDiff with finite original P and measurable closed events; pointwise symmetric differences lie inside Ephysical, then measureReal_mono pays with P.real Ephysical<=P.real H1source complement<=payment1.
5. The imported239 helper and its main existential selector are NOT selected consumers. None of235/237/239 existentialcg selectors is allowed.

No new externalShaoZhou assertion is introduced. The existing ScalarShaoZhouFiniteCostTailInput remains an explicit conditional argument at currentz, with the original literal sourceCost0.

## Exact equality-event API and ambient contexts

The literal Ephysical set is the complement of {T0=Tphysical}. Use the following source-qualified primary head and existing real MeasurableEq instance, followed by MeasurableSet.compl from the foundational definition packet above.

```json
{
  "path": "Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean",
  "sha256": "03bdd1fd16c69f61acf8ae50d684f54c9b565d03c6fa880fc338fcbd3bbebadb",
  "bytes": 49519,
  "contexts": [
    {
      "startLine1": 27,
      "endLine1": 28,
      "raw": "open Set Function MeasureTheory\n\n"
    },
    {
      "startLine1": 29,
      "endLine1": 30,
      "raw": "universe uι\n\n"
    },
    {
      "startLine1": 31,
      "endLine1": 32,
      "raw": "variable {α β γ δ δ' : Type*} {ι : Sort uι} {s : Set α}\n\n"
    },
    {
      "startLine1": 46,
      "endLine1": 46,
      "raw": "set_option backward.isDefEq.respectTransparency false in\n"
    },
    {
      "startLine1": 60,
      "endLine1": 60,
      "raw": "section ULift\n"
    },
    {
      "startLine1": 61,
      "endLine1": 62,
      "raw": "variable [MeasurableSpace α]\n\n"
    },
    {
      "startLine1": 74,
      "endLine1": 75,
      "raw": "end ULift\n\n"
    },
    {
      "startLine1": 76,
      "endLine1": 77,
      "raw": "section Nat\n\n"
    },
    {
      "startLine1": 78,
      "endLine1": 79,
      "raw": "variable {mα : MeasurableSpace α}\n\n"
    },
    {
      "startLine1": 123,
      "endLine1": 124,
      "raw": "end Nat\n\n"
    },
    {
      "startLine1": 125,
      "endLine1": 126,
      "raw": "section Quotient\n\n"
    },
    {
      "startLine1": 127,
      "endLine1": 128,
      "raw": "variable [MeasurableSpace α] [MeasurableSpace β]\n\n"
    },
    {
      "startLine1": 180,
      "endLine1": 181,
      "raw": "end Quotient\n\n"
    },
    {
      "startLine1": 182,
      "endLine1": 183,
      "raw": "section Subtype\n\n"
    },
    {
      "startLine1": 188,
      "endLine1": 189,
      "raw": "section\n\n"
    },
    {
      "startLine1": 190,
      "endLine1": 191,
      "raw": "variable [MeasurableSpace α]\n\n"
    },
    {
      "startLine1": 201,
      "endLine1": 202,
      "raw": "end\n\n"
    },
    {
      "startLine1": 203,
      "endLine1": 204,
      "raw": "variable {m : MeasurableSpace α} {mβ : MeasurableSpace β}\n\n"
    },
    {
      "startLine1": 290,
      "endLine1": 291,
      "raw": "end Subtype\n\n"
    },
    {
      "startLine1": 292,
      "endLine1": 293,
      "raw": "section Atoms\n\n"
    },
    {
      "startLine1": 294,
      "endLine1": 295,
      "raw": "variable [MeasurableSpace β]\n\n"
    },
    {
      "startLine1": 365,
      "endLine1": 366,
      "raw": "end Atoms\n\n"
    },
    {
      "startLine1": 367,
      "endLine1": 368,
      "raw": "section Prod\n\n"
    },
    {
      "startLine1": 387,
      "endLine1": 388,
      "raw": "variable {m : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}\n\n"
    },
    {
      "startLine1": 568,
      "endLine1": 569,
      "raw": "end Prod\n\n"
    },
    {
      "startLine1": 570,
      "endLine1": 571,
      "raw": "section Pi\n\n"
    },
    {
      "startLine1": 572,
      "endLine1": 573,
      "raw": "variable {X : δ → Type*} [MeasurableSpace α]\n\n"
    },
    {
      "startLine1": 577,
      "endLine1": 578,
      "raw": "variable [∀ a, MeasurableSpace (X a)] [MeasurableSpace γ]\n\n"
    },
    {
      "startLine1": 691,
      "endLine1": 691,
      "raw": "variable (X) in\n"
    },
    {
      "startLine1": 696,
      "endLine1": 696,
      "raw": "variable (X) in\n"
    },
    {
      "startLine1": 743,
      "endLine1": 744,
      "raw": "variable (X)\n\n"
    },
    {
      "startLine1": 765,
      "endLine1": 766,
      "raw": "end Pi\n\n"
    },
    {
      "startLine1": 772,
      "endLine1": 773,
      "raw": "section TProd\n\n"
    },
    {
      "startLine1": 774,
      "endLine1": 775,
      "raw": "open List\n\n"
    },
    {
      "startLine1": 776,
      "endLine1": 777,
      "raw": "variable {X : δ → Type*} [∀ i, MeasurableSpace (X i)]\n\n"
    },
    {
      "startLine1": 783,
      "endLine1": 783,
      "raw": "set_option backward.isDefEq.respectTransparency false in\n"
    },
    {
      "startLine1": 804,
      "endLine1": 805,
      "raw": "end TProd\n\n"
    },
    {
      "startLine1": 810,
      "endLine1": 811,
      "raw": "section Sum\n\n"
    },
    {
      "startLine1": 820,
      "endLine1": 821,
      "raw": "variable {m : MeasurableSpace α} {mβ : MeasurableSpace β}\n\n"
    },
    {
      "startLine1": 863,
      "endLine1": 864,
      "raw": "end Sum\n\n"
    },
    {
      "startLine1": 869,
      "endLine1": 869,
      "raw": "section prop\n"
    },
    {
      "startLine1": 870,
      "endLine1": 871,
      "raw": "variable [MeasurableSpace α] {p q : α → Prop}\n\n"
    },
    {
      "startLine1": 919,
      "endLine1": 920,
      "raw": "end prop\n\n"
    },
    {
      "startLine1": 932,
      "endLine1": 932,
      "raw": "section Set\n"
    },
    {
      "startLine1": 933,
      "endLine1": 934,
      "raw": "variable [MeasurableSpace β] {f g : β → Set α}\n\n"
    },
    {
      "startLine1": 999,
      "endLine1": 999,
      "raw": "open scoped symmDiff in\n"
    },
    {
      "startLine1": 1005,
      "endLine1": 1005,
      "raw": "open scoped symmDiff in\n"
    },
    {
      "startLine1": 1008,
      "endLine1": 1009,
      "raw": "variable [Countable α]\n\n"
    },
    {
      "startLine1": 1035,
      "endLine1": 1036,
      "raw": "end Set\n\n"
    },
    {
      "startLine1": 1037,
      "endLine1": 1037,
      "raw": "section Finset\n"
    },
    {
      "startLine1": 1038,
      "endLine1": 1039,
      "raw": "variable [MeasurableSpace β] {f g : β → Finset α}\n\n"
    },
    {
      "startLine1": 1073,
      "endLine1": 1074,
      "raw": "section DecidableEq\n\n"
    },
    {
      "startLine1": 1075,
      "endLine1": 1076,
      "raw": "variable [DecidableEq α]\n\n"
    },
    {
      "startLine1": 1098,
      "endLine1": 1098,
      "raw": "open scoped symmDiff in\n"
    },
    {
      "startLine1": 1104,
      "endLine1": 1105,
      "raw": "end DecidableEq\n\n"
    },
    {
      "startLine1": 1106,
      "endLine1": 1107,
      "raw": "variable [Countable α]\n\n"
    },
    {
      "startLine1": 1111,
      "endLine1": 1112,
      "raw": "end Finset\n\n"
    },
    {
      "startLine1": 1113,
      "endLine1": 1114,
      "raw": "section curry\n\n"
    },
    {
      "startLine1": 1115,
      "endLine1": 1116,
      "raw": "variable {ι : Type*}\n\n"
    },
    {
      "startLine1": 1117,
      "endLine1": 1118,
      "raw": "section Function\n\n"
    },
    {
      "startLine1": 1119,
      "endLine1": 1120,
      "raw": "variable {κ X : Type*} [MeasurableSpace X]\n\n"
    },
    {
      "startLine1": 1134,
      "endLine1": 1135,
      "raw": "end Function\n\n"
    },
    {
      "startLine1": 1136,
      "endLine1": 1137,
      "raw": "section Sigma\n\n"
    },
    {
      "startLine1": 1138,
      "endLine1": 1139,
      "raw": "variable {κ : ι → Type*} {X : (i : ι) → κ i → Type*} [∀ i j, MeasurableSpace (X i j)]\n\n"
    },
    {
      "startLine1": 1156,
      "endLine1": 1157,
      "raw": "end Sigma\n\n"
    },
    {
      "startLine1": 1158,
      "endLine1": 1159,
      "raw": "end curry\n\n"
    },
    {
      "startLine1": 1160,
      "endLine1": 1160,
      "raw": "variable (α) in\n"
    }
  ],
  "excerpts": [
    {
      "startLine1": 1150,
      "endLine1": 1180,
      "body": "@[fun_prop]\nlemma measurable_piCurry : Measurable (Equiv.piCurry X) := measurable_sigmaCurry\n\n@[fun_prop]\nlemma measurable_piCurry_symm : Measurable (Equiv.piCurry X).symm := measurable_sigmaUncurry\n\nend Sigma\n\nend curry\n\nvariable (α) in\n/-- Typeclass for a measurable space `α` for which the diagonal of `α × α` is measurable. -/\nclass MeasurableEq [MeasurableSpace α] where\n  measurableSet_diagonal : MeasurableSet (diagonal α)\n\nexport MeasurableEq (measurableSet_diagonal)\n\nattribute [measurability] measurableSet_diagonal\n\ntheorem measurableSet_eq_fun {m : MeasurableSpace α} [MeasurableSpace β] [MeasurableEq β]\n    {f g : α → β} (hf : Measurable f) (hg : Measurable g) : MeasurableSet {x | f x = g x} :=\n  measurableSet_diagonal.preimage (hf.prodMk hg)\n\n@[fun_prop]\ntheorem Measurable.eq {m : MeasurableSpace α} [MeasurableSpace β] [MeasurableEq β]\n    {f g : α → β} (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x = g x :=\n  measurableSet_setOfPred.mp (measurableSet_eq_fun hf hg)\n\ninstance [MeasurableSpace α] [MeasurableEq α] : MeasurableSingletonClass α := by\n  constructor\n  simp_rw [← ofPred_eq_eq_singleton, measurableSet_setOfPred]\n",
      "bodySHA256": "e2159665681f1da6549dd4615f6d406651bf580f48cb401eec20bcb6afdca536"
    }
  ],
  "bindingPath": "C:/game/shao lean/drafts/oq56/unit220/parent-interfaces01/pinned-closure-context01-result.json"
}
```
