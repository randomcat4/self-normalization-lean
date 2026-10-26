# RhoWeightedDeletionMoments — exact qualified interface

Originalp51 S13 absD/J capped-deletion ingredients and explicit-window rho/rho² S6/S8 orders. Actual originalh, originaln denominators, full normalizer m^n and inherited extra m^-1 partial-tilt factor are retained. All11 public leaves include genuine weightedL1. rho=0 and x=0 remain included without divisionbyrho. S14 combined fees, generalS15/S11/DC/fullOQ56 remainOPEN; originalShaoZhouattribution/p54repairs retained.

Source SHA256 c5daf6b99c5604801dc2571f7dac902472bbbcd1c3960e1b813b8745303edc59; 33183B /687LF. FirstoriginalO 9fedf9b3263e38caa68c7218bb0bfce3625e3063ff3c9f55410a048288900744 /2725248B.

Complete frozen heads:

```lean
private theorem scaled_centered_kernel_model
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o, g o ∂μ) = 0)
    (hgsecond : (∫ o, g o ^ 2 ∂μ) = 1)
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun z : Ω × Ω => r z.1 z.2))
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ))
    (hrsymm : ∀ o y, r o y = r y o)
    (hrcan : ∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    let k : Ω → Ω → ℝ := fun o y => g o + g y + t * r o y
    let gk : Ω → ℝ := fun o => ∫ y, k o y ∂μ
    let rk : Ω → Ω → ℝ := fun o y => k o y - gk o - gk y
    let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
    let vk : ℝ := ∫ z : Ω × Ω, rk z.1 z.2 ^ 2 ∂(μ.prod μ)
    Measurable (fun z : Ω × Ω => k z.1 z.2) ∧
      MemLp (fun z : Ω × Ω => k z.1 z.2) 2 (μ.prod μ) ∧
      (∀ o y, k o y = k y o) ∧
      (∫ z : Ω × Ω, k z.1 z.2 ∂(μ.prod μ)) = 0 ∧
      (∫ o, (∫ y, k o y ∂μ) ^ 2 ∂μ) = 1 ∧
      gk =ᵐ[μ] g ∧
      (∀ o y, gk o = g o → gk y = g y → rk o y = t * r o y) ∧
      (fun z : Ω × Ω => rk z.1 z.2) =ᵐ[μ.prod μ]
        (fun z : Ω × Ω => t * r z.1 z.2) ∧
      vk = t ^ 2 * v ∧
      Real.sqrt vk = t * Real.sqrt v


private theorem remove_positive_scale_offset
    (A B ρr : ℝ) (p : ℕ)
    (hscaled : ∀ t : ℝ, 0 < t →
      t ^ p * A ≤ B * (1 + t * ρr) ^ p) :
    A ≤ B * ρr ^ p


theorem actual_quadratic_rho_weighted_deletion_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 4 ≤ n)
    (x : ℝ) (hx : 0 ≤ x)
    (hwindow : x ≤ Real.sqrt (n : ℝ) /
      (2 * Real.exp (1 / 2 : ℝ))) :
    let C : ℝ := Real.exp (1 / 2 : ℝ)
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
    let ρr : ℝ := Real.sqrt v
    let a : ℝ := x / Real.sqrt (n : ℝ)
    let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
    let w : Ω → ℝ := fun o => Real.exp (φ o)
    let m : ℝ := ∫ o, w o ∂μ
    let L : Ω → ℝ := fun o => w o / m
    let ρ : Measure Ω :=
      μ.withDensity (fun o => ENNReal.ofReal (L o))
    let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let I : ℝ := m ^ n
    let R : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Real.exp (∑ j ∈ Finset.univ.erase i, φ (ξ j)) / I
    let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      min |a * g (ξ i)| 1
    let e : (Fin n → Ω) → Fin n → Fin n → ℝ :=
      fun ξ j k => r (ξ j) (ξ k)
    let F : (Fin n → Ω) → ℝ := fun ξ =>
      Shao.OQ5.P35.unorderedPairSum (e ξ)
    let Fdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Shao.OQ5.P35.unorderedPairSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i)
    let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
      Shao.OQ6.ResidualDeletion.rowSum (e ξ) j
    let ψdel : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ i j =>
      Shao.OQ6.ResidualDeletion.rowSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i) j
    let Λsq : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j : Fin n, ψ ξ j ^ 2
    let Λdelsq : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      ∑ j : Fin n, ψdel ξ i j ^ 2
    let u : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
      ψ ξ j / ((n : ℝ) - 2)
    let udel : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ i j =>
      ψdel ξ i j / ((n : ℝ) - 2)
    let J : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, u ξ j ^ 2
    let Jdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      ∑ j : Fin n, udel ξ i j ^ 2
    let D₁ : (Fin n → Ω) → ℝ := fun ξ =>
      F ξ / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    let D₁del : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Fdel ξ i / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    let cross : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      ∑ j ∈ Finset.univ.erase i,
        2 * r (ξ i) (ξ j) * (ψ ξ j - r (ξ i) (ξ j))
    (∀ ξ i, Λsq ξ - Λdelsq ξ i = ψ ξ i ^ 2 + cross ξ i +
      ∑ j ∈ Finset.univ.erase i, r (ξ i) (ξ j) ^ 2) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i|) P₀) ∧
      (∑ i : Fin n,
        ∫ ξ, R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i| ∂P₀) ≤
          4 * Real.sqrt 2 * C * ρr * (1 + x) ^ 2 /
            Real.sqrt (n : ℝ) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => R ξ i * cap ξ i * |cross ξ i|) P₀) ∧
      (∑ i : Fin n,
        ∫ ξ, R ξ i * cap ξ i * |cross ξ i| ∂P₀) ≤
          16 * C ^ 2 * ρr ^ 2 * (n : ℝ) ^ 2 * x * (1 + x) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => R ξ i * cap ξ i * |Λsq ξ - Λdelsq ξ i|) P₀) ∧
      (∑ i : Fin n,
        ∫ ξ, R ξ i * cap ξ i * |Λsq ξ - Λdelsq ξ i| ∂P₀) ≤
          24 * C ^ 2 * ρr ^ 2 * (n : ℝ) ^ 2 * (1 + x) ^ 2 ∧
      (∀ i : Fin n, Integrable
        (fun ξ => R ξ i * cap ξ i * abs (abs (D₁ ξ) - abs (D₁del ξ i))) P₀) ∧
      (∑ i : Fin n,
        ∫ ξ, R ξ i * cap ξ i * abs (abs (D₁ ξ) - abs (D₁del ξ i)) ∂P₀) ≤
          4 * Real.sqrt 2 * C * ρr * (1 + x) ^ 2 /
            Real.sqrt (n : ℝ) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => R ξ i * cap ξ i * |J ξ - Jdel ξ i|) P₀) ∧
      (∑ i : Fin n,
        ∫ ξ, R ξ i * cap ξ i * |J ξ - Jdel ξ i| ∂P₀) ≤
          96 * C ^ 2 * ρr ^ 2 * (1 + x) ^ 2 

```

Validation: same independent complete683LF source/proof review plus all4 affected frozen repair contexts; completeall4 actualTYPE826LF and0 requiredVALUE; native02 andsameFIRSTO importonly allowner recursiveAX audit actualRC0/0. Everyowner hasonlypropext/Classical.choice/Quot.sound. Native01 RC1/5errors/10warnings/noobject retained. Native02 13source/stylewarnings plusstanding134Bstderr; auditstanding134Bstderr. Strictwrappersfalse/FIRSTEMPTYnull(notreturnedfield), mixedsavedSHA+currentbytes/ns/newfullSHA modes retained honestly. No acceptedoldproducer orleafAX replay, no cleanuprecompile, no merge.
