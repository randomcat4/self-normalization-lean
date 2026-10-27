# Unit221 exact repair01 data/capture/proposition ledger

Status: complete exact frozen repair candidate; same independent affected review and authorized parent machine gates still pending. No new non-Prop value, helper, instance, lambda, predicate, binder, assumption, data family or existential witness is introduced.

All45 frozen header values below retain their complete types/values/captures. Their source lines are derived from the actual unchanged head, while all body locators are searched only after the theorem proof delimiter.

- **original.f**, source line 27. Type `ℕ → Ω → ℝ`; captures Ω.

  ```lean
  let f : ℕ → Ω → ℝ := fun (_k : ℕ) (_o : Ω) => (0 : ℝ)
  ```

- **original.g**, source line 28. Type `Ω → ℝ`; captures Ω, mΩ, μ, h.

  ```lean
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  ```

- **original.r**, source line 29. Type `Ω → Ω → ℝ`; captures Ω, h, g.

  ```lean
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  ```

- **original.v**, source line 30. Type `ℝ`; captures Ω, mΩ, μ, r.

  ```lean
  let v : ℝ :=
        ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω mΩ mΩ μ μ)
  ```

- **original.rho**, source line 32. Type `ℝ`; captures v.

  ```lean
  let rho : ℝ := Real.sqrt v
  ```

- **original.rowIntegrable**, source line 33. Type `Ω → Prop`; captures Ω, mΩ, μ, h.

  ```lean
  let rowIntegrable : Ω → Prop := fun o => Integrable (h o) μ
  ```

- **original.gLp**, source line 34. Type `ℝ≥0∞ → Prop`; captures Ω, mΩ, μ, g.

  ```lean
  let gLp : ℝ≥0∞ → Prop := fun p => MemLp g p μ
  ```

- **original.projectionLaw**, source line 35. Type `Measure ℝ`; captures Ω, mΩ, μ, g.

  ```lean
  let projectionLaw : Measure ℝ :=
        @Measure.map Ω ℝ mΩ (borel ℝ) g μ
  ```

- **original.pairLaw**, source line 37. Type `@Measure (Ω × Ω) (mΩ.prod mΩ)`; captures Ω, mΩ, μ.

  ```lean
  let pairLaw : @Measure (Ω × Ω) (mΩ.prod mΩ) :=
        @Measure.prod Ω Ω mΩ mΩ μ μ
  ```

- **reduced.μ₀**, source line 44. Type `@Measure Ω m₀`; captures Ω, mΩ, m₀, μ, hm₀.

  ```lean
  let μ₀ : @Measure Ω m₀ := μ.trim hm₀
  ```

- **reduced.g₀**, source line 46. Type `Ω → ℝ`; captures Ω, m₀, μ₀, h.

  ```lean
  let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
  ```

- **reduced.r₀**, source line 47. Type `Ω → Ω → ℝ`; captures Ω, h, g₀.

  ```lean
  let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
  ```

- **reduced.v₀**, source line 48. Type `ℝ`; captures Ω, m₀, μ₀, r₀.

  ```lean
  let v₀ : ℝ :=
          ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
  ```

- **reduced.rho₀**, source line 50. Type `ℝ`; captures v₀.

  ```lean
  let rho₀ : ℝ := Real.sqrt v₀
  ```

- **finite.mJ**, source line 71. Type `MeasurableSpace (J → Ω)`; captures J, Ω, mΩ.

  ```lean
  let mJ : MeasurableSpace (J → Ω) :=
            @MeasurableSpace.pi J (fun _ : J => Ω) (fun _ : J => mΩ)
  ```

- **finite.mJ₀**, source line 73. Type `MeasurableSpace (J → Ω)`; captures J, Ω, m₀.

  ```lean
  let mJ₀ : MeasurableSpace (J → Ω) :=
            @MeasurableSpace.pi J (fun _ : J => Ω) (fun _ : J => m₀)
  ```

- **finite.P**, source line 75. Type `@Measure (J → Ω) mJ`; captures J, instJ, Ω, mΩ, μ, mJ.

  ```lean
  let P : @Measure (J → Ω) mJ :=
            @Measure.pi J (fun _ : J => Ω) instJ
              (fun _ : J => mΩ) (fun _ : J => μ)
  ```

- **finite.P₀**, source line 78. Type `@Measure (J → Ω) mJ₀`; captures J, instJ, Ω, m₀, μ₀, mJ₀.

  ```lean
  let P₀ : @Measure (J → Ω) mJ₀ :=
            @Measure.pi J (fun _ : J => Ω) instJ
              (fun _ : J => m₀) (fun _ : J => μ₀)
  ```

- **sample.mN**, source line 91. Type `MeasurableSpace (Fin n → Ω)`; captures n, Ω, mΩ.

  ```lean
  let mN : MeasurableSpace (Fin n → Ω) :=
            @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ)
  ```

- **sample.mN₀**, source line 93. Type `MeasurableSpace (Fin n → Ω)`; captures n, Ω, m₀.

  ```lean
  let mN₀ : MeasurableSpace (Fin n → Ω) :=
            @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => m₀)
  ```

- **sample.P**, source line 95. Type `@Measure (Fin n → Ω) mN`; captures n, Ω, mΩ, μ, mN, Fintype (Fin n).

  ```lean
  let P : @Measure (Fin n → Ω) mN :=
            @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
              (fun _ : Fin n => mΩ) (fun _ : Fin n => μ)
  ```

- **sample.P₀**, source line 98. Type `@Measure (Fin n → Ω) mN₀`; captures n, Ω, m₀, μ₀, mN₀, Fintype (Fin n).

  ```lean
  let P₀ : @Measure (Fin n → Ω) mN₀ :=
            @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
              (fun _ : Fin n => m₀) (fun _ : Fin n => μ₀)
  ```

- **sample.N**, source line 101. Type `ℝ`; captures n.

  ```lean
  let N : ℝ := Real.sqrt (n : ℝ)
  ```

- **sample.W**, source line 102. Type `(Fin n → Ω) → ℝ`; captures n, Ω, g.

  ```lean
  let W : (Fin n → Ω) → ℝ := projectionW n g
  ```

- **sample.V**, source line 103. Type `(Fin n → Ω) → ℝ`; captures n, Ω, g.

  ```lean
  let V : (Fin n → Ω) → ℝ := projectionV n g
  ```

- **sample.D**, source line 104. Type `(Fin n → Ω) → ℝ`; captures n, Ω, r.

  ```lean
  let D : (Fin n → Ω) → ℝ := residualStatisticD n r
  ```

- **sample.J**, source line 105. Type `(Fin n → Ω) → ℝ`; captures n, Ω, r.

  ```lean
  let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
  ```

- **sample.Ddel**, source line 106. Type `(Fin n → Ω) → Fin n → ℝ`; captures n, Ω, r.

  ```lean
  let Ddel : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
  ```

- **sample.Jdel**, source line 107. Type `(Fin n → Ω) → Fin n → ℝ`; captures n, Ω, r.

  ```lean
  let Jdel : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
  ```

- **sample.A**, source line 108. Type `(Fin n → Ω) → ℝ`; captures n, Ω, D.

  ```lean
  let A : (Fin n → Ω) → ℝ := fun ξ => |D ξ|
  ```

- **sample.Adel**, source line 109. Type `(Fin n → Ω) → Fin n → ℝ`; captures n, Ω, Ddel.

  ```lean
  let Adel : (Fin n → Ω) → Fin n → ℝ := fun ξ i => |Ddel ξ i|
  ```

- **sample.B1**, source line 110. Type `(Fin n → Ω) → ℝ`; captures n, Ω, r, C0, rho.

  ```lean
  let B1 : (Fin n → Ω) → ℝ := studentizerClipBudget n r C0 rho 1
  ```

- **sample.B1del**, source line 111. Type `(Fin n → Ω) → Fin n → ℝ`; captures n, Ω, r, C0, rho.

  ```lean
  let B1del : (Fin n → Ω) → Fin n → ℝ := studentizerClipBudgetDeleted n r C0 rho 1
  ```

- **sample.s2**, source line 112. Type `(Fin n → Ω) → ℝ`; captures n, Ω, g, r.

  ```lean
  let s2 : (Fin n → Ω) → ℝ := centeredSq n g r
  ```

- **sample.s**, source line 113. Type `(Fin n → Ω) → ℝ`; captures n, Ω, s2.

  ```lean
  let s : (Fin n → Ω) → ℝ := fun ξ => Real.sqrt (s2 ξ)
  ```

- **sample.d**, source line 114. Type `(Fin n → Ω) → ℝ`; captures n, Ω, g, r.

  ```lean
  let d : (Fin n → Ω) → ℝ := centeredDelta n g r
  ```

- **sample.e**, source line 115. Type `(Fin n → Ω) → ℝ`; captures n, Ω, g, r, C0, rho.

  ```lean
  let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r C0 rho 1
  ```

- **sample.Tclip**, source line 116. Type `(Fin n → Ω) → ℝ`; captures n, Ω, g, r, C0, rho.

  ```lean
  let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r C0 rho 1
  ```

- **sample.Tactual**, source line 117. Type `(Fin n → Ω) → ℝ`; captures n, Ω, s, W, D, Classical.propDecidable (s ξ = 0).

  ```lean
  let Tactual : (Fin n → Ω) → ℝ :=
            fun ξ => @ite ℝ (s ξ = 0) (Classical.propDecidable (s ξ = 0))
              0 ((W ξ + D ξ) / s ξ)
  ```

- **sample.cap**, source line 120. Type `(Fin n → Ω) → Fin n → ℝ`; captures n, Ω, g, N, z.

  ```lean
  let cap : (Fin n → Ω) → Fin n → ℝ :=
            fun ξ i => min (|g (ξ i)| / N) (1 / (1 + z))
  ```

- **sample.deletedTest**, source line 122. Type `(Fin n → Ω) → Fin n → ℝ`; captures n, Ω, cap, A, Adel, z, B1, B1del.

  ```lean
  let deletedTest : (Fin n → Ω) → Fin n → ℝ :=
            fun ξ i => cap ξ i * (|A ξ - Adel ξ i| + z * |B1 ξ - B1del ξ i|)
  ```

- **retained.mRet**, source line 145. Type `MeasurableSpace ({j : Fin n // j ≠ i} → Ω)`; captures n, i, Ω, mΩ.

  ```lean
  let mRet : MeasurableSpace ({j : Fin n // j ≠ i} → Ω) :=
              @MeasurableSpace.pi {j : Fin n // j ≠ i}
                (fun _ : {j : Fin n // j ≠ i} => Ω)
                (fun _ : {j : Fin n // j ≠ i} => mΩ)
  ```

- **retained.mRet₀**, source line 149. Type `MeasurableSpace ({j : Fin n // j ≠ i} → Ω)`; captures n, i, Ω, m₀.

  ```lean
  let mRet₀ : MeasurableSpace ({j : Fin n // j ≠ i} → Ω) :=
              @MeasurableSpace.pi {j : Fin n // j ≠ i}
                (fun _ : {j : Fin n // j ≠ i} => Ω)
                (fun _ : {j : Fin n // j ≠ i} => m₀)
  ```

- **retained.PRet**, source line 153. Type `@Measure ({j : Fin n // j ≠ i} → Ω) mRet`; captures n, i, Ω, mΩ, μ, mRet, Fintype {j : Fin n // j ≠ i}.

  ```lean
  let PRet : @Measure ({j : Fin n // j ≠ i} → Ω) mRet :=
              @Measure.pi {j : Fin n // j ≠ i}
                (fun _ : {j : Fin n // j ≠ i} => Ω)
                (inferInstance : Fintype {j : Fin n // j ≠ i})
                (fun _ : {j : Fin n // j ≠ i} => mΩ)
                (fun _ : {j : Fin n // j ≠ i} => μ)
  ```

- **retained.PRet₀**, source line 159. Type `@Measure ({j : Fin n // j ≠ i} → Ω) mRet₀`; captures n, i, Ω, m₀, μ₀, mRet₀, Fintype {j : Fin n // j ≠ i}.

  ```lean
  let PRet₀ : @Measure ({j : Fin n // j ≠ i} → Ω) mRet₀ :=
              @Measure.pi {j : Fin n // j ≠ i}
                (fun _ : {j : Fin n // j ≠ i} => Ω)
                (inferInstance : Fintype {j : Fin n // j ≠ i})
                (fun _ : {j : Fin n // j ≠ i} => m₀)
                (fun _ : {j : Fin n // j ≠ i} => μ₀)
  ```

The body ordinary lets are the SAME five frozen reduced-model values μ0/g0/r0/v0/rho0 and the SAME qualified22023-value packet in a local proposition. Their entire text is unchanged. The two body letI instances are exactly MeasurableSpace Omega:=m0 at actual line202 and IsProbabilityMeasure μ0:=hprob0 at208. The latter is the explicitly authorized219 probability Prop instance. Both prior letI warnings are retained; no linter suppression is added.

The only inserted lines retype FOUR existing local propositions via definitional conversion. No new have helper is added. Complete alias types, environments and exact code:

- **hrho**, source lines 211–211. New presentation: `rho₀ = rho : Prop`. Existing captures: Ω, mΩ, m₀, μ, μ₀, h, g, r, g₀, r₀, v, v₀, rho, rho₀. Additional captures: NONE.

  ```lean
    change rho₀ = rho at hrho
  ```

- **finite.hPmap**, source lines 224–224. New presentation: `P₀ = @Measure.map (J → Ω) (J → Ω) mJ mJ₀ id P : Prop`. Existing captures: Ω, mΩ, m₀, μ, μ₀, J, instJ, mJ, mJ₀, P, P₀. Additional captures: NONE.

  ```lean
      change P₀ = @Measure.map (J → Ω) (J → Ω) mJ mJ₀ id P at hPmap
  ```

- **sample.hPmap**, source lines 247–248. New presentation: `P₀ = @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P : Prop`. Existing captures: Ω, mΩ, m₀, μ, μ₀, n, mN, mN₀, P, P₀. Additional captures: NONE.

  ```lean
      change P₀ =
        @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P at hPmap
  ```

- **retained.hPRetMap**, source lines 393–395. New presentation: `PRet₀ = @Measure.map ({j : Fin n // j ≠ i} → Ω) ({j : Fin n // j ≠ i} → Ω) mRet mRet₀ id PRet : Prop`. Existing captures: Ω, mΩ, m₀, μ, μ₀, n, i, mRet, mRet₀, PRet, PRet₀. Additional captures: NONE.

  ```lean
        change PRet₀ =
          @Measure.map ({j : Fin n // j ≠ i} → Ω)
            ({j : Fin n // j ≠ i} → Ω) mRet mRet₀ id PRet at hPRetMap
  ```

m0/hm0 still come only from218 at exact Nat→Omega→Real family fun _k _o=>0. Literal μ0=μ.trim hm0 precedes reduced letI. Original rowIntegrable/gLp data remain captured under original mOmega/mu. The original total projection/residual values and variance/rho, normalized moments, all-row integrability iff, all-p MemLp iff and AE canonicality are unchanged. No observation selector, filler/default point or new Nonempty/standard-Borel/separation/higher-moment/positive-rho premise occurs.

E still comes ONLY from qualified220 at explicit real z=0, SAME n/C0/rho/reduced model, with proofs0≤0 and0≤1. Its direct captures remain Omega,m0,n,r,C0,rho,i, with original h/mu closures through r/rho. E has no actual-z or deleted-coordinate capture. Actual-z full/sliced measurability is separate. Original n,n-1,n-2 coefficients, signed Ddel/Jdel/B1del, physical s=0/clipped V=0 distinction, continuous min cap and full-sample deletedTest remain exactly frozen.

All inline lambda/predicate data retain their exact provenance: h/r pair functions; projection/residual integrals; original rowIntegrable/gLp families; original/reduced identity maps and pi-space/measure families; arbitrary J/instJ/B/mB/T; zeroV/zeroS sets; physical predicate and both inherited/frozen deciders; six indexed observable slices; retained j≠i subtype; restriction fun j=>ξ j.val; signed triple/map functions; canonical coordinate evaluation through existing measurable_pi_apply. Their full typed captures and source lines are in SOURCE-MAP.json and the exact prior freeze.

Source maps now cover all412 lines once as locator intervals and map all405 unchanged prior lines to their new locations. The complete21 local have inventory includes bullet htriple and hretained. Fun keyword lines use exact Unicode identifier boundaries and exclude identifiers such as hJfun/measurableSet_eq_fun; funext term constructors and the tactic ξ binder are separate. All names remain case-sensitive, including hD versus hd. These are deterministic author metadata corrections, not independent semantic review or kernel evidence.

Qualified218/219/220 source/firstO/TYPE/Q evidence and complete prior405 independent source review are reused by exact bindings. The same independent reviewer must cover the four Prop conversions and all affected joins. No accepted producer/leafAX/proof replay or new API query occurred. p51candidate/p54repairs/external Shao-Zhou attribution and all open CDF/root/fee/atom/reflection/zero-event scope remain; OQ3 stays user-paused.
