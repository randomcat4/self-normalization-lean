# Unit221 source data and capture ledger

Status: same-author complete source candidate; exact parent freeze preserved; no independent review or Lean check.

The full source is OriginalCountablyGeneratedModel.lean. SOURCE-MAP.json maps its complete declaration/proof sections, all45 header typed values, inline data/predicates/lambdas, local instances and inherited producer applications. The parent candidate-data and original source bindings remain exact.

Every header type/value/capture below is copied losslessly from the frozen record; source line numbers identify the current source occurrence.

- **original.f**, source line 27. Type: `ℕ → Ω → ℝ`. Captures: Ω.

  ```lean
  let f : ℕ → Ω → ℝ := fun (_k : ℕ) (_o : Ω) => (0 : ℝ)
  ```

- **original.g**, source line 28. Type: `Ω → ℝ`. Captures: Ω, mΩ, μ, h.

  ```lean
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  ```

- **original.r**, source line 29. Type: `Ω → Ω → ℝ`. Captures: Ω, h, g.

  ```lean
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  ```

- **original.v**, source line 30. Type: `ℝ`. Captures: Ω, mΩ, μ, r.

  ```lean
  let v : ℝ :=
        ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω mΩ mΩ μ μ)
  ```

- **original.rho**, source line 32. Type: `ℝ`. Captures: v.

  ```lean
  let rho : ℝ := Real.sqrt v
  ```

- **original.rowIntegrable**, source line 33. Type: `Ω → Prop`. Captures: Ω, mΩ, μ, h.

  ```lean
  let rowIntegrable : Ω → Prop := fun o => Integrable (h o) μ
  ```

- **original.gLp**, source line 34. Type: `ℝ≥0∞ → Prop`. Captures: Ω, mΩ, μ, g.

  ```lean
  let gLp : ℝ≥0∞ → Prop := fun p => MemLp g p μ
  ```

- **original.projectionLaw**, source line 35. Type: `Measure ℝ`. Captures: Ω, mΩ, μ, g.

  ```lean
  let projectionLaw : Measure ℝ :=
        @Measure.map Ω ℝ mΩ (borel ℝ) g μ
  ```

- **original.pairLaw**, source line 37. Type: `@Measure (Ω × Ω) (mΩ.prod mΩ)`. Captures: Ω, mΩ, μ.

  ```lean
  let pairLaw : @Measure (Ω × Ω) (mΩ.prod mΩ) :=
        @Measure.prod Ω Ω mΩ mΩ μ μ
  ```

- **reduced.μ₀**, source line 44. Type: `@Measure Ω m₀`. Captures: Ω, mΩ, m₀, μ, hm₀.

  ```lean
  let μ₀ : @Measure Ω m₀ := μ.trim hm₀
  ```

- **reduced.g₀**, source line 46. Type: `Ω → ℝ`. Captures: Ω, m₀, μ₀, h.

  ```lean
  let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
  ```

- **reduced.r₀**, source line 47. Type: `Ω → Ω → ℝ`. Captures: Ω, h, g₀.

  ```lean
  let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
  ```

- **reduced.v₀**, source line 48. Type: `ℝ`. Captures: Ω, m₀, μ₀, r₀.

  ```lean
  let v₀ : ℝ :=
          ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
  ```

- **reduced.rho₀**, source line 50. Type: `ℝ`. Captures: v₀.

  ```lean
  let rho₀ : ℝ := Real.sqrt v₀
  ```

- **finite.mJ**, source line 71. Type: `MeasurableSpace (J → Ω)`. Captures: J, Ω, mΩ.

  ```lean
  let mJ : MeasurableSpace (J → Ω) :=
            @MeasurableSpace.pi J (fun _ : J => Ω) (fun _ : J => mΩ)
  ```

- **finite.mJ₀**, source line 73. Type: `MeasurableSpace (J → Ω)`. Captures: J, Ω, m₀.

  ```lean
  let mJ₀ : MeasurableSpace (J → Ω) :=
            @MeasurableSpace.pi J (fun _ : J => Ω) (fun _ : J => m₀)
  ```

- **finite.P**, source line 75. Type: `@Measure (J → Ω) mJ`. Captures: J, instJ, Ω, mΩ, μ, mJ.

  ```lean
  let P : @Measure (J → Ω) mJ :=
            @Measure.pi J (fun _ : J => Ω) instJ
              (fun _ : J => mΩ) (fun _ : J => μ)
  ```

- **finite.P₀**, source line 78. Type: `@Measure (J → Ω) mJ₀`. Captures: J, instJ, Ω, m₀, μ₀, mJ₀.

  ```lean
  let P₀ : @Measure (J → Ω) mJ₀ :=
            @Measure.pi J (fun _ : J => Ω) instJ
              (fun _ : J => m₀) (fun _ : J => μ₀)
  ```

- **sample.mN**, source line 91. Type: `MeasurableSpace (Fin n → Ω)`. Captures: n, Ω, mΩ.

  ```lean
  let mN : MeasurableSpace (Fin n → Ω) :=
            @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ)
  ```

- **sample.mN₀**, source line 93. Type: `MeasurableSpace (Fin n → Ω)`. Captures: n, Ω, m₀.

  ```lean
  let mN₀ : MeasurableSpace (Fin n → Ω) :=
            @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => m₀)
  ```

- **sample.P**, source line 95. Type: `@Measure (Fin n → Ω) mN`. Captures: n, Ω, mΩ, μ, mN, Fintype (Fin n).

  ```lean
  let P : @Measure (Fin n → Ω) mN :=
            @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
              (fun _ : Fin n => mΩ) (fun _ : Fin n => μ)
  ```

- **sample.P₀**, source line 98. Type: `@Measure (Fin n → Ω) mN₀`. Captures: n, Ω, m₀, μ₀, mN₀, Fintype (Fin n).

  ```lean
  let P₀ : @Measure (Fin n → Ω) mN₀ :=
            @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
              (fun _ : Fin n => m₀) (fun _ : Fin n => μ₀)
  ```

- **sample.N**, source line 101. Type: `ℝ`. Captures: n.

  ```lean
  let N : ℝ := Real.sqrt (n : ℝ)
  ```

- **sample.W**, source line 102. Type: `(Fin n → Ω) → ℝ`. Captures: n, Ω, g.

  ```lean
  let W : (Fin n → Ω) → ℝ := projectionW n g
  ```

- **sample.V**, source line 103. Type: `(Fin n → Ω) → ℝ`. Captures: n, Ω, g.

  ```lean
  let V : (Fin n → Ω) → ℝ := projectionV n g
  ```

- **sample.D**, source line 104. Type: `(Fin n → Ω) → ℝ`. Captures: n, Ω, r.

  ```lean
  let D : (Fin n → Ω) → ℝ := residualStatisticD n r
  ```

- **sample.J**, source line 105. Type: `(Fin n → Ω) → ℝ`. Captures: n, Ω, r.

  ```lean
  let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
  ```

- **sample.Ddel**, source line 106. Type: `(Fin n → Ω) → Fin n → ℝ`. Captures: n, Ω, r.

  ```lean
  let Ddel : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
  ```

- **sample.Jdel**, source line 107. Type: `(Fin n → Ω) → Fin n → ℝ`. Captures: n, Ω, r.

  ```lean
  let Jdel : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
  ```

- **sample.A**, source line 108. Type: `(Fin n → Ω) → ℝ`. Captures: n, Ω, D.

  ```lean
  let A : (Fin n → Ω) → ℝ := fun ξ => |D ξ|
  ```

- **sample.Adel**, source line 109. Type: `(Fin n → Ω) → Fin n → ℝ`. Captures: n, Ω, Ddel.

  ```lean
  let Adel : (Fin n → Ω) → Fin n → ℝ := fun ξ i => |Ddel ξ i|
  ```

- **sample.B1**, source line 110. Type: `(Fin n → Ω) → ℝ`. Captures: n, Ω, r, C0, rho.

  ```lean
  let B1 : (Fin n → Ω) → ℝ := studentizerClipBudget n r C0 rho 1
  ```

- **sample.B1del**, source line 111. Type: `(Fin n → Ω) → Fin n → ℝ`. Captures: n, Ω, r, C0, rho.

  ```lean
  let B1del : (Fin n → Ω) → Fin n → ℝ := studentizerClipBudgetDeleted n r C0 rho 1
  ```

- **sample.s2**, source line 112. Type: `(Fin n → Ω) → ℝ`. Captures: n, Ω, g, r.

  ```lean
  let s2 : (Fin n → Ω) → ℝ := centeredSq n g r
  ```

- **sample.s**, source line 113. Type: `(Fin n → Ω) → ℝ`. Captures: n, Ω, s2.

  ```lean
  let s : (Fin n → Ω) → ℝ := fun ξ => Real.sqrt (s2 ξ)
  ```

- **sample.d**, source line 114. Type: `(Fin n → Ω) → ℝ`. Captures: n, Ω, g, r.

  ```lean
  let d : (Fin n → Ω) → ℝ := centeredDelta n g r
  ```

- **sample.e**, source line 115. Type: `(Fin n → Ω) → ℝ`. Captures: n, Ω, g, r, C0, rho.

  ```lean
  let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r C0 rho 1
  ```

- **sample.Tclip**, source line 116. Type: `(Fin n → Ω) → ℝ`. Captures: n, Ω, g, r, C0, rho.

  ```lean
  let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r C0 rho 1
  ```

- **sample.Tactual**, source line 117. Type: `(Fin n → Ω) → ℝ`. Captures: n, Ω, s, W, D, Classical.propDecidable (s ξ = 0).

  ```lean
  let Tactual : (Fin n → Ω) → ℝ :=
            fun ξ => @ite ℝ (s ξ = 0) (Classical.propDecidable (s ξ = 0))
              0 ((W ξ + D ξ) / s ξ)
  ```

- **sample.cap**, source line 120. Type: `(Fin n → Ω) → Fin n → ℝ`. Captures: n, Ω, g, N, z.

  ```lean
  let cap : (Fin n → Ω) → Fin n → ℝ :=
            fun ξ i => min (|g (ξ i)| / N) (1 / (1 + z))
  ```

- **sample.deletedTest**, source line 122. Type: `(Fin n → Ω) → Fin n → ℝ`. Captures: n, Ω, cap, A, Adel, z, B1, B1del.

  ```lean
  let deletedTest : (Fin n → Ω) → Fin n → ℝ :=
            fun ξ i => cap ξ i * (|A ξ - Adel ξ i| + z * |B1 ξ - B1del ξ i|)
  ```

- **retained.mRet**, source line 145. Type: `MeasurableSpace ({j : Fin n // j ≠ i} → Ω)`. Captures: n, i, Ω, mΩ.

  ```lean
  let mRet : MeasurableSpace ({j : Fin n // j ≠ i} → Ω) :=
              @MeasurableSpace.pi {j : Fin n // j ≠ i}
                (fun _ : {j : Fin n // j ≠ i} => Ω)
                (fun _ : {j : Fin n // j ≠ i} => mΩ)
  ```

- **retained.mRet₀**, source line 149. Type: `MeasurableSpace ({j : Fin n // j ≠ i} → Ω)`. Captures: n, i, Ω, m₀.

  ```lean
  let mRet₀ : MeasurableSpace ({j : Fin n // j ≠ i} → Ω) :=
              @MeasurableSpace.pi {j : Fin n // j ≠ i}
                (fun _ : {j : Fin n // j ≠ i} => Ω)
                (fun _ : {j : Fin n // j ≠ i} => m₀)
  ```

- **retained.PRet**, source line 153. Type: `@Measure ({j : Fin n // j ≠ i} → Ω) mRet`. Captures: n, i, Ω, mΩ, μ, mRet, Fintype {j : Fin n // j ≠ i}.

  ```lean
  let PRet : @Measure ({j : Fin n // j ≠ i} → Ω) mRet :=
              @Measure.pi {j : Fin n // j ≠ i}
                (fun _ : {j : Fin n // j ≠ i} => Ω)
                (inferInstance : Fintype {j : Fin n // j ≠ i})
                (fun _ : {j : Fin n // j ≠ i} => mΩ)
                (fun _ : {j : Fin n // j ≠ i} => μ)
  ```

- **retained.PRet₀**, source line 159. Type: `@Measure ({j : Fin n // j ≠ i} → Ω) mRet₀`. Captures: n, i, Ω, m₀, μ₀, mRet₀, Fintype {j : Fin n // j ≠ i}.

  ```lean
  let PRet₀ : @Measure ({j : Fin n // j ≠ i} → Ω) mRet₀ :=
              @Measure.pi {j : Fin n // j ≠ i}
                (fun _ : {j : Fin n // j ≠ i} => Ω)
                (inferInstance : Fintype {j : Fin n // j ≠ i})
                (fun _ : {j : Fin n // j ≠ i} => m₀)
                (fun _ : {j : Fin n // j ≠ i} => μ₀)
  ```

The only body ordinary lets instantiate the same frozen μ0,g0,r0,v0,rho0 values. The body letI measurable space is the frozen m0 instance. Its only further body letI is the explicitly authorized Prop-valued IsProbabilityMeasure μ0 witness hprob0 from219 at Fin0. No new measurable structure, law, global helper or observation selector is introduced. The authorized CountablyGenerated proof instance is not needed as a local instance; its exact proof is returned.

The23-let packet used in the actual-z local Prop change is the exact qualified220 packet, instantiated at reduced μ0/m0 with g0/r0/v0/rho0. Its data are producer/frozen values, not additional choices. Rewriting g0=g,r0=r,rho0=rho leaves the ORIGINAL observables. The inherited physical conditional has Real.decidableEq, while the theorem head has Classical.propDecidable; hphysicalSame proves equality pointwise under the SAME s=0 predicate without changing either guard or branches.

m0/hm0 come only from qualified218 at f(k,o)=0. The zero family has type Nat→Omega→Real and no observation capture. Fin0 is the exact authorized base index; its canonical Fintype is used only in219 specialization. All J/n/retained product data remain the explicitly frozen pi/map/product values with their original/reduced spaces.

E comes ONLY from qualified220 at explicit real z=0, proofs0≤0 and0≤1, the SAME n,C0,h/mu0 and reduced normalization. Rewriting r0/rho0 identifies its factor equation with literal original Ddel/Jdel/B1del. E does not depend on actual z or ξ i, no filler/default observation enters, and no global E family is selected. Its direct captures are Omega,m0,n,r,C0,rho,i with original h/mu through r/rho. The actual-z packet supplies cap/deletedTest and all other z-dependent measurability, while its existential E is not extracted.

Original rowIntegrable and gLp are introduced before reduced letI; their Prop-valued DATA meanings remain original mOmega/mu. Every exponent transfer is an iff. AE canonicality stays AE; no pointwise canonicality, row-integrability or extra moment premise is inserted.

Typed inline data/predicate inventory: kernel h pair lambda; original/reduced projection integrals; original/reduced residual square integrals; rowIntegrable/gLp; identity Ω/pair/arbitrary finite/full/retained maps; exact V=0 and s=0 sets; physical s=0 predicate and explicit deciders; six indexed cap/Ddel/Jdel/Adel/B1del/deletedTest functions; retained j≠i predicate; restriction fun j=>ξ j.val; signed triple and its map lambda; arbitrary target B,mB,T; all explicit pi-family type/measurable-space/measure lambdas. The exact types/values/captures are in the frozen record and SOURCE-MAP.json.

Canonical coordinate evaluations fun ξ=>ξ j appear only through existing measurable_pi_apply in local Prop proofs of measurable frozen identity maps. Their typed generic/full/retained forms and captures are listed in SOURCE-MAP.json, exactly following219 source/API; no additional helper or selected observable is defined. Function extensionality/case-split lambdas construct Prop proofs only. Triple Borel conversion uses the existing right-associated real product structure supplied by220 and BorelSpace.measurable_eq.

No non-Prop data outside the frozen header/inline data, exact qualified producer witnesses, canonical given API/instance data and specifically approved Fin0/zero specialization is introduced. All other local have bindings are derived propositions. No further API request is identified; future elaboration must still check instance/let matching.

Source scope remains p51 repair candidate with p54 p-moment/strict-margin/compact-boundary fixes and external Shao-Zhou attribution. No S11/S27/generalS15/DC/CDF, fee-limit, atom/reflection/zero-event-payment or full-root closure is asserted.

Lexical inventory is case-sensitive. SOURCE-MAP.json lists exact fun keyword lines using Unicode identifier boundaries, excluding names ending in fun such as hJfun/measurableSet_eq_fun. funext term constructors and the separate tactic binder ξ:Fin n→Omega are inventoried separately. hD and hd remain distinct case-sensitive proof names. No mathematical source byte changed for this metadata refinement.
