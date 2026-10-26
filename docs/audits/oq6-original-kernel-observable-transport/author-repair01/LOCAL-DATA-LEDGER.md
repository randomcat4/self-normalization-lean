# Unit 219 exact repair01 local data and instance ledger

This ledger describes only the new complete 319-LF source bound by CAPTURE-AND-PROP-LEDGER.json. The exact frozen 12-hunk delta is in EXACT-DELTA-GUARD-MAP.json. All 18 header values are recreated with the identical frozen type and value in the proof. No new kernel, law, observation, statistic, moment premise, existential witness or global helper is introduced.

| Value | Exact type | Exact value | Header / proof binding | Header / proof line | Captures |
|---|---|---|---|---|---|
| g | `Ω → ℝ` | `fun o => ∫ y, h o y ∂μ` | let / let | 33 / 85 | Ω, mΩ, μ, h, canonicalRealStructures |
| r | `Ω → Ω → ℝ` | `fun o y => h o y - g o - g y` | let / let | 34 / 86 | Ω, h, g |
| v | `ℝ` | `∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω mΩ mΩ μ μ)` | let / let | 35 / 87 | Ω, mΩ, μ, r, canonicalOriginalProduct |
| rho | `ℝ` | `Real.sqrt v` | let / let | 37 / 89 | v |
| rowIntegrable | `Ω → Prop` | `fun o => Integrable (h o) μ` | let / let | 38 / 90 | Ω, mΩ, μ, h, canonicalRealNorm |
| gLp | `ℝ≥0∞ → Prop` | `fun p => MemLp g p μ` | let / let | 39 / 91 | Ω, mΩ, μ, g, canonicalRealStructures |
| projectionLaw | `Measure ℝ` | `@Measure.map Ω ℝ mΩ (borel ℝ) g μ` | let / let | 40 / 92 | Ω, mΩ, μ, g, canonicalRealBorel |
| pairLaw | `@Measure (Ω × Ω) (mΩ.prod mΩ)` | `@Measure.prod Ω Ω mΩ mΩ μ μ` | let / let | 42 / 94 | Ω, mΩ, μ |
| mJ | `MeasurableSpace (J → Ω)` | `@MeasurableSpace.pi J (fun _ : J => Ω) (fun _ : J => mΩ)` | let / let | 44 / 96 | J, Ω, mΩ |
| mJ₀ | `MeasurableSpace (J → Ω)` | `@MeasurableSpace.pi J (fun _ : J => Ω) (fun _ : J => m₀)` | let / let | 46 / 98 | J, Ω, m₀ |
| P | `@Measure (J → Ω) mJ` | `@Measure.pi J (fun _ : J => Ω) (inferInstance : Fintype J) (fun _ : J => mΩ) (fun _ : J => μ)` | let / let | 48 / 100 | J, FintypeJ, Ω, mΩ, μ, mJ |
| μ₀ | `@Measure Ω m₀` | `μ.trim hm₀` | let / let | 51 / 103 | Ω, mΩ, μ, m₀, hm₀ |
| localReducedInstance | `MeasurableSpace Ω` | `m₀` | letI / let | 52 / 114 | Ω, m₀ |
| g₀ | `Ω → ℝ` | `fun o => ∫ y, h o y ∂μ₀` | let / let | 53 / 116 | Ω, m₀, μ₀, h, canonicalRealStructures |
| r₀ | `Ω → Ω → ℝ` | `fun o y => h o y - g₀ o - g₀ y` | let / let | 54 / 117 | Ω, h, g₀ |
| v₀ | `ℝ` | `∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(μ₀.prod μ₀)` | let / let | 55 / 118 | Ω, m₀, μ₀, r₀, canonicalReducedProduct |
| rho₀ | `ℝ` | `Real.sqrt v₀` | let / let | 56 / 119 | v₀ |
| P₀ | `@Measure (J → Ω) mJ₀` | `Measure.pi (fun _ : J => μ₀)` | let / let | 57 / 120 | J, FintypeJ, Ω, m₀, μ₀, mJ₀ |

rowIntegrable : Ω → Prop and gLp : ℝ≥0∞ → Prop are captured function data, not new assumptions. The header retains letI for the reduced measurable space; the proof uses ordinary let at line114 with the same exact type/value. Original v, projectionLaw, pairLaw and P now explicitly use the original mΩ/product/pi structures in both copies. The typed Fintype J argument is the same supplied caller instance.

The two retained local class proofs use ordinary let: reducedProbability : IsProbabilityMeasure μ₀ := hμ₀prob at line115; mappedSigmaFinite : ∀ _ : J, SigmaFinite (@Measure.map Ω Ω mΩ m₀ id μ) := fun _ => by rw [← hμmap]; infer_instance at lines287–291. They are derived Props, not new model premises.

The new hsub at lines243–244 has exact type Integrable (fun y : Ω => h o y - g₀ o) μ₀ and exact value ho.sub hconst. It captures only the bound good row o, its derived row integrability ho, the integrable constant hconst, h, g₀ and the reduced law/space/canonical real structures. It is discharged inside the existing AE canonicality proof. CAPTURE-AND-PROP-LEDGER.json supplies all 38 named local Prop types, exact source value ranges/captures and all 22 conclusion routes. These author ledger counts do not predict generated declaration ownership.

The explicit map_prod_map application at lines180–182 fixes α/γ at original mΩ, β/δ at reduced m₀, both maps at id, both factors at original μ and SFinite at @SFinite Ω mΩ μ, derived from original probability. The explicit measurable_pi_iff application at lines282–283 fixes source mJ, target family fun _ : J => m₀ and the tuple identity. The complete 15- and 6-slot typed argument maps are in the JSON ledger.

The following unnamed function/data terms appear as arguments or lambda bodies. Their exact values are fixed by the source; none is a new arbitrary function:

- `id : Omega -> Omega`, `id : (Omega*Omega)->(Omega*Omega)`, and `id : (J->Omega)->(J->Omega)`; canonical identities, with domain/target sigma algebras explicitly specified in each use. They capture only the indicated types.
- `Prod.fst` and `Prod.snd : (Omega*Omega)->Omega`; canonical coordinate maps. In hidPair their source structure is explicitly mOmega.prod mOmega; in reduced measure-preserving uses it is m0.prod m0.
- `Prod.map (id : Omega->Omega) (id : Omega->Omega)` and `fun xi j => (id : Omega->Omega) (xi j)`; canonical pair/tuple identities, definitionally the corresponding id. They capture Omega and J as appropriate, with no inverse or separation hypothesis.
- Coordinate measurable-structure families `fun _ : J => mOmega` and `fun _ : J => m0`, and constant type family `fun _ : J => Omega`; these are the frozen pi values. Original/reduced/mapped measure families are exactly `fun _ : J => mu`, `fun _ : J => mu0`, and `fun _ : J => @Measure.map Omega Omega mOmega m0 id mu`. The map family supplied to pi_map_pi is exactly `fun _ : J => (id : Omega -> Omega)`.
- Kernel uncurry `fun t : Omega*Omega => h t.1 t.2`, its fixed sections `h o`, and residual uncurry `fun t => r0 t.1 t.2`; all capture the already frozen h or r0 and, for a section, the bound o. Fubini's implicit `Function.uncurry h` has this exact kernel value.
- Projection squares `fun o => g0 o^2` and `fun o => g o^2`, and residual squares `fun t => r0 t.1 t.2^2` / `fun t => r t.1 t.2^2`; all use natural exponent two and canonical real operations. The scalar map in congrArg is exactly `fun z : Real => z^2`.
- Lifted projections `g0 ∘ Prod.fst` and `g0 ∘ Prod.snd` mean exactly `fun t => g0 t.1` and `fun t => g0 t.2`. The residual difference is exactly `fun t => h t.1 t.2 - g0 t.1 - g0 t.2`.
- For canonicality, `fun _ : Omega => g0 o` is the constant section depending on the bound o. The integrable subtraction functions are exactly `fun y => h o y - g0 o` and `fun y => h o y - g0 o - g0 y`. Their integral decompositions are used only after section integrability is available.
- Projection-law composition `g0 ∘ id` means exactly `fun o => g0 (id o)`. The statistic-law composition `T ∘ id` means exactly `fun xi => T (id xi)`. These are definitionally g0 and T, respectively; the named original g is related by the proved pointwise equality.
- The a.e. equality proofs use only `Filter.Eventually.of_forall` on already proved pointwise equalities. They do not choose representatives, exceptional sets, sample observations or new kernels.

All implicitly captured real topology/Borel/norm/real normed-space/completeness/second-countability structures are canonical. ENNReal structures are canonical. Original mOmega, explicit m0 and their canonical product/pi structures are the only observation measurable structures. Original probability is the frozen caller Prop. Reduced probability, finite/SFinite coordinate/product instances, and the mapped SigmaFinite family are derived Props. `classical` locally permits the standard `Classical.propDecidable` data for proof propositions, including the integrability contradiction; it does not add Nonempty Omega, an observation selector or any new axiom beyond the permitted whitelist. There is no newly chosen type, law, scalar code, observable, density or existential witness.
