# Full local data and instance ledger

All values are transparent constructions from the frozen binders. Source lines refer to OriginalKernelObservableTransport.lean, whose exact current hash is recorded in SOURCE-MAP.json and MANIFEST.json. All 18 header values and their complete original/reduced types/values are copied verbatim in the parent freeze and in SOURCE-MAP.json. They are recreated in the proof with identical definitions, not changed mathematical data.

| Proof-local value | Type | Exact value / captures | Lines |
|---|---|---|---|
| g | Omega -> Real | `fun o => integral y, h o y dmu`; original mOmega/mu/h/canonical real structures | 80 |
| r | Omega -> Omega -> Real | `fun o y => h o y - g o - g y`; h/g | 81 |
| v | Real | Original integral of `r(t.1,t.2)^2` under `mu.prod mu`; original mOmega/mu/r | 82 |
| rho | Real | `Real.sqrt v`; v | 83 |
| rowIntegrable | Omega -> Prop | `fun o => Integrable (h o) mu`; ORIGINAL measure/space and h. This is Prop-valued function DATA, not an assumption | 84 |
| gLp | ENNReal -> Prop | `fun p => MemLp g p mu`; ORIGINAL measure/space and g. Prop-valued function DATA, not a stronger moment premise | 85 |
| projectionLaw | Measure Real | `mu.map g`; original domain structure, canonical real Borel target | 86 |
| pairLaw | @Measure (Omega * Omega) (mOmega.prod mOmega) | `mu.prod mu`; original mu/mOmega | 87 |
| mJ | MeasurableSpace (J -> Omega) | `@MeasurableSpace.pi J (fun _ => Omega) (fun _ => mOmega)`; J/Omega/mOmega | 88-89 |
| mJ0 | MeasurableSpace (J -> Omega) | Same exact pi instance with m0; J/Omega/m0 | 90-91 |
| P | @Measure (J -> Omega) mJ | `Measure.pi (fun _ : J => mu)`; ORIGINAL coordinate space, mu, supplied Fintype J | 92 |
| mu0 | @Measure Omega m0 | `mu.trim hm0`; original mu/mOmega and structural m0/hm0 | 93 |
| local measurable-space instance | MeasurableSpace Omega | EXACT m0; original values above remain typed at mOmega. Non-Prop instance, so the frozen letI spelling is retained | 104 |
| g0 | Omega -> Real | `fun o => integral y, h o y dmu0`; reduced m0/mu0/h/canonical real structures | 106 |
| r0 | Omega -> Omega -> Real | `fun o y => h o y - g0 o - g0 y`; h/g0 | 107 |
| v0 | Real | Reduced integral of `r0(t.1,t.2)^2` under `mu0.prod mu0`; m0/mu0/r0 | 108 |
| rho0 | Real | `Real.sqrt v0`; v0 | 109 |
| P0 | @Measure (J -> Omega) mJ0 | `Measure.pi (fun _ : J => mu0)`; reduced coordinate space, mu0, supplied Fintype J | 110 |

There are two further named proof-local class PROOFS, using ordinary let as recommended for Prop classes by the actual unit 218 linter diagnostic. `reducedProbability : IsProbabilityMeasure mu0` has exact value hmu0prob and captures original probability, hm0 and trim equality on univ (line 105). `mappedSigmaFinite : forall _ : J, SigmaFinite (@Measure.map Omega Omega mOmega m0 id mu)` has exact value `fun _ => by rw [<- hmuMap]; infer_instance`; it captures hmuMap and reducedProbability and chooses no member of J (267-271). These types are propositions; their proof values add no model premise. They differ from the data families rowIntegrable/gLp, whose values are functions returning propositions themselves.

The complete named derived-Prop ledger, including full types and source value ranges/captures, is the derivedProofLocals array in SOURCE-MAP.json. No hypothesis is obtained from a hidden external result. Its important local assumptions are only introductions from implication/iff/forall goals: o/y:Omega; j:J; p:ENNReal; the caller T:(J->Omega)->Real; hT:Measurable[mJ0,borel Real] T; ho in the respective row-integrability implication or Fubini-good set; hp in the two Lp directions; and hnot:Not (Integrable (fun o => g0 o^2) mu0) under proof by contradiction. All are scoped to their displayed source blocks and are discharged.

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
