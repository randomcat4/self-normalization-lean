# Complete stage 1 data/capture ledger

There is one proposed public theorem and no global definition value, private helper head, existential data output, chosen measurable subspace, factor function, kernel replacement, or proof body. The exact declaration is in CANDIDATE-HEAD.txt and candidate-declarations-data.json. Every item below is a transparent binder or typed header let; no local proof data have been authored.

| Input | Exact type | Origin and restrictions |
|---|---|---|
| Omega | Type u | Arbitrary caller type; no Nonempty or standard-Borel premise. |
| mOmega | MeasurableSpace Omega | Named ambient instance supplied by caller. |
| J | Type v | Arbitrary caller finite-index type. |
| instFintypeJ | Fintype J | Caller instance, computational finite-index data; no chosen enumeration is exported. |
| mu | @Measure Omega mOmega | Original caller probability law; it is never retyped after the instance change. |
| h | Omega -> Omega -> Real | SAME original caller kernel; no a.e. replacement. |
| m0 | MeasurableSpace Omega | Explicit caller data; intended future qualified 218 witness, not chosen in 219. |

Prop binders are original IsProbabilityMeasure mu, hh, hh2, hhsymm, hcenter, hprojectionsecond; structural hm0 and hh0. Their full exact types are in the candidate JSON. There is no law, independence, canonicality, moment or measurability premise hidden in a data definition. The original h-measurability premise hh is retained even though structural hh0 and hm0 also imply it.

| Header value | Exact type | Exact value and captures |
|---|---|---|
| g | Omega -> Real | `fun o => integral y, h o y dmu`; captures Omega/mOmega/mu/h and canonical real Bochner structures. |
| r | Omega -> Omega -> Real | `fun o y => h o y - g o - g y`; captures h/g, literal pointwise residual. |
| v | Real | Original integral of `r(t.1,t.2)^2` under `mu.prod mu`; captures mOmega/mu/r and canonical product/real structures. |
| rho | Real | `Real.sqrt v`; captures v; no positivity premise. |
| rowIntegrable | Omega -> Prop | `fun o => Integrable (h o) mu`; captures the ORIGINAL measure and measurable structure, h and canonical real norm. This is a Prop-valued DATA family, not an assumption. |
| gLp | ENNReal -> Prop | `fun p => MemLp g p mu`; captures ORIGINAL mOmega/mu/g and canonical real topological/enorm structures. Prop-valued DATA family, not an assumption. |
| projectionLaw | Measure Real | `mu.map g` with original domain measurable structure and canonical real Borel target. |
| pairLaw | @Measure (Omega * Omega) (mOmega.prod mOmega) | `mu.prod mu`; original product law. |
| mJ | MeasurableSpace (J -> Omega) | `@MeasurableSpace.pi J (fun _ : J => Omega) (fun _ : J => mOmega)`; captures J/Omega/mOmega. |
| mJ0 | MeasurableSpace (J -> Omega) | Same exact pi instance expression with m0; captures J/Omega/m0. |
| P | @Measure (J -> Omega) mJ | `Measure.pi (fun _ : J => mu)` under ORIGINAL coordinate structure; captures J/FintypeJ/Omega/mOmega/mu/mJ. |
| mu0 | @Measure Omega m0 | `mu.trim hm0`; captures original mu/mOmega and explicit m0/hm0. |
| local instance | MeasurableSpace Omega | EXACT letI value m0. All original quantities above are typed before this local override. No global instance is declared. |
| g0 | Omega -> Real | `fun o => integral y, h o y dmu0` with m0 installed; captures h/mu0/m0 and canonical real structures. |
| r0 | Omega -> Omega -> Real | `fun o y => h o y - g0 o - g0 y`; captures h/g0. |
| v0 | Real | Integral of `r0(t.1,t.2)^2` under `mu0.prod mu0`; captures m0/mu0/r0. |
| rho0 | Real | `Real.sqrt v0`; captures v0. |
| P0 | @Measure (J -> Omega) mJ0 | `Measure.pi (fun _ : J => mu0)` with reduced coordinate structure; captures J/FintypeJ/m0/mu0/mJ0. |

The final universal T has type `(J -> Omega) -> Real` and is caller-bound in the conclusion. Its measurability is EXPLICITLY from mJ0 to `borel Real`; it is not an arbitrary ambient-only observable. The final universal exponent p has canonical ENNReal type, and all exponents including 0/infinity are covered. Universal observations o/y have the SAME Omega type. No non-Prop existential output occurs.

Standard instances captured implicitly by notation are the canonical real topology/Borel/normed additive group/real vector-space/complete-space/second-countability structures, canonical ENNReal structures, the explicitly typed original or reduced product/pi measurable structures, and the supplied Fintype J. Probability/SFinite/finite-measure instances are either supplied original Props or mathematically derived in the eventual proof; they are not new input data. The explicit @Measure.map source/target structures in the final pair/sample/scalar-law clauses are frozen, not inferred from a possibly wrong ambient instance.

For actual statistics, n/C0/y/z/p/envelope w are NOT captured in this theorem. They belong to downstream caller functions T and retain all their original assumptions. When needed, future qualified 218 supplies w's reduced measurability along with its countable family. Pointwise equality of g/r/rho preserves all deterministic original-n functions; the theorem supplies their laws only after reduced measurability has been discharged. This ledger does not promise hidden statistic, code, CDF, source theorem or density data.
