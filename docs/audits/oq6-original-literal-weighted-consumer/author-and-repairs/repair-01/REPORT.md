# Unit228 repair01: explicit source measurable spaces in hIntEq

Status: **NARROW_AUTHOR_REPAIR_COMPLETE_NOT_LEAN_CHECKED.** The complete new source is `OriginalLiteralWeightedConsumer.lean`,41664B/658LF, SHA256 `df16a04be1a36ccef76eedc4872e7f1dd911d5be2da7117e307bcf24662b1155`. Old b348 source and all prior source/review/native/timeout bytes remain unchanged.

The actual native02 diagnostics report exactly two errors at old487/491: a synthesized source instance mN₀ differs from the source mN inferred from typing P. That300s-bound attempt ended naturally RC1 after96.0434306s, without an object. This repair addresses that elaboration mismatch; it does not reinterpret the earlier90s timeout or claim a kernel result.

Only old lines484–491 inside the frozen hIntEq proof are replaced by new lines484–497. `EXACT-DELTA.json` contains both literal blocks, exact old/new fingerprints and the checked byte equality of everything before and after the replacement. The frozen preamble/head/closing, all76 ordinary data lets/types/RHSs and46 target conclusions are unchanged. No performance edit, warning-only edit, new helper, local instance or mathematical premise is introduced.

The repair makes the existing integral_map applications explicit:

- The q application has source `(Fin n→Ω×ℝ),mAug,ν`, target `(Fin n→Ω),mN₀`, map q and target function f.
- The identity application has source `(Fin n→Ω),mN,P`, target `(Fin n→Ω),mN₀`, map id and the SAME f. The real normed additive group and real normed-space arguments are the existing canonical instances, now written explicitly as typed inferInstance arguments.
- The second map-law rewrite uses the already retained `hP₀map.symm`, whose exact statement is `@Measure.map ... mN mN₀ id P=P₀`. This is the same equality used to construct hId immediately above the callback. It avoids elaborating `hId.map_eq` with a fresh mistaken source instance. The q law and final `h1.symm.trans h2` composition are unchanged.

The required API was inspected in the Root-curated pinned Mathlib source, rather than inferred from a different version or checked locally. `coordination/pinned-api-20261026/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` is72547B/SHA256 `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670`, identical to the source03-fin-integral-rpow copy whose manifest records pinnedGitBlobExact. Its152–155 and183–184 context gives the G normed-group/normed-space and m/μ parameters. Its complete1076–1078 statement is:

```
theorem integral_map {β} [MeasurableSpace β] {φ : α → β}
    (hφ : AEMeasurable φ μ) {f : β → G}
    (hfm : AEStronglyMeasurable f (Measure.map φ μ)) :
    ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ
```

Consequently the explicit positional application fixes α,G,their canonical real structures,m,μ,β,target measurable space,φ,hφ,f,hfm. It does not add target integrability: hf remains measurability under mN₀, giving the same target AE strong measurability under the exact pushforward. The existing hq/hId AE measurability proofs are unchanged. The callback still proves exactly `∫x,f(q x)∂ν=∫ζ,f ζ∂P` through the SAME q/id/ν/P₀/originalP.

No missing mathematical interface or necessary extra premise was found. The new proof text is not elaborated or kernel checked by this author. It needs an independent affected-proof/interface review, followed by the lead's exact-new-source bounded native and, only after a first object succeeds, same-object all-owned TYPE/required VALUE/transitive-AX gates. The unchanged source portions and their accepted review remain reusable; no full old producer review/check was replayed.

All writes are confined to repair-01. Lean/server/network/transfer/Git/API/children are zero, and all six prior warning-producing constructs are left byte-identical outside the replacement. Requested model/effort remain gpt-6.1-sol/xhigh; unobservable actual configuration and usage fields are null. RELEASE0 records zero writer/heavy/inflight/pending-external/child state.
