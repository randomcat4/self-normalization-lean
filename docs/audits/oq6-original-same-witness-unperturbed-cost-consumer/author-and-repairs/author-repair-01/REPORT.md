# Unit242 source002: minimal affected hIntegralNew repair

Status: COMPLETE_MINIMAL_AUTHOR_REPAIR_UNCHECKED. The complete source002 is125296B/1880LF, SHA25691ecbf51f6773d06d2b6d2b02e98f31bd2d433bdae03596fbe90c00f529765e5. It differs from reviewed source001 only by inserting the16 ASCII bytes `, sub_add_cancel` in the simplification list at line1840. No Lean or server check was performed by this author. Independent affected-proof review, the lead's new-source native check, and eventual same-original-object all-owned TYPE/required VALUE/transitive-axiom review remain pending. qualified=false.

The activation6426176b8935d5d92949865c72d9e1dd56e99c9e0dc5ee0b8f67f582aa1347d8 /6854B and all18 input hashes/byte counts were verified before the FIRST author write, RUNTIME-ACK.json. Both old author releaseedd8390c836c1269ddd5a11f62cafe87948327dd2420d8019efb42a1eaaede9e /2245B and independent reviewer releasee8804e285f49ee02c8ad40f096ffa2448fc05d6c6fcb1d861102665683abee8b /2195B have writer/heavy/inflight/pendingExternal/children/uncertain all0. Only the new unit242/author-repair-01 directory is written. Old source, freeze, reviewer evidence, producer evidence, failures and all other owners' bytes remain read-only.

## Exact failure and repair

The complete native001 error projection was read. The preserved receipt reports natural RC1 after62.29056249931455s, one error/three warnings, no object, all owned processes ended, preservation_equal=true and no timeout cleanup. The single error at1840 is a shape mismatch after Tendsto.add: the actual result uses a pointwise lambda whose body is `(newIntegral-oldIntegral)+oldIntegral`. The existing hPiAdd equality concerns whole-function Pi addition, so the original simplification list did not cancel that actual lambda body.

The repaired line is:

```lean
    simpa only [hPiAdd, zero_add, sub_add_cancel] using hDiffLimit.add (hOld45 i)
```

The standard real identity sub_add_cancel rewrites the pointwise body directly to newIntegral. zero_add still changes the target `0+oldTarget` to oldTarget. hDiffLimit, hOld45, the full hIntegralNew statement, and the existing hPiAdd statement/proof are unchanged. No new named fact is introduced; no full-function alias, assumption, callback or ordinary value is added. This changes the failed elaboration step while preserving its exact original mathematical conclusion.

## Byte provenance and retained scope

DIFF.json and DIFF.patch describe the complete one-line difference. The longest common prefix is122450B with SHA2562d01e4a44c6c335b989e87707591956008d66ad57d13b1c6152a9fb94f914a9e. The unchanged suffix is2830B with SHA256d72b6a4b24e148e8a9a824d4e1f4619b371218fbad4e4fd33c0b7dc97fcbe08b. Its old start is byte122450 and new start byte122466, zero-based. Thus every125280 old byte is preserved in order, and the only new bytes are the explicit16B insertion. Old source001 remains at its original path and original SHA25690c48141896acf22f27d0470cd3c99fae57bc53470a4b143bab9e210b3979ce0.

Frozen preamble, whole frozen head including trailing LF, and frozen closing are exact. All138 public ordinary types/RHS are checked in source order. Direct source recount preserves the89 result-let mirrors plus two original witness choices, three explicit proof instances,24 explicitly typed have facts, one call each to qualified240 and241, all52 old analytic clauses, all seven frozen new clauses, and the whole original payment branch. There are zero additional ordinary values, instances, imports, assumptions, theorem/helper declarations, models or callbacks. The source remains strict UTF-8 without BOM and LF.

AFFECTED-PROP-CONTEXTS.json provides the complete unchanged types and actual enclosing scopes of hIntegralNew, hDiffLimit and hPiAdd, binding the historical complete94-record source001 context file. Only the proof rewrite at1840 needs new independent review. The unchanged-region complete SOURCE review and qualified240/241 producer evidence are reused exactly; no accepted proof or check is replayed. No B/Bdelete premise, Aepsilon/Anew convention, perturbed/unperturbed cost distinction, original source scope, witness identity or root claim changes.

All work was local reading, exact16B repair and deterministic byte/inventory checks. Lean/server/network/upload/Git/API/children calls and writes outside the new owned folder are0. Requested model/effort remains gpt-6.1-sol/xhigh; actual backend/model/effort and four usage counters are unexposed and null. MANIFEST.json seals these payloads. lastzeroRELEASE.json is the final write, releasing all six categories at0 with no further author write.
