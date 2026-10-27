# Unit 241 affected independent review: function-division representation

Verdict: **AFFECTED_CORRECT_PENDING_KERNEL**. There is no blocking gap in the affected repair. This review joins the new hRatioGap representation step to my exact prior complete source review; it does not claim a new kernel pass, compiled-declaration review, axiom pass, or final qualification.

I am the same original never-author reviewer `/root/oq56_unperturbed_deleted_cost241_source_review`, resumed only for this affected repair. I wrote RUNTIME-ACK.json first and verified activation SHA256 `2576fa4ab40e5ae1e5dc2117ac427d2cb6980f2d49cd44311c026dd7696f5ce9` /5963B and all nineteen inputs. Requested model/effort remain gpt-6.1-sol/xhigh. Actual backend/model/effort and input/cached-input/output/reasoning-subset counts are unexposed and null. The previously read math-theorem workflow remains applicable; no math-ultra workflow is used.

The repaired source is SHA256 `a3f6a76b636d66b1049289293c12884bcc8474379b059f835507f3f49f73e5f8`, 19004 bytes, 372 LF, zero CR, UTF-8 without BOM. It has the same frozen public theorem, complete statement, import and assumptions. The author repair manifest is `0b2e30ed1f2bcee3c072ba7ca192bbd18b93f115a759d553e1ed4adff111ed61` /4923B; its final release is `59d9b0faa56d3cf0f04d635a8a3f1869eceb14a5fdf44b8f0c9e76f78daceeaa` /2746B, with all six operational counts zero. Its five manifest payloads were independently rehashed.

## Exact affected range and retained complete review

I independently compared the raw old and new byte arrays. The unchanged prefix is exactly 17866B, SHA256 `73837ea9250c895d066e11810574afb1785a3d8700dc10d96d4eb14f801b5bcb`. The unchanged suffix is exactly 655B, SHA256 `03b0d7fd96c48991caeacd0b2c74aac7f7fc514ddfd178664320b26a0754e756`. The original 61B block at zero-based offsets [17866,17927) is replaced by the new 483B block at [17866,18349). Their respective hashes are `e6732a98bb3c8438de9d00030fde363da4d6fa3ee696a5346d1350075ef8fcb5` and `a71b9a9c7b405df37b5eed3647f6a8b23bcdd0884a59e9e55cdbd4c4031739cb`. Reconstructing prefix + new block + suffix equals the entire repaired source. The newline after each replaced block belongs to the preserved suffix. This is old source line348 replaced by new lines348–355, with a net increase of 422 bytes and seven LF.

The prior complete review is sealed by manifest `2cda108350fbf1666da117fd19fbade063be0c0edeaf65a60a583581985d6236` /2704B and final release `d69a65b9ffc5771b5ec59742b367b0bd236c95ee3c5665e1f4ec03fc190c4ea9` /2271B. Its full coverage is `683d7964fe5f5dd12dded03f285118c0bd966d30d725e7c4909c71ebbe16f264` /59673B and report is `d278567b56155ebf8ca401831c6733f11543fe59b45529958d9e716468da8086` /19219B. I verified those bindings and all five manifest payloads. That complete review applies to old source `a3c7a3ea81a70a5472d63db5f3baea749ebb11432baac74f54271b2420416dd3` /18582B365LF, which is also unchanged in its preserved directory.

The byte equality establishes the reuse boundary, rather than an author assertion of similarity. All proof bytes before old348 are reused unchanged. The old suffix beginning immediately after the old348 text is reused at the corresponding new offset; the hCostDiff declaration moves349→356, hCostGap356→363, and final proof/closing lines move by seven. Their text, types and proofs are identical. The whole frozen declaration, all fifteen ordinary type/RHS/scope records, all six instance entries, the source-model premises, and the unchanged earlier pointwise/integrability/L1/finite-sum proof coverage are reused exactly. I did not commission or repeat an unaffected whole-proof review.

## Affected proof and full bearing context

I read the repaired statement's full universal ratio context at lines92–104 and the complete bearing proof context at lines317–368. The branch retains I0/sourceCost0 : ℝ, Iη : ℕ→ℝ, fullη : ℕ→Ω→ℝ, the same two literal finite-cost lets, and exactly the premises 0<I0, Iη→I0, and sourceCostη→sourceCost0. hTotalLim has the same numerator difference and zero limit as previously reviewed. hRatioGap retains exactly the same pointwise quotient goal and invokes the same hTotalLim, hIηlim and hI0.ne'.

The new hPiDiv has the explicitly declared proposition

```lean
((fun k : ℕ => (∑ i : Fin n, ∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
  (∑ i : Fin n, ∫ ω, weightedDeletedη k i ω ∂ν)) / Iη) =
  (fun k : ℕ => ((∑ i : Fin n, ∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
    (∑ i : Fin n, ∫ ω, weightedDeletedη k i ω ∂ν)) / Iη k)
```

Its left side is division of two functions ℕ→ℝ with the existing pointwise function operation. Its right side displays the same quotient at each k. The proof `funext k; simp only [Pi.div_apply]` reduces function equality to identical real values. It is correct for every k and requires no nonzero-denominator premise: Pi.div_apply describes total real division as well when Iη k=0. The binder k introduced by function extensionality is only a bound proof variable. hPiDiv is a local equality Prop, not a newly named ordinary function, choice, witness, instance or scalar alias. It lives only inside hRatioGap and is not a new public interface.

The final step changes to `simpa only [zero_div, hPiDiv] using hTotalLim.div hIηlim hI0.ne'`. The division limit API supplies the quotient function on the left of hPiDiv and limiting value 0/I0. zero_div reduces that limiting value to zero; hPiDiv rewrites exactly the function argument to the frozen pointwise-lambda goal. The orientation and numerator, measure, finite index set and denominator all match. This directly addresses the sole compact native001 diagnostic. It changes representation, not the mathematical statement or the denominator condition used by limit division.

The subsequent hCostDiff still expands the same two approved costs and cancels their common full integral for every k under total real division. hCostGap still rewrites through that equality and adds the unchanged perturbed-cost limit. Thus the repair does not create a dependence on all-k denominator positivity or on measurability/integrability of the arbitrary common full integrand in this cancellation-only branch.

## Ordinary values, Prop inventory, boundaries and source fidelity

The fifteen approved ordinary values and their full contexts are unchanged and recorded by exact prior-coverage reference in COVERAGE.json, together with their full type/RHS/scope records. The optional sourceCostη and unperturbedSourceCostη lets remain inside the same universal Prop branch. There is no local let/letI, new definition, extra import, custom instance, choice, existential witness or added mathematical premise. The six inventoried source/environment instance entries remain exact; the proof uses the existing pointwise division operation, not a new instance declaration.

Independent extraction from the repaired source gives thirty-six explicitly typed named have facts: the previous thirty-five with identical types and one new hPiDiv equality. Only hRatioGap's proof is affected. COVERAGE.json maps each old fact to its new source line, records its exact type, and marks unchanged coverage reuse separately from the affected/new proof judgments. These are source facts, not predictions of compiler-generated owner counts.

All boundary judgments from the complete review remain applicable by byte equality. The repair itself is valid for arbitrary n, including n=0, arbitrary measure and real z/epsilon signs, zero K/Hdelete, and finite-index zero Iη. A positive limiting I0 remains the only nonzero denominator input to the limit theorem. The earlier cancellation before measurability still avoids B/Bdelete assumptions; the same selected qualified234 premise availability, p54 repairs and external-result attribution remain untouched. No different existential source model, source tail engine, original H-complement quantitative payment, CDF/atom/physical-statistic/root or full OQ56 conclusion is introduced.

## Failure preservation and remaining exact gates

The bound compact native001 projection reports RC1, one error at old348, zero warnings, no object, ended owned execution and unchanged preservation state. Its remote receipt binding is `ac9a78589bf7bab4ed26253ae4cbbbfb027325eeef669deb093085123ea273cc` /22085183B. I read only the supplied projection and did not fetch a remote receipt, replay that attempt, overwrite its diagnostics, or treat it as a pass. It is retained failure evidence. The diagnostic shows precisely function quotient versus pointwise lambda after zero_div simplification; the new equality covers that representation discrepancy at source level.

The repaired source still needs designated-server native002, a successful same-first-original-object all-actual-owned TYPE/required VALUE/transitive-axiom audit, and an independent final qualified source/compiled/evidence join. The accepted whitelist remains propext, Classical.choice and Quot.sound. Native001 did not create an object, so this review makes no original-object existence claim for unit241. A further proof edit requires review of its affected scope; no future bytes are approved here.

Local checks confirm exact frozen prefix/head/closing, exact reconstruction, unchanged fifteen ordinary definitions and six inventory instances, thirty-six explicit Prop facts, UTF-8/LF, and absence of sorry/admit/axiom/unsafe/native_decide in the source. These checks are not Lean elaboration or kernel verification. I made no proof repair and ran no Lean/local compilation/server/network/upload/Git/API/child operation. Writes are confined to `unit241/source-review-affected-01/`; original review, sources, freeze, failed receipts and all other owners' files remain read-only.

The affected verdict is source-only, qualified=false, kernelPending=true, with no blocking source gaps. MANIFEST.json seals the five payloads. lastzeroRELEASE.json is the final write and records writer/heavy/inflight/pendingExternal/children/uncertain all zero; no activity continues after that release.
