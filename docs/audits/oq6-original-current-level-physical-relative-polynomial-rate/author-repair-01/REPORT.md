# Unit262 minimal proof-only native01 interface repair

STATUS: COMPLETE_PROOF_ONLY_REPAIR_CANDIDATE

The new complete source and proof are ready for the SAME retained independent reviewer to assess the affected delta. This author has performed local source reading, hashing, exact diff and byte/patch validation only. The candidate is unqualified: no new Lean, axiom, server, network, Git publication or child operation occurred.

## Exact authorization and preserved inputs

The sole author role is `/root/oq56_unit262_author_repair01`, writing only `C:/game/shao lean/drafts/oq56/unit262/author-repair-01`. The activation is `repair01-author-ACTIVATION.json`, SHA256 `a6e6accd31aacc91aab442aac67f65579bd674fe54e8eee5be0249632183c4d3`, 2946 bytes. Its complete eight inputs were read and their exact hashes and byte sizes verified before source writing. READ_ACK.json records the actual read acknowledgment. The prior author release `6c2031bd087ecb82617899f5887e88ceacb5fb2136def46fcfc98334e38be45e` has all six counters zero; its source directory was not modified.

The preserved old full source is SHA256 `06bf9452ba1bcb23e751749739d231c10f93fa77fb7e615bcbc448d3e4b78e7b`, 18403 bytes/357 LF. The old proof is SHA256 `17ad0d82c4161b3cf0b4bb65d7198428eb0b8f581eecadaa8133ae89e62314a9`, 14443 bytes/279 LF. The complete independent SOURCE report `6ecc9afd54ec45426e2214f28f739c3d028caf601d59aaa2483e05140cf3cc66` was read. It accepts the mathematical argument, with machine qualification still pending. The failed native01 compact diagnostic `91d370fba1ca8dddd5098a4e0cccf4128b68cd47f599265da1eefc911daa3349` records natural RC1, 6.089823387563229 seconds, no object and three errors; that failure remains preserved and is not a proof result.

The activation and INPUT-BINDINGS.json bind every direct input, frozen fragment and read-only accepted API example. Existing qualified dependency evidence and the already adopted P177 fce0 provenance are reused exactly; no adoption or old proof/kernel/axiom check was repeated.

## Complete minimal repair

Exactly two lines are inserted and one no-op line is deleted in each of the assembled source and matching proof fragment. DIFF.patch and PROOF-DIFF.patch contain the exact two-hunk changes.

1. New source line119 inserts `simp only [Real.rpow_eq_pow]` in hpower, immediately before the unchanged `rw [← Real.rpow_mul (Nat.cast_nonneg n)]`. The failed rewrite expected real HPow notation while the target used explicit nested Real.rpow. This identification gives the library rewrite the representation it uses. The power exponents remain 1/3 and 3/2, and their product remains 1/2; the existing sqrt conversion and arithmetic proof are unchanged.
2. New source line122 inserts `simp only [Real.rpow_eq_pow] at hpower ⊢` immediately before the unchanged final composition/hpower simplification. This puts the equality and the pointwise limit-comparison goal in the same representation. The same hthird, same power-times-exponential asymptotic theorem, same t0/2 coefficient, same hRlimit and same pre-p threshold remain.
3. Old source line182, `dsimp only at hMomentN`, is deleted. Native01 reported that it made no progress. The unchanged moment specialization is destructured directly by the unchanged rcases; no hypothesis, conclusion, producer or mathematical interface is replaced.

The repair pattern was read in the curated accepted sources `library/Shao/C2/OriginalMomentEnvelope.lean` lines48-53 and `library/Shao/OQ3/NormalizedIIDPairSuperpolynomialDecay.lean` lines20-27. Both normalize explicit rpow with `Real.rpow_eq_pow` before nested `Real.rpow_mul`, and normalize the local power equality and comparison goal before rewriting. The same normalization-before-multiplication pattern was also read at `library/Shao/OQ6/FiniteHilbertSignMoments.lean` lines622-623. These are API identification examples, not imported new assumptions or replacement mathematical results.

All other proof bytes are unchanged. In particular, the original physical statistic/event, all windows including absorption, original zero-denominator convention, beta-zero branch, quantifier order and explicit Ktail remain exact. The frozen 62-LF head, preamble and closing remain exact, and the existing proof-local `maxHeartbeats 800000 in` is unchanged; there is no new option or resource request.

## Result and static evidence

The candidate full source is SHA256 `05fafc9fcc2aa994975a5c0b1923e48680816207e1136c420516f2f93170e6a9`, 18462 bytes/358 LF. Its proof is SHA256 `1591333e50dca44220e909bc0683e759438e882ea212a3024c4625654602e3b7`, 14502 bytes/280 LF, identical to assembled source lines76-355. The complete new assembled source, including all new proof lines, was actually self-read.

STATIC-CHECKS.json records exact frozen assembly, unchanged options, no forbidden proof constructs, one source theorem, exact input hashes, and strict forward/reverse application of both unified patches. The strict parser checks each hunk position/count and every context/deletion line without fuzzy offsets. Reversing the new source/proof patches recovers the exact old source/proof hashes above. Actual generated/private owner counts and kernel/type/value/recursive-axiom success are deliberately not inferred from text.

All new files use UTF-8 without BOM, LF line endings and one final LF. The first READ_ACK serialization attempt produced a null record after a PowerShell boolean-literal error. It is retained as READ_ACK.invalid-01.json; the valid actual acknowledgment was then written before any mathematical source write. No mathematical source was affected by that administrative serialization failure.

The next dependency is the SAME independent reviewer affected SOURCE review, followed by the lead-controlled native02 and, only if it succeeds, the same-original-object all-actual-owner TYPE/required VALUE/transitive-axiom gate. The author does not claim those gates passed. Full OQ56 and root remain OPEN.

Requested model/effort: gpt-6.1-sol/xhigh. Actual model/backend/effort and separate input, cached-input, output and reasoning-subset usage are unexposed/null. The final author write is LASTFINALWRITE.json; after it all six author counters and writer/execution/child/publication authority are released, with no further writes before a new explicit activation.
