# Unit236 independent affected repair01 review

**Verdict: SOURCE_REPAIR_CORRECT_KERNEL_PENDING** (activation-equivalent spelling: CORRECT_SOURCE_REPAIR_KERNEL_PENDING). The four changed proof sites are mathematically correct, address the four saved elaboration diagnostics, and preserve the unchanged frozen statement and proof interfaces. No critical affected mathematical gap was found. `qualified=false`, `kernelPending=true`, `kernelChecked=false`, `axiomAudited=false`.

This is the original fresh NEVER-AUTHOR reviewer, `/root/oq56_exceptional_tail236_source_review`, continuing under the explicit affected-review activation. The reviewer never authored or repaired236. Only `drafts/oq56/unit236/source-review-repair-01/**` is writable under this activation. Actual runtime ACK preceded review. The existing math-theorem workflow applies; no math-ultra workflow or additional context was used. Requested model/effort remain explicitly `gpt-6.1-sol`/`xhigh`; actual model/effort and the four usage fields are unexposed and remain null.

## Bound versions and exact review scope

The affected activation is SHA256 `6de8e95c4a0830db1560c672764bc6315b8c73a8ccc42aa20f1f68887b9dff89`,6121 bytes. All16 immediate bound inputs matched their recorded hashes and byte lengths. The repaired source is SHA256 `cb1ed434c1029e674ddff14a1be07ab55b2fb064060acbe92bea389a93f7df8f`,11444 bytes,245 LF. Its predecessor is SHA256 `ebddcd2141aa704400cec5d3c3b6157ba6d83cdb8df17a8b5b28ab8320cecf6d`,11078 bytes,239 LF. Neither source was written by this reviewer.

The original complete source-to-statement/proof review is reused through its sealed manifest SHA256 `59fda28fa41b68c0ef954d8db7b1e2ac9075e9dc34ebbb6f0c0f498a4526dd3c`,3126 bytes, and zero release SHA256 `949468a5a81048c36ad518114597a78991c21ffd9d92e43b9c120da16ceb2023`,2459 bytes. Its five completed payloads and37 distinct immutable input records remain bound. Original governance-file fingerprints are preserved as historical observations of mutable governing metadata, not reclassified as frozen mathematical inputs.

This round reads the complete new minimal.diff, repair REPORT, compatibility description, complete3792-byte native diagnostic text, the complete four new proof spans and adjacent proof/consumer context. It verifies byte correspondence for the rest. It does **not** repeat the original complete mathematical review or the accepted Gaussian/P51/233/235 proof reviews. The original review's actual-definition, full-public-head, p54/p51 primary-source and pinned-API coverage remains applicable to the byte-identical statements and unchanged proof portions.

## Saved first-native outcome and all four diagnostics

The normalized diagnostic input has SHA256 `5e83774569b2426a3b0d89835d7179121118c644ee0d53229e6c7ff32f495e48`,6971 bytes. The completeDiagnosticText field was read in full and independently encoded as UTF-8:3792 bytes, SHA256 `2256c8ceba1afdc601eba497e1c369347f6cc7e4b5eb5ccfff8f3c976ff9faf7`, exactly the saved stdout fingerprint. This verifies coverage of the complete saved text, not merely its four error headlines.

The saved lead receipt reports actual RC1,6.189834870398045 seconds, no timeout, all owned group members ended, no object, source preservation, and no post error. These are saved exact lead observations; this reviewer performed no new server/process inspection. The existing mathlib-local-changes stderr warning is preserved. This failure is not a proof pass, counterexample, or quota conclusion.

The two type mismatches at old59 and65 show a composed function in the obtained Tendsto statement while the expected type is its explicit lambda. The rewrite failures at old108 and112 show `Real.rpow` products in the target, while the rewrite search did not find the displayed overloaded-power pattern. No additional source error is reported in this3792-byte diagnostic text.

## Complete affected mathematical review

**Change1, old59 -> new59, with complete context new45–60.** The only edit adds `Function.comp_def` to `simpa only [Real.rpow_zero, one_mul]`. The input remains the global pinned theorem `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) b hb`, composed with the unchanged `hthird`. Function composition expands `(f ∘ g) n` to `f (g n)`. Therefore the resulting function is exactly

`fun n : ℕ => Real.exp (-b * Real.rpow (n:ℝ) (1/3:ℝ))`.

The original real-power-zero and one-multiplication reductions remain. The scalar b, proof hb, filter, zero limit and target proposition are unchanged. This fixes the displayed definitional mismatch without adding a rate premise, function parameter, or mathematical limit assertion.

**Change2, old65 -> new65, with complete context new61–78.** The only edit adds `Function.comp_def` to `simpa only [Real.rpow_one]`. The unchanged input is the same pinned decay theorem at real exponent1, coefficient b>0, composed with hthird. Expanding the composition and applying real-power-one gives exactly

`fun n : ℕ => Real.rpow (n:ℝ) (1/3:ℝ) * Real.exp (-b * Real.rpow (n:ℝ) (1/3:ℝ))`.

No underlying function or limit has changed. The downstream hsmallLimit still adds hexp and hlinearExp and multiplies by128/3, so its already-reviewed residual calculation receives exactly the same two propositions. Function.comp_def is used solely to expose composition within the proof term; no ordinary binding, callback, or added assumption appears.

**Change3, old108–109 -> new108–112, with complete context new85–114 and consumer new123–129.** The proposition remains `hproduct : s * Real.rpow x (2/3:ℝ) = x`. The unchanged `dsimp only [s]` exposes `Real.rpow x (1/3:ℝ) * Real.rpow x (2/3:ℝ)`. The new calc uses the symmetric equality from the exact pinned head

```lean
Real.rpow_add (hx : 0 < x) (y z : ℝ) :
  x ^ (y + z) = x ^ y * x ^ z
```

with the existing hxpos and fully typed real exponents1/3 and2/3. The ordinary real Pow instance is definitionally Real.rpow, as covered by the original exact primary-source review. Hence the direct proof term is precisely the required equality to `Real.rpow x ((1/3:ℝ)+(2/3:ℝ))`. Normalizing that real sum gives1; `Real.rpow_one x` gives x. Every step is a proof of equality, with no new data binding or positivity premise. The unchanged consumer new129 rewrites the same hproduct proposition to derive the same fast linear rate.

**Change4, old112–113 -> new115–119, with complete context new113–133.** The proposition remains `hsqrt : s*u = Real.sqrt x`. After unchanged `dsimp only [s,u]`, the symmetric fully typed `Real.rpow_add hxpos (1/3:ℝ) (1/6:ℝ)` gives `Real.rpow x ((1/3:ℝ)+(1/6:ℝ))`. The sum is1/2 in ℝ, and the symmetric exact pinned `Real.sqrt_eq_rpow x` gives Real.sqrt x. The direct term avoids the old rewrite search while proving exactly the same identity. The unchanged consumer new130–133 multiplies `2*t0<=u` by s>=0 and rewrites s*u using this identical hsqrt fact, yielding the same `t0*s<=sqrt(x)/2` bound.

All four edits are therefore sufficient at the mathematical/source level for their stated purpose. Actual name resolution, elaboration, tactic execution and kernel acceptance of the repaired source remain the required new server check; this source review does not predict a successful exit code as an observed fact.

## Independent full-byte correspondence

The new minimal.diff is SHA256 `f34073b56144c39f6a9291881e726a1a40e12e8ceec8674af72b7bff527f0c48`,1841 bytes. Its two textual hunks contain exactly the four replacement spans below; the last two replacements share a textual hunk because they are adjacent. Six old lines are replaced by twelve new lines.

| Old inclusive lines | New inclusive lines | Affected fact |
|---|---|---|
| 59 | 59 | hexp proof simplification |
| 65 | 65 | hlinearExp proof simplification |
| 108–109 | 108–112 | hproduct proof |
| 112–113 | 115–119 | hsqrt proof |

The reviewer independently extracted exact LF-terminated lines from both bound sources and compared **every** unchanged chunk:

| Old inclusive lines | New inclusive lines | Result |
|---|---|---|
| 1–58 | 1–58 | Byte-identical |
| 60–64 | 60–64 | Byte-identical |
| 66–107 | 66–107 | Byte-identical |
| 110–111 | 113–114 | Byte-identical |
| 114–239 | 120–245 | Byte-identical |

Forward reconstruction from the old unchanged chunks plus the exact new replacements equals all11444 new bytes and their new SHA256. Inverse reconstruction from new unchanged chunks plus the exact old replacements equals all11078 old bytes and reproduces the original SHA256 `ebddcd2141aa704400cec5d3c3b6157ba6d83cdb8df17a8b5b28ab8320cecf6d`. These were actual local-memory reconstructions and comparisons, not acceptance of the author's asserted result. No reconstructed source was written. This establishes the exact applicability of the prior full review to all unaffected portions.

The frozen preamble plus full head and ` := by` prefix match the new source exactly; the frozen closing matches exactly. All ordinary let lines are identical to the old version: the result cWindow plus exactly five proof-local lets cWindow,b,x,s,u. Their types, RHS and scopes are unchanged and remain those approved in the freeze. The new calc expressions are Prop-valued equality steps. There are no additional ordinary helpers, declarations, instances, witnesses, callbacks or assumptions. The repaired source remains UTF-8 without BOM,245 LF,zero CR and no forbidden proof-escape token.

## Interaction, source fidelity and evidence boundary

The original complete review remains applicable to the same real t0/cg arguments and positivity proofs, result cWindow fixed before n/z, one eventual cutoff, actual n>=4, and nonempty whole closed sixth-root window. The literal payments and target are byte-identical. The unchanged hsmallLimit/five-event intersection consumes the same repaired limit propositions; unchanged hlinear/hsqrtRate consumes the same repaired algebraic propositions. All subsequent Gaussian and factoring proof bytes are identical up to the line shift.

Thus the reverse public ratio at(z,0), actual Gaussian tail definition, exact3/8 loss,16 numerator,128/3 residual,3t0/8 exponent, positive divisions and closed-endpoint reasoning retain the prior complete source review. No independent233/235 cg witnesses are identified; no event/model consumer or source-window intersection is newly claimed. p54's bounded/convergent conditional p-moment repair remains intact, and the false arbitrary-polynomial variation sentence is not restored. No probability/SZ/CDF/atom/zero-denominator/full OQ56/root closure or novelty claim is introduced.

The saved native001 failure and all old source/review/evidence bytes remain preserved. New qualification requires the lead's exact new source native002, then the same first successful original object's actual module-index owner TYPE/required VALUE/transitive AX audit and independent final evidence join. The original source review and this affected supplement together provide source/proof coverage; neither substitutes for those machine receipts.

All reviewer actions were local reads, small deterministic byte comparisons and owned review-artifact writes. No Lean/server/network/upload/Git/API operation, child, source/freeze/author/other-owner write, or accepted old proof/check replay occurred. Final zero release records writer/heavy/inflight/pendingExternal/children/uncertain0 for this reviewer and is the last authorized write.
