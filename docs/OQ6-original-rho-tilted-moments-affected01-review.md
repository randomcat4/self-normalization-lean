# Unit 213 same-reviewer affected repair01 SOURCE review

STATUS: CORRECT

The repaired source is accepted for new native02: `acceptedForNative=true`, `qualified=false`. I found no critical gap in the two authorized proof changes or their interactions. This is a source review; no new kernel, actual-owner TYPE/FULLVALUE or recursive-axiom result is available at this boundary.

New source SHA256 `7efcc429e36c4849009e01f05f1db9c9400165b4d5be1e43a0677b0285fed4bf`, 20086 bytes, 459 LF. Current repair freeze v2 SHA256 `cfdb7451847d5d842ff508f2e18a6850e381577d83e8ef0fc0d216e26894a5eb` superseded v1 before author implementation. The four complete mathematical heads and all local data retain original substantive freeze SHA256 `47d21e0b9d2890fcae23bdf4008c78a134149feccf6c802c117e974fbb998105`.

Same independent reviewer `/root/oq56_rhomoments213_final_review`, separate from author `/root/oq56_rhomoments213_author`; prescribed gpt-6.1-sol/xhigh. Actual provider model/effort telemetry and input/cached-input/output/reasoning-subset counts remain unavailable/null. Only this new affected-review directory was written. No source edit, Lean, server, network, upload, Git, API or subordinate-agent operation was performed.

## Evidence boundary and exact reuse

Native01 on the prior exact 457-LF source ended naturally RC1 with two source errors, eight source warnings, no object and exact preservation according to the bound lead diagnostics. Its elapsed time is 10.684514991939068 seconds. That failure remains a failure; the prior complete SOURCE verdict was never a machine pass. No original successful object exists for that failed source, and this review invents none. The underlying large remote receipt/config/log files were not fetched or read; this review uses the exact compact affected-diagnostics packet supplied by the lead.

The prior complete SOURCE review is reused through its exact sealed manifest SHA256 `e487ec365498b4ee88cf527d97e3b4da09ebb4bd5b62e10da71952b74f8f623f` and all six payload fingerprints. Its original p51 source-to-statement review, all four complete proof reviews, 28 named proof-data values, 21 header-let occurrences, 92 named derived-Prop blocks, three complete direct actual TYPE reviews, 52 verified bindings, old qualified proof/object/axiom reuse, and explicit P35 source-data evidence decision remain applicable outside the two changes. This is evidence reuse, not another complete old-proof/kernel/leaf-axiom review or replay.

I independently reconstructed the entire repaired source by applying precisely the two authorized literal substitutions to the previously reviewed source, then compared every byte. No other source difference exists. The imports/options/namespace, four complete heads, all data initializers/captures, assumptions, anonymous closures, other Prop statements and warning-producing regions are unchanged. There is no hSubI, new proposition, helper, instance declaration or cleanup edit. The additional two lines come only from spelling out the hN4 proof.

## H03: explicit subtraction function for integral addition

I read the complete repaired H03 context and proof, source lines 140–174, including its unchanged L2/L1 steps, constant c, square/linear integrability, entire expansion, probability-mass evaluation and final nonnegative-square argument.

At line 163 the sole change is `integral_add (hSqI.sub hLinI)` to `integral_add (hSqI.sub' hLinI)`. The exact pinned `Integrable.sub` head returns `Integrable (f-g) mu`; the exact `Integrable.sub'` head returns `Integrable (fun a => f a-g a) mu`. Both require the same two integrability proofs and the same ambient measurable-space/normed-additive-group context. In this application beta=Real and alpha=X; hSqI is integrability of `fun z => |f z|^2` and hLinI is integrability of `fun z => 2*c*|f z|` under the same probability P.

The primed head therefore gives the explicit integrand `fun z => |f z|^2-2*c*|f z|` required by `integral_add`, whose full head integrates `fun a => f a+g a`. The second addend remains the integrable constant c^2. This directly addresses native01's failed rewrite pattern containing a pointwise function-subtraction application. The next unchanged `integral_sub hSqI hLinI`, constant multiplication, constant integral and mass-one rewrites have the same integrable terms and their exact explicit integral heads. The function subtraction is pointwise the same mathematical function; no measure, value, premise or target inequality changed.

I reviewed the selected complete primary `integral_add`, `integral_sub`, `Integrable.sub` and `Integrable.sub'` heads together with the previously bound L1Space and Bochner effective contexts. The required instances are the existing measurable X and usual Real normed-additive/real-normed-space instances. `integral_add` and `integral_sub` take explicit integrability premises; the replacement supplies those premises rather than assuming a new integral identity. H03 still proves genuine `(integral |f|)^2<=integral f^2` on a probability space, using the unchanged integrability-justified expansion.

## P01: exposing the frozen real cast to the cast tactic

I read the complete repaired P01 statement and proof context, source lines 176–455. The declaration still quantifies exactly n>=4, y>=1, the original h-model inputs and explicit quadratic window. Its local N remains exactly `(n : Real)` at line 275.

At lines 292–294 the proposition is still `(4 : Real)<=N`. The proof now performs `dsimp only [N]` immediately before `exact_mod_cast hn`. This unfolds only the already frozen local initializer, so the cast tactic sees `(4 : Real)<=(n : Real)` with `hn : (4 : Nat)<=n`. It addresses native01's expected-type mismatch without changing the local proposition or adding an assumption. N is not reassigned; the local unfolding affects only that proof goal.

All consumers retain exactly the same hN4 proposition: positivity of N, sqrt(N), N-1 and N-2; positivity of dD and dJ; n<=2(n-2), its squared ratio and the J bound; and n<=2(n-1) for D. The remaining complete P01 proof uses the unchanged 139 scale rho, 140 structural/density/full-law data, fixed original denominators, H03 and scalar bounds. The repaired H03 conclusion is applied unchanged at new line 397. The same 23 conjunction leaves are assembled at lines 452–455. No interaction changes the full-law measure, residual, rho=0 handling, original normalizations or explicit window.

## Scope, coverage and remaining machine work

The source remains one public theorem plus three private theorem helpers, zero new global non-theorem source declarations. All 28 named proof-data values, 21 head-let occurrences and 92 named derived-Prop introductions are unchanged in inventory. H03 hExpand has only its proof application changed; hN4 has only its proof tactic block changed. Source lines after the latter shift by two. COVERAGE.json records complete affected declaration text/heads, the exact delta and interactions, and hash-bound reuse of the unaffected coverage.

The original p51 S3/S5 scope, literal rho/rho-squared scaling, constants 14/56/8, original h/projection/residual/tilt, J=sum(psi/(n-2))^2 and D=F/(sqrt(n)(n-1)) are unchanged. No weighted deletion, S14 fee/probability, general S15 or OQ56/root completion claim is introduced. The prior narrowly scoped P35 decision remains unchanged; no standalone reflected packet is fabricated.

The eight original warnings were not cleaned up. New compiler diagnostics are unknown until native02 actually runs, so this review does not predict a warning count or claim those diagnostics are gone. The same-source native02 and, only upon success, its same FIRST original-object all-owned full TYPE/required non-theorem FULLVALUE/recursive AX packet remain required. The standard whitelist is propext, Classical.choice, Quot.sound. The same reviewer can then complete final machine-evidence review, reusing this affected SOURCE judgment and the sealed original full review. All prior failure and review bytes remain preserved. Runtime is natural zero after this review, with no command dispatched or pending.
