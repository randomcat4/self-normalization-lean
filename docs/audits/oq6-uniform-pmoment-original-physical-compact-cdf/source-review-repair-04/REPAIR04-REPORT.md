# Unit275 independent affected SOURCE review — repair04

Verdict: **CORRECT at SOURCE level for the exact repair04 candidate**, with no critical mathematical or source-coverage gap found in the affected change. This verdict is independent of the author. It carries the exact unchanged SOURCE3 evidence forward and adds a complete affected review of both old and new helper7 declarations. It is not a kernel, object, TYPE, VALUE or axiom receipt: qualified=false and kernelChecked=false.

The reviewed complete source is 215e03f4731a56bce41aa7682de1269c907ceab1d57afd0587acda2a465c45b4, 83842 bytes, 1618 LF. The aggregate helper1–8 plus public-main proof stream is 9894981ced7713e826b5a8a23ba38ad48cd6a7c489ecdac741adb5387126c090, 63115 bytes, 1240 LF. The frozen private-eight plus public HEAD stream remains dcc42f20519dca48918f8f1d2b779d846b410ba86a19a9724f5ff7c3ccbfbb14, 20197 bytes, 350 LF. The main proof remains eb4641c5e92daa45daaeae7ded73b923a6264e4ab178923201057105e987e1a1, 7079 bytes, 146 LF.

## Activation, independence and actual reading

I independently verified the exact SOURCE4 activation SHA256 205aebab9259f66fd237a5c61c9339166ac83831cbd99ed36e455ea61f641d7d, 43888 bytes, and all 188 input SHA256/byte bindings before the first write. The actual runtime ACK is READ_ACK.json in this sole new review directory. The prescribed settings are gpt-6.1-sol/xhigh; actual backend/model/effort and usage are unexposed and null. I am separate from the author and made no author/source repair.

I read the complete repair04 author report, the complete native04 inspection including both complete 557-character error contexts, and each complete old and new helper7 declaration at SOURCE1046–1178: all 43 frozen HEAD lines and all 90 proof lines on each side. I also read the unchanged caller at SOURCE1228–1300 and 1380–1422 and the main common-K introduction at 1471–1485 to check the affected interaction. The author report is explanatory evidence; the proof judgments below come from the actual source calculations and diagnostic targets.

The same reviewer’s prior complete SOURCE3 reading of all 1618 source lines, all 1240 proof lines and all 350 HEAD lines is reused only where bytes and surrounding binding contexts are identical. Its report, verdict, coverage and terminal release were among the 188 exact verified inputs. Its complete source-to-five-original-pages interpretation remains bound to the unchanged p40, p41, p44, p51 and p54 files. No unchanged accepted producer proof, TYPE, kernel check or leaf axiom audit was rereviewed or replayed automatically.

## Exact affected proof judgment

The only changed source lines are 1141 and 1155, corresponding to helper7 local proof lines 53 and 67 and aggregate proof-stream lines 862 and 876. Each old line is “add_le_add_left (abs_sub_le _ _ _) _”; each new line is “add_le_add (le_refl _) (abs_sub_le _ _ _)”. Each replacement adds five ASCII bytes, so the complete source and aggregate proof stream each increase by exactly ten bytes with no LF change.

For SOURCE1141, put A=|P₀(T≤x)−P₀(Tstar≤y)|, a=P₀(Tstar≤y), b=Φ(y), c=Φ(x). The actual second calc step has target A+|a−c| ≤ A+(|a−b|+|b−c|). The real triangle inequality abs_sub_le a b c proves the right component; reflexivity proves A≤A. Applying add_le_add to those two proofs in that order produces precisely this syntactic target. The left summand is preserved on the left, with the target’s grouping intact.

The old native04 diagnostic says the old term instead has type |a−c|+A ≤ (|a−b|+|b−c|)+A. Commutativity makes the numerical inequality equivalent, but the old proof term does not match the displayed calc target by definitional equality. The new two-input addition proof resolves that alignment directly. The placeholders are inferred from the real-valued calc target; they add no assumption and are not proof escapes.

For SOURCE1155, replace A by |P₀(T<x)−P₀(Tstar<y)| and a by P₀(Tstar<y). The same triangle proof with b=Φ(y), c=Φ(x), combined with A≤A as the first add_le_add input, proves precisely the open-CDF target. Both cases are covered in their full old and new binding contexts. No desired CDF conclusion, regularity hypothesis or premise is inserted.

## Complete affected context and payments

The first calc step still compares the actual physical statistic T with the actual uncentered Tstar by the triangle inequality. T uses the same FiniteRows.uStatistic and jackknifeSq, with its exact zero branch when R2 is not positive; Tstar uses the same uncenteredSq and denominator 2√J. The local g is the actual row integral, r=h−g−g, v is the actual residual second moment, s=1+√v, N=n and q=√N. The level is y=τ(x), τ(x)=x/√(1+c_n x²), for n≥3 and x∈[0,1]. The bound and measurable-statistic conclusion are unchanged.

The input comparison to Tstar still costs at most P₀(Z), Z={R2=0}, paid by exp(−cgN)+(1/16+16720s)/q. The uncentered CDF bound costs C·(Lcompact+16(1+4096)(1+y)s/q)+exp(−cgN)+(1/16+16384s)/q. Normal-CDF movement costs 12/N. The subsequent add_le_add uses these three existing facts with exactly the same closed/open comparisons. The final ring equality produces exactly C·(Lcompact+65552(1+y)s/q)+2exp(−cgN)+(1/8+33104s)/q+12/N: 16720+16384=33104 and 1/16+1/16=1/8. Neither changed line alters any fee or coefficient.

The complete measurable-complement argument below is unchanged and valid for atoms, including x=0 and the physical zero branch. The strict tail {x<T} is the complement of {T≤x}, and the closed tail {x≤T} is the complement of {T<x}. Measurability of T supplies measurability of both threshold sets. Probability complement and |−z|=|z| transfer each CDF error exactly, without a continuity or atomlessness premise. Thus the two repaired inequalities feed the same four strict/closed CDF/tail conclusions.

The unchanged helper8 caller passes the same actual hLowModel, obtained from qualified unit265 at the same p,B and cg, into helper7. It absorbs this same raw bound with Lcompact≤8β/N^((p−2)/2), the coefficient 131104 on s/q, the same exponential/polynomial estimates and K=131112C+33117+2/cg. The public proof fixes that K at SOURCE1474 before introducing any model at 1480. All n≥3 and all four errors on [0,1] keep their existing scope.

## Exact maps, reconstruction and complete coverage union

I independently compared every old/new source line and verified exactly the two replacements above. Both five-opcode maps are continuous on both sides and every equal region is actually equal. Source equal ranges are 1–1140, 1142–1154 and 1156–1618; aggregate-proof equal ranges are 1–861, 863–875 and 877–1240. All nine per-proof maps, byte bindings and source/stream positions were verified. The other seven helper proofs and the public main proof are byte-identical.

The full patch contains one hunk for old/new SOURCE1046–1178, with 131 equal context lines, two removed lines and two inserted lines. I reconstructed the complete old and new affected declarations from it, then reconstructed both complete files with the surrounding unchanged bytes; both exact source hashes agree. This is a full affected declaration context, including all binders, not a clipped two-line excerpt.

The independently reconstructed canonical assembly has exactly 28 segments. All eight frozen helper HEADs, their order and universes/binders, PRE18, public HEAD47, CLOSE2 and the eight separator LFs match exact frozen bytes. The complete source is UTF-8 without BOM, LF only, with exactly one final LF. Its only option is the frozen autoImplicit false. No resource override, sorry, admit, new axiom, unsafe or native_decide appears.

The exact previous complete review plus current affected full-context review covers SOURCE1–1618, proof-stream1–1240 and HEAD-stream1–350 with zero holes. Of those, 1616 source lines and 1238 proof lines are unchanged and eligible for exact prior-evidence reuse. The two new proof-term lines have fresh independent judgment, and the full 133-line old/new helper7 context and caller interaction have been read again. The coverage file records the maps and provenance; it does not claim that unchanged 1618 lines were all reread during this repair04 turn.

## Retained mathematical scope

Exact unchanged SOURCE3 proof evidence continues to cover the closed finite numerator algebra; actual retained/deleted arrays and full observation costs without indicator deletion; normalization of the actual scalar engine; globally legal D2 clipping; typed old296 low-energy inclusion; G/H/Z localization and fees; complete early scale split with s>√n handled after the common constant is fixed; actual FiniteRows physical statistic and zero branch; all-n≥3 cost absorption; and actual trim/projection/product-observable-law transport back to the original measurable model. Their complete statements and proofs have no repair04 change.

The public theorem gains no assumption or quantifier change. No residual budget, envelope, mixed moment, independence of g and r, StandardBorel premise, desired-CDF premise or model-dependent K is added. The broader external hSZC contract remains explicit and distinct from the earlier tail hSZ input, and no existence theorem for that contract is claimed. There is no unit264 model-K uniformity claim, and unqualified units273/274 are not dependencies. Original five-page attribution and limits are retained; OQ56/root groups remain OPEN.

## Machine evidence and limit of this verdict

Native04 applies to the old SOURCE3 source 4f3ecd10323122eaf3d35d3f782d893fdfa6294e26f6605aa4e02ffa07707a95, not this new candidate. The exact inspection f218e56efc283029737f871ed502a737580d43cba3fddb7d5f4e125fd1e44fef, 13644 bytes, records natural RC1 after 9.668974505737424 seconds, no object, two emitted type-mismatch errors, 58 retained warning headings, 34953 protected artifacts preserved, all owned processes ended and ownLive empty. Both error contexts were complete and unclipped; no heartbeat or maximum-error-cap text is reported. The raw 17417-byte stdout remains server-only and was not read here.

That failed attempt is not a whole-source default-budget success and does not establish that the later proof is kernel-checked. The repaired candidate has no native or all-owned axiom receipt in this activation. The future acceptance gate remains an exact new native05 success and the same FIRST original object’s actual-owned TYPE, non-theorem FULLVALUE and transitive-axiom packet with the permitted propext, Classical.choice and Quot.sound whitelist, followed by a new explicit SAME FINAL activation. No separate unit274 result qualifies unit275.

## Seals and authority release

Only the six designated review outputs in the new source-review-repair-04 directory are written. No source, frozen declaration, old seal, other owner file, shared implementation or library is changed. Lean, AX, toolchain, server/SSH, transfer, network, Git/API, child, Goal, schedule, sidebar and proxy actions are zero. A local JavaScript string-construction attempt for the deterministic verifier failed before invoking the shell; the corrected read-only verifier completed successfully and did not run Lean or mutate source.

A pre-seal format check found an extra final LF in newly written review payloads; only these new review outputs were normalized to one final LF before sealing. The unique terminal REPAIR04-CHECKPOINT.json will bind all final payloads after a fresh recheck of all 188 inputs. It releases all active SOURCE, review, write, implementation, execution, child and publication authority with heavy/inflight/pendingExternal/writer/child/publication all zero, activeWait=false and ordinaryTurnEnded=true. Only SAME_FINAL_DORMANT remains pending a new explicit FINAL activation and the exact new successful machine packet; it confers no active write or waiting authority.
