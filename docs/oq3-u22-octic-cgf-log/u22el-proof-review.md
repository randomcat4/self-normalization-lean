STATUS: CORRECT
JUSTIFICATION: The exact EL223 frozen theorem is implemented in full. Its finite logTaylor residual is exactly the stated eleven-term weighted polynomial; every term has weighted degree at least nine and satisfies the independently qualified EK222 tail interface. The positive constant is chosen before the radius and complex terms. Complete source, actual type, required values and recursive axiom coverage agree with the same first successful server object. This verdict certifies the frozen generic polynomial bound only.

# Independent complete final review: OQ3 EL223

Reviewer: /root/oq3_el223_final_review; fresh independent final reviewer, separate from the author and declaration owner. No child was spawned. The only review output written is this file. The review uses math-theorem and its prompt-library, openai-workflow and lean-verification references, subject to the project's stronger server-only and exact-evidence-reuse rules; math-ultra was not used.

## Exact reviewed version and evidence

- Module: Shao.OQ3.ComplexLogTaylorOcticCorrection.
- Source, fully read lines 1-122: drafts/oq3/u22el-source.lean, SHA256 737c7cb733adaeecd69ad1bcd9944b820631e33f9946b36a8de01be2b61f7788, 6147 bytes, 122 LF, zero CR. The live server source and preserved source-02.lean match these exact bytes.
- Frozen declaration, fully read all 14 LF: u22el-frozen-declaration.lean.txt, SHA256 876158f1dd80cac31933cc12be7a84a9f4958b54ed5c612fe3b13b8fdfe0911f, 828 bytes. Its complete text equals the source declaration before `:= by`, including both statement lets.
- Frozen scope, fully read from the server run's scope.md: SHA256 50b8ab9d53595d277f3de3eb596f0dab3f09cbd09d74c913ee1d39982b7e36ed, 1659 bytes, 26 LF. No assumption or result scope was altered.
- Complete actual type: u22el-actual-types.txt, SHA256 21d77029ed6c44a37d1ba6c9380d3d44f39bb75ef6b0f6276ef333cb7ae1350f, 1747 bytes, 35 LF, all read. Its full bytes occur in the server audit.log.
- Complete audit program, all 47 LF read: u22el-Audit.lean, SHA256 de26f31d006c6d45e6b0197b506612176a93a078dfa51b0e7caac801b17265ea, 2007 bytes.
- Receipt: u22el-receipt.json, SHA256 a346787eba81dd9ff6c9824dacb897449fd2b33ac5b3e2d84497beba6be2b996, 7677 bytes, 265 LF. Audit record: u22el-audit-record.json, SHA256 3028e301b3d913cf70e1aa8bcff48426335166ae45f5953315d5541b3964a382, 3023 bytes, 103 LF. Build history: u22el-build-history.json, SHA256 b43314b0a67c08aa70169fc5df5470aa1155f81cb97d5fab9f613effccd67bc9, 4312 bytes, 162 LF. These evidence records were read and their local/server hashes agree.
- Dependency-source binding: u22el-dependency-source-binding.json, SHA256 f0fc5633dd808d01c70b4028c43f45f9a74633dc58e4b1bf3b7a4fcb7831dba6, 225 bytes. Qualified dependency binding: u22el-qualified-dependency-binding.json, SHA256 dfe4698c5b30d7bb6f80d95af9a94142a75e190254310c2283298b0d4b56c00a, 1102 bytes. Both were read completely.
- Proof design, all 61 LF read: u22el-proof-design.md, SHA256 aedf2f63562cb676a745d8f7d9808071ef1e86afbba8502b1822fe572898e017. Its lines 3-5 describe the earlier pre-implementation checkpoint; they are historical, not the current implementation or machine state. The full current source and source-bound receipts are authoritative. The implemented local values and residual agree with the design.
- First original object: .lake/build/lib/lean/Shao/OQ3/ComplexLogTaylorOcticCorrection.olean, SHA256 8d9bcc5b99df0218feaeaa7c482962a12979b884c10eb1ce02200ded499d2680, 4991256 bytes. Read-only server hashing observed this same object twice; no compilation was run by the reviewer.
- Server worktree: /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3. Existing run directory: /root/rivermind-data/shao-lean-20261021/runs/oq3/u22el-20261027. All observations used the existing tools/server.py broker read-only.

## Statement fidelity, quantifiers and both lets

The theorem has seven arbitrary real constants A,B,C,D,E,F,G, each explicitly assumed nonnegative. For these constants it asserts existence of a real K with 0<K, followed by every real r with 0<=r<=1, followed by every seven complex terms a,b,c,d,e,f,g with norm bounds A*r^2 through G*r^8 in order. There are no hidden positivity, nonzero, independence, probability-law, analyticity or smallness hypotheses.

Both frozen statement lets were checked literally, including signs, brackets, divisions and coefficients:

```
P = a+b+c+d+e+f+g
Q = a+b+c+d+e+f+g
    -(a^2+2*a*b+2*a*c+b^2+2*a*d+2*b*c+2*a*e+2*b*d+c^2)/2
    +(a^3+3*a^2*b+3*a^2*c+3*a*b^2)/3-a^4/4
```

The conclusion is precisely norm(Complex.logTaylor 5 P - Q)<=K*r^9. The actual type's pretty-printed `have P := ...; have Q := ...` represents these same statement lets; it adds no hypothesis and changes no quantifier. Its seven separate norm assumptions and both radius inequalities match the freeze completely.

Q retains all and only weighted-degree <=8 terms of P-P^2/2+P^3/3-P^4/4 when a,...,g have weights 2,...,8. For the quadratic part the allowed unordered weight pairs are (2,2),(2,3),(2,4),(3,3),(2,5),(3,4),(2,6),(3,5),(4,4); off-diagonal pairs have factor two, matching Q. The cubic retained multisets are (2,2,2),(2,2,3),(2,2,4),(2,3,3), with factors 1,3,3,3. The only retained quartic is (2,2,2,2), yielding a^4. All seven linear terms are retained. This verifies the semantic truncation description independently of merely matching Lean text.

## All proof-local data: nine factors and eleven monomials

For review notation only, put H=d+e+f+g, U=e+f+g, V=f+g, W=b+c+d+e+f+g, Y=c+d+e+f+g and T=2*b+Y. These are precisely the source's literal expressions; no new theorem assumptions are introduced. All entries of weights, bounds and z (source lines 23-25 and 101-102) were checked:

| j | z j | weights j | bounds j |
|---|---|---|---|
| 0 | a | 2 | A |
| 1 | b | 3 | B |
| 2 | c | 4 | C |
| 3 | H | 5 | D+E+F+G |
| 4 | U | 6 | E+F+G |
| 5 | V | 7 | F+G |
| 6 | W | 3 | B+C+D+E+F+G |
| 7 | Y | 4 | C+D+E+F+G |
| 8 | T | 3 | 2*B+(C+D+E+F+G) |

The complete coefficient vector and all 99 entries of powers:Fin11->Fin9->Nat (lines 26-39) match the following. The degree column is the exact sum of weights j * powers t j, not an inferred ordinary degree.

| t | coeff t | powers row in j=0,...,8 order | monomial including coefficient | weighted degree |
|---|---|---|---|---|
| 0 | -1 | [1,0,0,0,0,1,0,0,0] | -a*V | 2+7=9 |
| 1 | -1 | [0,1,0,0,1,0,0,0,0] | -b*U | 3+6=9 |
| 2 | -1 | [0,0,1,1,0,0,0,0,0] | -c*H | 4+5=9 |
| 3 | -1/2 | [0,0,0,2,0,0,0,0,0] | -H^2/2 | 2*5=10 |
| 4 | 1 | [2,0,0,1,0,0,0,0,0] | a^2*H | 2*2+5=9 |
| 5 | 1 | [1,0,0,0,0,0,0,1,1] | a*Y*T | 2+4+3=9 |
| 6 | 1/3 | [0,0,0,0,0,0,3,0,0] | W^3/3 | 3*3=9 |
| 7 | -1 | [3,0,0,0,0,0,1,0,0] | -a^3*W | 3*2+3=9 |
| 8 | -3/2 | [2,0,0,0,0,0,2,0,0] | -3*a^2*W^2/2 | 2*2+2*3=10 |
| 9 | -1 | [1,0,0,0,0,0,3,0,0] | -a*W^3 | 2+3*3=11 |
| 10 | -1/4 | [0,0,0,0,0,0,4,0,0] | -W^4/4 | 4*3=12 |

All powers are natural numbers and all coefficients are complex constants with the displayed rational values. The finite vectors really have sizes 9 and 11; the proof's complete fin_cases enumeration at lines 105-106 establishes 9<=each exact degree. No row or high-degree contribution is dropped.

## Complete proof review by bearing step

Lines 40-47: hbounds checks each of the nine nonnegative bound entries by the seven stated nonnegative assumptions and arithmetic. K0 is exactly the finite sum over Fin11 of norm(coeff t) times the product over Fin9 of bounds j raised to powers t j. Each factor and hence each summand is nonnegative; hK0 proves this without additional assumptions.

Lines 42-49: weights, bounds, coeff, powers and K0 are defined before `intro r ... a ... g`. Thus K0 and K=K0+1 depend only on A,...,G and fixed finite data. hK0 implies K>0, including when all constants vanish. Choosing K before r and terms satisfies the essential uniform quantifier; it is not a radius-dependent or term-dependent witness.

Lines 50-60: the local hsum proves the finite-sum tail inequality for arbitrary Fin m. First apply norm_sum_le, then the supplied component bounds. With 0<=r<=1 and s<=ww j, pow_le_pow_of_le_one gives r^(ww j)<=r^s in the correct direction. Multiplication by ZZ j preserves order because hZZ j>=0. Sum_le_sum and sum_mul give norm(sum zz)<=(sum ZZ)*r^s. This is valid at r=0 and r=1; no division by r or strict radius premise occurs.

Lines 61-78: each hh instantiation of hsum was checked completely. h5 uses [d,e,f,g], bounds [D,E,F,G], weights [5,6,7,8], s=5. h6 uses [e,f,g], [E,F,G], [6,7,8], s=6. h7 uses [f,g], [F,G], [7,8], s=7. The hZZ, hzz and degree premises in each finite branch are exactly the original sign/bound assumptions or closed natural inequalities. simp with Fin.sum_univ_succ/add_assoc only rewrites the finite sums.

Lines 79-90: h3 similarly uses [b,c,d,e,f,g], [B,C,D,E,F,G], weights [3,4,5,6,7,8], s=3; h4 uses [c,d,e,f,g], [C,D,E,F,G], [4,5,6,7,8], s=4. All branches and arithmetic hypotheses are explicitly supplied, including the full g tail. These bounds are the W and Y rows, respectively.

Lines 91-100: ht first bounds norm(2*b+Y) by norm(2*b)+norm(Y). norm_mul and norm(2:Complex)=2 give 2*norm(b). The b bound and h4, followed by r^4<=r^3 and nonnegativity of C+D+E+F+G, yield (2*B+(C+D+E+F+G))*r^3. This justifies the ninth row's weight 3 and its factor two. ring only rearranges the scalar bound. There is no missing estimate on the doubled b term.

Lines 101-104: hz performs all nine finite cases. The first three are ha,hb,hc; the remaining six are h5,h6,h7,h3,h4,ht with exactly the matching bounds and weights. No assumption concerning a tail is imported as an additional hypothesis.

Lines 105-106: hdegree enumerates all eleven rows using the complete weights and powers matrices. The resulting lower bounds are exactly the degree table above. Norm_num performs exact finite natural arithmetic.

Lines 107-108: hlog is the exact identity Complex.logTaylor 5 z=z-z^2/2+z^3/3-z^4/4. The pinned Mathlib definition at Complex/LogBounds.lean:67 is `fun z => sum j in range n, (-1)^(j+1)*z^j/j`. For n=5, j ranges from 0 to 4, not 1 to 5. The j=0 summand is zero because Lean's division by zero is total and equals zero, including its numerator z^0. Terms j=1,2,3,4 have signs +,-,+,- and denominators 1,2,3,4. No analytic-log equality or branch assumption is asserted. Expanding this finite definition via norm_num and ring is exact symbolic proof.

Lines 109-113: heq is an exact polynomial identity for all complex terms. An independent algebraic expansion confirms all coefficients and signs. If L2 and L3 denote exactly the numerator polynomials of Q, then

```
R2 = P^2-L2 = 2*a*V+2*b*U+2*c*H+H^2
R3 = P^3-L3 = 3*a^2*H+3*a*Y*T+W^3
R4 = P^4-a^4 = 4*a^3*W+6*a^2*W^2+4*a*W^3+W^4
logTaylor 5 P-Q = -R2/2+R3/3-R4/4.
```

For R2 expand P=a+b+c+H and split off the retained cross terms with d and e; the omitted a-tail is exactly V=f+g and omitted b-tail is U=e+f+g. For R3 use P=a+W, W=b+Y and W^2-b^2=Y*(2*b+Y)=Y*T. For R4 use the binomial expansion of (a+W)^4. Substitution yields exactly the eleven rows above. The source rewrites hlog, unfolds both statement lets, expands the finite vectors/sums/products and closes by exact norm_num/ring. This is a universally quantified identity, not numerical testing or finite sampling of term values.

Lines 114-119: congrArg norm heq replaces the residual norm by the complete finite polynomial norm. The EK222 call takes z,bounds,weights,coeff,powers,d=9,r with hr0,hr1,hbounds,hz,hdegree in exactly the consumed interface's order. Its right side is definitionally K0*r^9. Finally K0<=K0+1 and r^9>=0 give the required (K0+1)*r^9. There is no dropped coefficient norm or unbounded intermediate quantity. Every local value and local proof used in the theorem, including the per-tail hh bindings, has been covered above.

## Qualified dependency coverage and exact reuse

The only project import is Shao.OQ3.ComplexWeightedMonomialRemainderBounds (EK222); the other direct import is pinned Mathlib.Data.Fin.VecNotation. EK222 directly imports pinned Mathlib.Analysis.SpecialFunctions.Complex.LogBounds. No EF/EH module or EM224 consumer is an EL223 dependency.

The complete two EK222 public declaration heads were read from the exact server source without rereading their old proofs: complex_weighted_monomial_bound for a finite complex monomial at nonnegative r, and complex_weighted_polynomial_tail_bound for finite complex coefficients/exponents with 0<=r<=1 and every weighted degree>=d. Both bind arbitrary finite types, natural weights/exponents and nonnegative real bounds; the latter is the direct call here. Its coefficient-sensitive bound is exactly `(sum t, norm(c t)*prod j,A j^(p t j))*r^d`. EL223 satisfies every premise as reviewed above. The monomial interface is the qualified underlying public helper; no strengthened conclusion is assumed.

All 20 LF of EK222 actual types were read, including its two public theorems and generated complex_weighted_monomial_bound._simp_1_1 of type (a^m)^n=a^(m*n) for any monoid. The two public heads have the standard three axioms; the generated helper has AXIOMS []. This is all3 actualTYPE/0VALUE coverage, matching COMPLETE_QUALIFIED and parentFullReportRead=true, not a partial public-only review.

Exact reused bindings, independently rehashed without reading old proof/review content:

- EK222 source SHA256 0b3e9eac03a3ad7124ff0b4cf87a4a74deaeead2dfeb630c5e57106d570317c1 (2270 bytes, 54 LF); local and live server bytes match the qualification.
- EK222 first original object SHA256 3c6dd3a6d5560d8d44469d391f1d5ba8701f75b802eed958a62d89be86b39fd8 (87776 bytes), observed live and equal to the qualified binding.
- EK222 completed independent review SHA256 d21e469b28e1141e8fc76cb6b645c55c7aac50767cfbe90b725b634d47ca25a2 (21029 bytes, 119 LF); reviewer /root/oq3_ek222_final_review released; parentFullReportRead true.
- EK222 receipt SHA256 ca42980ece616ce7c7ad3cafdf9297775275890e52b79aa86828e904611a4c20; actual types SHA256 841cdb7ceb19fc18419926c4d2fa7cf3db6c839c2460cd5ea8e732d40ffc3ff2 (1126 bytes, 20 LF).
- u22ek-qualification.json and EL223's qualified-dependency-binding are identical SHA256 dfe4698c5b30d7bb6f80d95af9a94142a75e190254310c2283298b0d4b56c00a. This explicitly covers complete final review/all actual types/zero required values/first original object and no successful-check replay.

The old EK222 proof body and old review content were not reread, and no old producer/kernel/axiom check was replayed. Hashing old files solely verifies that the already qualified evidence is the exact consumed version.

## Boundary and degeneracy attack

At r=0 each original norm bound has a strictly positive exponent and right side zero, forcing a=...=g=0. Thus P=Q=0 and logTaylor 5 0=0, so the target is 0<=0. Zero exponents in the finite monomial representation mean ordinary x^0=1; every row still has positive total weighted degree and contains a vanishing positive-power factor, so this representation does not introduce a 0^0 gap.

At r=1 all power-reduction inequalities become equalities; the triangle/product estimates still give the finite constant K, independent of the terms. If any or all of A,...,G are zero, the corresponding term vanishes; all tail bounds remain nonnegative and the proof divides by none of these constants. If all are zero, K0=0 and the chosen K=1 remains strictly positive. No special sign restriction on the complex terms is used. Negative residual coefficients and cancellation are safely handled by norm(coeff t), including -1/2,-3/2,-1/4. The theorem remains valid for arbitrary allowed phases and large coefficients at r=1.

The statement does not require P to lie in a disk for an analytic logarithm. Complex.logTaylor 5 is a globally defined finite polynomial. Introducing a small-P or nonzero-1+P premise would change this theorem unnecessarily; none is used.

## Kernel, all actual owners, axioms, pins and failure provenance

Native01 used source f29167ab75f6e51471abeebcdec2529b36003f98b483e0126a118274c49c083b (6147 bytes, 122 LF) and ended naturally RC1 in 2.887330386787653 seconds. Its full 398-byte build-01.log, SHA256 33280ccca229627516693e33e400d74c8db6224050340476cfd268ddebcdee53, reports nonexistent Mathlib.Data.Matrix.Notation object at the import. Read-only inspection confirms the corresponding source module does not exist at the pinned mathlib commit. This is an invalid import name, not a missing-cache request. The failure is retained.

The complete source01-to-source02 diff is one line: line 2 replaces `import Mathlib.Data.Matrix.Notation` by `import Mathlib.Data.Fin.VecNotation`. Byte comparison after that exact replacement yields identical files, so all theorem/statement/proof bytes are unchanged and both source snapshots remain 6147 bytes. Fin.VecNotation source and compiled object exist. No cache hydration or dependency producer replay was needed.

Native02 is the first successful complete native check, RC0 in 12.593869935721159 seconds, bound to the current source and first object above. Its complete 969-byte build-02.log SHA256 ef8dc61e80efb0e76c2b8b110e52869f25b032cc363a032adb9ac0d0a37b2cf0 has no errors. It retains the existing mathlib local-changes warning and two proof locations (108,113) with overlapping unused-tactic/unnecessary-sequence-focus linter diagnostics for `<;>`; these are style warnings. The proof is sealed without cosmetic edits or rechecking.

The same-first-object all-owner audit ended RC0 in 5.659751737490296 seconds. Complete audit.log SHA256 ccc5cd9b4170689f53b2c8057ec51e3e766c09598332457575df433e9091d78f, 1999 bytes, 42 LF, was read. It contains exactly one owned DECL/TYPE, KIND theorem, no VALUE, U22EL_FROZEN_DEFINITIONS 0, FROZEN_THEOREMS 1, ALL_THEOREMS 1, ALL_DECLARATIONS 1 and AXIOM_GATE PASS. Counts are derived from actual owner enumeration, not copied from the public declaration count alone.

Audit lines 23-40 enumerate every environment constant owned by this module, including any private/generated owner if present. They reject new project axioms, collect recursive axioms for every actual owner and reject anything outside [propext, Classical.choice, Quot.sound]. The only actual owner is Shao.OQ3.complex_log_taylor_octic_correction_bound; its exact actual type uses those three standard axioms. There are no separate module-owned definition values to review. All proof-local lets still received the complete source-value review above. Source scanning found no sorry, admit, added axiom, unsafe or native_decide; the recursive audit independently excludes hidden sorryAx or other new axioms.

Read-only server observations confirm lean-toolchain=leanprover/lean4:v4.36.0-rc1 and mathlib HEAD=807d3836b165983210ee2ecf3cd28f239436949c through cache-overlays/shared-v34/packages/mathlib. The consumed LogBounds.lean and Fin/VecNotation.lean exactly equal their bytes at that pinned Git commit, with hashes d3711d5d5b528b8d1733d531d5ae78bc77d13a68079a7243af3251abc48380f7 and 5c636e6d665ce3a6bd7ad3ba5c242371515aa7d1888c8466f71b7d662264cd17. Their existing compiled object hashes are 216aff6dbc47d6b7f350f090f48c0d1e983edae8c6c623dc6d0ce123eb16c226 and 1653f3b1390153c3ee28c6b1019515aa61c732effc9b9974ea689d2cd06754f2, respectively. The historical local-changes warning therefore does not conceal a changed consumed definition or notation source.

Receipt resource records use phase ROOT_OQ56_OQ3_40, CPU36-39,44-47 and native -M8192 -j4. Their nested memory helper retains its historical phase39 policy name, with project140GiB/other-system60GiB/aggregate180GiB/hard200GiB and the existing c12-heavy.lock reserved to OQ3. Current AGENTS/REGISTRY confirm explicit OQ3 resumption, same sole lead and child ceiling1. The reviewer ran only byte/log/interface/pin observations, no Lean, AX, build, upload, publication, cache mutation or resource change; no new heavy admission was required.

## Original-source scope and exclusions

Original read-only C:/game/shao/current/oq3/proofs/r2/report.md lines 1-158, including full sections 1-2, was read. It concerns a fixed x in (0,1), actual tilted laws and uniform weak-Cramer with strict 0<beta<2/5, actual moment/covariance/saddlepoint hypotheses and an externally attributed Angst-Poly order-six engine. EL223 is a supporting finite complex polynomial estimate only. It neither imports that external conclusion as a fresh axiom nor establishes it.

The generic letters A,...,G in EL223 are seven real norm-bound coefficients; they are not the historical OQ3 branch labels. The letter E here is only one real bound and is not a replacement for an original common event. No original same-E/same-law/actual-rho packet, p54 repair, strict beta range or external-result attribution is changed by this source. Later consumers must preserve those original bindings themselves.

This proof does not identify actual CGF/moment/cumulant coefficients, combine canonical logarithm remainder estimates on a common radius, prove an actual-law logarithm identity, produce an order-six characteristic-function expansion, or close inversion/exterior/B-D/root results. Those remain OPEN. EM224 and any later actual coefficient consumer are outside this review and receive no inherited review verdict. Correctness of this generic lemma must not be reported as mathematical completion of the OQ3 root.

## Final determination, telemetry and release

CORRECT for the exact frozen EL223 declaration and current source SHA256 737c7cb733adaeecd69ad1bcd9944b820631e33f9946b36a8de01be2b61f7788. Full source-to-statement/proof/local values/all1 actualTYPE/0 requiredVALUE/recursiveAX review is complete, with exact qualified EK222 interface reuse and the original source-bound server native/audit evidence. No critical gap, assumption change or uncovered owned declaration was found. This is a correctness determination for an auxiliary theorem; novelty or root completion is not claimed.

Prescribed model/effort: gpt-6.1-sol/xhigh, fresh reviewer. Actual model and effort telemetry are not independently exposed in this child context; they are not guessed from the prescription. Structured telemetry: {"prescribedModel":"gpt-6.1-sol","prescribedEffort":"xhigh","freshContext":true,"actualModel":null,"actualEffort":null,"inputTokens":null,"cachedInputTokens":null,"outputTokens":null,"reasoningSubsetTokens":null,"telemetryUnavailableReason":"No actual model/effort/token counters exposed to this reviewer runtime"}. No subscription percentage or purchased-credit allocation is inferred.

Release: after writing this sole report, this reviewer stops. It retains no source/server/publication/execution authority, no pending operation and no child. No cross-chat message was sent. Exclusive write authority to this report is released upon final delivery to the parent.
