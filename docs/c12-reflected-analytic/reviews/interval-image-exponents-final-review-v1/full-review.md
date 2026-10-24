STATUS: CORRECT
JUSTIFICATION: The final frozen unit faithfully formalizes the source interval image exponent algebra, integer-index nonnegativity, actual first spatial derivatives, affine slope absorption, and both signed tail comparisons. Every production proof, all 23 complete elaborated owner types and both complete definition values were reviewed. The exact recorded kernel and recursive-axiom evidence is bound to the reviewed source and installed object. There are no critical gaps within this frozen target.

Unit 53, `Shao.C2.IntervalImageExponents`. Independent reviewer: fresh prescribed gpt-6.1-sol / xhigh, separate from the author; no subdelegation, production edit, Lean invocation, audit replay, cache write, or execution lease. The math-theorem final verification protocol and current streamlined acceptance were applied. Runtime acknowledgement is in `runtime-ack.json`. Input, cached input, output and reasoning-subset usage are unavailable and remain null.

## Exact reviewed version and evidence

| Item | SHA256 |
|---|---|
| Complete source, 7132 bytes / 156 lines | a2ade7b54d268c9d9052d995309eceeaee3db8899fea95f2138fb2e2871d157b |
| Successful output and installed object, 1201280 bytes | d7cf70b797a7567622e110104b1bb94a5144a77eef647646873f9293cc488072 |
| Current V2 declaration freeze | b0149a47fb7a205a7a63ebe635d121566a484d7449015fbc7b7fdf2e5436463f |
| Author receipt | bebde98e69f421c0e39e454bfd6eb5e8149ace7eb8a913ab36bac9e45e398ab4 |
| Complete 23 actual-type export, 30090 bytes | 521ed464e1dfa09a1388c4d688150407999a88ef00dea082da7bc6eafb837fc7 |
| Complete two-definition value export, 3050 bytes | fcc40d65a3003e566545c598aa8689ae8ad90b0c9fb66d0effff967f1644d4d6 |

Read-only server observations confirmed every one of the 18 receipt-listed artifact hashes and sizes, local packet matches for all seven packet artifacts also listed in that receipt, current production source = successful attempt005 snapshot, and output object = installed object. Every complete type/value export block equals its corresponding full audit-log block. The owner set, type set and definition-value set agree exactly. `OwnedAudit.lean` selects by actual module ownership, without namespace filtering, and calls recursive `Lean.collectAxioms` for every owner. The 23 owners comprise 21 theorems (13 source theorems and eight generated theorem constants) plus two definitions; there are no other kinds or omitted other-namespace owners. Every result uses only propext, Classical.choice and Quot.sound.

The reused attempt005 kernel receipt and audit receipt both have exit 0. Toolchain is leanprover/lean4:v4.36.0-rc1, mathlib is 807d3836b165983210ee2ecf3cd28f239436949c, and the package path resolves to the accepted shared-v34 view. Branch is author/c12-interval-gaussian-v71 at b7c9d5d80f39b2eb2e942a114c2a90fff940dea3. The receipt records the C12 lock, CPUs 14–17, -M8192 and -j4. Source bytes are UTF-8 without BOM, LF only. No accepted old module or successful gate was replayed.

## Source fidelity and boundaries

I fully read the read-only supplement lines 4255–4300 and context 4192–4253. Whole-source hash is b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd. The definitions preserve exactly A_m = 8m²a²+4ma(z−y) and B_m = 2(y+(2m+1)a)(z+(2m+1)a). The derivative variable is the starting spatial endpoint y, with a,z,m fixed. Actual `HasDerivAt` is used, not an assumed derivative or a formal coefficient label.

The source assumes a>0 and interior endpoints. The nonnegativity and tail theorems validly extend those estimates to the closed endpoints |y|,|z|≤a. They therefore provide the exponent geometry needed at walls, but do not prove wall traces of an infinite series. A_0=0 is unconditional. Integer discreteness is retained for general exponent nonnegativity: replacing the integer index by an arbitrary real one would be false (a=1,y=1,z=−1,m=1/2 makes A negative). Tail statements use real m≥0 or real m≥1; the proofs directly establish these stronger inequalities, so every intended integer application remains covered.

For B, B_0=2(a+y)(a+z) is the lower-wall base and B_−1=2(a−y)(a−z) is the upper-wall base. The reflected B tail is indexed −m−1, including −1 at m=0. The reflected A tail is indexed −m, including −1 at m=1. Both source base factorizations 2(a−y)(3a+z) and 2(a+y)(3a−z) retain the correct factors and signs. The tails do not need T≤a²; that condition belongs to the later summation application, so its omission here strengthens a correct algebraic statement rather than weakening the source result.

Closed endpoints can make factors and exponents zero. The proofs use nonstrict inequalities and handle those equalities. The generic slope lemma also covers C=0 and d=0. Identities and derivative results are valid for all real arguments because the definitions are polynomials; the positive-width geometric bounds do not claim the source's zero-width probability extension.

## Complete mathematical and declaration coverage

All 13 complete frozen mathematical heads, both complete definition values, imports and surrounding context were compared with the final source. All 30090 bytes of the unelided actual-type export and all 3050 bytes of the unelided value export were emitted in full and read. No sampling, dictionary compression or omitted binder/instance context was used. The real arithmetic, order, powers, integer casts, absolute values, real square root and full real normed-space `HasDerivAt` instance arguments agree with the intended scalar statements. Per-owner exact type-block hashes, full-type hashes, full definition-value hashes, source locations and individual review reasons are in `full-review.json`.

- `imageA`: Complete definition has four real arguments in source order a,y,z,m and value 8*m^2*a^2+4*m*a*(z-y). Both natural powers are 2; the sign of d=z-y is preserved. No domain predicate is built into this polynomial.

- `imageB`: Complete definition has value 2*(y+(2*m+1)*a)*(z+(2*m+1)*a), with the common odd shift and both endpoint factors. It is not a squared single factor.

- `int_abs_ge_one`: Integer discreteness is essential: m!=0 and m>=0 imply m>=1; the other integer branch implies m<=-1. Exact casts preserve these inequalities, and the two absolute-value branches give the stated real absolute value bound.

- `imageA_zero`: Unfolding the full imageA definition at real index zero removes both terms. No endpoint or width premise is required.

- `imageA_nonneg`: The m=0 case uses the exact zero identity. Otherwise r=abs((m:Real))>=1 and abs(z-y)<=2*a. Thus m*(z-y)>=-r*abs(z-y)>=-2*r*a. The displayed decomposition into 8*a^2*(r^2-r) and 4*a*(m*(z-y)+2*r*a) consists of nonnegative terms. The proof uses the closed endpoint hypotheses exactly and retains the integer index.

- `imageB_nonneg`: For integer m>=0 the common shift is at least a, making both factors nonnegative; for the complementary integer branch m<=-1 it is at most -a, making both factors nonpositive. Multiplying the two factors and the positive constant 2 gives nonnegativity. No false real-index generalization is present.

- `imageA_affine_identity`: With c=-4*m*a and d=z-y, expansion of ((c-d)^2-d^2)/2 equals 8*m^2*a^2+4*m*a*d. The minus sign in c and the cross term agree. The ring proof requires no positivity premise.

- `imageB_affine_identity`: Writing k=(2*m+1)*a, c=2*(z+k), d=z-y gives c-d=y+z+2*k; the difference of squares divided by 2 is exactly 2*(y+k)*(z+k). The full identity is valid for all real arguments.

- `imageA_hasDerivAt`: The constant quadratic term has derivative zero. The derivative of z-w is -1 and left multiplication by 4*m*a gives -4*m*a. HasDerivAt is the ordinary real derivative at y with a,z,m held fixed. Final function extensionality plus pointwise simplification and ring normalization establishes the exact full function, rather than only a value at y.

- `imageB_hasDerivAt`: The first factor w+k has derivative one; the other endpoint and shift are fixed. Multiplication by 2*(z+k) yields the exact constant derivative 2*(z+k). The commuted factor order is justified pointwise after funext. No differentiability assumption is imported as a premise.

- `imageB_positive_tail`: For real m>=0 the exact difference from B_0+8*m^2*a^2 is 4*m*a*(y+z+2*a). Each factor is nonnegative because y,z>=-a and a>0. The stronger real-index and m=0 statements validly include the source integer m>=1 application.

- `imageB_negative_tail`: Reflection (y,z)->(-y,-z) preserves both absolute-value bounds and maps B_m to B_(-m-1), and B_0 to B_-1. The complete conversion is polynomial equality; the negative index is -m-1, not -m. Real m>=0 covers all remaining negative integer B terms.

- `imageA_positive_tail`: The exact difference from B_0+8*m*(m-1)*a^2 is 2*(a-y)*(3*a+z)+4*(m-1)*a*(z-y+2*a). Closed endpoint geometry gives a-y>=0, 3*a+z>=2*a>0, and z-y+2*a>=0; real m>=1 gives m-1>=0. At m=1 the source base difference is exactly preserved.

- `imageA_negative_tail`: The same endpoint reflection maps A_m to A_-m and B_0 to B_-1. In particular the base term becomes 2*(a+y)*(3*a-z), with correct signs. All hypotheses survive reflection, and m>=1 covers the negative integer A branch.

- `affine_slope_abs_bound`: Let x=abs(c), q=abs(d), s=sqrt(2*C). The identity and c*d<=abs(c)*abs(d) give x^2<=2*x*q+2*C; C>=0 gives s>=0 and s^2=2*C. If x>2*q+s then x>0, s*x<x^2-2*x*q, while s^2<=s*x, contradicting the first inequality. The proof includes C=0 and d=0 and introduces no sign assumption on c or d.

The eight generated constants were also reviewed in full, rather than only counted:

- `imageA.eq_1`: Generated equation theorem expands imageA to exactly its full definition for all four real arguments. Its numeral certificate references agree with the reviewed values.

- `imageB.eq_1`: Generated equation theorem expands imageB to the exact two factors and leading 2 for all four real arguments. Both occurrences of the odd shift are unchanged.

- `imageA._proof_1`: Generated numeral certificate type is Nat.AtLeastTwo (7+1), certifying the real numeral 8. No mathematical premise or value is hidden here.

- `imageA._proof_2`: Generated numeral certificate type is Nat.AtLeastTwo (3+1), certifying the real numeral 4. Its full type was read.

- `imageB._proof_1`: Generated numeral certificate type is Nat.AtLeastTwo (1+1), certifying the real numeral 2 in the definition. Its full type was read.

- `int_abs_ge_one._proof_1_1`: Generated integer arithmetic theorem states that m!=0 and 0<=m are incompatible with not(1<=m). The full quantified Int type is correct.

- `int_abs_ge_one._proof_1_2`: Generated integer arithmetic theorem states that not(0<=m) is incompatible with not(m<=-1). It uses only integer discreteness and requires no omitted hm premise.

- `imageB_nonneg._proof_1_1`: Generated integer arithmetic theorem is the corresponding negative-integer branch not(0<=m) -> not(m<=-1) -> False. Its scope and complete type agree with the source branch.

Generated theorem proof certificates were not expanded: the complete production proofs, complete actual types, exact kernel object binding and recursive axiom audit cover them according to the current audit-output boundary. All non-theorem values were fully read, with no exceptions.

## Import-only refreeze and all failed attempts

V1 hash 3bfa55da2045bf275fc26e6f090ebbd1566f7a8a93a30aae65d4140f88b0f670 differs from V2 only by replacing the nonexistent `Mathlib.Tactic.Omega` import with `Lean.Elab.Tactic.Omega`. The installed core object exists, hash 87258147a03a21caba06688bd877297248129a1528e1c32e598de1a11ad09d8b, and predates the attempts. No cache build was needed. Full source projection for attempt001 equals V1; every attempt002–005 projection equals V2. Thus all 13 mathematical heads, both full definition values and the remaining context are unchanged throughout.

The local V2 freeze and explicit import-only record have modification time 2026-10-24 10:37:21.656815 UTC, before attempt002's source snapshot at 10:37:35.668861 UTC. The original freeze file was created at 10:35:16.8485608 UTC, before attempt001. Server freeze copies were archived after success; their later timestamps are not used as pre-gate evidence. These are ordinary filesystem provenance observations, not a cryptographic trusted timestamp.

The complete attempt001 source, complete final005 source, all unelided successive full-source diffs and all five full logs were read directly through read-only responses. This covers the entire failed-version proof context through exact unchanged-source comparison plus every changed line. Raw logs and failed source snapshots remain remote and were not copied into this workspace.

| Attempt | Full-source SHA256 | Complete observed result / exact delta |
|---|---|---|
| 001 | a70b83c808f62bfd8ad6df7bf55cbde8f1f98a3b5d827c000a302c0aed0a1a22 | Missing Mathlib.Tactic.Omega object; the only 001→002 change is the import. |
| 002 | 4944594b6ce42248d57be6f86978e2bfd53e9944ffb9d8d7cbd2e8d31c0872e1 | `dsimp` made no progress in the two derivative conversion branches. |
| 003 | 7513c14b4efd04bdb6fe60fd30ebd065860ed73f13715183a389fde023a100e9 | Replacing those two `dsimp` calls by `simp` still made no progress. |
| 004 | dbf93321b7d4abefdc98e23d9c40e40977e94318167d58e2e55197241fba4b65 | Making simplification optional exposed the two complete function-equality goals; scalar ring normalization alone could not close them. |
| 005 | a2ade7b54d268c9d9052d995309eceeaee3db8899fea95f2138fb2e2871d157b | `funext` followed by pointwise simplification and ring normalization closes the exact functions. Only nonlogical linter warnings remain. Kernel and whole-owner recursive axiom receipts pass. |

No premise or definition was changed to repair a failed proof. These attempts concern import availability and function-equality elaboration only. The read-only interface inspection itself initially found that remote `rg` was unavailable; Python file traversal resolved that textual lookup. It did not run Lean or affect a proof gate, and no uncertain operation was replayed.

## Dependencies and evidence reuse

The imported unit32 HalfLineSpatialProfiles source is exactly 748ef00e57c2d88ded95208cd4e961916d261b99f91894c2bd15014637e81729 and its output/installed object is exactly 2533120d2cf347520ff211d04e08e6e5028d875e16e4cd34738e3b57faeb1635. Its qualified complete independent review is CORRECT, hash 207cdaed8fd92e51545abfdc8cbebb5e31e83392f457a40f2b18fcb788a95b81. That evidence is reused without re-reviewing or rebuilding its old proofs. This new source consumes none of unit32's specialized theorem interfaces or definitions: it uses its imported standard scalar algebra/calculus environment. Complete relevant standard `HasDerivAt` definition and addition, subtraction, constant multiplication, constant addition, identity and constant derivative interfaces, plus real square-root nonnegativity/square identities, were inspected. Direct source blobs for those files equal the pinned mathlib HEAD byte-for-byte. The package's repository-local-change warning therefore does not indicate a changed consumed calculus/square-root source in this review.

## Acceptance scope and remaining obligations

This is LEAN_FULLY_CHECKED for the exact final frozen local target, using the already successful source-bound author receipt plus this independent complete semantic/proof/type/value review. It is elementary source-bound exponent formalization; historical novelty or publication significance is not certified.

The interval image infinite sum and its normal convergence, termwise differentiation, differentiated-image estimates, Gaussian-series/profile summation, killed heat-kernel or Brownian probability identification, high-time sine expansion, interval higher/mixed/time derivative bounds, one-sided traces of the kernel, PDE for the quotient, and compensated small-step Taylor bound are outside this unit and remain OPEN. All original C12/OQ3/OQ4/OQ56 root groups remain OPEN. No finite algebraic identity or tail comparison is treated as a root closure.

No uncovered declaration or mathematical gap remains inside the frozen target. The writer and execution release records no in-flight operation. All output is confined to this review directory.
