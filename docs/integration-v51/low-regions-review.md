# Actual marked low Regions1/2 — independent final review

STATUS: **CORRECT**. No critical gap or required fix.

Reviewer: /root/common_marked_pair_review; gpt-6.1-sol / xhigh, independent of the author, math-theorem with no math-ultra. This is the second explicitly assigned frozen consumer review in this fresh reviewer context. The accepted low-derivative producer and other unchanged predecessors were reused by exact hash and complete consumed interface, without another proof review or Lean gate.

## Frozen accepted artifact

- Commit bd6ad019004270f6d1f0e4120b92097b26bbc17a, parent 6e6e59ee94c6fd5775e45513c6621a1b6662d9d5.
- Shao/Probability/QuadraticFullNoiseMarkedLowRegions.lean: 71,293 bytes, 1,258 lines.
- Source SHA256 366e8729e1a11cdf13c23108214ad1266d6799641668c68a909ea1a3f8379461.
- Object SHA256 d7e2ec9093379ae0ac8929758847f1ef299faaf439ff2e7b8b12ec8e07326951.
- Local draft, current server source and frozen commit blob agree. The commit changes only this module. The source is UTF-8, no BOM, LF only, zero CR.
- Both complete public statements match the frozen candidates after whitespace-only normalization. Their source order is reversed; there is no mathematical signature change.

All source/proof lines 1–1258 and every actual owned type were read: 2 frozen public theorems, 25 private handwritten theorems and 40 generated theorems, totaling 67, with zero definition values. Eight generated declarations are under the public theorem prefix, so a private-prefix-only check would miss them; the actual module-owner map includes all eight. The JSON gives every name, original complete type hash, kind, axiom list, source range and individual verdict.

## Source fidelity and exact scope

The read-only original supplement SHA256 is b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd. Complete target passages LF2610–2640 and LF3419–3507 were read, together with LF2370–2424 and LF2470–2476 for the actual low-frequency/cone and marked-norm conventions. The same reviewer context also read the actual D/E and signed whole-u-IBP passage LF2340–2376 and LF2554–2595.

Both statements retain the actual conditional truncation law, normalized original n-second moment, original mean-zero parent law, truncation budget, i≤n, m=n-i and the actual conditional mu,m3,T,gamma. They use actual standard nested real u derivatives of D and W=uE, and actual chi/(sqrt(r)+sigma*w/y)^2 with |sigma|=1 and sine shift sigma*w. The r phase is exp(-i*v*r). The integrands are actual nonnegative norms divided by y^2 over real two-dimensional volume.

All frozen guards remain: epsilon/(1+x)≤h, 0<kappa≤1/128, L2≥20, 1≤kappa*sqrt(L2), 0<y≤2, |w|≤y/16, L2*gamma^2≤T<y^2. Region2 additionally retains h≤1 and (4*h)*y≤delta, where delta is positive, ≤1/16 and chosen before every law/scale parameter. No raw-law assumption is claimed to imply those last two guards; the source h=epsilon0/(1+y) adapter remains open.

Region1 is exactly the source low-frequency set intersected with the closed cone, including u!=0. Region2 is exactly the original low-frequency set minus that cone, including its origin.

## Complete proof review

**Actual joint measurability and genuine two-dimensional integrability (lines 18–106, 154–183, 353–388).** The actual characteristic integrals are jointly continuous by domination with the probability-integrable constant one. The actual compact sine mark is jointly continuous by genuine domination with |a(r)|. Positive difference quotients produce the actual u derivative measurability, and a second application produces the actual nested second derivative. Actual global differential producers pay both slice differentiability premises.

The affine fiber helper proves true L1 of a moving fiber indicator from actual zero- and first-weighted-v marked norms. The nonnegative-region helper then proves integrability of the outer fiber norm using an actual integrable u envelope. Only after integrable_prod_iff establishes genuine pair L1 does it use Fubini and integral comparison. A one-dimensional slice estimate is never substituted for pair L1.

**Gaussian and inverse-u payment (lines 108–151, 185–351, 768–977).** Both real half-lines of |u|^s*Gaussian are genuinely integrable for s>-1. Positive affine scaling gives exactly a^(-s-1), including the Jacobian. For ordinary sine moments, the two paid powers k and k+1/2 give the claimed scaling.

The inverse-u moment retains the actual F_y(u)=min(y|u|,1+sqrt(y|u|)). The inequality min(t,1+sqrt(t))≤2sqrt(t) gives, away from the zero point,
|u|^-1*Gaussian*F_y(u) ≤ 2sqrt(y)*|u|^(-1/2)*Gaussian.
The -1/2 power is genuinely L1. This proves actual J_-1 integrability and the stated bound without using a divergent |u|^-1 Gaussian majorant near zero. The ae exclusion of u=0 occurs only in this valid domination argument.

At a=sqrt(T), the exact factor is R(T,y)=1+sqrt(y)*T^(-1/4). A finite positive sum chooses one constant before T,y for all six degrees0–5 and J_-1. The four actual profiles K0,K3,K1,Ke are expanded into those paid moments; true L1 precedes every integral_add. Their bounds are respectively C*R, C/T*R, C*y/sqrt(T)*R and C*R.

**Actual signed marked kernels and outside tails (lines 232–260, 390–454).** The accepted global smooth amplitude family at k=2 applies to theta=sigma*w/y, since |sigma|=1 and y>0 pay the exact parameter guard. The actual global mark zero/first-v norms keep the sine minimum. For Region2, the accepted N0=32 outside sine theorem applies to the actual signed amplitude and shift under aStar*y≤delta. Its true zero/first-weighted-v tails have powers31/30. When aStar≤4, both are dominated by C/(1+|u|/4)^30. The fixed outer profile (1+|u|)^5/(1+|u|/4)^30 is truly L1: continuous on a compact interval, and dominated on |u|≥1 by 32*4^30*|u|^-25, whose real tail integrability is proved.

**Region2, including its origin (lines 456–766).** The actual source-law bridge pays probability, moments, positive variance, support and gamma>0. It yields T≤4/3 and gamma≤2h≤2; h>0 is derived from the source cutoff lower bound. The actual low-frequency odd polynomial is bounded by 1000*(m|mu|+m*m3)*(1+|u|)^5*(1+|v|), after using exp(-T*u^2/256)≤1. The actual even global derivative bound is controlled by 2*Cg*(sqrt(T)+gamma)*(1+|u|)^5. Every uniform coefficient bound uses displayed guards.

The proof introduces a strict outside region R' only internally. It proves R=R' almost everywhere using volume.ae_ne(0,0): the low-frequency inequalities force v=0 if u=0, so the only discarded point is precisely the original origin. Measure.restrict_congr_set then gives actual equal restricted measures, transferring both integrability and values back to the unchanged public R. The original origin is not silently deleted.

At aStar=4h, h≤1 pays aStar≤4 and (4h)y≤delta pays the outside theorem. The actual zero/first-v tail estimates and the fixed genuine u-L1 profile pay the complete moving pair integrals. Finally n*m2≥3/4 yields m≤2*T*n, preserving the raw source coefficients:
odd ≤ C*y^-2*T*(n|mu|+n*m3);
even ≤ C*y^-2*(sqrt(T)+gamma).
Constants precede all law/scale parameters.

**Region1 and the exact R(T,y) factor (lines 979–1256).** The actual low/cone producer is applied on precisely the closed source low-frequency/cone domain with u!=0. The algebraic grouped odd bound is
N0*K0 + N3*K3 + N3*K0*|v|,
with N0=m|mu| and N3=m*m3. The even bound is Ke. Global actual zero/first-v marked norms pay each moving fiber; the weighted term retains (1+y|u|)F_y(u). The exact y|u|K0≤K1 helper handles its u=0 branch separately and is an equality elsewhere.

The paid profiles produce actual pair L1 and bounds before the final product integral. The source coefficient conversion m≤2*T*n, T≤4/3 and y≤2 gives
N0+N3/T+N3+N3*y/sqrt(T) ≤ 20*(n*m3+T*n|mu|).
The final output is exactly the source odd coefficient times R(T,y)/y^2 and the even R(T,y)/y^2. No conditional mu=0, arbitrary supplied amplitude, missing derivative envelope, time-sum premise or probability equality is inserted.

All 40 generated actual types were separately read. They are standard union/Iic/Ici membership, IntegrableOn-univ equivalences with the actual general measures, explicit numeral/product/natural-power/integer-power nonzero facts, characteristic-zero cast successors, and the finite natural index obligations paying degrees0–5. Their complete generic binders and premises are preserved in the actual-type coverage.

## Exact evidence and predecessor reuse

The author receipt SHA256 is 5a02b622ad0df76b9bd20a43c4285d6d0217304431205970a288bdb501cccea8. It records kernel and owned-axiom exits0. Lean is leanprover/lean4:v4.36.0-rc1 and mathlib is 807d3836b165983210ee2ecf3cd28f239436949c; current server pins were read. The author used CPU10–13, the shared root-heavy.lock and -M8192 -j4 -DautoImplicit=false.

- check13 log: 152 bytes, SHA256 e737184c2f87adf2667327bab4abebab172f4f20d49ec8e12bd6dc6246ad139b; no source diagnostic, only the known mathlib local-changes warning.
- Full actual-owned types/values/axioms log: 449,324 bytes, SHA256 2d36d4eeb322fb61093f7bc730102365cac55ae192db05114e3066a0799be279.
- Owned audit JSON: 17,501 bytes, SHA256 b48381f560d4295cb22f0056ba34ed5f6711fa49ab014e5cf76beaf2bf99641d.
- Audit/export script: SHA256 c865cd466046df382e667650193812ed686732a04f0c76f809cdfdc04f1388bd; fully read.

The full log's 67 ACTUAL_TYPE blocks before AUDITED_TARGET_CONSTANTS have zero U+22EF/U+2026 markers and zero definition values. The two additional public #check copies after ACTUAL_PUBLIC_TYPES_BEGIN contain two U+22EF omissions. Those redundant copies were not used for coverage: both full public types were completely read in the actual-owned section. No new export or Lean replay was needed.

Exact module ownership and every transitive collectAxioms row were checked. All 67 actual type names, kinds and axiom lists match the owner JSON, including generated names outside the private prefix. All axioms are within propext, Classical.choice and Quot.sound. No sorry/admit/new axiom/unsafe/native_decide occurs in the frozen source. Display-only folding affected 1,144 canonical standard instance subtrees; every mathematical parameter, measure, guard and quantifier remained explicit, with original complete type hashes in JSON.

The accepted low-frequency derivative module retains source67cf873490270a75f136486d99d258e252256729036758de4802ab9d7d32e70f and object7fa6d0e9f697c8a290c07c7a160248023bf35c30bfafcaba584d8207a6d05658. Its existing complete CORRECT review was reused once. Complete consumed interfaces and exact source/object hashes were also checked for global actual derivatives, marked outside norms, marked global norms, amplitude family, source truncation/moment bridges and actual full-noise law. Their unchanged proofs were not reviewed again.

## Acceptance boundary and runtime

Accepted: both exact frozen actual moving two-dimensional Region1/2 post-IBP marked norm integral L1/bounds, with all67 owned proof/type/generated/axiom coverage.

The h=epsilon0/(1+y) smallness adapter, five-region/IBP/inversion assembly, short-time integrals, m2-weighted grids, probability/desmoothing and original C1/C2 conclusions remain open. This module does not itself assert whole-u IBP or a probability equality.

Only this review Markdown and JSON were written for this unit. No source was changed and no Lean/build/audit/cache action was replayed. Both explicitly assigned frozen reviews are COMPLETE; no command remains in flight; reviewer released. Authoritative usage counters are unavailable, and no subscription-percentage allocation is inferred.
