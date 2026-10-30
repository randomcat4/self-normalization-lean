# unit285 author-01 — actual-variance finite IID concentration

STATUS: PROVED (author's mathematical derivation; independent SOURCE review and Lean elaboration have not run).

The candidate implements exactly the two frozen declarations in `Shao.OQ5.P41.VarianceSensitiveIIDBernstein`, in their frozen order. PRE, both HEADs and CLOSE are byte copies of freeze-01. There are two explicit theorems and no new top-level definitions, assumptions, options or helper declarations. All auxiliary arguments are local `have` or `let` expressions. The source is a candidate, with `sourceAccepted=false`, `kernelChecked=false`, `qualified=false`; no object or axiom receipt is claimed.

## Actual ACK, ownership and execution

Before the first author write, all 22 activation inputs were read as bytes and their SHA256 and byte counts matched. The actual ACK was sent to the parent before proof drafts began. INPUT-ACK.json truthfully records that message and the later repeated successful check; it does not pretend its own file existed before the proof drafts. Supplemental primary sources were separately bound and verified before use. Only the new `drafts/oq56/unit285/author-01` directory was written. No other owner, shared source, curated library, source/history, old seal or cache was edited. The author is not the independent reviewer.

The requested model/effort is gpt-6.1-sol/xhigh, with fresh context. Actual unexposed model/backend/effort and input/cached-input/output/reasoning-subset telemetry remain null. The math-theorem skill and its role, workflow and Lean references were read. The explicit project restrictions override skill toolchain probes. There was no Lean, AX, compiler/toolchain probe, SSH, network, upload, Git/API publication, cache/resource operation, child, Goal, schedule or sidebar operation. Local file hashing, text reads, assembly and static inventory are the only deterministic work.

## T01: actual second moment pays the small-parameter MGF

The almost-everywhere absolute bound yields f in [-B,B]. Since nu is a probability measure, f is integrable. The same bound gives 0 <= f^2 <= B^2 almost everywhere, so f^2 is also integrable. The bounded-interval exponential-integrability theorem gives integrability of exp(t*f) for every real t; smallness is needed for the estimate, not for integrability.

At x=0 and z=u in the original pinned `Complex.exp_bound_sq`, the complete remainder bound is

    ||exp(u)-1-u|| <= |u|^2, provided |u| <= 1.

Taking real parts using `Complex.re_le_norm`, with the pinned real-exponential conversion and complex real norm, gives exp(u) <= 1+u+u^2. For almost every observation, |t*f| = |t|*|f| <= |t|*B <= 1. The candidate therefore obtains

    E exp(t*f) <= E(1+t*f+t^2*f^2)
               = 1+t^2*E(f^2)
              <= 1+t^2*v
              <= exp(t^2*v).

Both additions are justified by actual integrability, and the actual integral mean hmean is used at the linear term. The final second-moment comparison multiplies hsecond by t^2 >= 0. This is an actual-variance estimate; it neither substitutes B^2 for v nor assumes an MGF/Bernstein contract. T01 is valid for B=0, v=0 and t=0 without division or a positivity premise.

## T02: same finite product, strict two-sided event

Write P = Pi_i nu, X_i(x)=f(x_i), S=sum_i X_i, m=card(iota), a=m*v. P is a probability measure by the actual finite-Pi instance, including the empty index type. `iIndepFun_pi` supplies independence of these actual coordinate functions. Their measurability is hf composed with coordinate evaluation. The a.e. bound is transported by `Measure.tendsto_eval_ae_ae`, never made pointwise.

For each real z with |z|*B <= 1, bounded-interval exponential integrability is established for every coordinate. The pinned independent finite-sum integrability theorem then supplies exp(z*S) integrability. For each coordinate, `measurePreserving_eval` identifies its map with nu, and `mgf_map` gives mgf(X_i,P,z)=mgf(f,nu,z). The pinned `iIndepFun.mgf_sum` thus gives

    mgf(S,P,z) = mgf(f,nu,z)^m <= exp(z^2*v)^m = exp(z^2*a).

The nonnegative base required for the power comparison is the actual `mgf_nonneg`. The source includes an explicit function-extensional equality between S and the function-valued finite sum, so this connection is not an assumed definitional equality of finite sums.

When q=0, P.real(H) <= 1 <= 2 establishes the result. When B=0, hbound forces f=0 nu-almost everywhere. Transporting this equality to every coordinate and using finite `eventually_all` makes S=0 P-almost everywhere. The frozen nonnegative threshold is never strictly below |S|=0 there, so the strict bad event is null.

In the remaining branch B>0 and q>0, let

    d = sqrt(a*q)+B*q,    t=q/d.

Here a>=0, d>0 and t>0. The candidate verifies all of the following without any positivity assumption on a:

    d^2 >= a*q,
    |t|*B = q*B/d <= 1,
    t*d = q,
    t^2*a <= q.

Indeed d^2-a*q = 2*sqrt(a*q)*(B*q)+(B*q)^2 >= 0. Multiplying a*q <= d^2 by q>=0 and dividing by d^2>0 gives t^2*a<=q. The threshold in the frozen HEAD is exactly 2*d. The original upper-tail Chernoff theorem with t and lower-tail theorem with -t now give, respectively,

    P(2*d <= S) <= exp(-2*q+t^2*a) <= exp(-q),
    P(S <= -2*d) <= exp(-2*q+t^2*a) <= exp(-q).

The strict event {2*d < |S|} is contained in the union of those two non-strict one-sided events. Real-measure monotonicity and the union inequality yield the exact frozen 2*exp(-q) bound. Measurability of the strict event is proved directly from the measurable finite sum and its absolute value.

## Boundary and source-fidelity checks

* Empty iota/card zero: no Nonempty premise was introduced. The cited finite-Pi, finite-sum independence, integrability and MGF APIs explicitly have empty cases; a=0 and S=0 are permitted throughout the positive-B branch. No division by m or by a appears.
* v=0: a=0 is permitted. The parameter d=B*q stays positive in the only branch that divides; t^2*a=0 gives an even stronger exponent. The proof never divides by v.
* B=0: the direct a.e.-zero branch covers every q, including intersections with v=0 or empty iota. All coordinate equalities remain almost everywhere.
* q=0: the probability bound is used before any division by q or d. The strict zero-threshold event is not claimed null in general.
* Strictness: the frozen `<` is retained literally. A non-strict absolute bad event at B=v=0 and constant f=0 would have probability one for any q, contradicting 2*exp(-q) when q>log(2). This false substitute is neither stated nor used.
* The generic engine corresponds to the Bernstein payment invoked at p41(14), with p41(9) explaining why the later original residual consumer must retain its conditional mean. No p41 original consumer, anomaly-vector validity event, polylog simplification, Delta/Mills/anomaly integration or S11/root closure is claimed here.

## External API audit and validation boundary

The complete used declarations, their proofs and their section/typeclass environments were read from the pinned primary files listed in PRIMARY-API-TRACE.md and READING-COVERAGE.json. SUPPLEMENTAL-BINDINGS.json includes the exact extra input bytes obtained read-only by the parent. Files supplied but unused are distinguished from used mathematical dependencies. In particular IntegrableExpMul and ExpDeriv do not contribute a hidden extra import or premise. No unit283 or unit284 candidate module is imported. No accepted shared private Bennett proof was read, copied, rebuilt or referenced by a mangled name.

ASSEMBLY.json records every contiguous component byte slice and LF position, with no omitted separator bytes. STATIC.json records deterministic source syntax/encoding scans, exact frozen byte matches, source declaration count and forbidden-token absence. These checks do not parse, elaborate, compile or prove Lean correctness. Actual generated/owned names, full generated types/values, first object and recursive axiom dependencies remain unknown until the designated server gates. No fabricated receipt or axiom whitelist pass is reported.

One local metadata attempt stopped on a PowerShell path-array concatenation error before source assembly or any seal. Its exact failure and local effects are retained in LOCAL-METADATA-FAILURE-001.json. The affected metadata was rebuilt with explicit path/hash/byte records; the later deterministic gate passed. This was not a mathematical, Lean, server or axiom result.

The author has completed this authorized source unit and is releasing all active, dormant and future writer/execution authority in the unique LAST.json. There is no queued/retry/waiting/uncertain operation, no future self-resume, and any repair requires a new explicit activation. Independent complete SOURCE review, designated-server native and same-first-object all-actual TYPE/FULLVALUE/transitive-AX receipts, and independent FINAL remain required. PE-R, PE-L, NR, DC, OQ56 and root remain OPEN.
