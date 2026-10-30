# unit285 SAME author repair01

STATUS: REPAIRED_SOURCE_CANDIDATE_UNCHECKED

This explicit reactivation repairs the five actual native01 source diagnostics within the two proof bodies. It does not change a frozen statement, premise, constant, event, declaration order, import or option. PRE, both HEADs (25 LF total) and CLOSE remain byte-exact. The old author-01 seal, old independent SOURCE report, complete native01 failure and every activation input remain immutable. Only the new author-repair-01 directory was written. The author is not the independent reviewer.

## ACK and exact failure

repair01-ACTIVATION.json has SHA256 736829965bac153e7db0c80c0b7986ba77a5b74de3905ed4f8354c2735d8790f, 19450B. All 75 exact inputs passed SHA256/byte verification before any repair write. The parent received an actual ACK before INPUT-ACK.json and component writes. They were checked again at the first repair write and at sealing. The four parent-authorized supplemental inputs for the norm measurability route were separately verified before use; both actual primary files were read completely, including their namespaces, complete declarations/proofs and typeclass context.

native01 was an actual naturally ended RC1 in 10.285743510350585 seconds, with five errors and one style warning, no object and no AX result. Its original receipt SHA256 is 5ffb62c77472ddd2d77d69b966a168ac85b84e56e7abc5b56772e6ede9a93887 (43012684B, retained on the server). The bound native01-terminal-inspection.json contains the complete normalized five errors and warning and exact stdout/stderr provenance. This repair neither replays that request nor reclassifies it as a pass.

## Five source repairs

1. Old line 61: `Integrable.add` returns integrability of a function-valued sum. Passing that proof without naming `integral_add`'s function arguments made rewrite look for an unapplied function-add normal form instead of the literal lambda in the integral. Both uses now explicitly pass the complete `f := ...` and `g := ...` lambdas from the actual original `integral_add {f g}` interface. The same integrability proofs discharge the same functions; integral linearity and mean-zero elimination are unchanged.
2. Old line 73: the actual elaborated additive inequality was the right-summand order `t^2*E(f^2)+1 <= t^2*v+1`. The candidate now uses `simpa only [add_comm]` on that exact term to put it in the frozen calculation's `1+...` order. The actual second-moment comparison and nonnegative multiplier are unchanged.
3. Old line 110: `Measurable.abs` was absent in the actual environment. The candidate supplies an explicitly typed local `hAbsmeas` from the actual public `Measurable.norm hSmeas`, followed only by `Real.norm_eq_abs`. The norm theorem's codomain is alpha=Real and domain is beta=(iota->Omega). The existing Real normed additive group, Real opens-measurable Borel structure and original product measurable domain provide its exact typeclasses. No topology or StandardBorel condition on Omega is added. The strict event is then measurable by the same `measurableSet_lt` with `hAbsmeas`.
4. Old line 245: after choosing the first member of the union, `change 2*d <= S x` now exposes the set predicate before the existing absolute-value simplification.
5. Old line 248: after choosing the second member of the union, `change S x <= -(2*d)` now exposes the set predicate before the existing negative absolute-value rewrite and `linarith`.

The old `letI` style warning is deliberately retained, per the parent direction; no option is added to suppress it. This candidate has not been run through Lean, so neither its error count nor its warning count is asserted. The full unified diff and CHANGED-BYTE-INTERVALS.json are computed from the actual complete old and new UTF-8 source bytes. DIFF-COVERAGE.json maps all five diagnostics to their new source spans and records the retained warning. No changed interval lies in PRE, a HEAD or CLOSE.

## Mathematical invariants

The entire actual-variance route remains unchanged: f is measurable, almost everywhere bounded by B, has actual integral mean zero and actual second-moment integral bounded by v. Integrability of f, f^2 and exp(t*f) is derived from bounded support under a probability law. The original complex exponential remainder gives exp(u)<=1+u+u^2 on |u|<=1; legitimate integration gives mgf<=exp(t^2*v). No variance is replaced by B^2 and no MGF/Bernstein contract is assumed.

The same actual P=Pi(nu), X_i(x)=f(x_i), S=sum_i X_i and coordinate map laws supply independent exponential integrability and the product MGF <=exp(t^2*m*v). q=0 still uses P(H)<=1 before any division. B=0 still proves f=0 nu-AE, then S=0 P-AE and nullity of the strict event. For B>0,q>0, a=m*v>=0, d=sqrt(a*q)+B*q>0 and t=q/d>0 still satisfy d^2>=a*q, |t|*B<=1, t*d=q and t^2*a<=q. Hence both one-sided Chernoff exponents are <=-q and their union costs exactly 2*exp(-q). Empty indices/card0 and v0 still require no division by m or v. The frozen strict absolute bad event is not changed into a false non-strict zero-threshold event.

Unchanged source-to-statement mathematics has the exact old independent SOURCE-only report, SHA256 8285e5f9305f4dd11256e0e6673cc4c50d6e77cf6dab2fbb4508d1c0bd838e69, as preserved prior evidence. That report is not a machine receipt for either source version and does not accept the repaired proof bytes. A fresh affected independent review must cover this candidate's changes and their interaction with the complete statements/proofs. Primary unchanged interfaces are retained by their exact initial bindings and old trace; PRIMARY-API-TRACE.md documents the new precise interface work and reuse boundary.

## Validation and authority boundary

Local validation is deterministic text/byte work only: complete source assembly, exact frozen comparison, full unified diff, changed byte spans, explicit declarations/options/imports, forbidden source tokens and UTF-8-no-BOM/CR0/single-final-LF checks. These do not elaborate Lean or audit generated constants. Actual generated owner names, TYPE/FULLVALUE inventory, first object and recursive axiom result remain null. No sourceAccepted, kernel or qualification pass is claimed.

There was no author Lean/AX/compiler/probe/SSH/network/upload/Git/API/cache/resource/child/Goal/schedule/sidebar action. No new format or execution wrapper was installed. The requested model/effort remains gpt-6.1-sol/xhigh, SAME original author. Actual unexposed model/backend/effort/input/cachedInput/output/reasoningSubset telemetry is null.

The unique LAST.json releases every active, dormant and future writer/execution/publication/child authority with allSix0 and no queued operation, retry, pending wait, uncertain execution or self-resume. Any further repair requires a new explicit activation. Designated-server native/same-FIRSTO allactual TYPE/FULLVALUE/recursive-AX and independent FINAL remain later parent-managed gates. Original Bernstein consumer, Delta, Mills, anomaly costs, PE-R, PE-L, NR, DC, OQ56 and root remain OPEN.
