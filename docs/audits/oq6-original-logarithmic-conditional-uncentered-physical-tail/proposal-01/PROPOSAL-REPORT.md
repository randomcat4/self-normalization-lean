# Unit 274: actual conditional mean shift with the original random denominator

STATUS: VALID_MATHEMATICAL_INTERFACE_PROPOSAL_PENDING_PARENT_FREEZE_AND_IMPLEMENTATION

The next substantive unit can prove the **actual uncentered conditional physical closed tail on [2, c n^q] with the original polynomial error**, while retaining the same actual conditional law, original finite-row denominator and zero-denominator convention. It must first prove a genuine lower bound for RH on the existing actual goodset and pay that goodset's complement relative to the Gaussian tail. A small numerator by itself does not accomplish this.

The proposed HEAD/PREAMBLE/CLOSING are declaration candidates only. There is no Lean proof, native/axiom execution or kernel claim. The dependency on 273 remains explicitly pending: its frozen declaration is SOURCE accepted, first native01 ended RC1 with no object, and same-author repair is in progress. Neither this proposal nor 273 is qualified.

## Authorization, scope and actual reading

Activation: `C:/game/shao lean/drafts/oq56/unit274/proposal-ACTIVATION.json`, SHA256 `75e593d32007271f07b6714bbae3674cf1f2a4b327c0a8ee2dd3a0c1f10785c5`, 10739 bytes. All 38 bound inputs were actually byte/hash verified before the first READ_ACK. Sole writable scope is this `proposal-01` directory. No other owner's file was changed.

Complete original-page reading: p40 379 LF; p41 449 LF; p44 180 LF; p49 109 LF; p50 236 LF; p51 355 LF; p52 134 LF; p53 111 LF; p54 86 LF. All nine were read completely. Also read completely: 273 frozen HEAD, 133 LF, SHA256 `5ab4e6f66fa939e04457c2cf98338f7e7db95b4fdf36f04ea0940c762849696d`; its independent SOURCE report, 120 LF, SHA256 `283ea7fa6596a01153c08b85eff6bf88ca4b5285c5638a673a4b862c0a296473`; 273 parent SOURCE intake and native01 terminal inspection. The repair activation's role/task/status projection was read to avoid overlapping the live author's work.

Qualified 177/264/266/267/270 evidence was reused by exact source binding. Their complete relevant public theorem statements were read. Accepted proofs, generated TYPE inventories and accepted kernel/leaf axiom gates were not re-reviewed or replayed. In particular, the current 273 SOURCE report does not upgrade the failed native. The original-source byte provenance and all prior failures are retained.

math-theorem was used for source-to-statement, quantifier, hidden-assumption and boundary analysis. Its general execution suggestions do not override the explicit proposal-only/server-only task. Windows Shell7 guidance was used for UTF-8-safe local file operations; no toolchain discovery or execution was undertaken.

## What the original source actually requires

p40 and p51 S1 fix the original symmetric order-two kernel, first projection, centered-row jackknife coefficients and the convention T=0 at a zero denominator. p41 section 4 and p51 S6 define the actual conditional kernel H=g+g'+lam*r, its conditional mean kappa, its true projection G, and sigma. p54 F1-F2 replace the false p-moment-rate assertion by a uniform eventual bound for the standardized p-moment; only variance and sqrt(m) times the actual mean have the prescribed arbitrary polynomial rate. No beta_std-beta polynomial rate is used here.

p51 S6 says the mean shift must be controlled through the actual lower-denominator event; p51 S3 and p54 F4-F6 require payment for actual failed concentration/low-energy events. The proposal carries these statements into the same conditional family and same finite physical statistic. It does not claim the exceptional-block integration in p41 section 6, PE/DC as a whole, NR for arbitrary L2 kernels, the p50/p52/p53 negative constructions, or an OQ56 root closure. Any alpha>0 here concerns a logarithmically truncated background, not an unrestricted original-sample relative-tail theorem for that alpha.

## Reused public interfaces and their exact role

* 177 `actual_logarithmic_conditional_rates`, source SHA256 `51f597017859a870d7067b0eed1213093a0ed6b98c1726f86977260e6c2c7c3a`, supplies the actual log cutoff A=2(J+1)/(1-2/p), the normalized restriction nu_n, and `sqrt(m)*abs(kappa) <= Kmean*n^(-J)` uniformly for lam in [0,1] and m<=n. Its exported J>=0 estimate at J=0 is only boundedness; this exported estimate alone does not give a vanishing deterministic shift.
* 266 `uniform_pmoment_original_boundedPolylog_goodset_frontier`, source SHA256 `f40b9fc01f7c58e94200bdece91e00457f621cc7b1f3afea14696b8989116cd8`, has cg and N before arbitrary normalized models. With moment budget 2*beta, cg is exactly `(1/(4*(2*beta)))^(2/(p-2))/4`. On its actual `projectionGood intersect Crows` event it gives energy>=1/2, |centeredDelta|<=1/32, the exact square-root factorization and the original 3+1+4 complement payment.
* 267, source SHA256 `6ed38ca7c071e20ea6555a8ac47c34e85d9b2afe67e116c942e9bde9c0cf9dc8`, confirms that this is the actual current-level goodset and original physical zero convention, with the same payment. Its additional `(1+rho)*z <= sqrt(m)` geometry is needed for its clipped-process conclusions. The proposed denominator/mean-shift unit can consume 266 directly and does not silently import 267's clipped conclusions or its extra geometry.
* 270, source SHA256 `26d2ebb296f939f60461e9b32fa419e071f570a6875b894bd1b14f26320dd018`, supplies one common N for normalized original physical tails under the explicit external hSZ and bounded polylog envelope. 273 assembles this for the actual nu_n/Hstd family and rescales m to n. The next unit consumes that centered-tail interface only after 273 is genuinely qualified.
* 264, source SHA256 `a2dda2b0def88529c2f2d08cb90557e79b8a3a481adefecd84ab51a629f4575f`, supplies all strict/closed compact CDF/tail errors under a **distinct explicit external** `ScalarShaoZhouFiniteCostCDFInput`. It does not assert existence of that contract. Its model-dependent existential K is an important limitation discussed below.

## Complete deterministic lower bound and mean-shift calculation

Use exactly the definitions in 273: H=g+g'+lam*r under nu_n, kappa the actual product integral, G its actual centered row projection, sigma2=integral G^2, sigma=sqrt(sigma2), Hstd=(H-kappa)/sigma, and gstd/rstd the actual projection and residual of Hstd. The conditional model has sigma>=1/2 and beta_std<=2*beta; it has the common standardized envelope budget Menv and polylog height supplied by 273.

Fix m with n<=2m and m<=n, and a level z>=2. Let qm=t0*m^(1/3), Ktail=tailScale(Menv), and let Crows be **exactly** the event

`abs(originalUpper m rstd) <= Ktail*m*qm` and `norm(originalRows m rstd)^2 <= Ktail*m^2*qm`.

Let Hgood=projectionGood(m,gstd,z) intersect Crows, the actual event used by 266. No independent/free goodset is postulated. On Hgood, writing d=centeredDelta, 266 yields V^2>=1/2, |d|<=1/32 and sstd=V*sqrt(1+d). Consequently

`sstd^2 >= (1/2)*(31/32) = 31/64 >= 1/4`, so `sstd>=1/2`.

273's **pointwise finite algebra** gives RH=2*sigma*sstd for every finite sample, including exceptional projection rows and zeros. Hence on Hgood,

`RH >= 2*(1/2)*(1/2) = 1/2 > 0`.

With `delta_n=2*Kmean*n^(-J)`, the actual random mean shift therefore satisfies

`abs(sqrt(m)*kappa/RH) <= 2*sqrt(m)*abs(kappa) <= delta_n`.

The true Tuncenter equals Tcenter plus that shift on Hgood, since its actual RH is positive there. No assertion is made that RH has a global deterministic lower bound. At RH=0 both original statistics are 0 by the frozen convention; this event is outside Hgood and is already paid, rather than deleted without cost. No a.e. projection equality is promoted to a pointwise equality: 273's sampled-kernel cancellation is the finite pointwise bridge used here.

The two closed-event comparisons follow sample by sample on Hgood:

`{Tcenter >= z+delta_n} intersect Hgood subset {Tuncenter >= z}`,

`{Tuncenter >= z} intersect Hgood subset {Tcenter >= z-delta_n}`.

Thus the exact lower/upper probability sandwich in the proposed HEAD holds with one P(Hgood complement). This remains valid at atoms and at the equality boundaries; no continuity of the statistic's distribution is assumed.

## Actual complement payment, relative payment and window

The raw complement payment is

`payment = 3*exp(-qm) + exp(-cg*m) + 4*exp(-z*sqrt(m)/2)`.

It is the same original 3+1+4 payment and the actual conditional product law P=nu_n^m. It is not a Markov estimate for the small mean numerator or a bound for an invented envelope threshold event. Since z>=1, the last term is at most `4*exp(-sqrt(m)/2)`.

`OriginalExceptionalTailAbsorption.eventually_original_exceptional_payment_absorbed` gives, in its small m^(1/6) window,

`2*payment <= exp(-(t0/2)*m^(1/3))*Psi(z)`.

The proposed HEAD states the slightly weaker safe consequence `P(Hgood complement)/Psi(z) <= exp(-(t0/2)*m^(1/3))`. All divisions use the public strict positivity of the standard normal tail. Since m>=n/2, the exponential is eventually at most n^(-1/2), uniformly in m and z. It is absorbed by the displayed cubic polynomial term.

Let c0 be 273's centered-tail constant, cR its remainder-window scale with Menv, and cA=min(1,sqrt(t0)/2) the exceptional-payment scale. A valid choice of c is any positive number at most

`min(c0/2, min(2^(-1/6)*cR, 2^(-1/6)*cA))`.

As q=(p-2)/(2p) is in (0,1/6], z<=c*n^q and n<=2m imply both 266's and the absorption theorem's m^(1/6) restrictions. Choosing a smaller c only changes a fixed model constant. It does not strengthen a statistical assumption or enlarge a source window.

## Why the proposed precision assumption is explicit

The HEAD proposes `hJ : 1/2 <= J`, stronger than 273's `0<=J`. This is an explicit selectable cutoff-precision restriction, not a silent change. It is sufficient to retain the original two-term error instead of adding a third mean-shift term. For n>=1,

`delta_n <= 2*Kmean/sqrt(n)` and `(1+z)*delta_n <= 2*Kmean*(1+z)^3/sqrt(n)`.

Moreover J>=1/2>q makes `delta_n*(1+c*n^q)` tend to 0 uniformly on the proposed z window. One common N can therefore impose delta_n<=1/2 and delta_n*(1+z)<=1/4. This precision remains entirely compatible with the source instruction that the cutoff exponent A can be chosen for an arbitrary preassigned polynomial order; the resulting A and conditional model are explicitly those in the HEAD.

If the parent wants an arbitrary 0<J instead, a mathematically valid alternative keeps an additional `(1+z)*n^(-J)` error and either assumes J>q for the unchanged full q window or narrows the exponent, for example to min(q,J/2). At J=0 the exported 177 estimate alone does not show a small shift. None of these alternatives should be silently substituted for the proposed declaration. The parent must freeze its chosen statement before implementation.

## Centered-tail use, Gaussian rate and final uncentered bound

For z>=2 and delta_n<=1/2, both shifted levels t_-=z-delta_n and t_+=z+delta_n are at least 1, and t_+<=2z<=c0*n^q. These are genuine legal uses of 273. Their polynomial errors are bounded by a fixed multiple of the error at z, since 1+t_+<=2*(1+z) and p<=3.

The existing `standardNormalTail_local_comparison` gives only constant-factor comparison, so citing it alone would not establish a vanishing error. The required pure Gaussian estimate is obtained using the existing public `standardNormal_derivatives` and `standardNormal_mills_bounds`: on the segment from z to t, the logarithmic derivative of Psi has magnitude at most 1+max(z,t). If |t-z|<=delta and delta*(1+z)<=1/4, the mean-value bound followed by the elementary exponential increment bound gives

`abs(Psi(t)/Psi(z)-1) <= 2*exp(2)*(1+z)*delta`.

The constant is deliberately loose. The public local comparison bounds the accompanying multiplicative Psi(t)/Psi(z) by exp(2). This is a new elementary deterministic estimate to prove in the implementation, **not** a new external probability contract or the desired uncentered conclusion used as an input. The two probability sandwiches, the centered-tail error at t_-/t_+, this Gaussian increment bound, and the actual relative bad-event payment then give exactly the final two-term rate in the proposed HEAD. A finite positive K can absorb all fixed constants including Kmean, 273's centered K, exp(2), the rho bound and m-to-n comparison factors.

## One common N and exact actual law

The existential order is fixed: original mu/h/w/p/alpha/tau/J, external hSZ and t0 first; then c,K,N; then every n>=N, every lam in [0,1], every m between n/2 and n, and every allowed z. No N, c or K may be selected after lam, m or z. A common N is the maximum of: 273's N; twice the common 266 threshold for p,2*beta,Cpoly,1/alpha,t0,Menv; twice the exceptional-payment threshold; the deterministic shift/Gaussian-neighborhood threshold; exponential-to-n^(-1/2) absorption; and a window-nonemptiness threshold. All have fixed inputs, and all are uniform in the family members to which they are applied.

The probability law remains P=nu_n^m, with `nu_n=(mu Cn)^(-1) smul mu.restrict Cn`, and Pmu=mu^m. 273's exact product-restriction identity supplies, for every measurable event E,

`P.real E = Pmu.real(E intersect allGood)/(dn^m)`.

Here allGood is the actual finite rectangle Cn^m and dn=mu.real(Cn)>=1/2. The proposed HEAD retains the full measurable-event identity, allGood mass and measure equality, then displays the same uncentered-tail rate with the **actual original-law conditional ratio**. It does not turn this ratio into the unrestricted original-sample tail, which would require paying/integrating exceptional blocks. The finite physical map is measurable, so its tail event is eligible for the law identity.

## The level-one obstruction and the precise next interface

One cannot extend this **shift-sandwich proof from the exported centered-tail estimate alone** to all z>=1: at z=1 and positive delta, t_-=1-delta<1, outside 270/273. This is an actual information gap. For example, a triangular abstract centered-statistic family can have exactly normal upper tails at every t>=1 while placing all remaining mass at 1-delta_n/2. Adding the deterministic delta_n then makes the tail at 1 equal to 1, despite delta_n tending to zero. This is a counterexample to the inference from that restricted tail interface, not a counterexample satisfying the actual original kernel hypotheses.

Likewise, a_n=sqrt(m)*kappa tending to 0 does not by itself control a_n/RH: deterministic RH=a_n^2 gives a diverging shift. This is a diagnostic counterexample to omitting the denominator bound, not a claim about the genuine actual goodset.

For a full [1,c*n^q] result through a compact-tail route, the distinct named external contract `hSZC : ScalarShaoZhouFiniteCostCDFInput C` must remain explicit. 264's four atom-safe compact conclusions are relevant, but its public quantifier order is `forall normalized model, exists K, forall sample size`, so directly applying it to each nu_n/Hstd permits K to depend on n and lam. The 264 public theorem does **not** supply a uniform conditional-family K merely because beta_std and rho_std are bounded. Its upstream public compact physical theorem also chooses the low-energy c after the model. A uniform compact consumer with cg chosen from the common p-moment budget (or a new proof of the conditional-family compact estimate from hSZC and the same uniform budgets) is therefore a genuine missing interface. Do not hide it in an assumed desired compact conclusion, and do not extract proof-local constants as if the theorem exported them.

The broad scalar tail contract hSZ itself allows arbitrary controlled D1/D2, so it is not asserted that hSZ logically cannot yield a full level-one theorem. A separate direct application at the original z>=1, with the actual deterministic kernel-mean contribution included in the finite-cost numerator and explicit deletion costs, could avoid the below-one threshold entirely. That is a **new finite-cost consumer**, not an application of 273 at an illegal shifted level. This proposal does not implement or certify that alternative. Thus [2,...] is a sound next intermediate for the existing interfaces; an additional CDF contract is necessary for the specified compact route, not proved logically necessary for every conceivable proof from hSZ.

## Explicit remaining work and release

The parent should freeze the full proposed declaration only after accepting the explicit J>=1/2 choice and the [2,...] scope. Implementation then requires a source-qualified 273 dependency, the deterministic RH/shift bound, one common threshold assembly, the sharp Gaussian increment helper, measurable probability sandwiches and final constant absorption. It requires independent complete source-to-statement/proof review plus exact-source server native/all-owned transitive-axiom evidence before acceptance. No per-unit execution wrapper or repeated accepted check is needed.

No mathematical implementation, Lean/axiom or server command, upload, network request, Git/API publication, child context, Goal, automation, sidebar or proxy action occurred. A local read-only PowerShell projection initially had a duplicate-key parser error; no mutation executed in that failed command. Subsequent projection reads succeeded. All proposed text is UTF-8 without BOM and LF normalized. Existing source bytes, accepted evidence and failures were preserved.

Prescribed model/effort: gpt-6.1-sol/xhigh. Actual model/backend/effort and input/cachedInput/output/reasoningSubset usage are not reliably exposed and remain null. This is SOURCE/INTERFACE analysis only, with no originality or root-completion claim. After ACK/manifest sealing, the unique LASTFINALWRITE releases all proposal, source-analysis, writer, execution, reviewer, child, publication and retained authority; role-local heavy/inflight/pendingExternal/writer/child/publication are all zero, with no active wait.
