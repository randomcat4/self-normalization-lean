# Independent final review: actual complex-boundary amplitudes

STATUS: CORRECT

The exact three frozen bundles are correct. Full source-to-statement,
proof, actual-type/value and axiom coverage is complete. The original
export's two truncated private type records were repaired by a narrowly
scoped type-only supplement, fully read here. Source, object, successful
kernel receipt and all-owned transitive-axiom receipt remain unchanged.
No mathematical or remaining evidence gap was found.

Reviewer: `/root/common_amplitude_final_review`, fresh independent
`gpt-6.1-sol` / `xhigh`; not the author, no implementation ownership, no
subagents. Author `/root/common_complex_amplitude_author` released production
write authority before this review. The reviewer modified only these review
files and `drafts/c12-amplitude-final-review/` evidence. No Lean execution,
producer rebuild, old-proof re-review, axiom rerun, native graph traversal,
cache action, or production edit was performed by the reviewer.

## Exact version and existing mechanical evidence

| Artifact | SHA256 |
| --- | --- |
| `drafts/c12-complex-amplitudes/SourceComplexBoundaryAmplitude.lean` | `ad51e5f6ffc1a80c750c90b71f90fa70fc21ebfdde8b78f8a811c9ee369f06aa` |
| Original reusable `attempt-024.olean` | `5f030a73345db4fbe224b5b42929126bcc34c40dda934f4ad483658025931563` |
| Root declaration freeze | `48a9305bd34eb54c91978ed138f18ced8f0da24112dbd9295ca141fecd1d2fd4` |
| Original kernel log | `13d21e56a622275d67ad20c5f9499de3a3575639d59d77d83b9c2c3c92a0ecdc` |
| Original actual type/value/axiom export | `cf99e34c2ec2d9e643fc0f0d1b74f50ebb2fb6e336e81d8e775118e89dbdd2ac` |
| Exact-owner transitive-axiom JSON | `9c48c9d824372f6b31cb553a10a37a50764ba1483c4c4cd96becb4e39b3ae7d8` |
| Existing exporter source | `17c04aa17ca4cde7fb5f8d84a7d71d4fdf40d8ec0b594be0f97a1e5577f59027` |
| Complete two-type supplement | `9e0bde1240f7d3d0f0f5285be201662659d0180640f2d8e69d6cb5b6aafbc506` |
| Type-only supplement receipt | `468971a6792582f12dd96b1805bf9513be77913c8fe9bcb9718c92c26a5c58f5` |
| Reviewer read-only server observation | `8b6b4d67d5e4dc9bd278979886678467ff49dc2d73895b2e0ed2bd9f2895788d` |

The source is 102443 bytes / 2093 LF lines, UTF-8, zero CR bytes. The
freeze binds candidate `2e4b2b4176c747c532ab02b288848e67e7beab8f4c862a256fce3d2d3ff8d3c1`,
source contract `7025db48dac133182d6b8875d5e2cf26a5ff8d19d6434026e60b49b134e97d6d`
and accepted Sobolev binding
`365ca1e056d05c2e970fe2d5860da6aac23d18dc30c633d3737090f9d39592fd`.

One read-only server request independently checked the existing archive and
current production source/object against these hashes. It observed
`DIRECT_RC=0` in both `attempt-024.rc` and
`complex-amplitude-owned-audit.rc`, frozen parent
`6dbd8394e336af1da55d6bf7c3d3bc3fd87f6a49`, and toolchain
`leanprover/lean4:v4.36.0-rc1`. The original kernel log has zero source error
diagnostics and 60 harmless tactic/lint/deprecation warnings. Raw kernel
logs remain server artifacts; the local observation retains their hashes
and diagnostic classification. Exact server evidence directory:
`/root/rivermind-data/shao-lean-20261021/outputs/common-complex-amplitudes/`.

The established exporter was fully read. Its selection is actual module
ownership via `env.getModuleIdxFor?`, without a public-name/prefix filter.
`Lean.collectAxioms` is transitive and rejects every axiom outside
`propext`, `Classical.choice`, `Quot.sound`. The verified owner map and
export agree on 126 distinct constants: 123 theorem constants and exactly
3 definitions. Source parsing gives 48 authored theorem declarations and
75 generated theorem constants; the three public bundles are a subset of
the 48. No `sorry`, `admit`, new axiom, `unsafe`, or `native_decide` occurs.

## Reading and coverage boundary

All 2093 source lines, including every proof, were read. All three literal
definition values and all three full public statements were compared with
the exact freeze, without changing assumptions. The original actual export
was read in full through a lossless balanced-term abbreviation view: 114
complete subexpressions and two namespace prefixes have explicit expansion
dictionaries; reversing those substitutions reproduces the entire
whitespace-normalized export exactly. No argument, binder, instance,
definition value, or declaration is dropped by that view. The dictionary
and body were read completely. The view SHA256 is
`59039fd4acda6499598f245f9611e7d4952b0e58a2c6274855acc861e7e04459`.

Of the original 126 actual-type records, 124 are untruncated; the two
identified Schwartz-related records are completed by the exact-object
supplement (756593 bytes, two records, zero literal ellipses). Its entire
dictionary and complete body were read using 17 lossless term aliases,
SHA256 `69f34a6e6440d3c03f9868b1602f57074367ed0699831a68df147cdbd2b70494`.
Raw supplement record coverage is lines 3-3911 (`boundary_sobolev`, actual
type lines 4-3910) and 3912-8348 (`actual_demodulated_schwartz_budget`,
actual type lines 3913-8347). Every original visible type fragment matches
the corresponding complete type with only the literal ellipses expanded.
The complete normalized type hashes are respectively
`e9b100b628b908bf3f9cf27a1c9940fde71f2495ea3950dfa673884c47ac7d35` and
`2bccfb9bb506719c9fdd9cb5510572760694b62f2e616d1da4e45bc60a05c997`.
The supplement source hash is
`c4eab6f52c935ec6bf3d9cd2d43bcd0803331259b7d4490ef6526d4d1d30d7a5`;
it only reads these exact owner-qualified constant types, raises printer
limits and returns direct rc0. Before/after producer source/object hashes
are unchanged; no producer compilation, axiom rerun or native traversal
was performed. This repairs exactly the two rendering gaps without
invalidating or repeating other evidence.

All 126 actual types and all three actual values are now complete.
Every generated arithmetic, numeral,
definition-equation, set-membership and simplification type was read and
matched to its parent declaration; none introduces an extra mathematical
premise or an additional definition. The JSON receipt records every owned
name, kind, actual-type hash/range, axiom list, source-parent range and
review coverage. The original export and any repair are preserved separately.

Full old proofs are reused under their qualified exact-source/object
acceptances, rather than reviewed again. The complete actually consumed
source-level heads and literal transform/cutoff/phase values were read
against their exact source hashes. The old complete actual-object
qualifications are reused at the private access seams. The new proofs
that pay the amplitude envelope, sharp norms and localized recursion were
reviewed in full here.

## Source fidelity and frozen interfaces

Read-only originals were hashed:
`main.tex` = `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`;
`supplement.tex` =
`b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`.
Complete relevant passages read: main 610-619; supplement 2415-2430,
2429-2454, 2743-2784, 3222-3241, 3268-3326 and 3664-3698.
These specify the actual allowed cutoff, theta split, two amplitudes,
negative-phase mark, localized derivative decay, Sobolev route and outside
tail. The signed-frequency convention is retained exactly; opposite
spatial phase follows by replacing `u` by `-u`.

`sourceKernelCutoff` is literally the previously accepted bump centered at
25/16 with inner/outer radii 23/16 and 47/32. It is never shadowed or
replaced. The new theta is exactly
`Real.smoothTransition ((t + 1) / 2)`. The amplitude definitions have the
frozen exponential signs and split scale `Delta=(1+lam*y)^(-1)`; the mark is
literally `sourceMarkExponential a y (-u) v`. Expanding the accepted mark
value yields precisely `integral a(r)*exp(-i*(u*y*sqrt(r)+v*r)) dr`.

All bundles retain `y>=2`, `1/16<=N<=7`, `lam>=y/sqrt(N)`, both branches,
all real spatial points and frequencies. No amplitude, derivative,
Fourier-norm, or tail estimate is supplied as a public hypothesis. The
fixed positive constants precede all growing parameters; the outside
constant also precedes `aStar`. Orders 0 through 32 are included, and the
requested decay rate is the literal `1/256`.

## Mathematical proof review

**Theta and actual amplitudes (source 35-842).** Global smoothness of theta
is affine composition. Its closed plateaux and range are retained. Compact
jet bounds on [-1,1], a finite sum over `Fin 33`, and local constancy on
the two complementary open rays give one bound before every derivative
order and point, including order zero and both endpoints.

The amplitude is smooth on the actual cutoff support, where `r>1/16`.
Outside that support the literal amplitude is locally zero, so totalized
square root/division cause no off-support differentiability gap. Compact
support, nonnegativity and the closed upper/lower split supports are
proved directly. Recombination uses only the displayed exponent algebra
and is valid for every real r.

The setup derives `lam*y>=1`, `1/4<=sqrt(N)<=3`, and `0<Delta<=1` from
the unchanged public assumptions. A proof-local positive smooth extension
of sqrt agrees with actual sqrt for every r>=1/16; its compact jet bound
is fixed before the parameters. It changes no global definition.
The accepted actual chi derivative budget is specialized at k=0, theta=0.
Finite-order composition and two actual Leibniz formulas pay all amplitude
derivatives. For the upper branch the favorable side uses
`sqrt(r)+sqrt(N)<=5`; for the lower branch the coefficient
`sqrt(r)/(sqrt(N)*(sqrt(N)+sqrt(r)))` lies in [1/60,19/5]. The unfavorable
side is confined to distance Delta. These yield the fixed exponent
`4-|r-N|*(1+lam*y)/256`, uniformly including N endpoints and centers outside
the chi support. Off actual amplitude support all iterated derivatives
vanish locally. No vanishing Leibniz term is treated as nonzero.

The exact exponential envelope integral is `512/(1+lam*y)`, with both
half-line integrability and translation proved before the integral
comparison. Domination pays genuine integrability of every derivative,
then gives `C*Delta/Delta^k`. The final enlarged constant covers the
pointwise and L1 conclusions together. The proof never substitutes a
totalized integral for an Integrable obligation.

**Actual mark and sharp norms (source 843-1612).** The mark integral is
identified with the literal negative phase. True phase-integrand L1 and
continuity follow from the compact actual amplitude and a norm-one phase.
The accepted coarse global norm theorem is used only after deriving the
actual C2 amplitude budget, and pays genuine unweighted/weighted Fourier
integrability. Its coarse numerical bounds are not used as the sharp
localized estimates.

Let Q=Delta^-1, T=y|u|, R=Q+T/Q. Polynomial absorption into the weaker
exponential rate 1/512 proves weighted amplitude estimates for spatial
powers 0,1,2. For the literal physical-coordinate demodulation
`b(r)=a(r)*exp(i*(-u*y*sqrt(r)+(u*y/(2sqrt(N)))*r))`, smooth extension agrees
on support and local zero handles its complement. The centered phase has
first derivative at most `16*T*|r-N|` and second derivative at most G*T.
The actual product derivatives therefore satisfy budgets D, D*R, D*R^2
times the same localized exponential. Integrating their squares gives
L2-squared budgets `512*D^2/Q`, `512*(D*R)^2/Q`, and
`512*(D*R^2)^2/Q`. The produced Schwartz representative has exactly the
same function value, with A=S/sqrt(Q), S=32*D. It is not a separately
assumed amplitude.

The exact qualified private Sobolev theorem is applied to this actual b
with R>=1 and all three proved budgets. Its frequency is the unit phase
`exp(-i*v*r)`, including its already qualified normalization. There is no
missing rescaling factor: working directly in physical r gives
`sqrt(R)/sqrt(Q)=sqrt(1+T/Q^2)<=1+sqrt(T)/Q`.
For c=u*y/(2sqrt(N)), the actual identity is B(v)=U(v+c). Translation
preserves the unweighted integral. The weighted integral is bounded by
`integral |v|*|U(v)| + |c|*integral |U(v)|`; genuine integrability of both
sides is paid, `|c|<=2*T`, and R<=Q+T. Thus one fixed enlarged constant
gives the exact frozen widths `1+Delta*sqrt(T)` and
`(Delta^-1+T)*(1+Delta*sqrt(T))`, for every real u including zero.

This physical-coordinate proof differs algebraically from the draft
contract's affine-z route but has identical scale and conclusions. It
does not weaken or add a mathematical assumption.

**Genuine localized IBP32 and outside31 (source 1367-1482, 1614-2022).**
A joint compact smooth regularization constructs J(w,r) with one uniform
bound for every r derivative through 32, before w. Its parameter bump is
one on closed |w|<=1/16, and its r bump is one on [1/16,4]. On that actual
box J is exactly `(1+w/(2sqrt(r)))^-1`. On the larger bump support r>=3/64
and |w|<=1/8, the denominator stays positive. Off that support the numerator
is locally zero, so the globally totalized reciprocal introduces no
smoothness gap. All regularizers are proof-local.

For fixed w, the actual recursion is `F0=a`,
`F(m+1)=deriv(Fm*J(w))`. Every Fm is globally smooth/compact, with support
inside actual a. An induction keeps all remaining L1 jets simultaneously:
for m+j<=32, `integral |D^j Fm| <= A*(M*2^32)^m*Q^(m+j)/Q`.
The successor uses the full j+1 Leibniz sum, the genuine preceding
derivative L1 bounds, Q>=1 and the binomial sum `2^(j+1)<=2^32`.
This is a proved recursion bound, not a supplied oscillatory estimate.

For v!=0 and |u*y/v|<=1/16, put w=u*y/v and
phi(r)=r+w*sqrt(r), q=phi'. The slope is nonzero on actual support
(indeed q>=7/8 there). Globally `Fm/q=Fm*J(w)` because Fm vanishes off
support; hence its required smoothness is paid. The qualified single-step
IBP theorem is applied at frequency -v with all support, continuity,
derivative and nonzero-slope conditions. Iteration proves the actual
identity `|v|^m*norm(B(v))=norm(I_m)` for every m. At m=32 the genuine
F32 L1 budget gives `|v|^32*norm(B(v))<=P*Q^31`.

The separate actual a L1 payment gives `norm(B(v))<=A/Q` for every v.
Combining |v|<=Q and |v|>Q yields
`(1+|v|/Q)^32*norm(B(v))<=C/Q` in the cone. The v=0 branch uses only the
low-frequency bound, so no division by zero is hidden. The strict outside
condition `|v|>|u|/aStar`, `aStar>0`, and `aStar*y<=1/16` pays the cone
for both frequency signs. When u=0 the outside set excludes only v=0 and
the same reasoning applies.

For G(z)=Q*norm(B(Q*z)), the profile bound is fixed independently of all
parameters. The accepted generic profile-tail theorem is used only after
paying that actual bound, continuity and nonnegativity. A positive change
of variables v=Q*z, including the indicator-set transport, cancels Q and
gives exactly `C/(1+Delta*|u|/aStar)^31`. Actual outside integrability also
follows from the already paid global L1. No raw-moment condition or
weighted outside assertion is introduced.

**Final assembly (source 2024-2093).** The maximum of two fixed positive
constants precedes y,N,lam,j,u,aStar. All literal phase, genuine
integrability, continuity, sharp norm and outside conclusions are retained
in one conjunction. Algebra only rewrites Q^-1 to the frozen Delta and
transports the already proved tail denominator.

## Exact accepted dependencies reused

| Module | Source SHA256 | Original object SHA256 |
| --- | --- | --- |
| SourceFourierTestKernel | `151fe42cda5414873ea9c9ea3359d256e971132073ea9d1c714ea0105af234d3` | `f3d751f7a84fa991841a6a005e009b1d6ee28cb2347f55a0280417637adaaeba` |
| SourceKernelAmplitudeFamily | `1a5c4ca17ab1cfbad4565412827f3546de519512a577a7e4041347f9c48e9970` | `15cc5fde79f240f26782f0daabf9c49c1a06f60968068cebf2a684818db94ff7` |
| SourceMarkFourierNorms | `67d7b455b31fd939d56f78d760f3fea0f331e375c27bcd6f1aea3ce9ab902998` | `fa56f513ff44ca0d09436ddbb241a7b6840e3161b5aecc6048c7074f75f0fe87` |
| SourceKernelMarkedOutside | `dadbe680967951cc91272055c4cd99688616631b4125cbc999ff5c602b63c868` | `2be9fff325937c535766dbfd9d8f69c618d358fe69ed9c994caa643672e2dd35` |

The four current consumed server objects were independently hash-verified
in the single read-only request. Local curated sources have the displayed
hashes. Read complete consumed cutoff value/data (source 14-28), family
head (171-180), mark value (13-15), private unit transform (161-162),
private Sobolev head (178-188), private product-derivative head (256-263),
global mark norm head (666-679), literal markedPhase (129-130), private
single-step IBP head (178-185), and private generic profile-tail head
(1000-1006). Their existing complete CORRECT qualifications are reused.

The four private access seams in the two old modules use the exact numeric Lean.Name prefix
`_private.Shao.Probability.<Module>.0.Shao.Probability`, followed by the
actual theorem name. The bridge proof is simply `apply` that qualified
constant and supply the complete matching hypotheses; the successful new
source kernel check confirms access. No old source edit, copied proof,
new axiom, public bridge definition or upstream rebuild is involved.

Qualified review bindings: kernel v46 review JSON
`64e9f7e5ebc28bff4e564172e1bcafba5820b073742381244f48ead60a625e2a`;
amplitude v49 review JSON
`594b50d45d7964c74eb0c34329689e0e7128385245320e9fad03d589f0409746`;
mark v48 review JSON
`f9d7830d58941d366e31a4f2be3c0316a57651be33d925882f49b5a23d34ca04`
and corrected complete export
`5718163a79644f31771ba00a6c73133c42618d12ed8f3ea2b3fb33ece14db671`;
marked outside v49 review JSON
`b560fa53ce6c835cca47cff51faf9b384847bbbb7354a66825ab5dc7143039f0`.

## Scope and remaining work

This milestone pays the exact fixed-theta/actual-amplitude localized
producer, sharp localized mark norms and outside31 at order32. It makes no
novelty claim. It does not prove contour deformation, shifted inversion,
the growing complex kernel or Xi, probability bounds, summation,
desmoothing, or any original C1/C2/OQ root theorem. All original root groups
remain OPEN. Root integration must bind this unchanged source/object and
the repaired review coverage to its aggregate interface checks.

No proof correction is requested. The report and companion
`coordination/common-amplitude-final-review.json` bind this exact accepted
scope. Reviewer report-write authority is RELEASED at completion; no
production ownership, resource lock, Lean process, audit process or child
context remains with this reviewer. Root owns subsequent integration.
