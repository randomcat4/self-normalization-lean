# Independent final review — actual marked outside-v tails

STATUS: CORRECT

Reviewer: /root/common_outside_mark_review, fresh independent gpt-6.1-sol/xhigh.
Completed: 2026-10-23T10:25:26+00:00. No source edits, subagents, Lean execution,
builds, cache writes or repeated successful gates.

Frozen author commit: `34d5657179e38d070bd1fd4b7645d0f74a61e826`.
Module: `Shao.Probability.SourceKernelMarkedOutside`.
Public theorem: `Shao.Probability.sourceKernel_marked_outside_norms`.
The amplitude-family commit `f607d3399121d6058d09e96eca8bf299f6e12076`
is an ancestor.

## Exact source and accepted inputs

- Target source SHA256:
  `dadbe680967951cc91272055c4cd99688616631b4125cbc999ff5c602b63c868`.
  All 1100 lines / 57844 bytes read. Local draft, current server source and
  frozen commit blob agree. UTF-8 LF, no CR/BOM or forbidden proof terms.
- Target object SHA256:
  `2be9fff325937c535766dbfd9d8f69c618d358fe69ed9c994caa643672e2dd35`.
- Complete second statement equals the original declaration freeze after
  whitespace removal. Candidate SHA256
  `ad064d55bd60ef9770c5c67ce1a16600a0afdbcd67d695b0849f9f880b484806`;
  contract SHA256
  `9af7cff8c8088425844e7c6d09880bed3c82ff9e5b08313910a2269b8231a115`.
- Accepted amplitude source/object remain
  `1a5c4ca17ab1cfbad4565412827f3546de519512a577a7e4041347f9c48e9970` /
  `15cc5fde79f240f26782f0daabf9c49c1a06f60968068cebf2a684818db94ff7`.
  Complete public interface and interaction read; reuse its sole accepted
  CORRECT review and root scope acceptance, without repeating internal proof review.
- Accepted actual cutoff source/object remain
  `151fe42cda5414873ea9c9ea3359d256e971132073ea9d1c714ea0105af234d3` /
  `f3d751f7a84fa991841a6a005e009b1d6ee28cb2347f55a0280417637adaaeba`.
  Its actual bump definition and full data interface were read. This separately
  accepted dependency is present in the worktree but is not a tracked path in
  this earlier author commit; no commit provenance is invented for it.
- Target and family paths are clean. Unrelated new consumer work may change
  the worktree/head; whole-tree cleanliness and unchanged current HEAD are
  not acceptance requirements.

## Source-to-statement fidelity

Read the original supplement LF2402–2424,2571–2582,3252–3266, full source
SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`.
The formal theorem uses the exact accepted
`chi(r)/(sqrt(r)+theta)^k`, k=0/2, with CLOSED signed
`|theta|<=1/16`. The additive theta is distinct from the later localized
smooth-step Theta. There is no free amplitude, derivative budget or tail
estimate premise.

Constants precede k,theta,aStar,y,u,w. The statement retains aStar>0,
0<=y<=2, aStar*y<=delta and |w|<=y/16. The true inline B/Bsin integrals,
strict outside set |v|>|u|/aStar, all four actual IntegrableOn conclusions,
both weighted tail exponents31/30, and min(y|u|,1) are unchanged. The
source threshold factor c is absorbed into aStar=a_*/c as frozen; later
consumer scale payments are not certified here.

## Proof review

1. Lines35–127 prove local-zero quotient smoothness, recursive smoothness/
   support retention, compactness, uniform bounds and the exact affine
   r-slice derivative. The actual recurrence is
   F_(n+1)=D_r(F_n/q), not a surrogate derivative estimate.
2. Lines178–278 apply genuine whole-line integration by parts and iterate
   it through32. With g=F_n/q, the proof pays g*q=F_n globally and actual
   integrability of all three products in the standard library IBP theorem.
   All recursive amplitudes and quotients have r-support in [1/16,4];
   therefore their boundary products vanish exactly on a containing fixed
   interval [-1,5]. This is actual compact-support boundary removal.
3. Lines280–457 build a compact JOINT (s,theta,r) family before choosing
   frequencies. On the outer box |s|,|theta|<=1/8 and r in [1/16,4],
   sqrt(r)>=1/4, the denominator is positive and
   q=s/(2sqrt(r))-1 lies in [-5/4,-3/4]. The inner closed bumps are one.
   The exact outside condition gives v!=0 and |u*y/v|<=1/16.
   The uniform F_32 bound is independent of s,theta,v; both signs of v
   are retained. Low |v| is handled separately by the j=0 actual bound.
4. Lines459–754 prove ordinary Fourier IBP32 for the actual low-parameter
   cosine and sine-derivative families. Integral differentiation is
   dominated by the integrable |a(r)sqrt(r)|. The complex-valued mean-value
   norm inequality and S(0)=0 give C|s|. The exact trig shift and
   |u*w|<=y|u| preserve the small factor without dividing by y.
5. Lines756–868 use the exact two exponential phases +/-u, including their
   true shift factors and I/2 sign, then split y|u|<=1 versus >1.
   This proves the exact sine minimum factor. Closed theta endpoints,
   u=0 and y=0 are included; y=0 forces w=0 through the original bound.
6. Lines870–1025 prove continuity of the actual parameter integrals and
   integrate the positive reciprocal-power envelopes on the measurable
   strict tail set. Reflection/translation give the exact real-power tail.
   The |v| weight lowers power32 to31 and hence yields exponent30.
7. Lines1027–1098 assemble the unchanged public statement with
   delta=1/16 and C=2*max(Ce,Cs)>0, proving all integrability and tail outputs.

No critical mathematical, semantic or evidence gap was found.

## Complete actual declaration and axiom coverage

The successful server export
`outputs/common-cone-derivatives-v44/marked-outside-actual-owned-types-values-and-axioms.log`
has 417942 bytes / 5719 lines and SHA256
`e382986584f0c9f42b6cf6c55c4afe7ef06f7fb48f44d09a824782c975da634f`.
I read ALL 101 actual types and ALL16 actual definition values, including
private/generated relations, the dependent Nat matcher and recursive bodies,
bump constructors/obligations, all generated simp relations, and the repeated
complete public type. To bound context, repeated complete balanced
subexpressions were presented with a fully read 51-entry exact abbreviation
dictionary. Expanding that dictionary reproduced the full whitespace-normalized
raw export exactly. No mathematical content or instance argument was discarded;
this was not a names/prefix-only inspection. There are no ellipses or
pretty-printer truncation markers.

The JSON report contains a per-constant coverage entry with exact owner,
kind, source location, actual-type/value ranges and hashes, axioms and
review conclusion. The 101 unique exported names exactly equal the actual
module-owner map:85 theorems including generated,16 definitions including
generated,1 public theorem. The exporter selects by exact
env.getModuleIdxFor? ownership, not a namespace prefix, and runs transitive
Lean.collectAxioms on EVERY owned constant. The exporter itself was fully
read (SHA256
`49a0863c34fd01521bd789c94376f3f9baff97acfd070ecfbe9a79a1d56b15a8`).
Owned-audit JSON SHA256:
`eab6324f6c42b19f57857fa8d473e0006a3ee1768477e631a3c23fb64153a750`.
The only transitive axioms are propext, Classical.choice and Quot.sound.

Reuse the exact successful author kernel/all-owned-audit receipts.
Kernel exit0; kernel log SHA256
`e737184c2f87adf2667327bab4abebab172f4f20d49ec8e12bd6dc6246ad139b`
contains the existing mathlib local-changes warning only. Toolchain is
leanprover/lean4:v4.36.0-rc1; pinned and actual mathlib commit is
807d3836b165983210ee2ecf3cd28f239436949c. No new Lean or cache gate was run.

A read-only metadata query initially requested the separately accepted cutoff
from the earlier target commit and exited1 because that path was not tracked
there. No write/check occurred; direct target/family commit equality and the
accepted cutoff current source/object hashes were then verified. The failed
query is recorded in the JSON and does not alter successful mechanical evidence.

## Scope and release

CORRECT for the exact frozen N0=32 actual outside-v producer. There is no
generic-N0, actual Region3/5 probability, whole-u IBP, inversion, localized
growing-y, de-smoothing or C1/C2 closure claim. Actual scale inequalities,
moving domains and remaining source consumers stay open.

REVIEW_COMPLETE_RELEASED. Only the two review files were written. No source,
reviewer heavy process or child remains owned/running; the different author
continues the next source-bound consumer.
