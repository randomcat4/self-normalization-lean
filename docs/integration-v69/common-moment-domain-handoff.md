# SourceMomentDomain author handoff

Status: AUTHOR_KERNEL_ALL_OWNER_AXIOM_PASS; independent complete review pending.
The author is gpt-6.1-sol / xhigh / fresh and does not independently accept this
proof. Writer and execution authority are released; no operation is in flight.

Remote worktree: `/root/rivermind-data/shao-lean-20261021/workspaces/common-fixed-cutoff-exports-v65`.
Branch: `feat/common-moment-domain`.
Source-only commit: `fff5061e2ac508d094e4e6cf07bbfe4ff49f7e04`.
Tree: `293c9bb0e5b3beabc379db7036c16ea15b568f01`.
Source SHA256: `38001730626dfcd13ffc6cee1b226dea9e1361b0f0514f663becfaaf7970eed2`.
Only `Shao/Probability/SourceMomentDomain.lean` is committed. No push, PR or merge.

Both complete public headers match the exact root-frozen text; see
`head-binding-check.json`. The source is UTF-8 with LF. Two public theorems,
seven generated `_simp` theorems, nine actual module-owned declarations, all
theorems, zero definitions of any kind. Actual owner local module index is 4760.

The first theorem integrates the Bernoulli tangent for U=n*z², q=p/2. It derives
the true p-moment lower bound, beta positivity, H positivity and H≤n^(1/6).
For every 0≤x≤H it pays x⁶≤n and n*integral F(x*z)≤1. It does not assume a
Lyapunov comparison or mean zero. The n=1 and x=0 cases use the same paid
nonnegative-power arguments; no division by n-1 or x occurs.

The second theorem constructs the actual quotient pushforward. It explicitly
pays sigma>0, sqrt(n)>0 and b=sigma*sqrt(n)>0. The first moment is integrable
from |z|≤1+z²; the actual map is a probability measure, is centered and has
n*raw2=1. Real-power multiplication and addition yield the exact original
beta denominator. The finite product pushforward is `Measure.pi_map_pi`.
Each weak crossing event is pulled back by a pointwise positive scalar identity;
the argument in fact works for every real sign scalar and therefore covers both
required signs. Neither the energy nor the threshold is divided out, so Q=0,
x=0, negative x, arbitrary atoms and asymmetric raw laws are all retained.

Original producer gate: attempt03, direct rc=0, same-call original object
`/root/rivermind-data/shao-lean-20261021/checks/common-moment-domain/attempt03.olean`,
SHA256 `8f7ccf7d80680f86f52df88e6b239f5d35f51530202422e371dc2f2d3c6ce776`.
Its execution alias is the worktree `.lake/build/lib/lean/Shao/Probability/SourceMomentDomain.olean`
symlink. No successful-source producer recompile occurred. The final log has
only existing package-view local-change and unused-tactic style warnings; the
successful source was kept unchanged.

Attempt01 and attempt02 failed with genuine elaboration/interface errors and
are preserved on the server with source snapshots, SHA256, full logs and native
directrc=1. Main corrections were explicit proof-local rpow-to-power rewriting,
exact function arguments for integral rewrites, current probability-map
instance/API and reinstating goal aliases before rewriting Pnorm. No frozen
statement, assumption or let literal changed. The full-type postprocessor first
rejected its own single-line AX regex, then was corrected to parse multiline AX;
this required no Lean rerun.

One all-owner audit passed with direct rc=0 using the established exporter
template and exact `getModuleIdxFor?` owner equality, no namespace filter.
Every one of nine constants received a transitive `Lean.collectAxioms` check;
only propext, Classical.choice and Quot.sound occur. Full actual types without
omission, names, AX lists, local indices and per-type hashes are in
`actual-owned-types.json`; there are no non-theorem values to export.

All original six dependency pairs and four newly required event-measurability
pairs have been byte-verified against their original accepted objects and exact
source hashes. See `dependency-byte-reuse.json`. Zero old-module Lean commands,
zero cache writes and zero accepted-object copies/recompiles. Resources were
activation before cd, CPU10–13, shared root-heavy.lock, -M8192 -j4,
autoImplicit=false, Elab.async=false. Large logs and binary objects remain on
the server; local evidence is only source and compact receipts/type exports.

The independent reviewer should read the frozen heads, whole 286-line source,
all nine actual full types, and root proof-candidate sections 2 and 9 against
original paper main.tex lines150–218. Existing accepted dependencies need no
repeat kernel or complete proof review. Author-receipt.json binds all evidence.

Next dependency belongs to root: independent complete final review and then
consume this producer for the original C1 assembly. END, SmallBoundary and
assembly remain separate unpaid root work. Every original root remains OPEN.
