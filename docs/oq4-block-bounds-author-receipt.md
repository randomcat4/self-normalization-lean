# KilledBlockBounds author implementation receipt

Date: 2026-10-21. This records implementation and actual checks, not an
independent mathematical or formal review certificate.

Frozen interface: `drafts/oq4/frozen-killed-block-bounds-v1.md`.
Remote source: `Shao/OQ4/KilledBlockBounds.lean` in
`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`.
Local identical source: `drafts/oq4/block-bounds/KilledBlockBounds.lean`.

Final source SHA256:
`cc46dc9257cc89d6e31139a60593a419d296fd5f691f10eb565d6310d9dd2408`.

Unique author-generated olean SHA256:
`4539e4db00306349dc262de4308f76510a07686a92ab0d96a31ac3b029c06f9c`.

## Actual execution

All Lean ran only on the designated server, one process at a time with
CPU affinity 0–3, using Lean v4.36.0-rc1 and mathlib
807d3836b165983210ee2ecf3cd28f239436949c. No local Lean, Git commands,
shared-cache writes, version-lock changes, public/root edits, or changes
to previously reviewed source or oleans were performed.

Complete original logs remain only on the server in
`repro_outputs/oq4-block-bounds/`:

1. `check-02.log` and `.exit`: full module target, exit 0, zero-byte log.
2. `olean.log` and `.exit`: unique same-source olean emission, exit 0,
   zero-byte log.
3. `audit.log` and `.exit`: actual import and dynamic audit of every
   module-owned declaration with transitive axiom output, exit 0.

The ownership filter uses `env.getModuleIdxFor?` and
`env.header.moduleNames`, with no namespace or root-name restriction.
There are 10 explicit declarations (4 definitions, 6 theorems) and 13
generated constants, 23 total. A server parser verified 23 declaration
names and 23 axiom records, with zero unexpected axioms. Fourteen sets
are `{propext, Classical.choice, Quot.sound}` and nine are `{propext}`.
Source scan found no sorry, admit, added axiom, unsafe, or native_decide.

The first check exposed only a redundant tactic after field simplification
and one tactic-sequence warning. These were repaired before final freeze.
No source changes followed the successful zero-diagnostic check.

Read-only source hash checks confirmed:

- BoundaryOccupation:
  `1568e5514fc4ca8053ccd9b0f123f86e61cc294df0f6de199c8a688b9d7de8a6`.
- KernelAbsorption:
  `b11d2f68db3581ed61abab670e72234b950df669b379e98f65172f3097f5d168`.
- AveragedResidual:
  `ffe155446ff31b1f1e20dc6ff1b8dc14b1c5274b2593a4cc774183b053491aa2`.
- KilledPathLaw:
  `1f1b664d81e551bb6a58ca335c3b568cfbd684e991e12b733f599a5ed2eada9f`.

## Probability premises and actual kernel instantiation

The two new input predicates package only the frozen all-time real
product probabilities. `iidIntervalConcentration` quantifies every natural
t>=1 and real x, on the existing prefix endpoint in the closed interval
[x,x+1]. `iidOneSidedSurvival` quantifies every natural t>=1 and real
d>=0 and retains both the existing closedUpper event and the lower event
formed by negating the path. No kernel, layer, residual, mass-block, or
finite-absorption conclusion is embedded in either predicate.

The layer theorem specializes them at the two positive natural half-block
lengths and at d=j+1. It obtains the actual killed-row layer estimate from
BoundaryOccupation for every natural j. The generic beta parameter of
this auxiliary is instantiated as the actual integral of |y|^3 in the
full-moment theorems; its nonnegativity follows from integral_nonneg.

R3 instantiates AveragedResidual with precisely
`killedIterKernel nu h floor(h^2) z`. Its finite instance, real mass <=1,
and AE closed support are supplied by actual kernel theorems, and its
layer premise is the result just obtained, not a new hypothesis. The
conclusion includes genuine residual integrability and the actual
`killedAction` bound. Beta<=M yields exactly the displayed residual
constant E.

R4 rewrites the actual mass using KilledPathLaw. A surviving path from
z>=0 belongs to the closed upper event at depth h-|z|; from z<0 it belongs
to the closed lower event. The zero prefix is admitted using |z|<=h.
The all-time survival input pays this actual event. The floor/root bound
and a closed-source cosine chord inequality then give A=2Cs and B=2CsM.
No global nonnegativity of cosine is asserted.

The final D8 theorem retains all three genuine moment integrabilities,
mean zero, second moment one, beta<=M, M/Cq/Cs nonnegativity, h>=3,
pi(1+M)<=h, floor(h^2)<=N, the exact smallness inequality, and S/AC.
It has no separate R3 or R4 hypothesis: the two actual block theorems
provide those hypotheses internally to KernelAbsorption. The constants
are exactly C_layer=12CqCsM(1+M), E=pi^3M/48+2pi C_layer(1+2M),
A=2Cs, B=2CsM, R=exp(pi^2), and H=2(1+AR)R.

## Reproduction

Run sequentially on the designated server:

```sh
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/KilledBlockBounds.lean
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/KilledBlockBounds.olean Shao/OQ4/KilledBlockBounds.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-block-bounds/Audit.lean
sha256sum Shao/OQ4/KilledBlockBounds.lean .lake/build/lib/lean/Shao/OQ4/KilledBlockBounds.olean
```

The exact helper is preserved locally as `Audit.lean`. `summary.json` is
a curated hashes/counts/names summary, not a raw log. `declarations.md`
lists every explicit and generated name. The anonymous complete proof
was written first in `proof.md`.

This establishes the reduction from explicit S/AC to actual layer/R3/R4
blocks and conditional finite D8. S/AC themselves, B1, Brownian and
terminal-block estimates, long-time K/Kv, 4/pi, energy-denominator results
and OQ4 remain OPEN. No fourth moment, density, nonlattice or bounded
support premise is added; rho is not identified as a killed eigenvalue.
Independent review remains separate and is not self-signed here.
