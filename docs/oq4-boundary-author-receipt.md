# BoundaryOccupation author implementation receipt

Date: 2026-10-21. This records implementation and execution, not an
independent mathematical or formal review certificate.

Frozen interface: `drafts/oq4/frozen-boundary-occupation-v1.md`.
Final remote source: `Shao/OQ4/BoundaryOccupation.lean` in
`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`.
Local identical source: `drafts/oq4/boundary/BoundaryOccupation.lean`.

Source SHA256:
`1568e5514fc4ca8053ccd9b0f123f86e61cc294df0f6de199c8a688b9d7de8a6`.

Unique author-generated olean SHA256:
`0d0d8341e72e327d32227707beec8d56c55ce9b622445a1a2dd1eba1f73e20d0`.

## Actual server checks

All Lean ran only on the designated server, one process at a time with
CPU affinity 0–3, using Lean v4.36.0-rc1 and mathlib
807d3836b165983210ee2ecf3cd28f239436949c. No local Lean, Git commands,
shared-cache writes, public/root changes, version-lock changes, or edits
to previously reviewed source or its olean were performed.

Complete original logs remain only on the server in
`repro_outputs/oq4-boundary/`:

1. `check-06.log` and `.exit`: all three frozen conclusions, exit 0,
   zero-byte log.
2. `olean.log` and `.exit`: unique same-source olean emission, exit 0,
   zero-byte log.
3. `audit.log` and `.exit`: actual import and dynamic module-ownership
   enumeration with transitive axiom output for every constant, exit 0.

There are 17 explicit declarations (3 definitions and 14 theorems) and
24 generated constants, 41 total. The audit uses
`env.getModuleIdxFor?` plus `env.header.moduleNames`, without namespace or
root-name filtering. It includes the generated imported-name descendant
`Shao.closedUpper.eq_1`. A server parser verified 41 declaration names and
41 axiom records with zero unexpected axioms: 23 standard three-axiom
sets, 11 `{propext, Quot.sound}` sets, and 7 `{propext}` sets. Source scan
found no sorry, admit, added axiom, unsafe, or native_decide.

Earlier logs preserve API adaptations involving a finite-permutation sum
overload, a dependent-coordinate cast, null-measurable-set arguments,
measure extensionality, and tactic-sequence warnings. All were resolved
before final source freeze. Transient bridge failures explicitly reported
`operation_may_have_started=false`; transfers reported zero completed
files and no possible partial file. Only bounded retries were used, and
the final transfer and actual check succeeded. No mathematical source
changes followed the successful zero-diagnostic target.

Read-only dependency hash checks confirmed:

- KilledPathLaw:
  `1f1b664d81e551bb6a58ca335c3b568cfbd684e991e12b733f599a5ed2eada9f`.
- OccupationPayment:
  `3ed77e585a0a687b471d46e004872d35c18d7181388a7828c34e83085bd094d9`.
- FiniteIID:
  `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b`.
- ClosedSurvival:
  `bb6f334d2a7956ebf2d727d2feabd0765c30af33da4e8b4197f1fd658921811f`.

## Source mechanism and constants

The exact killed row is transferred by the certified KilledPathLaw to its
unnormalized surviving endpoint law. Concatenation's product law is
obtained from standard measure-preserving finite-coordinate and sum/product
equivalences. Fixed reversal preserves the iid product law using the
standard `measurePreserving_piCongrLeft` permutation interface; the shared
iid joint-law theorem is not reproved. No probability measure conditioned
on survival is formed.

The proof fixes the entire unconditioned last block before applying the
closed unit-interval concentration bound to the first-block endpoint.
The upper endpoint layer forces reversed lower survival (sMinus), and the
lower endpoint layer forces reversed upper survival (sPlus). Open layer
ends are enlarged to closed interval ends, preserving atoms. The union
bound permits overlap. All events, path maps, interval sections and
measure-preserving transformations have actual measurability proofs.

The numerical reduction proves the natural half-block lengths are positive
and `m <= 3 sqrt(l) sqrt(r)` when m>=6, giving the explicit constant 6.
For h>=3 it proves floor(h^2)>=6 and h^2<=2 floor(h^2), then uses the
nonnegative beta<=M bound to obtain exactly the displayed constant 12.
No division by beta, Cq, or Cs occurs, so zero parameters are retained.

All three final statements retain their real all-product concentration
and upper/lower survival hypotheses. Nu is any Borel probability law,
with no added centering, variance, moment, density, nonlattice, or bounded
support premise. Beta in this module is only the displayed nonnegative
parameter.

## Reproduction

Run sequentially on the designated server:

```sh
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/BoundaryOccupation.lean
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/BoundaryOccupation.olean Shao/OQ4/BoundaryOccupation.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-boundary/Audit.lean
sha256sum Shao/OQ4/BoundaryOccupation.lean .lake/build/lib/lean/Shao/OQ4/BoundaryOccupation.olean
```

`Audit.lean` is locally preserved. `summary.json` is a curated
hash/count/name summary, not a raw log. `declarations.md` lists every
explicit/generated declaration. The anonymous complete proof was written
first in `proof.md`.

Only the conditional reverse-block boundary-occupation mechanism and its
safe constants are proved. S/AC itself, unconditional O0, marked O1/O2,
actual R3/R4, B1, Brownian blocks, K/Kv, 4/pi and OQ4 remain OPEN.
Independent review is separate and is not self-signed here.
