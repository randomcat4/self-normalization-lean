# KilledPathLaw author implementation and execution receipt

Date: 2026-10-21. This is an author implementation receipt, not an
independent mathematical or formal certification.

Frozen interface: `drafts/oq4/frozen-killed-path-law-v1.md`.
Remote source: `Shao/OQ4/KilledPathLaw.lean` in
`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`.
The local identical source is `drafts/oq4/path-law/KilledPathLaw.lean`.

Final source SHA256:
`1f1b664d81e551bb6a58ca335c3b568cfbd684e991e12b733f599a5ed2eada9f`.

Unique author-generated olean SHA256:
`6dc60412e5024fc6691b0115025f4a5fb90bcb98574467b1d244cd415b127958`.

## Execution and unchanged dependencies

All Lean commands ran only on the designated server, sequentially with
CPU affinity 0–3, using Lean v4.36.0-rc1 and mathlib
807d3836b165983210ee2ecf3cd28f239436949c. The author did not modify any
previously reviewed or common source, root import, Git state, version
lock, shared cache, or common dependency olean. The parent prepared the
common project dependency artifacts; the author generated only this
module's olean. No local Lean execution took place.

Read-only dependency SHA256 checks confirmed:

- KilledIteration:
  `03b97e5708ffa552cfa4eccec5cf3c042da9805f9ab69561f4cb3e2701a690b5`.
- ClosedSurvival:
  `bb6f334d2a7956ebf2d727d2feabd0765c30af33da4e8b4197f1fd658921811f`.
- FiniteIID:
  `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b`.
- MeasurablePath:
  `827dc47b74dae67101a4d874f412e4cb55bafe1e67b9ba767c6896c0b7e58b41`.

## Actual final checks

Original complete logs remain only on the server in
`repro_outputs/oq4-path-law/`:

1. `check-05.log` and `.exit`: complete module target, exit 0, zero-byte log.
2. `olean.log` and `.exit`: unique same-source olean emission, exit 0,
   zero-byte log.
3. `audit.log` and `.exit`: import of that olean and actual dynamic
   transitive-axiom audit of every declaration owned by this module, exit 0.

The audit filters by `env.getModuleIdxFor?` and
`env.header.moduleNames`, with no namespace or root-name restriction.
It therefore also covers any auxiliary constant generated under an
imported declaration name. There are 20 explicit declarations (2
definitions, 18 theorems) and 15 generated constants, 35 total. A server
parser verified 35 names and 35 axiom records, with zero unexpected
axioms. The sets are: 23 standard three-axiom sets, 10
`{propext, Quot.sound}` sets, and 2 `{propext}` sets. Source scan found
no sorry, admit, added axiom, unsafe, or native_decide.

Earlier complete logs are preserved on the server. Initial checks fixed
classical event decidability, a dependent Fin-cons cast simplification,
deprecated set-notation lemma names, and syntactic composition/preimage
forms needed by rewrite matching. One connection operation reported
`operation_may_have_started=false` and `remote_may_still_be_running=false`;
the successful bounded retry verified the uploaded source before checking.
No final source changes followed the zero-diagnostic check.

## Reproduction

On the designated server, run sequentially:

```sh
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/KilledPathLaw.lean
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/KilledPathLaw.olean Shao/OQ4/KilledPathLaw.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-path-law/Audit.lean
sha256sum Shao/OQ4/KilledPathLaw.lean .lake/build/lib/lean/Shao/OQ4/KilledPathLaw.olean
```

The exact audit helper is preserved locally as `Audit.lean`.
`summary.json` is a curated hash/count/name summary, not a raw log.
The complete explicit/generated list is in `declarations.md`. The anonymous
complete mathematical proof was written first in `proof.md`.

## Scope

The implementation proves every frozen item. The core is a stronger
nonnegative measurable-test integral identity. It uses the genuine kernel
composition, the unconditioned product first-coordinate/tail split, and
exact prefix identities. Equality of all such tests gives the exact
unnormalized row measure. Bounded Borel real tests on both sides are
genuinely integrable before their integral equality is used. The constant
test gives real survival mass. Arbitrary iid samples are transferred using
the already shared joint-law theorem; it is not reproved.

All n,h,z are allowed in the shifted interface. Time zero has no extra
kill, so an outside start still has the row delta_z. Positive-time walls
remain weak and retain atoms. The common closedStrip connection requires
only z=0 and h>=0 and includes n=0, h=0, zero paths, and endpoint equality.
No moment, density, nonlattice, bounded-jump, or post-survival independence
assumption is added.

O0/R3/R4/B1, Brownian approximation, energy-denominator assertions,
long-time limits, K/Kv, 4/pi, and OQ4 remain OPEN. Independent review is
separate and is not self-signed here.
