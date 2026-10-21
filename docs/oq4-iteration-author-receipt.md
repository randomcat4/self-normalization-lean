# KilledIteration implementation receipt

Date: 2026-10-21. This is an implementation and execution receipt, not an
independent mathematical or formal review certificate.

Frozen interface: `drafts/oq4/frozen-killed-iteration-v1.md`.

Final source: `Shao/OQ4/KilledIteration.lean` in remote worktree
`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`.
Local identical source: `drafts/oq4/iteration/KilledIteration.lean`.

Source SHA256:
`03b97e5708ffa552cfa4eccec5cf3c042da9805f9ab69561f4cb3e2701a690b5`.

Unique author-generated olean SHA256:
`b4c434c5d9eec412d791f0970c68fca40bde9fca356d9227687947c3bdd2bb15`.

Read-only certified one-step dependency `Shao/OQ4/KilledKernel.lean` was
rechecked at SHA256
`f90c1996f4c220473371b0f5ea3c74a7b8287e8f997f1a2cd3f0831cd6bd626f`.

## Executed checks

All Lean commands ran only on the designated server, one Lean process at a
time, affinity CPUs 0–3. The shared package cache was read-only. No Git,
root-import, common-source, dependency-lock, or reviewed-source changes
were made. Lean is v4.36.0-rc1 with mathlib
807d3836b165983210ee2ecf3cd28f239436949c.

1. Full module target: `repro_outputs/oq4-iteration/check-02.log`, exit 0,
   empty log (no errors or warnings).
2. Actual olean generation:
   `.lake/build/lib/lean/Shao/OQ4/KilledIteration.olean`,
   `repro_outputs/oq4-iteration/olean.log`, exit 0, empty log.
3. Import of that olean and dynamic declaration/axiom enumeration:
   `repro_outputs/oq4-iteration/Audit.lean`,
   `repro_outputs/oq4-iteration/audit-02.log`, exit 0.

The audit dynamically enumerated 33 new constants: 26 explicit declarations
(3 definitions, 1 instance, 22 theorems) and 7 generated constants. All 33
transitive axiom sets are subsets of `{propext, Classical.choice,
Quot.sound}`. Local parsing verified 33 declaration records and 33 axiom
records, with no unexpected axiom. The source contains no sorry, admit,
new axiom, unsafe, or native_decide. Complete names are in `declarations.md`;
the actual audit output remains on the server. A raw local audit-log copy was
removed by the lead under the shared workspace log policy; this curated receipt
and declaration ledger retain the result without copying full logs.

The preserved first target log `check-01.log` records two API-adaptation
errors (successor normalization and the namespace of the library integral
composition theorem). Both were fixed before the final source was frozen.
The first audit log `audit.log` on the server records a counter type
inference error in the audit helper; the helper was explicitly annotated
as Nat and passed as `audit-02.log`. Neither audit change modified the
frozen mathematical source.

## Reproduction

Run on the designated server, keeping the commands sequential:

```sh
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/KilledIteration.lean
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/KilledIteration.olean Shao/OQ4/KilledIteration.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-iteration/Audit.lean
sha256sum Shao/OQ4/KilledIteration.lean .lake/build/lib/lean/Shao/OQ4/KilledIteration.olean
```

`Audit.lean` is preserved locally as well. It constructs its root list from
every explicit module declaration, enumerates each root and generated
descendant from the imported environment, and invokes `#print axioms` for
each name, so dependency axioms are checked transitively.

## Scope

The implementation covers all four frozen goals: actual kernel powers and
identity zero step; uniform finite/subprobability bounds and exact support;
bounded Borel integrability, measurability and the mass-weighted bound;
zero/one-step formulas, genuine integral semigroup, real linearity,
absolute-value domination, and global/closed-source order. It imposes no
moment assumptions and treats arbitrary real h, including h=0 and h<0.

The anonymous complete derivation is `proof.md`. No iid path equivalence,
occupation input, R3/R4/O0, Brownian approximation, or long-time theorem is
certified by this module. K, Kv, and OQ4 remain OPEN. Independent review is
arranged by the parent and is not self-signed here.
