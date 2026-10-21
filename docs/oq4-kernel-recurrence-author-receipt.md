# KernelRecurrence implementation and execution receipt

Date: 2026-10-21. This is an author implementation receipt, not an
independent review certificate. The module has not been self-certified.

Frozen interface: `drafts/oq4/frozen-kernel-recurrence-v1.md`.

Final remote source: `Shao/OQ4/KernelRecurrence.lean` under
`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`.
The local identical source is `drafts/oq4/recurrence/KernelRecurrence.lean`.

Source SHA256:
`a4a5fc67cf47c8e188cbe2e2360afa4fa1bfe0a7082bb9f30fbacd6a5ad5c940`.

The unique author-generated olean at
`.lake/build/lib/lean/Shao/OQ4/KernelRecurrence.olean` has SHA256
`d1f24ac02e42162948d390054a92e034f5952e090145cb0f2700930da5e5f45a`.

Read-only dependency sources were checked at the exact frozen hashes:

- KilledIteration:
  `03b97e5708ffa552cfa4eccec5cf3c042da9805f9ab69561f4cb3e2701a690b5`.
- AveragedResidual:
  `ffe155446ff31b1f1e20dc6ff1b8dc14b1c5274b2593a4cc774183b053491aa2`.

KilledIteration was still undergoing final independent review when this
new unit was assigned. This receipt records implementation/check results
only and does not anticipate that independent verdict.

## Actual server results

Lean v4.36.0-rc1; mathlib
807d3836b165983210ee2ecf3cd28f239436949c. All Lean commands ran only on the
designated server, sequentially with CPU affinity 0–3. No local Lean,
shared-cache writes, Git commands, public/root changes, dependency-lock
changes, or edits to any previously reviewed source were performed.

Full logs remain only on the server in `repro_outputs/oq4-kernel-recurrence/`:

1. `check-03.log` and `.exit`: complete source target, exit 0, zero-byte log.
2. `olean.log` and `.exit`: actual unique olean generation, exit 0,
   zero-byte log.
3. `audit-module.log` and `.exit`: corrected import of that olean and dynamic
   enumeration of all declarations owned by the KernelRecurrence module,
   without any namespace/root-name filter, exit 0.

The corrected audit checked 37 constants: 23 explicit declarations (5
definitions, 18 theorems) and 14 generated constants. It printed the
transitive axiom set of every constant. A separate server parser verified
37 names and 37 axiom records, with zero unexpected axioms: 29 use
`{propext, Classical.choice, Quot.sound}`, 7 use `{propext}`, and one uses
`{propext, Quot.sound}`. The source token scan found no sorry, admit,
added axiom, unsafe, or native_decide.

The original 36-count audit was incomplete: its explicit-root-prefix
filter omitted `Shao.OQ4.killedAction.congr_simp`, a new constant generated
under an imported declaration name. The corrected helper uses
`env.getModuleIdxFor?` and `env.header.moduleNames` to select every
declaration owned by the imported `Shao.OQ4.KernelRecurrence` module,
regardless of its name. The formerly omitted constant was actually
rechecked and has transitive axioms
`{propext, Classical.choice, Quot.sound}`. Original `audit.log` and its
36-count result remain preserved on the server for transparent history.
Only the import audit was rerun for this correction: mathematical source,
target-check results, and the uniquely generated olean were not changed
or rebuilt. Their hashes still match the values recorded above.

Earlier diagnostics remain preserved on the server: `check-01.log` records
a nested-absolute-value parser issue, a missing explicit measurability
proof, and a redundant tactic warning; `check-02.log` passed but reported
two unused positive-h parameter names. These names were prefixed with an
underscore, retaining both h>0 premises, before the final zero-diagnostic
source was frozen. No frozen source was subsequently modified.

## Reproduction commands

Execute on the designated server, sequentially:

```sh
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/KernelRecurrence.lean
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/KernelRecurrence.olean Shao/OQ4/KernelRecurrence.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-kernel-recurrence/KernelAudit.lean
sha256sum Shao/OQ4/KernelRecurrence.lean .lake/build/lib/lean/Shao/OQ4/KernelRecurrence.olean
```

The exact audit helper is also preserved locally as `KernelAudit.lean`.
`kernel-summary.json` is a curated hash/count/name/correction summary. The complete
declaration ledger is `kernel-declarations.md`; the anonymous full
mathematical derivation is `kernel-proof.md`. Existing DelayedRecurrence
source and its original proof, receipt, and ledger were not modified.

## Verified scope

All five frozen items are implemented. The actual F/G positivity bounds
use closed-interval row support; the defect identity uses the true
semigroup and integrable subtraction. D0 and D1 retain their R3/R4 block
inputs explicitly. Natural subtraction uses m≤k, including m=0 and k=m.
D2/D3 retain precisely ερ^−(m+1), Aρ^−m, and Bρ^−m. D4 includes n=0 and
m=0 and supplies only the finite reciprocal-power bound. No global
nonnegativity of the cosine or increment-moment assumptions are added.

R3/R4/O0, moment-class positivity and uniform control of ρ, iid path
equivalence, B1 initial constants, long-time limits, and 4/π remain OPEN.
The root problems K, Kv, and OQ4 remain OPEN.
