# LindleySignedBlock author receipt

Status: the frozen one definition and four theorem signatures have been
implemented and pass the designated server check. Final independent proof
review is pending; this author does not certify their own implementation.

The original proposal is retained as `LindleyFourier-next-scope.md`.
Its frozen proposal SHA256 is
`99f2a8c006c56569cbc34514786c9f7ac972d8892cf5171a826f4b8b5a44773e`.
The independent statement review
`LindleySignedBlock-statement-review.md` returned CORRECT without revision,
and the coordinator then authorized implementation.

## Frozen source

Local: `C:/game/shao lean/drafts/c12/LindleySignedBlock.lean`, 428 lines.

Remote:
`/root/rivermind-data/shao-lean-20261021/workspaces/lead-c12/Shao/Probability/LindleySignedBlock.lean`.

Matching local/remote source SHA256:

```text
a9f959580b66cc8de684ebe93be0bce360db44e30f5a7ea93b4e85bc9730dd15
```

The source is frozen at that hash for the independent proof reviewer.
It exposes exactly one public definition and the four frozen public
theorems. Fourteen private helpers and generated proof declarations are
also covered by the axiom scan.

The consumed old source remains unchanged:

```text
Shao/Probability/LindleyTelescoping.lean
518b7029d435ddd3b32a414f8893d6c49e26910cff18117d8da0cc6eb67bc93c
```

## Actual server evidence

Pinned toolchain: Lean `4.36.0-rc1`;
mathlib `807d3836b165983210ee2ecf3cd28f239436949c`.

Final targeted command:

```text
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-c12
taskset -c 0-3 lake env lean \
  -o .lake/build/lib/lean/Shao/Probability/LindleySignedBlock.olean \
  Shao/Probability/LindleySignedBlock.lean
```

Result: exit code 0; stdout and stderr both empty. No old dependency was
rebuilt, no full project build was run, and no Lean process ran locally.

Subsequent server `lake env lean --stdin` checks imported the new module
and printed transitive axioms for all five public declarations. Each had
exactly `[propext, Classical.choice, Quot.sound]`. A following environment
scan used `Lean.collectAxioms` on the public-name prefixes and
`_private.Shao.Probability.LindleySignedBlock.`. It rejected any axiom
outside that whitelist and reported:

```text
AUDITED_DECLARATIONS 24
```

That final scan exited 0 with empty stderr. It covers five public
declarations, fourteen private helpers, and five generated declarations.
The audit was supplied on standard input; no shared audit script changed.
The source token scan for `sorry`, `admit`, `axiom`, `unsafe`, and
`native_decide` found no matches.

Separate explicit-type output confirmed, in particular:

```text
@MeasurableSet Ω (Shao.Probability.lindleyHistory X k hk) E
```

The usual pretty-printer hides the measurable-space argument and displays
only `MeasurableSet E`; the explicit check confirms this is the frozen
history condition, not ordinary ambient measurability. The actual iid,
probability, bounded-test and time-index inputs are unchanged.

## Proof entry points and scope

* Lines 19–32 define the exact prefix sigma algebra and identify it with
  the supremum of the individual original-coordinate comaps. The definition
  has the standard `@[instance_reducible]` attribute for its class type;
  this adds no hypothesis or mathematical content.
* Lines 196–304 prove the weighted iid step. The history condition first
  supplies an exact Borel-prefix inverse image for every eligible `E`.
  The actual iid sample is transferred to its canonical product law.
  Separating the current coordinate leaves the event indicator unchanged
  because `k≤i.val`; the genuine previous Lindley state and partial square
  sum are likewise unchanged. Product Fubini and the existing actual
  kernel semigroup prove the integral equality. Neither restricted-law
  independence nor a weighted expectation identity is an input assumption.
* All weighted product integrands are proved measurable and genuinely
  integrable by the unit bound before Fubini. The finite restriction in
  later set integrals is used only for integrability and integral algebra,
  never as an iid probability law.
* Lines 308–394 prove the signed block identity. Genuine integrability
  precedes `integral_sub` and `integral_finsetSum`. A finite tail cancellation
  lemma evaluates states only at bounded times in `Fin (n+1)` and includes
  empty/full blocks. The reflection defect is the unchanged public defect
  with its actual partial square sum.
* Lines 398–424 apply the history-localized identity. The terminal test and
  initial future-kernel values each lie in `[0,1]`, so their difference has
  norm at most one. The actual set-integral norm bound pays precisely
  `(μ E).toReal`. The absolute value is outside the signed block integral.

The result covers `n=k=0`, `k=n`, `k=0`, noncentered and deterministic
increment laws, zero-energy paths and all permitted history events. No
moment, positive-variance, smoothness or Gaussian hypothesis was added.
The source's literal strict CDF test remains admissible without changing
its `q>0` restriction or strict threshold; no new CDF convention is defined.

The unit is the finite signed-block payment from
`supplement.tex:824–830` and `3050–3075`. It does not bound the bad clock
probability, construct the actual smoothing noise, prove characteristic
function or derivative estimates, prove a smoothing error for strict CDFs,
or establish the quantitative Fourier comparison or either root group.

Only the owned new Lean draft, matching new server source, existing
proposal status and this receipt were written. No frozen dependency,
root import, branch synchronization, shared cache, lock or other author's
file was changed.
