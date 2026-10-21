# Shared FiniteIIDMoments author execution and relocation receipt

Status: IMPLEMENTED; SERVER TARGETS, COMPATIBILITY AND TRANSITIVE AXIOM
GATES PASSED. Pending fresh independent implementation/diff review and
coordinator integration. This is not an author-issued independent verdict.

## Frozen binding and exact files

Frozen scope SHA256:
`3033eb9df9d7586a8b94912ff6ceef6a597275174309af7262b53ac1c080a8db`.
Its bytes remain unchanged. Independent declaration report:
`FiniteIIDMoments-shared-declaration-review.md`, CORRECT.

The coordinator provided the dedicated server worktree
`/root/rivermind-data/shao-lean-20261021/workspaces/shared-iid-moments`,
branch `feat/shared-iid-moments`, base
`413e668847a150d430328b00cb45ffb070ce1d76` (coordinator reports the same
tree as merged main `f61b7757daf1ed6b66de02e396c6feaec7aab927`).
The initial worktree was clean and the old source matched its frozen hash
before either owned file was written.

| Owned server file | Local readback mirror under drafts/c12 | Frozen SHA256 |
|---|---|---|
| `Shao/Probability/FiniteIIDMoments.lean` | `FiniteIIDMoments.lean` | `d2417f73424ea90a13edb10bdad267d638d66fec432c3107362a2d0246fe2bfa` |
| `Shao/OQ5/P35/FiniteIIDMoments.lean` | `FiniteIIDMoments-OQ5-compat.lean` | `8efe17261c763f6f56263c6db26f759a342500c26f8305a50e356ef686fa0027` |

Both local readback hashes equal their server hashes. The shared module is
540 lines; the compatibility entry point is 104 lines. No root import,
pin, package/cache, other implementation or scope was edited. No commit,
stage, reset or push was performed. The `lead-oq56` worktree was only read;
its old module still has frozen SHA256
`4b2c65ec7fb03767b6a469ef5918592c9a76e993ad95262e6a7aae6840c4520b`
after all gates.

## Exact relocation/difference evidence

The new `Shao.Probability` module contains the frozen 3 definitions and
6 public moment theorems, plus the original 2 private definitions and
17 private theorems. The original proof block was transferred, including
the two unused private measurability helpers and every small-length
branch. A server byte comparison reconstructed the new body from the
frozen original and asserted exact equality after only:

1. Replacing the namespace and its closing name.
2. Expanding `unorderedPairSum` to its exact double sum in the shared
   `finitePairProductSum` definition.
3. Replacing the one `hcnt` proof term `pairCount_eq_choose m` with
   `(Nat.cast_choose_two ℝ m).symm`.

The seven shared imports are exactly the frozen Mathlib-only list. There
is no direct Shao import and hence no project dependency leading to OQ5.
The shared module was compiled standalone before the compatibility
entry point, so its proof does not inherit OQ5 declarations from a combined
audit environment.

In the old namespace, the original three definition bodies are retained
byte for byte. All six original theorem signature strings, from their
`omit` line through the type, match both the original and new shared
source exactly. Each old theorem proof consists solely of applying its
fully qualified shared same-basename theorem to the original arguments.
No iid proof remains in the compatibility file. Its tracked diff is
13 insertions and 448 deletions; the new shared file is not included in
that tracked-file stat until the coordinator stages it.

The server assertions returned:

```text
ALL_SHARED_PROOF_BYTES_PRESERVED_EXCEPT_TWO_FROZEN_NEUTRAL_REPLACEMENTS
ALL_SIX_ORIGINAL_SIGNATURE_STRINGS_IDENTICAL
ALL_THREE_ORIGINAL_DEFINITION_BODIES_IDENTICAL
SHARED_PROJECT_IMPORT_CLOSURE_EMPTY
FORBIDDEN_SCAN_CLEAN_BOTH_SOURCES
INDEX_EMPTY
```

Here “two neutral replacements” refers to the pair definition body and
the choose-two proof term; the namespace/import packaging edits are
accounted for separately. A final `git diff --check` exited zero.

## Actual targeted server checks

Every Lean invocation ran on the designated server after sourcing
`activate.sh` and selecting the new worktree. No local Lean was used.
Versions were rechecked after all gates:

```text
Lean 4.36.0-rc1, c9afcddf514a6772bd4d649f7cfc04eff0b9f15e
Mathlib 807d3836b165983210ee2ecf3cd28f239436949c
```

The common form of every target command was

```sh
source /root/rivermind-data/shao-lean-20261021/activate.sh &&
cd /root/rivermind-data/shao-lean-20261021/workspaces/shared-iid-moments &&
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/<module>.olean <module>.lean
```

Both owned targets passed with actual remote `exit_code=0`, empty stdout
and stderr. The public source and its produced `.olean` were reported to
the coordinator immediately after the first successful standalone check
for use by the parallel FourierPower author.

The existing direct importers and the two missing accepted dependencies
were then compiled in the following order against the rebuilt compatibility
entry point. Every result was exit zero with empty stdout/stderr:

| Target under Shao/OQ5/P35 | Actual seconds |
|---|---:|
| `ConditionalStatistics.lean` | 4.02 |
| `ConditionalBackground.lean` | 4.53 |
| `ConditionalMixture.lean` | 4.85 |
| `ConditionalStudentizer.lean` | 29.93 |
| `ConditionalNumerator.lean` | 29.28 |

These were actual target checks generating fresh local-worktree artifacts,
not imports relying solely on the previous accepted consumer artifacts.

### Signature, definitional identity and caller bridge checks

A separate server `lake env lean --stdin` imported the old compatibility
entry point and common `FiniteIID`. It exited zero with empty stderr.
It compiled:

- Three universally quantified pointwise `rfl` equalities between the old
  and new definitions, for every natural length, type, function family
  and observation.
- Six `rfl` equalities between the fully applied declaration constants
  `@Shao.OQ5.P35.finite_iid_...` and `@Shao.Probability.finite_iid_...`.
  This verifies their types are definitionally equal, including binder
  order, parameters and probability/moment assumptions.
- The frozen caller-side equality between shared `finiteFeatureSum Z ω`
  and `prefixSum (samplePath Z ω) m`, using only the three named existing
  definitions/length lemma in the proposed `simp only` proof.
- `#check @...` for all 9 old and all 9 new public objects.

No positive-length, mean-zero, positive-variance or additional moment
assumption was introduced. The original Nat-subtraction boundaries and
actual raw/centered distinctions remain in the moved proof bytes.

### Full transitive axiom and source gates

A fresh server stdin audit imported the produced compatibility module and
used `Lean.collectAxioms` on all environment constants matching the shared
public prefix, shared module-private prefix, old public prefix and old
module-private prefix. It threw an error for any axiom other than
`propext`, `Classical.choice`, `Quot.sound`. The successful audit exited
zero with empty stderr and reported:

```text
GROUP SHARED COUNT 13
GROUP SHARED_PRIVATE COUNT 23
GROUP COMPAT COUNT 9
GROUP COMPAT_PRIVATE COUNT 0
AUDITED_DECLARATIONS 45
```

This includes all new definitions, helpers, generated equation/proof/simp
declarations and all old wrappers. All 45 passed. An initial audit driver
used the reserved Lean keyword `prefix` as a local variable; that driver
parse error was corrected to `pref` and the entire audit was rerun
successfully. No source change was needed.

Both final source files passed a whole-source token scan for
`sorry`, `admit`, `axiom`, `unsafe`, `native_decide` with zero occurrences.
Final source hashes, whitespace check and unchanged original/consumer
hashes were rechecked after the Lean gates.

## Read-only accepted consumers: verification copies only

A recursive project-import inspection found 30 project modules in the
three consumers' old closure. Every already-present unmodified dependency
was byte-equal to its accepted source in `lead-oq56`, except the owned
compatibility entry point as intended. Exactly four sources were absent
from the new worktree. Under the coordinator's explicit authorization,
their accepted bytes were copied after checking the hashes below:

| Source under Shao/OQ5/P35 | Accepted/unchanged SHA256 |
|---|---|
| `ConditionalStatistics.lean` (already tracked) | `30961217d94582b790c8ad8c75b0a776fac253c973066bb3553d77c14821863a` |
| `ConditionalBackground.lean` (verification-only copy) | `bd8fbc670d0c29179994482f93aad25e48587ed423c34884f2f6f60adb7481dc` |
| `ConditionalMixture.lean` (verification-only copy) | `3be0b68edb5435fb6c1136a0d6ab134e23f28dea4494d0d4d35bf93b2bd3a5be` |
| `ConditionalStudentizer.lean` (verification-only copy) | `85766d90d01cb9e50e342183a6168a356b5ddd2cea84887c5d7439c7abb8eb62` |
| `ConditionalNumerator.lean` (verification-only copy) | `a47d906cd619e57594a9eed98a3204c8218a4a8c82f8e1b9eb4ba6725ae08c13` |

The four copied hashes are bound by the accepted OQ56 unit23–26 reports
and `drafts/oq56/pr05/oq5-p35-counterexample-review.md`. Their hashes and
equality to the read-only source worktree were checked again after all
compiles. No consumer proof was edited.

Final Git status has only the owned tracked compatibility edit, the owned
new untracked shared module, and these four untracked verification-only
files. The index is empty. The four verification-only files MUST NOT be
staged or included in this migration change. Root owns the final two-file
staging/commit, root-import decision and joint integration gate.

This author keeps both implementation source hashes frozen for independent
relocation/diff review. The migration itself establishes no new Fourier
derivative, Gaussian comparison or full C1/C2/OQ56 root result.
