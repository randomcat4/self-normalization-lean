# ReflectedSurvival author verification receipt

Status: author implementation and all required author-side mechanical checks passed. Independent source-to-statement and proof review remains pending; this receipt is not an independent review.

## Frozen interface and artifact

- Interface: `drafts/oq4/frozen-reflected-survival-v1.md` (statement translation previously CORRECT, supplied by the lead).
- Server source: `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/ReflectedSurvival.lean`.
- Final source SHA256: `b54b2300ef77375782e60a541bcffd6bed05ac4de61a776c6e0fd5e189568809` (12725 bytes).
- Author-only emitted olean SHA256: `3739499874a4c83599cca84c991fb24d742b2d2cd9532c9900dde07e320d8128`.
- Local final source: `drafts/oq4/reflected/ReflectedSurvival.lean`; anonymous derivation: `proof.md`.
- UTF-8 without BOM, LF only, exactly one final LF. The source is frozen after the successful checks below.

## Mathematical scope

The module proves the genuine finite product reflection law for every natural dimension, exact closed upper/lower event reflection, actual Gaussian CDF reflection, the strict-CDF left-cutoff limit with atoms, and reflected BE from the sole original-law BE premise. It then calls the accepted actual finite-survival theorem twice with two separately explicit original SP inputs, and derives the actual closed unit-interval concentration predicate directly from the arbitrary-law closed-CDF theorem and the explicit parameter β ≥ 1. It does not call the moment-based high-level concentration theorem.

Final existing predicate argument order is `iidOneSidedSurvival ν β Cs` and `iidIntervalConcentration ν β Cq`, matching their actual accepted definitions. Cs = √2 exp(6+3 C_BE); Cq = 1+2 C_BE; both are proved nonnegative. The final joint theorem has the entire ν-CDF premise and both original SP identities explicitly in its signature. There are no added moments, atomlessness, support, density, symmetry, or conditional-independence assumptions. Zero-dimensional product and reflection facts, zero prefix, closed endpoints, atoms, and d=0 remain intact.

BE and each original SP are explicit inputs. Unconditional S/AC/O0, B1, long-time K/Kv, the energy denominator, and the complete OQ4 roots remain OPEN.

## Execution and checks

Every Lean invocation ran only on the designated server, after activation and then changing to the OQ4 worktree. Each invocation used one process with affinity `taskset -c 0-3`. No local Lean, Git operation, shared cache/lock/root/common-source edit, package download, or extra module olean emission occurred.

Toolchain: `leanprover/lean4:v4.36.0-rc1`.
Mathlib revision: `807d3836b165983210ee2ecf3cd28f239436949c`.
Parent-reported accepted-baseline merge: `f73e3ca6534783c94dc6855fe4277a83b145dcf0` on `feat/oq4-one-sided`; this author did not perform Git operations.

| Check | Exit | Full server record |
|---|---:|---|
| New source body after imports of all 21 prior OQ4 modules | 0 | `repro_outputs/oq4-reflected/coexist03.log`, `.exit` |
| Canonical source target | 0 | `repro_outputs/oq4-reflected/target01.log`, `.exit` |
| Author-only olean emission | 0 | `repro_outputs/oq4-reflected/olean.log`, `.exit` |
| Actual 22-module imports and all-new-constant transitive axiom audit | 0 | `repro_outputs/oq4-reflected/audit.log`, `.exit` |

The coexistence, canonical target, and olean logs are empty (0 bytes); there are no final compilation diagnostics. Initial development failures are retained separately as coexist01/coexist02 logs on the server. They concerned pointwise-negation elaboration, explicit measurable-set typing, an iff proof, and a local measure abbreviation. The frozen mathematical hypotheses and conclusions were not changed.

The dynamic audit selects constants solely by `env.getModuleIdxFor?` and owner module name `Shao.OQ4.ReflectedSurvival`, without any namespace/root-name prefix filter. It found **29 constants = 17 explicit (1 definition, 1 instance, 15 theorems) + 12 generated**. This includes `Shao.OQ4.lowerBlockSurvival.eq_1`, generated under an imported definition's name. All 29 received actual transitive `#print axioms` records: 21 depend on {propext, Classical.choice, Quot.sound}, 7 on {propext}, and 1 on {propext, Quot.sound}. No unexpected axioms occurred. The source banned-token scan is empty. Full per-declaration results are in `declarations.md` and curated `summary.json`.

Full raw logs and binary artifacts remain only on the server. Local files contain only curated source, proof, declarations, receipt, summary, checkpoint, and reproducibility helpers.

## Reproduction

Run on the server from the assigned worktree; the exact audit and coexistence sources are in both this local directory and the server record directory.

```sh
set -e
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean repro_outputs/oq4-reflected/CoexistSource.lean
taskset -c 0-3 lake env lean Shao/OQ4/ReflectedSurvival.lean
# Author emission already performed exactly once; reviewers use import/no-o checks.
# taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/ReflectedSurvival.olean Shao/OQ4/ReflectedSurvival.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-reflected/Audit.lean
python3 repro_outputs/oq4-reflected/summarize.py
```

The local `check.ps1` transfers only this owned source and its coexistence helper, then requests the named server target. `Audit.lean` imports all 22 modules. `summarize.py` validates the actual audit records, final exits, encoding, banned tokens, and hashes, and writes only a curated summary.
