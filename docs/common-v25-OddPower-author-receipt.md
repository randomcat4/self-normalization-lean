# OddPower author implementation receipt

Status: implementation and server gates PASS; independent proof review PENDING.
This is an author receipt, not a self-issued CORRECT review. Complete C1/C2 remain OPEN.

## Frozen identity and delivery

- Scope: `OddPower-next-scope.md`, SHA256
  `005abcc7752ff48345617c7e946dc616494907ad57637017abff82b6ef989c3d`.
- Existing independent declaration review: `OddPower-declaration-review.md`, CORRECT.
- Local implementation: `drafts/c12/OddPower.lean`.
- Remote module:
  `/root/rivermind-data/shao-lean-20261021/workspaces/takeover-odd-power/Shao/Probability/QuadraticCharacteristicOddPower.lean`.
- Source SHA256 (local and remote agree):
  `d526459c86cab6fdd8d4fc207e4950e03993bac0a26e7c2c6a7567f747b1b838`.
- Feature branch: `feat/takeover-odd-power`; source commit
  `758409913957f711fcfa9934301a2bfeb405625e`.
- Base: origin/main `c7f54caf9d43d6ee149c9d11aa0cb88d552d0b1b` (v18).
- One committed file, 603 lines; worktree clean after commit. No root import,
  manifest, shared implementation, old worktree or frozen-scope edit. No merge or push.
- Server recorded completion: `2026-10-21T16:23:59Z`.

The earlier `lead-c12` was inspected read-only. It contained no OddPower candidate
or matching log. Its untracked continuation sources were left untouched. The new
worktree uses the shared package directory through a symlink. It reads accepted
project build outputs from integration-p35-v18 through individual file symlinks
in its own build tree. Only the new target's own output was compiled/written.

## Actual three public statements

`OddPower-source-check.py` compares every public signature to the three frozen
Lean blocks, after whitespace normalization only. PASS: exactly zero source
definitions, exactly the following three public theorems, and unchanged signatures:

1. `quadraticChar_single_derivative_bounds`.
2. `quadraticChar_odd_power_residual_bounds`.
3. `quadraticChar_odd_power_lowFrequency_normalized`.

The source scan finds none of `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`.
There are 12 private source lemmas. No hypotheses were added or removed; no
centering, fourth moment, nonzero characteristic value, or odd exponent assumption
was introduced. The positive actual third moment is derived from positive variance.

## Proof structure supplied for independent review

The singleton iid specialization of the accepted power derivative theorems gives
actual first and second differentiability for the original integral. The weighted
integrand is genuinely integrable by its modulus `|a|`. Subtracting the actual
`iμ` inside the integral and using the global real exponential phase bound gives
the first derivative payment. The accepted power bound at length one gives the
raw second-moment payment; its `V+μ²` cancels to `m2` without a new assumption.

The private finite geometric identity bounds `x^k-y^k` for every natural `k`.
Actual power differentiation is then polynomial:

    (f^k)' = k f^(k−1) f',
    (f^k)'' = k f^(k−1) f'' + k(k−1) f^(k−2) (f')².

Differences of the first row are factored into `δ' f^(k−1)` and
`g'(f^(k−1)-g^(k−1))`. Differences of the second row use `δ''`, the same
power difference, and `(f'−g')(f'+g')`; its norm gives the exact factor two.
The remaining power difference at length `k−2` gives `k(k−1)(k−2)`.
Thus the frozen geometric-sum derivative counts are paid through algebraically
equivalent polynomial formulas, without differentiating any frequency bound.

All natural subtractions precede casts, also in private formulas. At lengths
0/1/2 the missing terms vanish through the actual natural coefficients; at
length 3 the final residual factor is `q^0`. These formulas and their HasDerivAt
proofs are uniform, so no illicit negative exponent or zero-value division occurs.

For `g(r)=χ(−r,v)`, the proof explicitly obtains `g'(r)=−f'(−r)` and
`g''(r)=f''(−r)`. Existing true-law odd bounds supply `a0,a1,a2`, retaining
the actual mean in `a0,a1`. Damping bounds the two actual characteristic values.

The normalized payment derives `V≤m2`, `m3>0`, `m3|v|≤m2|u|/128`,
`L≤|μ|+2m2|u|`, `N|μ|≤2sqrt(T)` and `NL≤2R` from the frozen inputs.
For each removed count `j=1,2,3`, length at least 6 gives `2(ℓ−j)≥ℓ`;
`m2≤4V` then pays `q^(ℓ−j)≤E`. The final estimates are

    E·2A,
    E·(2B+4RA),
    E·(2N m3|u|+8RB+2TA+8R²A).

The bound `R²≤2T(1+Tu²)` pays the frozen constants 2, 4 and 18.

## Actual server checks

Pinned Lean: `4.36.0-rc1`, commit
`c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`.
Lake: `5.0.0-src+c9afcdd`.
Mathlib checkout: `807d3836b165983210ee2ecf3cd28f239436949c`.
All Lean invocations ran on the designated server, sequentially, with CPU affinity
0–3. No local Lean, dependency rebuild, cache download or `lake update` was run.

Final target command after activation and entering the new worktree:

```sh
lake env bash -c 'export LEAN_PATH=/root/rivermind-data/shao-lean-20261021/workspaces/integration-p35-v18/.lake/build/lib/lean:$LEAN_PATH; taskset -c 0-3 lean -o .lake/build/lib/lean/Shao/Probability/QuadraticCharacteristicOddPower.olean Shao/Probability/QuadraticCharacteristicOddPower.lean'
```

`check-007.log`: Lean exit 0, empty stdout/stderr. Log SHA256:
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
New own olean SHA256:
`28fed60b3306d4c4b9d673cfda1ebc04e2dfc7191a50d1e1d7dc9c26eb7d86f9`.

The subsequent import audit uses the new worktree's build path first, where all
accepted dependency outputs are read-only symlinks. The audit imports the actual
new target and enumerates constants by `env.getModuleIdxFor?`, not namespace spelling.
For every imported project constant it runs transitive `Lean.collectAxioms` and
rejects everything outside `propext`, `Classical.choice`, `Quot.sound`.

`audit-002.log`: Lean exit 0; 20 module-owned constants, all 20 theorem constants,
including 3 public, 12 private source lemmas and 5 generated proof declarations.
The complete imported Shao dependency graph has 221 audited constants. All pass.
Separate `#print axioms` for the three public theorems returns the same whitelist.
Audit source: `OddPower-audit.lean`; server copy and log are under
`/root/rivermind-data/shao-lean-20261021/logs/takeover-odd-power/`.
Audit source SHA256: `6eab122b1dfb48df77ef0fe069585b652a1733f76d00945d46bcd2bc8b4dc6d4`.
Audit log SHA256: `0c648e9ea895cc90b5c2868c7a118d3b3187108fac9fb92d116651e27296c59d`.

Frozen accepted source hashes remain exactly:

```text
QuadraticCharacteristic.lean       8fd7815191dbd1ba9180159effe8c353d8b82d998d4d0d50bb6f957355b628f5
QuadraticCharacteristicPower.lean  5a51275c796d3bd0cc59b496a15b21e1c6bd5afd101b72f66a4c5e83511164c8
LowFrequencyDamping.lean           ffdeace2421a3c0fdf63def48eb96b882f9dc98014e5614d226a07f87a02bb65
lean-toolchain                    d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4
lake-manifest.json                40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e
```

## Failure ledger and remaining gate

All full logs stay on the server. `check-001` and `check-002` exposed integral/cast
and function-congruence API details; `check-003` exposed a numeral norm and function
notation rewrite; `check-004` passed the first two frozen theorems. `check-005`
found the strip-product cancellation and an overbroad arithmetic tactic timeout;
`check-006` found an addition-order type mismatch. These were repaired without a
signature or premise change. Final `check-007` passed all three.

`audit-001` failed only because putting integration's build root first shadowed
the new module path. No Lean proof failed there. The corrected per-file read-only
reuse and own build path gave the successful `audit-002`; target proof was unchanged.

Independent source-to-statement and proof review by a separate context remains the
acceptance gate. This unit has not been merged or added to root imports, and it
does not close noise derivatives, smoothing, inversion, source moment discharge,
or the complete C1/C2 roots.
