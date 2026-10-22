# QuadraticChordNoise author implementation receipt

Status: AUTHOR_GATES_PASS; independent source-to-statement/full proof review PENDING.
The source is frozen. This receipt does not issue a CORRECT verdict on its own proof.
Complete C1/C2 and the remaining Fourier comparison remain OPEN.

## Frozen identity

- Frozen scope: `FourierComparison-next-scope.md`, SHA256
  `912c3e001bcea85a64332c9efaf530ef55f3ddc0bf055841a762468a65a5ab44`.
- Independent declaration review: `FourierComparison-declaration-review.md`, CORRECT,
  SHA256 `4d65964334493503f776db43e4aa0d1daa1de8ff0e8d35fde6c2a6396109cdc1`.
- Local source: `drafts/c12/QuadraticChordNoise.lean`.
- Canonical new module: `Shao/Probability/QuadraticChordNoise.lean`.
- Local and server source SHA256:
  `75069c06d5794a5e530e99260e6e3308656623ea39944ac70f1d958ffd40d275`.
- Source bytes: 25849; lines: 544.
- New server worktree: `/root/rivermind-data/shao-lean-20261021/workspaces/takeover-chord-noise`.
- New branch: `author/quadratic-chord-noise`.
- Frozen source commit: `32fefb4c537f96071ff576db76f268e1bb9d3b4c`.
- Base: accepted main `22a5e1f97311ad40aa49efbcfab4f5fc67a65de3`.
  The frozen dependency versions are unchanged. This uses the root-authorized
  alternative of the original accepted dependency base; the later GitHub main
  was not yet a local object when the isolated worktree was created.
- Exactly one committed file; worktree clean after commit. No push or merge.
- Server evidence timestamp: `2026-10-21T17:05:02.599103+00:00`.

Shared package sources/outputs were accessed read-only. This worktree reads accepted
project outputs from `integration-source-clock-v28` through individual file symlinks
inside its own build directory. The new module's output is an ordinary new own file,
not a symlink. No shared source, root import, manifest, version lock, old worktree,
cache or other lane was edited. No missing-cache request was necessary.

## Exact source contract

The source checker compares all four public theorem signatures and all four complete
definition bodies against the frozen Lean blocks after whitespace normalization only.
It passes with exactly the following public definitions:

1. `quadraticTriangleLaw`.
2. `quadraticBiasedPairLaw`.
3. `quadraticChordLaw`.
4. `quadraticChordChar`.

The exact public theorems are:

1. `quadraticTriangle_probability_char`.
2. `quadraticChord_law_data`.
3. `quadraticChordChar_exact`.
4. `quadraticChordChar_cone_gap`.

There are 22 private source lemmas and no additional source definitions. The scan
finds no `sorry`, `admit`, `axiom`, `unsafe` or `native_decide`. The original fixed law,
actual variance, raw third moment, positive cutoff and almost-everywhere support
are retained. No mean-zero, symmetry, density, nonatomicity, fourth moment,
nonzero characteristic value or positive gap premise was added.

Source check artifacts:

```text
QuadraticChordNoise-source-check.py
  b775089c89b095b03a9293af350826d07ce881b6f392edc5fea9b1d34b9ae002
QuadraticChordNoise-source-check.json
  a739fc47660ee0bb3413734f25516a6c933865b0d20262a8a0e61b6b19a9f9b3
```

The checker is lightweight source-text processing; it does not invoke local Lean.

## Proof supplied for independent review

The triangle density is rewritten as an actual indicator on [-1,1]. Its integral
is split at zero, giving the two affine weights `1+r` and `1-r`. At nonzero frequency
the proof differentiates the explicit affine exponential antiderivative and applies
the actual interval fundamental theorem. At zero frequency it uses the independently
computed density mass 1. This proves the characteristic formula for the defined
withDensity law, rather than constructing a free function with the desired formula.

The accepted pair-square theorem supplies both true integrability and the identity
`∫D²=2V`. Dividing by positive `2V` therefore normalizes the actual biased law. The
triangle product and polynomial chord map give actual probability measures. Support
is transported first to the true product, then through absolute continuity of
withDensity, then through the measurable pushforward. The common triangular variable
is retained in both chord coordinates. The inequality for the second coordinate
uses `A²-A'²=(A-A')(A+A')`; it preserves the requested `2h|Z|` form. Every required
phase integral is genuinely integrable because its norm is 1 on a probability law.

The exact characteristic proof first rewrites the actual pushforward integral and
uses Fubini on the normalized product. It then evaluates the genuine triangular
characteristic function at `Dθ`. Pointwise algebra handles `θ=0` and `D=0` separately,
without cancelling a zero factor. In particular, `θ=0` gives `D²/2`, not the default
zero quotient. The triangle formula and the probability norm bound give
`0≤kernel≤1`, hence `0≤Q≤D²/2`; this pays true Q integrability using only h3. The
withDensity integral becomes exactly `V⁻¹∫Q`. Its imaginary part is zero and the
same pair-square integral gives its upper bound 1. This part uses no support premise.

For the final theorem, actual AE support yields `|A+A'|≤2h`. The closed cone gives
`|v(A+A')|≤|u|/2`, hence `u²/4≤θ²≤9u²/4` and `θ≠0`. The cosine numerator is
nonnegative, so multiplication by these positive-denominator bounds gives the
pointwise constants 4/9 and 4. Integrating the true AE inequalities and applying
the accepted `quadraticChar_gap_identity` gives precisely the frozen characteristic
gap comparison after division by the actual positive variance. Neither D, χ, K
nor the characteristic gap is inverted.

The extra Mathlib import supplies elementary interval integrals. A local priority
declaration selects the standard complex-to-real normed space instance for the
derivative/integral coercions; it creates no new mathematical definition or axiom.
Review should inspect this instance selection alongside the actual declarations.

The mathematical provenance remains the original main.tex:650–707 construction and
supplement.tex:1988–2042 support discussion, with fixed source hashes already bound
by the scope. This is a formalization of those explicit dependencies, not a novelty
claim or a claim to complete C1/C2.

## Actual pinned server execution

All Lean invocations were on the designated server, sequential, CPU affinity 0–3.
No local Lean, dependency rebuild, full Mathlib build, cache download or lake update.

```text
Lean 4.36.0-rc1, commit c9afcddf514a6772bd4d649f7cfc04eff0b9f15e
Lake 5.0.0-src+c9afcdd
Mathlib 807d3836b165983210ee2ecf3cd28f239436949c
```

After activation and entering the isolated worktree, final target command:

```sh
lake env bash -c 'export LEAN_PATH=/root/rivermind-data/shao-lean-20261021/workspaces/takeover-chord-noise/.lake/build/lib/lean:$LEAN_PATH; taskset -c 0-3 lean -o .lake/build/lib/lean/Shao/Probability/QuadraticChordNoise.olean Shao/Probability/QuadraticChordNoise.lean'
```

`check013.log`: Lean exit 0, empty stdout/stderr. SHA256:
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
Own new olean SHA256:
`a11b4c8c4638f5692916b5bbe9b6c395480fd1144e898119160aab40c0458341`.

The audit imports the actual compiled module with this worktree first on LEAN_PATH.
It enumerates ownership using `env.getModuleIdxFor?`, including private, generated,
definition and cross-namespace constants. Every actual imported Shao constant is
also audited by transitive `Lean.collectAxioms`; only `propext`, `Classical.choice`,
`Quot.sound` are accepted. All four public theorems additionally have `#print axioms`.

`audit001.log`: Lean exit 0; 55 module-owned constants, comprising 4 source definitions
and 51 theorem constants. The latter include the 4 public theorems, 22 private source
lemmas and 25 generated theorem declarations. All 190 constants in the actual imported
Shao dependency graph pass the same transitive whitelist. No namespace-prefix-only
audit is being substituted for module ownership.

Full logs stay in `/root/rivermind-data/shao-lean-20261021/logs/takeover-chord-noise/`.
Hashes:

```text
audit.lean / local QuadraticChordNoise-audit.lean
  764d8d2bf0dd6572c2bdd63a70027d51ea329adc6fb0e50ae7b7abda68f7ac85
audit001.log
  2dbbe3d01e5b97942dac7e278bec0b59029089502cfb5c086c9e7bc65e7f8148
result.json / local QuadraticChordNoise-server-result.json
  a7d86a26ee646952b0e3913ceb7b4acb8019c5f5e92530508a6994bd96df8930
QuadraticCharacteristic.lean
  8fd7815191dbd1ba9180159effe8c353d8b82d998d4d0d50bb6f957355b628f5
LowFrequencyDamping.lean
  ffdeace2421a3c0fdf63def48eb96b882f9dc98014e5614d226a07f87a02bb65
lean-toolchain
  d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4
lake-manifest.json
  40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e
```

## Development failure ledger and remaining gate

The thirteen target iterations resolved concrete pinned-library details of interval
integral coercions, measurable-set elaboration, actual AE product/map transport,
polynomial support multiplication, and tactic cleanup. check009 passed the first
three complete public statements; check010 supplied the fourth with one remaining
norm-rewrite frontend error. check011/check012 exposed proof-script cleanup goals;
check013 passed the complete frozen module without diagnostics. No failed attempt
was repaired by changing a public signature or a source premise. Audit001 passed
on its first run. No cache miss or resource-limit exception occurred.

A fresh independent source-to-statement and full proof review is still required,
followed by the root-owned integration/import and whole-library ownership gate.
Only the root may integrate this frozen one-file source commit. No complete noise
Ξ, Ξ derivative, high-frequency optimized decay, smoothing, inversion, time summation,
strict CDF transfer or C1/C2 root result is supplied by this unit.
