# TruncatedEnergy N0 author verification receipt

Author implementation and all required mechanical checks passed. The lead reported independent declaration and anonymous mathematical review CORRECT. Final independent source-to-statement and full formal review is pending; this receipt is not a self-signed independent review.

## Frozen artifacts

- Interface: `drafts/oq4/frozen-truncated-energy-v1.md`.
- Read-only original: `C:/game/shao/current/oq4/energy01.md`, verified SHA256 `2e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6`.
- Anonymous mathematical proof N0-v1: `proof.md`, frozen SHA256 `afe5f5c496158d7903548d3d49a01a6bcca5799c3c541fe3937e5f3a68bd7dce`; it has not been edited after submission.
- Server source: `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/TruncatedEnergy.lean`.
- Final source SHA256: `bd8015535312de5812ccca340e5bb6e7dd2d1c55a8da1e627f6aa228500495c0` (21487 bytes).
- Author-only unique emitted olean SHA256: `1710e3f38dbd61c0cdd229b09ddcd72d02270343f5a61007a4d27cd262f1ba43`.
- Local final source: `drafts/oq4/energy/TruncatedEnergy.lean`.
- Source and curated files are UTF-8 without BOM, LF only, exactly one final LF. Source bd801 and proof afe5 are frozen.

## Exact coverage

1. Actual energyWeight is Borel measurable and nonnegative for arbitrary real h,s. For T≥0, h>0, |s|≤T it is pointwise at most exp(4T), hence genuinely integrable under every finite measure. These auxiliary statements include the frozen admissible domain h≥1.
2. For h>0 and genuinely integrable |x|³, energy_third_moment_payments returns all three genuine truncated-moment integrabilities and the four exact payments: strict tail mass β/(8h³), tail absolute first integral β/(4h²), tail square integral β/(2h), and closed-cutoff fourth integral 2hβ. β is the actual integral, never a free surrogate.
3. Under probability, unit second moment, and h≥1, energy_cutoff_mass_lower proves actual closed-cutoff mass≥3/4. energyNormalizer_bounds then proves (3/4)exp(-4T)≤Z≤exp(4T), using genuine integrability and no β-smallness or assumed positivity of Z.
4. energy_exp_remainder_bound proves the precise factor exp(4T)/2 for every |u|≤4T. Its formal proof uses the second derivative bound through derivative monotonicity on both sides of zero, an equivalent elementary proof of the anonymous Taylor estimate. The actual truncated remainder is Borel and genuinely integrable, and its integral is bounded by exp(4T)T²β/h³. energyNormalizer_expansion proves the actual first-order formula with C_Z(T)=1/8+T/2+exp(4T)T² exactly.
5. energyWeight_at_zero retains the zero atom; energyNormalizer_at_zero states Z(h,0)=ν.real{|x|≤2h} for arbitrary h. No assertion that this mass is one is made. Closed endpoints ±2h and the strict complement retain every boundary atom.

There is no centering or id-integrability premise in the module, nor a new β≥1 premise, global fourth/exponential moment, bounded support, density, nonlattice or symmetry hypothesis. Constants depend only on T. Only the finite even-weight normalization N0 is supplied. No normalized tilted law, normalized moments, tilted mean, log Z, E2/E3/E4, BE/SP, K/Kv, energy denominator or complete root theorem is claimed.

## Server execution and exact checks

All Lean work ran only on the designated server, after activation and then changing to the assigned OQ4 worktree. Every invocation used one process with `taskset -c 0-3`. Only the new module's olean was emitted, exactly once. Old mathematical targets and oleans were not rebuilt. No Git, common/root/manifest/lock/shared-cache edits or package downloads occurred.

Parent-confirmed branch `feat/oq4-energy-tilt`, HEAD `9fd37d07bbda4830edf3bf7eba544c7de4dc04e8`, after merging the accepted PR42 final head. Parent reported the 23 old OQ4 and four common direct sources had identical SHAs before/after. The author did no Git operation.

Toolchain `leanprover/lean4:v4.36.0-rc1`; mathlib revision `807d3836b165983210ee2ecf3cd28f239436949c`.

| Check | Exit | Full server record |
|---|---:|---|
| Full new source body with all 23 prior OQ4 imports | 0 | `repro_outputs/oq4-energy/coexist05.log`, `.exit` |
| Canonical final source with explicit minimal dependencies | 0 | `repro_outputs/oq4-energy/target02.log`, `.exit` |
| Author-only unique olean emission | 0 | `repro_outputs/oq4-energy/olean.log`, `.exit` |
| Actual 24-module import and owner-module all-new-constant audit | 0 | `repro_outputs/oq4-energy/audit.log`, `.exit` |

Successful source-coexistence, target and emission logs are 0 bytes, with no compilation diagnostics. The final import audit imports every old module and the actual new emitted module. `CoexistSource.lean` has the exact frozen source body; canonical target adds the explicit Deriv.Pow dependency needed for standalone derivative simplification.

The full dynamic audit uses exact owner module index, not a root-name or namespace filter. It found **50 actual new constants =22 explicit (4 definitions+18 theorems)+28 generated**. All actual transitive axiom records are whitelist subsets: 28 have {propext, Classical.choice, Quot.sound}, 22 have only {propext}. No unexpected axioms; banned source-token scan empty. Every name and axiom set is retained in curated declarations.md and summary.json.

Initial failed API attempts are preserved as curated source snapshots under history/ and full server-only logs coexist01, coexist02, coexist04 and target01. Core-only coexist03 passed. Fixes addressed an explicit squared cutoff inequality, indicator/function elaboration, measurability of piecewise functions, the actual integral_div name, pointwise function-operator simplification in integral identities, triangle-inequality names, and explicit standalone Deriv.Pow import. No mathematical premise, numerical constant, or target conclusion was changed. No additional package cache was needed or written.

Raw compile/audit logs and binaries remain only on the server. Local files are curated source, anonymous proof, declaration ledger, summary, receipt, checkpoint, reproducibility helper source, and failed source snapshots.

## Reproduction

```sh
set -e
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean repro_outputs/oq4-energy/CoexistSource.lean
taskset -c 0-3 lake env lean Shao/OQ4/TruncatedEnergy.lean
# Author emission already performed exactly once. Reviewers use no-o source/import checks.
# taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/TruncatedEnergy.olean Shao/OQ4/TruncatedEnergy.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-energy/Audit.lean
python3 repro_outputs/oq4-energy/summarize.py
```

The local check.ps1 transfers only the owned new source and coexistence helper for an explicitly named check. Audit.lean imports all24 and enumerates all module-owned names. summarize.py validates exact counts, transitive axioms, encoding, banned tokens, exits and hashes; it writes a curated summary, not copied raw logs.
