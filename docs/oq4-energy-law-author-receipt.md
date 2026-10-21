# EnergyTiltedLaw N1 author verification receipt

All required author-side implementation and mechanical checks passed. The lead reported independent statement and anonymous mathematical review CORRECT; final independent source/formal review is pending. This receipt is not an independent review.

## Frozen artifact and dependency

- Frozen interface: `drafts/oq4/frozen-energy-tilted-law-v1.md`.
- Anonymous proof N1-v1: `proof.md`, frozen SHA256 `3788a0145dddbbc47bb9bddcea5151eab5e11a574a84d2c2066c54fb8667c507`.
- Actual N0 dependency: TruncatedEnergy source `bd8015535312de5812ccca340e5bb6e7dd2d1c55a8da1e627f6aa228500495c0`, independently CORRECT/FULLY_CHECKED as reported by the lead; neither source nor olean was changed or rebuilt.
- Server source: `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/EnergyTiltedLaw.lean`.
- Final source SHA256: `ea13bcf07671ee77a90910807f09f6c1c1deb95e1834f0715bcc042ab5ecbddd` (24984 bytes).
- Author-only unique emitted olean SHA256: `6b4d4445a2d8872a38654e60f2c13f0b3ee49515a6ac31ff8cff87fe6b8d7cde`.
- Local final source: `drafts/oq4/energy-law/EnergyTiltedLaw.lean`.
- UTF-8 without BOM, LF only, one final LF. Final source and proof are frozen.

## Exact mathematical coverage

The definition energyTiltedLaw ν h s is the actual withDensity measure with nonnegative ENNReal.ofReal(w/Z) density; it has no T parameter. N0 genuinely supplies w-integrability and positive finite Z; these are proved consequences, not premises of the exported interface. The module proves IsProbabilityMeasure under the frozen admissible hypotheses, the exact real mass formula for every Borel A, and almost-everywhere closed support. The support statement actually holds for every h,s and original measure, including degenerate totalized density cases.

For every Borel real f whose actual product f*w is genuinely ν-integrable, energyTiltedLaw_integral proves genuine integrability under the constructed law and the exact quotient integral. No extension to arbitrary nonintegrable tests is assumed. The actual density criterion and Bochner change-of-measure APIs are used, with density finite and nonnegative established explicitly.

Original id-integrability and actual β≥1 are supplied internally from the genuine square/cube hypotheses and unit second moment, using the accepted third-absolute-moment theorem. All three weighted original moment functions and all three tilted moment functions are genuinely integrable. The three numerator bounds and normalized moment bounds have the exact frozen T-only constants:

E=exp(4T), C1=1/4+ET, C2=1/2+2ET, D=(4/3)E,
Cμ=D C1, Cm2=D(C2+T+C_Z(T)), Cm3=D E.

The exponential difference bound is proved on both signs of the actual cutoff argument using the exponential derivative bound. The second moment normalization compares M2 with Z and uses the actual N0 error and internal β≥1,h≥1 to retain the required T+C_Z terms. No numerical constant, height threshold or mathematical hypothesis was changed.

Only mean numerator and normalized mean statements require the original centering equation. The actual law, its support/change of measure, and all second/third conclusions do not. There is no id-integrability, β≥1, Z>0, numerator bound, moment bound, symmetry, density, bounded-support, fourth/exponential moment or exact tilted-centering hypothesis. β is always the actual original integral.

At s=0 the law is normalized closed truncation, generally different from ν. Original atoms at zero and ±2h remain, and the strict complement has zero tilted mass. Cases T=0 and h=1 are covered. The tilted mean is controlled rather than claimed to be zero; the second moment is raw about zero, not variance. This unit proves N1 only: no log Z precision, E2 exact recentering, E3 path density, E4, B1, BE/SP, K/Kv, random denominator, or complete root theorem.

## Actual server checks

Every Lean invocation was server-only, after activation and changing to the OQ4 worktree, using one author process with four-core affinity. Only the new module olean was emitted, exactly once. No old target/olean or shared cache/common/root/Git/manifest/lock change occurred. No package cache request or download was needed.

Parent-reported current branch `feat/oq4-energy-law`, HEAD `28b459e8d6e30cc06c8402027c1a8ee18a08c5a7`; this only committed independently accepted N0 and switched branch without changing source/olean dependencies. N1 was excluded from PR46. The author performed no Git operations.

Toolchain `leanprover/lean4:v4.36.0-rc1`; mathlib `807d3836b165983210ee2ecf3cd28f239436949c`.

| Check | Exit | Full server-only record |
|---|---:|---|
| Full new source body following all24 old OQ4 imports | 0 | `repro_outputs/oq4-energy-law/coexist05.log`, `.exit` |
| Canonical new source target | 0 | `repro_outputs/oq4-energy-law/target01.log`, `.exit` |
| Author-only unique olean emission | 0 | `repro_outputs/oq4-energy-law/olean.log`, `.exit` |
| Actual25-module imports and module-owner complete transitive axiom audit | 0 | `repro_outputs/oq4-energy-law/audit.log`, `.exit` |

All successful compilation logs are empty, with no diagnostics. Earlier failed API source snapshots are preserved under local history/; full logs coexist01–coexist04 remain only on the server. They concerned explicit function/id/Pi application simplification, squared absolute-value rewriting, and numerical-definition unfold order. Mathematical premises, targets and constants stayed fixed.

The dynamic audit filters by exact owner module index, with no constant-name/namespace prefix filter. It enumerated **54 actual new constants =29 explicit (7 definitions+22 theorems)+25 generated**. All54 actual transitive axiom sets are whitelist subsets:33 {propext, Classical.choice, Quot.sound},21 {propext}. No unexpected axioms; source banned-token scan empty. The complete per-declaration results are in declarations.md and curated summary.json. Raw logs and binary artifacts remain server-only.

## Reproduction

```sh
set -e
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean repro_outputs/oq4-energy-law/CoexistSource.lean
taskset -c 0-3 lake env lean Shao/OQ4/EnergyTiltedLaw.lean
# Author emission already completed once; reviewers use source/no-o and imports.
# taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/EnergyTiltedLaw.olean Shao/OQ4/EnergyTiltedLaw.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-energy-law/Audit.lean
python3 repro_outputs/oq4-energy-law/summarize.py
```

The local check.ps1, CoexistSource.lean, Audit.lean and summarize.py record the reproducible new-module workflow. Audit imports all25 modules and selects exact module ownership. Local artifacts are curated source/proof/receipt/declarations/summary/checkpoint/helpers and failed source snapshots only.
