# EnergyLogNormalizer N2 author verification receipt

Required author-side implementation and mechanical checks passed. The lead reported independent statement and anonymous mathematical review CORRECT. Final independent source-to-statement/formal review is pending; this receipt is not an independent review.

## Frozen artifacts

- Interface: `drafts/oq4/frozen-energy-log-normalizer-v1.md`.
- Anonymous proof N2-v1 frozen SHA256 `10515d73e42d76df5788b85e45f1a914ce8bb0c4d1a2e569a44113a82c848cff`.
- Server source: `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/EnergyLogNormalizer.lean`.
- Source SHA256 `6bbf4093ed296e5fa40cc680f77670c5a3889d95a3679a1cfaf011a84efa6906` (8357bytes).
- Author-only unique olean SHA256 `0b313122e8b66993d85ff6368f60349b80c8e9458d63464b3b752121f1c6b84b`.
- Local final source `drafts/oq4/energy-log/EnergyLogNormalizer.lean`.
- UTF-8 without BOM, LF only, one final LF. Source and proof are frozen.

The canonical module imports only fixed TruncatedEnergy N0, the accepted IntervalConcentration actual moment inequality, and Mathlib Log.Basic. It does not import N1 EnergyTiltedLaw. N0 bd801 and every old source/olean remained untouched.

## Exact coverage

energyLogThreshold M T is exactly H=2(1+M+T+C_Z(T)M). energyLogErrorConstant T is exactly C_log=C_Z(T)+4T²+4C_Z(T)². Both dependencies are explicit: H depends only on M,T; C_log only on T.

The actual probability law hypotheses are precisely true square/cube integrability, unit second moment, M≥0, actual β≤M, T≥0, |s|≤T and h≥H. Neither id-integrability nor original centering is present. Actual β≥1 is obtained inside the final theorem from the accepted unit-second-moment inequality, not added to the law assumptions.

energyLog_normalizer_close calls N0's real weight integrability and actual expansion and returns true weight integrability, h≥2, β≤M≤h, the explicit raw Z-error bound, |Z−1|≤1/2, 1/2≤Z≤3/2 and Z>0. These are conclusions, not extra inputs. Therefore the log theorem uses a genuinely positive finite normalizer and not total log conventions.

The pure real log lemma uses 1−1/z≤log z≤z−1 for z≥1/2 and proves |log z−(z−1)|≤2(z−1)² without an upper z≤1 assumption. The scalar square-payment lemma retains the coefficients four. It uses β≥1 and β≤h only as pure numerical conditions, supplied internally in the final actual theorem. The actual conclusion is |log Z−s/h²|≤C_log(T)β/h³, with no M,ν,h,s hidden in the error coefficient.

T=0, s=0, closed truncation atoms and unbounded original support are retained; Z(h,0) is never replaced by one. There is no new fourth/exponential moment, bounded-support, density, nonlattice or symmetry assumption. This proves only finite N2. It neither constructs nor certifies N1, nor proves E2/E3/E4, B1, BE/SP, K/Kv, a random denominator or any complete root theorem. Complete roots remain OPEN.

## Actual checks and resources

All Lean checks ran only on the designated server, after activation and changing back to the assigned worktree, with one author process and `taskset -c 0-3`. Only this new olean was emitted, exactly once. Old targets/oleans were not rebuilt. No Git/common/root/manifest/lock/shared-cache edit, install or cache download occurred.

Parent-confirmed branch `feat/oq4-energy-law`, HEAD `28b459e8d6e30cc06c8402027c1a8ee18a08c5a7`; no baseline/source mutation occurred during this task. Author performed no Git operation.

Toolchain `leanprover/lean4:v4.36.0-rc1`; mathlib `807d3836b165983210ee2ecf3cd28f239436949c`.

| Check | Exit | Full server-only record |
|---|---:|---|
| Exact new source body after25 prior OQ4 imports | 0 | `repro_outputs/oq4-energy-log/coexist02.log`, `.exit` |
| Canonical new source target | 0 | `repro_outputs/oq4-energy-log/target01.log`, `.exit` |
| Author-only unique olean emission | 0 | `repro_outputs/oq4-energy-log/olean.log`, `.exit` |
| Actual26-module imports and complete owner-module transitive axiom audit | 0 | `repro_outputs/oq4-energy-log/audit.log`, `.exit` |

All final compile logs are 0bytes, with no diagnostics. The initial coexist01 source and full server log are preserved: the sole failure was a redundant ring tactic after field_simp had already closed a rational identity. Removing that redundant tactic changed no premise, numerical constant or conclusion. No cache gap occurred.

The dynamic audit selects exact module ownership through env.getModuleIdxFor?, with no name-root/namespace filter. It found **17 actual new constants=8 explicit (2 definitions+6 theorems)+9 generated**. Actual transitive audit records:9 {propext, Classical.choice, Quot.sound},8 {propext}. No unexpected axioms; banned source-token scan empty. All names and exact axiom sets appear in declarations.md and curated summary.json. Raw logs and binaries remain server-only; local files are curated sources/proof/receipt/declarations/summary/checkpoint/helper source and failed API snapshots.

## Reproduction

```sh
set -e
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean repro_outputs/oq4-energy-log/CoexistSource.lean
taskset -c 0-3 lake env lean Shao/OQ4/EnergyLogNormalizer.lean
# Author emission already completed once; reviewers use no-o source and actual imports.
# taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/EnergyLogNormalizer.olean Shao/OQ4/EnergyLogNormalizer.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-energy-log/Audit.lean
python3 repro_outputs/oq4-energy-log/summarize.py
```

The local check.ps1, CoexistSource.lean, Audit.lean and summarize.py reproduce the owned-module checks. Audit imports all26 modules and enumerates every constant owned by the new module; the summarizer validates counts, axioms, exits, hashes and encoding without copying raw logs locally.
