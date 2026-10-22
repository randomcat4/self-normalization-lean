# EnergyE1Bounds author verification receipt

Author implementation and all required mechanical checks passed. Statement review was reported CORRECT by the lead; independent mathematical/final wrapper review and the lead integration gate remain pending. This is not independent certification or an E1-closure claim.

## Frozen artifacts

- Interface `drafts/oq4/frozen-energy-e1-bounds-v1.md`.
- Anonymous composition proof E1-v1 frozen SHA256 `bc4893ea78553175ab49586d4769c2b09e2afd6cffd5e2149acc57eaab765e25`.
- Server source `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/EnergyE1Bounds.lean`.
- Source SHA256 `448db6e250307358455e7c8da660ffdb094ddb5a42f0e7e81e9c08c02aa4d39d` (4591bytes).
- Author-only unique olean SHA256 `e927aada111c1df8170382b10399314dee4f0fed82d3fc1a9f5fdfdac1d8854c`.
- Local final source `drafts/oq4/energy-e1/EnergyE1Bounds.lean`.
- UTF-8 without BOM, LF only, exactly one final LF. Source and proof are frozen.

## Exact scope

Only composition of the frozen actual N0/N1/N2 is performed. CE1(T) is exactly 1+Clog(T)+Cμ(T)+Cm2(T)+Cm3(T); its dominance theorem uses only their accepted nonnegativity. The uniform height threshold is the existing energyLogThreshold M T without alteration. No new analytic estimate or dependence on ν,β,M,h,s is inserted into the common coefficient.

energyE1Conclusion is a transparent conclusion predicate on the same actual energyTiltedLaw and energyNormalizer. It expands to probability, genuine tilted id/square/cube integrability, ae closed support, internally supplied h≥2 and Z∈[1/2,3/2], and all four actual log/mean/raw-second/cube inequalities with the one same CE1(T). It is never a premise. Borel mass and weighted-integrable test change of measure remain directly traceable to the unchanged N1 public interfaces.

energyE1_common_bounds assumes exactly the original centered probability setting, genuine square/cube integrability, unit second moment, M≥0, actual β≤M, T≥0, |s|≤T and h≥H(M,T). Original id integrability and β≥1 are supplied inside the unchanged moment interfaces, not distribution hypotheses. N1 supplies genuine weighted and tilted integrability; no desired law, Z-error, numerator or moment conclusion is assumed. Coefficient enlargement uses actual β≥0 and h>0. energyE1_fixed_law_bounds takes M equal to the actual β and supplies its nonnegativity by integration; it preserves the same CE1 and threshold formula.

The raw second moment is not claimed to be variance, and the tilted mean is not claimed zero. T=0,s=0,weak threshold equality, closed endpoints/zero atoms and unbounded original support remain. No fourth/exponential moment, symmetry, atomlessness, density, nonlattice or bounded-support restriction is introduced. This wrapper does not prove E2/E3/E4, B1, BE/SP, K/Kv, random-denominator conclusions or any complete OQ4 root. Even finite E1 formal-coverage status is reserved for the dependency+wrapper independent/integration gates.

## Execution and checks

All Lean invocations ran only on the designated server, after activation and changing back to the assigned OQ4 worktree. Each used one author process with taskset -c 0-3. Only this new module olean was emitted, once. No old target/olean rebuild, Git/common/root/manifest/lock/cache change, installation or download occurred.

Parent-confirmed branch feat/oq4-energy-law, HEAD28b459e8d6e30cc06c8402027c1a8ee18a08c5a7; no baseline/source/olean mutation occurred during this task. Canonical imports are only EnergyTiltedLaw and EnergyLogNormalizer. The lead reported N0 bd801, N1 ea13 and N2 6bbf independently CORRECT/FULLY_CHECKED; this author did not read their tickets or edit their sources/proofs.

Toolchain leanprover/lean4:v4.36.0-rc1; mathlib807d3836b165983210ee2ecf3cd28f239436949c.

| Check | Exit | Full server-only record |
|---|---:|---|
| Full exact source body following all26 prior OQ4 imports | 0 | `repro_outputs/oq4-energy-e1/coexist01.log`, `.exit` |
| Canonical new source target | 0 | `repro_outputs/oq4-energy-e1/target01.log`, `.exit` |
| Author-only unique olean emission | 0 | `repro_outputs/oq4-energy-e1/olean.log`, `.exit` |
| Actual27-module imports and all-new-constant owner/transitive audit | 0 | `repro_outputs/oq4-energy-e1/audit.log`, `.exit` |

Every first attempt passed. Final compile logs are 0bytes, with no diagnostics. No cache/API blocker occurred. A curated initial source snapshot is preserved under history/; it is identical to the accepted source, and there are no failed API snapshots for this wrapper.

Exact module-owner enumeration found **7 actual new constants=5 explicit (2 definitions+3 theorems)+2 generated**. Every constant received an actual transitive axiom record:5 have {propext,Classical.choice,Quot.sound},2 only {propext}. No unexpected axioms or banned source tokens. The audit selects exact owner module index without namespace/root-name filtering. Complete names and axiom sets are in declarations.md and curated summary.json. Raw logs/binaries stay only on the server; local files are curated source/proof/receipt/declarations/summary/checkpoint/helper source and the initial snapshot.

## Reproduction

```sh
set -e
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean repro_outputs/oq4-energy-e1/CoexistSource.lean
taskset -c 0-3 lake env lean Shao/OQ4/EnergyE1Bounds.lean
# Author emission already completed once; reviewers use source/no-o and imports.
# taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/EnergyE1Bounds.olean Shao/OQ4/EnergyE1Bounds.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-energy-e1/Audit.lean
python3 repro_outputs/oq4-energy-e1/summarize.py
```

The local check.ps1, CoexistSource.lean, Audit.lean and summarize.py provide the exact workflow. Audit imports all27 modules. The summarizer checks encoding, hashes, successful exits, explicit/actual counts, complete transitive axiom coverage and banned tokens, and writes a curated summary rather than local raw logs.
