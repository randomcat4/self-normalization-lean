# EnergyLinearTiltComparisons author verification receipt

Author implementation and all required mechanical server checks passed. The lead reported the frozen statement and anonymous mathematics independently CORRECT/MATH_ONLY. Independent final source/formal certification is separate and pending; this author receipt does not self-certify it.

## Frozen artifacts

- Interface `drafts/oq4/frozen-energy-linear-comparisons-v1.md`.
- Anonymous mathematical proof SHA256 `d052c6eeb1c52dc81266d4e601d301a5b21536149117d9f401c3e6807b061f30`, unchanged from its proof-only freeze.
- Server source `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/EnergyLinearTiltComparisons.lean`.
- Final source SHA256 `f1aa93d33998f5365d236b9f96e2e04cab4e6235672a7b634988cd2330497cd4`, 11459bytes.
- Author-only unique olean SHA256 `0a7b8c991d4357e3114664e6a830487499be1b1271a3254799a00b50ee6ce614`.
- Local final source `drafts/oq4/energy-linear-comparisons/EnergyLinearTiltComparisons.lean`.
- UTF-8 without BOM, LF only, exactly one final LF. Final source/proof immutable.

## Exact scope and interface fidelity

Only the fixed first-law module EnergyLinearTiltLaw is imported. Its source63cf remains frozen; the derivative leaf f844 and every older source are unchanged and not needed as mathematical inputs.

The actual μ is energyTiltedLaw ν h s, and L,A1,A2,B3,μ_t,m are exactly the frozen first-leaf definitions. u1,m0,q,r are actual μ integrals of |x|,x,x²,|x|³; q_t,r_t are actual μ_t integrals. D is transparently exp(2h|t|), with no new numerical or abstract-law input. No new definition is introduced.

`energyLinear_raw_comparisons` proves the four conclusions |L−1|≤D|t|u1, |A1−m0|≤D|t|q, |A2−q|≤D|t|r, and 0≤B3≤Dr. `energyLinear_normalized_comparisons` proves |m−m0|≤D²|t|(q+|m0|u1), |q_t−q|≤D²|t|(r+qu1), and r_t≤D²r. Both additional normalization terms and the exact D² factor are present in the actual full theorem signatures. The mean and tilted raw moments are the actual first-leaf integrals/quotients.

Every public admissible interface quantifies ν probability,T,h,s,hT,hh,hs,hSq,hsecond, followed by k/t when applicable. Original cubic integrability is unused and omitted as an expressly permitted strengthening covering the entire frozen square/cube/unitsecond domain. No original center,M,K,θ,positive variance, bounded ν support, original exponential/fourth moment or symmetry/density assumption is introduced. The scalar algebra helper has abstract scalar error hypotheses only internally; neither of the actual grouped conclusion theorems assumes these errors or L positivity/reciprocal bounds.

## Actual integrability and normalization obligations

The signed-power integrability helper proves genuine μ-integrability of x^k exp(tx) for every finite natural k from the first leaf's actual absolute-power integrability. At0 this supplies x^k integrability. Before integrating each difference, its genuine integrability is explicitly obtained by subtracting two actual integrable functions, with pointwise polynomial conversion. The first leaf also supplies genuine absolute-power majorants. Therefore subtraction, absolute-integral estimates and a.e. integral monotonicity operate on genuinely integrable functions, including u1 obtained internally at power1/parameter0. The actual μ and μ_t probability/support and tilted moment integrability are internally supplied by the frozen dependencies.

A global scalar exp-difference estimate is proved using the elementary tangent inequality 1+y≤exp(y), splitting the sign of y. Applied only at points of actual μ's a.e. closed support, it gives |exp(tx)−1|≤D|t||x|. Multiplication by |x|^k and integration yields the stronger all-finite-k raw deviation; its k=0,1,2 instances give the requested raw comparisons. Nonnegative third numerator and its upper bound use actual integrability and a.e. exp(tx)≤D.

The exact lower L bound supplies internally 1/L≤D and L>0. The scalar quotient helper retains (A−b)+b(1−L), so the actual mean uses q+|m0|u1 and the actual second raw moment uses r+qu1. The third normalized bound uses B3/L≤Dr/L≤D²r. The division is solely by actual internally positive L; no variance or moment lower bound is used.

The anonymous mathematical proof remains unchanged. The formal scalar proof of its elementary exponential inequality uses the equivalent tangent-inequality argument, without any changed mathematical assumption, conclusion or constant. t=0,both signs of t,h=1,T=0,s=0,arbitrary atoms and closed endpoints±2h are included. The support is a.e. under actual μ, not an original ν support hypothesis. Zero or degenerate moments cause no division by them. All integrals are finite for each arbitrary real t.

The unit supplies only these finite comparisons. No parameter derivative, common positive variance window, endpoint sign, selected θ, exact centering, selected-θ log/moment bound or final common E2 constant is claimed. Complete E2,E3,E4,K/Kv,random denominator and every complete OQ4 root remain OPEN.

## Server execution and actual checks

Parent-confirmed branch feat/oq4-linear-comparisons, HEADae4b9c3865e33e231252693e23ff0338ead29b16. All29 old module sources were frozen. The author performed no Git operation and made no common/root imports/manifest/shared-cache/lock changes or package downloads. No old target or olean was rebuilt. Only the new module's olean was emitted, exactly once, by the sole author. All Lean ran only on the designated server after activation and changing back to this worktree, with taskset -c 0-3 and at most one author process.

Toolchain `leanprover/lean4:v4.36.0-rc1`; mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. No missing API/cache request occurred.

| Check | Exit | Full server-only record |
|---|---:|---|
| Exact final source body after all29 old module imports | 0 | `repro_outputs/oq4-energy-linear-comparisons/coexist02.log`, `.exit` |
| Canonical new source target with only first-law import | 0 | `repro_outputs/oq4-energy-linear-comparisons/target01.log`, `.exit` |
| Author-only unique olean emission | 0 | `repro_outputs/oq4-energy-linear-comparisons/olean.log`, `.exit` |
| Actual30 imports, complete owner enumeration, full signatures and transitive axiom audit | 0 | `repro_outputs/oq4-energy-linear-comparisons/audit.log`, `.exit` |

The successful source-body, target and olean logs are all0bytes. The local source-body artifact was checked equal to the exact final source with import lines removed, appended to all29 old imports. The final successful history snapshot is byte-identical to the frozen source.

The dynamic audit found10 actual new constants=8 explicit theorems+2 generated helpers;0 definitions. Of the explicit theorems2 group the requested conclusions and6 supply support/integrability/algebra. Both generated names are included, particularly the imported-name `Shao.OQ4.energyLinearSecondNumerator.eq_1`. All10 full signatures and all10 actual transitive axiom records were collected.9 records use {propext,Classical.choice,Quot.sound},1 only {propext}; no other axiom or banned source token. `declarations.md` and `summary.json` retain every record. Rawlogs/olean/binaries remain server-only.

## Retained failed API history

coexist01 failed only because the simplifier did not convert a pointwise function subtraction beneath Integrable, and a simp-only step on integral_sub made no progress. The repair used explicit function extensionality/ring for integrability and an explicit integral_congr_ae equality before integral_sub. The mathematics, all assumptions and seven constants were unchanged. coexist02 passed with no diagnostics. Both source snapshots remain in local history/; full failed logs and exit files remain in server repro_outputs/oq4-energy-linear-comparisons/. No failure was overwritten.

## Reproduction

```sh
set -e
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean repro_outputs/oq4-energy-linear-comparisons/CoexistSource.lean
taskset -c 0-3 lake env lean Shao/OQ4/EnergyLinearTiltComparisons.lean
# Author emission already completed once; reviewers use no-o source and actual imports.
# taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/EnergyLinearTiltComparisons.olean Shao/OQ4/EnergyLinearTiltComparisons.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-energy-linear-comparisons/Audit.lean
python3 repro_outputs/oq4-energy-linear-comparisons/summarize.py
```

Local check.ps1, CoexistSource.lean, Audit.lean and summarize.py retain the exact workflow. The summarizer validates source/olean hashes, encoding, all exits, full owned-name/signature/axiom record equality, the whitelist and source-token restrictions, and emits only curated JSON locally.
