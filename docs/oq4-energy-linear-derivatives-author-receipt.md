# EnergyLinearTiltDerivatives author verification receipt

All required author implementation and mechanical server checks passed. The lead reported independent statement CORRECT and anonymous mathematical CORRECT/MATH_ONLY. Independent final source/formal review is separate and pending; this author receipt does not self-certify it.

## Frozen artifacts

- Interface `drafts/oq4/frozen-energy-linear-derivatives-v1.md`.
- Anonymous proof SHA256 `9edcf7be76ace16c1bab921c0b9c094caea0ba493032fd3479a7ae217c05bb16`, unchanged.
- Server source `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/EnergyLinearTiltDerivatives.lean`.
- Final source SHA256 `f84467d102660c9abfa09062d1dbe8b3c499058b9960d779aa86fcd653b9a6b2`, 10286bytes.
- Author-only unique olean SHA256 `80caefbbc459a7c3c58a7907718f0a61b5524c3c3173c08f01a1225bf59ccb71`.
- Local final source `drafts/oq4/energy-linear-derivatives/EnergyLinearTiltDerivatives.lean`.
- UTF-8 without BOM, LF only, one final LF. Final source/proof are frozen.

## Exact objects and conclusions

Every conclusion is about the fixed first-leaf actual functions L=energyLinearNormalizer, A1=energyLinearFirstNumerator, A2=energyLinearSecondNumerator and m=energyLinearMean, and the actual measure μ_t=energyLinearTiltLaw. For every real t the four genuine HasDerivAt conclusions are L′=A1, A1′=A2, (log L)′=m and m′=A2/L−m². The same actual μ_t genuinely integrates the centered square and its integral is exactly A2/L−m². A separate HasDerivAt gives that actual integral as derivative. Its nonnegativity is proved by the squared integrand. L,A1,m and log L are continuous from these actual derivatives.

The single local-support envelope theorem bounds every natural power, hence the required j=0,1,2 cases: when |x|≤2h and |u−t|≤1, ‖x^j exp(ux)‖≤(2h)^j exp(2h(|t|+1)). The actual μ probability and ae closed support are supplied internally by N1/first leaf. At each t, the interval (t−1,t+1) is an actual neighborhood; the derivative envelopes are constants integrable under actual μ. The measurable parameter families, actual integrability at t, measurable derivative integrands, ae local bounds and pointwise parameter HasDerivAt are all supplied to Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le`. No interchange/differentiability hypothesis is assumed.

The quotient and logarithm use the first leaf's internally proved L>0. The centered-square integrability uses actual first/second tilted moments and probability, expands (x−m)² and integrates each genuinely integrable term, then uses the exact actual mean/second identities. It does not rely on a formal or potentially undefined variance notation.

Frozen assumptions are ν probability, original square/cube integrability, original second moment1,T≥0,h≥1,|s|≤T. Genuine derivative/continuity conclusions retain the original cubic condition as an explicit `_hCube` parameter, even though the support argument needs no additional use of it. Parameter order is ν,T,h,s,hT,hh,hs,hSq,hsecond,_hCube, then t when present. The centered-square integral and nonnegative-expression auxiliaries omit unused cube as a strengthening covering the whole frozen domain. The purely pointwise envelope has no measure assumptions.

All real t, both signs and t=0,h=1,T=0,s=0 and closed cutoff atoms are covered. No original center,M,K,θ,positive variance, bounded original ν support, original exponential/fourth moments or symmetry/density condition was added. Degenerate actual μ_t may have zero centered-square integral. No common positive variance interval, endpoint signs, θ existence, exact centering or selected-θ log/moment bounds are claimed. Complete E2,E3,E4,K/Kv,random denominator and OQ4 roots remain OPEN.

## Server checks

Every Lean run occurred only on the designated server, after activation and changing back to this worktree, with one author process and taskset -c 0-3. Only this module's new olean was emitted, exactly once. No old target/olean was rebuilt. No Git/common/root/manifest/audit/cache/lock modification, install or package download occurred. `Mathlib.Analysis.Calculus.ParametricIntegral` was already cached; no cache request was required.

Parent-confirmed baseline: feat/oq4-energy-centering HEAD2380a8e5798e848f3c9d644ff09e83a90194fd38; all28 prior OQ4 sources and their dependencies remained fixed throughout these checks. The author did not inspect or change Git state. Canonical imports are only the frozen EnergyLinearTiltLaw and cached ParametricIntegral modules. Toolchain `leanprover/lean4:v4.36.0-rc1`; mathlib `807d3836b165983210ee2ecf3cd28f239436949c`.

| Check | Exit | Full server-only record |
|---|---:|---|
| Exact new source body after all28 prior OQ4 imports | 0 | `repro_outputs/oq4-energy-linear-derivatives/coexist03.log`, `.exit` |
| Canonical new source target | 0 | `repro_outputs/oq4-energy-linear-derivatives/target01.log`, `.exit` |
| Author-only unique olean emission | 0 | `repro_outputs/oq4-energy-linear-derivatives/olean.log`, `.exit` |
| Actual29-module imports and complete owner-module transitive axiom audit | 0 | `repro_outputs/oq4-energy-linear-derivatives/audit.log`, `.exit` |

The successful source-body, target and olean logs are all0bytes, without diagnostics. The local source-body artifact was independently checked to be the exact final source body after deleting only its import lines, appended to the28 prior module imports.

The audit dynamically found **17 actual new constants=9 explicit theorems+8 generated**, including the cross-name helper `Shao.OQ4.energyLinearMean.eq_1`. All17 axiom records passed:11 have {propext,Classical.choice,Quot.sound},6 only {propext}. No unexpected axioms or banned source tokens. `declarations.md` and `summary.json` retain every name and actual axiom set. Raw logs and binaries remain server-only.

## Retained adaptation history

The first full coexistence attempt failed on definitional simplifications of exp derivatives and quotient function equality; a second attempt resolved the genuine integral derivatives but exposed a docstring/omit parsing issue and unused-section cubic warnings. These were mechanical API/signature adaptations, with no frozen premise or mathematical constant change. Failed snapshots coexist01/coexist02 and final successful coexist03 are retained under local history/. Their full failure logs and exit files remain only in server repro_outputs/oq4-energy-linear-derivatives/. No failed history was overwritten. The final source retains explicit original cubic parameters on the derivative/continuity conclusions.

## Reproduction

```sh
set -e
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean repro_outputs/oq4-energy-linear-derivatives/CoexistSource.lean
taskset -c 0-3 lake env lean Shao/OQ4/EnergyLinearTiltDerivatives.lean
# Author emission already completed once. Reviewers use source/no-o and actual imports.
# taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/EnergyLinearTiltDerivatives.olean Shao/OQ4/EnergyLinearTiltDerivatives.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-energy-linear-derivatives/Audit.lean
python3 repro_outputs/oq4-energy-linear-derivatives/summarize.py
```

Local check.ps1, CoexistSource.lean, Audit.lean and summarize.py retain the workflow. The summarizer checks source/olean hashes, source encoding, every exit/count, every owned declaration and actual transitive axiom record. No local raw log or binary is part of this delivery.
