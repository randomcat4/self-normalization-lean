# EnergyLinearTiltVarianceWindow author verification receipt

Author implementation and all required server mechanical gates passed. Parent reported independent frozen-statement and anonymous-mathematical CORRECT. Independent final source/formal certification is separate and pending; this receipt does not self-certify it.

## Frozen artifacts

- Interface drafts/oq4/frozen-energy-linear-variance-window-v1.md.
- Anonymous proof SHA256 `1571edff7df1dbaecb12720b4081d21013c8869340ef643faae84331ea63832c`, unchanged from the proof-only freeze.
- Server source `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/EnergyLinearTiltVarianceWindow.lean`.
- Final source SHA256 `a0059db361b524332d85c73eb13577b67de5df1fe4d7f41c3cd2aba9072e5c73`, 12062bytes.
- Author-only unique olean SHA256 `b087299dd71cf5e1bb24df55872fe4db467208ff4b6d64d28579a80d39f05cf0`.
- Local final source drafts/oq4/energy-linear-variance-window/EnergyLinearTiltVarianceWindow.lean.
- UTF-8 without BOM, LF only, exactly one final LF. Source/proof now immutable.

## Explicit constants and quantifiers

Four transparent real definitions introduce exactly A=P M, B=exp(2)K(A+6), C=A+5exp(2)K and Hvar=energyLogThreshold(M,T)+8(1+A+B+C+K). P is the unchanged actual energyE1Constant(T); J is exp(2). No unspecified existence constant or replacement threshold is used.

M,T,K≥0 are fixed before h. All actual laws and numerical conclusions apply to every ν probability satisfying original genuine square/cube integrability, original second1/mean0 and actual β≤M, every h≥Hvar, |s|≤T and |t|≤K/h². Original id integrability is supplied internally by the original-moment/E1 chain. No extra M≥1, center of μ/μ_t, variance lower bound, differentiability, bounded original ν support, exponential/fourth moment, density/symmetry/nonlattice premise is introduced. K is not selected here and Hvar explicitly depends on M,T,K.

## Mathematical payments actually implemented

The height theorem proves h≥energyLogThreshold(M,T),h≥2 and h≥8A,8B,8C,8K. It uses actual P≥1 and the known threshold lower bound, with nonnegative explicit constants. The scalar fraction helper divides only by h>0; for X≥0 and8X≤h it proves X/h≤1/8,X/h²≤1/8 and X/h²≤1/2, retaining X=0. The exponential theorem proves D²≤exp(2) from the actual t restriction and h≥8K, internally obtaining4h|t|≤1/2.

The initial-bound theorem calls actual energyE1_common_bounds. It explicitly retains |q−1|≤A/h and |m0|≤A/h², proves genuine μ-integrability of |x|, and proves q≤2,u1≤3,|m0|≤1,r≤A. The u1 estimate integrates the true pointwise |x|≤1+x² against actual μ probability, using genuine id/square/constant integrability. These numerical bounds are conclusions, never assumed.

The moment-bound theorem calls the frozen actual normalized comparisons. With the initial bounds it proves r+qu1≤A+6 and q+|m0|u1≤5, then obtains |q_t−q|≤B/h² and |m_t|≤C/h². It also returns |q_t−1|≤A/h+B/h²≤1/4 and C/h²≤1/2. Both normalization contributions from the comparison leaf remain intact. All involved moments and actual tilted-law quotient identities retain their genuine integrability from E1/first law; no abstract replacement law or input error estimates are used.

The final window theorem supplies actual μ_t probability, true id/square/centered-square integrability and the exact actual integral identity v_t=q_t−m_t² by calling the certified first-law and derivative interfaces. The just-proved moment bounds give3/4≤q_t≤5/4 and m_t²≤1/4. Hence1/2≤v_t≤2. It also returns genuine HasDerivAt m v_t at t by the certified all-real derivative theorem, including the closed window endpoints. The raw q_t is not called variance, and m_t is not assumed zero.

All frozen zero/sign/weak boundary cases are covered: K=0 forces t=0 but no division by K,A,B,C occurs; T=0,s=0,h=Hvar and |t|=K/h² remain included. Arbitrary closed cutoff atoms are retained via actual ae closed support. M<1 is not ruled out by a new premise; the admissible class may be empty, and the scalar constants remain valid for all M≥0. No original support assertion is inferred from actual μ/μ_t support.

Only the common finite variance window and its genuine derivative summary are supplied. There is no choice of K(M,T), endpoint sign, θ existence/uniqueness, exact centering, selected-θ log or moment error, or complete common E2 constant. E2,E3,E4,K/Kv,random denominator and all complete OQ4 roots remain OPEN.

## Server execution and actual gates

Parent-confirmed baseline: feat/oq4-linear-comparisons HEADae4b9c3865e33e231252693e23ff0338ead29b16. All30 old modules were frozen, including comparisonf1aa/derivativef844/firstlaw63cf. The author performed no Git action and changed no common/root import/manifest/cache/lock or other-owner file. No old target/olean was rebuilt. Only this new module's olean was emitted, exactly once.

Every Lean check ran only on the designated server after activation and changing back to this worktree, taskset -c 0-3 and at most one author Lean process. Toolchain `leanprover/lean4:v4.36.0-rc1`, mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. Canonical imports are only EnergyE1Bounds,EnergyLinearTiltComparisons and EnergyLinearTiltDerivatives. No cache module was missing; no package download/install/cache write occurred.

| Check | Exit | Full server-only record |
|---|---:|---|
| Exact final source body after all30 old OQ4 imports | 0 | repro_outputs/oq4-energy-linear-variance-window/coexist02.log and .exit |
| Canonical new source target | 0 | repro_outputs/oq4-energy-linear-variance-window/target01.log and .exit |
| Author-only unique olean emission | 0 | repro_outputs/oq4-energy-linear-variance-window/olean.log and .exit |
| Actual31-module imports, all module-owned signatures and transitive axioms | 0 | repro_outputs/oq4-energy-linear-variance-window/audit.log and .exit |

The three successful compilation logs are all0bytes. Local source-body equivalence was checked against the exact frozen source body with only import lines deleted, after all30 old imports. The coexist02 source snapshot is byte-identical to the final source.

Owner-index enumeration found15 actual new constants=11 explicit (4 definitions+7 theorems)+4 generated helpers. It applies no namespace/name-root restriction, including to imported-name helpers if present. Every one of15 full signatures and15 actual transitive axiom records was recorded:11 use {propext,Classical.choice,Quot.sound},4 only {propext}. No unexpected axiom or banned source token. Complete actual names/types/axioms are in declarations.md and summary.json. Rawlogs/olean/binaries remain server-only.

## Failed API adaptation history

coexist01 failed on positivity because the unfold order reintroduced a defined A beneath B/C, and on a pointwise integral comparison whose Pi.add notation required explicit reduction. The repair reordered transparent unfolding and added the exact pointwise change |x|≤1+x². No frozen constant, premise, conclusion or proof mathematics changed. coexist02 then passed without diagnostics. Both snapshots are retained under local history/; full failed log/exit remain only server-side and were not overwritten.

## Reproduction

```sh
set -e
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean repro_outputs/oq4-energy-linear-variance-window/CoexistSource.lean
taskset -c 0-3 lake env lean Shao/OQ4/EnergyLinearTiltVarianceWindow.lean
# Author emission already completed once; reviewers use no-o source and actual imports.
# taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/EnergyLinearTiltVarianceWindow.olean Shao/OQ4/EnergyLinearTiltVarianceWindow.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-energy-linear-variance-window/Audit.lean
python3 repro_outputs/oq4-energy-linear-variance-window/summarize.py
```

Local check.ps1,CoexistSource.lean,Audit.lean,summarize.py retain the workflow. The summarizer checks encoding/source/olean hashes, every exit/count, all name/signature/axiom record equality, the whitelist and source token restrictions. Only curated JSON, source/proof, receipts/ledger/checkpoint and helper/history source are retained locally.
