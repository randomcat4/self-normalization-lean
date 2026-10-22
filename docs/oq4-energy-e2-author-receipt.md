# EnergyE2Bounds author verification receipt

Author implementation and every required mechanical server gate passed. Parent reported independent statement and anonymous mathematical CORRECT. Independent final source/formal review and lead/root acceptance remain separate and pending; this receipt does not self-certify final E2 closure.

## Frozen artifacts

- Frozen interface drafts/oq4/frozen-energy-e2-bounds-v1.md.
- Anonymous proof SHA256 `77832539608025fab3220d6fb8a8e02d3aca5e676d3e7a9cde86a35baa334442`, unchanged from the mathematical freeze.
- Final server source `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/EnergyE2Bounds.lean`.
- Final source SHA256 `41b7343861549f55ae86cddb514a5ed55612448b1ab0efc1e3bb580182746ca8`, 11643bytes, identical to the scratch-approved frozen version.
- Author-only unique olean SHA256 `df937ab8fafcaacc7bbd37e3413356f15fddff0ed282807692269934614dd7c9`.
- Local final source drafts/oq4/energy-e2/EnergyE2Bounds.lean.
- UTF-8 without BOM, LF only, exactly one final LF. No format or mathematical correction was needed after freezing41b.

## Exact constants, actual laws and conclusion

The definitions are exactly H2(M,T)=energyLinearCenteringThreshold(M,T) and C2(M,T)=1+K+K(A+2K)+(A+B)+exp(2)A, where K is the unchanged energyLinearCenteringK(M,T)=1+4A, A=energyLinearVarianceA(M,T)=energyE1Constant(T)M, and B=energyLinearVarianceB(M,T,K)=exp(2)K(A+6). The full Hvar/Hcenter formula is preserved by definitional equality. M,T are fixed before ν,h,s; no h- or θ-dependent choice of a constant occurs.

The transparent predicate energyE2Conclusion is only a conclusion. For one actual θ it returns actual m(θ)=0, actual μ_θ probability, ae closed support, genuine id/square/absolute-cube integrability, exact actual integral mean0 and all four common-C2 inequalities: |θ|≤C2/h², |log L(θ)|≤C2/h⁴, |∫x²dμ_θ−1|≤C2/h, ∫|x|³dμ_θ≤C2. The same actual μ_θ is energyLinearTiltLaw ν h s θ, using the existing μ and exp(θx)/L(θ) density. No law or moment is replaced by an abstract input.

The common theorem retains ν probability, original square/cube genuine integrability, original second1/mean0, actual β≤M, M,T≥0, h≥H2 and |s|≤T. Original id integrability is supplied internally by the fixed moment/E1 chain. Probability, actual integrability, L>0, continuity, derivatives and variance-window bounds are supplied from the prior leaves and never assumed as new premises. No original bounded support, exponential/fourth moment,density,symmetry,nonlattice,centered μ or variance hypothesis is added.

## New log analysis and same-θ assembly

The elementary helper energyE2_abs_sub_zero_bound applies the genuine Lagrange theorem separately to positive and negative parameters, handling0 directly. Its derivative existence and continuity hypotheses are supplied internally in each actual application. For every mean-value point c the code explicitly checks |c|≤|t|, so all local derivative bounds are used only inside the certified parameter window. The generic helper makes no actual-law assumption and introduces no hypothesis into the final actual theorem.

For actual m, its all-real genuine centered-square derivative and continuity are supplied by the derivative leaf; the window theorem supplies |v(c)|≤2 when |c|≤K/h². Combined with actual m(0) and its E1 error, the first MVT proves |m(u)|≤(A+2K)/h² throughout the closed window. It does not transfer original ν mean0 to μ.

For actual log L, the genuine derivative m and continuity are supplied by the derivative leaf and L>0 by the first law. L(0)=1 gives log L(0)=0. The second MVT gives exactly |log L(t)|≤K(A+2K)/h⁴ for all |t|≤K/h², including negative and0 parameters. No unproved logarithmic integral identity, differentiation/interchange or formal derivative is used. The frozen coefficient including2K² is unchanged.

The common theorem obtains one θ and all true-law conclusions from the fifth leaf, then uses this very θ for every bound. It uses actual window q-error A/h+B/h²≤(A+B)/h, since h≥2, and actual normalized cubic comparison r_θ≤D²r≤exp(2)A. The explicit domination theorem covers K,K(A+2K),A+B and exp(2)A by the single exact C2. The fixed-law theorem substitutes M=actual β, with β≥0 supplied by its nonnegative integrand and β≤M by reflexivity. It adds no β≥1 or other new premise.

All zero/sign/weak-boundary/atomic cases are retained: T=0,s=0,t=0,θ=0,h=H2,closed parameter-window endpoints and arbitrary closed cutoff atoms. No new M≥1 is imposed on a possibly empty class with small M. All division is by h,h²,h⁴ with internally h≥2, or by already internally positive L. No θ uniqueness,selector,relative-path asymptotic or E3/E4/K/Kv/random-denominator/complete-root statement is claimed.

This unit covers the frozen finite one-dimensional E2 interface at the author mechanical level. E2 final certification remains pending independent final and lead gates; any later finite-E2 acceptance still does not close E3/E4 or the complete OQ4 roots, and main integration remains the root's separate responsibility.

## Isolated scratch and canonical release

The author initially operated only in own repro_outputs/oq4-energy-e2 scratch while the other author held the canonical snapshot window. Scratch02 full32 old imports+exact body and scratchTarget01 minimal-import no-o checks both passed with0-byte logs. During that phase no canonical target or olean was created; scratch-check.ps1 contains an explicit Emit guard. The frozen41b source and proof were preserved while waiting for parent explicit CANONICAL-WRITE-CLEAR.

Parent released the canonical window only after PR62 published the frozen Centering+EnergyPathLaw base. Actual baseline: feat/oq4-energy-e2-complete HEAD69d44c430ba5b2b9a9f3e7c3bf8d4607118465ef. The author read only the release metadata and imported EnergyPathLaw for coexistence; it is not a mathematical dependency and its implementation/proof/review was not read. Its accepted source hash is3336b977fbe88ae4c27ff7531ffeec6e14c71508587ac2abae99bf475757a177. The mathematical target still imports only EnergyLinearTiltCentering.

Before canonical writing, author-baseline.json captured and verified all33 accepted OQ4 source hashes, all32 Basic/Probability source hashes and Shao.lean,lake-manifest.json,lean-toolchain hashes; the target was absent. Final checks verified old33 hashes unchanged, the complete common path set and32 hashes unchanged, all three root/version hashes unchanged, and actual OQ4 source files exactly the old33 plus this one new target. Full curated hash maps remain in summary.json. No Git command,common/root/manifest/cache/lock change or another owner's file modification occurred.

## Actual server gates and audits

Every Lean check ran only on the designated server, after activation and changing back to this worktree, with taskset -c 0-3 and at most one author process. No old target/olean was rebuilt. This version's new olean was emitted exactly once, by its sole author. Toolchain `leanprover/lean4:v4.36.0-rc1`, mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. No missing cache/install/download occurred.

| Check | Exit | Full server-only record |
|---|---:|---|
| Necessary new33-old-imports+exactsourcebody coexistence | 0 | repro_outputs/oq4-energy-e2/coexist33.log and .exit |
| Canonical target no-o | 0 | repro_outputs/oq4-energy-e2/target01.log and .exit |
| Author-only unique olean emission | 0 | repro_outputs/oq4-energy-e2/olean.log and .exit |
| Exact fullsource audit: every getModuleIdxFor?=none declaration | 0 | repro_outputs/oq4-energy-e2/source-audit.log and .exit |
| Actual34imports audit: every module-owned declaration, full signature and transitive axioms | 0 | repro_outputs/oq4-energy-e2/audit.log and .exit |

The first three successful compilation logs are0bytes. Coexistence source body equals the exact final source with only its import lines removed, appended to all33 accepted imports. The scratch32 helper is retained separately as CoexistSource.scratch32.lean; the frozen scratch02 source snapshot is byte-identical to the final canonical source.

Both source-none and module-owner audits found exactly10 new constants=9 explicit (3 definitions+6 theorems)+1 generated helper. All10 source/owner names and all10 transitive axiom records match exactly, without namespace/name-root/private/generated filtering. All10 full actual signatures are recorded.9 use {propext,Classical.choice,Quot.sound},1 only {propext}; no unexpected axiom or banned source token. Complete declarations/types/axioms are in declarations.md and summary.json. Rawlogs/olean/binaries remain exclusively on the server.

## Preserved API history

The first scratch check failed on inference of a multiplication scalar/nonnegativity proof and the orientation of add_le_add_left/right. The repair provided an explicit typed scalar nonnegativity and explicit add_le_add components. The second scratch passed; no mathematical premise,constant,proof or conclusion changed. Both local source snapshots and full server-only scratch logs/exit files are retained. After freezing41b, every canonical-release check passed with unchanged bytes; no old scratch target was unnecessarily repeated.

## Reproduction

```sh
set -e
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean repro_outputs/oq4-energy-e2/CoexistSource.lean
taskset -c 0-3 lake env lean Shao/OQ4/EnergyE2Bounds.lean
# Author emission already completed once; reviewers use no-o source and actual imports.
# taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/EnergyE2Bounds.olean Shao/OQ4/EnergyE2Bounds.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-energy-e2/SourceAudit.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-energy-e2/Audit.lean
python3 repro_outputs/oq4-energy-e2/summarize.py
```

Local check/scratch-check,CoexistSource/SourceAudit/Audit,summarize/finalize helper sources retain the workflow. The summarizer validates encoding/hash/all exits, source-none/owner count/name/axiom equality, full signature collection, whitelist/source token restrictions and the frozen old/common/root hash maps. Only curated JSON,source/proof/receipt/ledger/checkpoint/helper/history source are copied locally.
