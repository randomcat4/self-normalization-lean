# EnergyLinearTiltCentering author verification receipt

Author implementation and all required mechanical server gates passed. The lead reported independent statement and anonymous mathematical CORRECT. Independent final source/formal certification remains separate and pending; this receipt does not self-certify it.

## Frozen artifacts

- Interface drafts/oq4/frozen-energy-linear-centering-existence-v1.md.
- Anonymous proof SHA256 `05899c370b22a54c329908fb748f2ab3059b156e6716a049ae0b34b37b13c559`, unchanged from its proof-only freeze.
- Server source `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/EnergyLinearTiltCentering.lean`.
- Final source SHA256 `82f48c2123d499eed5a7ac8974ff7d51d18e09987539f8323dece141e08bbe16`, 7357bytes.
- Author-only unique olean SHA256 `62dcead50c1fb8ff8d09acf6b4e4b428ad66bf89229cbfec0ecce480556ac3b9`.
- Local final source drafts/oq4/energy-linear-centering/EnergyLinearTiltCentering.lean.
- UTF-8 without BOM, LF only, exactly one final LF. Final source/proof immutable.

## Actual objects and exact scope

Two transparent definitions introduce exactly K(M,T)=1+4energyLinearVarianceA(M,T) and Hcenter(M,T)=energyLinearVarianceThreshold(M,T,K(M,T)), retaining the entire fixed Hvar expression. P remains the existing energyE1Constant(T), and A=P M. M,T≥0, thus K>0, are fixed before every actual ν,h,s; K is not chosen depending on h.

The full actual ν probability/original genuine square and absolute-cube integrability/unitsecond/mean0/actual β≤M hypotheses are retained. For every h≥Hcenter and |s|≤T, the actual family m,L,μ_t is unchanged. No abstract law, endpoint sign, tilted centering, continuity, differentiability or variance lower bound is assumed as a premise. Original id integrability comes from the fixed moment/E1 chain.

The positive-height theorem internally gives K>0,h≥energyLogThreshold(M,T),h≥2 and a=K/h²>0. The initial-mean theorem separately supplies the true equality m(0)=∫x dμ and the actual E1 error |∫x dμ|≤A/h². The original ν mean0 is used for E1, not transferred as μ mean0.

The interval-growth theorem invokes the actual Mathlib Lagrange theorem `exists_hasDerivAt_eq_slope`. Continuity on each compact [x,y] is supplied by the certified actual all-real family theorem. For every u∈(x,y) it explicitly derives |u|≤K/h² from the interval endpoint hypotheses and then calls the actual common variance-window theorem. This supplies the genuine HasDerivAt m v(u) and v(u)≥1/2. At the returned mean-value point the positive denominator y−x gives (y−x)/2≤m(y)−m(x). No derivative assumption or bound outside the closed window is introduced.

Applying that comparison to [0,a] and [−a,0], and using the actual initial error, proves strict endpoint signs m(−a)<0<m(a). The explicit margin is a/2−A/h²=(1/2+A)/h²>0, including A=0. The existence theorem invokes `intermediate_value_Icc` on actual continuous m and the strict signs; it returns a real θ with |θ|≤K/h² and actual m(θ)=0.

The law theorem uses that same θ and the unchanged actual μ_θ=energyLinearTiltLaw ν h s θ, whose density is exp(θx)/L(θ) under the fixed actual μ. It calls the certified first-law interfaces to return actual probability, ae closed support |x|≤2h, true id/square/absolute-cube integrability, and the exact actual moment identity ∫x dμ_θ=m(θ)=0. It does not construct or substitute another centered measure.

All weak/zero/atomic cases are retained: h=Hcenter, T=0,s=0, θ=0 and arbitrary original/closed-cutoff atoms. No extra M≥1 is added when the admissible class may be empty. A=0 is safe because K≥1, and all new division is only by internally positive h² or the supplied internally positive L. No original ν support/exponential/fourth moment,density,symmetry or nonlattice condition is introduced.

This is only strict endpoint sign, zero-parameter existence/range and the corresponding true centered law. There is no uniqueness, measurable/continuous selector, global monotonicity claim, selected-θ h⁻⁴ log estimate or final common second/third moment bound. Complete E2,E3,E4,K/Kv,random denominator and every complete OQ4 root remain OPEN.

## Server gates and coexistence

Parent-confirmed baseline feat/oq4-centering-and-path HEAD1695839731c586cbeb34f157f9aec2246ec00c7a, the frozen PR57 head. All31 old sources/oleans/proofs remained fixed. Before final imports, the lead explicitly confirmed E3 was still proof-only with no EnergyPathLaw source or olean, and the formal list was exactly31 old modules plus this Centering module. Therefore final32-module audit covers the complete then-frozen list, without assuming an unimplemented E3 target.

Every Lean check ran only on the designated server after activation and changing back to this worktree, taskset -c 0-3 and at most one author process. The author uniquely emitted this new olean exactly once; no old target/olean was rebuilt. No Git/common/root/manifest/shared-cache/lock or another owner's file was changed; no download/install occurred.

Toolchain `leanprover/lean4:v4.36.0-rc1`, mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. Canonical imports are the fixed EnergyLinearTiltVarianceWindow plus cached Mathlib.Analysis.Calculus.Deriv.MeanValue and Mathlib.Topology.Order.IntermediateValue. Their exact source interfaces and existing cache were inspected read-only. No missing cache/API blocker occurred.

| Check | Exit | Full server-only record |
|---|---:|---|
| Exact new source body after all31 old imports | 0 | repro_outputs/oq4-energy-linear-centering/coexist01.log and .exit |
| Canonical new source target | 0 | repro_outputs/oq4-energy-linear-centering/target01.log and .exit |
| Author-only unique olean emission | 0 | repro_outputs/oq4-energy-linear-centering/olean.log and .exit |
| Actual32 imports, complete owner signatures and transitive axioms | 0 | repro_outputs/oq4-energy-linear-centering/audit.log and .exit |

Every first attempt passed. All three compilation logs are0bytes, with no diagnostics. There is no failed API history in this unit; the initial successful source snapshot is retained under history/. Local source-body equivalence to the exact final body after deleting only imports, appended to all31 old imports, was asserted; the history snapshot is byte-identical to final source.

The owner-index audit found10 actual new constants=9 explicit (2 definitions+7 theorems)+1 generated helper, without namespace/name-root filtering. Every10 full actual signatures and10 transitive axiom records was collected.9 use {propext,Classical.choice,Quot.sound},1 only {propext}, with no unexpected axiom or banned source token. Complete signatures and axiom records are in declarations.md and summary.json. Rawlogs/olean/binaries remain only on the server.

## Reproduction

```sh
set -e
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean repro_outputs/oq4-energy-linear-centering/CoexistSource.lean
taskset -c 0-3 lake env lean Shao/OQ4/EnergyLinearTiltCentering.lean
# Author emission already completed once; reviewers use no-o source and actual imports.
# taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/EnergyLinearTiltCentering.olean Shao/OQ4/EnergyLinearTiltCentering.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-energy-linear-centering/Audit.lean
python3 repro_outputs/oq4-energy-linear-centering/summarize.py
```

Local check.ps1,CoexistSource.lean,Audit.lean,summarize.py retain the workflow. The summarizer checks exact source/olean hashes, encoding, all exits/counts, owned-name/signature/axiom record equality, whitelist and source-token restrictions. Local files are curated source/proof/receipt/ledger/summary/checkpoint/helper source plus the initial successful source snapshot, without rawlogs or binaries.
