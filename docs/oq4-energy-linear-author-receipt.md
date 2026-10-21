# EnergyLinearTiltLaw author verification receipt

All author implementation and required mechanical checks passed. Statement gate was reported independently CORRECT by the lead. Independent mathematical/final proof/source review remains separate and pending; this receipt is not independent certification.

## Frozen artifacts

- Interface `drafts/oq4/frozen-energy-linear-tilt-law-v1.md`.
- Anonymous proof LinearLaw-v1, frozen SHA256 `a246e6290d2db021aa9ae0e667b2752392f64d5dfa90954c6a55c953c40887a0`.
- Server source `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/EnergyLinearTiltLaw.lean`.
- Final source SHA256 `63cf342dcbe3cce728a42b283a539b8a56043f74a23f6f888ef94df378dcde78` (10550bytes).
- Author-only unique olean SHA256 `f94542eed162d0205d9eaac859abb6933b2ccf915f55ab35c1628bb8b8d3df31`.
- Local final source `drafts/oq4/energy-linear/EnergyLinearTiltLaw.lean`.
- UTF-8 without BOM, LF only, one final LF. Final source/proof are frozen.

## Exact objects and scope

The six requested definitions are the actual energyLinearNormalizer, energyLinearFirstNumerator, energyLinearSecondNumerator, energyLinearThirdNumerator, energyLinearTiltLaw and energyLinearMean. They use the same fixed actual energyTiltedLaw ν h s throughout. Their parameters are only ν,h,s,t, with no T,M,K or θ. The law is an actual withDensity measure with ENNReal.ofReal(exp(tx)/L) density.

All real t are quantified with no smallness restriction. The genuine integrability of exp(tx), x exp(tx), x²exp(tx), |x|³exp(tx) is supplied by the actual μ-probability and μ-almost-everywhere closed support from N1. No globally pointwise bound on the real line, no original ν bounded support or exponential moment, is used. One auxiliary actual-μ lemma handles every finite natural absolute power uniformly, then supplies the four requested cases.

The normalizer bounds are exactly exp(-2h|t|)≤L≤exp(2h|t|), so L positivity is a conclusion. The constructed μ_t is proved a probability law with the same ae closed support. The real mass identity holds for each Borel set and the true Bochner change-of-measure theorem holds for every Borel real f with genuinely μ-integrable f exp(tx). The three actual tilted moments are proved genuinely integrable and equal the specified numerator quotients; the first also equals the actual function m(t).

The zero-parameter conclusions are L(0)=1, actual measure equality μ_0=μ, and m(0)=∫x dμ, whose integral is backed by the t=0 integrability case. No zero mean is claimed. At s=0 the underlying μ remains normalized closed energy truncation, generally different from ν. All zero/end-point atoms, h=1,T=0,s=0,t=0 and positive/negative t are retained.

The interfaces actually need only original square integrability/unit second moment, ν probability, T≥0,h≥1,|s|≤T, because N1 probability/support already hold under these. The unused original cubic condition is omitted as an explicit strengthening that covers the entire frozen domain. The lead was informed before and after implementation. No centering,M,K,variance,θ,original exponential moment or distributional support/density/symmetry condition was added.

This is only the first finite-law/interface leaf of E2. It proves no parameter derivatives, common positive variance interval, endpoint signs, selected θ, exact centering, h⁻⁴ log L estimate or final selected-θ moment bound. E2/E3/E4,K/Kv,random denominator and every complete OQ4 root remain OPEN.

## Server execution and checks

Every Lean check ran only on the designated server, after activation and changing back to the OQ4 worktree, with one author process and taskset -c 0-3. Only this new olean was emitted, exactly once. No old module target/olean rebuild or Git/common/root/manifest/audit/cache/lock change, install or package download occurred.

Parent-confirmed baseline: branch feat/oq4-energy-centering, HEAD2380a8e5798e848f3c9d644ff09e83a90194fd38. Parent reported all27 old OQ4 and32 old Basic/Probability source SHAs unchanged after accepting the v30 baseline; no source/olean mutation occurred during author checks. The author performed no Git operation.

Toolchain leanprover/lean4:v4.36.0-rc1; mathlib807d3836b165983210ee2ecf3cd28f239436949c. Canonical import is only the fixed actual EnergyTiltedLaw module.

| Check | Exit | Full server-only record |
|---|---:|---|
| Exact new source body after all27 prior OQ4 imports | 0 | `repro_outputs/oq4-energy-linear/coexist01.log`, `.exit` |
| Canonical new source target | 0 | `repro_outputs/oq4-energy-linear/target01.log`, `.exit` |
| Author-only unique olean emission | 0 | `repro_outputs/oq4-energy-linear/olean.log`, `.exit` |
| Actual28-module imports and owner-module complete transitive axiom audit | 0 | `repro_outputs/oq4-energy-linear/audit.log`, `.exit` |

Every first attempt passed, with 0-byte successful compilation logs and no diagnostics. No API/cache blocker or failed version occurred; the initial successful source snapshot is retained under history/.

The dynamic audit enumerates exact module ownership through getModuleIdxFor? and no name/namespace filter. It found **24 actual new constants=20 explicit (6 definitions+14 theorems)+4 generated**. Every actual transitive axiom record is in the standard whitelist:23 have {propext,Classical.choice,Quot.sound},1 only {propext}. No unexpected axioms or banned source tokens. Full names and axiom sets are in declarations.md and curated summary.json. Raw logs and binaries remain only on the server; local files are curated source/proof/receipt/declarations/summary/checkpoint/helper source and initial source snapshot.

## Reproduction

```sh
set -e
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean repro_outputs/oq4-energy-linear/CoexistSource.lean
taskset -c 0-3 lake env lean Shao/OQ4/EnergyLinearTiltLaw.lean
# Author emission already completed once; reviewers use source/no-o and actual imports.
# taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/EnergyLinearTiltLaw.olean Shao/OQ4/EnergyLinearTiltLaw.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-energy-linear/Audit.lean
python3 repro_outputs/oq4-energy-linear/summarize.py
```

The local check.ps1, CoexistSource.lean, Audit.lean and summarize.py retain the exact workflow. Audit imports all28 modules and selects all declarations belonging to this module, including every generated helper. The summarizer validates encoding, hashes, exits, all counts and axiom records, without creating local raw logs.
