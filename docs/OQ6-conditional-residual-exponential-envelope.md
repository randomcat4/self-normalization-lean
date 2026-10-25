# Actual conditional residual exponential envelope

This component completes the stretched-exponential envelope transport used in p51 §6. It applies the already qualified true conditional projection carrier and uniform standardized residual interfaces to the actual conditional law. It does not close the original OQ5/OQ6 root theorem.

For the original envelope w, exponent α>0 and rate τ>0, define the deterministic scale aenv from the original second moment, wstd=aenv·w, tauStd=τ/aenv^α and Mexp=∫exp(τ w^α)dμ. The theorem chooses one N0 before the cutoff R and interpolation parameter lam. For every R≥N0, the actual normalized restriction ν to {w≤R} is a probability law, and the theorem proves integrability, the exact restricted-integral identity and the bound ∫exp(tauStd·wstd^α)dν≤2Mexp. It retains the actual standardized canonical residual Kstd and its product/cutoff envelopes almost everywhere under ν⊗ν, uniformly in lam∈[0,1]. The inputs and quantifier order are frozen; no abstract exponential-moment payment is substituted for the actual integral.

The only repair after the first mathematical source review is a local proposition connecting Real.rpow notation to the real power notation consumed by Real.mul_rpow. It changes five proof lines, with all frozen types/data, assumptions and the rest of the source preserved. The same independent reviewer completed the original source-to-statement/proof review, reviewed the exact affected scope and then read all actual owner metadata and types from the final imported object.

## Exact verified version

- Module: `Shao.OQ6.ConditionalResidualExponentialEnvelope`.
- Source SHA256: `c24bb3330f4fb6c384941596f434ef8839af04e9fdb91ce5780081e8dd7168bf` (21,227 bytes, 398 LF).
- Independent qualification SHA256: `dcbbd4cdf198f6f11dc4fcbd5b98167c580d594fb2f02f4d931fbc5a5ded7116`.
- Parent qualification SHA256: `48fb70c715211b92ea0b9143835736fd8344164024b43a16dce2c5f8efe16962`.
- Native kernel03: exit 0 in 8.91123559884727 seconds; source/object preservation and Git binding retained.
- Same-object import-only owner audit01: exit 0 in 5.300258511677384 seconds, without producing a new object.
- Object SHA256: `e4843dc11442aa69ca40bd3b5236e697238c7bb327594af2652821e1dfe8ddc7`.
- Actual module-index inventory: 8 theorem owners (1 public source theorem and 7 generated simplification theorems), 0 non-theorem values. All 607 TYPE lines were read independently. Every recursive axiom list is within `propext`, `Classical.choice`, `Quot.sound`; occurrences are 8, 2 and 2 respectively.
- Kernel receipt SHA256: `c6dc793466a954d68c43041d2882ee4a21b1c4b07d6d0b00a3c34bf1924907b8`.
- Audit receipt SHA256: `98cb320334cefe10252f90b53e819872984f5777ee476835e5029b487fe079f8`.

The strict runner reports success=false and outer exit 1 because it preserves existing Lake and style/unused/unreachable warnings. Both native Lean invocations returned 0. No clean-diagnostic claim or warning-cleanup recompile is made. The earlier environment exit127 (no Lean started) and original-source exit1 are archived; neither is treated as a proof pass.

The tracked review documents and qualification files bind the full local/server evidence. All Lean work ran on the pinned server toolchain `leanprover/lean4:v4.36.0-rc1` and mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. Existing qualified producer checks and complete proof reviews are reused by exact hash.

The remaining source-bound work includes the p44 moment/concentration and symmetrization engines, actual large-remainder payment, strict source budgets, relative probability/Mills-ratio engines and original root closure. The p54 polynomial p-moment rate previously rejected by counterexample is not reinstated. C2/C12/OQ56 remain OPEN; OQ3 remains PAUSED_BY_USER. This PR is for review and Root integration; the lane does not merge it.
