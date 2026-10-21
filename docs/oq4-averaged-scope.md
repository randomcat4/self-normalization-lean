# OQ4 conditional analytic averaged-residual payment

Source: shao@35d4580, `oq4/b01/proof01.md` Section 6 (R2/R3/R5/R6), SHA256 `7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38`.

The module combines the proved one-step killed-cosine residual bound, finite occupation-layer integral payment and cubic overshoot payment. For a centered unit-variance increment probability law with integrable first, second and third absolute moments, a finite endpoint measure of mass at most one, almost-everywhere closed-strip support and an explicit layer-mass bound `(C/h^2)(j+1)`, it proves absolute-residual integrability and the two frozen v2 bounds

`integral |r| <= (pi^3 beta/48 + 2 pi C (integral |y| + beta))/h^3`

and

`integral |r| <= (pi^3 beta/48 + 2 pi C (1 + 2 beta))/h^3`.

Parameter-integral measurability, actual integrability on both increment and endpoint measures, the endpoint mass factor and the finite integer top layer are proved. Atoms, boundary endpoints, arbitrary increment jumps and the zero endpoint measure are retained. No density, fourth moment or bounded-increment hypothesis is introduced.

This is a conditional analytic reduction. It does not instantiate the endpoint measure as an actual killed random-walk law or prove its O0 layer-mass estimate. The uniform constant is `C_{M,C}` when beta is bounded by M and C is fixed; it becomes a source-style `C_M` only after O0 supplies C=C(M). The historical v1 contract and failed constant-dependence review are preserved, with the minimal v2 correction and an explicit rounds record. Neither the exact inequalities nor the mathematical assumptions changed during that correction.

Five public theorems and all eight new constants passed author and independent server checks. The lead additionally checks the target without producing its olean and audits every imported Shao.OQ4 constant transitively, allowing only propext, Classical.choice and Quot.sound. The receipt records the actual audit count, hashes and commands. All Lean checks run on the designated server with the pinned toolchain and read-only shared cache.

Actual source R3, O0, R4, Brownian inputs, long-time K/Kv, E1-E6 and OQ4 remain OPEN.

The feature branch starts at `6018d26b11e0a89dc9189752c2acbdd75a29ab9c` (PR #9, following PR #7 and #8). The coordinator's latest announced main is `7a6ba6438136630ac0ca46b1fbda0d6eaa773827`; it has not been fetched into this checkout after two bounded fetch failures. This branch changes no common root import, shared manifest, shared audit script, definition or version lock. Integration must preserve the coordinator's newer common versions.
