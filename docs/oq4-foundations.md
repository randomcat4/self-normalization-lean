# OQ4: finite delayed stability and third-moment boundary payment

## Result and source boundary

This milestone implements two source-bound inputs to the OQ4 deterministic-wall argument, from shao@35d4580, `oq4/b01/proof01.md` Sections 6 and 8. The complete OQ4 theorem, the deterministic-wall theorems K/Kv, Brownian limits and the random-denominator bridge E1–E6 remain OPEN.

`DelayedRecurrence.lean` proves the complete finite numerical recurrence frozen in `oq4-finite-contract.md`. It controls the survival sequence and the test-function oscillation by non-circular joint strong induction, including zero coefficients and short horizons. The probabilistic estimates supplying D2/D3, the initial Brownian limit B1, and the eventually-small coefficient are separate obligations.

`OvershootSum.lean` proves the pointwise finite bound

    sum_{j<L} (j+1) max(u-j,0) ≤ 4(u+u³), u≥0,

uniformly over every cutoff L, with zero and integer boundary values included. `OvershootMoment.lean` integrates it over a finite measure space and proves summability and the same bound for the entire series of expected cell payments. Only a first and third absolute moment are needed. In the intended probability application U=|Y|, the source second moment already supplies the first moment. No fourth moment, exponential moment, bounded support, density or non-lattice condition is added.

The closed-wall killing convention remains distinct from existing crossing≥ events. These modules do not implement killing, delete coordinates, or replace the true random denominator. The probability occupation input O0 and residual estimate R2 are still needed to obtain R3.

## Declarations and integration

The lane entrypoint is `Shao.OQ4.Foundations`. It imports eight public theorem declarations and their implementation definitions/generated declarations. Root import and shared manifest integration belong to the coordinator; this branch does not edit them.

- `delayed_recurrence_bound` closes frozen F-D.
- `overshootCell_nonneg`, `overshoot_sum_le_cubic` close frozen F-R.
- `integrable_overshootCell`, `integral_overshootCell_nonneg`, `sum_integral_overshootCell_le`, `summable_integral_overshootCell`, `tsum_integral_overshootCell_le` close the frozen R6 expectation interface.

`verification/oq4/Audit.lean` explicitly verifies all eight public names are present and are theorems. It also traverses every constant under `Shao.OQ4`, including generated constants, and rejects any transitive axiom outside propext, Classical.choice and Quot.sound. The scope is the imported lane entrypoint, not the four complete root groups.

## Validation and provenance

All Lean checks run on the designated Linux server with Lean 4.36.0-rc1 / mathlib 807d3836b165983210ee2ecf3cd28f239436949c. No local Lean build or cache change is involved. See `verification/oq4/receipt.json` for exact source hashes, commands and coverage.

An isolated statement translator read the mathematical source and frozen statements without reading implementation or proof drafts. An independent reviewer then read the frozen declarations and final anonymous proofs and checked their exact formal signatures. The reviews distinguish local acceptance from root completion. The finite recurrence was implemented by a separate author; the overshoot and integration proofs were implemented by the OQ4 lead. The lead did not certify its own proofs. This is source-proof formalization and a finite numerical proof reconstruction, not a novelty or priority claim.

Source `oq4/b01/proof01.md` SHA256:
`7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38`.

The new weak-boundary variance-scaling module is a subsequent separate work unit. It is not included in this milestone's accepted coverage.
