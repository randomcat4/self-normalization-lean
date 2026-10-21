# OQ4 R1–R2: exact one-step killed cosine and boundary overshoot

Source: shao@35d4580, `oq4/b01/proof01.md` Section 6 (R1–R2), SHA256 `7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38`.

The module defines the actual one-step integral of the cosine observable retained on the closed interval. It proves the exact identity subtracting the strict-exit integral from the ordinary cosine addition formula, for arbitrary real frequency, wall and starting point. For a positive wall and the principal cosine frequency, every exit is controlled by its full positive overshoot, including arbitrarily large jumps and atoms at the endpoints.

Under the original centered unit-variance finite-third-moment law, the module proves integrability of the overshoot and the precise source R2 bound: the sine contribution costs π³β/(48h³) and the exit contribution costs π/(2h) times the expected positive overshoot. It uses the already checked R0 coefficient theorem and introduces no fourth moment, density, bounded-support, non-lattice or symmetry hypothesis.

The boundary cosine is zero at both endpoints, but the residual need not be zero there. No pointwise relative residual bound is asserted or used. The free coefficient is not identified with an actual killed-kernel eigenvalue.

Validation is performed only on the designated server, with the pinned Lean 4.36.0-rc1 / mathlib 807d3836. Four public theorems, three definitions and two generated equations comprise the nine new constants. The lane audit additionally checks every imported `Shao.OQ4` constant (eleven from R0 and nine new), under the standard transitive axiom whitelist. Frozen source-to-statement review and an independent final proof/Lean review cover the exact final source hash.

The probability occupation estimate O0, its use to average the residual into R3, R4, the long-time normalization/initial and terminal Brownian steps, K/Kv and the E1–E6 random-denominator chain remain OPEN. This module supplies the one-step residual input, without supplying any long-time probability input. Root imports and the shared manifest remain the coordinator's responsibility. This is a source-bound formalization without a novelty claim; it follows the separately reviewed R0 module in PR #7.
