# OQ4 R0: global third-moment trigonometric coefficient bounds

Source: shao@35d4580, `oq4/b01/proof01.md` Section 6 (R0), SHA256 `7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38`.

For an arbitrary centered real random variable of variance one with a finite third absolute moment β, this module proves the ordinary one-step cosine and sine coefficient errors at every real frequency a are at most |a|³β/6. At a=π/(2h), for every h>0, it gives the exact remainder π³β/(48h³) around 1−π²/(8h²), together with the same bound for the sine coefficient.

The proof covers negative, zero and arbitrarily large frequencies. The probability law may have atoms and unbounded support. First, second and third moment integrability are explicit; no fourth moment, symmetry, density, non-lattice condition or exponential moment is introduced. Global scalar bounds and the integrability of the trigonometric residuals are proved before taking expectations.

This closes the frozen R0 ordinary coefficient estimate. Positivity of the coefficient for large h, its normalized powers, the actual killed-cosine residual R1–R2, the averaged residual R3, long-time K/Kv, the Brownian factor 4/π, and all random-denominator E1–E6 conclusions remain separate obligations. No free coefficient is asserted to be a killed-kernel eigenvalue.

Validation uses only the designated server and the pinned Lean 4.36.0-rc1 / mathlib 807d3836. The coordinator supplied the required Trigonometric.Bounds cache; the lane did not write shared caches or locks. The four public declarations and all eleven new constants, including generated declarations, are checked under the axiom whitelist propext, Classical.choice, Quot.sound. `verification/oq4-cosine/Audit.lean` independently checks the explicit public list and every imported `Shao.OQ4` constant. See its receipt for hashes and actual commands.

The statement translator did not read the author implementation or proof. The independent mathematical review and final formal review are separate from author checks. This is source-bound formalization without a novelty or priority claim. This follow-up depends on the base work already submitted in PR #4, but does not alter its existing source files or public interfaces. Root imports and the shared manifest remain the coordinator's responsibility.
