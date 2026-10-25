# Double ghost sign invariance

This module proves the finite double ghost exchange mechanism used in p44(2). It is qualified for the exact source SHA256 `1e5a32ccdc30b8c70b7bc12add060392a0c90aa59d615d4d0e683c5ab1c34baf`, with original successful object `9bd9a88a805e8e2800733c41f932e4ffea67f6d3aa04ac2f1dfb4d86498a38fa`.

For a paired sample z=(x,y), `ghostMatrix` has literal zero diagonal and off-diagonal entries r(x_i,x_j)-r(y_i,x_j)-r(x_i,y_j)+r(y_i,y_j). A Boolean path keeps or exchanges each pair coordinate (true keeps, false exchanges). The corresponding signs satisfy D(T_s z)=diag(epsilon) D(z) diag(epsilon). `signLeft` is an isometry of the true Euclidean space, and the whole row action obeys the resulting vector and norm identities.

For every measurable space and probability measure nu, the actual finite paired product law (nu.prod nu)^n is preserved by this coordinate swap. Given only nu-a.e. nonnegative w and the original (nu.prod nu)-a.e. kernel envelope, the module proves the actual paired-law-a.e. matrix envelope using all four distinct-coordinate joint laws. This step does not assume w or r measurable. Product measurability of r is added for the final measurable row-norm functions and equality of their actual pushforward measures.

No kernel symmetry or canonical-mean premise is needed for these particular exchange statements. No positivity of n, weights or energies is added; n=0/1, atomic measures, repeated observations and nonzero original kernel diagonals are allowed. There is no topology or standard-Borel requirement on the observation space.

The exact frozen interface consists of six definitions and eight theorems. The module-index audit discovers 19 actual owners: 13 theorems and six definitions, including five generated theorems. Its complete TYPE output has 310 lines and its six non-theorem FULLVALUE outputs have 45 lines. All recursive axioms lie in propext/Classical.choice/Quot.sound.

The server native check and same-object audit both returned actual Lean RC0 (5.096313s and 5.334194s). Source diagnostics are empty. Both strict wrappers remain false because the existing Lake mathlib-local-changes notice occupies 134 stderr bytes; FIRSTEMPTY=false. The manual author stop prohibits warning-cleanup recompilation. The original source version and its native01 RC1/no-object receipt remain archived.

The original complete source review, changed-proof review, final report, exact coverage and independent/parent qualification records accompany this module. Qualified185/186 source/object evidence is reused without rebuilding or re-reviewing their internal proofs.

This does not prove the canonical ghost mean, Jensen/Fubini or outer q-integrability, random row moment or tail estimates, scalar quadratic chaos, DC, or any root theorem. The next row-moment module must pay those dependencies explicitly. p54 repairs and the external attribution of Shao–Zhou inputs remain in force. C2/C12/OQ56 remain OPEN; OQ3 remains PAUSED_BY_USER.
