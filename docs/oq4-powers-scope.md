# OQ4 free-cosine coefficient positivity, inverse powers and logarithmic error

Source: shao@35d4580, `oq4/b01/proof01.md` Section 6 (R0), Section 8 (normalization factors and D4), and the final exponent replacement in Section 9, SHA256 `7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38`.

The module uses the actual free-step cosine coefficient, the certified cubic Taylor remainder, centered unit-variance integrable moments and a common third-moment bound beta<=M. Under the explicit sufficient threshold h>=1 and h>=pi(1+M), it proves the frozen quadratic bounds and 3/4<=rho<1. It proves the quantitative reciprocal-power bound, both floor(h^2) block bounds by exp(pi^2), and the displayed logarithmic error with constant pi^3 M/48+pi^4/8, including its N-multiple.

The coefficient is the ordinary expectation of cosine; it is not asserted to be a killed-kernel eigenvalue. No density, atomlessness, symmetry, bounded increment or fourth-moment assumption is introduced. All natural zero exponents and multipliers are covered. The final-goal theorems retain the complete threshold and moment premises; a stronger R0 remainder helper legitimately uses weaker premises.

Eleven explicit theorems comprise four real scalar helpers and seven actual-coefficient statements. Acceptance requires isolated statement/constant review, independent mathematics/final formal review, designated-server target checks and all-constant transitive axiom auditing. Only propext, Classical.choice and Quot.sound are allowed. Actual generated counts, exact source hashes and commands are in verification/oq4-powers/receipt.json; full logs stay on the server.

This supplies coefficient control needed for the conditional recursion and the final logarithmic substitution. It does not prove block probability estimates, B1, Brownian approximation, the 4/pi prefactor, K/Kv or OQ4.

The exact pre-module base is accepted-main merge `7b0648095d6ba3f0b1a89384005af21ce1fee5f0`, combining feature origin PR #15 at dfe239643bd0b58acec4d83a8b639919761f74d9 with main9da55787ce7decdf177b3eaa9ca714503aca544a. The merge had no conflicts and left every frozen OQ4 mathematical source hash unchanged. No manual edits were made to common definitions, root imports, manifests, audit scripts or locks.
