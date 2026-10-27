# GB265 — Gaussian-damped actual probability characteristic function

This source-bound unit uses an arbitrary probability measure nu on the real
plane and its literal integral characteristic function, with the positive
frequency sign exp(i z dot w). No density, global undamped CF integrability,
moment, nonlattice or weak-Cramer hypothesis is introduced.

Freeze two complete declarations and both full Phi lets before implementation.
The first result gives actual strong measurability and the probability norm
bound at every frequency. The second gives genuine full-plane integrability
of exp(-i x dot z) Phi(z) exp(-b |z|^2), b>0, and its exact Gaussian-kernel
mixture formula with constant pi/b and exponent -|x-w|^2/(4b). The argument
must establish true joint product integrability before changing integral order.
It consumes the qualified FM250 Gaussian oscillatory integral and pinned
mathlib measure/Bochner/Fubini APIs. No unqualified old unit is imported.

This is an explicit Gaussian-smoothing method interface for the existing
normalized IID law, not a density claim for the original measure. For the
conventional inverse transform, division by (2*pi)^2 will give the kernel
normalization 1/(4*pi*b). A later unit must prove its genuine density law,
actual canonical use, uniform approximation, coupling and desmoothing.
All original B-D/exterior/positive-root obligations stay OPEN. Keep strict
beta<2/5, accepted joint-nonlattice counterexample, the p54/v_corr repair and
corrected Song uniform-in-law attribution. No original assumption changes.

All Lean and recursive-axiom checks run only on the designated server under
phase40 OQ3 CPU36-39,44-47/c12-heavy.lock/native -M8192 -j4. No successful
old native or leaf audit is replayed; first objects and failures are retained.
Final acceptance requires one separate complete independent review plus exact
same-first-object all-owned TYPE/VALUE/transitive-axiom receipt.
