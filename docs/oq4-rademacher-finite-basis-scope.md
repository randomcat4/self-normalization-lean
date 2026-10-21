# Complete finite sine basis for the actual Rademacher killed kernel

STATUS: LEAN_FULLY_CHECKED_FINITE_BASIS_B0_B3
SPECTRUM_STATUS: OPEN
OQ4_ROOT_STATUS: OPEN
MAIN_INTEGRATION_STATUS: PENDING_ROOT

For m>=1, H=m+1, integer states I=[-m,m] and modes J=[1,2m+1], this module constructs the actual sine family sin(j*pi*(w+H)/(2H)). Its first mode is the existing principal cosine on the whole real line. The complete family is orthogonal under the unnormalized counting sum with squared norm exactly H. Every function F:Z→R is reconstructed on I with the explicit coefficient (1/H)sum F(s)v_j(s), with no measurability, boundedness or support restriction on F outside I.

For all m<=h<m+1 and every legal integer start, each mode is genuinely integrable under the actual killedKernel of the fixed half-Dirac Rademacher law, and its actual one-step integral is cos(j*pi/(2H))*v_j(r). The full range includes zero and negative eigenvalues. Weak h=m boundary atoms are retained and exit mass is lost at the actual absorbing lattice points +/-(m+1); rows are not renormalized and the kernel is not replaced by a new matrix.

Nine explicit public theorems, seven public definitions, twenty explicit private declarations (three definitions/seventeen theorems) and forty-three generated theorems give seventy-nine actual owned constants (ten definitions/sixty-nine theorems). Registered new instances0. Source/import comparison covers all raw names, kinds, universes, full Expr types, axioms, all ten definition bodies and instance flags, including private/generated/outside-namespace declarations. Only propext, Classical.choice and Quot.sound occur. Independent fullsource/target/import checks and lead actual imports pass; raw logs/binaries remain server-only.

This closes B0–B3 only. All-mode finite powers, raw unweighted survival expansion, finite cot identities, explicit S1, S2–S4, low-threshold branch, other cosets, strict events and complete Spectrum/OQ4 remain OPEN. No source novelty claim is made. No common/root/import/version/cache file is manually changed; main integration remains root-owned.
