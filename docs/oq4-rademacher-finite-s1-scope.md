# Exact finite zero-start Rademacher survival formula

STATUS: LEAN_FULLY_CHECKED_FINITE_S1_C1_C5
SPECTRUM_STATUS: OPEN
OQ4_ROOT_STATUS: OPEN
MAIN_INTEGRATION_STATUS: PENDING_ROOT

For every natural m>=1, real m<=h<m+1 and natural time n including zero, the actual closed-strip probability under the fixed half-Dirac Rademacher product law equals

  (1/(m+1)) * sum_{ell=0}^m (-1)^ell * cot((2ell+1)*pi/(4*(m+1)))
               * cos((2ell+1)*pi/(2*(m+1)))^n.

The same formula holds for the actual killedMass at start zero. Cotangent means cos/sin. The proof establishes v_j(0)=sin(j*pi/2), even-mode cancellation, odd-mode signs, the exact finite odd coefficient, all half-angle denominator conditions and the full odd-mode range bijection. Counting normalization stays 1/(m+1), with no inserted lattice weights. It derives the probability identity through the actual kernel/path bridge. Zero and negative eigenvalues and 0^0 are retained; no division by an eigenvalue or survival probability occurs. The zero-time trigonometric identity is included.

The separate low-height branch covers every real 0<=h<1 and all natural n: both killedMass and the actual closed-strip probability equal 1 at n=0 and 0 otherwise. It uses the genuine zero row at m=0 and the actual kernel semigroup, without asserting a nondegenerate sine basis at m=0. All weak integer endpoints h=m are retained.

Nineteen explicit public theorems, one public definition, eight explicit private theorems and forty generated declarations give all68 source-owned constants, including every generated/private declaration without namespace filtering. There are no generated names outside the target namespace and no new instances. Source/direct/full42 declaration sets and their actual intersection are audited; the old863 constants and99 definitions remain unchanged, and the actual full union is931. Full raw names, kinds, universes, Expr types, axioms, definition bodies and complete instance registries are compared in matching import scopes. Only propext, Classical.choice and Quot.sound are allowed. Raw logs, Expr, registries and binaries stay on the designated server.

This closes the finite S1 C1-C5 interface only. Signed spectral pairing, uniform tails, S2-S5 asymptotics, strict events, other cosets, full general-data/atomic spectrum and the OQ4 root remain OPEN. Shared source/import/pin/cache changes and main integration belong to the root coordinator.
