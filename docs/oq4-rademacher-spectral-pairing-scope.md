# Exact signed finite Rademacher spectral pairing

STATUS: LEAN_FULLY_CHECKED_P1_P2
SPECTRUM_STATUS: OPEN
OQ4_ROOT_STATUS: OPEN
MAIN_INTEGRATION_STATUS: PENDING_ROOT

This proves the exact finite reflection pairing and positive principal-mode normalization of the certified finite S1 formula. For every natural m>=1, every real m<=h<m+1 and every natural n, including zero, the actual Rademacher killedMass and product-law closedStrip probability equal

  H^(-1) * sum_(2ell<m) (-1)^ell * (cot(alpha_ell)+epsilon*tan(alpha_ell)) * cos(beta_ell)^n + Z,

where H=m+1, alpha_ell=(2ell+1)pi/(4H), beta_ell=2alpha_ell, epsilon=(-1)^(n+m), and Z is the actual central zero-mode contribution, including 0^0 at n=0. Exact partition, reflection, parity and denominator conditions are proved. The first pair is a*rho^n*(1+epsilon*tan(delta)^2), with delta=pi/(4H), a=H^(-1)cot(delta), rho=cos(2delta)>0.

The remainder is the explicitly defined finite sum over the lower modes with ell=0 removed, plus Z/(a*rho^n). It is not an arbitrary error variable or hypothesis. Positive normalization gives the exact P2 probability and mass formula a*rho^n*(1+epsilon*tan(delta)^2+R). All natural times, negative reflected eigenvalues, the central zero mode, weak h=m, m=1/m=2 and empty-tail cases are retained. The n=0 normalization and the nonzero m=2 central contribution are checked separately. No large-time, sufficiently-large-height or tail-bound assumption is introduced.

All145 source-owned records are included:69 explicit public theorems,13 public definitions,2 private theorems and61 generated declarations. Both raw names outside the target prefix are private wrappers, with user namespace inside the target. Full source, actual direct import and full44 target records are compared in raw name, kind, universes, full Expr type, complete definition values, flags, axioms and corresponding registration states. The measured full44 union is1135 records and121 definitions. All old990 records and108 full definition values and owners remain exact in the full environment. New instances are zero.

Old killedAction.congr_simp has owner AllModes in the original S1 import scope and KernelRecurrence in the full old43 scope; every other field is identical. Corresponding-scope owner comparisons are exact and the full old owner is retained. No cross-scope owner equality is claimed. Complete scoped/private/inactive/erased/new/default registries and actual discrimination-tree paths and entry/child order are compared only in aligned import and lexical scopes.

The logical upstream is certified finite S1 PR98. Scalar PR104 is protected custody, not a Pair mathematical premise. Only propext, Classical.choice and Quot.sound occur. Raw logs, Expr, registries and binaries remain server-only. This is one original exact-pairing obligation; declaration counts are inventory, not additional original leaves. Uniform U1 tails, S2-S5 asymptotics, Brownian, strict events, other cosets, full Spectrum and the OQ4 root remain OPEN.
