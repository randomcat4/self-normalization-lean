# Global Rademacher scalar coefficient and log-cosine bounds

STATUS: LEAN_FULLY_CHECKED_SCA0_SCA1_SCA2
SPECTRUM_STATUS: OPEN
OQ4_ROOT_STATUS: OPEN
MAIN_INTEGRATION_STATUS: PENDING_ROOT

For every natural m>=1, with H=m+1, u=pi/(4H), z=pi/(2H), a=H^(-1)*cos(u)/sin(u) and rho=cos(z), this proves all frozen SCA0 legality conditions and the two absolute quantitative bounds

  |a-4/pi| <= (pi/3)/H^2,
  |log(rho)+(pi^2/8)/H^2| <= (pi^4/48)/H^4.

The positive constants are fixed before all m. The bundled existential theorem preserves that order. All m including1 and2 are covered, without a sufficiently-large threshold, free H, Taylor-error premise, time or probability hypothesis. The positive trigonometric denominators and logarithm arguments are established from the fixed domain. The transparent z and rho definitions are identified with the certified RademacherCosine definitions. Elementary derivative and monotonicity arguments establish the required remainder bounds.

This is an explicitly proved all-m auxiliary quantitative extension of the original asymptotic expansions. It depends only on certified Cosine definitions and real analysis; finite S1, spectral pairing, uniform tails and Brownian inputs are not premises. It does not establish their probability applications. C_log and C_tan are later derived requirements, outside this frozen scalar scope.

All59 source-owned declarations are audited:21 explicit public theorems,8 public definitions,9 private theorems and21 generated declarations. All9 raw names outside the direct target prefix are private wrappers for the intended namespace; no declaration is filtered out. The actual full43 union is990, including108 definitions; all old931 constants/100 definitions and their owners remain exact. New instances are zero. Full raw names, kinds, universes, complete Expr types, definition bodies, axioms and corresponding instance domains are independently compared. Only propext, Classical.choice and Quot.sound occur; raw logs, Expr, registries and binaries remain server-only.

S2-S5, probability comparison, Brownian, strict events, other cosets, full Spectrum and OQ4 remain OPEN. Shared definitions/imports/pins/cache and main integration belong to the root coordinator.
