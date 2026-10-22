# Deterministic finite Rademacher lattice displacement

STATUS: LEAN_FULLY_CHECKED_DA1
SPECTRUM_STATUS: OPEN
OQ4_ROOT_STATUS: OPEN
MAIN_INTEGRATION_STATUS: PENDING_ROOT
NEW_RAW_LEAF_INCREMENT: 0

For every natural m>=1, every real weak cell m<=h<m+1, and every natural n including zero, put H=m+1, N=(n:Real), lambda=pi^2/8, delta=H-h and use the actual certified Scalar.a and Scalar.rho. There is one positive absolute C, fixed before all these parameters, such that

  |lambda*N/h^2 + N*log(rho) + log(pi*a/4)
      - (pi^2/4)*(N/h^3)*(H-h)| <= C*(N/h^4 + H^(-2)).

All denominators and logarithm arguments are proved legal. The normalized amplitude logarithm is bounded internally, with an explicit positive lower bound and C_log; it is not a free Taylor/error hypothesis. The reciprocal displacement identity and remainder bound retain delta=1 at the weak integer endpoint h=m. No asymptotic sequence, positive-time, probability or Brownian premise is introduced. This is the deterministic DA1 component, not the actual S4 probability conclusion.

The logical upstream is actual certified RademacherScalarBounds PR104, whose exact contents are accepted in main v31. RademacherSpectralPairing PR111 is protected custody only. All38 new records are included:9 explicit public theorems,4 definitions,7 private theorems and18 generated declarations. All22 raw names outside the target prefix are private wrappers, and every user name remains in the target namespace. Actual raw/raw, raw/user, user/raw and user/user intersections with old44 are empty. New instances are zero; only propext, Classical.choice and Quot.sound occur.

Complete source/current-module, actual direct import and full45 target fields are checked, including raw structured names, full universe parameters and Expr types, all4 full definition values, flags, axioms and actual owners. The measured full45 union has1173 records/125 definitions; all old1135 records/121 definition values and corresponding owners remain exact. Whole registration states, all scoped/private/inactive/erased/new/default domains and actual discrimination-tree paths, chains, entries and child order are compared only after closure, import order and lexical scope align. Empty target instance/default exports are independently verified before their sole module slot is removed.

The original private and canonical ledgers differ only in title and STATUS header; every byte after line3 is exact. The author's title_only_curated label refers to that cosmetic header change. Original private failures, metadata failures and transport recovery are retained without replaying successful checks or target emission. The author emits one target olean; the independent reviewer uses no-o and its own raw captures; the lead checks actual imports only. All137 source/config files and102 build files are protected. Raw Expr, registrations, logs and binaries stay server-only. No source, pin, cache, root import or shared definition is changed by publication.

This is derived assembly in the existing deterministic DA family, with original-leaf increment0. DA2, uniform U1, actual S2-S5 probabilities, Brownian, strict events, other cosets, full Spectrum and the OQ4 root remain OPEN.
