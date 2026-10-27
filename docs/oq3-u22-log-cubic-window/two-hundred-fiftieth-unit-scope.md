# FM250 exact Gaussian oscillatory integral in one and two dimensions

The two complete declarations, with no statement lets, are frozen before
implementation. Prove actual complex integrability and the exact integral
for exp(-i x t) exp(-b t^2), then for the product-space kernel exp(-i x dot z)
exp(-b radius(z)^2), for every positive real b and all real x. The constants
are sqrt(pi/b) and pi/b respectively; the exponent is -radius(x)^2/(4b).

This supplies the zero-order normalization needed for the original report's
Gaussian/Hermite correction in lines 220–235, using exactly the negative
phase convention already frozen in FK248 and actual FL249. The one-dimensional
identity uses pinned mathlib's genuine complex Gaussian integral. The second
uses actual product integrability and the product integral identity, followed
by the positive real square-root square identity. No unproved density or
characteristic-function inversion premise is introduced.

The pinned Gaussian.FourierTransform and FourierTransformDeriv compiled
artifacts were observed present in the existing shared-v34 view; no new cache
write or old Lean gate is needed for intake. FJ247's separate missing polynomial
imports remain requested from root. FM has no dependency on unqualified FJ and
can advance independently while FL's full independent final review runs.

This result evaluates explicit Gaussian functions only. Actual full-plane
CF integrability, actual-law density, inversion, Hermite identification,
smoothing/desmoothing, exterior probabilities, B–D and OQ3 root stay OPEN.
Strict beta range, accepted counterexample, p54/v_corr and Song attribution
are preserved. All new exact-source kernel/all-owned recursive-axiom/type
receipts and an independent complete final review remain mandatory. Standard
three-axiom whitelist, no sorry/admit/new axiom/unsafe/native_decide, UTF-8 LF.
