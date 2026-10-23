# OQ3: actual open-domain standardization and local Legendre geometry

This milestone follows PR176 at exact parent `803d8d0fbea3c2a55b8167f7c1ff4902510f1b8e`. It adds eight OQ3 modules, 1129 source lines, ten public theorems and no public definitions. The full actual-module inventory has fourteen theorem owners, including four private helpers and no generated owners. Root alone integrates and merges.

| Module | Result and retained scope |
|---|---|
| OpenDomainAffineMoments | Genuine uniform natural Euclidean moments of the actual centered affine pushforward, from compact true-domain raw moments and an explicit matrix entry bound. |
| QuadraticWhiteningSpectralData | The literal positive symmetric covariance whitening, its two-sided frequency bounds and a uniform bound on every entry, proved from actual quadratic-form spectral bounds. |
| OpenDomainWhitenedFamily | Actual probability laws, zero means, identity covariance, natural moments and unchanged-exponent weak Cramer for the actual compact tilted family. Original actual uniform spectra and weak Cramer are retained. |
| OpenDomainRealMoments | Genuine integrability and uniform bounds for every nonnegative real radial power, including the original real 8+delta moment of the same actual whitened law. |
| OpenDomainCompactMeanChart | An actual mean inverse on a positive-radius moment neighborhood, with compact inverse image of its closed ball inside the true exponential-integrability interior. Inverse smoothness is stated at the center. |
| OpenDomainLegendre | Every genuine-domain global dual test is bounded by the actual interior tilt's value; the true EReal Legendre supremum is attained there and equals the finite expression on the actual compact inverse chart. |
| OpenDomainRateDerivatives | The actual local rate is smooth at its center, has gradient theta and inverse-actual-covariance Hessian, and equals the true global EReal rate throughout the chart target. |
| OpenDomainBoundaryRate | Along q=a^2/x^2, the actual rate has zero derivative at the saddle and second derivative Lambda1, including curvature 2*t0/x^2, with eventual equality to the true global EReal rate. |

The proofs use the actual normalized exponential tilt and genuine integrability, including before any integral comparison or covariance identity. The global Legendre proof compares all parameters in the true integrability domain, including its boundary, by Jensen under the actual tilted probability measure. Both rate Hessians use genuine neighborhood derivative identities; a derivative value at one point is never differentiated as though it were a neighborhood identity.

Every exact source version has a complete targeted server check and a whole actual-module-owner transitive axiom audit. The checks use Lean4.36.0-rc1, mathlib807d3836b165983210ee2ecf3cd28f239436949c, CPU14–17, native8192 MiB, four jobs, autoImplicit=false and one heavy command. All fourteen owners use only propext, Classical.choice and Quot.sound. Exact successful gates are reused; no old successful check or full dependency build was repeated. Failed complete attempts remain in their server evidence directories.

Independent source-to-statement/proof review covers every source line and every actual owner. The manifest binds each exact source, frozen declaration, printed actual type, historical author receipt, owner-audit source, environment and full independent report. Author receipts retain their creation-time pending-review status; the final manifest supplies acceptance of the exact source. The existing thin package overlay emits Lake's local-changes warning; relevant APIs were checked against pinned source, and no whole-cache-cleanliness claim is made.

The parent milestone's environment provenance remains at `../oq3-u22/u22e-environment-change.json` and `../oq3-u22/root-inverse-contdiff-cache-receipt.json`. Only lane-owned objects were added by symlink to the accepted source view. Shared cache, pins, common definitions and root imports were not changed.

OQ3 B and D remain OPEN. Original B retains its actual uniform spectral and weak-Cramer assumptions, beta<2/5, theta.2<0, positive Lambda1, fixed-x/global saddle geometry and explicit far-region probability bound. This milestone proves neither a general unbounded reference-law stability shortcut nor the local Taylor/lower-bound/amplitude estimates, Song Edgeworth engine, exact cell reconstruction/summation, boundary Laplace remainder or far-probability localization. Corrected fixed-x A and accepted bounded C scopes remain as previously accepted. No external theorem is introduced as an axiom.
