# Weighted third moments and the actual polygonal path

These two modules formalize the finite third-moment and interpolation estimates B2–B3 in `oq4/b01/proof01.md`, lines 239–255. The source argument concerns arbitrary centered real probability laws with an integrable third absolute moment. Neither module assumes a symmetric law, a bounded increment, a fourth moment, a density or a unit variance.

`WeightedThirdMomentB2` proves integrability of the cube of an arbitrary finite weighted sum under the actual product law. Under zero mean it proves

E|sum_i c_i Y_i|^3 <= 24 beta (sqrt(sum_i c_i^2))^3,

where beta=E|Y|^3. The coefficients may have either sign. The zero-dimensional sum, zero coefficients and zero third moment are covered. The proof uses actual independent copies, finite Rademacher signs and an explicit second/fourth moment argument for the sign average; it does not posit the desired moment inequality as an assumption.

`PolygonalThirdMomentB3` defines the actual path by the finite ramp expression

W(n,h,a,t)=sum_i max(0,min(1,t*h^2-i))*a_i/h.

It identifies this expression with prefix sums on grid times and with their affine interpolation on each grid interval. For h>0 and 0<=s<=t with t*h^2<=n, it proves integrability of |W(t)-W(s)|^3 and the bound

E|W(t)-W(s)|^3 <= 24 beta (sqrt(t-s))^3.

The increment coefficients are nonnegative, bounded by one before scaling, and their unscaled sum is (t-s)h^2 on the stated time interval. Their squared sum after scaling is therefore at most t-s, including intervals shorter than one grid step. The finite-path endpoint and the empty path are retained.

These are intermediate moment estimates. Finite-dimensional Gaussian limits for varying row laws, tightness of laws on continuous-path space, identification of the Brownian limit, killed-event continuity and the stopped-cosine identity remain separate source obligations. B0/B1, K/Kv and all general OQ4/Spectrum/energy root groups remain OPEN; this milestone adds no root leaf.

The source files preserve the exact UTF-8/LF bytes checked by the server and the independent final reviewers. Full actual-owned type and definition-value coverage includes private and generated declarations; transitive axiom dependencies are restricted to propext, Classical.choice and Quot.sound. Existing successful checks are reused. Only the B2 pure-source object needed by the actual B3 import is emitted once; objects, caches and raw logs remain on the server. The B3 source has no object emission at this milestone.

Pinned environment: Lean 4.36.0-rc1 and mathlib 807d3836b165983210ee2ecf3cd28f239436949c. Actual checks are server-only on CPU18–21 with -M8192 -j4, autoImplicit=false and debug.skipKernelTC=false, serialized by the lane flock. Root alone integrates and merges. Verification bindings are in repro_outputs/oq4-polygonal-moments/acceptance.json.
