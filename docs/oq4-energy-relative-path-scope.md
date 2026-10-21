# Same-theta finite multiplicative energy path bounds

STATUS: LEAN_FULLY_CHECKED_FINITE_RELATIVE_PATH_BOUNDS
ROOT_STATUS: OPEN
E3_STATUS: OPEN

This leaf realizes the finite relative comparison underlying oq4/energy01.md equations(7)-(8), source snapshot35d4580b61e22e7145f47730045a09874ef93259 and document SHA2562e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6.

Fix M,T>=0, P=energyE1Constant(T), C=energyE2Constant(M,T), H=energyE2Threshold(M,T). For every original real probability nu with genuine square/cube integrability, mean0, second1 and actual third absolute moment beta<=M, h>=H and |s|<=T, the entry point internally chooses one actual E2 centering theta before every path length n. It returns that same theta's complete E2Conclusion and, for all n including0, genuine integrability and three comparisons on the same actual closed absolute-partial-sum event.

Writing p for the energy-tilted law's survival probability, r for the same theta's centered law survival probability, L for its actual linear normalizer, and I for the original nu energy-weighted path integral, the bounds are

exp(-C/h)*L^n*r <= p <= exp(C/h)*L^n*r,
exp(-e2)*r <= p <= exp(e2)*r,
exp(-e)*r <= I <= exp(e)*r,

with nonnegative e2=C/h+C*n/h^4 and e=P*M*n/h^3+e2. True positive L and Z justify their logarithmic exponent identities; the original energy normalizer error pays P*M*n/h^3. No finite factor is silently set to1. No probability is divided out, so zero survival mass remains covered. The endpoint bound is |S_n|<=h on the same closed event, without shifting by cumulative drift.

Real iid versions transfer the original integral and both laws' survival events through the exact finite joint-law map, including three different probability spaces. Theta is chosen before all n and sample families. Each row uses its own measurable independent coordinates with the specified actual marginal; no new coupling or cross-space independence is imposed.

There are6 explicit public theorems and4 definitions. Definitions, private and generated helpers are audited as actual module-owned declarations and are excluded from the public theorem count. The actual final owned count and complete signatures are recorded in declarations.md and the independent review.

All signs s/theta, n=0, closed/truncation boundary atoms, s=0, T=0, h=H, all-zero paths and zero survival masses remain included. There is no new support, exponential/fourth moment, symmetry, density, nonlattice or survival positivity premise. The original law is retained.

This leaf is finite. Joint h->infinity,n/h^3->0, shared two-variable operators(9)-(10), K/Kv,E4,random-denominator layers and complete E3/OQ4 root remain OPEN. The subsequent JointTransport statement has its own source review and separate gates. No shared source, root imports, manifests, toolchain or cache is changed.
