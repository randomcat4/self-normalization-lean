# Conditional ghost-square moments

`Shao.OQ6.ConditionalGhostSquareMoments` proves the conditional ghost-square input and independent coordinate-sum moment estimate used in p44, section 3. It consumes the qualified conditional residual envelope and heterogeneous stretched-exponential sum-moment producers.

For the actual conditioned probability law ν and its product ν × ν, the theorem uses W(z) = wstd(z₁) + wstd(z₂), Y(z) = W(z)², β = α/2, tauPair = tauStd/2^α, and Mpair = (2 Mexp)². For every 0 < α ≤ 2, it proves actual exponential integrability of Y^β and its integral bound by Mpair. The scale Cmom is fixed before the truncation level, interpolation parameter, sample size, and moment order. For every n, including zero, and real q ≥ 1, the actual independent product-law sum is integrable to order q and its moment root is bounded by Cmom (n + q^(1/β)).

The theorem retains the existing almost-everywhere bounds for the same standardized residual Kstd. Its proof establishes product-law integrability before using the product-integral identity; it assumes neither a free factorization identity nor a ghost-square moment bound.

The exact qualified source has SHA256 d0fad94a739902f5e9ac36f4c81df0485571e797914b51d7d7e17d2d233503ab. The original server object has SHA256 1ee93f593cadb2c5e03fc696902f9f0021494c2fd31e93073e8b4f2e0b5d2344. Native kernel and same-object all-owner audit both returned 0, with no errors, in 8.0905s and 5.3595s. Existing warnings and strict wrapper success=false are retained; no warning-cleanup compilation was performed. The module-index audit covered all 10 actual theorem owners, including 7 generated helpers, all 1024 lines of complete types, and recursive axiom dependencies. There are no non-theorem owners. All axioms are in propext, Classical.choice, Quot.sound.

The independent complete source/proof review, affected T01 review, final all-owner review, coverage map, and exact source/object qualification accompany this source. The original failed kernel attempt remains preserved at the server paths bound by those records. Successful evidence for unchanged producers and proof ranges is reused.

This result covers this conditional ghost-square input and coordinate-sum moment component only. It does not close the Hilbert sign estimate, random row tail, double-ghost symmetrization, scalar quadratic chaos, double-counting assembly, or the original C2/C12/OQ56 root theorem. The p54 repairs and external Shao–Zhou attribution remain unchanged. C2/C12/OQ56 remain OPEN; OQ3 remains PAUSED_BY_USER.
