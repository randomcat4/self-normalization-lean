# Canonical product-envelope moments and strict tails

This module proves the finite-sample product-envelope branch in original p44(7)–(8), including the alpha=2/3 half-window. It consumes the qualified actual scalar and row moment interfaces from units190/188 and the stretched-exponential independent-sum interface from183.

Let nu be an actual probability measure on an arbitrary measurable space. The kernel r is product-measurable and integrable, with both marginal-AE canonical identities and the product-AE envelope |r(a,b)|<=w(a)w(b). Assume alpha in(0,2], tau>0, M>=1, w>=0 nu-AE, and actual integrability and expectation bound E exp(tau*w^alpha)<=M. Symmetry is explicit for original scalar F; the standalone row theorem does not require it. No measurable-w, topology on the sample space, pointwise canonicality, zero value-diagonal, distinct-observation, nonatomicity or kernel/envelope independence assumption is added.

A proof-local measurable representative of w is recovered from its actual exponential integrability. The paired square (v(a)+v(b))^2 has exponent alpha/2, rate tau/2^alpha, and exponential bound M^2. AE transport returns the actual paired energy for original w. With C=envelopeMomentScale(alpha,tau,M), the actual L1 and root moments are:
- paired energy at real p>=1: C*(n+p^(2/alpha));
- original scalar at real q>=2: 8*C*q*(n+q^(2/alpha));
- actual row norm at real q>=2: 2*sqrt(q)*C*(n+q^(2/alpha)).
The combined moment theorem uses the explicit common scale max(8*C,2*sqrt(2)*2^(2/alpha)*C) for scalar q and row2q.

For q>=2 and2*q<=n^(alpha/2), the actual strict scalar and row-squared events have probabilities <=exp(-q) and <=exp(-2*q), with scales CF=16*exp(1)*C and CL=32*exp(1)^2*C^2. Common CT=max(CF,CL) gives their probability sum <=2*exp(-q). For alpha=2/3, the window is exactly q<=n^(1/3)/2. Threshold atoms remain in the complement because events are strict. Zero-sample moments and impossible n=0/1 tail windows are handled without division by zero.

## Exact qualification

Accepted source SHA256: 3c51f9c5cb19f972b1d06a2725d7f98b98dfd19c47a4d99e05c162ffe537b89b (41789bytes,924LF).
Original server object SHA256: b4e5e8be0b1206b9e621d54fc8dedb5031087178ce8348071fc088ac2cbda015.
Native02 actual Lean exit0,0errors,21warnings retained; original-object module-index audit actual exit0 without recompiling. Strict wrappers remain false, FIRSTEMPTY=false, both134byte Lake stderr files preserved. Original native01 failure and v1/v2 parser-normalization provenance remain distinct.

The independent reviewer read the complete source, affected repair delta, all50 actual TYPEs(1912lines), all7 required FULLVALUEs(79lines). Actual ownership derives25source+25generated,43theorems+7definitions,22private names,0foreign/unmapped names, all bodies present. Recursive axioms are limited to propext, Classical.choice and Quot.sound; per-owner occurrences50/40/40. Raw audit stdout reconstructs exactly164240bytes/SHA256 2fa3aad1132e7d9054b0285affe7eda776b6ab479b7ec94eccf968f278d158f6.

Adjacent source-review, repair-review, exact repair patch, final review, coverage and two qualification records preserve the complete evidence chain. Qualified producers were reused without replaying checks.

This closes exactly this source-bound p44(7)–(8) unit. Bounded p44(9) connectors, eventual p51 growth and Studentizer geometry remain later obligations. C2/C12/OQ56 remain OPEN; OQ3 PAUSED_BY_USER. p54 repairs, published Shao–Zhou attribution, unverified novelty boundaries and124 nonprerequisite status remain.
