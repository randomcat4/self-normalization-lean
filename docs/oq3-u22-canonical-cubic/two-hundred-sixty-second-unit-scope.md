# FY262 — uniform local cubic Hermite coefficient bound

Freeze both complete declarations and the one complete P1 let before implementation.
The same qualified safe Nat.rec Hermite family supplies all four low orders.
Prove explicit H0/H1/H2/H3 bounds on the unit interval, including the linear
vanishing of the odd terms. Then use all four binomial mixed-cubic terms,
with coefficients bounded in absolute value by B, to prove an origin zero
and the explicit local bound (16/3)*B*sqrt(x1^2+x2^2).

The normalized coefficient sum retains 1/6, choose(3,j), all j:Fin4,
both Hermite factors and exact coordinate degrees. No coefficient is
assumed positive or nonzero; B=0 and arbitrary negative b are included.

This is a source-bound helper for the report's uniform P1(z)=O(|z|)
step. Its b are explicit generic coefficients; they are not silently
identified with actual canonical cumulants. A subsequent consumer must
derive the actual mixed third-moment bound from the qualified FF radial
moments, and identify the full cubic Fourier/Hermite correction.
Density/globalCF/inversion/smoothing/exterior/B-D/original root remain OPEN.
No changed asymptotic beta range, p54 repair, Song attribution or counterexample.
