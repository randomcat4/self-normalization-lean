# Unit136: uniform sine-series wall estimate

The numerical series is the existing mixedSineSeries00 on all real space. No killed-kernel interpretation is assumed. The source-bound dependency is the positive-cutoff analytic bound needed to make the continuously monitored first-loss terms in unit135 vanish on continuous paths.

All four complete declaration heads were frozen before proof implementation. The original last head accidentally used adjacent absolute-value bars, which Lean lexed as an invalid || token. Original frozen-v1 bytes/record and attempts001/002 are preserved. freeze-v2-syntax-correction.json records the explicit abs (abs x - a) repair before implementation against the corrected freeze. No mathematical premise or quantifier changed.

The private order0/1 strip bound uses the established weighted-Gaussian summability at H and termwise uniform strip estimate at every U>=H. A norm bound at x=0 proves its constant is nonnegative. The bound in fact does not require j<=1, but that frozen assumption limits the intended usage.

The first public theorem proves both exact zero-wall values term by term, including arbitrary real analytic time: zero sine factor at -a and sin((n+1)*pi)=0 at a. The second uses the established spatial derivative of the series and the convex mean-value bound on all real space, producing nonnegative global M,L uniform in U>=H. The third subtracts the appropriate zero wall according to the sign of x and obtains L*abs(abs x-a). It does not restrict endpoint x to the interval, which is necessary for small overshoots.

Attempt003 passes the server kernel. Actual module-owner selection finds exactly4 owners: all theorems,3public1private,0generated/definitions. Each recursive axiom set is in propext/Classical.choice/Quot.sound. Complete actual-type export and the empty complete value export accompany the receipt. The first-loss error limit, actual killed/sine or image equality, unconditional hSmall, and original C12 root groups remain OPEN.
