# Conditional finite absorption for the actual killed kernel

Assume the exact three genuine moment integrabilities, mean zero, second
moment one, beta≤M, M≥0, h≥1 and π(1+M)≤h. Let m=⌊h²⌋₊, m≤N, and
|z|≤h. Use the actual previously defined principal cosine, free coefficient
rho, killed kernel powers, and normalized quantities fₖ=Fhatₖ(z),
gₖ=Ghatₖ(z). Set R=exp(π²), D=ER/h³, A'=AR and B'=BR/h.

The certified coefficient theorem gives 3/4≤rho<1. In particular every
normalizing power is positive. The floor property m≤h² and h²≥1 imply
m≥1: otherwise m=0 and h²<m+1=1, a contradiction. The explicit
finite-power estimates give

    rho^−(m+1)≤R, rho^−2m≤R, rho^−m≤R.

Here the last bound uses m≤h²≤2h² in the already certified uniform
inverse-power theorem.

Actual kernel positivity gives fₖ≥0 and gₖ≥0 for all k. Moreover
Fₘ(z)≤Gₘ(z), so multiplication by the positive reciprocal gives fₘ≤gₘ.
For k≤2m, the actual mass Gₖ(z)≤1 and the certified finite-range
normalization bound give gₖ≤rho^−2m≤R. In particular fₘ≤gₘ≤R.
These are derived initial bounds, not assumptions on the desired global
normalized mass.

Retain the two explicit block hypotheses, for every |w|≤h:

    Uₘ|r|(w)≤E/h³,       Gₘ(w)≤A phi(w)+B/h.

The actual normalized D2 identity/estimate then gives, for m≤k,

    |fₖ₊₁−fₖ| ≤ [(E/h³)rho^−(m+1)]gₖ₋ₘ ≤ D gₖ₋ₘ.

The second inequality uses E/h³≥0, the displayed inverse-power bound,
and explicitly gₖ₋ₘ≥0. The actual normalized D3 estimate gives

    gₖ₊ₘ ≤ [A rho^−m]fₖ + [(B/h)rho^−m]gₖ
           ≤ A'fₖ+B'gₖ.

The coefficient bounds use A,B≥0, h>0, and rho^−m≤R. The second
comparison explicitly uses both fₖ≥0 and gₖ≥0; it does not presume
nonnegativity of the principal cosine outside the closed source interval.

All hypotheses of the certified finite delayed-recurrence theorem are now
met with its parameters (A',B',D,C)=(AR,BR/h,ER/h³,R). In particular its
smallness hypothesis is exactly the frozen condition

    (AR)(ER/h³)N+BR/h≤1/2.

The theorem uses noncircular strong induction and yields, with
H=2(1+AR)R,

    gₖ≤H                    for every k≤N,
    |fₖ−fₘ|≤D(k−m)H         for every m≤k≤N.

Combining the first conclusion with the previously proved actual-kernel
nonnegativity gives 0≤gₖ≤H. No bound on all gₖ was assumed before invoking
the finite theorem. Natural subtraction is used only under m≤k. There is
no division by A, B, or E, so their zero values are included. N=m is also
included and makes the fluctuation conclusion zero.

This proves a conditional finite D8 bridge for the actual kernel. It does
not prove either block hypothesis, B1's limit fₘ→1, O0/R3/R4, Brownian
terminal-block estimates, iid survival estimates beyond the imported kernel
algebra, 4/π, or any root K/Kv/OQ4 theorem. The free coefficient is not
identified as a killed-kernel spectral eigenvalue.
