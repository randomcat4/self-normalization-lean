# Actual killed blocks from explicit all-time S/AC inputs

Let ν be a Borel probability law with genuine integrability of y, y²,
|y|³, mean zero and second moment one. Put beta=∫|y|³dν and assume
0≤beta≤M, M≥0, Cq,Cs≥0. Retain these actual product-law inputs:

1. For every natural t≥1 and every real x, the probability that the t-step
   prefix sum belongs to the closed interval [x,x+1] is at most
   Cq beta/sqrt(t).
2. For every natural t≥1 and real d≥0, both existing closed upper survival
   and closed lower survival have probability at most Cs(d+beta)/sqrt(t).

The input predicates below package exactly these quantifiers and events;
they contain no block-bound or kernel conclusion.

Let h≥3, m=⌊h²⌋₊, and |z|≤h. The floor inequalities give m≥6,
m≥h²/2, and positive first and last natural half-block lengths. Apply the
certified BoundaryOccupation h-squared theorem for each natural j. The
first input supplies its closed concentration bound at t=m/2; the second
supplies its two one-sided bounds at t=m−m/2 and d=j+1≥0. Thus, for the
actual row κ=Pᵐ(z), every layer has mass at most

    [C_layer/h²](j+1),  C_layer=12 Cq Cs M(1+M).

No new layer-mass hypothesis is introduced. This is an actual kernel row,
with finite measure, mass at most one, and almost-everywhere closed strip
support furnished by the certified kernel-power interface.

Instantiate the certified averaged residual theorem with precisely this
κ and the layer estimates just obtained. It proves actual integrability
of the absolute principal residual under κ and bounds its integral by

    [π³ beta/48+2π C_layer(1+2beta)]/h³.

All coefficients are nonnegative. Since beta≤M, this is at most E/h³,
where E=π³M/48+2π C_layer(1+2M). This gives actual R3 uniformly for every
source start, using the actual mass and support, not an arbitrary-row
renaming.

For R4 set d=h−|z|≥0. A genuinely surviving shifted path starting from a
nonnegative z has every ordinary prefix at most h−z=d, hence belongs to
the existing closed upper event; when z<0 it has every prefix at least
−h−z=−d, hence belongs to the existing closed lower event. The zero prefix
is also admissible because d≥0. The actual path-law mass identity and the
all-time one-sided input therefore give

    Gₘ(z)≤Cs(d+beta)/sqrt(m).

The floor bound implies h≤2sqrt(m), so the last expression is at most
2Cs(d+beta)/h. On the closed source interval, the elementary cosine chord
inequality gives

    d/h=(h−|z|)/h≤cos(πz/(2h))=principalCosine h z.

This follows from 1−2x/π≤cos x for 0≤x≤π/2 and evenness of cosine,
and retains both endpoints. It is not a global cosine positivity claim.
Using beta≤M gives exactly

    Gₘ(z)≤A phi(z)+B/h,  A=2Cs, B=2CsM.

Finally retain π(1+M)≤h, m≤N and the stated finite smallness condition
with R=exp(π²): (AR)(ER/h³)N+BR/h≤1/2. All coefficient parameters are
nonnegative. The just-proved actual R3 and R4 statements supply the two
block hypotheses of the certified KernelAbsorption theorem for every
closed source start. Its noncircular finite recurrence yields, for
H=2(1+AR)R,

    0≤Ghatₖ(z)≤H                         (k≤N),
    |Fhatₖ(z)−Fhatₘ(z)|≤(ER/h³)(k−m)H     (m≤k≤N).

R3 and R4 are conclusions supplied internally, not premises of this final
D8 statement. The complete moment and threshold assumptions are retained.
The argument permits h=3, N=m, zero allowed parameters, atoms, asymmetry,
and arbitrarily large jumps. It adds no fourth moment, density,
nonlattice or bounded-support assumption.

The constants depend explicitly on M,Cq,Cs. This proves only a reduction
from the displayed all-time S/AC probability bounds. S/AC themselves,
B1, Brownian and terminal-block estimates, long-time K/Kv, 4/π, energy
denominator results and OQ4 remain OPEN. The free rho is not identified
with a killed-kernel spectral eigenvalue.
