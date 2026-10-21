# Conditional boundary occupation from unconditioned blocks and fixed reversal

Let ν be any Borel probability law. Write Π_t for its product law on the
existing Shao.Path t, and use the actual killed row κ=P^(l+r)(z). Assume
l,r≥1, h≥0 and |z|≤h. Let d(w)=h−|w| and let E_j be the existing
boundaryLayer d j, so j≤d(w)<j+1. No moment hypothesis is imposed.

By the certified path-law identity, κ(E_j) is the unconditioned product
probability of full closed survival and an endpoint in E_j. The standard
finite-product measurable equivalence splits a path into a first block a
of length l and an independent complete last block b of length r. Write
T=prefixSum(a,l), V=prefixSum(b,r), and w=z+T+V.

Reversal is a fixed coordinate permutation of b; its product law is still
Π_r. For 0≤k≤r its prefix sum is

    prefixSum(reverse b,k)=V−prefixSum(b,r−k).

The full surviving path at time l+r−k has position
x=z+T+prefixSum(b,r−k), lying in [−h,h]. At k=0 the reversed prefix is
zero. For k>0 the displayed identities and full closed survival give the
same position bounds (l≥1 ensures the monitored time is positive).

Split according to the sign of w. If w≥0, its layer condition says

    h−j−1 < w ≤ h−j.

Then each reversed last-block prefix w−x is at least w−h>−(j+1).
Thus reverse b belongs to the closed lower-survival event L_r(j+1).
For fixed b the first-block endpoint T belongs to the length-one closed
interval [h−j−1−z−V, h−j−z−V]. The strict lower endpoint was only
enlarged to a weak bound, retaining atoms. If w≤0, the layer condition
instead gives

    −h+j ≤ w < −h+j+1.

Now every reversed prefix is at most w+h<j+1, so reverse b belongs to
U_r(j+1); fixed b forces T into
[−h+j−z−V,−h+j+1−z−V]. This correctly pairs the upper endpoint layer
with the lower-survival input sMinus and the lower layer with sPlus.
If both sign descriptions apply, their union only enlarges the bound.

All prefix, concatenation, reversal, endpoint, interval-section, and
one-sided-event maps are measurable. In each of the two enlarged events,
fix the entire unconditioned last block b. The uniform first-block
concentration input bounds its section probability by q whenever b is in
the relevant reversed one-sided event, and by zero otherwise. Tonelli for
the unconditioned product measure gives at most q times that terminal
event probability. Fixed reversal preserves Π_r, so these two bounds are
q sMinus and q sPlus. Subadditivity proves

    κ.real(E_j) ≤ q(sPlus+sMinus).

No assertion of independence under survival or normalization of a killed
row occurs.

For the second conclusion let m≥6, l=m/2 and r=m−l. Natural integer
arithmetic gives l,r≥1 and m/3≤l,r, hence sqrt(l)sqrt(r)≥m/3. Insert
the exact real concentration/survival hypotheses

    q=Cq beta/sqrt(l),
    sPlus=sMinus=Cs(j+1+beta)/sqrt(r).

Their nonnegativity is explicit. The first conclusion and the denominator
bound imply

    κ.real(E_j) ≤ 2 Cq Cs beta(j+1+beta)/(sqrt(l)sqrt(r))
               ≤ 6 Cq Cs beta(j+1+beta)/m.

This argument permits zero beta, Cq, or Cs; no such parameter is divided by.

Finally let h≥3 and m=⌊h²⌋₊. The floor inequalities give m≥6 and
m≥h²/2. If 0≤beta≤M and M≥0, then for every natural j,

    beta(j+1+beta) ≤ M(1+M)(j+1).

Combining this with the previous bound yields exactly

    κ.real(E_j) ≤ [12 Cq Cs M(1+M)/h²](j+1).

Both final reductions retain their actual all-product S/AC probability
inputs, quantified for the displayed j; they do not manufacture those
inputs. Closed atoms, both layer endpoints, h=0 in the first interface,
and overlapping enlarged halves are preserved. The result is conditional
boundary occupation only. It does not establish S/AC, unconditional O0,
energy-marked O1/O2, actual R3/R4, B1, K/Kv, 4/π, or OQ4.
