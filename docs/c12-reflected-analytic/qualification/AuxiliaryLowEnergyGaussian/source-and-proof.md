# Unit 155: low raw energy paid by the actual Gaussian tail

Source: supplement.tex lines 5120–5122. The first frozen head proves the scalar
payment exp(-A)<=8/3*standardNormalTail(y) whenever y>=0 and A>=y+y^2/2.
The second applies it to the actual unit154 energy-tilted product law, with
0<=s<=1/(128*beta^2), x>=0 and n>=1024*beta^2*(1+x)^6. Its actual weak raw
energy probability P.real {energy<=n/8} is <=8/3*standardNormalTail(3*x/2).
This pays the source's low-energy Gaussian-tail term. If the source rank
condition is l/beta^2>=K*(1+x)^6/2, choosing K>=2048 pays this explicit rank.
No universal constant is chosen after observing a law or sample.

The first proof reuses the exact accepted GaussianTail ratio_bound at the
comparison arguments y and0, with tail(0)=1/2 and tail(y)>0. The tangent
1+y<=exp(y) gives 1/2<=4/3*exp(y+y^2/2)*tail(y). Multiplying by exp(-A)>0,
combining real exponentials, and using y+y^2/2-A<=0 gives the explicit8/3
constant. No Gaussian Mills proof is reimplemented or assumed.

The second proof pays beta>=1 via the exact unit152 theorem. Thus division by
1024*beta^2 is positive. The explicit rank condition gives
5*n/(1024*beta^2)>=5*(1+x)^6, which dominates (3*x/2)+(3*x/2)^2/2 for x>=0.
The actual weak energy probability from unit154 is then paid by the first
head. Energy remains the uncentered square sum, and the actual product of
native tilted measures is unchanged. The stronger weak-event bound includes
all equality/zero-energy atoms; it implies the source's strict event estimate.

Both heads and complete import/context were frozen before proof work and are
unchanged. Attempt001 is preserved: an unavailable sq_zero lemma name was
replaced by the native zero_pow instance, and a redundant ring after an
already-closing congr step was removed. Only those proof expressions changed.
Attempt002 passed; no successful gate was replayed. Actual module ownership
has two public theorems, no private/generated owners or non-theorem values.
The exact recursive all-owner axiom audit permits only propext,
Classical.choice and Quot.sound.

Author writer/execution release is for fresh complete independent exact-source
review. Existing accepted GaussianTail and finite-path evidence is reused, with
actual consumed interfaces/hashes checked. The auxiliary finite3 hypothesis
does not modify the original finite2 sample laws. The centered event implication,
legal own-law C1 budget, full rare-suffix estimates and original roots remain
subsequent work, not conclusions of this unit.
