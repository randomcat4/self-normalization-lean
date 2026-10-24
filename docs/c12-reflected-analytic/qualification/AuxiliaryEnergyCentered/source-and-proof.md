# Unit 152: auxiliary tilt small-parameter centered law

Source: supplement.tex lines 5103–5107, for the bounded/preprocessed auxiliary
law of lines 5094–5101. The original finite-second-moment sample laws are not
given new moment assumptions. Two exact declaration heads were frozen before
implementation, with one project import and no global non-theorem values.

First, the auxiliary absolute third moment beta is proved to be at least one
from probability, integrability of square and absolute cube, and second moment
one. The proof integrates 3*z^2 <= 1+2*|z|^3; its difference factors as
(|z|-1)^2*(2*|z|+1). Thus beta>=1 is paid rather than assumed.

Second, for s>=0 with s*beta^2<=1/128, the literal native energy tilt rho is a
probability law. Its actual identity and centered identity are integrable,
the centered mean is zero, and the centered square and absolute cube are
genuinely integrable. Its drift is <=2*s*beta, its actual variance lies in
[1/2,2], and its centered absolute third moment is <=12*beta. The smallness
condition is the source's inverse-beta-square condition in equivalent
multiplicative form, since beta>=1 has been proved. The stronger printed
beta*sqrt(s)<=.01 estimate is not asserted or required for this unit's bounds.

Exact unit150/151 normalizer, raw moments, genuine variance and drift bounds
are consumed. Beta>=1 gives s<=1/128. Native
Real.exp_bound_div_one_sub_of_interval gives exp(s)<=2. The square-root loss
is <=1/8 and the general drift bound is <=1/64. Substitution into the actual
unit151 variance lower bound gives 1/2; its upper bound is <=exp(s)<=2.
The cube triangle estimate |z-mu|^3<=4*(|z|^3+|mu|^3), proved from the norm
triangle inequality and 3*(a+b)*(a-b)^2>=0, gives an integrable envelope and
then the explicit centered-cube constant12. Mean zero is the genuine
integral_sub identity under the proved probability law. Centered square
integrability follows from the proved MemLp2 identity minus a constant.

Attempt001 source/command/log are preserved. It exposed three elaboration
issues: pointwise function addition before integral rewriting, one final
definitional equality after the cube integral expansion, and an identity-
function/measure annotation for the centered mean rewrite. Those proof
expressions alone changed; all frozen import/context/head bytes remain exact.
Attempt002 passed. The nonblocking local-instance style hint is retained.
The all-owner map contains exactly two public theorems, no private/generated
owners or non-theorem values. Recursive collectAxioms permits only propext,
Classical.choice and Quot.sound. Original successful old gates were not replayed.

Author writer/execution release is for a fresh independent complete review of
this exact source, full actual types, consumed interfaces, original source and
server evidence. The centered law's comparison-budget input, tilted lower raw
energy, quantitative rare-suffix budgets and full original roots remain open.
