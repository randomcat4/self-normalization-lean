# Unit 153: auxiliary low raw energy Laplace ingredient

Source: supplement.tex lines 5113–5120, following the auxiliary bounded product
law and energy-only tilt of lines 5078–5107. The three exact frozen heads prove
single-law estimates, including the actual tilted exponential observable. No
new moment assumption is imposed on the original finite-second-moment laws.

For centered probability nu with unit second moment and integrable square and
absolute cube, beta denotes the absolute third moment. First, for every a>=0,
a-a*sqrt(a)*beta <= 1-phi(a), with phi(a)=integral exp(-a*z^2) dnu.
Second, if a*beta^2<=1/64 then phi(a)<=exp(-7*a/8). Third, for 0<=s<=q and
(s+q)*beta^2<=1/64, exp(-q*z^2) is genuinely integrable under the literal native
rho=nu.tilted(-s*z^2), and its expectation is <=exp(-3*q/4).
These are the source's Laplace loss, decay and ratio ingredients in a general
parameter form. They do not yet assert the product-law Chernoff bound, the
specific q=1/(128*beta^2) choice, or a rare-suffix/root comparison.

For the pointwise lower loss set t=sqrt(a)*|z|. If t<=1, native
Real.abs_exp_sub_one_sub_id_le at -t^2 bounds the exponential remainder by
t^4<=t^3. If t>=1, t^2-t^3<=0 and 1-exp(-t^2)>=0. Thus
a*z^2-(a*sqrt(a))*|z|^3<=1-exp(-a*z^2). Both sides are genuinely integrable
by h2/h3 and the exact unit150 bounded weight. Integrating gives the first
head. The smallness condition gives sqrt(a)*beta<=1/8; hence 1-phi(a)>=7*a/8.
The global exponential tangent gives phi(a)<=1-7*a/8<=exp(-7*a/8).

For the third head, integrability under the actual tilt follows from native
integrable_tilted_iff and the integrable combined weight at s+q. Native
integral_tilted and integral_div identify its true expectation with
phi(s+q)/phi(s). The numerator uses the proved decay, the denominator uses
the exact positive unit150 phi(s)>=exp(-s), and s<=q gives
exp(s-7*(s+q)/8)<=exp(-3*q/4). No substituted law, assumed Laplace estimate,
unproved integrability or division by a nonpositive normalizer is used.

All imports/context/three heads were frozen before implementation and remain
unchanged. Attempt001 passed; there are no failed attempts. The exact all-owner
map contains three public theorems, zero private/generated owners and zero
non-theorem values. Recursive collectAxioms uses only propext, Classical.choice
and Quot.sound. No successful previous Lean or audit gate was replayed.

Author writer/execution release permits complete independent source/proof/
actual-type/interface/axiom/receipt review. Exact150151 dependencies already
have qualified independent evidence;152 is in the same new review batch. The
next dependency is the actual deterministic product-length low raw energy
bound. Quantitative rare-suffix budgets and original full roots remain OPEN.
