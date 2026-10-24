# Unit 151: actual auxiliary energy-tilt moments and variance

Source: supplement.tex lines 5103–5107, following the energy-only auxiliary tilt
of lines 5094–5101. The auxiliary law is centered, has second moment one and
integrable absolute cube. These assumptions are not imposed on the original
finite-second-moment laws of units 145/147. This unit proves general estimates
for every s >= 0 before paying the small-s numerical regime in the source.

For the literal native rho=nu.tilted (fun z => -s*z^2), both the square and the
absolute cube are genuinely integrable. With beta=integral |z|^3 dnu and
mu=integral z drho, the tilted square moment lies between
1-sqrt(s)*beta and exp(s), and the tilted absolute cube is <= exp(s)*beta.
The actual native variance equals the tilted square moment minus mu^2. It lies
between 1-sqrt(s)*beta-(s*exp(s)*beta)^2 and exp(s).

The proof consumes the exact unit150 source-bound normalizer/drift theorem
(independent review pending when this unit was authored). Weight V=exp(-s*z^2)
lies in (0,1], so the weighted square/cube and both native tilted moments are
integrable by domination and integrable_tilted_iff. The native integral_tilted
formula gives their true weighted integrals divided by the true normalizer.
The pointwise loss 1-V <= sqrt(s)*|z| follows by setting t=sqrt(s)*|z| and
using 1-V<=t^2 when t<=1, and 1-V<=1<=t otherwise. Multiplication by z^2 and
integration pays the raw square loss. Dividing the nonnegative numerator by
Z<=1 can only increase it; upper moment estimates instead use Z>=exp(-s).
Genuine MemLp2 follows from the proved square integrability. Native
variance_eq_sub and the squared unit150 drift bound then give both variance
estimates. No totalized-integral or zero-variance shortcut is used.

All imports, full context and the single declaration head were frozen before
implementation and remain unchanged. Attempt001 is preserved: its two errors
were a measurable absolute-cube expression and one function-difference
unfolding. Only those two proof expressions changed. Attempt002 passed; its
nonblocking local-instance style hint was retained without polishing/replay.
The exact-source all-owner audit uses getModuleIdxFor? and recursive
collectAxioms. It finds one public theorem, zero private/generated owners and
zero non-theorem values, with only propext/Classical.choice/Quot.sound.

The source's fixed variance interval [1/2,2], centered third-moment estimate,
legality of the centered law's C1 input and the quantitative rare-suffix budget
remain subsequent work. Original full C12 root groups remain OPEN. Author
writer/execution release permits a complete independent review of this exact
source, full actual type, consumed interfaces and server receipt.
