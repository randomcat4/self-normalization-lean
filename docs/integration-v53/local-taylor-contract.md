# Next source contract: local Taylor shifts for the true short-time kernel

Status: CANDIDATE_PENDING_ROOT_FREEZE. The complete literal declaration is in
`local-shift-candidate-declarations.md`; there is no next production source or
proof implementation. The current SourceShortTimeKernelBounds source remains
842e13b2b1a59fa4673b6f938d3a58ba986116fdb0ba3fd72745cef1614da06d,
commit9c258ccccfae5fe3e34110dde0822325401f8174, with author kernel/AX evidence
and independent review still pending. This next consumer cannot be accepted
until that producer receives its qualified complete independent review.

Original read-only supplement SHA256
b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd.
Relevant source: LF608–618 defines the actual odd/even decomposition and
equation evenoddlocal; LF624–650 gives the derivative budgets; LF690–710
uses those budgets on the actual event U_i≤y/16. This unit prepares exactly
that local kernel estimate, not the regulator moments or probability event.

The raw-law normalization, mean, conditional cutoff, moments, gamma, source
scales and exact max-guard index set are identical to the completed short
kernel producer. No centering or symmetry of the retained law is assumed.
All C,epsilon0,L2 are absolute and chosen before the raw law, and the actual
positive gamma/m2/y payments come from the same accepted source bridges.
J may be empty and i=n is retained in the finite range; no nonempty premise
or endpoint deletion is permitted.

The requested O_i/E_i are finite nonnegative real numbers, chosen after the
source/clock parameters but before q,w,u. They bound the actual standard
derivatives uniformly for every real q and every closed |w|≤y/16. Their
actual m2-weighted sums obey the original odd/even source budgets. These
properties are conclusions produced from
sourceTruncation_futureNoise_short_kernel_sums, not assumptions and not a
new opaque derivative-envelope interface. O/E outside J may be chosen zero.

The arbitrary index-dependent q_i,w_i strength of the completed producer is
essential. First prove boundedness of the actual derivative-value sets at
each selected index from m2>0, nonnegativity of the remaining finite sum and
the producer's joint-choice conclusion. Each spatial set is genuinely
nonempty because q=w=0 is allowed and y>0. Thus any use of real suprema or
least upper bounds pays nonemptiness and boundedness internally; neither is
supplied as an unbounded csSup premise. A convenient finite construction is
to choose approximate maximizing spatial points separately for odd/even,
double their nonnegative derivative values to get global upper bounds, and
apply the producer to those actual finite selections. The absolute factor2
is absorbed into C. An equivalent exact-sup construction with a proved
finite sum-sup interchange is allowed, but no unproved interchange is.

For each selected i and fixed q, the displayed actual o/e satisfy
o(0)=0, e(-u)=e(u), and
f(0,q)-f(-u,q)=e(0,q)-e(u,q)+o(u,q).
The producer proves differentiability of o,e,e' at every point of the closed
local interval. Evenness plus actual differentiability gives e'(0)=0.
Apply the actual real mean value/Taylor remainder theorem on [0,u] to o
and e, paying continuity on the interval from differentiability, to obtain
|o(u,q)|≤u*O_i and
|e(u,q)-e(0,q)|≤(u²/2)*E_i.
Handle u=0 separately; the nondegenerate interval proof must not divide by
u or introduce a strictly positive regulator assumption at this endpoint.
The resulting shift inequality keeps the actual factor1/2 in front of E_i.

This is a real consumer for the subsequent localized correction expectation:
O_i/E_i are deterministic uniform budgets, so the later actual reflected
regulator U_i and square-sum Q_i can be substituted on U_i≤y/16 and the
genuine E[U_i],E[U_i²] payments applied before summing. This unit does not
replace those moments with a common deterministic regulator cap, which
would lose the original nm3 improvement. It does not assume regulator
moment bounds or claim their production. It also does not pay U_i>y/16,
the microscopic T<L2*gamma² range, large y, desmoothing or C1/C2.

If root freezes this next unit, assign a new production module/ownership;
do not append it to or edit the already frozen SourceShortTimeKernelBounds.
Preserve author/reviewer separation, server-only exact source checking and
all actual-owned type/value/transitive-axiom requirements. No next proof or
Lean execution is authorized merely by this candidate preparation.
