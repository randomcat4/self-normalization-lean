# Unit 230 complete author implementation

Status: COMPLETE_SOURCE_READY_FOR_FIRST_SERVER_CHECK_AND_INDEPENDENT_REVIEW.
Lean status: LEAN_TRANSLATION_UNAUDITED; no new kernel or axiom receipt exists.

The source is `IIDSourceStrictMomentBudgets.lean`, implementing the sole
frozen theorem
`Shao.OQ6.IIDSourceStrictMomentBudgets.actual_iid_source_z_strict_moment_budgets`.
Its SHA256 is
`68dec15cc392157d84d3bf8d6dd8193668182458f6734daadbf668b19f2144b7`;
the complete source has 10511 bytes, 241 LF and zero CR, with no UTF-8 BOM.

## Exact interface and ownership compatibility

The complete 557-byte frozen preamble and 2097-byte frozen declaration head
are the exact source prefix, immediately followed by ` := by` and LF. The
complete 48-byte frozen closing is the exact source suffix. The parameters,
instances, all nine ordinary lets, their full types/right-hand sides and
dependency scopes, all conjunctions, the beta-zero branch and positive-beta
closed window have not changed. The declaration is implemented without adding
a global helper or mathematical premise.

The proof repeats exactly the nine frozen ordinary values. Its only additional
ordinary helper is the explicitly permitted local

`f : Ω → ℝ := fun o : Ω => Shao.truncationF (z * (g o / N))`,

inside the current n,z,N scope. The source's 19 ordinary let occurrences are
the nine in the head, nine proof repeats, and this f. All proof-local facts
have explicit proposition types. There is no additional ordinary value let,
parameter, local instance value or top-level declaration. The prose names
m,d,a,b from Stage 1 were not introduced as values.

Writes are confined to `unit230/author-01/**`. All four Stage 1 manifest
payload hashes were reverified unchanged. The curated library and all other
owners' implementations remain untouched. Units228/229 were not read,
imported, copied, renamed, retried or used. No shared Probability change is
required.

## Proof implementation and semantic coverage

Lines68-90 establish the outer constant packet. The beta integral is
nonnegative. Positivity of `min(1/2,cBudget)/2` gives c>0. The genuine
real-power multiplication identity and `(1/p)*p=1`, using p>0, give the exact
frozen cth-power identity. Halving the positive minimum supplies strict room.
This c depends only on p,cBudget and is established before introducing n,z.

Lines92-119 repeat the exact product, normalization, integrand and budget
values. The qualified scalar source API is called with all its actual
arguments at `y=z-1`, not z. From `z≥1`, that parameter is nonnegative, and
`1+(z-1)=z` identifies both its genuine integrability and normalized p-moment
rate with the literal source-z kernel. The dependency's original accepted
qualification is reused; no old proof is reconstructed or rechecked.

Lines120-156 make the IID transport explicit. The local f is measurable.
Each coordinate evaluation preserves the product law and has marginal μ;
`integrable_comp_of_integrable` proves coordinate integrability and
`integral_map` proves the equality of coordinate and scalar integrals. A sum
of n identical marginal integrals gives `L=n*scalarBudget` and `L=n*δ_i`.
Every truncation integrand is nonnegative, so every δ and L are nonnegative.
The summand comparison `δ_i≤L` uses n≥1 and `L=n*δ_i`, avoiding division by
any budget. The qualified scalar rate therefore becomes the unconditional
rate for the actual sum L.

Lines157-165 handle beta=0 before any cancellation. The unconditional rate
gives L≤0, hence L=0. Since `0≤δ_i≤L`, each δ_i is zero. This branch relies
on the genuine integrability already established and does not exploit the
total value of a nonintegrable Bochner integral.

Lines166-235 prove the strict window packet. The zero-beta disjunct gives
L=0≤c^p. In the positive-beta disjunct, monotonicity raises the closed window
inequality to p. `Real.mul_rpow` separates all three nonnegative bases, and
`Real.rpow_mul` gives the exact exponent cancellations
`(-1/p)*p=-1` and `((p-2)/(2*p))*p=(p-2)/2`.
`Real.rpow_neg_one` then turns the beta factor into beta inverse. Beta and
the n-power denominator are proved strictly positive before field
cancellation. This yields `beta*z^p/n^((p-2)/2)≤c^p`, and hence L≤c^p.
The strict outer half-margin gives each δ_i<1/2 and L<cBudget; z≥1 gives
`cBudget≤cBudget*z²`, proving the requested strict total margin even at the
closed upper window endpoint. The upper endpoint p=3 is retained. No
standardized second moment or mean-zero premise was introduced.

Line236 supplies the complete eleven-part inner packet. No CDF, coding,
weighted-limit, zero-event-smallness, external-SZ application or root closure
is asserted. The source faithfully implements the accepted quantitative S19
ingredient, within the original primary repair-candidate's stated scope and
external attribution.

## Validation performed and pending gates

Only local deterministic byte/hash/format/declaration-inventory checks were
performed. The frozen prefix/closing compare exactly, the source contains one
top-level theorem, all ordinary value-let names are in the frozen inventory,
and the prohibited-token scan has zero matches. All directly bound input
hashes were reverified. Parent-observed availability of all ten compiled
direct imports is preserved as existing read-only evidence; this author did
not replay any import or old-producer check.

No Lean compilation, axiom audit, server/network request, transfer, Git/API
publication or child delegation occurred. The complete proof is authored,
but its elaboration, first exact-source server kernel/all-owned transitive
axiom audit, and qualified independent full source-to-statement/proof review
remain pending. This report is an author explanation and cannot replace that
independent review or those receipts.

The requested model/effort are gpt-6.1-sol/xhigh in the same authorized author
context. Actual model/effort and input/cachedInput/output/reasoningSubset usage
are not exposed and are recorded as null, without a fabricated subscription
allocation. The author releases the implementation writer slot with zero
ongoing, heavy, in-flight, pending external or uncertain operations.
