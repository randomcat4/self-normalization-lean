# Unit 230 repair01: same independent reviewer's affected proof-delta review

STATUS: CORRECT
SOURCE_STATUS: SOURCE_ACCEPTED_FOR_NEW_NATIVE
qualified: false
kernelPending: true

The exact new source is
`author-01/repair-01/IIDSourceStrictMomentBudgets.lean`, SHA256
`4905904cb5e8f37f1731c92da9e504e614e8dc7734a5de3f124ab2bceff55c36`,
10716 bytes, 245 LF, zero CR, UTF-8 without BOM. The sole public theorem is
`Shao.OQ6.IIDSourceStrictMomentBudgets.actual_iid_source_z_strict_moment_budgets`.
No critical gap was found in the exact four-line affected repair and its
interactions with the previously reviewed proof. This is acceptance for a new
native check, not a claim that the repaired source has compiled.

## Independence and exact evidence reused

This is the same never-author independent reviewer
`/root/oq56_iid_source_strict_budgets230_source_review`, newly activated only
for `unit230/source-review-01/repair-01/**` by activation SHA256
`564cb97237a24dcaac294ec675ddae2581aaca5683c24e36788d386000221d17`.
The matching parent repair intake is SHA256
`78307d7830ae4629820561d739d293c6095afb362f48ede9d155b8a606112e85`.
Actual ACK was sent before the affected review. The reviewer has not authored
or repaired the proof and has not edited any source, frozen file or other
owner's file. The math-theorem/project proof and resource rules remain in
force; no math-ultra workflow is used.

The prior exact complete independent SOURCE review is reused, rather than
repeated. It covers all 241 LF of source SHA256
`68dec15cc392157d84d3bf8d6dd8193668182458f6734daadbf668b19f2144b7`,
all 355 LF of primary p51, the entire frozen statement and typed inventory,
the actual qualified scalar public API at y=z-1, the product-integral
transport interfaces, and the entire original mathematical proof. The prior
review manifest SHA256 is
`60d52dcd74ba43bca9196856162c3225070a59b18728bc0f22443ee85795650b`;
its zero release SHA256 is
`f938c34e767fd510fe6b7fe0bb26cf40eedf97429f47b1049ed2b20a9ec9b74d`.
The parent complete-source intake SHA256
`8325a0af71c316eb9cb6916491c8fb9c8d416217a94ab625071484663dbbbfa1`
confirms that exact review's acceptance for the first native attempt. The
old producer's already qualified proof/evidence is reused unchanged and was
not re-reviewed or rebuilt here.

Literal new-source context read for this review is new lines 68-91 and
173-231. The complete repair delta, author report, compatibility, inputs,
manifest, release, parent repair intake and prior source intake were read.
All four native001 diagnostic errors, including their complete printed
contexts, were read from the existing normalized diagnostics. Complete
mathematical review coverage of the repaired source is the prior full review
plus this exact affected-delta review, supported by independent byte-exact
reverse reconstruction. This does not claim a redundant literal full read of
the new 245-line file or a second full read of p51 or the old scalar proof.

## Native001 failure is retained as failure

The normalized diagnostics bind the original 68dec source and receipt SHA256
`f82e7aae7fde8e904504d5fc1227e41ce0b6db495939a162a68bc7e509b6b53c`.
They record actual RC1, four errors, zero warnings, no original object,
natural completion, no owned Lean process remaining and protected-record
preservation. The four errors are precisely old lines 83, 190, 197 and 208:
the rewrite patterns print real HPow expressions while the targets print
explicit Real.rpow applications. This is a concrete representation mismatch
in the attempted rewrites, not a successful kernel receipt or a counterexample
to the previously reviewed mathematical argument. No server request or retry
was made by this reviewer. The new source remains uncompiled in this review.

## Independent exact-delta and frozen-value check

The reviewer independently checked the actual new lines and their anchors,
not merely the author's delta summary. Exactly these lines were inserted:

| New line | Old anchor | Affected proof | Inserted normalization |
| --- | --- | --- | --- |
| 83 | 83 | hcpower | `simp only [Real.rpow_eq_pow]` |
| 191 | 190 | hbeta power | `simp only [Real.rpow_eq_pow]` |
| 199 | 197 | n power | `simp only [Real.rpow_eq_pow]` |
| 211 | 208 | product equality in hWindowPower | `simp only [Real.rpow_eq_pow] at hβrootNonneg hnrootNonneg hβpower hnpower ⊢` |

There are four insertions, 205 added bytes, zero deleted/replaced original
bytes. Removing those exact four lines reconstructs the complete old source
byte-for-byte. The new prefix is still the exact frozen 557-byte preamble,
2097-byte head and ` := by` separator; its closing is still the exact frozen
48-byte suffix. All 19 ordinary typed let lines remain identical; the exact
reverse reconstruction also preserves their complete multiline types, RHSs,
scopes and captures. Thus all nine frozen values, their proof repeats and
the permitted f remain unchanged. There is one top-level theorem, no new
ordinary helper/parameter/instance, and no forbidden sorry/admit/axiom/unsafe/
native_decide token. The independent static result is in STATIC-DELTA.json.

## Affected proof and interaction review

**New 81-87, insertion 83.** After unfolding the local c, the target contains
the explicit nested Real.rpow of the positive half-minimum. Rewriting by
Real.rpow_eq_pow converts that expression to the same real HPow spelling
printed by the reverse Real.rpow_mul pattern in native001. Both exponents
remain real: 1/p and p. The base is unchanged and hhalfMinPos.le is still the
nonnegative-base premise. The unchanged field identity (1/p)*p=1 uses the
unchanged hpne; the final exponent-one reduction proves the original exact
constant identity. No power was changed to a natural power, no positivity
premise was added, and c's ordinary RHS still captures only p,cBudget before
all n,z. The resulting hcpower's declared type is unchanged, so hcSmall and
the later strict half-margin are exactly the previously reviewed consumers.

**New 190-195, insertion 191.** The new normalization changes only the goal's
presentation from explicit nested Real.rpow to real HPow. The same positive
beta base and real exponents -1/p and p are used. The unchanged reverse
Real.rpow_mul call still receives hβpos.le. The same hpne validates
(-1/p)*p=-1, and Real.rpow_neg_one reduces to beta inverse. The declared
result remains `(Real.rpow beta (-1/p)).rpow p = beta^-1`. This conversion
does not add a positive-beta assumption to the public theorem: it remains
strictly inside the existing positive-beta disjunct, after the independent
zero-beta proof. There is no new evaluation or cancellation at beta=0.

**New 196-202, insertion 199.** Both nested rpow occurrences and the RHS
are normalized consistently to real HPow. The base remains the positive
real cast of n and the real exponents remain (p-2)/(2*p), p, (p-2)/2.
The unchanged hnPos.le supports rpow multiplication; the unchanged field
identity uses hpne and proves exactly
((p-2)/(2*p))*p=(p-2)/2. No n=0 case or new denominator occurs. The
declared hnpower proposition is unchanged and retains n=1 and p=3.

**New 203-225, insertion 211.** The first inequality of the calc already
uses the unchanged hPowBound at the original explicit-rpow type. In the
following equality subproof the fourth insertion rewrites both the goal
and the four facts used directly by the next rewrite:
hβrootNonneg, hnrootNonneg, hβpower and hnpower. This is necessary interaction
coverage: the nonnegativity facts determine the beta-root and n-root bases
passed to Real.mul_rpow, and the two power identities must match the
post-expansion expressions. After normalization they all use the same real
HPow spelling and the same bases/exponents. Two mul_rpow rewrites separate
the product, then the normalized hβpower and hnpower give exactly the desired
beta inverse and n power. hcPos.le needs no additional normalization because
it states positivity of the unchanged local c, rather than a syntactically
explicit rpow. hPowBound is consumed before this equality subproof, and
hdenPos is consumed later at the unchanged outside type, so neither requires
a simultaneous normalization in this local equality.

The local tactic rewrites transport propositions by equality; they introduce
no ordinary value or additional input premise. The enclosing hWindowPower
keeps its declared explicit-rpow type. Consequently the later multiplication
by beta, division by the n-power and field cancellation remain exactly the
previously reviewed argument. Positivity of beta and the n-power is still
established before cancellation. No consumer can receive a weakened or
differently normalized mathematical statement from the bridge.

## Unaffected semantics and pending gate

Byte-exact reconstruction supports reuse of the complete earlier review of
IID product laws and all genuine scalar/marginal integrability, delta/scalar
and total identities, the unconditional source-z p-moment rate, beta=0
vanishing before cancellation, the positive-beta closed S19 window, strict
half-margin budgets, p=3, n=1 and possible empty-window cases. The four
changes affect only the proof's representation for rewriting. They alter no
assumption, quantifier, constant, law, integration domain, cutoff convention,
source-z interpretation or generic cBudget meaning. There is no new hidden
centering, unit-variance or positive-beta premise. Primary repair status,
p54 repairs, external attribution and all original open-scope limits remain.
No CDF/SZ application, coding witness, weighted limit, zero-event payment or
root closure is asserted.

This exact repaired source is accepted for a new native check. Native001
remains the original failure, without object or axiom receipt. New native
success and same-FIRST-original-object all-actual TYPE/VALUE/transitive-AX
evidence remain required; qualified=false and kernelPending=true persist.
The same independent reviewer may later join those actual new receipts and
inspect any newly exposed interface or proof risk without an automatic
duplicate full proof review.

All work was local and confined to the activated review directory. There
were zero Lean commands, server/network/transfer/Git/API operations, children
or old producer/leaf-AX replays. Units228/229 were not read or used. Requested
model/effort are gpt-6.1-sol/xhigh; actual model/effort and input/cachedInput/
output/reasoningSubset are unexposed and null. The bundle's RELEASE records
zero ongoing writers, heavy, in-flight, pending external or uncertain work.
