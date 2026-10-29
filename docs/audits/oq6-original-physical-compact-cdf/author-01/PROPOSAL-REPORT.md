# Unit264: original arbitrary-space physical compact CDF proposal

Status: PROPOSAL_ONLY; NOT_FROZEN; NO_IMPLEMENTATION. The mathematical reduction described below has no identified missing mathematical premise after the two qualified input theorems are reused. The proposed Lean theorem remains INCOMPLETE: no proof source has been written, elaborated, independently reviewed, or kernel checked for unit264.

Author: `/root/oq56_unit264_author`, the sole unit264 proposal author under `interface-proposal-ACTIVATION.json`. Sole lane owner: chat `01a1822b-1815-7f21-a1af-2e0b15ee67a5`. All outputs are in `drafts/oq56/unit264/author-01`; no other owner, shared implementation, library snapshot, original source, or integration file was modified. Unit263 proceeds independently.

The actual read acknowledgment was written before every proposal artifact. `READ_ACK.json` binds the activation and all thirteen exact inputs, records the complete required declaration reads, complete p51/p54 and independent report reads, and distinguishes parsed reuse metadata from a new literal reading of old compiled TYPEs. All thirteen byte/hash bindings matched. Old source/proof/object/kernel/axiom evidence is reused; this author has not repeated its independent review or remote checks.

## Exact proposed public interface

Proposed module: `Shao.OQ6.OriginalPhysicalCompactCDF`.

Proposed theorem: `Shao.OQ6.OriginalPhysicalCompactCDF.actual_original_physical_compact_cdf_tail_rpow_rate`.

`HEAD-PROPOSAL.txt` contains the full proposed declaration, with no proof delimiter or body. It is obtained from qualified170's exact declaration at lines343–383 by only these edits: rename the theorem; rename its ordinary CDF input binder from `hSZ` to `hSZC`; name the existing measurable-space binder `mΩ`; remove the public `MeasurableSpace.CountablyGenerated Ω` instance. Every original kernel/probability/moment assumption, local value, coefficient, event, threshold, and quantifier order otherwise remains literal. The binder name `mΩ` helps retain the original structure explicitly inside the eventual proof and adds no hypothesis. `PREAMBLE-PROPOSAL.txt` and `CLOSING-PROPOSAL.txt` specify the exact surrounding file text. Only one public theorem is proposed; there is no new public definition, auxiliary axiom, or public transport assumption.

In mathematical notation, let μ be any probability measure on any measurable Ω, and let h:Ω×Ω→ℝ be jointly measurable, symmetric, in L²(μ×μ), centered, with projection g(o)=∫h(o,y)dμ(y) satisfying ∫g²dμ=1. Put r(o,y)=h(o,y)−g(o)−g(y), v=∫r²d(μ×μ), s=1+√v, and β=∫|g|^p dμ. The only added moment premise is the same genuine integrability of |g|^p as170, for 2<p≤3. A supplied `ScalarShaoZhouFiniteCostCDFInput.{u} C` is required, exactly as170.

The conclusion is one K>0 before all n and x. For every n≥3 and every x∈[0,1], with the original iid product law Pₙ=μ^(Fin n), the same error

    K * (β / Real.rpow (n:ℝ) ((p−2)/2) + s / Real.sqrt (n:ℝ))

bounds all four errors: Pₙ(T≤x) versus Φ(x), Pₙ(T<x) versus Φ(x), Pₙ(x<T) versus 1−Φ(x), and Pₙ(x≤T) versus 1−Φ(x). Measurability of the same physical T in the ORIGINAL product measurable space is part of the conclusion. The head retains170's public name `P₀` for Pₙ; below, `Pₙᶜ` denotes the separate internal coarse product law, so these are not confused.

There is no public countable-generation, standard-Borel, atomlessness, positive-rho, extra moment/envelope, beta bound, desired probability bound, event-agreement, or coarsening premise. `hSZC` is deliberately distinct from the scalar Shao–Zhou TAIL input used in other units. No implication from that tail input to this CDF input is assumed or proposed.

## Source-to-statement bearing and limits

The original bearing is p51 S1's arbitrary-measurable-observation reduction and p51 S5's nonnegative compact physical CDF/strict-endpoint problem. The exact normalized assumptions and physical finite-row statistic are inherited from qualified170, rather than replacing h by an abstract statistic with a desired law. Unit221 is the qualified same-original-space coarsening bridge needed to remove the public countable-generation premise.

p51 S1 writes n≥4 for its centered-row development. The present n≥3 is not inferred by dropping that source condition: it is precisely qualified170's already reviewed and kernel-checked finite-row compact range. The new generic finite-J reduction adds no n restriction. Conversely, this proposal does not claim every p51 statement at n=3.

p51 S27 displays a compact estimate with its own stated residual coefficient. This proposal preserves the exact rate already proved by qualified170, with s=1+√v, rather than silently replacing170's rate by a differently normalized p51 expression or claiming to reprove all of S27. The only new mathematical scope is arbitrary original measurable Ω for that precise conditional170 conclusion.

The original p51 file remains an attributed repair candidate. p54's correction is preserved: conditional standardized p-moments need convergence/uniform boundedness, not arbitrary polynomial convergence rates. No conditioning, truncation-family uniformity, or rate of a changing conditional p-moment is used here. p54's strict upper-event margins, full source-upper payment and compact-versus-tail distinction are not discharged by this wrapper. The supplied broader L² scalar CDF input remains an external conditional input with Shao–Zhou attribution; existence/proof of that input is not asserted.

## Qualified dependencies and exact evidence reuse

The required complete qualified221 declaration at source lines17–177 and complete qualified170 rate declaration at343–383 were read. The distinct CDF input definition at `NormalizedIntegrableCDFAssembly.lean` lines19–68 was read in full. The input declaration quantifies arbitrary measurable probability spaces, independent measurable centered L² scalar coordinates with total variance1, scalar-coordinate full/deleted functions, nonnegative envelopes, almost-everywhere domination and positive denominators, genuine full/deleted cost integrability, and z≥0; it yields a CDF estimate. Its first conjunct is 1<C. It is an ordinary supplied Prop, not an axiom or a newly established result.

| Dependency | Exact source | Original object | Reused qualification |
| --- | --- | --- | --- |
| 221 `actual_normalized_original_countably_generated_model` | SHA256 `8691f69ca9ab84649f92b20385c415a2129250cc8f64375d6296e2d59a381627`, 21808B | `3b1dd126d9efe2ddc543e59e63228afb275be155de16a491b3654e7b3bfa07ff`, 3453368B | complete independent source/affected-proof review, all actual TYPE/recursive AX, native0 and same-first-object audit0 |
| 170 `actual_physical_compact_cdf_tail_rpow_rate` | SHA256 `d264ae1c1f04cee3b43ec5e44829a5986574d70f30615f7bdeb1f1bfab2a14ae`, 26260B | `c907a0e8730cae485e8e6614f4fb3aa5f839687cb748b71f2706b9cb7c7a0dfb`, 3118176B | retained complete original review plus exact affected review, all actual TYPE/recursive AX, native0 and same-first-object audit0 |

Both accepted qualifications retain strict-wrapper-success=false and their warnings while separately certifying actual native/audit return0 and exact original objects. This proposal does not relabel those fields. The standard axiom whitelist in that evidence is propext, Classical.choice, Quot.sound. The new wrapper still needs its own exact-source independent complete review and same-first-original-object all-owned audit later. Source/proof evidence from unchanged221/170 is not to be replayed merely because this consumer is new.

The rest of `NormalizedIntegrableCDFAssembly` is not a newly requested assumption. Its accepted definition is already a transitive dependency of170; unit264 only passes the identical input `hSZC` to170 at the internally selected measurable structure. No external-input theorem is silently substituted.

## Route A: one common coarsening, before every n and x

Apply qualified221 once to original Ω,mΩ,μ,h and the exact original hh,hh2,hhsymm,hcenter,hprojectionsecond. Its additional zero observable family f is internal to that theorem. Choose its one witness m₀≤mΩ and let μ₀=μ.trim(hm₀). Install countable generation and probability only for this internal m₀/μ₀.

Read the relevant outputs with the original and coarse structures kept explicit:

1. h is jointly measurable on m₀×m₀; μ₀ is a probability; h has the same L² and mean-zero facts there.
2. g₀(o)=∫h(o,y)dμ₀(y) is measurable for m₀, and g₀=g as TOTAL functions, not only almost everywhere. Thus r₀=r, v₀=v, rho₀=rho exactly. In particular170's coarse residual scale s₀=1+√v₀ equals the original s. The equality of v-integrals is a separate221 output; it is not inferred from r₀=r alone while ignoring the measure change.
3. ∫g₀²dμ₀=1, and the remaining normalized projection/residual facts required by170 are supplied. Original symmetry is pointwise in h and remains the same statement.
4. The exact projection law identity is

       ν₀ := @Measure.map Ω ℝ m₀ (borel ℝ) g₀ μ₀
           = @Measure.map Ω ℝ mΩ (borel ℝ) g μ =: ν.

5. For EVERY finite J, before any statistic is chosen,221 gives original/coarse product structures mJ,mJ₀, laws PJ,PJ₀, measurable identity id:(J→Ω,mJ)→(J→Ω,mJ₀), the exact product identity PJ₀=map id PJ, and map T PJ₀=map T PJ for every target B,mB and every mJ₀-measurable T.

No countable-generation instance for mΩ is inferred or installed. The same m₀ and μ₀ work before all later n/x. Retain original `mΩ`, original μ, all original g/r/v/s/β values and original product structures explicitly when entering an m₀ instance scope; a local `letI` must not accidentally change the meanings of those captured values. The named original-space binder in the proposed head makes this capture discipline visible.

This route does not use221's later specialized n≥4 centered/clipped-statistic clause. That clause has different guards and is unnecessary. In particular no proof of equality with a clipped process, no epsilon coding, no n≥4 restriction and no new zero-event payer enters this reduction.

## Route B: genuine p-moment transport, including integrability

The all-ENNReal-p MemLp equivalence in221 is not used as a shortcut for the real-rpow integrability premise. The following measurable-law argument proves exactly the needed statement and exact beta value.

Let F:ℝ→ℝ be F(t)=Real.rpow |t| p. From 2<p obtain p≥0. The map F is continuous, hence Borel measurable and a.e. strongly measurable for each of ν and ν₀. This is the same continuity fact already used in qualified170 lines74–78: continuous absolute value composed with `Real.continuous_rpow_const` for a nonnegative exponent. No regularity assumption on the observation space is needed.

First recover original measurability of g without adding it to the public head. The identity id:(Ω,mΩ)→(Ω,m₀) is measurable since m₀≤mΩ. Compose this with m₀-measurability of g₀, then use the TOTAL equality g₀=g. Thus both g:(mΩ)→ℝ and g₀:(m₀)→ℝ have the measurable-map witnesses required below.

The exact `integrable_map_measure` equivalences, with spaces/measure arguments explicit, are

    Integrable F ν   ↔ Integrable (F ∘ g) μ,
    Integrable F ν₀  ↔ Integrable (F ∘ g₀) μ₀.

Their hypotheses are the a.e. strong measurability of F on the mapped real law and a.e. measurability of the corresponding g. The original hgp is precisely the right side of the first equivalence after unfolding g,F. It gives Integrable F ν. Rewrite by ν₀=ν, then use the second equivalence in the reverse direction to obtain

    hgp₀ : Integrable (fun o => Real.rpow |∫y,h(o,y)dμ₀(y)| p) μ₀.

This transfer explicitly establishes finite/integrable moments before any equality of Bochner integrals is used. It does not exploit the totalized zero integral of a nonintegrable function.

Now the two `integral_map` equalities, justified by those measurability witnesses (and the already established integrability), give

    β₀ = ∫ F(g₀(o)) dμ₀(o)
       = ∫ F(t) dν₀(t)
       = ∫ F(t) dν(t)
       = ∫ F(g(o)) dμ(o) = β.

These are exact equalities with the same real exponent p, including p=3. There is no ENNReal exponent conversion, new moment bound, beta enlargement or change of constants. The same law method would work for any Borel integrable real function of the projection; only F above is needed here. The local uses of `integrable_map_measure`/`integral_map` in qualified170 lines67–83 and94–102 were read to verify the actual parameter direction, rather than treating a slogan about equal laws as a formal interface.

## Route C: apply170 at the selected structure

At m₀/μ₀, apply the exact qualified170 theorem with the SAME C,hSZC,h,p,hp2,hp3; use coarse hh₀,hh2₀,hcenter₀,projection-second1 from221, unchanged hhsymm, and hgp₀ above. The original type universe is unchanged, so the universally quantified `ScalarShaoZhouFiniteCostCDFInput.{u} C` applies directly to this probability space. It needs no transport of its own and no additional external input.

170 returns K>0 before all n≥3 and x∈[0,1]. Keep exactly this witness. Its internal explicit construction K=131112*C+33117+2/c belongs to the already qualified proof; the wrapper neither reproves it nor asserts a stronger public numeric formula/uniformity. K may depend on the fixed original model and supplied input as permitted by the signature. There is no added uniformity in μ,h or p.

The170 error under μ₀ is

    K * (β₀ / Real.rpow N ((p−2)/2) + (1+√v₀)/√N).

Substitute β₀=β and v₀=v to obtain the literal proposed original error. N=n and q=√N do not depend on the measurable structure. This exact rewriting introduces no additive payment, multiplicative loss or quantifier change.

## Route D: the literal physical finite-row function is unchanged

For each n, define Hξ(i,j)=h(ξ i,ξ j). The complete directly relevant existing finite-row definitions were read:

    U(ξ) = (n.choose 2:ℝ)⁻¹ * unorderedPairSum Hξ,
    rowMean(Hξ,i) = ((n:ℝ)−1)⁻¹ * ∑(j≠i) Hξ(i,j),
    R2(ξ) = 4*((n:ℝ)−1)/((n:ℝ)−2)^2
             * ∑i (rowMean(Hξ,i)−U(ξ))^2,
    T(ξ) = if 0<R2(ξ) then √(n:ℝ)*U(ξ)/√R2(ξ) else 0.

This expanded `T` is the original physical finite-row statistic requested by the task. There is no imported definition actually named `physicalFiniteRowsT` in the curated OQ6 snapshot; the proposed head deliberately retains170's full literal expression instead of introducing an unreviewed alias or new public value. The coefficients, unordered off-diagonal pair count, excluded diagonal, centered rows and positive-square guard remain exact.

The expression T uses only n,h and the sample values. It has no occurrence of μ,μ₀,mΩ,m₀,g,r,v, a clipping budget, or a canonical coding witness. Consequently the170 coarse T and the proposed original T are the SAME total function on the SAME underlying type `Fin n → Ω`; their U,R2,q expressions are literal identical. This is a pointwise identity on every sample, not merely an equality in distribution or an almost-everywhere denominator identity.

For n≥3, the coefficient of the squared centered-row sum is nonnegative and its denominator is nonzero; hence R2≥0. The existing guard therefore gives exactly T=0 when the physical jackknife square is zero, independently of the sign of U. If the square is positive, it is the usual physical Studentized U-statistic. In p51 S1 notation, R_h=2*s_phys and √n*U=2*(W+D), so the nonzero branch is (W+D)/s_phys; the zero branch agrees as well. The public rate's s=1+rho is a DIFFERENT fixed model scale, not this sample denominator.

No projection-energy-zero event is identified with the physical-jackknife-zero event. No guard is replaced by a clipped V=0 guard. Any mass on either such set, and any equality atom at a threshold, is retained by the identical total function.

## Route E: generic finite-J law and all four original event probabilities

Fix any n≥3. Specialize ONLY221's generic finite-J clause to J=Fin n and B=ℝ with Borel measurable structure. Its generic v,w universes can be instantiated at0; Ω stays at u. Let mN and Pₙ use mΩ/μ; let mN₀ and Pₙᶜ use m₀/μ₀. The170 conclusion supplies

    hT₀ : Measurable[mN₀,borel ℝ] T.

221 supplies measurable id:(mN)→(mN₀), so hT₀ composed with id proves

    hT : Measurable[mN,borel ℝ] T,

which is the public ORIGINAL-space measurability conclusion. Apply221's generic target law to that SAME T and hT₀:

    @Measure.map (Fin n→Ω) ℝ mN₀ (borel ℝ) T Pₙᶜ
      = @Measure.map (Fin n→Ω) ℝ mN (borel ℝ) T Pₙ.

This clause has no lower bound on n at all, so it is available at n=3. In particular no specialized n≥4 centeredT output is being used covertly.

For any real x, all four intervals Iic(x), Iio(x), Ioi(x), Ici(x) are Borel measurable. Evaluate this exact measure-law equality on each interval. On each side use `Measure.map_apply` with the corresponding hT₀ or hT and the Borel-set proof. This yields equal ENNReal probabilities of the corresponding preimages. Apply ENNReal.toReal, which is the definition used by `Measure.real`, to obtain the four exact equalities

    Pₙᶜ.real {ξ | T ξ ≤ x} = Pₙ.real {ξ | T ξ ≤ x},
    Pₙᶜ.real {ξ | T ξ < x} = Pₙ.real {ξ | T ξ < x},
    Pₙᶜ.real {ξ | x < T ξ} = Pₙ.real {ξ | x < T ξ},
    Pₙᶜ.real {ξ | x ≤ T ξ} = Pₙ.real {ξ | x ≤ T ξ}.

The set identities are precisely T⁻¹(Iic x), T⁻¹(Iio x), T⁻¹(Ioi x), T⁻¹(Ici x). Both domain measurable structures and both actual product measures remain explicit in the eventual terms. These equalities are valid at every x, before imposing x∈[0,1].

Replace the four coarse probabilities in170's four inequalities by these equal original probabilities, and replace β₀,v₀ by β,v. Keep170's same K and its hT conclusion after composition. This closes the proposed mathematical route.

No probability-continuity, limit exchange, reflection, complement subtraction, zero-set payment or atom-free premise is needed in this wrapper. Each strict/closed event is transported directly as a Borel preimage. The endpoints x=0 and x=1 therefore require no separate unstated exception. Existing170 already supplies its four inequalities at both endpoints, including its independently verified zero convention.

## Boundary and quantifier audit

| Item | Exact treatment |
| --- | --- |
| n=3 |170 explicitly covers it;221 generic J covers it; n−2=1; no n≥4 specialized clause is called. |
| n=0,1,2 |Not in the proposed conclusion; no claim is made. |
| p=2 |Excluded by the unchanged strict 2<p rate hypothesis. No endpoint extension is proposed. |
| p=3 |Included; F is continuous for nonnegative p and all law/integral equalities are exact. |
| x=0, x=1 |Each of four Borel-interval equalities applies directly; inherited170 includes both. |
| Zero physical denominator |Same total function with positive-R2 guard and zero else branch under both laws. |
| Projection zero |Not equated to physical R2=0; no probability is removed. |
| Atoms/ties/diagonal h values |No atomlessness; all strict/closed endpoints retained; finiteRows excludes diagonals exactly as before. |
| Arbitrary Ω |No standard-Borel/separation/countable-generation/nonempty assumption is public. An empty space cannot carry the given probability instance, without any additional premise. |
| K and witnesses |One common m₀,μ₀, then one K before all n/x; no dependence of K on n or x. No stronger uniformity is asserted. |
| p-moment |Genuine original hgp, genuine coarse hgp₀, exact β₀=β; no totalized nonintegrable-integral shortcut. |
| Measure instances |Original `mΩ`/μ/π values captured explicitly, local coarse instances used only in the170 call and its coarse facts. |
| External input |Exact broader L² CDF Prop hSZC; tail hSZ alone is insufficient and is never used as a replacement. |

## Remaining gaps and required next action

No new mathematical premise or unresolved mathematical transfer lemma has been identified in the route above. In particular genuine p-moment integrability, equality of beta, preservation of residual scale, original measurability, n≥3 and all four exact original event laws have explicit derivations. This is a proposal bearing argument, not an independently accepted proof.

The concrete remaining obligations are:

1. The parent must decide and freeze the complete proposed head/preamble/closing before implementation. This author has no declaration-freeze authority and does not claim the head is already frozen.
2. A new explicit implementation activation is required. Only then may the same sole author write a proof source. Exact universe instantiation, nested conjunction extraction from221 and explicit instance arguments remain unelaborated Lean obligations. The named `integrable_map_measure`, `integral_map`, `Measure.map_apply` and composition calls above describe the needed interfaces, not a claim that an unrun term has been accepted.
3. The new proof must receive one qualified independent COMPLETE source-to-statement/proof review, including the measure-instance captures, total projection equality, p-integrability chain and all four law joins. Accepted unchanged221/170 proofs and their source-bound evidence are reused exactly. A mere parent proposal read is not that independent final review.
4. The new exact proof source must receive designated-server native kernel success and same-FIRSTO actual all-owned TYPE/required VALUE/transitive-axiom audit under the current lane resource gates. No local Lean, version probe, server call, source upload or audit was performed in this proposal.

If a later elaboration issue appears, it is not authorization to add a new public countability, moment, atomlessness, n≥4 or desired-event premise. The author must repair the expression within the parent-frozen statement or report the exact missing interface to the parent. New constructive proof-body data will also require the project's normal freeze discipline before their implementation.

Full OQ56/root, external scalar-input existence/proof, unbounded/growing or relative-tail ranges, p54 conditional-family uniformity/strict-upper margins, DC and source-wide original research closure remain OPEN. No novelty or priority certification is claimed. Historical other-lane statuses in the reused old review documents are archival evidence, not new runtime directions.

Requested model/effort: gpt-6.1-sol/xhigh. Actual backend/model/effort telemetry is unexposed and recorded null. Input, cached-input, output and reasoning-subset counts are separately null; no token or subscription allocation is invented. No child, chat, Goal or schedule was created. No network/Git/API/publication operation occurred.

The final `PROPOSAL-READY.json` is written last and binds the manifest. It records writer/heavy/inflight/pendingExternal/uncertain/children all zero and an idle, still-exclusive unit264 author role. It is not a release of that role, not a mathematical qualification, and not a persistent continuation mechanism.
