# Unit283 mathematical fidelity trace

STATUS: DECLARATION_PROPOSAL_ONLY. This is the author's source-to-statement trace, not independent acceptance, a proof, Lean elaboration or qualification.

The complete primary p41 and p51 texts were read. p41 section5 L253 conditions on all exceptional observations O_a, not only their envelope values. The full observation determines r(O_a,o), g(O_a), w(O_a), c_A and the actual interaction. p41 section6 subsequently integrates those actual values. Existing281 exposes the background marginal under one mixed membership mask, which is insufficient by itself to identify these sections. The proposed joint pushforward and inverse reconstruction supply this specific transport gap.

| Source object | Literal proposed counterpart | Fidelity obligation |
| --- | --- | --- |
| Original iid observations | `Measure.pi (fun _ : Fin n => μ)` | μ is the original probability law on an arbitrary measurable Ω. |
| Background B, exceptional A=B complement | `B` and `(Bᶜ : Finset (Fin n))` | No exceptional coordinates omitted. |
| Fixed arbitrary enumerations | eB/eA equivalences with the entire two subtypes | Neither increasing order nor sample-dependent selection is required. |
| Actual two vectors | `splitSample B eB eA x` | First background, second entire anomalous observation vector. |
| Original observation recovery | `joinSample B eB eA (b,a)` plus T01/T02 | Every original coordinate returns to its position. |
| Mixed membership event | Existing281 `fixedMaskEvent C B` | All B coordinates in C and all complementary coordinates in C complement. |
| True retained law | `(μ C)⁻¹ • μ.restrict C` | Actual normalized restriction, not a postulated replacement law. |
| True anomalous law | `(μ Cᶜ)⁻¹ • μ.restrict Cᶜ` | Retains entire observations, including g, w and r dependence. |
| Positive mask | T07 and T11 actual full-mask nonzero guard | No forall-mask or both-single-coordinate positivity strengthening. |
| All masks | T08/T09/T10 without nonzero guard | Original actual mask mass multiplies the full product/section integral. |
| Conditional interaction section | `backgroundSection B S a`, or `{b | joinSample ... (b,a) ∈ T}` | a is fixed as a full vector while background alone is integrated. |
| Integrate all anomalous values | Outer integral against Fin(card complement) product of anomalous conditional law | Inner background probability, outer entire anomaly vector, both in ENNReal. |
| Product-a.e. envelope | T11 anomaly-a.e. background-a.e. predicate | The result cannot be read as forall anomalous values. |

All finite lengths and both empty blocks are included. B=univ leaves a singleton empty anomaly-vector space with its empty product measure; B=empty does the same for background. For n=0 both blocks are empty and their product still has total mass1. If μ(C)=0 or μ(C complement)=0 while a corresponding block is nonempty, the mixed mask may have zero mass. T08/T09/T10 remain weighted zero identities. Empty exponents and empty products follow existing281/Pi conventions, retaining 0^0=1 rather than cancelling undefined scalar expressions.

T11 needs its positive mask guard: from an a.e. property under a zero restriction one cannot infer an a.e. property for a possibly nonzero conditional block product. It retains a measurable predicate Q as the event-level measurable interface. It does not assert that every concrete anomalous observation satisfies the envelope, nor does it replace actual anomalies by independent samples after their values are fixed. It is a law-level transport statement and makes no regular conditional distribution existence assertion.

No StandardBorelSpace, atomlessness, continuity, RCD, stronger sigma-algebra, or additional model moment condition is present. p51 S1 explicitly explains why arbitrary original measurable spaces must not silently be strengthened. This finite split needs none of the standard Borel coding used in p51 S4. The first projection, residual and envelope remain the original ones when a later consumer instantiates T with their actual measurable event.

The generic transport statements do not introduce a new physical-statistic formula. Qualified279/281 original denominator n-2, background scaling, genuine centered-row studentizer, m>=4 physical domain, sB=0 guard and closed-tail convention stay in the event passed by the later consumer. The transport itself has no m>=4 premise because any measurable finite-coordinate event is covered, including empty blocks. This does not extend the physical geometry below its qualified domain.

The target has no tail constants and does not claim (14), (15), (16), (20), (21) or PE-R/PE-L. In particular it has not established c_A's mean/variance bound, a section-uniform Bernstein estimate, actual Delta absorption, or low-sB control. Those source-bound dependencies remain separate. It supplies the full observed-value integration bridge needed before those a.e. section estimates can be used honestly.

The public existing coordinate conditional joint producer is reused as the sole conditioning input. Existing281 exact selected actual TYPEs and fixedMaskEvent VALUE were read from its qualified owner metadata, as were their source declarations. Existing279 backgroundSample's source fixed RHS and complete selected actual TYPE/VALUE were read. Three supplemental pinned primary API packets supply complete bearing contexts. The underlying Equiv split literally restricts the original function to predicate/negated-predicate coordinates; measurable piCongrLeft enumerates subtype vectors in the direction specified by its apply_apply theorem. The complement subtype and the negated-membership subtype are connected by exact Finset.mem_compl, not by deleting observations. Measure.prod_apply_symm has precisely outer second-factor and inner first-factor order, and Measure.ae_ae_comm preserves the two a.e. quantifiers. None of this repeats independent old proof review or changes accepted evidence. The new packet remains for parent freeze and later fresh independent review and server kernel/all-owned-axiom certification.
