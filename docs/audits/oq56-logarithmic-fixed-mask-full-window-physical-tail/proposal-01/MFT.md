# Unit282 mathematical fidelity trace

STATUS: DECLARATION_PROPOSAL_ONLY. The trace compares the complete proposed statement with the primary sources and exact qualified supplier interfaces. It is not an independent correctness certificate or mechanical proof.

## Source-to-target chain

p41 section2 defines hB=g+g'+((m-2)/(n-2))*r, NB and sB. p51 S1/S6 retain the genuine centered-row studentizer, its zero convention, conditional projection, nonzero kernel mean and uniformity over m in[n/2,n] and lambda in[0,1]. Qualified276 already supplies that conditional model and a full uncentered closed-tail bound on z>=1. Qualified279 identifies the reindexed finite physical statistic with the original NB/sB formula at m>=4. Qualified281 supplies the genuine fixed mixed-mask conditional/restricted law and original closed-tail intersection. Proposed282 transports276 through281 without reconstructing the model.

## Literal global hypotheses

| Proposed prefix | Exact requirement retained from276 | Use and fidelity |
| --- | --- | --- |
| Omega : Type u, MeasurableSpace Omega | Arbitrary measurable observation space | No standard-Borel or countable-generation strengthening. |
| mu, IsProbabilityMeasure mu | Original observation law | Pn is its n-coordinate product; no new background law is postulated. |
| h, hh | Real product-measurable kernel | Parameter projection/residual measurability follows from this prefix. |
| hh2 | MemLp h 2 under mu.prod mu | Retained even though the transport algebra alone is simpler. |
| hhsymm | Pointwise h symmetry | Retained; derives pointwise r symmetry required by physical281. |
| hcenter | Original full kernel integral0 | Not replaced by a conditional-zero-mean premise. |
| hprojectionsecond | Actual original projection second moment1 | No fresh projection normalization or variance assumption. |
| w, hw, hwone | Measurable envelope,1<=w mu-a.e. | Exact source strengths; no everywhere envelope upgrade. |
| alpha,tau,hAlpha,hTau,hwexp | Both positive and exp(tau*w^alpha) integrable | Conditional theorem keeps arbitrary alpha>0; no unconditional PE-R claim for arbitrary alpha. |
| henvelope | Product-a.e. absolute residual bounded by w*w' | Original residual h-g-g' under mu, not conditionally canonical residual. |
| p,hp,hgp | 2<p<=3 and original projection p-moment finite | Same p and beta in rate. |
| J,hJ | J>=1/2 | Same polynomial truncation parameter and A. |
| cSZ,C1,C2,C3,C4,hSZ | External finite-cost tail input | Separate explicit contract, not proved to exist here. |
| CCDF,hSZC | External finite-cost CDF input | Separate explicit contract, not inferred from hSZ. |
| t0,ht0 | t0>0 | Passed unchanged to276; no dropped global premise. |

A deterministic prefix comparison checks that the exact lines after the theorem name through ht0 in T02 equal those in the bound complete276 public HEAD. The display table uses readable labels for hAlpha/hTau only; the literal HEAD uses hα/hτ exactly.

## Exact values and quantifiers

| Object | Proposed exact expression or quantifier | Source/fidelity |
| --- | --- | --- |
| g | Integral h(o,y) under original mu | The original true projection; no new definition. |
| r | h(o,y)-g(o)-g(y) | The original residual, not assumed canonical under nu_n. |
| beta | Integral rpow(abs(g),p) under mu | Same global p-moment as276. |
| A | 2*(J+1)/(1-2/p) | Exact276 A after substitution of its local e. |
| qpow | (p-2)/(2*p) | Original full conditional-window exponent. |
| c,K,N | Exists c,K with0<c,0<K, then exists N>=8 | One application of276 chooses the same witnesses, before all n,B,e,z. |
| n | All naturals n>=N | Original n appears throughout cutoff, window and rate. |
| Rn,Cn | rpow(A*log(n)/tau,1/alpha), {w<=Rn} | Original logarithmic cutoff; measurable Cn retained. |
| dn,nu_n | mu.real Cn, (mu Cn)^(-1) smul mu.restrict Cn | Same true probability conditional law; dn>=1/2 retained. |
| Pn | Pi over Fin n of original mu | Actual original n-dimensional ambient law. |
| B,e | All Finsets of Fin n and all Fin(cardB) equivalences with B subtype | No preferred enumeration and no data-selected mask. |
| size | n<=2*cardB and cardB<=n | Both retained explicitly; m>=4 is derived and returned. |
| lambda | backgroundScale B=(cardB-2)/(n-2) | Exact n-2 denominator, shown in[0,1] with n>=8,m>=4. |
| P | Pi over Fin(cardB) of nu_n | Existing276 conditional product, transported by281. |
| z | All reals1<=z<=c*rpow(n,qpow) | Closed original full conditional window. |
| error | beta*rpow(1+z,p)*rpow(n,-(p-2)/2)+(1+z)^3/sqrt(n) | Same n, beta,p and powers. |
| final payment | Pn.real(E)*K*error | Zero-weight-safe direct multiplication; same K. |

The source contains a real local B=beta^(1/p) and a real local e=1-2/p. The proposed statement does not need these unused local names: A substitutes the latter RHS exactly, and its B/e binders are the finite mask and enumeration. No global hypothesis, witness order, value or rate is altered by omitting unused local intermediate names.

## Definition and event correspondence

T01 explicitly writes H, sampleH, U, RH and Tuncenter. The sampledKernel RHS is g(x_i)+g(x_j)+r(x_i,x_j), and scaledResidual B r is backgroundScale B*r. Substitution therefore gives exactly H at each pair. Both physicalStatistic and Tuncenter test the same RH=0 and return0; otherwise both are sqrt(m)*U/RH. This is a literal formula interface at every finite m, not a lower-denominator estimate or a new finite NB/sB theorem.

The main event is the supplier281 originalBackgroundClosedTail. Its fixed RHS tests the original backgroundStudentizer B; at0 it returns0 and otherwise uses original backgroundNumerator B divided by that same studentizer. Its intersection with E is under Pn. The m-coordinate backgroundClosedTail is only the conditional supplier event consumed after the exact281 bridge. It is not substituted for the original event by assertion.

fixedMaskEvent is an intersection over all n coordinates: B coordinates lie in Cn and complement coordinates lie in Cn-complement. Its mass is dn^m*(1-dn)^(n-m). Thus this is a mixed mask, not the m-dimensional allGood event from276. The proposed intersection law uses281 to establish that difference rather than relabeling276's Pmu/allGood ratio.

## Zero, atoms and range checks

The core bound subtracts Pn.real(E) and never divides by that weight. For zero mask weight it remains a zero identity/bound. No forall-mask positivity premise is hidden. The statements preserve n=m, complementary empty blocks and exponent0 conventions from281. B.card>=4 follows from n>=8 and the half-sample inequality, so original physical geometry does not cross its qualified boundary.

The RH=0 and sB=0 guards are exact; closed z is exact. No continuity, atom-free law, almost-sure positive denominator, or strict-to-closed conversion is assumed. Source276's max(2,z) good events, centered shifts and their payment have already been discharged inside its accepted uncentered estimate and are not reimplemented here. This proposal transports only z>=1.

The sole pointwise symmetry requirement in the main theorem is original hhsymm, copied from276. It implies r symmetry needed by281. T01 has no symmetry premise because only definition substitution is involved. No conditional canonical residual or IID anomalous/background coupling is silently introduced.

## Full interface coverage and evidence reuse

The selected276 complete actual TYPE was read through the lossless lexical dictionary plus encoded entire type; complete279 and281 selected TYPE/VALUE were read literally. No unshared binder, universe, instance, dependent let or target was omitted. Reconstruction to the original276151780B stream passed. The original TYPE streams and source/evidence hashes remain bound in BEARING-API-BINDINGS.json. This is complete interface reading, not a repeat independent review of old proofs.

The original22 activation inputs remain unchanged. Three later supplemental qualification inputs establish281 qualified status, separately counted. Parent reports and qualified first-object evidence for276/279/281 are reused exactly. No old producer, theorem proof, source build or leafAX is replayed. Two proposed source theorems are not an actual compiled-owner inventory; actual owner/TYPE/VALUE/AX counts stay null until separately authorized execution.

## Accepted scope and open scope

This proposal would consume accepted conditional model/tail and exact finite physical/mask transport to obtain one fixed-mask, weighted original closed-tail error. It does not establish all-mask summation, random selection, full anomalous-value conditioning/Fubini, cross-interaction/Delta concentration, low sB control, rareblock exponential integration or large-KQ payments. It does not establish external hSZ/hSZC existence, unconditional PE-R/PE-L/NR/DC, full OQ56 or root completion. Qualified276's true conditional projection/variance/commonN stay accepted; the open status concerns this consumer and the broader original application.
