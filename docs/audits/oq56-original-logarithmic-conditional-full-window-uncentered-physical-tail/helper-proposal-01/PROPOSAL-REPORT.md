# Frozen276: closed private helper proposal and complete proof plan

Status: PROPOSAL_ONLY_NOT_FROZEN_NOT_IMPLEMENTED. Three exact additional private HEADs are proposed in PROPOSED-HELPER-HEADS.json. No new helper proof body, main proof body, executable Lean source, standalone helper check or prefix check is supplied. The parent must separately freeze approved HEAD bytes and activate implementation. Mathematical and machine qualification remain false.

The main HEAD is the exact 7086-byte/121-LF declaration with SHA256 `3c5d8ae17cfe31959ce0e5dbc03cd36655ac022b2850adce1e07868c68de085d`; PRE and CLOSE remain exact. This explicit main freeze supersedes the historical prospective notes saying main276/qualified275 were pending. Accepted273/274/275 evidence is reused, with no automatic old proof or all29 actual275 TYPE review. The actual public275 TYPE1116–1419 was fully read, in addition to its47-LF source HEAD. All27 activation bindings were verified before first write. Only the new helper-proposal-01 directory is writable.

## Proposed declarations and why these three

1. `half_sample_and_mean_rate_bounds`:9 LF,449 bytes, SHA256 `dd2be13af6b0f11717eee863a6db219457b227a901311790a326a33bf2c668d8`. Its explicit real parameters are p,J,Kmean, with exactly p in(2,3], J>=1/2 and Kmean>=0; its natural parameters require only n>=1 and n<=2m. It packages the three substantive repeated scale bounds needed for actual275, centered273 and the original mean shift. The unused m<=n premise is deliberately absent from this helper; it remains present in the public main.
2. `eventual_near_window_and_exception_rate`:9 LF,427 bytes, SHA256 `fe4bcb9b1426c37b172c715b9adea4a1e95eca3f1a1abe2fa800fc678d47a59b`. Its parameters are p,t0,ccenter with p>2,t0>0,ccenter>0. It returns one N>=8, before all n and m, ensuring centered window height3 and the exceptional exponential <=2/sqrt(n) uniformly for every m>=n/2. It needs no model, lambda,z,p<=3 or artificial variance budget.
3. `near_closed_tail_sandwich_and_rate`:21 LF,1191 bytes, SHA256 `49cac5d0a8f372a1ac0ab2ab28bd2ab8c4ee01bc0dc8f5134152a1d94970006e`. Universe u and every type, measurable-space, probability-measure, function, set, scalar, nonnegativity and range parameter are explicit. It combines the two needed closed-event sandwiches and the compact relative bound in one lemma. Its local centered closed-tail certificate is proved in main from actual public275 and273 outputs, as detailed below. It is not a new public/external CDF premise and cannot be left unproved at the call site.

No wrapper for the already-public275 uniform existential, the Gaussian representation/Lipschitz result, the original conditional-law identity or the elementary max(2,z) split is proposed. Those are direct public applications/local steps. H3 combines event comparison and its numerical consequence so that two nearly identical measure-algebra bodies are not introduced. H1 and H2 remove scalar reasoning from the large original-model binder telescope. These are implementation seams, not new mathematical claims of independent value.

The proposed source order is the existing frozen private finite bridge, H1, H2, H3, exact frozen public main, then exact CLOSE. H1–H3 have no cyclic dependency. Only the main uses their combined outputs. The existing PRE already opens the intended P51 namespace; no new import or option is proposed.

## Original-model constants and public existential order

Write a=(p-2)/2 and q=(p-2)/(2p). Call public273 with J>=0 derived from the frozen J>=1/2, retaining all original assumptions and external tail input hSZ. Its returned constants ccenter,Kcenter and threshold Ncenter precede n,lambda,m,z. Call public274 under its exact frozen assumptions, obtaining c274,K274,N274 and its full original-model package. Its prefix supplies beta>=1,A>0,cg>0; its probability/statistic/law package precedes its z>=2 clause and is therefore available even when the new target z is near1.

Eliminate the actual PUBLIC275 existential at Bclass=2*beta, using 1<=2*beta. Obtain Kcdf>0 BEFORE any conditional model nu_n,lambda,m or compact level is instantiated. The public TYPE is an existential K with a property for all models; it exposes no equality to the source-chosen explicit K formula. This plan uses only that public existential. It neither calls a private275 helper nor infers a hidden witness formula. The external hSZC is distinct from hSZ and is kept as a separate public276 hypothesis; neither contract's existence nor a relation between them is proved.

Use the actual fixed source expressions

    RhoBound = 4*Cenv^2*M2^2,
    S = 1 + sqrt(RhoBound),
    E = beta*rpow(n,-a) + 1/sqrt(n),
    D = (4+2*S)*Kcdf + 64*Kcenter,
    Ddelta = 2*Kmean,
    Knear = (D+2*Kmean)/Psi(2) + 2,
    Kfull = 1+K274+Knear,
    cfull = c274.

Here Psi is the actual Shao.standardNormalTail. S is not a free variance budget: qualified273 gives actual rho_std<=sqrt(RhoBound). All occurrences of beta,Kmean,Cenv,M2 and the conditional model are the frozen original lets. Kmean>=0 follows from beta>=1, nonnegativity of the rpow/integral expressions and squared W2, not an added main assumption. Public Gaussian basic gives Psi(2)>0. Hence D>=0,Ddelta>=0,Knear>0,Kfull>0 and cfull>0. Kcdf was selected uniformly in the class before model instantiation, while S is the legitimate fixed original-family bound.

## H1 proof plan: finite scale factors and delta

The assumptions give0<a<=1/2, n>0,m>0 and m>=n/2. Monotonicity of the negative power gives

    m^(-a) <= (n/2)^(-a) = 2^a*n^(-a) <= 2*n^(-a),

since a<=1. Also sqrt(n)<=sqrt(2)*sqrt(m)<=2*sqrt(m), so1/sqrt(m)<=2/sqrt(n). For n>=1 and J>=1/2, n^(-J)<=n^(-1/2)=1/sqrt(n); multiplying by nonnegative2*Kmean gives the third output. Every cancellation uses positive n,m or their square roots. No asymptotic statement is used in H1.

At the actual standardized model, beta_std<=2*beta and1+rho_std<=S. Convert the public275 denominator form beta_std/rpow(m,a) to beta_std*rpow(m,-a) using m>0. H1 then bounds its error by

    Kcdf*(4*beta*n^(-a)+2*S/sqrt(n))
      <= (4+2*S)*Kcdf*E.

The same H1 gives delta_n=2*Kmean*n^(-J)<=2*Kmean/sqrt(n)<=Ddelta*E. E>=0, and the actual274 common threshold already gives0<=delta_n<=1/2.

## H2 proof plan: one uniform common threshold

q>0 follows from p>2. An elementary explicit threshold construction suffices; no exponential-rate supplier beyond scalar real analysis is assumed. Put C=216/t0^3>0 and choose a natural N at least the ceiling of

    max(8, max((3/ccenter)^(1/q), C^2)).

For n>=N, positive-base power identities yield3<=ccenter*n^q and sqrt(n)>=C. For any n<=2m, set x=(t0/2)*m^(1/3)>0. The scalar inequality1+y<=exp(y) at y=x/3, cubed and combined with the exponential addition identity, gives exp(x)>=(x/3)^3=x^3/27. Since(m^(1/3))^3=m,

    exp(-x) <= 216/(t0^3*m)
      <= 432/(t0^3*n) = 2*C/n <= 2/sqrt(n).

This proves exactly the H2 output, uniformly in m. The larger harmless threshold constant216 does not change the frozen displayed error or exceptional payment. No threshold is selected after lambda,m or z.

Choose common N=max(N274,max(Ncenter,Nnear)), with Nnear from H2. It is >=8. N274 preserves the original window containing2, cutoff/conditional-probability properties and delta<=1/2. Ncenter preserves the full centered model. Nnear raises the centered window to3 and gives the exponential-to-E comparison. There is no275 model-dependent N because public275 already holds for every sample size >=3.

Exact pinned Mathlib spellings for elementary rpow identities, the exponential lower bound and the ceiling inequalities have not been checked here; only a proposal, not an implementation or machine result, is authorized. The derivation above supplies the mathematical route without treating guessed Lean names as verified suppliers. If implementation chooses another Shao lemma instead, its exact public source/hash must first be bound and read. No missing Shao-level mathematical interface was found in the27 supplied inputs.

## Actual closed centered-tail certificate on[1/2,5/2]

Fix n>=N, a legal lambda, and m with n<=2m<=2n. Extract the same actual conditional standardized model from273 and the physical uncentered/statistic/law package from274. They have identical fixed original lets; do not create a new law or alter the model. Qualified273 provides actual Hstd measurability,L2,symmetry,mean0,unit projection second moment,p-moment integrability,beta_std<=2*beta and the actual residual rho bound. Instantiate the public Kcdf property at nu_n,Hstd,m; m>=4 supplies its m>=3 condition.

The existing frozen private finite bridge, applied to Hstd with its actual gstd and rstd, identifies the275 physical statistic guarded by0<R2 with Tstd guarded by sstd=0. The public273 pointwise identity Tcenter=Tstd then identifies this actual event with the original Tcenter event for EVERY sample. This is exactly where the pointwise finite bridge is needed. There is no replacement of actual gstd by its AE projection formula, and no AE-to-pointwise upgrade.

For1/2<=v<=1, take275's FOURTH conjunct, the closed upper tail `{v<=T}`. Use the public Gaussian representation and the definition of standardNormalCDF to replace1-CDF(v) by Psi(v). H1 and the actual rho bound give absolute error <=(4+2*S)*Kcdf*E. This step never converts a strict physical tail to a closed tail or discards an atom.

For1<=v<=5/2, H2 supplies v<=3<=ccenter*n^q. Apply public273's original centered relative tail at v. Psi(v)>0 and Psi(v)<1 convert it to an absolute error with no factor larger than1. Because1+v<=7/2<4 and p in(2,3], both(1+v)^p and(1+v)^3 are at most64. The result is <=64*Kcenter*E.

Split at v<=1; the equality v=1 can legally use either public bound and is covered by the first branch. Nonnegativity of both coefficients then yields the one local certificate

    forall v in[1/2,5/2],
      |P.real{v<=Tcenter}-Psi(v)| <= D*E.

This is H3's hcenter argument. It is constructed from the qualified public suppliers, not added as a desired-CDF assumption. The generic private helper's hbad,hshift,hdelta-rate arguments are similarly instantiated by actual274,H2,H1; none becomes a new public276 parameter.

## H3 proof plan: closed-event comparison and legal Gaussian normalization

Let z in[1,2] and use the actual274 good set at legal level2. Pointwise |Tuncenter-Tcenter|<=delta gives the literal closed inclusions

    {z+delta<=Tcenter} subset {z<=Tuncenter} union Hgood-complement,
    {z<=Tuncenter} subset {z-delta<=Tcenter} union Hgood-complement.

Measurability and finite real-measure monotonicity/union bounds give the exact two H3 sandwich outputs. Each side uses ONE exceptional mass. There is no unproved atom-free exchange; all inequalities at the event boundaries are non-strict. The case delta=0 is included.

Both shifts z+-delta lie in[1/2,5/2]. Public `Shao.standardNormalTail_representation(v).2.1` equals1-cdf(actualGaussian)(v), and the public standardNormalCDF definition identifies that cdf. Public `Shao.OQ4.standardNormalCDF_lipschitz` therefore gives

    |Psi(v)-Psi(z)| <= |v-z| = delta

at each shifted level. No new derivative, density bound or separate Gaussian wrapper is needed. The local centered certificate and delta<=Ddelta*E bound each shifted mass's absolute deviation from Psi(z) by(D+Ddelta)*E.

Public standardNormalTail_basic gives qz=Psi(z)>=Psi(2)=q2>0. Nonnegative exceptional mass and hbad give bad/qz<=bad/q2<=2*E. Divide the two one-sided sandwich errors by qz, use D+Ddelta>=0 and E>=0, and combine them into

    |P.real{z<=Tuncenter}/Psi(z)-1|
      <= ((D+Ddelta)/Psi(2)+2)*E.

The +2 comes from the bound on a single bad mass; it does not double the event comparison fee. E=0 causes no division by E and is covered. The positivity used for division is exclusively the actual Gaussian tail's positivity.

## max(2,z), far levels and exact original conditional ratio

For every new legal z>=1, let y=max(2,z). The274 prefix guarantees2<=c274*n^q, while the new target gives z<=cfull*n^q with cfull=c274. Hence y is legal for274. Its good set and its exact3+1+4 payment are precisely the frozen276 Hgood/payment, including the third exponent evaluated at max(2,z).

Since z<=y, actual Gaussian antitonicity gives Psi(z)>=Psi(y)>0. Thus the274 bad-payment relative bound at y also holds at actual z with the SAME exponential right-hand side. The absolute payment and pointwise RH/shift bounds are copied from the public274 output for that actual good set.

If z<=2, y=2. The just-obtained bad/Psi(2)<=exp[-(t0/2)*m^(1/3)] combines with H2 and1/sqrt(n)<=E to give H3's bad/Psi(2)<=2E. Apply H3 to obtain the newly needed z-level sandwiches and near error. At z=2 this branch remains legal.

If z>=2, y=z. Simplify max(2,z) and reuse the public274 sandwiches and full displayed relative bound without reconstructing its accepted proof. A split at z<=2 covers all real z>=1, including the boundary2.

For z>=1, E is bounded by the frozen displayed error

    beta*(1+z)^p*n^(-a) + (1+z)^3/sqrt(n),

using p>0,beta>=0 and nonnegative n powers. Kfull>=Knear and Kfull>=K274 absorb both cases. The constants and common N were fixed before all n,lambda,m,z.

Finally the measurable event `{z<=Tuncenter}` can be substituted into274's PUBLIC exact conditional-law identity

    P.real E = Pmu.real(E intersection allGood)/dn^m.

This yields the last frozen normalized-ratio clause by equality. It gives no unrestricted original-Pmu tail. All probability, measurability, cutoff mass, original mean bound and scale identities required earlier in the121-LF HEAD come from the same public273/274 packages; no new premise is introduced to recover them.

## Preserved finite bridge and future integration gates

The finite bridge's exact mathematical HEAD and complete static author proof remain unchanged in their sealed directory. PROPOSED-HELPER-HEADS.json records ONLY a possible future-copy deletion of the historical marker comment at old PROOF line2, `-- FINITE_ONLY_SCRATCH_NOT_CHECKED_NOT_MAIN276`. No removal or future-copy write has occurred. The predicted comment-only copy has74 LF,2959 bytes, SHA256 `b91f24e6f03eb91a0e767baf9be317672027a7b72dc7073049eb83a6692b0c09`; all other proof bytes are retained. Parent implementation activation must explicitly decide this copy operation. Old manifests, LAST, source bytes and static receipts remain untouched.

Future complete SOURCE review must cover the whole bridge in its changed import/binding context, all newly authorized bodies, the exact main proof and its original source scope. Later server native/all-actual-owner/recursive-axiom checking remains required under the existing limits. No standalone helper or prefix acceptance is planned. Proposal text and deterministic static checks do not establish elaboration, kernel acceptance, actual ownership or independent correctness.

The proposal retains p54 eventual2beta repair; external hSZ/hSZC attribution; actual rho rather than a free variance budget; original max-level good-set fees; closed atoms and zero-denominator conventions; common-N order; and original conditional rather than unrestricted Pmu scope. NRPE/DC, external contract existence and all wider OQ56/root closures remain open.

No Lean/toolchain probe, AX, server/SSH call, transfer, network, Git/API publication, child, Goal, schedule, sidebar, proxy or resource change occurred. This role is prescribed gpt-6.1-sol/xhigh; actual backend/model/effort and input/cached-input/output/reasoning-subset counts are unexposed null. Final unique LAST releases all assigned author/write/review/execution/child/publication authority, six runtime counts are zero and no active wait remains.
