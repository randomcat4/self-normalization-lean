# Terminal normalization P2 and conditional common-M Lemma K

AUTHOR_STATUS: PROVED at the mathematical-proposal level from the exact producer contracts below. This is neither a parent declaration freeze nor implementation, independent review, Lean/kernel qualification, or acceptance. Author154 uses the prescribed gpt-6.1-sol/xhigh and math-theorem only. No Lean, import/object/toolchain probe, build, remote request, Git operation, or production mutation was run. Only this owned proposal directory is written.

## 1. Exact source, quantifiers, and status

The original read-only source is C:/game/shao/current/oq4/b01/proof01.md, SHA256 7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38. Its lines9–36 and316–351 were read in full. The target is the common-M varying-row sequential conclusion of K, via its actual normalized terminal-block P2. A single fixed-law conclusion would not cover it. The parent intake d00b25aa95ece57f99b4c8f42e31343b437f271957ccccb064a8545bcad3140d was read in full as intake, not independent evidence, and the argument below checks each step against actual producers.

For every natural j let nu_j be a real Borel probability measure, with the supplied instance p_j=hprob j. Assume, for every j,

    x |-> |x|^3 is integrable under nu_j;
    integral x dnu_j=0;             integral x^2 dnu_j=1.

The first line means Integrable (x |-> |x|^3) nu_j, not merely a finite value of Lean's totalized integral. Write beta_j=integral |x|^3 dnu_j. Fix ONE real M with beta_j<=M for all j. Fix common real Cq,Cs>=0 and retain literally, for every j,

    iidIntervalConcentration nu_j beta_j Cq;
    iidOneSidedSurvival nu_j beta_j Cs.

These are the actual all-positive-time product probabilities defined in KilledBlockBounds, including both reflected one-sided survival events and the closed unit-interval concentration event. They remain unpaid primitive assumptions. There is no arbitrary S/BE/SP/block/normalization/desired-limit premise, supplied D8 conclusion, or supplied Brownian model in a public head.

Let h_j>0 tend to positive infinity; let N_j be natural. Assume

    N_j/h_j^2 -> positive infinity;       N_j/h_j^3 -> 0.

No coupling between rows, law convergence, symmetry, nonlattice condition, monotonicity of either sequence, or positive survival mass is assumed. The public targets are

    @normalizedKernelMass nu_j p_j h_j N_j 0 -> a=4/pi;

    (pi-product of N_j copies of nu_j).real (Shao.closedStrip h_j)
      / ((4/pi)*exp(-lambda*N_j/h_j^2)) -> 1,

where lambda is the EXISTING RademacherScalarBounds.lambda=pi^2/8>0. The output has the literal finite product and closed strip, not an arbitrary row probability. The explicit row probability instances occur in all normalized varying-row expressions. The finite P2 identity/bound and the free-rate compensation are separately exposed; the latter needs neither S/AC nor the long-time condition.

This conditional consumer does not discharge actual S/AC. It does not close unconditional original K, Kv, general OQ4, or any other original open root. Kv requires a separate variance/rescaling adapter. No novelty claim is made.

## 2. Literal objects and dependency ledger

For proof-local notation only, using exactly KernelRecurrence/KilledIteration, put

    rho_j=principalRate nu_j h_j=integral cos((pi/(2*h_j))*x) dnu_j;
    G_j(k)=@killedMass nu_j p_j h_j k 0;
    F_j(k)=@kernelCosine nu_j p_j h_j k 0;
    Ghat_j(k)=rho_j^(-k)*G_j(k);
    Fhat_j(k)=rho_j^(-k)*F_j(k).

Here rho^(-k) denotes the inverse of the natural power rho^k, not a newly defined real-power operation. Existing principalCosine h w is cos((pi/(2*h))*w). The P1 producer writes cos(pi*w/(2*h)); these coincide by a real ring identity for all h (and in particular h>0). No integrand is replaced by a pointwise approximate cosine.

The only constants introduced below are proof-local lets. The proposed module adds ZERO def/abbrev/instance values. All top-level heads are exhaustively listed in declarations.lean.txt: nine private helpers and four public theorems, thirteen total.

| Dependency | Mathematical use | Status at this proposal |
|---|---|---|
| Qualified CosinePowers, SHA2f54864af99038bfb3e751d59df9d0f09969ae4aa29cd456c1e0fd8fe6758704 | Actual rho large-h bounds and actual cosineCoefficient_log_error_mul with N=L and N=N_j | KNOWN qualified input; reused, not rechecked |
| Qualified KernelRecurrence, SHAa4a5fc67cf47c8e188cbe2e2360afa4fa1bfe0a7082bb9f30fbacd6a5ad5c940 | Literal five normalization/cosine values | KNOWN qualified input |
| Qualified KilledIteration and KilledPathLaw | Actual finite powers, masses, product path probability and closedStrip bridge | KNOWN qualified input |
| BrownianLongTimeRelativeBridge.varying_row_long_time_relative_bridge, frozen combined13-head SHA2014c3defaaf825ff154718a85805b00d37670424f32844654049ba5c664aecd; full row proof SHA1f9bc954e16cc9374aac594d3112dac0b53d41138ef8eee352002f2790334a21 | Common-M all-k normalized mass bound and cosine convergence uniformly for floor(h^2)<=k<=N | Exact frozen producer; implementation/qualification pending, not accepted by this packet |
| BrownianTerminalKernelBlock.terminal_kernel_block, complete source SHA045993480833f6afb57b4fcd2e86aff7559f9048ddb81c636a18615bfcdf4dfb, formal e15b865a07e8c837bb55693a7f6cf14654f40945f42bc01682e41adcebc09057 | Finite actual P1 for every n>=0; no moment assumptions | Complete LOCAL producer; qualification pending |
| BrownianUniformSurvival.uniform_brownian_survival_momentClass, source SHA8a3eea602b4bfcb3326b77c240d1a4f07e757915114871d70753e563969f4d18 | Actual fixed-T, all-law/common-M/all-start error threshold | Complete LOCAL producer; qualification pending |
| BrownianTerminalSpectral.remainderC and remainderC_pos, source SHA16408556daac4f3263fea6c3b88acc9f3167ff3e6165c17b427f990c17d0a3de | Universal actual spectral tail constant C=4/(3*pi*(1-exp(-2*pi^2)))>0 | Complete LOCAL producer; qualification pending |
| Actual CanonicalBrownian, source prefix3c223b5b/PR205, original sole object prefix220e2302 | B, law, probability instance and IsBrownianReal used INTERNALLY in the actual error theorem | Parent reports qualified; exact upstream binding remains parent's gate |
| Actual S/AC producers | Supply the public primitive assumptions eventually from the original moment class | OPEN/unpaid |
| This proposal's scalar limits, P2 normalization, epsilon assembly and final conversion | Derived below, with no desired-conclusion premise | PROVED_HERE mathematically; freeze/review/kernel/axioms pending |

Every pending producer is a qualification dependency, not an additional public theorem premise pretending that the result is accepted. The actual148 varying-row B1 ancestry is internal to the row152 producer and is also qualification-dependent. This consumer never applies a fixed-nu theorem to changing nu_j.

## 3. Derived lower moments, sign, and large-h rho control

For each row, install its supplied probability instance p_j locally. The function 1+|x|^3 is integrable. For r>=0, splitting at r<=1 proves r<=1+r^3 and r^2<=1+r^3: in the first case r,r^2<=1; in the second r<=r^2<=r^3. Therefore |x| and |x^2| are bounded by this integrable function. The identity and square are Borel measurable; Integrable.mono' yields both required lower-moment integrabilities, without new premises.

Pointwise |x|^3>=0 gives beta_j>=0 by integral_nonneg. In particular 0<=beta_0<=M, so M>=0 is DERIVED. No strict positivity of M or beta is used. Set the fixed real constant

    D_M=pi^3*M/48+pi^4/8>=0.

Since h_j->infinity, eventually 1<=h_j and pi*(1+M)<=h_j. On that same eventual set, apply actual cosineCoefficient_large_h_bounds in row j with common M, the row-local lower integrabilities just derived, its given third integrability, mean0/second1 and beta_j<=M. It gives

    3/4<=rho_j<1, hence rho_j>0.                                      (A1)

The same inputs to actual cosineCoefficient_log_error_mul, for EVERY natural q, give

    |q*log rho_j+lambda*q/h_j^2|<=D_M*q/h_j^3.                         (A2)

This is the actual free one-step expectation. Positivity is paid before using exp(log rho_j)=rho_j, before cancelling powers, and before interpreting inverse-power normalization. Any early rows with zero/negative rho cause no difficulty: all cancellation and limit identities are eventual only.

## 4. Separate free-rate compensation

Use (A2) with q=N_j. Its right side is D_M*(N_j/h_j^3)->0, with D_M fixed. Squeeze the absolute value, then use the metric/absolute-difference criterion, to obtain

    e_j=N_j*log rho_j+lambda*N_j/h_j^2 ->0.

Continuity of exp gives exp(e_j)->1. On the eventual set (A1), log_pow and exp_log at rho_j^N_j>0 imply exactly

    exp(e_j)=rho_j^N_j*exp(lambda*N_j/h_j^2).                           (A3)

This proves public varying_row_free_cosine_rate_compensation. It does not use N_j/h_j^2->infinity, Cq,Cs, S/AC, Brownian data, killed masses, or a desired exponential-rate premise. The public input hpos is as given; no added lower-moment or M>=0 premise is needed. N_j=0 is permitted.

## 5. Fixed terminal time: floor, natural subtraction and inverse rate

Fix ANY T:NNReal. For this section write t=(T:Real), L_j=floor_nat(t*h_j^2) and m_j=floor_nat(h_j^2). This is exactly PolygonalKilledFunctionalLimit.floorHorizon T (h_j); t>=0. Nat.floor_le and Nat.lt_floor_add_one give

    0<=t-L_j/h_j^2<1/h_j^2,                                          (A4)

using h_j^2>0 to divide. Since 1/h_j^2->0, (A4) proves L_j/h_j^2->t. Also

    0<=L_j/h_j^3<=(t*h_j^2)/h_j^3=t/h_j ->0.                         (A5)

All these statements include T=0. At T=0 the floors are0 and the limits are exact; there is no hidden positive-time requirement in the scalar helpers.

Use (A2) with q=L_j. By (A5), its right side tends0. With (A4) it follows that

    L_j*log rho_j -> -lambda*t.

Exponentiation and the eventual positive-base identity give rho_j^L_j->exp(-lambda*t)>0. Inverting at this NONZERO scalar limit gives

    r_j(T):=(rho_j^L_j)^(-1) -> exp(lambda*t).                         (A6)

This pays the inverse terminal-rate limit from the actual logarithmic error and floor; it is not a new premise. No killed mass is inverted.

Now additionally use the long-time condition. Eventually N_j/h_j^2>=t+2. Together with L_j<=t*h_j^2 and m_j<=h_j^2, it yields, by real arithmetic and the natural-to-real order embedding,

    L_j+m_j<=N_j.                                                     (A7)

Indeed the real cast of L_j+m_j is at most (t+1)h_j^2, strictly below (t+2)h_j^2<=N_j. Define n_j=N_j-L_j using NATURAL subtraction. From (A7) one obtains

    L_j<=N_j;  m_j<=n_j;  n_j<=N_j;  n_j+L_j=N_j.                    (A8)

For m_j<=n_j, write N_j=(N_j-L_j)+L_j and cancel L_j in L_j+m_j<=N_j; the sum order is commutative. The identity n_j+L_j=N_j is Nat.sub_add_cancel using L_j<=N_j. No unproved replacement of natural subtraction by real subtraction is used.

## 6. Common-M actual source supremum error tends to0 for FIXED T

For T>0 let E_j(T) be the EXISTING sourceSurvivalError (nu_j) T h_j with explicit instance p_j. Its literal value is the BrownianUniformSurvival.survivalError with actual CanonicalBrownian.B and CanonicalBrownian.law, a real sSup over physical z in [-h_j,h_j] of

    e_j(z)=|killedMass nu_j h_j L_j z
             - brownianSurvival canonicalB canonicalLaw T (z/h_j)|.

Both actual probabilities lie in[0,1], hence 0<=e_j(z)<=1 for every z. The image set is bounded above by1. It is nonempty because0 belongs to[-h_j,h_j] (h_j>0). Its real supremum is therefore >=e_j(0)>=0. Whenever all its entries are<=delta, csSup_le with that nonempty image gives E_j(T)<=delta. This is the proposed private source_survival_error_bounds_of_forall helper. It never infers a strict supremum bound or assumes attainment.

Fix epsilon>0. Apply the exact public uniform_brownian_survival_momentClass to actual canonical B/law/isBrownianReal, this FIXED positive T, the common M and delta=epsilon/2>0. It supplies one real threshold A>0 for EVERY law in the moment class and EVERY physical start. Since h_j->infinity, eventually h_j>=A. For each such j, pass nu_j, p_j, row third integrability, mean0, second1, beta_j<=M. Then every |z|<=h_j has e_j(z)<epsilon/2, and thus e_j(z)<=epsilon/2. The preceding genuine sSup argument gives

    0<=E_j(T)<=epsilon/2<epsilon.

The metric criterion proves E_j(T)->0. The threshold may depend on T, epsilon and M and the fixed canonical model. It is uniform over the varying laws and all starts. We use no fixed-law tendsto_survivalError theorem to justify the changing-law conclusion. T will remain fixed while this limit is used.

## 7. Exact finite actual P2 normalization

Take a fixed probability law nu, h>0, natural n, T>=1, and rho=principalRate nu h>0. Let L=floorHorizon T h. Actual150 terminal_kernel_block gives, for ALL n including0,

    |G(n+L)-a_T*F(n)|<=(E+C*exp(-9*lambda*t))*G(n),
    a_T=(4/pi)*exp(-lambda*t),  C=BrownianTerminalSpectral.remainderC>0.

The actual integrands agree by the ring identity noted in section2. Multiply both sides by the positive (rho^(n+L))^(-1). Absolute homogeneity gives the left side of P2. Since rho^(n+L)=rho^n*rho^L and all three powers are nonzero,

    (rho^(n+L))^(-1)*G(n)= (rho^L)^(-1)*Ghat(n),
    (rho^(n+L))^(-1)*F(n)= (rho^L)^(-1)*Fhat(n).

Thus exactly

    |Ghat(n+L)-a_T*(rho^L)^(-1)*Fhat(n)|
      <=(E+C*exp(-9*lambda*t))*(rho^L)^(-1)*Ghat(n).                    (P2)

This proves public normalized_terminal_kernel_block. Its only extra normalization hypothesis is actual rho>0. It has no moment, S/AC, Brownian, desired-limit or n>=1 premise. It divides by no probability. The sum n+L is exact, so substituting (A8) is legitimate.

## 8. Row D8 supplies the T-INDEPENDENT bound and cosine limit

Apply the exact frozen common-M public152 varying_row_long_time_relative_bridge ONCE to the original rows and scales, retaining the literal actual S/AC inputs. Its constant is exactly

    R=exp(pi^2)>0;    H=2*(1+(2*Cs)*R)*R>0.                           (A9)

It gives an eventual set independent of T on which, simultaneously for EVERY k<=N_j,

    0<=Ghat_j(k)<=H.                                                  (A10)

It also gives, for every delta>0, eventually in j, simultaneously for EVERY m_j<=k<=N_j,

    |Fhat_j(k)-1|<delta.                                               (A11)

In particular H depends only on the common Cs. It does not depend on T, epsilon, j, nu_j, h_j or N_j. The row theorem's common-M statement and its explicit instances are essential; the fixed-law theorem is not used here.

For each fixed T, intersect (A8) with (A10) and obtain 0<=Ghat_j(n_j)<=H eventually. Intersect (A8) separately with each (A11); the metric criterion gives

    Fhat_j(n_j)->1.                                                   (A12)

This is valid despite n_j depending on j: the universal k quantifier in (A11) is inside the eventual set, and (A8) verifies its whole admissible range. By (A6), (A12) and continuity of scalar products,

    a_T*r_j(T)*Fhat_j(n_j)->4/pi.                                     (A13)

Indeed exp(-lambda*t)*exp(lambda*t)=1. There is no required positivity of Fhat in this product-limit argument; boundedness and positivity are used only in the error estimate on the appropriate eventual set.

## 9. Choose T FIRST, then choose the row threshold: full epsilon proof

Fix epsilon>0. With H from(A9) and C>0, there exists T:NNReal with T>=1 such that

    2*H*C*exp(-8*lambda*t)<epsilon/3.                                 (A14)

For a direct construction, put D=6*H*C/epsilon>0, q=log D/(8*lambda), t=max 1 (q+1), and T=the nonnegative real t. Then t>=1 and t>q. Since8*lambda>0, -8*lambda*t<-log D; exponentiating gives exp(-8*lambda*t)<D^(-1). Multiplication by2*H*C>0 yields(A14) exactly. This is the private terminal_tail_small helper. In particular it is not a varying-time invocation of a fixed-time invariance principle.

Fix this selected T for all remaining limits. Put b=exp(lambda*t)>0. By(A6), eventually r_j(T)<=2*b: choose |r_j-b|<b. By section6, eventually

    0<=E_j(T)<epsilon/(6*H*b).                                        (A15)

By(A13), eventually

    |a_T*r_j(T)*Fhat_j(n_j)-4/pi|<epsilon/3.                           (A16)

Intersect these eventual sets with(A1),(A8),(A10); all depend on this FIXED T and epsilon and are selected before j. On the resulting set, r_j(T)>0 and 0<=Ghat_j(n_j)<=H. Apply(P2), using n_j+L_j=N_j. The triangle inequality gives

    |Ghat_j(N_j)-4/pi|
      <= |Ghat_j(N_j)-a_T*r_j(T)*Fhat_j(n_j)|
          +|a_T*r_j(T)*Fhat_j(n_j)-4/pi|
      <= E_j(T)*r_j(T)*Ghat_j(n_j)
          +C*exp(-9*lambda*t)*r_j(T)*Ghat_j(n_j)
          +|a_T*r_j(T)*Fhat_j(n_j)-4/pi|.

The first term is <epsilon/3: by(A15) and r_j*Ghat_j<=2*b*H, it is at most E_j*2*b*H<epsilon/3. The second is <=2*H*C*exp(-8*lambda*t)<epsilon/3 by(A14) and exp(-9*lambda*t)*b=exp(-8*lambda*t). The last is <epsilon/3 by(A16). Thus |Ghat_j(N_j)-4/pi|<epsilon. This proves the full public varying_row_normalized_kernel_mass_tendsto.

The threshold order is forall epsilon>0, exists a FIXED T>=1, exists a row threshold, forall larger j. No T_j growing with j is fed into a fixed-time limit; no interchange of limits is asserted; no limsup formalism is needed. The exact H is independent of the T choice. No division by G_j or Ghat_j and no assumption G_j>0 occur.

## 10. Actual finite-product closed-strip relative asymptotic

Let d_j=lambda*N_j/h_j^2 and a=4/pi>0. Section4 proves c_j=rho_j^N_j*exp(d_j)->1. Section9 proves Ghat_j(N_j)->a. On the eventual set rho_j>0, normalization cancels exactly:

    G_j(N_j)*exp(d_j)=Ghat_j(N_j)*c_j ->a.

Since exp(-d_j)>0 for EVERY j, and a>0, the final denominator is always positive regardless of whether G_j is zero. For all rows in the same eventual positive-rho set,

    G_j(N_j)/(a*exp(-d_j))=Ghat_j(N_j)*c_j/a ->1.                     (A17)

No probability appears in a denominator. The algebra uses exp_neg and inverse/cancellation only for nonzero rho powers, the positive scalar a and positive exponentials.

Finally the existing KilledPathLaw.killedMass_eq_closedStrip_probability in each row, with h_j>=0 from hpos j, gives for EVERY j

    G_j(N_j)=(Measure.pi (fun _ : Fin(N_j) => nu_j)).real
                (@Shao.closedStrip (N_j) h_j).                       (A18)

This is an exact equality of actual unconditioned finite product probabilities, including atoms and endpoints. Its proof uses killedMass_eq_path_probability and shiftedClosedSurvival_eq_closedStrip. The shifted event monitors times1 throughN, while closedStrip also monitors k=0; that extra condition is |0|<=h_j and is paid. At N_j=0 both survival events have full measure and the equality still holds. Substituting(A18) into(A17) proves public varying_row_closedStrip_relative_asymptotic, the desired original common-M sequential K conclusion CONDITIONAL on actual S/AC and producer qualification.

## 11. Exhaustive boundary, scope and completion audit

All natural k,n,L,N zero cases are covered by actual finite P1/P2 and the path-law bridge. The long-time/positive-scale assumptions eventually make the D8 range nonempty; early bad-scale rows are irrelevant only by eventual equality, never by changing a sequence. T=0 is allowed in scalar floor/rate helpers but is explicitly excluded from the source-survival convergence helper by hT>0 and from terminal P2 by T>=1. All floor divisions use h_j>0. The image sSup uses a verified nonempty closed interval and bounded image, not a compactness/attainment claim. Literal weak endpoints, strict exit, lattice cosets, asymmetric laws and atoms are retained. The common-M hypothesis and common Cq,Cs occur before every row threshold. Individual third-moment finiteness with unbounded beta_j is not claimed sufficient.

There are exactly thirteen proposed top-level theorem heads, nine private and four public; zero new transparent values, aliases or instances. All constants used in the proof are proof-local lets of existing literals. No hidden new top-level lemma, arbitrary probability event, Brownian premise, sourceSpitzer premise or rate-limit assumption is required. The new module path was checked absent in the read-only library. See API evidence for exact producer calls and reused pinned primary source interfaces.

The argument is complete as a conditional mathematical proposal. Parent must read the WHOLE proof and declaration file and freeze the exact mathematical/public/private interface before implementation. Qualification dependencies must be bound to their accepted exact versions. A later implementation still needs one source-bound server kernel/all-owned-transitive-axiom receipt and a fresh qualified independent complete source-to-statement/proof/actual-type review; this author's proof is not that independent review. Only propext, Classical.choice and Quot.sound are allowed. No new axiom, sorry, admit, unsafe or native_decide is authorized.

NEXT_DEPENDENCY: parent complete proof/head freeze, then authorize implementation in the owned new module; actual S/AC remains the separate unpaid producer chain. This author stops/releases after delivering this proposal and compact static checkpoint, as explicitly assigned. All original open roots retain OPEN status.
