# Original OQ4 window and iid transfer: complete mathematical proposal

Author181, fresh gpt-6.1-sol/xhigh; math-theorem, no math-ultra. Status: PROVED_AS_MATHEMATICAL_PROPOSAL_RELATIVE_TO_THE_EXPLICIT_DEPENDENCY_CONTRACTS. This is not a parent freeze, independent review, Lean implementation or server certificate. The exact future E5 and positive-boundary consumers have not been treated as formally qualified. All original root groups remain OPEN until every required qualification and integration gate is paid.

The owned output is only this directory. No Lean, parser, server, Git, package/cache mutation, installation, local test or raw download was performed. The companion declaration file lists the complete two-module proposal, including all private heads, full definition values, imports and options. Mathematical proof-local choices below introduce no additional module declaration. An additional module helper or changed interface must be frozen before implementation.

## 1. Exact original source and objects

The complete read-only sources `C:/game/shao/current/oq4/frozen01.md` and `denom01.md` fix one iid real law while n varies, with E|X_1|³ finite, E X_1=0 and 0<E X_1²<infinity. For every decreasing a_n tending to zero with a_n n^(1/6) tending to infinity, the target is

    sup_{a_n<x<1} |P(M_n <= x V_n) / P(U_B <= x) - 1| -> 0.

Here S_k=sum_{i=1}^k X_i, M_n=max_{1<=k<=n}|S_k| for n>0, V_n=sqrt(sum_{i=1}^n X_i²), and U_B is the actual time-one absolute Brownian supremum for the given genuine Brownian B. Every wall is weak. The source U is represented by the qualified measurable BrownianSup.U, almost surely equal to the continuous-path supremum. Its actual CDF is the qualified BrownianSup.probability B P hB. No free reference function F appears in the formal target.

Only sufficiency is proved here. `sharp01.md` was read in full for scope: its fixed Rademacher lattice-offset necessity is a separate exact-scale result. No supremum over laws, fourth moment, density, nonlattice condition, exponential moment, bounded increments or replacement of the random energy by its mean is introduced. The common124 mechanism, p54 repairs and external BE-SP attribution are unchanged. No novelty or firstness claim is made.

For the standardized product-law part let nu be one fixed probability measure on R, with integral |z|³ finite, integral z=0 and integral z²=1. Let pi_n be its actual Fin n product measure. A path a:Fin n->R has S_k(a)=prefixSum a k and Q(a)=energy a. ClosedStrip(w) monitors k=0,...,n. Define

    p(n,x) = pi_n.real(randomDenominatorEvent n (x sqrt(n))),
    e(n,x) = |p(n,x)/F_B(x)-1|,
    W_n = {e(n,x):a_n<x<1},  w_n=sSup W_n.

These are precisely A01-A04, with real totalized division and real sSup at every early index. Their complete values are frozen candidates, not implicit conventions. The future positive-boundary B20 contract proves p(n,x)=pi_n.real ClosedStrip(x sqrt Q) for every n and real x, including n=0. Its argument at n=0 is genuine empty-path algebra: Q=0, every available prefix is zero and both walls are zero. No cancellation of sqrt(0) is used.

## 2. Dependency boundary

The E5 input to this proposal is the exact public `RandomDenominatorAsymptotic.randomDenominator_relative_main_tendsto` head H24 from the parent's frozen proposal: under the fixed nu assumptions and h_j->infinity, n_j/h_j²->infinity, n_j/h_j³->0, the actual E(n_j,h_j)/farMainTerm(n_j,h_j) tends to one. No positivity is required at every early index. H24 is called internally, after its future formal qualification, and is not assumed as a hypothesis of A09 or any original root theorem.

The positive-boundary input is the exact proposed public `PositiveBoundaryStudentized.studentized_positive_boundary_ratio_tendsto`: for the same fixed nu, n_j->infinity and x_j->x_*>0, p(n_j,x_j)/F_B(x_j)->1. Its proof internally pays the actual energy LLN from the second moment, Brownian positive-level atom/continuity/positivity facts, and the precise floor/horizon row theorem. Its public BrownianPositiveCDF.probability_mono and probability_pos also supply the finite-supremum bounds below. This complete two-module proposal was read; the parent has since frozen it, but implementation, independent review and source-bound server qualification are still unpaid. No desired LLN, Donsker theorem, weak limit, ratio or whole window is inserted into any new public root's premises.

Qualified old first-term, finite-iid and variance-scaling results are used only through the actual consumed public heads and full values listed in api-evidence.md. Their old successful checks are reused without a new old-proof review or Lean print. The actual source/object binding still has to be verified when these new modules are eventually checked.

## 3. Small-boundary scales: A05-A07

Let n_j be natural with n_j->infinity, x_j real with x_j>0 eventually and x_j->0, and f_j=x_j(n_j:real)^((1:real)/6)->infinity. Put h_j=x_j sqrt(n_j). Eventually n_j>=1 and x_j>0, so every denominator in the following identities is positive. For N=(n_j:real)>0, sqrt N=N^(1/2), real-power addition gives N^(1/6)N^(1/3)=N^(1/2), and real-power multiplication gives (N^(1/6))³=sqrt N. Consequently

    h_j=f_j N^(1/3),
    N/h_j²=1/x_j²,
    N/h_j³=1/f_j³.

The first is real-power arithmetic with 1/6+1/3=1/2, not a natural-number quotient. For the second use h_j²=x_j² N and cancel N>0. For the third use h_j³=x_j³ N sqrt N, while f_j³=x_j³ sqrt N, then cancel N>0. These are exact equalities on the positive tail; A05 states precisely that tail's scalar facts.

Since N>=1, N^(1/3)>=1 and h_j>=f_j eventually. Thus h_j->infinity: each prescribed real R is eventually exceeded by f_j and then by h_j. Next 1/x_j²->infinity. Explicitly, for any R choose c=1/sqrt(max(R,0)+1)>0. Eventually 0<x_j<c, whence 1/x_j²>max(R,0)+1>R. Finally 1/f_j³->0: for eta>0, eventually f_j>max(1,1/eta), and hence 0<=1/f_j³<=1/f_j<eta. The eventual exact identities give A06's three scales without changing any early n=0 or nonpositive x term.

The qualified farMainTerm value is (4/pi) exp(-(pi²/8)n/h²), and the qualified literal Brownian firstTerm value is (4/pi) exp(-(pi²/8)/x²). Substituting n/(x sqrt n)²=1/x² proves their literal equality on n>0,x>0, which is A07. No asymptotic exponent error or logarithmic probability comparison is used.

## 4. Actual small-boundary ratio: A08-A09

For the actual B/P/hB, qualified actual_brownian_firstTerm says: for each epsilon>0 there is delta>0 such that 0<x<delta implies |F_B(x)/firstTerm(x)-1|<epsilon. Since x_j>0 eventually and x_j->0, that inequality holds eventually for each epsilon. Hence F_B(x_j)/firstTerm(x_j)->1, proving A08.

Apply future qualified H24 internally with the h_j from Section3. All its fixed-law and scale conditions have just been paid, so p(n_j,x_j)/farMainTerm(n_j,h_j)->1. A07 identifies the main term with firstTerm(x_j) eventually. Its value is strictly positive at every real x because 4/pi>0 and exp is positive. Dividing the two convergent ratios gives

    [p(n_j,x_j)/firstTerm(x_j)] / [F_B(x_j)/firstTerm(x_j)] -> 1.

The scalar identity (p/m)/(F/m)=p/F holds whenever m!=0, even with totalized real division at F=0. In addition the actual positive-level CDF theorem gives F_B(x_j)>0 on the positive tail, so the ratio has its genuine probability interpretation there. This proves A09. No lower bound uniform in j for F_B(x_j) is assumed; it may tend to zero exponentially.

The FAR weak multiplicative wall is (h_j/sqrt(n_j))*sqrt Q. On n_j>0 it equals x_j sqrt Q exactly. Q=0 is untouched: nonnegative squared coordinates summing to zero all vanish, hence all prefixes vanish, and the source weak inequality is 0<=0. We never replace M<=xV by a quotient event on V>0.

## 5. Eventual lower-window positivity and bad subsequences: A10-A11

Since a_n n^(1/6)->infinity, that product is eventually greater than zero. For n>=1 its real-power factor is positive, so a_n>0 eventually. Since a_n->0, a_n<1 eventually. This proves A10. The extra source Antitone a hypothesis is retained in every public whole-window and original iid theorem; the proof does not need it, and no source assumption has been silently changed.

Here is the complete extraction asserted by A11. Suppose e is any real function of n and x, a_n>0 eventually, and frequently in n there exists x in (a_n,1) with e(n,x)>=epsilon. Choose N so that a_n>0 for all n>=N. Frequently in the natural atTop filter means that for every lower cutoff L there is a bad n>=L. Choose a bad n_0>=N and one of its witnesses x_0. Having chosen n_j, choose a bad n_(j+1)>=max(N,n_j+1), together with a witness x_(j+1). Classical choice and natural recursion suffice. Thus n_j is strictly increasing, each x_j belongs to (a_(n_j),1), each x_j>0, and every chosen error is at least epsilon.

The sequence x_j lies in compact [0,1]. Sequential compactness gives x_* in [0,1] and a strictly increasing map phi with x_(phi(j))->x_*. Replace n_j by n_(phi(j)) and x_j by x_(phi(j)). The composition is strictly increasing, every exact witness/error condition survives, and all points still lie in (0,1). This is the complete A11 conclusion. It selects only bad indices. It does not infer eventual badness at every n from failure of an eventual good statement.

## 6. Epsilon-tail for the original window: A12

Fix epsilon>0. If it is not eventually true that every x in (a_n,1) has e(n,x)<epsilon, the negation of eventuality says frequently there is such an x with epsilon<=e(n,x). Apply A10 and A11. Obtain strictly increasing n_j, positive x_j in (a_(n_j),1), x_j->x_* in [0,1], and errors >=epsilon at every j. Strictly increasing natural indices satisfy n_j>=j, and therefore n_j->infinity.

If x_*=0, the original divergent lower-window scale composed with n_j gives

    a_(n_j) (n_j:real)^(1/6) -> infinity.

The nonnegative real-power factor and x_j>a_(n_j) imply x_j(n_j:real)^(1/6)>=a_(n_j)(n_j:real)^(1/6). Hence the former tends to infinity by direct order comparison. A09 applies and gives p(n_j,x_j)/F_B(x_j)->1, so its absolute error tends to zero, contradicting the fixed positive lower error.

If x_*>0, invoke the future qualified positive-boundary ratio theorem internally at n_j and x_j. Its assumptions are exactly the fixed original standardized law, n_j->infinity and x_j->x_*>0, all already paid. Again the absolute error tends to zero, the same contradiction. This branch includes x_*=1; there is no unexamined endpoint. Equivalently its probability and continuous positive CDF conclusions permit the same division, but no new rate is needed. These two cases exhaust [0,1] and prove A12.

## 7. Genuine finite real supremum and its limit: A13-A17

At every n and x, the actual probability p(n,x) is between zero and one. The finite product is a probability measure including Fin0, and its weak random-wall event is measurable by finite prefix/energy measurability. This proves A13.

Fix n with 0<a_n<1. The point (a_n+1)/2 lies strictly between a_n and 1, so W_n is nonempty (A14). Actual Brownian positivity gives c=F_B(a_n)>0. Monotonicity gives F_B(x)>=c for every x in (a_n,1). Thus 0<=p(n,x)/F_B(x)<=1/c. For any such nonnegative ratio r,

    |r-1| <= r+1 <= 1+1/c.

Every W_n member therefore has the explicit finite bound 1+1/F_B(a_n), giving A15 and BddAbove W_n. The real conditional-complete-lattice theorem `isLUB_csSup` now proves that w_n really is the least upper bound. An actual member of W_n is nonnegative, so 0<=w_n. This proves the entire A16 specification. It is not an assumed global lower bound on F_B(a_n), and its bound may diverge with n.

For epsilon>0, apply A12 with epsilon/2. On its eventual tail every member of W_n is <epsilon/2, hence <=epsilon/2. Intersect with A10's 0<a_n<1 tail and use the least-upper-bound property: 0<=w_n<=epsilon/2<epsilon. Thus |w_n-0|<epsilon eventually, proving A17. The actual sSup definition at early empty or unbounded W_n has never been changed; convergence depends only on the proved good tail. This closes the requested finite-supremum obligation rather than stopping at a pointwise or epsilon-tail assertion.

## 8. Original source coordinates and maxima: B01-B11

Now let (Omega_X,mu) be an arbitrary probability space, independent of the given Brownian probability space. Let X:Nat->Omega_X->R denote source variables. Only X_1,X_2,... are used. B01 takes sourcePath_n(omega)(i)=X_(i.val+1)(omega), so the map from Fin n to source indices is fixed once and for all. The iid assumptions apply to the shifted family i->X_(i+1); X_0 is unconstrained and unused.

For k<=n, the bijection from {i:Fin n:i.val<k} to {i in range k} preserves each source summand X_(i+1). Reindexing the finite sum proves B06. The same Fin n/range n bijection with squared summands proves B07: sourceEnergy_n=sum_{i=1}^n X_i². Both identities include their empty sums.

For n>0, B03 is the actual qualified absMax of this path. Its qualified absMax_le_iff head and B06 prove B08: M_n<=w iff every positive source prefix k<=n has absolute sum<=w. This is exactly the original max, not a maximum over an invented empty set. At n=0 B03 explicitly extends the sequence by zero, while B02 is the empty sum zero.

If each positive X_i is measurable, sourcePath_n is measurable coordinatewise (B09). Energy, sqrt energy and the positive-length absMax are measurable by the qualified finite-path APIs, so the weak comparison event B04 is measurable; at n=0 it is the whole space. This proves B10. One can instead express its closed-prefix constraints as finite measurable intersections.

For B11, set w=x sqrt(sourceEnergy). At n>0 and w>=0, the qualified mem_closedStrip_iff_absMax_le gives the exact event identity. At n>0 and w<0, both conditions are false: closedStrip membership forces 0<=w by its zero prefix, and absMax>=0 makes absMax<=w impossible. Thus the identity is valid at every real x, without adding an x>=0 premise. At n=0 both sourceMaximum and sourceEnergy are zero, the wall is zero and the single prefix is zero, so both events are the whole space. This pays the finite event equality used later, including early zero length.

## 9. Exact positive variance scaling and all zero-energy atoms: B12-B14

Fix sigma>0 and standardize Z_i=X_i/sigma. Pointwise, sourcePath(Z)=sigma^(-1) times sourcePath(X). Qualified prefixSum_smul and energy_smul give

    S_k(Z)=S_k(X)/sigma,   Q(Z)=Q(X)/sigma².

Since Q(X)>=0 and sigma>0, sqrt(Q(Z))=sqrt(Q(X))/sigma. For example the nonnegative expression sqrt(Q(X))/sigma has square Q(X)/sigma² and hence is that square root; this covers Q=0. Multiplication of the real weak inequality by sigma>0 proves, for every prefix and every real x,

    |S_k(Z)| <= x sqrt(Q(Z)) iff |S_k(X)| <= x sqrt(Q(X)).

B11 therefore gives sourceEvent(n,Z,x)=sourceEvent(n,X,x) for all n,x, which is B12. The argument does not divide by Q or require x positive. Its n=0 and Q=0 cases are literal identities. In the original positive-n maximum, qualified absMax_smul_of_nonneg gives the same M_n(Z)=M_n(X)/sigma identity directly.

From the original integrable absolute cube, the first and square moments are integrable. For every real y,

    |y| <= 1+|y|³,   y² <= 1+|y|³.

For |y|<=1 both are <=1; for |y|>1 both are <=|y|³. The right side is integrable on a probability space, and Y is AE measurable, so integrable domination proves B13, without a fourth moment.

For measurable Y=X_1 define v=integral Y², sigma=sqrt(v), nu=mu.map(Y/sigma). The premise v>0 gives sigma>0 and sigma²=v. B13 supplies the lower integrability required by the exact qualified `Shao.OQ4.standardized_moments`, which gives integrable Z, Z², |Z|³, mean zero and second moment one for Z=Y/sigma. Measurability of Z makes nu a probability law. The exact identical-distribution pair Z on mu and id on nu has the defining map equality. Apply its measurable compositions by z, z² and |z|³, its integrability transport, and its integral equality. This gives the actual nu third integrability, mean zero and second moment one in B14. Finiteness of the original second moment was derived from the third moment; it has not been replaced by an extra supplied variance premise.

## 10. Arbitrary iid-space finite law and exact probability: B15-B16

Assume first that the positive X_i are measurable, the shifted family is independent, and every X_(i+1) is IdentDistrib with X_1 under mu. Compose each coordinate with the fixed measurable map y->y/sigma. This preserves independence and identical distribution. Restrict the resulting family along the injective Fin.val map; no sample-dependent selection is used.

The common actual law is nu=mu.map(X_1/sigma). Each normalized finite coordinate is IdentDistrib with id under nu: compose the supplied IdentDistrib with normalization and then the actual normalized X_1/id law. Qualified FiniteIID.iid_samplePath_map_eq_pi now gives

    mu.map(sourcePath_n(Z)) = Measure.pi(fun _ : Fin n => nu),

which is B15. Its domain includes Fin0. The sourcePath shift has already been paid exactly; no one-based coordinate is silently dropped.

The actual finite weak-wall path event A={a:ClosedStrip(x sqrt Q(a))} is measurable: Q and every prefix sum are measurable, sqrt is continuous and all comparisons are weak measurable comparisons. The map identity transports its measure to its exact preimage. B11 identifies this preimage with sourceEvent(n,Z,x), B12 identifies that with sourceEvent(n,X,x), and future qualified PositiveBoundaryStudentized.randomDenominatorEvent_eq identifies A with the event in productProbability. Taking finite real measures proves B16 for every n,x. No probability limit is used here. The finite map's probability law, not a distributional heuristic, is what transfers the original iid event.

## 11. AE-measurable versions and exact original probabilities: B17-B21

The final public interface permits AE-measurable positive coordinates, so it includes ordinary measurable random variables without restricting the original probability space or law. For each j>=0 let g_j=(hX_j).mk(X_(j+1)), a measurable version with X_(j+1)=g_j almost surely. Define Y_k=g_(k-1), where natural subtraction makes the value at k=0 harmless and unused. Then Y_(j+1)=g_j is measurable and X_(j+1)=Y_(j+1) almost surely. This proves the existential version head B17; the construction is proof-local and introduces no hidden top-level value.

At a fixed finite n, intersect the finitely many coordinate agreement events. On the resulting full-measure event the two paths, energies, maxima and weak events agree pointwise for every x. This proves B18. In fact a single countable intersection gives agreement for all positive coordinates, but finite agreement suffices. The argument covers n=0 with an empty intersection.

Independence transfers by the pinned iIndepFun_congr equivalence. For identical laws, each supplied IdentDistrib contains the needed AE measurability. The pinned IdentDistrib.of_ae_eq gives X_i identically distributed with Y_i; combine its symmetry for the left coordinate, the original identical-distribution assertion and the reference-coordinate AE comparison by transitivity. This proves B19, with no law change.

B10 makes each sourceEvent for Y measurable. B18 identifies the original event with it modulo mu-null sets; hence the original event is NullMeasurableSet, proving B20. Measure congruence for AE-equal events gives the same actual outer measure and hence the same real measure, whether or not mu is complete. For every x these probabilities are equal, so their exact image sets over the same open interval are equal. Applying sSup proves B21 at every early or late n. No tail approximation or error term arises from choosing measurable versions.

The version of X_1 and X_1 itself agree almost surely. Their absolute cubes and squares agree almost surely too, so integrability and all three integrals transfer by congruence. Thus Y has exactly the original finite-third, mean-zero and positive-second assumptions. No extra measure completion, density or atomlessness is imposed.

## 12. The original finite supremum and final iid target: B22-B25

B22 pays the genuine finite supremum directly for sourceEvent. For 0<a_n<1 its error-image set is nonempty at the midpoint. For any event on the probability space, 0<=mu.real(event)<=1. Together with actual F_B monotonicity and positivity at a_n, the calculation in Section7 gives the finite bound 1+1/F_B(a_n). The real sSup is therefore an IsLUB and is nonnegative. No measurability assumption is needed just for this finite numerical bound; B20 separately guarantees that the events in the actual AE theorem are legitimate null-measurable events. A10 makes B22 applicable eventually under the original a hypotheses.

For measurable X, B14 at X_1 supplies the actual fixed standardized nu. It depends on mu and X_1, neither of which varies with n. B16 gives equality of each original probability and each standardized product probability at all n,x. Consequently their error-image sets and their exact sSup values are equal at every n. A17 applied to this nu therefore proves B23, `source_window_measurable_tendsto`, under precisely the original moment/variance and decreasing-window conditions.

For AE-measurable X, choose Y by B17. B19 supplies its independence/common law; Section11 transfers the moments. Apply B23 to Y, and transfer the exact error function by B21. This proves B24, `source_window_ae_tendsto`. Finally expand only B05 and B04. This is B25's displayed limit

    sSup { |mu.real{M_n(X)<=x sqrt(Q_n(X))}/F_B(x)-1| : a_n<x<1 } -> 0.

B07 and B08 identify the displayed Q_n and M_n with the original one-based sum of squares and maximum over 1<=k<=n. B22 and A10 show that the displayed real sSup is a genuine finite supremum eventually. Its early n=0 extension is explicitly fixed and irrelevant to the limit. Every Q_n=0 atom is retained in the actual weak multiplicative event, and the actual given Brownian CDF is displayed in the final head. This is the whole original fixed-law sufficiency target as a mathematical consequence of the named dependency contracts, with no desired limit among its public premises.

## 13. Scope and remaining qualification

The mathematical bridge is complete relative to the explicit E5 and positive-boundary contracts. Qualification is still required for those implementations and these two new modules: parent exact declaration freeze, implementation, a fresh qualified independent complete source-to-statement/proof review, exact-source server kernel receipt and all-owned transitive-axiom audit. The whitelist remains propext, Classical.choice and Quot.sound. No accepted old unit needs rerunning solely for this proposal or a new context. Source proofs and exact hashes determine reuse.

The companion API evidence records primary pinned sources and old source hashes; none is a certificate for this new proposal. The checkpoint records actual runtime as FINAL_STOP with writer release. This ends this author's authorized mathematical unit; it does not represent ongoing execution or closure of any original root group.
