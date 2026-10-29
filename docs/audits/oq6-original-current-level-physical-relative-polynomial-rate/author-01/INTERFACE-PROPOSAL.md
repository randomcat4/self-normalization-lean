# Unit262 interface proposal: original current-level physical relative polynomial rate

STATUS: PROPOSAL_READY. This is an interface and rigorous route proposal, not a completed proof, not a lead freeze, and not permission to implement. Upstream261 exact candidate1ae7e408 is not yet complete SOURCE/kernel/final-qualified. Implementation must wait for both explicit lead freeze and exact261 final qualification; any affected upstream change requires rebinding before use.

Owner: /root/oq56_unit262_author under sole OQ56 lead01a1822b-1815-7f21-a1af-2e0b15ee67a5. Exclusive new-write directory: drafts/oq56/unit262/author-01. No server, Lean, AX, external, child, publication, schedule or shared-file authority. Other owners' bytes have not been edited.

## Exact proposed artifact and public statement

Module: Shao.OQ6.OriginalCurrentLevelPhysicalRelativePolynomialRate.
Theorem: actual_original_current_level_physical_relative_polynomial_rate.
The complete proposed preamble/head/closing are the three sibling *-PROPOSAL.txt files. They contain no proof body. The proposed theorem has one substantive original-model conclusion, with a positive explicit constant and the requested physical relative error rate.

Retain original h, mu, joint measurability, L2 kernel, symmetry, centering and unit projection second moment. Keep g=E[h|first coordinate], r=h-g-g', v=E r^2 and rho=sqrt(v). Keep the original ambient product probability P and exactly the261 physical statistic, including its true centered denominator and the zero-denominator value0.

Quantifiers remain: original h/mu data; exists cg>0; all Cenv,aenv,t0,Menv and their original signs; eventually n; all w and original envelope hypotheses; z and the original tilt/envelope/geometry windows; then p, original p-integrability, cSZ/C1..C4 and explicit broader-L2 conditional hSZ. The beta=0 OR positive-beta p-window is retained byte-for-byte from261.

The one explicit extra hypothesis is:
  z <= min(1,sqrt(t0)/2) * n^(1/6).
It appears beside the existing windows, before p and the hSZ constants. No implication from the old windows is asserted. A minimum-window facade could be derived later, but is not needed for this proposal.

The only public lets after the exact moment window are the original mN/P, D1, physical, and the two numerical constants:
  K0 =64*exp(1/2)^4*(1+4*512),
  Ktail =8*(1+C1+C2+C3+C4)*exp(C3)*(1+K0).
The proposed conclusion is0<Ktail and
  |P.real{z<=physical}/Psi(z)-1|
    <= Ktail*(beta*(1+z)^p*n^(-((p-2)/2))
        +(1+rho)*(1+z)^3/sqrt(n)).
There are no public fee bounds, coding witnesses, callbacks, generic probability comparisons, nonzero-denominator assumptions, positivity assumptions on the lower factor, or missing event assumptions.

## Source-bound interface map

1. Sealed261 OriginalCurrentLevelPhysicalFiniteCostTail.lean,1ae7e408e77d15677f56b9c33b34dfc8898a8a0ea80ebf99e98be48c16f3e732,24766B/432LF, supplies the original current-z physical lower and upper estimates and K0 cubic replacement. This source is PROVISIONAL ONLY until the independent complete SOURCE review, server first-object/all-owned audit and final qualification are completed. No261 pass is claimed here.
2. Qualified259 OriginalLevelDependentUpperPhysicalFrontier.lean,1136c7f4cd654dc8fcf0ddc9b8c4575f901175e8b785c42aa9fd3926f562a172,70472B/1114LF, public moment packet lines490-530 explicitly identifies its L0 with original L, nonnegativity, original-beta moment rate, beta=0 branch, exact cWindow power, and strict moment window. Its existing qualified evidence is reused. No old complete-proof adjudication or old machine replay is proposed.
3. The already accepted IIDSourceStrictMomentBudgets.actual_iid_source_z_strict_moment_budgets public head gives exactly the original product-law moment estimate and, importantly, L<=cWindow^p under the retained OR window. Using this direct original-law producer avoids selecting a second coding witness. It is the producer consumed by259's accepted moment route. Only its public bearing interface is needed.
4. Accepted OriginalExceptionalTailAbsorption.eventually_original_exceptional_payment_absorbed, complete245LF sourcecb1ed434c1029e674ddff14a1be07ab55b2fb064060acbe92bea389a93f7df8f, supplies the exact cAbs=min(1,sqrt(t0)/2)>0 and2B(1)<=R*Psi(z) on its explicit window, with R=exp(-(t0/2)*n^(1/3)). Existing exact qualification is reused without new review/check.
5. Shao.standardNormalTail_basic.2.2.1 gives Psi(z)>0, permitting all divisions by Psi(z).
6. Pinned Mathlib Analysis.SpecialFunctions.Pow.Asymptotics theorem tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero supplies the new polynomial absorption step below; it is not replaced by an absolute-smallness assertion.
7. Real.add_one_le_exp, exp positivity, monotonicity and exp-add/neg identities suffice for both scalar exponential linearizations; no derivative or additional smoothness premise is needed.

## Rigorous route to be implemented only after freeze/qualification

A. Select cg once from261 before all envelope constants. Retain its eventual n assertion. Separately obtain the accepted exceptional absorption eventual assertion for the same t0 and that cg. Form the third eventual assertion R<=1/sqrt(n) by the t0-only route inB. Intersect these eventual assertions before introducing w,z,p,cSZ,C1..C4. This preserves uniformity in every later quantified parameter.

B. Put b=t0/2>0 and s_n=n^(1/3). The nat-cast atTop map composed with positive rpow gives s_n->+infinity. Apply the existing asymptotic theorem with real exponent3/2 and b, and compose with s_n, to obtain
  (s_n)^(3/2)*exp(-b*s_n)->0.
For n>=4, rpow-multiplication and sqrt_eq_rpow give (s_n)^(3/2)=sqrt(n), since(1/3)*(3/2)=1/2. Hence sqrt(n)*R->0. An eventual bound by1 and sqrt(n)>0 give R<=1/sqrt(n). This eventual threshold depends only on t0; it does not depend on p, beta, cSZ or C1..C4. The combined threshold also contains261's original envelope threshold and the accepted absorption threshold(t0,cg), exactly in the allowed outer order.

C. For the original g, hh implies measurability by stronglyMeasurable.integral_prod_right'.measurable. The original integral g^2=1 forces Integrable(g^2), since an undefined Bochner integral is0; hence MemLp g2 by memLp_two_iff_integrable_sq. These are consequences of existing hypotheses, not new assumptions. Apply the accepted direct iid moment producer with cBudget=cSZ>0. Its original P and truncationF unfold definitionally to261's deltaoriginal and Loriginal; no reduced-law integral or coding choice is introduced.

D. Write L=Loriginal, q=(p-2)/2 and A=beta*(1+z)^p*n^(-q). The original moment producer gives0<=beta,0<=L and
  L<=beta*z^p/n^q.
Its exact OR window, including beta=0, gives
  L<=cWindow^p=min(1/2,cSZ)/2<=1/4.
In the beta=0 branch its explicit zero conclusion also gives L=0; no inverse power at beta=0 is used. In the positive branch the existing producer already raises the stated window to p and cancels the positive powers of beta/n. Converting division into n^(-q) for n>0 and monotonicity z^p<=(1+z)^p for p>2 and z>=1 yield L<=A. This is the actual original truncated-moment upper bound, not L2<=4 or an unexplained smallness claim.

E. Let E=(1+rho)*(1+z)^3/sqrt(n), so cubicCost=K0*E and E>=1/sqrt(n)>=0 because rho=sqrt(v)>=0 and z>=1. In particular R<=E. Let B(z)=3exp(-q_n)+exp(-cg*n)+4exp(-z*sqrt(n)/2), q_n=boundedPolylogMomentOrder(t0,n). Since z>=1 and sqrt(n)>=0, exp(-z*sqrt(n)/2)<=exp(-sqrt(n)/2), so B(z)<=B(1). The accepted absorption lemma yields
  2B(z)<=2B(1)<=R*Psi(z),
  4B(z)<=2R*Psi(z).
The lower2 and upper4 fees remain distinct through this calculation.

F. Divide261's cubic physical bounds by Psi(z)>0, using only the fee comparisons above. For Q=P.real{z<=physical}/Psi(z), obtain
  exp(-C1*L)*(1-C2*K0*E)-R <= Q,
  Q <= exp(C3*L)*(1+C4*K0*E)+2R.
The same physical P/statistic is used on both sides. This is a current-z cubic application, not a repetition of the old fixedclip1 symbolic-cost relative packet.

G. hSZ explicitly supplies positive cSZ,C1,C2,C3,C4. Real.add_one_le_exp(-x) gives1-exp(-x)<=x. With x=C1*L>=0 also exp(-x)<=1. Expand the lower expression first, rather than multiplying a comparison by1-C2*K0*E. Thus, with no sign premise on this factor,
  1-Q <= (1-exp(-C1*L))+exp(-C1*L)*C2*K0*E+R
       <= C1*A+(C2*K0+1)*E.
For x=C3*L>=0, multiplying1-exp(-x)<=x by exp(x)>0 gives exp(x)-1<=x*exp(x). Since L<=1/4,
  exp(C3*L)-1<=C3*exp(C3/4)*L,
  exp(C3*L)<=exp(C3/4)<=exp(C3).
Consequently
  Q-1 <= C3*exp(C3/4)*A+(C4*K0*exp(C3/4)+2)*E.
This covers large cubicCost and nonpositive lower factors without changing the theorem.

H. Let S=1+C1+C2+C3+C4 and H=S*exp(C3)*(1+K0). All components are positive, S>=1, exp(C3)>=1, and1+K0>=1. Therefore C1<=H, C3*exp(C3/4)<=H, C2*K0<=H, C4*K0*exp(C3/4)<=H and1<=H. The lower E coefficient is<=2H, the upper E coefficient is<=3H, and both A coefficients are<=H. Since Ktail=8H, both signed deviations are<=Ktail*(A+E), and abs_le closes the proposed bound. This also proves0<Ktail. The preferred explicit constant is thus justified without optimizing it or changing quantifier dependencies.

## Boundary and scope checks

- n>=4 ensures positive sqrt(n) and rpow denominators. p>2 supplies p>0. beta=0 is an explicit branch; no positive-beta assumption is silently added.
- Gaussian tail is strictly positive for every real z. Physical zero denominator remains0, as in261; no atom continuity or almost-sure positivity is added.
- The envelope, tilt, geometry and original p windows all remain explicit. The absorption window is visibly additional. Nothing claims they follow from one another.
- Ktail depends on C1..C4 and a fixed numeric K0. The eventual n threshold is chosen before p or the hSZ constants. The new R threshold depends only on t0.
- hSZ is the explicit broader-L2 conditional input already used in261, not an established unconditional external Shao-Zhou theorem. No external SZ closure or publication novelty is claimed.
- Original bounded-polylog envelope source scope only. The original unbounded-envelope conditioning, p54 conditional uniformity consumers, compact CDF/atoms, DC and full OQ56/root remain OPEN. Existing original p51 S3/S19 and p54 corrected bytes stay read-only.
- All old accepted source/proof/machine evidence is reused exactly. No old producer, leaf AX, wholeproof readjudication or local/server Lean action is requested in this proposal stage.

## Transition condition and current runtime

Precise mathematical interface gap: none found for the proposed bounded-envelope conditional theorem. Administrative/evidence dependency:261 is still an unqualified sealed candidate; complete independent SOURCE/kernel/all-owned final evidence and explicit lead declaration freeze are both required before implementation. If261 changes, the affected interface/source binding must be updated first.

Actual local reads and proposal writes are complete. Current authority remains idle at PROPOSAL_READY, with no proof body and no source implementation, heavy0/inflight0/pendingExternal0/children0/uncertain0/publication0. This is not FINALWRITE and does not release ownership; await the lead's exact next activation. Requested model/effort are gpt-6.1-sol/xhigh; actual model/backend/effort and separate input/cached-input/output/reasoning-subset usage are unexposed and recorded null.
