# Unit 158: source parameters pay the actual tilted drift and event

Source: supplement.tex lines 5094–5101 and 5123–5130. The two exact heads pay
the deterministic parameter conditions needed by unit157, rather than assuming
the desired small drift. For beta>=1,L>=0,s>=0,x>=1, time s*n<=L*x^2 and
rank n>=4000000*(1+L)^2*beta^2*(1+x)^6 imply n>0,n>=4*x^2,
s*beta^2<=1/128 and sqrt(n)*(2*s*beta)<=1/(1000*(1+x)).

The second head uses the auxiliary centered unit-second-moment probability law
with its genuine absolute third moment beta, literal native energy tilt rho
and actual mu=integral z drho. Beta>=1 is paid by unit152. The parameter head
pays the small-s condition of the actual unit152 mean bound. Thus the actual
sqrt(n)*|mu| satisfies the small drift budget. For every actual raw path with
energy>=n/8, its raw weak endpoint event at a=sqrt(9*x^2/4-1) implies the true
centered weak endpoint event at y=a-1/(100*(1+x)), by exact unit157.

This is a source-bound explicit sufficient rank. If the source l>=
K*beta^2*(1+x)^6/2 is used, choose K>=8000000*(1+L)^2 once after fixing L.
For l=t or t-1, the source st<=L*x^2 also gives sl<=L*x^2 by l<=t,s>=0;
this deterministic transport is not an extra assumed drift conclusion. The
finite3 hypotheses belong only to the auxiliary preprocessed law and do not
change the original finite2 sample-law assumptions.

For the parameter proof put c=1+L,d=1+x. The actual rank gives
sqrt(n)>=2000*c*beta*d^3>0. Positive products imply n>=4*x^2 and
n>=128*beta^2*L*x^2. Multiply the time bound by128*beta^2, then cancel the
proved positive n to obtain s*beta^2<=1/128. Multiply the square-root rank
by s*sqrt(n):
c*d^2*(1000*d*sqrt(n)*(2*s*beta))<=s*n<=L*x^2<=c*d^2.
Cancellation of the genuinely positive c*d^2 and positive1000*d yields the
desired drift budget. All divisions and cancellations have explicit signs;
L=0 and s=0 are included. The second proof consumes the exact152 actual mean
and the exact157 actual finite-path event without a new drift premise.

All imports/context/two heads were frozen before implementation and remain
unchanged. Attempt001 is preserved: two positive-factor cancellation expressions
used generic multiplication lemmas instead of the pinned native iff aliases.
Only those two proof expressions changed after reading the exact native
GroupWithZero/Defs signatures. Attempt002 passed. The all-owner map contains
two public theorems, no private/generated owners or non-theorem values. Every
recursive axiom is propext, Classical.choice or Quot.sound. No successful old
kernel/audit was replayed.

Author writer/execution release is for complete fresh independent exact-source
review. The centered law's legal own C1 budget, product/measure transport and
complete rare-suffix estimate remain subsequent dependencies. Current root
registry v85 records original C1 complete and C2/C12 open; this unit does not
claim a further root closure.
