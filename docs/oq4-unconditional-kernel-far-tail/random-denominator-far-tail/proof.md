# Random-denominator far energy tail — mathematical author proposal v1

Status: COMPLETE_MATHEMATICAL_PROOF_PROPOSAL; declarations NOT FROZEN; no Lean implementation, kernel check, axiom receipt or independent review exists for this unit. Author165, OQ4 lane. This is a source-bound auxiliary result, with no novelty claim. General OQ4 and the other random-denominator dependencies remain OPEN.

Source: `C:/game/shao/current/oq4/denom01.md`, complete file read, SHA256 `71b4f28df03edfe3cc8a4ff5f95beb7d80b716d4b7c64fed01a2dc6989448d3f`, especially lines79–112. E1 source: complete `energy01.md` read, SHA256 `2e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6`, with E1 used below. The original files are candidates; their status does not confer certification on this proof. Existing source repairs/p54 attribution are untouched.

## 1. Exact objects, statement and scope

Let ν be any probability measure on R, with genuinely integrable x² and |x|³ and ∫x²dν=1. Put β=∫|x|³dν, so β≥0. No mean assumption is used. Put π_n=ν^(Fin n), Q(a)=Σ_i a_i², S_k(a)=Σ_{i<k}a_i. For n≥1, M(a)=max_{1≤k≤n}|S_k(a)| is exactly `Shao.absMax`. For h>0 let x=h/sqrt(n) and

E(n,h)={a: |S_k(a)|≤x sqrt(Q(a)) for every 0≤k≤n}.

For n≥1 this is exactly {M≤x sqrt(Q)} because x sqrt(Q)≥0. In particular Q=0 implies all a_i=0 and belongs to E; no path is removed on account of zero energy. The definition using `closedStrip` is total at n=0, but no zero-time denominator identity is a theorem of this proposal. Every substantive finite far-tail bound assumes n≥1; the limit uses eventual positivity of n.

For every integer j≥1 set

H_j=sqrt(2^(j+1)) h,
F_j=E(n,h) ∩ {2^j n≤Q<2^(j+1)n}.

Here and below powers of2 are real natural powers. Define

Z(H,s)=∫ exp(su²/H²) 1_{|u|≤2H} dν(u),
Z(H,0)=ν.real{|u|≤2H},
C(s)=s exp(4s),
A(s)=1/8+s/2+exp(4s)s²,
D(s,ν)=A(s)β,
t=n/h², r=n/h³.

The exact finite estimates proved here are, for s>0, h≥1, n≥1:

(F1) π_n.real(F_j) ≤ [Z(H_j,s)^n−Z(H_j,0)^n]/[exp(s 2^j n/H_j²)−1].

If also log2≤st/2, then, simultaneously for every j≥1,

(F2) π_n.real(F_j) ≤ [2 C(s)t/2^(j+1)] exp(−st/4+D(s,ν)r/8),

(F3) π_n.real(E(n,h)∩{Q≥2n}) ≤ C(s)t exp(−st/4+D(s,ν)r/8).

Consequently, for any sequences n_k∈N, h_k∈R with h_k→+∞, n_k/h_k²→+∞, n_k/h_k³→0, and any fixed s>π²/2=4λ, λ=π²/8,

(L) π_(n_k).real(E(n_k,h_k)∩{Q≥2n_k}) / [(4/π) exp(−λ n_k/h_k²)] →0.

The denominator in(L) is the displayed positive real expression. No Brownian quantity, K, conditional MGF, self-normalized target asymptotic, bounded support, fourth moment, density or nonlattice premise occurs. No E4/E5 center/middle/window result is used. Unit second moment is an actual integral equality, not replacement of Q by a variance.

## 2. Direct finite product identity — no untruncated MGF

For H>0, s≥0 and any n define the closed cutoff box

B_H={a:∀i,|a_i|≤2H},
G_(H,s)(a)=1_(B_H)(a)[exp(s Q(a)/H²)−1].

All these functions/events are measurable: the coordinate evaluations are continuous, there are finitely many coordinates and prefixes, energy is continuous, and sqrt is continuous on R. The weak walls are closed; layer lower/upper inequalities give measurable half-open sets. For the variable random wall, the functions |S_k|−(h/sqrt n)sqrt Q are continuous for each fixed h,n, and one intersects their closed nonpositive sublevel sets for k≤n.

Let w_s(u)=`energyWeight H s u` and w_0(u)=`energyWeight H 0 u`. At every path,

(P1) G_(H,s)(a)=Π_i w_s(a_i)−Π_i w_0(a_i).

If a∈B_H, finite exponential multiplication gives Π_i exp(s a_i²/H²)=exp(sQ/H²), whereas Π_i1=1. If a∉B_H, there is a coordinate outside the box; that factor vanishes in both products and both sides of(P1) are0. For n=0 the box is all paths and both sides are0; this algebraic identity does not interpret a normalized zero-time maximum.

For u inside the cutoff, 0≤u²/H²≤4. Thus 0≤w_s≤exp(4s) and 0≤w_0≤1 globally. Both weights are integrable against the probability measure ν. The two finite product functions are integrable against π_n by `Integrable.fintype_prod`; alternatively their global bounds are exp(4sn) and1. Finite Fubini/product integration gives

∫Π_i w_s(a_i)dπ_n=Z(H,s)^n,
∫Π_i w_0(a_i)dπ_n=Z(H,0)^n.

Subtracting these two truly integrable products, using(P1), proves

(P2) ∫G_(H,s)dπ_n=Z(H,s)^n−Z(H,0)^n.

The integrand G is nonnegative: Q≥0 and s≥0. This is the cutoff-product integral of an exponential DIFFERENCE. It is not the difference of two merely formal infinite quantities. It uses neither the private product-density helper of `EnergyPathLaw` nor an assumption that the untruncated exponential is integrable. The direct product identity is the allowed alternative to the existing normalized density interface.

## 3. Nonnegative Markov difference and actual one-layer event

For any measurable A⊆B_H∩{Q≥q}, with q>0, s>0, H>0, let d=exp(sq/H²)−1>0. Pointwise, d1_A≤G_(H,s): on A use Q≥q and monotonicity of exp; outside A use G≥0. Both sides are integrable, so

d π_n.real(A) ≤ ∫G_(H,s)dπ_n.

Divide by the positive d and use(P2). This proves the generic finite difference Markov estimate with no centering or moment premise at all.

Now let n≥1, h>0, j≥1, a∈F_j. Since Q<2^(j+1)n, n>0, h>0,

(h/sqrt n)sqrt Q < sqrt(2^(j+1))h=H_j.

One may replace this strict inequality by its weak consequence. Every monitored prefix obeys |S_k|≤H_j, including S_0=0, so a∈`Shao.closedStrip H_j`. The qualified public theorem `Shao.abs_coordinate_le_two_mul_of_mem_closedStrip` gives |a_i|≤2H_j for every i. Therefore F_j⊆B_(H_j). Also Q≥2^j n>0. Apply the generic estimate with A=F_j, H=H_j, q=2^j n. This proves(F1), retaining lower energy equality and all cutoff equality atoms.

The following exact equalities/inequalities are used uniformly over j≥1:

H_j²=2^(j+1)h²,
2^j n/H_j²=t/2,
n/H_j²=t/2^(j+1),
H_j≥2h,
H_j³≥8h³,
n/H_j³≤r/8.

The square identity follows from sqrt(2^(j+1))²=2^(j+1)>0. The height inequality follows from 2^(j+1)≥4 and monotonicity of sqrt, and hence the cube comparison follows since both heights are positive. No implicit j-dependent constant appears.

## 4. Actual normalizer difference and first-order upper bound

For H>0, s≥0 and every u,

0≤w_s(u)−w_0(u)≤[C(s)/H²]u².

Outside |u|≤2H both weights vanish. Inside, the exponent v=su²/H² lies in[0,4s], and the qualified E1 primitive `energyTilt_weight_difference_inside` with T=s gives

|w_s(u)−1|≤exp(4s)s u²/H².

The left side w_s−1 is nonnegative there; this proves the global inequality. Integrate it using actual integrability of both weights and of u². Because ∫u²dν=1,

(N1) 0≤Z(H,s)−Z(H,0)≤C(s)/H².

Also Z(H,0)≥0 and hence Z(H,s)≥Z(H,0)≥0. For H≥1 the qualified E1 primitive `energyNormalizer_expansion` with T=s, |s|=s gives

|Z(H,s)−1−s/H²|≤A(s)β/H³.

Consequently

(N2) Z(H,s)≤1+u_H, u_H=s/H²+D(s,ν)/H³≥0.

The two constants C(s), A(s) depend on s alone. D=A(s)β depends on the fixed actual law only through β. The mean is unused. We deliberately use the raw normalizer expansion, rather than the combined `energyE1Conclusion` whose mean estimate has an unnecessary zero-mean hypothesis.

## 5. Powers, denominator and the uniform layer majorant

For real a≥b≥0, integer n≥1, u≥0 and a≤1+u,

(S1) a^n−b^n≤n(a−b)exp(nu).

Indeed a^n−b^n=(a−b)Σ_(k=0)^(n−1)a^(n−1−k)b^k. Every summand is ≤a^(n−1), so the difference is ≤n(a−b)a^(n−1). Since 1+u≤exp u, a^(n−1)≤exp((n−1)u)≤exp(nu). All multipliers are nonnegative; the case a=b, including a=b=0 and n=1, is covered without cancellation or division by a.

Apply(S1) with a=Z(H_j,s), b=Z(H_j,0), u=u_(H_j). Combining(N1)–(N2),

Z(H_j,s)^n−Z(H_j,0)^n
 ≤ C(s)(n/H_j²) exp(sn/H_j²+D(s,ν)n/H_j³).

For y=st/2≥log2, exp(−y)≤1/2. Therefore exp(y)−1=exp(y)(1−exp(−y))≥exp(y)/2 and

(S2) 1/[exp(st/2)−1]≤2exp(−st/2).

Insert these inequalities into(F1) and use the exact height identities:

π_n.real(F_j)
 ≤ [2C(s)t/2^(j+1)] exp(st/2^(j+1)+D(s,ν)n/H_j³−st/2)
 ≤ [2C(s)t/2^(j+1)] exp(−st/4+D(s,ν)r/8).

The last line uses j≥1, t≥0, D≥0, r≥0. It holds for EVERY j under the SAME h≥1 and log2≤st/2. Thus(F2) is a genuine uniform majorant, not an exchange of a pointwise limit and a supremum.

## 6. Exact dyadic cover and the absolute probability union

For n>0 and any finite real Q≥2n there exists exactly one integer j≥1 with 2^j n≤Q<2^(j+1)n. To prove existence without a logarithm or non-atomic assumption, the set

J={j∈N:1≤j and 2^j n≤Q}

is nonempty (j=1). It is finite: 2^j≥j+1 by induction, so membership implies j+1≤Q/n; choose a natural integer larger than Q/n. Let j be the largest element. If Q≥2^(j+1)n then j+1 would be a larger member, a contradiction. Uniqueness follows from strict increase of 2^j n. In particular Q=2^j n is assigned to layer j, not lost or counted in its predecessor. Hence the SET E∩{Q≥2n} equals the countable union of F_(k+1), k∈N.

The majorant in(F2) is summable: for k≥0,

2^(−((k+1)+1))=(1/4)(1/2)^k,
Σ_(k≥0)2^(−(k+2))=1/2.

For completeness, the finite partial sums are (1/2)(1−2^(−m)) and their limit is1/2, since (1/2)^m→0. Thus the series of nonnegative real layer probabilities is summable by comparison with(F2). Countable subadditivity applies to the actual probability measure π_n; converting to real values is legitimate because π_n is finite. Equivalently, apply finite union subadditivity to the first m layers, then continuity from below and the convergent numerical majorant. This proves

π_n.real(E∩{Q≥2n})≤Σ_(k≥0)π_n.real(F_(k+1))
 ≤ 2C(s)t exp(−st/4+Dr/8) (1/2),

which is(F3). This step controls the absolute infinite union, including arbitrarily large finite energies. It is not the assertion that each fixed layer is negligible.

## 7. Relative limit and eventual positive times

For the stated sequences put t_k=n_k/h_k² and r_k=n_k/h_k³. As h_k→+∞, eventually h_k≥1. As t_k→+∞, eventually t_k>0 and st_k/2≥log2. Since h_k≥1, t_k>0 implies n_k>0. Thus all hypotheses of(F3) hold eventually; no early n_k=0 value is used.

Let λ=π²/8 and δ=s/4−λ>0. The literal main term is positive because π>0 and exp is positive. Divide(F3) by this term to obtain the eventual bound

0≤relative far mass≤[C(s)π/4] t_k exp(−δt_k) exp(Dr_k/8).

Here exp(Dr_k/8)→1. To prove t exp(−δt)→0 without leaving a hidden asymptotic lemma, for t>0 use exp(δt/2)≥1+δt/2≥δt/2. Squaring yields exp(δt)≥δ²t²/4>0. Therefore

0≤t exp(−δt)≤4/(δ²t)→0 as t→+∞.

The product on the right tends to0, so the squeeze theorem proves(L). The assumption r_k→0 supplies the vanishing exponent correction; neither K nor any survival probability estimate enters. If a consumer already has n_k≥1 for all k it may use the same theorem directly; otherwise the eventual argument handles the finite prefix.

## 8. Proof and acceptance ledger

PROVED_HERE mathematically: direct finite cutoff-product difference identity; nonnegative difference Markov estimate; actual dyadic event inclusion; actual normalizer difference; finite uniform layer bound; exact dyadic cover; summable absolute-union bound; literal-main-term relative limit.

KNOWN_QUALIFIED_DEPENDENCIES reused at their actual public scope: finite paths/energy/closed strips and coordinate estimate; measurability; `energyWeight_integrable`; `energyNormalizer_expansion`; `energyTilt_weight_difference_inside`; standard finite Fubini/product integration and elementary real exp facts. Exact source hashes and public heads/values are in `api-evidence.md`.

No mathematical gap was found in this far calculation. The honest strengthening is that centering is unnecessary for this auxiliary statement; no assumption of the original OQ4 root is altered. No source candidate is declared formally proved. The next gate is parent substantive reading and freeze of ALL heads/values/imports in `declarations.lean.txt`, followed by authorized implementation, server kernel/all-owned transitive-axiom gate and a separate qualified complete source-to-statement/proof review. This author owns only this draft directory and has performed no Lean/server/Git/shared-source operation.
