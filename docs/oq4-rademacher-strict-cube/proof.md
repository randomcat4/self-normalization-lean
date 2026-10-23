# Strict Rademacher survival on the frozen perfect-cube subsequence

STATUS: PROVED

This is a mathematical proof of F1--F4 of `frozen-rademacher-strict-cube-v1.md` (SHA256 `aa5cfc0f508ffb7a3b2cf88cb5a7ae1955e10f364ca73278003305b8f73457fd`). It uses the public statements specified below. It makes no claim of a new Lean verification, a general-distribution result, or closure of the original OQ4 root.

## 1. Objects, notation, and the public inputs actually used

Fix the law

\[
\nu=\tfrac12\delta_1+\tfrac12\delta_{-1},\qquad
\mu_n=\bigotimes_{i\in\operatorname{Fin}n}\nu
\]

on the actual space \(\operatorname{Path}n=\operatorname{Fin}n\to\mathbb R\), with its product Borel measurable space. These are exactly `RademacherCosine.law` and `RademacherS5Assembly.pathLaw n`. In particular, each \(\mu_n\) is a probability measure. The transparent path definitions are

\[
S_r(a)=\operatorname{prefixSum}(a,r)
 =\sum_{i\in\operatorname{Fin}n,\ i<r}a_i,\qquad
E(a)=\operatorname{energy}(a)=\sum_{i\in\operatorname{Fin}n}a_i^2,
\quad V(a)=\sqrt{E(a)}.
\]

The sum is saturated at the path length, exactly as in the source definition. For all real \(h,s\), set

\[
\begin{split}
A_{n,h}&=\{a:\ \forall r\in\mathbb N,
                    \ 1\le r\le n\Longrightarrow |S_r(a)|<h\},\\
C_{n,h}&=\{a:\ \forall r\in\mathbb N,
                    \ r\le n\Longrightarrow |S_r(a)|\le h\},\\
\mathcal S_{n,s}&=\{a:\ \forall r\in\mathbb N,
                    \ 1\le r\le n\Longrightarrow |S_r(a)|<sV(a)\}.
\end{split}
\]

Here \(C_{n,h}\) is exactly `Shao.closedStrip`. Write
\(p_<(n,h)=\mu_n^{\rm real}(A_{n,h})\) and
\(p_\le(n,h)=\mu_n^{\rm real}(C_{n,h})\). The latter is the same function `p` in S4 and S5, by their public definition bridges; it is not defined through a spectral expression.

Fix, independently of all the preceding objects, any type \(\Omega\), measurable space on it, probability measure \(P\), process
\(B:\mathbb R_{\ge0}\to\Omega\to\mathbb R\), and
\(h_B:\operatorname{IsBrownianReal}(B,P)\). In the rest of the proof,

\[
b(z)=\operatorname{Shao.Probability.BrownianSup.probability}(B,P,h_B,z),
\quad \lambda=\pi^2/8,\quad a=\pi^2/4=2\lambda,
\quad g(z)=\frac4\pi\exp(-\lambda/z^2).
\]

In particular \(b(z)=P^{\rm real}\{U\le z\}\) for the actual measurable Brownian supremum variable of the public interface, and it also equals the actual full-strip probability. The public theorem `BrownianSup.measurable_U` supplies the measurability of this Brownian event. No coupling of \(B\) with the finite paths is required or used.

The following are the only non-elementary mathematical inputs to the argument.

**Input S4 (KNOWN).** The public `RademacherS4Assembly.S4_ALL`, with `definition_bridges`, `actual_brownian_bridges`, and `S4Outputs`, has the following consequence for the actual functions just fixed. If natural sequences \(m_j,n_j\) and a real sequence \(h_j\) satisfy, for every \(j\),

\[
1\le m_j,\quad m_j\le h_j<m_j+1,
\qquad h_j\longrightarrow+\infty,\quad n_j/h_j^2\longrightarrow+\infty,
\]

and \(n_j/h_j^3\) is eventually bounded by one fixed positive constant, then, writing
\(H_j=m_j+1\) and \(y_j=h_j/\sqrt{n_j}\),

\[
\log\frac{p_\le(n_j,h_j)}{b(y_j)}
 -a\frac{n_j}{h_j^3}(H_j-h_j)\longrightarrow0. \tag{I4}
\]

All natural quantities in real formulas are cast to \(\mathbb R\). The same conclusion supplies a natural tail threshold on which \(n_j>0\), \(y_j>0\), \(p_\le(n_j,h_j)>0\), \(b(y_j)>0\), and their quotient is positive, and on which its logarithm equals the difference of the two probability logarithms. These are outputs of the theorem, not additional hypotheses in this proof.

**Input S5-CUBE (KNOWN).** The public `RademacherS5Assembly.S5_CUBE`, through `PhaseOutputs` and `PhaseLimits`, gives, for exactly
\(\sigma(j)=(j+1)^3\),

\[
\begin{split}
Q_1(\sigma(j))&\longrightarrow e^a,\\
\log Q_1(\sigma(j))&\longrightarrow a,
\end{split} \tag{I5}
\]

where
\(Q_1(n)=p_\le(n,\operatorname{height}(1,n))/b(\operatorname{x}(1,n))\),
\(\operatorname{height}(1,n)=(n:\mathbb R)^{1/3}\), and
\(\operatorname{x}(1,n)=(n:\mathbb R)^{-1/6}\), with the exact `Real.rpow` definitions. It also gives a tail on which these actual probabilities and ratios are positive and their probability/log identities hold. Its `PhaseOutputs` additionally includes every fixed natural index shift. We will verify that our sequence is the shift by exactly one, rather than substitute a sequence with the same phase.

**Input B1 (KNOWN).** The public `BrownianSup.actual_brownian_firstTerm` says

\[
\forall\epsilon>0\ \exists\delta>0\ \forall z,
\quad 0<z<\delta\Longrightarrow |b(z)/g(z)-1|<\epsilon. \tag{IB}
\]

The public `actual_brownian_eventually_positive` also gives a \(\delta_B>0\) such that \(0<z<\delta_B\) implies \(b(z)>0\) and \(b(z)/g(z)>0\). The displayed definition of `firstTerm` is exactly \(g\). No exponential error estimate, rate of convergence in (IB), or positivity for every positive real argument is an input here.

All remaining arguments below are proved directly. The exact locations and hashes of these inputs, and of every other file projection read, are recorded in `receipt.json`. In particular no upstream implementation proof is used.

## 2. Measurability, support, and the integer bridge (F1)

For fixed \(n,r\), \(S_r\) is a finite sum of continuous coordinate projections, so it is continuous on the finite product \(\mathbb R^{\operatorname{Fin}n}\). The function \(E\) is a finite sum of squared coordinates and is continuous and nonnegative. Since the real square-root function is continuous, \(V=\sqrt E\) is continuous as well. Consequently, for every real \(h,s\),

\[
A_{n,h}=\bigcap_{r=1}^n\{a:|S_r(a)|<h\},\qquad
C_{n,h}=\bigcap_{r=0}^n\{a:|S_r(a)|\le h\},
\]

and

\[
\mathcal S_{n,s}=\bigcap_{r=1}^n
   \{a:|S_r(a)|-sV(a)<0\}
\]

are measurable sets. In fact the strict sets are open and the weak set is closed. This includes empty intersections: \(A_{0,h}=\mathcal S_{0,s}=\operatorname{univ}\) for every real \(h,s\). Thus \(p_<(0,h)=1\), with no condition on \(h\).

Let

\[
G_n=\{a:\ \forall i\in\operatorname{Fin}n,\ a_i\in\{1,-1\}\}.
\]

The fixed one-coordinate law satisfies \(\nu(\{1,-1\})=1\), by its two Dirac summands. The finite-product rectangle formula therefore gives
\(\mu_n(G_n)=\prod_{i\in\operatorname{Fin}n}1=1\). This also proves the assertion when \(n=0\), since the product is empty. This is one common measurable set for all coordinates, all partial sums, and the energy, rather than a separate exceptional set chosen for each test.

For \(a\in G_n\), choose, deterministically, \(z_i=1\in\mathbb Z\) when \(a_i=1\), and \(z_i=-1\) otherwise. Then \(a_i=(z_i:\mathbb R)\), and for every natural \(r\),

\[
S_r(a)=\left(\sum_{i<r}z_i:\mathbb R\right).
\]

Thus every partial sum is an integer and its absolute value is the real cast of a nonnegative integer. This conclusion has been derived from the fixed product law, not assumed.

Now fix arbitrary natural \(n,k\) with \(k\ge2\), and put \(m=k-1\) using natural subtraction. Since \(1\le k\), subtraction has its ordinary value: \(m+1=k\), \(m\ge1\), and

\[
(m:\mathbb R)=(k:\mathbb R)-1. \tag{2.1}
\]

For any nonnegative integer \(d\), integer discreteness gives
\(d<k\) if and only if \(d\le k-1=m\). (Indeed, \(d<k\) means \(d+1\le k\), and conversely \(d\le m\) gives \(d< m+1=k\).) Real casting preserves these comparisons. Applying this to the integer absolute value above gives, on \(G_n\), for every \(1\le r\le n\),

\[
|S_r(a)|<(k:\mathbb R)
\quad\Longleftrightarrow\quad |S_r(a)|\le(m:\mathbb R). \tag{2.2}
\]

The additional \(r=0\) condition in \(C_{n,m}\) is true: \(S_0=0\) by the empty sum, and \(0\le m\). Thus

\[
a\in A_{n,k}\quad\Longleftrightarrow\quad a\in C_{n,k-1}
\qquad(a\in G_n). \tag{2.3}
\]

Since \(G_n\) has full \(\mu_n\)-measure, the actual strict and weak sets are equal almost everywhere. Equalities of the measures, and then of their real values, give

\[
p_<(n,k)=p_\le(n,k-1) \qquad(n\in\mathbb N,\ k\ge2). \tag{2.4}
\]

For \(n=0\) both events in (2.3) are the whole path space: the strict condition is empty and the sole weak condition is \(0\le k-1\). Hence both sides of (2.4) are exactly one. There is no omitted zero-time case.

On the same set \(G_n\), every squared coordinate is one, so the genuine energy and its square root satisfy

\[
E(a)=\sum_{i\in\operatorname{Fin}n}1=(n:\mathbb R),
\qquad V(a)=\sqrt{(n:\mathbb R)}. \tag{2.5}
\]

For \(n\ge1\) this also proves that the zero-energy set has probability zero; for \(n=0\) the energy is identically zero. No path model or zero-energy convention has been altered in obtaining (2.5).

## 3. Exact geometry of the frozen subsequence (F2)

For every \(j\in\mathbb N\), set exactly as frozen

\[
k_j=j+2,\qquad n_j=k_j^3,\qquad
K_j=(k_j:\mathbb R),\quad N_j=(n_j:\mathbb R)=K_j^3,
\quad x_j=K_j/\sqrt{N_j}.
\]

The equality \(N_j=K_j^3\) is the ordinary natural-to-real cast of the natural cube. Always \(k_j\ge2\), \(n_j\ge8\), and \(K_j,N_j>0\). If \(i<j\), then \(k_i<k_j\), and

\[
k_j^3-k_i^3=(k_j-k_i)(k_j^2+k_jk_i+k_i^2)>0.
\]

This proves that \(j\mapsto n_j\) is strictly increasing. In particular this proof keeps \(j=0\): \(k_0=2\), \(n_0=8\), and \(x_0=1/\sqrt2\).

The positive real number \(K_j\sqrt{K_j}\) has square \(K_j^3=N_j\); the uniqueness of the nonnegative square root yields

\[
\sqrt{N_j}=K_j\sqrt{K_j},\qquad
x_j=\frac1{\sqrt{K_j}}>0,\qquad
x_j\sqrt{N_j}=K_j. \tag{3.1}
\]

Here cancellation is legitimate since \(K_j>0\). To check the real-power convention explicitly, \(N_j>0\) permits the defining formula \(N_j^t=\exp(t\log N_j)\). Since \(\log N_j=3\log K_j\),

\[
N_j^{1/3}=\exp(\log K_j)=K_j,\qquad
N_j^{-1/6}=\exp(-\tfrac12\log K_j)=\frac1{\sqrt{K_j}}=x_j. \tag{3.2}
\]

Thus these are exact `Real.rpow` values with positive base and real exponents; no free cube root is introduced. Equations (3.1)--(3.2) give

\[
\operatorname{S5.height}(1,n_j)=K_j,
\qquad \operatorname{S5.x}(1,n_j)=x_j. \tag{3.3}
\]

Also

\[
\frac{N_j}{K_j^2}=K_j\longrightarrow+\infty,
\qquad x_j=1/\sqrt{K_j}\longrightarrow0. \tag{3.4}
\]

For completeness, \(K_j=j+2\) tends to positive infinity by the Archimedean property. Given \(\epsilon>0\), once \(K_j>\epsilon^{-2}\), (3.1) gives \(0<x_j<\epsilon\); this proves the second limit from the positive side.

By (2.5), for each \(j\) the identity \(V=\sqrt{N_j}\) holds on \(G_{n_j}\), a full-measure set. Combining it with (3.1) shows, on that same set,

\[
x_j V(a)=x_j\sqrt{N_j}=K_j.
\]

Consequently \(\mathcal S_{n_j,x_j}\) and \(A_{n_j,k_j}\) are equal almost everywhere, and

\[
\mu_{n_j}^{\rm real}(\mathcal S_{n_j,x_j})=p_<(n_j,k_j). \tag{3.5}
\]

Their measurability was proved for every real threshold in Section 2. Dividing (3.5) by the same actual \(b(x_j)\) gives exactly the frozen \(R_<(j)\), including as a total real quotient at every \(j\). The ordinary positive-probability interpretation on a common tail is established in Section 7.

## 4. Apply generic S4 to the actual adjacent weak threshold

Define natural \(m_j=k_j-1\) and real
\(h_j=(m_j:\mathbb R)=K_j-1\). By (2.1), these are the same threshold. We have, for every \(j\),

\[
1\le m_j,\quad h_j=m_j<m_j+1=K_j,
\quad H_j=m_j+1=K_j,
\quad H_j-h_j=1. \tag{4.1}
\]

Here the inequalities with real terms use the specified casts. Thus the all-index weak-cell hypotheses of S4 hold even at \(j=0\), where \(m_0=h_0=1\).

The three scale hypotheses can all be checked explicitly. First \(h_j=K_j-1\to+\infty\). Second,

\[
\frac{N_j}{h_j^2}
=K_j\left(\frac{K_j}{K_j-1}\right)^2\ge K_j\longrightarrow+\infty.
\]

Finally, since \(K_j\ge2\),

\[
1<\frac{K_j}{K_j-1}=1+\frac1{K_j-1}\le2,
\qquad
0<\frac{N_j}{h_j^3}=\left(\frac{K_j}{K_j-1}\right)^3\le8. \tag{4.2}
\]

Thus the fixed S4 bound may be chosen as \(M=8\) and the bound's tail threshold as zero. Moreover \(1/(K_j-1)\to0\), so

\[
\frac{N_j}{h_j^3}\longrightarrow1. \tag{4.3}
\]

Put

\[
y_j=\frac{K_j-1}{\sqrt{N_j}}
       =x_j\left(1-\frac1{K_j}\right),\qquad
Q^-_j=\frac{p_\le(n_j,h_j)}{b(y_j)}.
\]

For all \(j\), \(0<y_j<x_j\), so \(y_j\to0\) from the positive side. S4 applies to precisely the three sequences \((m_j,n_j,h_j)\), without a change of law, time, or real threshold. It yields a natural \(J_-\) such that for all \(j\ge J_-\),

\[
p_\le(n_j,h_j)>0,\quad b(y_j)>0,\quad Q^-_j>0,
\quad \log Q^-_j=\log p_\le(n_j,h_j)-\log b(y_j), \tag{4.4}
\]

and (I4), (4.1), and (4.3) yield

\[
\log Q^-_j-a\frac{N_j}{h_j^3}\longrightarrow0,
\qquad \log Q^-_j\longrightarrow a. \tag{4.5}
\]

On this positive tail \(Q^-_j=\exp(\log Q^-_j)\). By continuity of the exponential and eventual equality of these actual sequences,

\[
Q^-_j\longrightarrow e^a. \tag{4.6}
\]

This step uses generic S4. It does not apply any fixed-\(c\) S5 result to a varying value \(1-1/k_j\).

## 5. The actual Brownian denominator shift and its nonzero constant

Define the actual normalized first-term value \(T(z)=b(z)/g(z)\). Since \(4/\pi>0\) and the exponential is positive, \(g(z)>0\). By (IB) and the positive-side convergence of \(x_j,y_j\),

\[
T(x_j)\longrightarrow1,\qquad T(y_j)\longrightarrow1. \tag{5.1}
\]

The stated Brownian positivity theorem and these convergences supply a natural \(J_B\) such that for all \(j\ge J_B\),
\(b(x_j),b(y_j),T(x_j),T(y_j)>0\). More explicitly, take its \(\delta_B>0\) and use \(x_j,y_j\to0^+\) to put both arguments in \((0,\delta_B)\); the maximum of the resulting two natural thresholds is a permissible \(J_B\).

Set

\[
D_j=\frac1{y_j^2}-\frac1{x_j^2}.
\]

Every denominator in the following computation is nonzero for every \(j\), by \(K_j\ge2\) and \(N_j>0\). Using \((\sqrt{N_j})^2=N_j=K_j^3\) gives the exact identities

\[
\begin{split}
D_j
&=N_j\left(\frac1{(K_j-1)^2}-\frac1{K_j^2}\right)\\
&=\frac{K_j(2K_j-1)}{(K_j-1)^2}\\
&=2+\frac3{K_j-1}+\frac1{(K_j-1)^2}
\longrightarrow2. \tag{5.2}
\end{split}
\]

In particular the exponent change does not tend to zero. The first-term quotient is exactly

\[
\frac{g(y_j)}{g(x_j)}=\exp(-\lambda D_j)
\longrightarrow \exp(-2\lambda)=e^{-a}. \tag{5.3}
\]

On the tail \(j\ge J_B\), using the actual definitions \(b=Tg\),

\[
L_j:=\frac{b(y_j)}{b(x_j)}
 =\frac{T(y_j)}{T(x_j)}\exp(-\lambda D_j).
\]

By (5.1), division continuity at denominator one, and (5.2),

\[
L_j\longrightarrow e^{-a}. \tag{5.4}
\]

All the quantities on this tail are positive. The logarithm is continuous at one, so (5.1) gives \(\log T(x_j),\log T(y_j)\to0\), and hence

\[
\log L_j=\log T(y_j)-\log T(x_j)-\lambda D_j
\longrightarrow-a. \tag{5.5}
\]

This argument consumes only the actual first-term equivalence and its stated positivity. It explicitly accounts for the full constant caused by moving the Brownian denominator.

## 6. The two actual multiplier limits (F3)

By (2.4), \(p_<(n_j,k_j)=p_\le(n_j,h_j)\) for every \(j\). Therefore, on the tail where both Brownian probabilities are positive,

\[
R_<(j)=\frac{p_<(n_j,k_j)}{b(x_j)}=Q^-_j L_j. \tag{6.1}
\]

Taking limits in (6.1), using (4.6) and (5.4), gives

\[
R_<(j)\longrightarrow e^a e^{-a}=1. \tag{6.2}
\]

On the positive tail the logarithm of (6.1) is
\(\log R_<(j)=\log Q^-_j+\log L_j\). Equations (4.5) and (5.5) thus give

\[
\log R_<(j)\longrightarrow a-a=0. \tag{6.3}
\]

For the weak multiplier, let \(\sigma(j)=\operatorname{S5.cubeSeq}(j)\). Its transparent definition is
\(\operatorname{CP.cubeIndex}(j+1)=(j+1)^3\). For every natural \(j\), natural addition associativity gives the exact fixed-shift identity

\[
n_j=(j+2)^3=\sigma(j+1)
          =\operatorname{S5.shift}(\sigma,1)(j). \tag{6.4}
\]

The source sequence has not been replaced by an arbitrary phase-equivalent sequence; (6.4) identifies every term, including \(n_0=8=\sigma(1)\). From (3.3) and the definitions,

\[
R_\le(j)=\frac{p_\le(n_j,k_j)}{b(x_j)}
          =Q_1(\sigma(j+1)). \tag{6.5}
\]

The fixed shift tends to infinity and is explicitly included in S5's `PhaseOutputs`. Applying (I5) along that shift, with its positive tail, gives

\[
R_\le(j)\longrightarrow e^a,
\qquad \log R_\le(j)\longrightarrow a. \tag{6.6}
\]

It also gives a natural \(J_+\) such that, for every \(j\ge J_+\), \(p_\le(n_j,k_j)>0\), \(b(x_j)>0\), \(R_\le(j)>0\), and its probability/log identity holds. This completes both weak and strict limits for the exact frozen sequence.

## 7. One common legal tail and all needed log identities (F2)

Take the natural number

\[
J=\max\{J_-,J_B,J_+\}.
\]

The three thresholds are outputs already constructed above; they can depend on the fixed Brownian data. There is no hypothesis asserting uniformity over Brownian realizations or sequences. For every natural \(j\ge J\), the following actual quantities are simultaneously positive:

\[
\begin{gathered}
p_<(n_j,k_j)=p_\le(n_j,h_j),\quad p_\le(n_j,k_j),\quad
b(x_j),\quad b(y_j),\\
Q^-_j,\quad L_j,\quad R_<(j),\quad R_\le(j),\quad
p_\le(n_j,k_j)/p_<(n_j,k_j).
\end{gathered} \tag{7.1}
\]

The strict numerator is positive by (2.4) and (4.4); the strict ratio is positive by (6.1), or directly by positive division. The self-normalized strict numerator in (3.5) is the same positive number. Positive real division and multiplication now give, for all these same \(j\),

\[
\begin{split}
\log R_<(j)
 &=\log p_<(n_j,k_j)-\log b(x_j),\\
\log R_\le(j)
 &=\log p_\le(n_j,k_j)-\log b(x_j),\\
\log Q^-_j
 &=\log p_<(n_j,k_j)-\log b(y_j),\\
\log L_j&=\log b(y_j)-\log b(x_j),\\
\log R_<(j)&=\log Q^-_j+\log L_j,\\
\frac{p_\le(n_j,k_j)}{p_<(n_j,k_j)}
 &=\frac{R_\le(j)}{R_<(j)},\\
\log p_\le(n_j,k_j)-\log p_<(n_j,k_j)
 &=\log R_\le(j)-\log R_<(j)\\
 &=\log\frac{p_\le(n_j,k_j)}{p_<(n_j,k_j)}
  =\log\frac{R_\le(j)}{R_<(j)}.
\end{split} \tag{7.2}
\]

The first identity remains identical after replacing its strict numerator by \(\mu_{n_j}^{\rm real}(\mathcal S_{n_j,x_j})\), by (3.5). Thus the actual strict self-normalized ratio and its logarithm have precisely the meanings and limits asserted for \(R_<\).

The frozen all-index definitions are kept at every \(j\); no values of an early term are reassigned. If they are represented with total real division and `Real.log`, each calculation requiring ordinary division/logarithms above is an eventual equality on (7.1). Removing a finite initial set when proving a limit is justified by eventual equality and changes no definition or quantifier of the frozen statement. The event and geometric assertions, in contrast, were proved for every \(j\), including zero.

## 8. Adjacent probabilities and normalization by the main rate (F4)

By (7.2), the two probabilities are compared at the same time \(n_j\). The limits (6.2) and (6.6), with limiting denominator \(1\ne0\), give

\[
\frac{p_\le(n_j,k_j)}{p_<(n_j,k_j)}
 =\frac{R_\le(j)}{R_<(j)}
\longrightarrow e^a. \tag{8.1}
\]

The logarithmic difference in (7.2) has limit

\[
\log p_\le(n_j,k_j)-\log p_<(n_j,k_j)
 =\log R_\le(j)-\log R_<(j)
\longrightarrow a-0=a. \tag{8.2}
\]

Finally the exact identity \(N_j/K_j^2=K_j>0\) from (3.4) and \(1/K_j\to0\) give

\[
\begin{split}
\frac{\log R_<(j)}{N_j/K_j^2}
 &=\log R_<(j)\frac1{K_j}\longrightarrow0\cdot0=0,\\
\frac{\log R_\le(j)}{N_j/K_j^2}
 &=\log R_\le(j)\frac1{K_j}\longrightarrow a\cdot0=0.
\end{split} \tag{8.3}
\]

These are limits of actual probability ratios and, on the common tail, ordinary actual probability logarithms. In particular (8.2) is a nonzero constant change which (8.3) loses under main-rate normalization.

## 9. Quantifier and boundary ledger

| Frozen obligation | Where proved and exact coverage |
|---|---|
| Fixed law and actual path energy | Sections 1--2; exactly the given Rademacher product law for every natural path length. Coordinate support, integer partial sums, and energy are derived from that law. |
| Arbitrary real strict thresholds; event measurability | Section 2 proves measurability of \(A_{n,h}\) and \(\mathcal S_{n,s}\) for every \(n\in\mathbb N\), \(h,s\in\mathbb R\), and of the actual weak event. No arbitrary-real-threshold lattice classification is asserted. |
| Integer bridge | Section 2 proves (2.4) for every \(n\in\mathbb N\), every natural \(k\ge2\); both natural subtraction and its real cast are explicit. |
| Path length zero | Strict events are empty intersections for every real threshold; at the bridge's weak threshold both probabilities are one. Energy is identically zero there. |
| Index zero of the frozen sequence | All event and geometry identities hold at \(j=0\), with \(n_0=8\). Positivity of Brownian denominators is only claimed on the displayed output tail. |
| Exact powers and sequence | Sections 3 and 6 prove the positive-base real-power identities, the natural cube identity, and the exact S5 shift by one. |
| Actual strict self-normalization | (2.5), (3.1), and (3.5) derive the almost-everywhere identity and measurable-event probability equality for every \(j\). |
| Arbitrary Brownian data | The proof fixes arbitrary \((\Omega,P,B,h_B)\) once; all uses refer to its same actual \(b\). No finite-path/Brownian independence or coupling is added. |
| S4 hypotheses and phase | Section 4 checks all-index \(m\ge1\), the entire weak cell, both divergent scales, and the single fixed bound \(M=8\); its weak phase is exactly one. No parity assumption is used. |
| Brownian shift constant | (5.2) proves the exact inverse-square difference tends to two, and (5.3)--(5.5) retain its factor \(e^{-a}\). |
| Common legal tail | Section 7 constructs one natural \(J\) with every positivity and log identity as a conclusion. There is no all-positive-input premise. |
| All limits F3--F4 | (6.2), (6.3), (6.6), and (8.1)--(8.3), on the original frozen index set. |

No target conclusion is an input. No theorem for a fixed scale parameter is applied with a varying scale parameter. No stronger Brownian error bound is assumed. There are no remaining mathematical lemmas marked OPEN in this proof. This proof establishes the specified perfect-cube assertion only: it does not assert a uniform finite \(O(n/h^3)\) theorem, a noninteger strict-phase classification, or a general-distribution OQ4 result. Independent verification of this anonymous proof and any subsequent formal implementation are separate work.

## 10. Precise mathematical source/interface references

1. Frozen target: `C:/game/shao lean/drafts/oq4/frozen-rademacher-strict-cube-v1.md`, full lines 1--116, 7454 bytes, SHA256 `aa5cfc0f508ffb7a3b2cf88cb5a7ae1955e10f364ca73278003305b8f73457fd`.
2. Original source: `C:/game/shao/current/oq4/c01/spectrum01.md`, full lines 1--119 read; primary target lines 112--115 and restricted consequences of 116, 118--119, 4306 bytes, SHA256 `b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b`. The source is not used as a proof of the target; its conclusions are proved above using the frozen interfaces.
3. S4 mathematical declaration: `C:/game/shao lean/drafts/oq4/frozen-rademacher-s4-probability-assembly-v1.md`, definitions and statements 49--165, 11831 bytes, SHA256 `144e3c290ca60c174ceec0cc85b41519a82faf0eb55c09a1c54e61e1d097e00a`.
4. S4 public formal declaration freeze: `C:/game/shao lean/drafts/oq4/frozen-rademacher-s4-formal-statements-v1.lean.txt`, exact definitions 25--170, bridges 172--221, and `S4_ALL` 233--244, 16426 bytes, SHA256 `0c4af1e038d7290b08daf6da9578519be7ffc913611f91fca2b833129d5fe6f1`. Only the named public statement consequences in Input S4 are consumed.
5. S5 mathematical declaration: `C:/game/shao lean/drafts/oq4/frozen-rademacher-s5-probability-phase-v1.md`, definitions/statements 46--163, especially 142--161, 15006 bytes, SHA256 `b79dd1cb131277acab9f156668ed1fde8aafa9c6632b821951719617b701b04d`.
6. S5 public formal declaration freeze: `C:/game/shao lean/drafts/oq4/frozen-rademacher-s5-formal-statements-v1.lean.txt`, definitions 27--75, probability/log predicates 101--128, `PhaseLimits`/`PhaseOutputs` 212--228, definition bridges 230--251, and `S5_CUBE` 344--351, 24193 bytes, SHA256 `1b1ad31b8147cb142f7c5bca262903abe11428cc186e93b967a5adaeb01dd6a4`. The support/energy statement at 266--270 was visible as a public head but (2.5) is proved directly above.
7. Exact natural cube-index definition: `C:/game/shao lean/drafts/oq4/frozen-rademacher-critical-phase-formal-statements-v2.lean.txt`, line 44 `cubeIndex(k)=k^3`, 10959 bytes, SHA256 `d2656efb76cbbdba2ad08bc9352b05270461e466aec8a94d09b9dca0ed60a4bc`.
8. Transparent finite-path definitions: `C:/game/shao lean/library/Shao/Basic/FinitePath.lean`, lines 18--31; actual weak-event definition: `C:/game/shao lean/library/Shao/Basic/ClosedSurvival.lean`, lines 26--27; fixed law definition: `C:/game/shao lean/library/Shao/OQ4/RademacherCosine.lean`, lines 15--19. Their file hashes and all additional header-only projections appear in the read ledger.
9. Actual Brownian input: `C:/game/shao lean/library/Shao/Probability/BrownianFirstTerm.lean`, public theorem heads `actual_brownian_firstTerm` 143--145 and `actual_brownian_eventually_positive` 154--156, with parameters from 28--30; 8289 bytes, SHA256 `f4faa8c89016aea74dd16c8ea0dc359213390413d3ab0faff234dd98d0a87c6a`. Their implementation proofs were masked before the first `:=` and not read.
10. Exact first term: `C:/game/shao lean/library/Shao/Probability/BrownianSpectralEnvelope.lean`, transparent definition 12--13, 10152 bytes, SHA256 `97e1a9f13d2b86874b94df93540d3355dcc38dac8dff81ad3a823ded68396fc7`; actual Brownian variable measurability: `C:/game/shao lean/library/Shao/Probability/BrownianSup.lean`, public head `measurable_U` at line 127. No envelope proof or Brownian approximation proof was read.
