# Actual conditional energy concentration E4 — author163 mathematical proposal

Status: COMPLETE MATHEMATICAL COMPOSITION, PROPOSAL ONLY. This is not a declaration freeze, an implemented Lean module, an independent review, or an acceptance receipt. Its K/Kv producer is the still-unqualified future `UnconditionalKernelAsymptotic` interface. The derivation below contains no additional mathematical obligation after those exact producer theorems; their qualification, this proposal's declaration freeze, implementation and independent review remain unpaid. Original OQ4 and random-denominator roots stay OPEN.

Source: all 125 lines of `C:/game/shao/current/oq4/energy01.md` were read, SHA256 `2e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6`. The target is E4, lines99–120, specifically (11) and (12), with the true K/Kv producer imported rather than a desired-limit hypothesis. The proof reuses qualified E1/E2 and scalar E3 transport. It neither duplicates nor proves the separately owned two-variable operator identities E3(9)–(10).

## 1. Objects, quantifiers and unchanged assumptions

Let ν be one fixed actual Borel probability measure on ℝ. Assume only

\[
\int |x|^3\,dν<\infty,\qquad \int x\,dν=0,\qquad \int x^2\,dν=1.
\]

The first assumption is genuine `Integrable (fun x => |x|^3) ν`; lower moments are derived below. Define the actual finite number β=∫|x|³dν. Let h:ℕ→ℝ and n:ℕ→ℕ obey

\[
h_j\to+\infty,\qquad n_j/h_j^2\to+\infty,\qquad n_j/h_j^3\to0.
\]

There is no all-index positive-height assumption. Finite early zero/negative heights and zero path lengths remain permitted. All divisions in the proposed Lean statements are total real division; positivity needed for estimates or division of inequalities is proved only on a tail.

For a path a∈ℝ^{Fin n_j}, let S_k=∑_{i<k}a_i, Q(a)=∑_i a_i², and

\[
 A_j=\{a:|S_k|\le h_j\text{ for every }0\le k\le n_j\},\quad
 Y_j(a)=(Q(a)-n_j)/h_j^2,\quad
 π_j=ν^{\otimes n_j},\quad G_j=π_j(A_j).
\]

These are exactly `Shao.closedStrip`, `Shao.energy`, `Measure.pi` and its `.real` event probability. `closedStrip` includes S₀=0 and the closed boundary. In particular boundary atoms and all-zero paths are not removed. Write

\[
 I_j(s)=\int 1_{A_j}(a)e^{sY_j(a)}\,dπ_j(a).
\]

This is literally the old transparent `energyJointIntegral ν (n j) (h j) s`, whose integrand is `energyPathIntegrand`. For any fixed h≥1, n and real s it is integrable: on A each increment has |a_i|≤2h, so 0≤Q≤4nh² and the integrand has a finite deterministic bound; off A it is zero. The qualified `energyPathIntegrand_integrable` supplies this fact directly with T=|s|. It does not assert global integrability of exp(sQ/h²).

The three proposed public outputs are eventual G_j>0; I_j(s)/G_j→1 for every fixed s∈ℝ; and π_j(A_j∩{|Y_j|>ε})/G_j→0 for every fixed ε>0. There is no claim uniform in s, x, ν or β, and no abstract conditional probability is introduced.

## 2. Lower moments really are integrable

For t≥0, t≤1+t³ and t²≤1+t³: when t≤1 both left sides are at most1; when t≥1 both are at most t³. Hence

\[
 |x|\le1+|x|^3,\qquad |x^2|=|x|^2\le1+|x|^3.
\]

The majorant is integrable because ν is a probability measure and the third absolute moment is integrable. The functions x and x² are Borel measurable, so comparison proves genuine first- and second-moment integrability. Also β≥0 by nonnegativity of its actual integrand. No extra second-moment integrability premise is added to any public head.

## 3. A complete finite-prefix adapter for the actual Kv theorem

This paragraph proves the private `tail_variance_closedStrip_relative_asymptotic`. Let ρ_j be arbitrary actual measures, v_j real numbers, and M a fixed real number. Suppose on a cofinal tail all of the following hold: ρ_j is a probability measure, its absolute third moment is integrable and at most M, its mean is zero, its second moment is v_j, and 1/2≤v_j≤2. Retain the fixed original ν above as a legal fallback law.

Choose one integer N so that all these row statements and h_j≥1 hold for every j≥N. This is possible by finite intersection of the eventual assertions and h_j→∞. Define **proof-local** sequences

\[
 \widehatρ_j=\begin{cases}ρ_j&j\ge N,\\ν&j<N,\end{cases}\quad
 \widehat v_j=\begin{cases}v_j&j\ge N,\\1&j<N,\end{cases}\quad
 \widehat h_j=\begin{cases}h_j&j\ge N,\\1&j<N.\end{cases}
\]

Every patched row is now an actual probability law with integrable third absolute moment, mean zero, second moment exactly \widehat v_j and variance window [1/2,2]. Its third moment is at most B=max(β,M): in an early row it equals β; in a late row it is at most M. Every \widehat h_j is strictly positive. Because the three patched sequences equal the original ones for j≥N, the height limit and both scale limits are unchanged. These are equalities on an explicitly chosen tail, not a change to the original event.

Apply the exact future161 theorem
`UnconditionalKernelAsymptotic.varying_row_variance_closedStrip_relative_asymptotic`
to \widehatρ, \widehat v, B, \widehat h and n. Every one of its all-index inputs has just been verified, including actual mapped-law integrability already internal to that theorem. Its conclusion is

\[
 \frac{\widehatρ_j^{\otimes n_j}(A(\widehat h_j))}
 {(4/π)\exp[-λ\widehat v_jn_j/\widehat h_j^2]}\longrightarrow1,
 \qquad λ=π^2/8.
\]

For j≥N, the law, height, variance, finite product measure and closed set in this displayed ratio are exactly the original ones. Substituting those equalities transfers the limit to

\[
 \frac{ρ_j^{\otimes n_j}(A(h_j))}
 {(4/π)\exp[-λv_jn_j/h_j^2]}\longrightarrow1.\tag{13}
\]

This adapter supplies no K/Kv limit as a hypothesis. Its sole non-elementary limit input is an application of the stated producer theorem, which removes the old S/AC/CDF/SP desired-input predicates internally. The qualification of that producer and its underlying chain remains pending; this paragraph does not certify it.

## 4. Original survival asymptotic and eventual positivity

Apply (13) with ρ_j=ν, v_j=1 and M=β. Every row condition holds for every index. With

\[
 a_j=(4/π)e^{-λn_j/h_j^2}>0
\]

we get G_j/a_j→1. Strict positivity of a_j uses π>0 and exp>0 and is valid for every real h_j, including a zero height under total division. On a tail G_j/a_j>1/2, hence G_j>0. This proves the first public result without claiming positivity at every finite index.

## 5. The same actual centering parameter and the tilted survival ratio

Fix an arbitrary real s. Set proof-locally T=|s| and M=β. Both are nonnegative; the common β bound is equality. The lower moments in §2 and the raw mean/second assumptions satisfy every hypothesis of the qualified `energyJointTransport_common_bounds` with constant sequence s_j=s. Obtain its one centering sequence θ. It is selected before the choice of length sequence, and is used unchanged for all the following assertions. We use its eventual `energyE2Conclusion` and its `energyJointSequenceConclusion` for the given n and hshort. No θ is supplied by the public theorem's caller.

Put

\[
 ρ_j=\operatorname{energyLinearTiltLaw}(ν,h_j,s,θ_j),\quad
 v_j=\int x^2\,dρ_j,\quad
 C=\operatorname{energyE2Constant}(β,|s|).
\]

The transparent E2 conclusion, for this exact ρ_j and θ_j, gives on a tail: actual probability, genuine first/second/third integrability, actual mean zero, third moment at most C, and

\[
 |v_j-1|\le C/h_j.\tag{14}
\]

The qualified constant domination theorem gives C≥1. As h_j→∞, restrict to a tail on which h_j≥max(1,2C). Thus C/h_j≤1/2, so 1/2≤v_j≤3/2≤2. All the eventual row inputs of §3 hold, with common third bound C; the early rows are patched only inside that adapter. In particular no early θ-row is assumed to be a probability law.

Let

\[
 H_j=ρ_j^{\otimes n_j}(A_j)
   =\operatorname{energyJointCenteredProbability}(ν,n_j,h_j,s,θ_j),\qquad
 b_j=(4/π)e^{-λv_jn_j/h_j^2}>0.
\]

The equality is the old literal definition of `energyJointCenteredProbability`. Equation (13) yields H_j/b_j→1. Moreover, for h_j>0,

\[
 \left|\frac{-λ(v_j-1)n_j}{h_j^2}\right|
 \le |λ|\frac{C}{h_j}\frac{n_j}{h_j^2}
 =|λ|C\frac{n_j}{h_j^3}\longrightarrow0.\tag{15}
\]

Here n_j≥0, h_j>0 and C≥0 justify multiplication of inequalities; no estimate in n_j/h_j² is discarded. The right side tends to0 by hshort, so the exponent on the left tends to0 by the absolute-value squeeze. Since a_j and b_j have the same positive factor4/π, exact exponential algebra gives

\[
 b_j/a_j=\exp[-λ(v_j-1)n_j/h_j^2]\longrightarrow1.\tag{16}
\]

Combine H_j/b_j→1, (16) and G_j/a_j→1. On the eventual G_j>0 tail, all denominators in

\[
 \frac{H_j}{G_j}=\frac{H_j}{b_j}\frac{b_j}{a_j}\big/\frac{G_j}{a_j}
\]

are nonzero. Limit multiplication and division by a limit1 give H_j/G_j→1. This proves the private `e2_centered_survival_ratio`. The event on each side remains the same absolute closed strip, with no cumulative drift translation and no replacement by an unconditional energy event.

## 6. Actual fixed-s energy integral ratio

The qualified joint sequence conclusion supplies an eventual finite conclusion and

\[
 δ_j=\exp(\operatorname{energyRelativePathError}(β,|s|,n_j,h_j))-1
 \longrightarrow0,
\]

as part of its transparent `energyJointErrorLimits`. Its actual finite absolute bound is

\[
 0\le δ_j,\qquad |I_j(s)-H_j|\le δ_j H_j.\tag{17}
\]

It also supplies actual strip-integrability (already independently available for h_j≥1). This is an existing proved relative bound against the actual centered law, not an absolute o(1) estimate against a rare probability.

On the common tail G_j>0, dividing (17) by G_j gives

\[
 \left|\frac{I_j(s)}{G_j}-\frac{H_j}{G_j}\right|
 \le δ_j\frac{H_j}{G_j}.
\]

H_j is a nonnegative real measure, so the right side is nonnegative on that tail; δ_j→0 and H_j/G_j→1 imply it tends to0. Squeeze yields I_j(s)/G_j−H_j/G_j→0, and addition yields I_j(s)/G_j→1. This proves the second public result for the arbitrary fixed s, including s=0 and both signs. Only bounded-strip exponentials were integrated. There is no fourth moment, global exponential moment, bounded original support, density, nonlattice or symmetry premise.

## 7. Complete finite exp-pair deviation inequality

For y∈ℝ define only in this proof f(y)=e^y+e^{-y}−2. This is even. For u=e^{|y|}>0,

\[
 f(y)=u+u^{-1}-2=(u-1)^2/u\ge0.\tag{18}
\]

For fixed ε>0 put D=f(ε). Since e^ε>1, (18) gives D>0. If |y|>ε, write u=e^{|y|} and v=e^ε. Then u>v>1 and

\[
 (u+u^{-1}-2)-(v+v^{-1}-2)
 =(u-v)\left(1-\frac1{uv}\right)\ge0.
\]

If |y|≤ε, (18) gives 0≤f(y). The two cases prove, for every y,

\[
 D\,1_{\{ε<|y|\}}\le f(y).\tag{19}
\]

This proves the private `exp_pair_deviation_bound`, including D>0. No probabilistic or integrability assertion occurs in it.

Now fix any finite n, any h≥1 and the actual probability law ν; no moment assumption is needed in the following finite argument. Let π=ν^{⊗n}, A=closedStrip(h), Y=(Q−n)/h² and B=A∩{ε<|Y|}. The set A is measurable by the qualified closed-survival interface. Q is a finite sum of continuous coordinate squares, so Y and B are measurable. Under the finite probability measure π, indicators1_A and1_B are integrable. The old integrability theorem with T=1 gives both F₊=energyPathIntegrand(h,1) and F₋=energyPathIntegrand(h,−1) integrable. Thus F₊+F₋−2·1_A is genuinely integrable; no difference of nonintegrable functions is used.

For every path a, if a∉A then both sides below are zero. If a∈A then the old literal integrand equals e^{±Y}, and (19) applies. Therefore

\[
 D1_B(a)\le F_+(a)+F_-(a)-2\,1_A(a).
\]

Integral monotonicity and linearity for these integrable functions give the exact finite inequality

\[
 Dπ(B)\le I(1)+I(-1)-2π(A).\tag{20}
\]

This proves `energy_deviation_finite_bound`. It remains valid when π(A)=0 and when n=0; its proof never divides by a survival probability. The strict deviation condition and the closed strip event are literal throughout.

## 8. Conditional concentration

Return to the original sequences and fix ε>0. On the common tail where h_j≥1 and G_j>0, use (20) and D>0 to obtain

\[
 0\le\frac{π_j(A_j\cap\{ε<|Y_j|\})}{G_j}
 \le\frac{I_j(1)/G_j+I_j(-1)/G_j-2}{D}.\tag{21}
\]

The left inequality uses only nonnegativity of the actual real measure and G_j>0. The right numerator tends to1+1−2=0 by §6 at the two fixed values s=1 and s=−1. Since D is a strictly positive fixed real, the right side tends to0; (20) also ensures it is nonnegative on the relevant tail. Squeeze in (21) proves the third public result. This is exactly source (12), using the exp-pair form of twice the cosh gap. Only eventual positivity was used to divide.

## 9. Exhaustiveness, qualification and remaining scope

The declaration proposal lists exactly five private theorem heads and three public heads. The proof order matches the file: lower moments; tail-Kv adapter; public positivity; actual E2 survival ratio; public fixed-s Laplace; finite exp-pair inequality; finite integrated inequality; public concentration. No new global definition, opaque value, instance, notation or structure is proposed. Local β,T,C, fallback patches, a_j,b_j,H_j,δ_j,D are explicitly specified above; they are ordinary proof-local lets and do not change the public problem.

Qualified existing work reused: exact EnergyJointTransport, EnergyE2Bounds, EnergyPathLaw, and their actual closed-strip/finite-path definitions. The proof uses only the direct public heads and the transparent values listed in api-evidence.md; no new complete producer review or old proof replay is requested.

Unpaid qualification: actual future161 K/Kv and its 149→150→154→156→161 dependencies, this complete proposed new module, independent complete final source-to-statement/proof review and exact-source server kernel/transitive-axiom receipt. During this author turn the parent reported rootBE QUALIFIED at exact source `8bf02df1210d69a2934746987d0022a85166d17c9850fa4fd27656eb88bb2af9`, object `d67df1b97eddcde16ee7d9fedc6e6e7e4af11e22e04732a69dbd0b5883b76b57`, with fresh full review; that parent-reported upstream status is recorded without rereading or duplicating BE. The parent freezes declarations before source implementation. No local/server Lean, build, audit, cache, Git or shared implementation operation was performed for this proposal.

Source120 expressly leaves random-denominator far layers unpaid. Thus neither (11) nor (12), nor this proof, supplies the full relative asymptotic of P(M_n≤xV_n), a uniform x-window, full E3 operator conjugacy, or general OQ4 root closure. Attribution remains to the original E1–E4 source and the named producer chain; no novelty claim is made.
