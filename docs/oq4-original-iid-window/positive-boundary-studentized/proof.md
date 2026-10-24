# E6 positive boundary: complete mathematical proof proposal

Status: PROVED_AS_MATHEMATICAL_PROPOSAL; parent freeze, independent full review, Lean implementation and exact-source server kernel/all-owned transitive-axiom checks are UNPAID. Author: fresh context180, prescribed gpt-6.1-sol/xhigh. This is an auxiliary source-bound proof, not a novelty claim or closure of original OQ4. All root groups remain OPEN.

Only this directory is owned. No implementation, Lean/parser/server/Git/cache/install/download action was taken. Parent notes `positive-boundary-studentized-next-math-notes-v1.md` were read in full. The proposal deliberately has two coherent future modules: A `BrownianPositiveCDF`, then B `PositiveBoundaryStudentized`. B depends on A; both exact complete inventories must be frozen before either is implemented. The proof bodies below are mathematical, not formal Lean evidence.

## 1. Exact target and source scope

The source is `C:/game/shao/current/oq4/denom01.md` E6, lines114–131, read together with the complete original assumptions in `frozen01.md`. Let ν be a probability measure on ℝ, ∫z dν=0, ∫z² dν=1, and ∫|z|³ dν<∞. Let π_n=Measure.pi(fun _ : Fin n => ν), Path n=Fin n→ℝ, S_k(a)=Σ_{i<n,i<k}a_i, and Q(a)=Σ_{i<n}a_i². ClosedStrip(w) monitors every integer 0≤k≤n with |S_k|≤w. In particular S_0=0 is included, n=0 is meaningful, and weak equalities are retained.

For a given actual Brownian B on a probability space (Ω,P), write U for the already constructed measurable `BrownianSup.U B P hB`, and F(x)=P.real{U≤x}. The existing theorem U=raw time-one supremum holds almost surely, and F equals the raw full-strip probability. No new process is presumed to preserve P; scaled processes below are proved Brownian on this same (Ω,P).

For arbitrary sequences n_j∈ℕ with n_j→∞ and x_j∈ℝ with x_j→x_*>0, prove

    π_{n_j}.real(randomDenominatorEvent n_j (x_j sqrt(n_j))) → F(x_*),

and consequently the ratio with F(x_j) tends to one. No all-index positivity of n_j or x_j is required. The actual event is exactly ClosedStrip(x_j sqrt Q), including n=0 and Q=0. The energy LLN is proved separately under only integrability of z² and its expectation one. This is genuinely stronger than the energy consequence needed here; no fourth moment, exponential moment, density, nonlattice condition, atomlessness of ν, symmetry, desired LLN, desired functional limit or desired CDF assertion is a premise.

This unit does not prove the x_*=0 branch, the entire moving window, arbitrary σ>0 scaling, or transfer to an arbitrary original iid space. Those remain distinct source-bound consumers. It does not change p54 repairs or external BE–SP attribution.

## 2. Proposal A: every positive Brownian atom is null

For c>0 in ℝ≥0 define C_c(t,ω)=(sqrt(c))^{-1}B(ct,ω). The pinned `IsBrownianReal.smul` proves that exact C_c is Brownian; its scalar is a real positive inverse square root, and its time multiplication is in ℝ≥0.

Fix x>0, set c=x² as a nonnegative real and T=c^{-1}. Then sqrt(c)=x. Multiplication t↦ct sends [0,T] bijectively onto [0,1]: t≥0 and t≤c^{-1} imply 0≤ct≤1; conversely s∈[0,1] has preimage c^{-1}s∈[0,c^{-1}], and c(c^{-1}s)=s. This is a deterministic assertion and includes both endpoints.

On any continuous sample path of B, both continuous absolute-value functions attain maxima on their nonempty compact intervals. Let A={|B(s,ω)|:0≤s≤1}. The set of values {|C_c(t,ω)|:0≤t≤T} is precisely {a/x:a∈A}, by the preceding bijection and |x^{-1}b|=|b|/x. The positive number x preserves order. An attained maximum m of A therefore gives an attained maximum m/x of the latter value set. This proves, with no appeal to a radius-null claim,

    BrownianSurvivalBoundary.pathSup C_c T 0 ω
      = BrownianSup.pathSup B ω / x.

Intersect the almost-sure continuity event with the existing event U=BrownianSup.pathSup B. On this single event,

    U(ω)=x  iff  BrownianSurvivalBoundary.pathSup C_c T 0 ω=1.

Here x≠0, so division is reversible. Apply the already qualified unit-level theorem `measure_pathSup_eq_one_eq_zero` to the actual Brownian C_c, T>0 and starting point u=0∈[-1,1]. The right event has P-measure zero; almost-sure equality of the two events gives P{U=x}=0. This works at every x>0, including x=1. Raw suprema need not be globally measurable: the conclusion uses equality modulo a null set and the already measurable U; the qualified raw unit-level theorem is exactly the consumed result.

## 3. Actual CDF continuity, monotonicity and positivity

We prove a general elementary fact. If Z:Ω→ℝ is measurable, P is a probability measure and P{Z=x}=0, then G(y)=P.real{Z≤y} is continuous at x. For y near x put I_y(ω)=1 when Z(ω)≤y and 0 otherwise. Every I_y is measurable, and |I_y|≤1. The constant 1 is integrable because P(Ω)=1.

If Z(ω)<x, the neighborhood y>Z(ω) of x forces I_y(ω)=1=I_x(ω). If x<Z(ω), the neighborhood y<Z(ω) forces I_y(ω)=0=I_x(ω). Thus I_y→I_x along y→x for almost every ω. The pinned filter dominated-convergence theorem for a uniform constant bound, applied to the countably generated real filter nhds x, yields ∫I_y dP→∫I_x dP. The integral of each measurable-set indicator of 1 is P.real of that set; all measures are finite. Therefore G is continuous at x. Applying this fact to measurable U and Section2 proves ContinuousAt F x for every x>0, and in particular F(r_j)→F(x) whenever r_j→x>0.

If x≤y then {U≤x}⊆{U≤y}; finite real measure monotonicity gives F(x)≤F(y). To show positivity at an arbitrary x>0, consume qualified `actual_brownian_eventually_positive`: choose its δ>0. Set y=min(x,δ)/2. Then y>0, y<x or at least y≤x (in fact y<x), and y<δ. The qualified theorem gives F(y)>0. Monotonicity gives 0<F(y)≤F(x). No new spectral estimate is needed.

## 4. Actual horizon scaling identity

For T>0 let C=C_T. For every sample ω, even outside continuity, multiplication s↦Ts bijects [0,1] and [0,T]. At s∈[0,1],

    |C(s,ω)|≤1/sqrt(T)  iff  |B(Ts,ω)|≤1,

because sqrt(T)>0. Consequently the raw sets are exactly equal:

    closedSurvival B T 0 = fullStrip C (1/sqrt(T)).

The qualified BrownianSup theorem identifies the latter probability with F_C(1/sqrt(T)), and `probability_eq_probability` for the two genuine Brownian processes C and B gives F_C(r)=F_B(r) at that same radius r. Therefore

    P.real(closedSurvival B T 0) = F_B(1/sqrt(T)).

This uses a time T process scaling. It is distinct from Section2, where c=x² and the raw supremum of C_c was inspected at time c^{-1}. For T=x_*^{-2}, sqrt(T)=1/x_* and the radius here is exactly x_*.

## 5. Proposal B: the actual finite-product energy LLN

This section assumes only that ν is a probability measure, z↦z² is integrable, and ∫z² dν=1. Define Ω∞=ℕ→ℝ, μ∞=Measure.infinitePi(fun _=>ν), Y_i(ω)=ω(i)², and A_n(ω)=(Σ_{i<n}Y_i(ω))/(n:ℝ), with real division totalized at n=0. InfinitePi of probability measures is a probability measure.

Every evaluation e_i:ω↦ω(i) is measurable and measure preserving from μ∞ to ν, by pinned `measurePreserving_eval_infinitePi`. Thus Y_0 is integrable and ∫Y_0 dμ∞=∫z² dν=1. Evaluation laws all equal ν, and their square compositions have equal mapped laws. The pinned `iIndepFun_infinitePi` with the measurable component function z↦z² proves joint independence of the whole family Y. In particular Y has the pairwise independence required by `strong_law_ae_real`. Its other hypotheses are exactly the integrability just established and `IdentDistrib (Y i) (Y 0) μ∞ μ∞`, obtained from the equal actual pushforward measures. The strong law therefore gives A_n→1 μ∞-almost everywhere. No integrability of Y_i² is invoked.

For every n, A_n is a finite sum of measurable squared evaluations divided by a constant, so it is measurable and hence strongly measurable. Pinned `tendstoInMeasure_of_tendsto_ae` now gives A_n→1 in μ∞-measure. Its pinned real-norm formulation gives, for every δ>0,

    μ∞.real{ω:δ≤|A_n(ω)-1|}→0.

We must pay the actual finite-law link, not merely name an iid realization. Define p_n(ω):Fin n→ℝ by p_n(ω)(i)=ω(i.val). It is measurable. Base coordinate independence from `iIndepFun_infinitePi` with component id, precomposed by the injective Fin.val, gives independence of this finite family. Each coordinate is IdentDistrib with id:ℝ→ℝ under ν, using the pinned evaluation map identity. The qualified `iid_samplePath_map_eq_pi` proves

    μ∞.map p_n = π_n

for every n, including n=0. In that case both target spaces are the singleton empty function space, and the theorem retains that case automatically.

For every ω and every n the literal finite sum reindexing Fin n↔{i∈ℕ:i<n} gives

    Q(p_n ω)=Σ_{i∈Fin n}ω(i.val)²=Σ_{i∈range n}ω(i)².

Define Bad(n,δ)={a:δ(n:ℝ)<|Q(a)-(n:ℝ)|}. Energy is continuous and Bad is measurable, so the actual map equality transports its probability exactly to μ∞.real of the corresponding range-n sum deviation. For n≥1, multiplying the identity A_n−1=(ΣY_i−n)/n by n>0 proves

    δn<|ΣY_i−n|  iff  δ<|A_n−1|.

This strict event is contained in the weak event used by convergence in measure. Its probability lies between 0 and a sequence tending to 0, so π_n.real Bad(n,δ)→0. At n=0, Q=0 and Bad is empty; this initial term is explicitly preserved, and the normalization equivalence was used only eventually n≥1. Composition with any n_j→∞ gives π_{n_j}.real Bad(n_j,δ)→0 without a monotonicity assumption on n_j.

For later use h3 implies square integrability under a probability measure: z²≤1+|z|³ for every real z. If |z|≤1 the square is ≤1; otherwise |z|²≤|z|³. The right side is integrable, and the square is measurable, so integrable domination proves the claim. This adds no fourth moment and requires no new premise in the studentized result.

## 6. Deterministic moving positive walls from the actual paid row theorem

Restore the fixed original ν hypotheses, and fix n_j→∞, r_j→r_*>0. Let N_j=max(n_j,1). Then N_j≥1 and N_j=n_j eventually; N_j→∞. Put

    T=NNReal.ofReal((r_*²)^{-1}),
    h_j=r_* sqrt(N_j),
    b_j=NNReal.ofReal(r_j/r_*),  u_j=0,
    ν_j=ν,   M=∫|z|³ dν.

Every h_j is positive. Since r_*²>0, T>0 and its real coercion equals (r_*²)^{-1}. The exact square-root identity sqrt(N_j)²=N_j gives

    (T:ℝ) h_j²=N_j,  floorHorizon T h_j=N_j.

Thus the row theorem's horizon inequality is satisfied with equality; no terminal floor is lost. Since N_j→∞, sqrt(N_j)→∞ and multiplying by r_*>0 gives h_j→∞. For example, any desired height R is exceeded once N_j>(max(R,0)/r_*+1)²; this proves the divergent limit without any bounded-subsequence claim. The real quotient r_j/r_* tends to1; the continuous ofReal map to ℝ≥0 therefore gives b_j→1. Also r_j>0 eventually, so (b_j:ℝ)=r_j/r_* eventually. The constant start u_j=0 tends to0∈[-1,1]. Constant ν_j is a probability law, has the required h3, mean0 and second moment1, with the same finite third-moment bound M at every index.

All hypotheses of the actual public `discrete_survival_tendsto_brownian` are now paid. It gives the probability limit of

    D_j={a:∀k≤floorHorizon T h_j, |0+S_k(a)/h_j|≤(b_j:ℝ)}

under the actual π_{N_j}, with limit P.real(closedSurvival B T 0). Since floorHorizon=N_j and h_j>0, multiplication by h_j proves the exact event identity

    D_j=ClosedStrip((b_j:ℝ)h_j).

This includes k=0 and k=N_j. Eventually, N_j=n_j and r_j>0, so (b_j:ℝ)h_j=(r_j/r_*)r_*sqrt(n_j)=r_j sqrt(n_j). Substitute those eventual equalities, including equality of the dependent finite product measures after N_j=n_j. Early original paths of length0 and negative radii have not been removed from the statement; they contribute only an unchanged finite prefix. Section4 gives the limit F_B(1/sqrt(T))=F_B(r_*). We have proved

    π_{n_j}.real ClosedStrip(r_j sqrt(n_j))→F_B(r_*).

This is an actual derived positive-radius functional limit. The paid row theorem was not misquoted as accepting an arbitrary limiting boundary.

## 7. Exact random event and finite probability sandwich

For every n and x, the qualified definition is

    E(n,x)=randomDenominatorEvent n (x sqrt(n))
          ={a:ClosedStrip((x sqrt(n)/sqrt(n))sqrt(Q(a)))}.

If n>0, sqrt(n)>0 and cancellation yields the exact event {a:ClosedStrip(x sqrt Q(a))}. If n=0, Fin0 is empty, Q=0, all prefix sums are0, and both wall formulas are0; both events are the full empty-path space. Thus the same event identity holds for every n. In particular Q=0 paths are included: all coordinates, hence all prefix sums, vanish, and the weak wall is0. We do not divide by sqrt Q or remove its atom.

All events used below are measurable. A deterministic closed strip is the countable intersection over k of either the whole space (if k>n) or the measurable set |S_k|≤w. For the actual random event replace w by its measurable energy wall (h/sqrt(n))sqrt Q. Measurability follows from the qualified measurable prefix sums and energy, continuity of sqrt and multiplication. Bad(n,δ) was already shown measurable.

Fix 0<δ<1 and x≥0. Off Bad(n,δ), |Q−n|≤δn, hence

    (1−δ)n≤Q≤(1+δ)n.

All quantities under square roots are nonnegative. Monotonicity of sqrt and sqrt(ab)=sqrt(a)sqrt(b) for nonnegative a,b give

    x sqrt(n)sqrt(1−δ)≤x sqrt Q≤x sqrt(n)sqrt(1+δ).

The x≥0 premise is used exactly when multiplying these inequalities. Therefore, with A_±=ClosedStrip(x sqrt(n)sqrt(1±δ)),

    A_- \ Bad(n,δ) ⊆ E(n,x),
    E(n,x) ⊆ A_+ ∪ Bad(n,δ).

The same proof covers n=0, where Q=0 and both deterministic walls are0. All threshold equalities remain on the good event; no atom is excluded. Taking finite real measures, subtracting the intersection with Bad for the lower bound and using subadditivity for the upper bound gives

    π_n.real A_- − π_n.real Bad(n,δ)
      ≤ π_n.real E(n,x)
      ≤ π_n.real A_+ + π_n.real Bad(n,δ).

The lower bound follows also from A_-⊆E∪Bad, which avoids a subtraction identity. These inequalities use only deterministic event relations and finiteness of π_n.

## 8. Actual studentized positive-boundary convergence and ratio

Take x_j→x_*>0, n_j→∞. Eventually x_j≥0, so Section7 applies at all sufficiently large j. Fix 0<δ<1. The two deterministic radii r_j^±=x_j sqrt(1±δ) tend to r_*^±=x_*sqrt(1±δ)>0. Section6 gives

    π_{n_j}.real A_j^±→F(x_*sqrt(1±δ)).

Section5 gives the bad-event probability→0. For completeness we close the two-limit squeeze directly. Let ε>0. As δ↓0, both x_*sqrt(1−δ) and x_*sqrt(1+δ) tend to x_*. Continuity from Section3 supplies a δ∈(0,1) such that each of the two resulting F-values differs from F(x_*) by <ε/4. For that one fixed δ, take j sufficiently large that x_j≥0, both deterministic probabilities are within ε/4 of their limits, and the bad probability is <ε/4. The lower inequality is then >F(x_*)−3ε/4 and the upper inequality <F(x_*)+3ε/4. In particular |π_{n_j}.real E(n_j,x_j)−F(x_*)|<ε. This proves the required actual probability convergence, with no assumed Slutsky theorem and no desired-limit premise.

Finally, F(x_j)→F(x_*) by actual CDF continuity, and F(x_*)>0 by Section3. Continuity of division at a nonzero denominator gives

    π_{n_j}.real E(n_j,x_j)/F(x_j) → F(x_*)/F(x_*)=1.

The endpoint x_*=1 is included; the proof in fact holds for every x_*>0. A future window argument may consume this exact ratio conclusion on a compactness-selected positive-limit subsequence. Nothing here assumes or proves the entire window in advance.

## 9. Acceptance boundary and exhaustive declarations

The companion `declarations.lean.txt` is the exhaustive proposed inventory: two future module headers, every private/public theorem head, all five full transparent definition values, all imports and options. No hidden helper theorem, structure, instance, macro or additional definition is proposed. Local `have`/`let` facts in eventual proof bodies are not additional module declarations. If implementation needs an additional declaration or mathematical change, parent must freeze its complete head/value first. Ordinary proof-body tactic/import elaboration corrections remain subject to the parent's exact source policy.

Qualified old source proofs and server receipts are reused; this author does not re-review them or repeat their checks. Current primary API evidence and local consumed-source hashes are in `api-evidence.md`. The attached checkpoint explicitly distinguishes this mathematical proposal from unpaid formal/independent certification. No source implementation is included here.
