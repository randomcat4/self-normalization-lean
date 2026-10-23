# OQ3 U22am / U22an / U22ao independent complete final review

STATUS: CORRECT

All five public theorems and all ten generated owned theorems are individually CORRECT. The three modules preserve the frozen exact auxiliary statements, genuine iid laws, physical tail convention, and source likelihood normalization. No critical mathematical or evidence gap was found within that scope. This does not close OQ3 B/D or the original probability asymptotic.

Reviewer role: sole fresh independent complete final reviewer, separate from the author; assigned configuration gpt-6.1-sol / xhigh, with no model change or child delegation. Applied math-theorem and the current project AGENTS.md, SERVER.md, TEAM ownership, REGISTRY and streamlined-acceptance instructions. Only this report is written. All server observations were read-only on CPU14-17 through tools/server.py. No Lean, kernel, axiom, build or old-proof check was rerun. Input, cached-input, output and reasoning-subset token counts are not exposed to this review context; no numerical usage or subscription-percentage allocation is inferred.

## Frozen input identity and complete coverage

All paths are relative to C:/game/shao lean unless explicitly absolute. Each entire final source, entire scope, entire actual-types file, entire Audit.lean, all three environment manifests and all three receipts were read. Complete source coverage includes imports, setup, every declaration, every final proof step and closing lines: AM160/160, AN94/94, AO117/117; total371/371 lines and17743 bytes. Complete actual-owned-type coverage is15/15:5 public plus10 generated, all theorems,0 private theorems,0 global definitions or other owned constants. Actual type files total106 lines/6408 bytes, without abbreviated or omitted type text. All local let values in statements and implementations were read and checked below.

| Unit / module | Frozen scope SHA256 | Final source SHA256 | Lines / bytes | Actual owned |
| --- | --- | --- | --- | --- |
| AM / Shao.OQ3.QuadraticSampleChangeOfMeasure | 0c3e3d8ee00e86dfb8cfdce399b2a86f16e23de02940a0925908865b544232c3 | b27ee727239ca0c31db3e3f04275eae1a13813adb1f1749edb564749df7d9bda | 160 /7577 |3:2 public+1 generated |
| AN / Shao.OQ3.SampleParabolaTailDomain | 0b8efea1829ca333f95980520626a9e9995e4135092e921eea45a201b8fdd581 | f5551b1154e81096c6a5b23cc229c1c2f5e06a7d8578057e67ac5ffcad48a01c |94 /4391 |2 public |
| AO / Shao.OQ3.StandardizedCellChangeOfMeasure | 3b0a048ac67ec9f7fcbd532e4dbe423f8e9801b5f768ee4b3e1d7babeb80a3ac | cecdbf313e675681bf62060134fe562b29e2f297cd35680ecd6c06f3496d01e1 |117 /5775 |10:1 public+9 generated |

Scopes are drafts/oq3/hundred-twentieth-unit-scope.md, hundred-twenty-first-unit-scope.md and hundred-twenty-second-unit-scope.md. Complete declarations match final sources after whitespace normalization. All seven archived attempts retain those same frozen declarations: AM01/02, AN01/02, AO01/02/03. Proof repairs did not silently change the freeze. Final local sources have LF only/no CR; their hashes equal both successful server snapshots and current worktree sources. No final source was normalized or modified by this reviewer.

The server worktree remains /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3, branch feat/oq3-physical-laplace-window, parent e7dfc9aa79f5b01b69792fa41fa7c801bed42cd9. Source hashes, rather than that parent commit alone, bind the new untracked modules.

## Original source, definitions and pinned interfaces

Read the original report's complete precise statement/zero-energy convention, section3 equations6-8 and surrounding small-cell argument, section4 near/far decomposition, boundary/scope audit, and repair01 section2's complete cell/test-function definitions and context. Whole-file identities were verified:

- C:/game/shao/current/oq3/proofs/r2/report.md: SHA256572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55,20102 bytes.
- C:/game/shao/current/oq3/proofs/r2/repair01.md: SHA2569d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd,5846 bytes.

Source W=(X,X^2), K(theta)=log E exp(theta dot W), and dP_theta=exp(theta dot W-K(theta))dP are genuinely represented. Shao.Path n is exactly Fin n->Real; Shao.energy z is exactly sum_i(z_i)^2; its consumed nonnegativity proof is finite-sum nonnegativity of real squares. No centered energy, variance surrogate or arbitrary map replaces these values. Read the actual values in library/Shao/Basic/FinitePath.lean; SHA256898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb matches server.

Shao.Probability.bivariateMGFDomain mu W is exactly {theta | Integrable (fun omega=>exp(theta.1*(W omega).1+theta.2*(W omega).2)) mu}. For W(x)=(x,x^2), membership is exactly the hf used by AM/AO. This is the true domain, rather than an arbitrary parameter set or a default nonintegrable integral. bivariateLogMGF is the log of that actual exponential integral; the true Legendre rate is a supremum over that domain. Read the actual values in BivariateLegendre.lean; SHA256d8bd5dc7099ffdbf52282ebb41ad03145a50b42547dec55bb42caacb31ed5f58 matches local/server. No new theorem asserts that arbitrary theta attains this rate at arbitrary y.

Primary pinned Mathlib definitions and complete consumed API statements were inspected directly. Measure.tilted is withDensity of ENNReal.ofReal(exp(f)/integral exp(f)); isProbabilityMeasure_tilted requires actual Integrable and nonzero base measure. Measure.pi is the finite product measure obtained from its product outer measure; its sigma-finite rectangle formula, pi_eq uniqueness and restrict_pi_pi have the exact hypotheses used by AM. Integrable.fintype_prod and integral_fintype_prod_eq_prod/eq_pow concern the actual coordinate functions and include empty finite products. Measure.real s=(mu s).toReal; every probability conclusion here uses finite mass, so infinite-mass-to-zero totalization is not a proof device.

The pinned integrable_withDensity_iff takes measurable density and finite-a.e. ENNReal density values, and equates Integrable g under withDensity with Integrable of g*density.toReal under the base measure. integrable_map_measure requires AE strong measurability of the integrand and AE measurability of the map. setIntegral_map requires those facts and the actual measurable target set. measureReal_inter_add_sdiff requires measurable U and finite Tail mass. All hypotheses are derived or follow from the actual finite probability products. Measure.map has a separate definition branch for non-AE-measurable maps; proved continuity of M/T ensures the genuine pushforward branch is used here.

ContinuousLinearEquiv extends an actual linear equivalence with forward/inverse continuity. Its symm is the inverse linear equivalence with those fields interchanged; apply_symm_apply and symm_apply_apply are true right/left inverse identities. Thus AO uses the actual inverse map. The pinned Real.sqrt positivity, sqrt_div's nonnegative-numerator premise, mul_self_sqrt and sq_sqrt premises were read and are met by n>0 and the relevant actual energy nonnegativity/positivity.

These directly inspected files equal pinned mathlib807d3836b165983210ee2ecf3cd28f239436949c bytes: Measure/Tilted.lean SHA355cce542b03dd9130d9511f80ae803cc11a12ba9e6a947e68402b124be2165f; Integral/Pi.lean43c50a9d9a683b2050e145154410a7260c3dd84f3ec3010630cc6b90572afcd9; Integral/Bochner/Set.lean e4d90b9fde463a9123e1ac3321ce25c0714e19ce92e172f297e062d9de16be75; Function/L1Space/Integrable.lean d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759; Measure/Real.lean1b9d1490fa5acbffc570eac67f465d3d6ab0520aa3e54464f7520d60d6619b8d; Measure/MeasureSpaceDef.lean3853c6899a36759a64c9658969fb2f1ea97f0d026598c0f0468c30fe2a5d7356; Measure/Map.lean7bae8f174146d4ef4055f79757c2a0a3af6a9090dda3d28ea17fbd54540e9593; Constructions/Pi.lean bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef; Analysis/Real/Sqrt.lean1f19e1d6722b2f51c2cd676d0b28ede856c7915ac815b597cef4b3919040c204; Topology/Algebra/Module/Equiv/Basic.lean7419dab9e876a969f3c8187efe5126106327510a00f69a183afac3d981bf41bc. An API search encountered absent server rg; Python completed that read without Lean/check replay or mutation.

AN imports qualified BoundaryLaplacePhysicalDomain (AI), source SHAa23647aacbbe2f103c5d91825e552224410e66b321a90a404bbdc7e01e0bf3c2. Its prior complete independent review drafts/oq3/u22aiaj-proof-review.md has SHA9d34f2dbe6e00345860a7f99ef3c596df2dd2e89e07bed1322e263738385e741. Existing qualification is reused. AN calls no AI physical-positivity theorem; the import supplies its Sqrt environment. No global q>0 or previously physical analytic radius is assumed.

## AM: full statements, local values and final proofs

Shao.OQ3.iid_quadratic_sample_tilt: CORRECT (AM11-74).

The full type quantifies any probability mu on Real, theta in the true exponential-integrability domain, and every natural n including0. Its statement lets are f(x)=theta.1*x+theta.2*x^2; S(z)=sum_i f(z_i); Z=integral exp(f)dmu; P=pi_i mu. It concludes actual Integrable exp(S) under P, normalizer Z^n, and P.tilted S=pi_i(mu.tilted f). Implementation f/S/Z are those exact values. Its two anonymous local probability instances for mu.tilted f and P.tilted S are derived from hf/hF, not added premises or global definitions.

AM25-29 takes hf directly from domain membership, obtains Z>0 using nonzero probability mu, and constructs the one-coordinate tilted probability. AM30-37 proves exp(sum_i f(z_i))=product_i exp(f(z_i)) pointwise and derives Integrable via finite-product Fubini from the actual coordinate hypotheses. AM38-45 obtains the exact normalizer Z^n, its positivity, and the tilted sample probability. No product-integrability premise is assumed.

AM47-51 factors exp(S)/Z^n as product_i(exp(f(z_i))/Z), retaining the finite constant product and exponential sum. AM52-74 uses pi_eq in the correct orientation and checks every measurable rectangle. The sample tilt's rectangle mass is the lintegral of that density. restrict_pi_pi supplies the product of coordinate restrictions. Every exp(f)/Z is integrable there by global hf, and each factor/product is nonnegative since Z>0. Thus lintegral/ofReal conversion, actual finite-product Fubini and ofReal distribution over the nonnegative integral product are legitimate. tilted_apply_eq_ofReal_integral' identifies every coordinate mass. Equality on all measurable rectangles proves measure equality, with sigma-finiteness from the finite/probability measures.

At n0, empty sums=0, empty products=Z^0=1, and the product law on the singleton empty path has mass1. The consumed finite-product lemmas explicitly cover this case. No positive-n division or source tail interpretation is used.

Shao.OQ3.iid_quadratic_cell_change_of_measure: CORRECT (AM76-157).

The full type retains arbitrary mu/theta/n, adds arbitrary y:Real^2 and measurable A, and assumes no bounded-X, moment, y-in-A, tilt-mean, density or approximation condition. Statement lets are the same f; K=log Z; P=pi_i mu; Q=pi_i(mu.tilted f); M(z)=(sum_i z_i/n,energy(z)/n); event E=M preimage A; G(z)=exp(-(theta.1*(sum_i z_i-n*y.1)+theta.2*(energy(z)-n*y.2))). Implementation repeats them and adds S=sum_i f(z_i), Z=integral exp(f), c=exp(n*(theta dot y))/Z^n. Its anonymous tilted-probability instance follows from hf. Every local value was read in full, including both centered coordinates and signs.

AM106-114 derives hf, Z>0, Z^n>0, continuity of actual M (valid also at n0 since division by a fixed real is total), measurable E, and the first theorem's normalizer/product-tilt identities for exactly the same f/S/P/Q. AM116-127 proves S(z)=theta.1*sum z+theta.2*energy(z) and the full pointwise cancellation (exp(S(z))/Z^n)*G(z)=c. The exponent sum is exactly n*(theta dot y), without a missing n or centering term.

AM128-142 proves the density measurable and finite everywhere as ENNReal.ofReal of a real number. Rewriting Q as P.tilted S permits integrable_withDensity_iff. G(z)*density(z).toReal is pointwise constant c; toReal_ofReal is justified by nonnegative exp(S)/Z^n. Since P is a finite probability product, that constant is Integrable. Thus genuine global Integrable G under Q is proved, including unbounded mu, rather than obtaining equality from a default nonintegrable integral. All cell restrictions are Integrable, including thin/unbounded cells.

AM143-147 applies setIntegral_tilted' on actual measurable E and the same cancellation, giving integral_E G dQ=c*P.real E. AM148-155 proves exp(-n*(theta dot y-log Z))*c=1 using exp(n log Z)=Z^n with Z>0. AM156-157 cancels the two positive normalizers and gives exactly the frozen factor exp(-n*(theta dot y-K)), with correct sign and log-partition contribution.

For n0, M=0 by totalized division, S=0, G=c=prefactor=1, so the event-dependent identity remains correct for all A. This is an exact measure extension, not a positive-sample-size tail result. No theta.2 sign or interior-domain hypothesis is needed.

## AN: full statements, local values and final proofs

Shao.OQ3.sample_self_normalized_tail_iff: CORRECT (AN9-51).

The full type quantifies any level>0, any n with1<=n and every actual path z. Its sole statement let M is the same raw first/second sample moment. The statistic is exactly if energy(z)=0 then0 else sum(z)/sqrt(energy(z)). The conclusion is equivalence with 0<M.2 AND level*sqrt(M.2)<=M.1, retaining strict physical q positivity and the inclusive tail boundary.

AN16-19 derives n>0, sqrt(n)>0 and genuine energy>=0. At energy=0, the left event compares strictly positive level*sqrt(n) with0 and is false; M.2=0 makes the right side false. This implements the original zero-energy convention without a spurious positive tail, variance replacement or assumed nonzero energy.

In the nonzero branch, nonnegative energy is positive and so is its square root. AN27-33 derives sqrt(energy/n)*n=sqrt(n)*sqrt(energy), using sqrt_div with the proved nonnegative numerator, n=sqrt(n)^2 and nonzero sqrt(n). AN34-51 proves both directions by multiplying/dividing only by positive n and sqrt(energy), using that exact scale identity. Inequalities remain non-strict. The forward direction supplies energy/n>0. The reverse direction never tries to infer a sign from a squared first coordinate: the original unsquared sum is retained. Negative first sums, zero paths and threshold equality are covered. n0 and nonpositive levels are explicitly outside this interface.

Shao.OQ3.iid_self_normalized_tail_map_and_split: CORRECT (AN53-91).

The full type adds arbitrary probability mu and measurable U, retaining level>0/n>=1. All four statement/implementation lets were checked: P is exactly iid pi_i mu; M is the same raw mean map; Tail={w|0<w.2 AND level*sqrt(w.2)<=w.1}; T is exactly the zero-convention statistic event. The conclusion includes measurable Tail/T, equality of P.real T with the actual map-M law's Tail mass, and its sum over U intersect Tail and Tail setminus U. No probability bound or asymptotic is a premise.

AN73-78 proves continuous M, continuous level*sqrt(w.2), and measurable Tail as the intersection of a strict half-plane and non-strict curve inequality. Real.sqrt is continuous on all reals; Tail separately enforces q>0. AN79-84 proves T=M preimage Tail pointwise using the first theorem and derives measurable T. AN85-87 applies map_apply with actual measurable M/Tail and then toReal, giving the exact probability equality. Finite probability P and measurable M yield the genuine iid sample-moment pushforward, without a nonmeasurable-map branch or infinite-mass totalization.

AN88-91 uses the finite real-measure intersection/set-difference identity with measurable U, reorders the intersection and obtains exactly (U intersect Tail)+(Tail setminus U). These disjoint pieces exhaust Tail even if U is empty/full or its boundary has atoms. Threshold equality belongs to Tail; q=0 is excluded. No exterior probability bound follows from this split and none is claimed.

## AO: full statement, local values and final proof

Shao.OQ3.iid_quadratic_standardized_cell_change_of_measure: CORRECT (AO10-114).

The full type quantifies probability mu, theta in the same true domain, n>=1, arbitrary anchor y, any continuous linear equivalence E:Real^2 equiv_L Real^2 and measurable A. It neither assumes nor concludes covariance whitening or y being a mean. All ten statement lets and implementation copies were read: f=theta.1*x+theta.2*x^2; K=log integral exp(f); actual P/Q product laws; raw M; F(w)=sqrt(n) scalar_mul E(w-y); T(z)=F(M(z)); rho=map T Q; B={v|y+sqrt(n)^(-1) scalar_mul E.symm(v) in A}; g(v)=exp(-sqrt(n)*(theta.1*(E.symm v).1+theta.2*(E.symm v).2)). Additional implementation G is exactly AM's centered path inverse likelihood. These are actual laws, exact cells and source weights, with no Gaussian surrogate or presumed density.

AO46-48 derives n>0/sqrt(n)>0. AO49-59 proves both affine inverses for J(v)=y+sqrt(n)^(-1) scalar_mul E.symm(v): J(F(w))=w and F(J(v))=v. Linearity moves the scalar, genuine E inverse identities cancel E/E.symm, sqrt(n)>0 permits scalar cancellation, and additive cancellation finishes. This is a true two-sided affine bijection for every allowed E.

AO60-65 derives continuous M,F,T,J and hence measurable B=J preimage A. AO66-74 proves B=F image A in both directions using those identities, rather than assuming arbitrary continuous images preserve measurable sets. AO75-78 proves T preimage B=M preimage A. Thus curved/truncated/arbitrarily thin measurable cells, including zero-area sets with possible atomic mass, retain their exact boundaries and mass; they are never replaced by centers or approximate rectangles.

AO79 establishes continuous g. AO80-84 proves for all real x,b that sqrt(n)*(sqrt(n)*(x/n-b))=x-n*b, using sqrt(n)^2=n and n>0. AO85-88 derives E.symm(T(z))=sqrt(n) scalar_mul(M(z)-y). AO89-101 substitutes both coordinates and the scalar identity to prove g(T(z))=G(z) pointwise. The outer -sqrt(n) and inner sqrt(n) give -n and exactly theta.1*(sum z-n*y.1)+theta.2*(energy-n*y.2) inside the negation. There is no determinant/Jacobian factor for this pushforward-law integral.

AO102-106 calls AM with the same mu/theta/n/y/A, retains genuine global Integrable G under the same Q, and uses integrable_map_measure with continuous g/measurable T. Its pointwise pullback G gives genuine global Integrable g under rho, hence on B. Integrability is derived, not assumed. AO107-111 applies setIntegral_map with measurable B and proved measurability data, then the exact preimage and pointwise pullback, giving integral_B g drho=integral_(M preimage A)G dQ. AO112-114 substitutes this into precisely AM's probability identity, retaining K/anchor/prefactor. All four promised conjuncts follow.

The repair's test function is precisely B.indicator g, whose expectation under this actual tilted transformed sample law is the set integral. Recovering the source standardized Z_n and exp(-n I(y)) interpretation still requires a genuine covariance inverse-square-root E, actual tilt mean y, and the corresponding Legendre equality. Arbitrary invertibility proves neither identity covariance nor whitening. n0 is correctly excluded because its sqrt(n) affine scale is not invertible.

## All ten generated actual theorems

Every full generated type was read, including universes, class hypotheses, binders and conclusions. All are theorems: no generated definition value is omitted. Their generation is included in the complete final kernel-checked proofs reviewed above, and their mathematical contents were independently checked below. Prefix AM means Shao.OQ3.iid_quadratic_cell_change_of_measure; prefix AO means Shao.OQ3.iid_quadratic_standardized_cell_change_of_measure.

| Prefix + suffix | Complete actual context and proposition | Individual verdict/reason |
| --- | --- | --- |
| AM._simp_1_1 | Any iota:Type u_1,R:Type u_4,NonUnitalNonAssocSemiring R,s:Finset iota,f:iota->R,a:R; sum_(i in s)a*f(i)=a*sum_(i in s)f(i). | CORRECT: finite-sum left distributivity needs no multiplicative unit/associativity/order. |
| AO._simp_1_3 | Any alpha:Type u_2,Zero alpha,OfNat alpha 2, NeZero 2; (2=0)=False. | CORRECT: explicit NeZero 2, then propext. |
| AO._simp_1_4 | Any alpha:Type u_2,Zero alpha,OfNat alpha 3, NeZero 3; (3=0)=False. | CORRECT: explicit NeZero 3. |
| AO._simp_1_5 | Any alpha:Type u_2,Zero alpha,OfNat alpha 4, NeZero 4; (4=0)=False. | CORRECT: explicit NeZero 4. |
| AO._simp_1_6 | Any M0:Type u_1,Mul M0,Zero M0,NoZeroDivisors M0,a,b:M0; a!=0->b!=0->(a*b=0)=False. | CORRECT: zero-product dichotomy contradicts both nonzero hypotheses. |
| AO._simp_1_7 | Any M0:Type u_1,MonoidWithZero M0,IsReduced M0,a:M0,n:Nat; a!=0->(a^n=0)=False. | CORRECT: vanishing natural power makes a nilpotent, hence zero in an IsReduced monoid; zero exponent is covered. |
| AO._simp_1_8 | Any G0:Type u_3,GroupWithZero G0,a:G0,n:Int; a!=0->(a^n=0)=False. | CORRECT: nonzero integer powers for positive/zero/negative exponents. |
| AO._simp_1_9 | Any R:Type u_1,AddMonoidWithOne R,CharZero R,n:Nat; (natCast(n)+1=0)=False. | CORRECT: this is natCast(n+1), nonzero by cast injectivity/successor nonzeroness. |
| AO._abel_1_1 | All y,w:Real^2; y+(w-y)=w. | CORRECT: product-real additive cancellation. |
| AO._abel_1_2 | All n:Nat,y:Real^2,E:Real^2 equiv_L Real^2,v:Real^2; y+sqrt(n)^(-1) scalar_mul E.symm(v)-y=sqrt(n)^(-1) scalar_mul E.symm(v). | CORRECT: additive cancellation even if the scalar is zero, so no missing n>0 premise. |

AM's generated theorem has recursive axioms [propext,Quot.sound]. AO._simp_1_8 and both AO._abel theorems have [propext,Classical.choice,Quot.sound]; each of AO's other six simp theorems has [propext]. Every public theorem has [propext,Classical.choice,Quot.sound]. Every set is inside the whitelist, with no sorryAx or added axiom.

## Exact server kernel / recursive whole-owner evidence reused

All successful logs and complete audit content were inspected without replay: each complete actual-types file is the entire DECL/TYPE/AXIOMS portion of its server audit.log. The entire remaining log has only the known thin-overlay mathlib warning and five expected count/PASS markers. Each successful133-byte build log contains only that warning, no Lean error/additional source warning. Consumed Mathlib source bytes were compared to the pin as above; no source/dependency/cache was fetched or rewritten.

Runs are /root/rivermind-data/shao-lean-20261021/runs/oq3/u22am-20261023 and siblings u22an-20261023/u22ao-20261023. Local scope/source/receipt/types/audit/environment hashes match server artifacts. All audit-record.json fields were read. Toolchain is leanprover/lean4:v4.36.0-rc1; actual mathlib HEAD807d3836b165983210ee2ecf3cd28f239436949c. Checks use unchanged accepted-source-view plus each module's own new artifact.

| Binding | AM | AN | AO |
| --- | --- | --- | --- |
| Successful source attempt |source-02.lean |source-02.lean |source-03.lean |
| Kernel exit / seconds |0 /5.483365513384342 |0 /5.240646092221141 |0 /5.537797698751092 |
| First whole-owner AX exit / seconds |0 /5.765227833762765 |0 /5.86361825838685 |0 /5.846788328140974 |
| Definitions / public / all theorems / all declarations |0 /2 /3 /3 |0 /2 /2 /2 |0 /1 /10 /10 |
| receipt.json SHA256 |ee62b7fa278613c37ceed8c3a7c34fbdbee3f3c8051afdd8fe8d0875ddd0c265 |02ff946c0d8737833b1ef527b7664478e47ea1e283b3c8f7817902d752361b96 |ebaac50c527d411b5918c2119808423c3eb1441c884adb3bde12db7bece0776d |
| Audit.lean SHA256 |4824fad2ecfb02b7242d1aa77e11b720a3083e705ea5c8173b5dd86551249313 |a822470bec0c6969647ad597862f3371b30802af70e972c6bd386eafb416fb6a |d651e8c808f51f5f86b796d62406817720f39f879cd694747fdacc749c4814be |
| audit.log SHA256 |7ad62f8dd5038e1c0f7d514e9b05f379912ae924fee78c91ec74aee489f10d3a |2f29b7125a4746a988a67553ac4fa421121ccce024ccb5f65d80926e3dc99469 |42b72bf3989d2700b4e5f8f984fc7e0f08c6a54e8ca3871daac9966f7226b557 |
| actual-types.txt SHA256 |64b0c4aa5e77cf1374bdfae3d704fbb7f2fcad9de68bee367702d1f6bb456f25 |643f0cf08a05d6df75528a5bb7d3261132ade45aad9627c6282dbdecd263edfa |a97ab8d7856e894ec11a1d5e67ef20e6e71d2e4641bae229576e4e06788689f9 |
| audit-environment.json SHA256 |16badab641d72f54b07f543d8cb458e240b8338feec95ab7c3b9cac8ba852075 |3a5e4c1e4e5d6c8709561225ba5d93beb467e5d9616fd4e74423fe0a14043eca |8fe360c6377742f5b10b54400101d937098077f95f1f8e5f69ee7a304b734a2a |
| audit-record.json SHA256 |bc8af754519dbe625ad154e3e6219e3408c8d82f0c8fc012e399ceef66aa22f8 |9e87849f7ab9a4d2005bff2f87c221215892ddb5d4bfd9f105f5b72c7b620109 |20260c0b0e89e47d313830b37b39b18e2830de01fe7f2a39190d46d12c363fc0 |

The common successful-build-log SHA256 is fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626. Every successful kernel/AX record specifies CPU14-17,native8192MiB,jobs4,autoImplicit=false. Audit scripts verify frozen names are actual theorems, enumerate env.constants by getModuleIdxFor? actual module ownership, reject owned axioms and call Lean.collectAxioms recursively for EVERY owned constant. Coverage is actual ownership, not public names or namespace prefixes alone. All three AXIOM_GATE markers PASS with the exact table counts.

All failed snapshots/logs remain archived. Read-only hashing verifies every archived source/log against build-history: AM01,AN01,AO01/02 have exit1; AM02,AN02,AO03 have exit0. Earlier failures are not counted as success. Declarations remain frozen as above; no successful gate was repeated.

Accepted-source-view resolves to the lane's own built .olean files, without local binary/cache copies:

| Module | Actual resolved object SHA256 |
| --- | --- |
|QuadraticSampleChangeOfMeasure |915e61dcc8e08a1019c9506bb76e4e77a8bac3774d43f4f0b6c5e30869fff125 |
|SampleParabolaTailDomain |bf1ad5800b710c4e789942f48cfb499cf78847774b6b2a64005002509df96b9c |
|StandardizedCellChangeOfMeasure |9c9a1bebc7acef561cd56cdedcaa6447ed3ddd4313f467027ab38ce211c07df5 |
|BoundaryLaplacePhysicalDomain (AI) |b6968c75e62296b8bd273c61028c82ee44b7ddbbcfe6462b99d2f2dac077504f |

AI's object matches its prior qualified report. Direct parent source hashes for FinitePath/BivariateLegendre and exact AM/AI match environment manifests. Existing accepted parent qualification is reused; this is not another full old-chain proof review or an aggregate integration gate.

## Final verdict and scope boundary

Public verdicts: CORRECT for Shao.OQ3.iid_quadratic_sample_tilt; iid_quadratic_cell_change_of_measure; sample_self_normalized_tail_iff; iid_self_normalized_tail_map_and_split; iid_quadratic_standardized_cell_change_of_measure. Every one of the ten exact generated declarations above is individually CORRECT. Batch interfaces are CORRECT: AO consumes exactly AM's G/Q/event; AN's M is the same actual sample map; all signs, factors, quantifiers and n restrictions agree. Complete review covers371 source lines,15 complete actual owned types,0 global definitions,all local values and all final proofs.

The precise frozen auxiliary scope has exact-source server kernel/recursive whole-owner AX PASS plus this fresh complete independent semantic/proof review, hence LEAN_FULLY_CHECKED in that scope. AM removes genuine iid tilt-normalizer and exact cell probability/likelihood obligations including unbounded mu/n0. AN supplies exact positive-energy tail/pushforward/near-far split for n>=1,level>0. AO exports the actual affine-transformed tilted sample law, exact measurable image cell and genuine inverse-likelihood integral for any explicit continuous linear equivalence.

No Gaussian/Edgeworth approximation, covariance whitening producer, small-cell boundedness/oscillation estimate, uniform cell error, local probability comparison, exterior exponential probability bound, finite-cover/rate-gap argument or OQ3 B/D closure is proved. Source equation6's I(y) interpretation still needs actual mean/rate specialization; equation8's geometry/test-function bounds need the genuine covariance choice, cells and uniform bounds. Thin cells/atoms are respected by the exact identity but give no approximation estimate. Original fixed x in(0,1),strict beta<2/5,actual tilt moment/spectral/WC/global-saddle assumptions,corrected constants,Song/Angst-Poly attribution,p54 repairs,accepted corrected-A/bounded-C scope and other roots are not broadened. No novelty claim or PR merge is made.

This is the sole written artifact. Strict UTF-8/LF line/byte count and SHA256 are returned after the final integrity operation. This context then stops all tools/writes; the lane lead owns continuation.
