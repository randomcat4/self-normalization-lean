# OQ3 U22aw / U22ax independent complete final review

STATUS: CORRECT

U22aw closed-ball theorem: CORRECT. U22aw arbitrary-cell thickening theorem: CORRECT. U22ax standardized Gaussian averaged-oscillation theorem: CORRECT. Both generated theorems: individually CORRECT. Complete frozen statements, all proof-local values, dependency applications and source-to-statement scope: CORRECT. No critical mathematical or evidence gap was found in this auxiliary scope.

Reviewer: sole fresh independent complete final reviewer, separate from the author, assigned gpt-6.1-sol / xhigh. Applied math-theorem and current project AGENTS.md, SERVER.md, compact TEAM/REGISTRY and streamlined acceptance. OQ3 owner 01a1669a-bca1-75e0-9d87-d07baee7b90a is ACTIVE, newWriterActivated=true and oldWriterReleased=true; these ownership facts are not treated as proof of runtime activity. Only this report is written. No source, freeze, receipt, parent review, shared implementation, cache or continuation file is changed. No children, math-ultra, model switch, Lean/lake invocation, gate replay or merge occurred. Every remote observation was read-only through tools/server.py with CPU14-17 affinity. Actual separate input, cached-input, output and reasoning-subset counts are unavailable to this reviewer; no token counts or subscription-percentage allocation are invented.

## Exact inputs and complete coverage

Evidence directory: C:/game/shao lean/drafts/oq3/. Both final sources were read completely: AW67/67 and AX79/79 lines, totaling146 lines /7236 bytes. This includes every import, namespace/setup line, complete public declaration, proof-local value, proof step and closing line. Both entire freezes, actual exports, audit programs, receipts and environment manifests were read. Actual DECL/KIND/VALUE records independently give AW3 theorems and AX2 theorems: three public targets plus two generated theorems, zero global definitions, zero private theorems and zero other owned constants. Exact exported names/order equal each receipt's all_owned_names; no count is copied from a descriptive summary.

| Input | SHA256 | Lines / bytes |
| --- | --- | --- |
| hundred-thirtieth-unit-scope.md | fc8e134881e3b96b972c4a2dd427979b7802ef4fab9376dc2d525bf2cfa45ea1 |24 /2290 |
| u22aw-source.lean | cf8f503b106b2ed2e3a5af602a8cf997f133da611f6c685226794789b3476246 |67 /3115 |
| u22aw-receipt.json | 633a67e93f17077c3b7b68571a03f96a77ac5e146bce240e0670f04c79fefbc3 |115 /4665 |
| u22aw-Audit.lean | f89299ac766730728008f0cc9ce7f4a8bbc61fdfc83751cf487b5387ef3ba673 |49 /2059 |
| u22aw-actual-types.txt | 2fb929cdc29985a642ef779392e9862a0f9ce652258fea0f4c15c6d6c490796e |20 /919 |
| u22aw-audit-environment.json | 8792ab3d5f80db4dd16b41ee31c8d4159fbedea108ad7cf52c5e095a6eb7c060 |12 /654 |
| hundred-thirty-first-unit-scope.md | ab990bd1ef147569573b792576841cde1eebe1b22ac075bb9ba84bbfead0a305 |29 /2675 |
| u22ax-source.lean | 3d071a81d880a7ec8dd770a42caad8c6f07118bb86d628fd7e72647c55d81c6d |79 /4121 |
| u22ax-receipt.json | 62df1db5f5cd12c4e8e5cd929cc5d0cfa7838479efe2d4320a50680dbad0303b |116 /4789 |
| u22ax-Audit.lean | 816d930fab0a8d224bc625e0894695d9b3eb873b4f1f67a874ddab165b81e749 |48 /2032 |
| u22ax-actual-types.txt | 77c048cf69c951b17baf5181850f3037fe981238b3c69eace863de945566c15e |24 /1450 |
| u22ax-audit-environment.json | 05d2ffa6e0886f07bfa82e5f5485e1e69bb5deb1cef8f3c3c3e0d5e61fc958be |14 /798 |

All table hashes were recomputed locally and independently on the server, with equality. The files are strict UTF-8 without BOM or CR bytes and use LF. Each complete public declaration before `:= by`, including AX's entire sequence of statement let values, matches the corresponding frozen code after whitespace normalization. Both server scope snapshots have earlier mtimes than source01/source02, consistent with the recorded preimplementation freeze. The full source01-to-source02 diffs change only proof expressions; no declaration, mathematical assumption or conclusion is revised. Neither final source contains sorry/admit/new axiom/unsafe/native_decide.

Observed worktree: /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3; branch feat/oq3-cell-oscillation-probability; HEAD e541a9ec39cf235fad723cf465a2b6ba575f637c. Both new modules remain untracked. Their current bytes equal the reviewed local sources and successful source-02.lean snapshots. Acceptance therefore binds exact source hashes, not the parent HEAD alone. Later AY and other continuation modules are outside this review.

## Every complete actual owned type

The exact exports were read in full locally and in the complete existing server audit logs. All five constants are theorems, each with recursive axioms `[propext, Classical.choice, Quot.sound]`. No global definition value is omitted because neither new module owns a definition.

```lean
-- Shao.OQ3.standard_gaussian_plane_closed_ball_bound._simp_1_1
∀ {α : Type u} [inst : PseudoMetricSpace α] {x y : α} {ε : ℝ},
  (y ∈ Metric.closedBall x ε) = (dist y x ≤ ε)

-- Shao.OQ3.standard_gaussian_plane_closed_ball_bound
∀ (r : ℝ),
  0 ≤ r →
    ((ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1)).real
      (Metric.closedBall 0 r) ≤ 4 * r ^ 2

-- Shao.OQ3.standard_gaussian_plane_cell_thickening_bound
∀ (A : Set (ℝ × ℝ)) (r h : ℝ),
  0 ≤ r →
    0 ≤ h →
      A ⊆ Metric.closedBall 0 r →
        ((ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1)).real
          (Metric.cthickening h A) ≤ 4 * (r + h) ^ 2

-- Shao.OQ3.standardized_gaussian_cell_averaged_oscillation_bound
∀ (n : ℕ),
  1 ≤ n →
    ∀ (theta : ℝ × ℝ) (E : (ℝ × ℝ) ≃L[ℝ] ℝ × ℝ) (y : ℝ × ℝ) (d : ℝ),
      0 ≤ d →
        ∀ (A : Set (ℝ × ℝ)),
          (∀ w ∈ A, ‖w - y‖ ≤ d / ↑n) →
            ∀ (h : ℝ),
              0 ≤ h →
                have B := (fun w => √↑n • E (w - y)) '' A;
                have g := fun v => Real.exp (-√↑n * (theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2));
                have kappa := (|theta.1| + |theta.2|) * ‖↑E.symm‖;
                have R := d * ‖↑E‖;
                have C := Real.exp (kappa * R);
                have Φ := (ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1);
                MeasureTheory.Integrable (Shao.OQ3.openBallOscillation (B.indicator g) h) Φ ∧
                  ∫ (z : ℝ × ℝ), Shao.OQ3.openBallOscillation (B.indicator g) h z ∂Φ ≤
                    8 * √↑n * kappa * C * h * (R / √↑n + h) ^ 2 +
                      2 * C * Φ.real (Metric.cthickening h (frontier B))

-- Shao.OQ3.standardized_gaussian_cell_averaged_oscillation_bound._simp_1_1
∀ {α : Type u} [inst : PseudoMetricSpace α] {x y : α} {ε : ℝ},
  (y ∈ Metric.closedBall x ε) = (dist y x ≤ ε)
```

Individual generated verdicts: AW's _simp_1_1 is CORRECT; AX's _simp_1_1 is CORRECT. Each quantifies every universe and PseudoMetricSpace, with arbitrary center, point and real radius. Closed-ball membership is precisely the displayed non-strict distance inequality; equality here is equality of propositions. No positive-radius or genuine-metric premise is hidden. The existing source-bound kernel and whole-owner audits cover both actual generated proofs, not merely their public parents.

## Qualified dependencies and exact consumed values

The complete AP, AV and AU source files, their complete actual-type exports, and all three complete existing final reports were read. Their unchanged complete qualifications are reused; no old proof or gate is reopened simply because this context is fresh.

| Qualified parent | Source SHA256 | Complete reused report SHA256 / lines / bytes |
| --- | --- | --- |
| AP / StandardizedCellBounds | 9dca0c3b15c57442b5d36cc96334c64320701e38925753baf47ade096bc3f402 | u22apaq-proof-review.md: 4d513e9cd8bd3ae775e697c5d39e8a4d4dc62247fac4aa6aa892ac167e784509 /138 /28115 |
| AV / CellAveragedOscillation | d92e1728663023c77a4315ce3dee53aff5d230e46d65a7f98657ba411f4d7487 | u22av-proof-review.md: e976833ac9dfa53edd612c9c22e5d214dee34fa870f8a008217e466014352246 /136 /23089 |
| AU / OpenBallOscillation | f1e693a8b9b2db416dd730bcdfb596030d768b911015bcfdfc50a16e97e62e2d | u22au-proof-review.md: c889f6d17b8fd2415f20ab3dd5ade726d011097668bd17ff73a2bd66f38440e0 /139 /22221 |

Their complete actual exports have identities AP8906afdc5186c5702a431aa06c1c8e40841623a08d7d2948ec8a5b9ae27c37e0 (43 lines /2619 bytes), AV99e1e389989195350f9ef49bcffbb3fd5e3e2b89a1e5d8ff25d007f33c4c9ab8 (21 /1265), AU6ffe4fb44aecebd2853b382f45d52f22f7f20f91219356ac337366b81d30fe11 (24 /1464). Current server source hashes match each qualified source. The AP/AV/AU accepted-source-view objects resolve to the same own worktree objects qualified previously: APc8d8a4ebb2a86a7b4039a4773d1ce5d006447aea84206eaa899d1f7a65c9a036, AV9f8cbe1ee0085940580934321bb5827d6c104849ff82b5218b7a9f041209e4ce, AUe8302c05e5b9717224b8ef8a78cad3a469d277b7f4c8fb5cc80e9a14509dca06. No parent source/object discrepancy remains.

AP's consumed support type quantifies every n>=1, actual continuous linear equivalence E, anchor y, d>=0 and arbitrary A, with the literal hcell bound on every w∈A. It concludes for every member v of the exact image F(A), F(w)=sqrt(n)•E(w-y), that ‖v‖≤d*‖E as continuous linear map‖/sqrt(n). Its other consumed theorem defines coefficient B=(|theta.1|+|theta.2|)*‖E.symm as continuous linear map‖ and the exact inverse-map exponential g. For R>=0 it proves actual positivity and |g(v)|≤exp(B*R) on ‖v‖≤R/sqrt(n), plus |g(v)-g(w)|≤sqrt(n)*B*exp(B*R)*‖v-w‖ on that same ball. These are derived producers, not desired weight/Lipschitz assumptions. The AP report also qualifies alignment with the actual AO affine cell and inverse likelihood weight, without asserting a covariance-square-root identity for arbitrary E.

AU's full definition value is exactly `fun f h z => sSup (insert 0 {r | ∃ u ∈ Metric.ball z h, ∃ v ∈ Metric.ball z h, r = |f u - f v|})`. Its complete qualification proves genuine boundedness of this value set, nonnegativity, all-pair domination, open strict superlevel sets and Measurable, under the everywhere bound |f|≤C and C>=0. Its finite-measure integrability theorem supplies genuine Integrable of this identical function. Empty balls are handled by inserted zero. This is neither an essential supremum nor a measurable envelope, and no default nonintegrable integral is being substituted.

AV's complete consumed type is for any finite μ, arbitrary A,g and C,L,h>=0, with only |g|≤C on A and the L-distance bound between pairs in A. It concludes genuine Integrable of this same openBallOscillation(indicator_A g), the all-center majorant `(cthickening h A).indicator (2*L*h) + (cthickening h (frontier A)).indicator (2*C)`, and the literal integral bound `2*L*h*μ.real(cthickening h A)+2*C*μ.real(cthickening h (frontier A))`. Its complete proof and existing report explicitly derive a global bound for the indicator, use AU's genuine measurability/integrability, bound every member of the actual pair-value supremum, and dominate actual closed-ball hits by the closed thickenings in the correct direction. The two majorant indicators are measurable because the thickenings are closed, and integrable because μ is finite. `integral_mono` is applied with BOTH integrability proofs, followed by legitimate integral_add and integral_indicator_const. Thus the new AX invocation inherits a qualified genuine integral inequality, including for nonmeasurable A, rather than importing a missing integration premise.

AW's direct accepted OQ4 source was read completely, including the consumed full types and the actual standardNormalCDF definition: library/Shao/OQ4/IntervalConcentration.lean, SHA256491e088fccc4457f18701ab7440da8cc9811183d462e3f3b7f22b096ccbf0875,163 lines /8765 bytes. Current server source is identical. The accepted-source-view IntervalConcentration.olean resolves to workspaces/integration-bearing-v43/.lake/build/lib/lean/Shao/OQ4/IntervalConcentration.olean with SHA25628b1b4463996ab9fb521de2847bff6928e3f98633d47460b1b27dfa6976d3c31,505344 bytes, exactly the assigned accepted identity. Its existing complete independent formal qualification interval-concentration-formal-review-v1.md was read and reused unchanged (drafts/oq4/review/, SHA25620b7a7bf0c121562201f2cb945f725699319706bfa4bd884787cf6bf4fd4bb4f,118 lines /9074 bytes). Its accepted lead receipt was read, SHA256176c9d1e7c184d34caa0443b7a5993f9953a3271d87217f0c810111f53218e7f,57 lines /2299 bytes. Historical CPU0-3 commands in that old receipt are historical evidence only; this reviewer launches no such command.

In that qualified OQ4 API, standardNormalCDF(x)=cdf(gaussianReal 0 1)(x), with exact equality to the actual γ.real(Iic x). The actual normal CDF is proved globally 1-Lipschitz from its genuine Gaussian density integral, not assumed. The closed-interval theorem takes any probability μ, L,ε>=0, any G with the global L-Lipschitz bound, all-x actual Iic-CDF error≤ε and a≤b, and concludes μ.real(Icc a b)≤L*(b-a)+2*ε. Its left cutoff a-δ and limiting inequality retain the left endpoint atom; ε=0 and a=b remain valid. AW uses precisely these already-qualified facts with the actual γ, L=1, ε=0 and endpoints -r,r. It does not invoke an iid Berry-Esseen premise or claim any sample-law atomlessness.

## AW: complete proof and all local values

standard_gaussian_plane_closed_ball_bound: CORRECT (AW10-42). The complete type has only an arbitrary real r and r>=0; its measure is the actual product of two gaussianReal 0 1 laws. AW15 defines γ as exactly that one-coordinate Gaussian and AW16 defines I as the actual closed interval [-r,r]. These are the only term-level lets in this module.

AW18-22 proves hCDF for EVERY real x, with zero error: after unfolding the actual γ at AW20, standardNormalCDF_eq_real makes the two identical real masses equal, and simp gives |0|≤0. It does not introduce a desired approximation premise. AW23-26 applies the full closed-interval theorem with L=1, ε=0, the actual standardNormalCDF, both nonnegative scalar proofs, its existing Lipschitz theorem with only one_mul normalized, hCDF, and -r≤r derived from hr. AW27 simplifies the exact expression 1*(r-(-r))+2*0 to 2*r. This proves the actual hI:γ.real(I)≤2*r, including r=0 and both endpoints.

AW28-34 proves hsub from every actual closed-ball member z. The existing ℝ×ℝ norm is max(|z.1|,|z.2|); Metric.mem_closedBall and dist_zero_right yield that maximum≤r. Each coordinate absolute value is at most its maximum, and abs_le produces precisely -r≤z.i≤r for both coordinates. Thus z∈I×I. There is no use of Euclidean norm equality or volume of a different ball; subset containment alone is sufficient even though in this metric the sets in fact coincide.

AW35-39 uses real-measure monotonicity with explicit finiteness of the target rectangle under γ.prodγ, then the actual product-real rectangle formula. Gaussian probability implies finite and s-finite, and its product is a genuine probability measure; therefore the formula is for the intended product law and no junk zero-product fallback can apply. I is also closed/measurable, though the pinned rectangle formula supports arbitrary sets. AW40-41 multiplies hI by itself using γ.real(I)>=0 and 2*r>=0 from hr. Both signs required by mul_le_mul are present, so a potentially negative real mass or upper bound is not silently squared. AW42 is exactly (2*r)*(2*r)=4*r² by ring. All finite-mass conversions are justified: Measure.real is (μ S).toReal, but these probabilities are never infinite.

standard_gaussian_plane_cell_thickening_bound: CORRECT (AW44-64). Its full type adds an arbitrary set A, h>=0 and the literal containment A⊆closedBall(0,r); it adds no measurability, closedness, compactness, density or desired-mass assumption. AW50-55 proves the precise geometric hball. The pinned cthickening_cthickening_subset uses ε=h, δ=r and s={0}, with hh and hr in that order, giving cthickening(h,cthickening(r,{0}))⊆cthickening(h+r,{0}). The two cthickening_singleton rewrites are valid at r>=0 and h+r>=0. Addition commutativity yields exactly closedBall(0,r+h) on the right, with no radius loss or attained-distance assumption.

AW56 composes cthickening's monotonicity under A⊆closedBall(0,r) with that hball. AW57-62 applies real-measure monotonicity and explicit finiteness of the actual Gaussian product at the larger closed ball. AW63-64 invokes the just-proved closed-ball bound at r+h>=0. This is the exact frozen 4*(r+h)² conclusion. Empty A, nonclosed/nonmeasurable A, singleton A, thin sets, r=0 and h=0 are all covered. At h=0 cthickening is closure(A), which remains in the containing closed ball. At r=0 the first theorem genuinely forces the Gaussian singleton mass to zero from the accepted closed-interval/CDF result; it is not an added atomlessness assumption about a sample law.

## AX: complete proof and every local value

standardized_gaussian_cell_averaged_oscillation_bound: CORRECT (AX10-76). The full statement retains n>=1, arbitrary theta, actual invertible continuous linear E, anchor y, d>=0, arbitrary A with hcell for every member and h>=0. Its B,g,kappa,R,C,Φ are exact local values, not extra quantified objects or assumptions. AX29-35 repeats the statement lets identically: B is the affine image, g has the same negative sign, sqrt(n), coordinates and actual E.symm, kappa uses the norm of E.symm's underlying continuous linear map, R=d*‖E as continuous linear map‖, C=exp(kappa*R), and Φ is the actual product standard Gaussian. AX36 introduces only L=sqrt(n)*kappa*C. There is no alternate support, truncated weight, proxy measure, covariance identification or new global definition.

AX37-42 proves all coefficient signs. hkappa uses nonnegative absolute values and inverse operator norm; hR uses hd and the operator norm; hC follows from strict positivity of the actual exponential; hs is square-root nonnegativity; hL multiplies precisely these nonnegative factors. No sign of theta's coordinates is required. n>=1 also supplies strict positivity of sqrt(n) inside the qualified AP producers, so their cancellation/division steps have no n=0 case. The new use of div_nonneg at AX58 only needs hs>=0 and hR>=0 and is therefore valid, with the stronger positive denominator already secured by hn for the actual setting.

AX43-44 obtains hsupport for the exact local B by applying AP with the unchanged n,hn,E,y,d,hd,A,hcell. Unfolding R gives precisely the AP radius d*‖E‖/sqrt(n). AX45 applies AP's exponential theorem with this R and hR. AX46-48 derives hbound for every actual v∈B by passing its hsupport to hweight and selecting the actual absolute-value upper bound. Its g,kappa,C are definitionally the same as AP's g,B,exp(B*R). AX49-51 similarly feeds both support facts into hvariation; unfolding L and rewriting dist(u,v)=‖u-v‖ yields the exact on-B distance bound. No bound on g outside B or on a larger neighborhood is assumed: AV legitimately needs regularity only between points of B, while the indicator is zero elsewhere.

AX52-53 instantiates the full qualified AV theorem with μ=Φ,A=B,g,C,L,h and the three explicit scalar signs hC,hL,hh, followed by the derived hbound,hLip. Gaussian probability and its product supply the required IsFiniteMeasure instance. The outputs are genuine hint:Integrable of the exact openBallOscillation(B.indicator g), an all-center hpoint majorant and the actual havg integral bound. hpoint is simply unused afterward; it is not a hidden hypothesis. The global bound of B.indicator g, its supremum's measurability and genuine integrability, and both integrability premises for integral monotonicity are already established by this qualified AV/AU invocation. Φ.real is finite at every set, so no infinite-mass-to-zero convention weakens either term.

AX54-56 converts the same hsupport to hB:B⊆closedBall(0,R/sqrt(n)) by the actual closed-ball membership and dist_zero_right. AX57-58 applies the newly reviewed AW thickening theorem to precisely this B, that radius, and the original h. Its required radius sign is div_nonneg hR hs, its thickness sign is hh, and its containment is hB. Thus hnear is the actual Φ.real(cthickening h B)≤4*(R/sqrt(n)+h)². It is not supplied as a premise and is not a bound for a different Gaussian/support set.

AX59 explicitly proves hcoeff:0≤2*L*h. AX60-64's change only zeta-reduces the statement lets to the identical proof values; it does not alter a binder, functional or conclusion. AX65 preserves genuine hint as the first conjunct and composes havg with the remaining inequality. AX67-71 multiplies the actual hnear only by hcoeff>=0, then adds reflexivity of the unchanged literal boundary term on the right. There is no needed sign assumption on that added term for add_le_add; in fact it is nonnegative because C and Φ.real are. AX72-76 unfolds only L and uses the exact ring identity 2*(sqrt(n)*kappa*C)*h*4*s²=8*sqrt(n)*kappa*C*h*s², with s=R/sqrt(n)+h. The final coefficient, power, near radius and entire boundary term match the freeze exactly. No small-h bound or boundary-tube estimate is used in this algebra.

All permitted degeneracies are safe: n=1, theta=0 (kappa=L=0 and g=1), d=0, h=0, empty A/B, nonclosed or nonmeasurable cells, thin sets, and nonattained distance infima or pair suprema. At h=0 the actual open balls are empty and inserted-zero oscillation is zero, while the boundary majorant can remain nonzero; this is a harmless upper bound. At d=0 every original member is y and its affine image0, consistent with R=0 and C=1. Arbitrarily large finite theta/E/d/h are allowed; the real exponential is finite for every such real argument. No assertion of uniform constants over varying E or theta follows from mere invertibility.

## Pinned primary APIs and the known warning

Server lean-toolchain is leanprover/lean4:v4.36.0-rc1. Actual mathlib resolves to cache-overlays/shared-v34/packages/mathlib at 807d3836b165983210ee2ecf3cd28f239436949c. No toolchain executable was invoked. The new Gaussian/product/finite-mass/thickening APIs and relevant surrounding assumptions were inspected directly; each primary file below was byte-compared with git show at the exact pin and matched.

| Primary Mathlib file | SHA256 |
| --- | --- |
| MeasureTheory/Measure/Prod.lean | 007561e86f53a65ad411fcbd20d05df9e922f01c5a93eff0f9de26ac49f12ca3 |
| MeasureTheory/Measure/Real.lean | 1b9d1490fa5acbffc570eac67f465d3d6ab0520aa3e54464f7520d60d6619b8d |
| MeasureTheory/Measure/MeasureSpaceDef.lean | 3853c6899a36759a64c9658969fb2f1ea97f0d026598c0f0468c30fe2a5d7356 |
| MeasureTheory/Measure/Typeclasses/Finite.lean | a8ef0ba0a9b953a5aae9fb16188cd7ad93e0e8d5767c564d02e9f2e8c57eedf2 |
| MeasureTheory/Measure/Typeclasses/Probability.lean | 00ef2a106c0ae4032944cec021ad58d04c370cc9b84547bed95462ca5205e25b |
| Topology/MetricSpace/Thickening.lean | 6429465471cb6e7121b79c0509583ea258efadd837133350e9faf7c47775a220 |
| Probability/Distributions/Gaussian/Real.lean | 9edebfff169cb577b6dab1a7912f2e8fec0e70a8dac39db105263e1a0f31b383 |

The actual gaussianReal(mean,variance) is dirac only at zero variance; at variance1 it is volume.withDensity of the actual Gaussian PDF. gaussianPDFReal is `(sqrt(2*pi*v))^-1*exp(-(x-mu)^2/(2*v))`; gaussianPDF is its ENNReal.ofReal. The existing Gaussian probability instance gives total mass1 for this actual law. The product definition uses its genuine bind/map construction for an s-finite second measure; the Gaussian's probability/finite instances ensure that condition, and the product probability instance gives Φ(univ)=1. The pinned measureReal_prod_prod is under the explicit SFinite second-measure section and gives the full real rectangle identity, without omitted set-measurability assumptions. Both coordinate Gaussians meet every measure-class condition.

Measure.real is exactly `(μ S).toReal`; measureReal_mono requires finiteness of the larger set, and the two AW uses provide it explicitly via measure_ne_top for the finite Gaussian product. cthickening is exactly `{x | infEDist x A ≤ ENNReal.ofReal h}`. The inspected monotonicity, singleton rewrite and iterated-thickening containment have exactly the signs supplied in AW. Product maximum norm and the remaining AP/AU/AV integral/supremum APIs retain their unchanged pinned qualifications in the complete reused reports. The successful Lake warning therefore does not hide a modified new primary API or a changed qualified parent interface.

## Existing exact-source server kernel and whole-owner recursive axiom evidence

Runs: /root/rivermind-data/shao-lean-20261021/runs/oq3/u22aw-20261023 and sibling u22ax-20261023. Both complete failed/successful build logs, complete audit logs, build-history.json and audit-record.json were read. All source/log hashes and byte sizes were recomputed. Each receipt.build_history exactly equals its complete server history, receipt.audit exactly equals audit-record.json, and the entire exact local actual-types.txt occurs verbatim in audit.log. No success is inferred from a dispatch or replayed for this review.

| Evidence | AW | AX |
| --- | --- | --- |
| Final source-02 kernel exit / seconds |0 /5.18019575625658 |0 /5.461607905104756 |
| build-02.log SHA256 |fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626 |fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626 |
| build-02.log lines / bytes |2 /133 |2 /133 |
| First complete whole-owner AX exit / seconds |0 /6.297009142115712 |0 /6.244888702407479 |
| audit.log SHA256 |42eb5c46461c4584d764981c4b6ce3e0802af9f22fd5949b4533beecaede27bf |ca2b7bc907b21d210e0aa22ceef4d791b4729a2f5091dce81c190efb48514fd6 |
| audit.log lines / bytes |27 /1171 |31 /1702 |
| build-history.json SHA256 |31d2fd507ee3b14de16eb1a9bae033b7763a7f8ac09d1ee9631d580b5efebc25 |a2a2fc2218092be274557748a92c2d71caf8ff9757cf7a390752f55ec6eae482 |
| build-history.json lines / bytes |50 /1932 |50 /1906 |
| audit-record.json SHA256 |4bf4f8ff953d6833f73831cb6426840418ce5176e2f68bab0abc7671acec67ca |dccacfa0fae10fb835cad4fcb9c864e138e6d8299b4d650b517903adc78700de |
| audit-record.json lines / bytes |18 /498 |18 /498 |
| Current own olean SHA256 |481b3b7696dcb2041b45db370c05c9d03b615e7128fe27ea7f889b84fdd25c80 |4d2dfd168f079af58adb648d5d3ed9d52e83acc8a7a5b704c1edf27ade85e91d |
| Current own olean bytes |126088 |201976 |

The accepted-source-view symlinks resolve to those exact own worktree objects. Both environment manifests record reuse of the accepted read-only view and only their own new artifacts, with the exact qualified dependency source hashes. Successful kernel/audit records specify CPU14-17, native8192MiB, jobs4 and autoImplicit=false. Both successful source logs contain only the known two-line Lake/mathlib local-changes warning; there is no source warning, proof error, suppressed failure or skipped final target.

Each entire audit program first requires the exact frozen public targets to exist as theorems, then iterates ALL constants with actual getModuleIdxFor? owner equal to its module. It rejects owned axioms and recursively calls Lean.collectAxioms for EVERY owned constant, rejecting any dependency outside propext/Classical.choice/Quot.sound. It logs complete types, theorem kinds and definition values if any. AW reports0 frozen definitions/2 frozen targets/3 total theorems/3 total declarations and U22AW_AXIOM_GATE PASS; AX reports0/1/2/2 and U22AX_AXIOM_GATE PASS. The actual exports agree. This covers both generated theorems and any private/other owner should one have existed; it is not public-name-only or namespace-prefix selection. Each of the actual five has exactly the standard three recursive axioms.

AW archived source01 SHA256133e5e0dc472d7df115872e8eb4b6f33d07922d4d55d913091f7e400ecc84adc (66 lines /3074 bytes) has exit1 and remains preserved. Its full build-01.log SHA2569da6f7fd3d8d2573ba6de718757d86dc5ff966dee7368bd9105ee082c0d43324 (17 lines /933 bytes) reports the unnormalized coefficient1 in the Lipschitz argument and nonexistent add_self_eq_two_mul alias. The complete final diff introduces the pointwise one_mul normalization and replaces only that alias with two_mul. AX archived source01 SHA256cde6da0fce5cdfce2df80a78f4aae7713ccfc26295a03461f9824dd313931c3a (79 lines /4122 bytes) has exit1. Its full failed log SHA2562f52ebeee8c8a44b61f01e2d320956d5fd40f9aebf4df80cab7c44d5ac6766ef (10 lines /673 bytes) reports add_le_add_right's addition orientation. Its sole diff replaces that expression by add_le_add of the same inequality and le_rfl. Both repairs preserve frozen declarations and mathematical assumptions; neither failed attempt is counted as success. All archived failures and warnings remain intact.

## Original-source fidelity, scope and final handback

Read the complete original repair01.md, in particular section2 lines43-110 and equations2-6, and report.md lines112-216 containing the Gaussian oscillation/Edgeworth context, actual cell/weight and equations7-9. Read-only identities under C:/game/shao/current/oq3/proofs/r2/ are repair01.md SHA2569d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd (226 lines /5846 bytes), report.md SHA256572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55 (20102 bytes).

The source B_Q is the image of an original small cell under sqrt(n)*Delta_Q^(-1/2)*(w-y_Q), and its test is exp(-sqrt(n)*theta_Q dot Delta_Q^(1/2)*v) times the indicator of that image. AX keeps the exact affine-image and inverse-map exponential structure already qualified in AO/AP and used by the prior cell-oscillation chain, with general explicit E and its actual inverse. It uses actual raw-cell support hcell to derive the actual support/weight/Lipschitz inputs. AW supplies the genuine product-standard-Gaussian near-neighborhood bound, and AX combines it with the genuine integral inequality for the actual supremum functional. Their roles in source equation4 and the near-set portion of equation5 are substantive and do not assume the desired probabilities or final integral error.

The formal norm on ℝ×ℝ is the existing maximum coordinate norm. All balls, thickenings, distances, operator norms and oscillations in the conclusions use it consistently. The product standard Gaussian law is the actual coordinate-independent standard Gaussian, but no literal Euclidean ball radius, covariance-whitening identity or source-family-uniform constant is silently asserted. E being an arbitrary continuous linear equivalence proves none of those additional source instantiations. For fixed theta,E,d, kappa,R,C are independent of n; uniformity over varying source cells still needs legitimate uniform parameter/operator/geometry bounds.

AW's whole-ball bound has the correct near-cell scale4*(R/sqrt(n)+h)^2 once the legitimate AP support is supplied. It does not give the sharper thin-frontier-tube scale O(h/sqrt(n)+h²). AX's boundary contribution remains EXACTLY `2*C*Φ.real(cthickening h (frontier B))`, with no assumed or concluded final tube bound. Consequently neither the h=n^-3 O(n^-7/2) oscillation rate, the actual at-most-five-arcs boundary geometry, the source whitening family/anchors/partition, the actual Edgeworth probability comparison, per-cell probability error, summation/exterior estimate, full Laplace probability nor original OQ3 B/D is closed here. No identification with an external bar-omega definition beyond the explicitly reviewed actual open-ball pair-supremum is silently added.

Source fixed x∈(0,1), strict beta<2/5, true moment/spectral/weak-Cramer/global-saddle assumptions, p54 repairs, corrected constants, positive-curvature requirements, explicit far-probability gap and Song/Angst-Poly attribution remain unchanged. No original-root closure or mathematical novelty certification is claimed. All three public targets and both generated theorems are CORRECT, with complete final source, full actual-type and proof-local-value coverage. Reusing the verified exact-source server kernel/whole-owner recursive-axiom receipts, both units meet LEAN_FULLY_CHECKED in precisely these frozen auxiliary scopes.

Only this report is written. The final integrity check rechecks the exact reviewed local inputs unchanged and returns this report's SHA256, line count and byte count. This reviewer then stops all tools/writes; the lane owner controls continuation.
