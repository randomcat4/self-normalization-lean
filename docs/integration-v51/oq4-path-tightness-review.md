# Independent final review: actual polygonal path-law tightness

STATUS: CORRECT

Reviewer context140, fresh gpt-6.1-sol/xhigh; author context136 is distinct. The review used math-theorem and the current streamlined acceptance rule. It used the anonymous stable Lean source, the original source passage, frozen statements, actual elaborated declarations, and execution/import evidence. The author's `proof.md`, `author-report.md`, correctness conclusions and other reviewers' correctness votes were not read. Existing B2/B3 acceptance was reused through exact source/object/receipt bindings; those old proofs were not reviewed again.

The verdict is for the exact pure source SHA256 `cce691cd441c19504bc925b5ed989ad5af0e49b4c6532d4f36d61bc747ef072d` (36,146 bytes, 798 LF, zero CR). It establishes the frozen tightness unit completely. It does not establish the later invariance principle or any original OQ4 root.

## Source and statement fidelity

The original read-only source is `C:/game/shao/current/oq4/b01/proof01.md`, SHA256 `7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38`. Lines 9–18 specify the row moment class and actual iid increments. Lines 233–255 give the finite-dimensional argument, B2, B3, and the remaining path-space tightness step. This module addresses the tightness implication of B3, rather than the entire assertion at line 255.

The mathematical freeze SHA256 is `756a672fe304b011c820d89e8c8ab7aa715fee747856220c9d808ae9c28b19a4`; the exact formal freeze is `a246918a30e0ec8514376ab82c0a2be314c2b181568e98315fdb70d4979318ef`. A comment-aware, whitespace-normalized comparison independently found exactly the same 46 explicit declaration headers and all 12 definition values in the formal freeze and final source, with no missing, extra or altered declaration. This comparison is recorded in `frozen-interface-validation.json`. The rational decay `15/16` is the exact formal freeze, a valid implementation of the mathematical freeze's suggested dyadic route.

The public target at source lines 736–795 has every frozen quantifier: arbitrary fixed `T : NNReal`, arbitrary sequences `nSeq`, `hSeq`, and real Borel probability measures `νSeq`; positivity and the full horizon for every row; integrability of the third absolute moment; mean zero; and one finite real upper bound `M` for every row. It assumes no variance normalization, fourth moment, symmetry, bounded support, density, atomlessness, process tightness, or Kolmogorov/Lp structure.

`Shao.Path n` is the accepted actual space `Fin n → ℝ`. The elaborated source sigma algebra is the finite product of `Real.measurableSpace`; the target sigma algebra is `ContinuousMap.measurableSpace`, the Borel sigma algebra for the actual compact-open topology on `C(unitInterval, ℝ)`. On the compact domain this is the usual uniform topology. No alternate measurable space or alternate process has been inserted.

The definition at lines 54–57 is literally the continuous map with value

`PolygonalThirdMoment.polygonalPath n h a ((T : ℝ) * (u : ℝ))`.

The law at lines 102–104 is literally the pushforward of `Measure.pi (fun _ : Fin n => ν)` under this particular map. The final result is tightness of the range of those actual laws. There is no existential modification or coupling assumption across rows.

## Complete proof review

**Actual observable, lines 40–110.** The accepted B3 definition is the finite ramp sum `∑ i, max 0 (min 1 (t*h²-i)) * a i / h`. For fixed `h`, finite sums, coordinate evaluations, multiplication, min/max and division by a fixed real are jointly continuous in `(a,t)`. Composition with `T*u` gives each continuous sample path; compact-open currying gives continuity in `a`, and hence Borel measurability. At zero every ramp vanishes since `i ≥ 0`. The `T=0` and `n=0` function identities are proved by extensionality. The pushforward is a probability measure because the finite product is a probability measure and the map is measurable. These arguments do not require `T>0` or `n>0`.

**All dyadic points and continuous chaining, lines 118–395.** The `Fin(2^k+1)` grid contains both endpoints. Natural floor is applied to the nonnegative real `2^k*u`; its index is at most `2^k`, including `u=1`. The floor error is nonnegative and strictly smaller than `2^-k`, giving convergence to every `u`. At a refinement the floor index is either twice the previous one or twice it plus one. If ordered points are within one mesh length, their floor indices differ by zero or one. The finite-index upper bounds used to construct adjacent edges are proved in both cases, so the last grid point introduces no invalid index.

The good family anchors `f(0)=0` and bounds every adjacent edge at every natural level by `A*q^k`, where `q=15/16`. The refinement bound is telescoped for arbitrary finite lengths, then bounded by the geometric tail `A*q^(k+1)/(1-q)`. Crucially, the proof passes to each actual continuous `f` at every point using dyadic convergence (lines 341–348); it does not stop with a finite grid identity. Combining two tails and the same-level edge gives

`|f(v)-f(u)| ≤ 31*A*q^k` whenever `|v-u| ≤ 2^-k`,

because `1 + 2*q/(1-q) = 31`. Reversing ordered endpoints uses the absolute-value symmetry explicitly. Level zero and the anchor give `|f(u)| ≤ 31*A`.

**Closed compact family, lines 397–450.** Every evaluation equality/inequality is closed in the actual continuous-map topology; arbitrary intersections preserve closedness. The uniform modulus tends to zero for each nonnegative `A`, yielding uniform equicontinuity. The value-preserving isometry to bounded continuous functions transports the family to a closed equicontinuous set whose range lies in the compact real interval `[-31*A,31*A]`. The hypotheses of `BoundedContinuousFunction.arzela_ascoli₂` are all discharged, and the compact image is transported back through the inverse isometry. This proves compactness of the entire closed dyadic family, including `A=0`; no compactness assumption has been added.

**Actual moment input, lines 452–550.** For `u≤v`, the times `T*u` and `T*v` are nonnegative, ordered, and satisfy `(T*v)*h²≤T*h²≤n`. Thus the accepted B3 integrability and moment theorems apply to the actual finite product law. Reversed endpoints are handled by symmetry. The identity `sqrt(T*(v-u))=sqrt(T)*sqrt(|v-u|)` uses `T≥0` and the ordered difference. The common third-moment bound yields

`E|X(v)-X(u)|³ ≤ C*(sqrt(|v-u|))³`, with `C=24*M*(sqrt T)³`.

For dyadic edge length `2^-k`, the coarse bound `(sqrt(2^-k))³≤(3/8)^k` is proved from `sqrt(1/2)≤3/4` and its exact square `1/2`, then by induction. The bound is deliberately coarse but has the needed summable rate. Integrability is proved separately, rather than inferred from a possibly default-valued total integral. The accepted B2 closure also includes `integrable_of_abs_cube`, so the mean-zero interface under a probability law and third-moment integrability is an actual integrable mean.

**Measurability and probability estimates, lines 552–705.** Each dyadic increment is the difference of two Borel evaluation maps composed with the observable. Strict violation events are measurable. With the zero anchor, the complement of the good-family preimage is exactly the union of all level violations. The finite indices are exactly `Fin(2^k)`.

For one edge, positivity of `A*q^k` permits cubing the threshold, applying nonnegative integrable Markov to the cube and dividing by its positive cube. Finite probability makes the `μ.real`/ENNReal conversion valid. Exact algebra gives

`(3/8)/q³ = 512/1125`.

The finite union has exactly `2^k` terms, giving layer ratio `r=1024/1125<1`. The countable union over all levels, ENNReal summation, nonnegativity, and the real summable geometric series give

`μ(X⁻¹(K_Aᶜ)) ≤ ofReal((C/A³)/(1-r))`.

The generic helpers' `hint` and `hbound` premises are genuine intermediate premises, not public assumptions. They are fully instantiated for the actual finite-row observable in the final theorem.

**Uniform amplitude and conclusion, lines 706–795.** Infinite ε is handled directly. For finite positive ε, `D=(1-r)*ε.toReal>0` and `A=1+C/D≥1` give `C≤A³*D`, hence the desired bound. This also covers `C=0` without dividing by `C`. In the final proof `M≥0` follows from the nonnegative row-zero third moment and its upper bound; hence `C≥0`. One amplitude and one compact `K_A` are selected before the arbitrary row is introduced. For every row, actual increment integrability and the actual dyadic moment estimate are supplied from B3. `Measure.map_apply` is justified by the actual map's measurability and the Borel complement of the closed good family. The exact compact-complement characterization of `IsTightMeasureSet` then closes the frozen target.

No generic probability or process hypothesis remains undischarged. The proof covers `T=0`, `n_j=0` when allowed by the horizon, `M=0`, `C=0`, `A=0` in the compactness helper, ε=∞, all endpoints, every natural dyadic level, and every row. It does not change an all-row hypothesis into an eventual one. Future consumers with only eventual positive scales must still handle their finite prefixes separately.

## All actual owned types and definition values

The unfiltered environment difference, module ownership and stage-two sets coincide exactly. There are 81 owned declarations: 69 theorems and 12 transparent definitions. They partition into 10 public declarations (2 definitions and 8 theorems), 36 explicit private declarations (10 definitions and 26 theorems), and 35 generated theorems. There are no generated definitions, authored opaque values, new inductive types, structures, assumption classes, or owned axioms.

All 81 actual elaborated types were read, with repeated standard topology/norm/instance expressions factored by exact textual aliases after their expansions were inspected. All 12 full elaborated definition values were read. These agree with the source and freeze:

| Definition | Complete mathematical content of actual value |
| --- | --- |
| `unitPolygonalPath` | `ContinuousMap.mk` of the particular accepted B3 path at `T*u`, with the proved continuity field |
| `polygonalPathLaw` | actual finite pi measure mapped by that particular continuous map, with product/Borel instances |
| `dyadicDecay` | real `15/16` |
| `dyadicEdgeRatio` | real `512/1125` |
| `dyadicLayerRatio` | real `1024/1125`; the generated proof for literal 1125 is shared with the edge ratio |
| `dyadicPoint` | subtype of the real grid coordinate `i.val/2^k`, with the proved interval-membership field |
| `dyadicFloorIndex` | `Fin.mk` of natural floor `⌊2^k*u⌋₊`, with the proved upper bound |
| `dyadicApprox` | that floor index evaluated by the dyadic point definition |
| `dyadicGood` | exact zero anchor and all-level/all-edge bounds `≤A*q^k` |
| `dyadicIncrement` | actual value at `i.succ` minus actual value at `i.castSucc` |
| `dyadicViolation` | strict real inequality `A*q^k < |increment|` |
| `dyadicLevelViolation` | union over exactly `Fin(2^k)` |

The generated theorem types were also inspected, including all their hypotheses. They consist of the unfolding equations for the frozen definitions and imported `polygonalPath`, the six literal `Nat.AtLeastTwo` proof objects, floor-case/arithmetic contradiction lemmas, two families of seven simplifier theorems for nonzero numerals/products/powers/cast-plus-one, and the `le_top` simplifier. In particular the declaration `Shao.OQ4.PolygonalThirdMoment.polygonalPath.eq_1` is owned by this compilation despite its imported-looking namespace. It is included in the 35 generated items and in every coverage check. No namespace-prefix filter lost it.

The per-name exact type hashes, raw type hashes, definition-value hashes, raw definition hashes and recomputed per-root axiom sets are recorded for all 81 names in `graph-validation.json`. The entire `owned-interface.txt` was reconstructed byte-for-byte from the native rows and matched. Raw constant names, including private names represented by nested `Lean.Name.mkStr/mkNum`, independently match the type and definition reference sets. The raw expressions contain no free variables or metavariables.

## Transitive closure, actual execution and import binding

Independent local traversal resolves all 985,309 exported type/value edges in the 35,642-node union closure. It recomputes the reachable axiom set separately from each of the 81 owned roots and matches every native `collectAxioms` result. The only axiom nodes are `propext`, `Classical.choice`, and `Quot.sound`. All 28 transitive opaque values are available and their value-reference edges are followed. All transitive theorems/definitions have available values; no unsafe or partial dependency is present. The final public tightness theorem alone reaches 35,607 nodes and all 28 opaque values. No prohibited proof bypass occurs in the pure source or actual closure.

The 36 project dependencies are classified by actual module ownership: one from `Shao.Basic.FinitePath`, 23 from accepted B2, and 12 from accepted B3. Their accepted source/object bindings are unchanged. B2 source `72147edf65e2b322bf7ee43569004069ea9cc01be53753323b3c1c8c894681fe` maps to object `9f17fff7fa969fa5e69c8cb06e8a0962280f033d93e58f1fdb0d47924e62a2bd`; B3 source `0e9c704432657c2a0baee0321ec24b90b0d513efcfe5738ff0736755ca387619` maps to object `2f276340bba49f7f4ed5c424d52a145690563f209140f939bdd37d76d86a554a`. The sole-object receipts bind the accepted independent receipt hashes `71f1cf59ea46689df80f6542302035841089c0b8f6ef11d2a2876196e33f97b0` and `dcc19e8dedca292225407e86c905f0de4190cd7b6ddffde3decaad57d8c3061c`, respectively. Only these acceptance bindings and consumed interfaces were checked; the old correctness votes/proofs were not read.

All 4,472 actual `findOLean` results match the runtime map, with no missing or duplicate module. Of these, 4,469 reuse already accepted hashes and target identities: 4,303 from the old4653 map, 161 pinned Init objects, two accepted row-block objects, and the three project objects. Two actual new imports match the root-only targeted cache receipt exactly. The one additional actual-needed `ContinuousMap.SecondCountableSpace` import has its pinned source/object fingerprint. This is precise subset reuse, without a full-cache rehash or a new Lean run. `runtime-validation.json` records the exact bases and comparisons. All three project aliases lie under the single designated runtime project prefix and resolve to the accepted objects.

The reused round003 server command checked the complete combined source, not only a helper file. Its 50,280-byte SHA256 is `b09d761c2e429ec31e008ffe1539cc7761a4c69d96cc7004b8b68220b00e47a2`; the first 36,146 bytes are exactly the reviewed pure source. The remaining 14,134 bytes are the inspected audit suffix, with only its output directory changed from round001 to round003. The suffix inventories the unfiltered actual environment and traverses every type and value, explicitly requesting opaque values.

The saved round003 response has exit code zero. Its request uses the pinned Lean `leanprover/lean4:v4.36.0-rc1`, pinned mathlib `807d3836b165983210ee2ecf3cd28f239436949c`, CPU18–21, the lane's standard exclusive nonblocking flock, `-M8192 -j4`, `autoImplicit=false`, `debug.skipKernelTC=false`, and a 600-second timeout. No object-emission argument is present. Native metadata confirms trust level 1025 and checking enabled. There are zero errors and 22 nonblocking lint warnings. The saved post-execution metadata records the command reaped and standard flock unheld. Elapsed seconds are null and remain null; no timing value is inferred. Failed rounds remain archived and were not replayed. The first successful exact source was preserved without cleanup.

The independent review ran no Lean, server, Git, network or new mathematical test. Local scripts only parsed and hashed existing evidence. It modified no implementation, accepted dependency, shared registry or source reference.

## Scope and release

The exact frozen actual finite-row `C([0,1],ℝ)` law tightness obligation is closed, conditional only on the accepted exact B2/B3 interfaces already bound above. No critical gap remains in this unit. Joint block finite-dimensional limits, Gaussian/Brownian identification, floor-horizon reconnection, killed continuous events, B4, B0/B1/K/Kv and general OQ4/root claims remain open. Raw-leaf delta is zero; no novelty is claimed.

Reviewer work state: STOP / RELEASED. No implementation write authority was acquired. All review artifacts are confined to `drafts/oq4/polygonal-path-tightness-final-review-v1/`.
