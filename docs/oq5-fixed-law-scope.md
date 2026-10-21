# p35 fixed-law foundation: scope and source contract

This milestone implements the first fixed-distribution dependencies C0/C1 of the original p35 OQ5 counterexample. It does not prove the complete counterexample or any OQ6 positive theorem. All complete root groups remain OPEN.

Source: read-only `current/oq56/inputs02/p35.md` §3, lines 66–101, SHA256 `F5308D1BCDBE2C54E075626617572BF264E3148DD4393324A22AC9664E4E2DA5`. The broader source contract is `docs/oq5-counterexample-contract.md`. The analytic construction, cross-category control and inherited earlier sparse mechanism retain their p35 provenance; these Lean modules assert no historical priority or novelty.

The coefficients and law are chosen once, with no current sample-size parameter:

* `FixedLawCoefficients`: exact category masses, mass normalization, first/second raw feature series, tuned offset nonnegativity and bound, weighted offset powers through degree three.
* `FixedCategoryLaw`: the actual infinite atomic probability measure, exact atoms, an explicit absolute-integrability bridge, and the raw value/offset integrability and integrals.
* `RealEncoding`: the Borel real encoding 3c+a and total decoders, with recovery for every c and a∈[-1,1], including both endpoints. Its formulas off the support are a fixed Borel extension, without a support assertion there.
* `RealLaw`: Lebesgue volume conditioned on [-1,1], its independent product with the category measure, the real pushforward probability law, and exact recovery of the entire joint distribution and both marginals.
* `FeatureMoments`: actual integrability, zero mean and exact positive variance of the centered category feature.

The continuous uniform is defined with normalized Lebesgue volume, not the library's counting-measure `uniformOn`. Neither d and Z independence nor a fourth feature moment is assumed. The scalar integration convenience theorem explicitly requires integrability, and the numeric moments prove it separately.

Still required for C0/C1 and ROOT: an actual infinite iid real sample sequence, the fixed symmetric Borel kernel and actual kernel/projection moments, canonical negative rank-one operator, non-domination, all fixed-n positive true Studentizers, fixed-J conditional background product law, conditional second-moment/variance estimates without a fourth feature moment, rare-event probabilities and tail/asymptotic conclusions. Finite row identities remain the previously merged modules; they do not close these probability dependencies.

Before implementation each frozen statement received an isolated source/statement review. Each final implementation requires server-only pinned compilation, a fresh proof/source-to-Lean review and a transitive axiom audit. All five final proof/source reviews returned CORRECT; 61 public definitions, instances and theorems passed transitive axiom checks at the exact recorded hashes. Reports identify exact source hashes; no local Lean was invoked and no shared cache modified by this lane. Root import and global coverage-manifest integration belong to the coordinator.
