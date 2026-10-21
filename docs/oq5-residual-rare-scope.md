# p35 residual operator and rare-event lower bound

This milestone formalizes original p35 section3's actual canonical residual operator and section4 formula(9). The same fixed real observation law and infinite iid sample from Construction are retained. CategoryTails proves actual below-category/tail probabilities with the special zero atom preserved. RareEvents defines literal fixed-position, exact-count and source rare events, and proves their actual product/binomial probabilities. BinomialBound proves choose(n,K)>=(n/K)^K for0<K<=n. RareLowerBound proves the actual rare-event probability is eventually at least exp(-5*k_j*log(k_j)).

ResidualOperator acts on the entire quotient L2(realLaw), is the actual residual-kernel integral operator on every L2 input, has one-dimensional range span{Z}, rank1 and precisely one nonzero real eigenvalue -featureVariance. Its raw integral action is proved AE with section integrability for every real x. No finite-dimensional ambient assumption, pointwise quotient-representative equality or additional spectral claim is imposed.

Source: original p35, SHA256 f5308d1bcdbe2c54e075626617572bf264e3148dd4393324a22ac9664e4e2da5. Contract docs/oq5-counterexample-contract.md. Fixed-law and actual-moment prerequisites retain source attribution. No fourth feature moment, offset/feature independence or triangular array is introduced. The actual source event lower bound closes Q0 only. Fixed-J conditional law, uniform conditional moment/studentizer bounds, actual Studentizer positivity and tail counterexample/root statements remain OPEN.

Import-only aggregate: Shao.OQ5.P35.ResidualRare. Root owns global imports, manifest/audit and integration. This lane does not merge its PR.
