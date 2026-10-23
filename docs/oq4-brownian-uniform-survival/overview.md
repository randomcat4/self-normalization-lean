# Uniform Brownian survival on a fixed time interval

`Shao.OQ4.BrownianUniformSurvival` compares the actual finite killed mass at `floor(T*h^2)` with the raw Brownian closed-strip survival probability. The error is the literal real supremum over every physical start `|z| <= h`, including both endpoints. The Brownian process is arbitrary and satisfies the actual `IsBrownianReal` interface.

`uniform_brownian_survival_momentClass` gives a threshold uniform over all real probability laws with mean zero, second moment one and third absolute moment at most a common `M`. The process, its law, the positive time and `M` are fixed before the threshold. `uniform_brownian_survival` and `tendsto_survivalError` provide the fixed-law consequences. `continuousOn_brownianSurvival` also proves continuity in every normalized start in the closed unit interval.

The proof uses raw null-measurable all-time events on a common full set of continuous paths. Lipschitz dependence of path suprema on the start and the qualified boundary-null theorem pay dominated convergence, including starts -1 and 1. The exact finite test bridge connects an observed floor prefix to a ceil-length row. Compactness of normalized starts and the actual varying-row limit give the uniform assertion. An epsilon/2 margin pays the literal supremum bound.

All 19 explicit heads, three definition values and eight imports were frozen before implementation. The actual environment contains 24 owned declarations, all three transparent values and five generated theorem types. The retained original object comes from the first successful whole-source kernel/native-axiom check, with no separate object-emission pass. Exact independent review and kernel/object evidence accompany this source; publication does not replay qualified old proofs or checks.

The result is the source's fixed-time B0 approximation, including its common-moment strengthening. It does not supply a quantitative finite-step Berry--Esseen bound, primitive one-sided survival estimate, long-time asymptotic or original OQ4 root closure.
