# p35 actual construction and kernel/projection moments

This milestone continues the original p35 counterexample after the fixed-law foundations in PR6. All complete OQ5/OQ6 root groups remain OPEN. It constructs the actual infinite sample and raw Borel kernel, and proves their actual moment premises and canonical residual identities. It does not replace a root with external assumptions.

Source: `current/oq56/inputs02/p35.md` sections 1–3, SHA256 F5308D1BCDBE2C54E075626617572BF264E3148DD4393324A22AC9664E4E2DA5; scope is the original p35 construction only. Its analytic construction and earlier sparse mechanism retain their original attribution. No p52/p53 strengthening or novelty claim is included.

The new modules provide:

* InfiniteSample: a specific probability measure on Nat→Real with a fully mutually independent measurable coordinate sequence, every marginal exactly the same realLaw, and the correct distinct-index product law. The sample law has no finite-n parameter.
* PopulationKernel: the fixed raw symmetric Borel kernel and exact evaluation bridge to the already merged finite kernel/row identities. The kernel is not rescaled or centered here.
* NoiseMoments and RealMoments: genuine integrability and exact continuous-noise moments (mean 0, second moment 1/3), transported category feature/offset moments on the real law, including actual offset third integrability. Transport uses measurable pushforwards and does not assume decoder embeddings.
* KernelMoments: actual kernel L1/L2 on the independent two-observation product, fixed-x section integrability for every real x, exact mean 2*dbar and raw projection g=A+d-dbar, exact residual -ZZprime, canonical zero section mean and residual second moment featureVariance².
* ProjectionMoments: actual mean-zero g with finite second and absolute third moments and raw second moment at least 1/3, using category/noise independence from the proved joint law for the mixed term.

All coefficients, law and kernel are fixed before sample size. Offset and feature remain functions of the same category and may be dependent. The residual-square argument multiplies second moments at distinct coordinates; it neither assumes nor proves a fourth feature moment. The projection third moment uses bounded noise and offset third moments, and does not use feature third moments. Numeric Bochner integrals are backed by separate integrability proofs.

These components implement C0 and the specified moment/identity portion of C1. Remaining work includes the actual negative rank-one L2 operator theorem and failure of domination, every fixed-n true Studentizer positivity, fixed-J conditional background law, second-moment/variance bounds, rare-event lower bounds and the two subsequence tail failures. Exact count-event work is tracked separately and is not part of this milestone. The source’s four complete root groups remain OPEN.

Each statement was frozen and independently compared with the source before implementation. Final immutable sources require actual pinned server compilation, independent proof/source-to-Lean review and transitive axiom audits. The coordinator owns shared imports, public theorem manifest and the final integrated gate; this lane only adds its aggregate `Shao.OQ5.P35.Construction`.
