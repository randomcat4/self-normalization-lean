# Conditional retained samples and true truncation budget

This milestone adds 43 public theorems in five unchanged independently reviewed modules: ConditionalIID (2), RetentionEvent (4), TruncationBudget (15), TruncationIntegrals (17), and TruncationRegularity (5). Exact declarations, source hashes, boundary audits and independent proof reviews are in the common-v7-<module>-scope.md and common-v7-<module>-review.md files beside this document.

The conditional law is the actual normalized restriction. Finite independent coordinates conditioned on their coordinate events have the product of the individual conditional laws, including an empty index type. A fixed nonempty retained set with positive fiber mass yields an increasing retained iid family under the genuine conditional probability measure. The retained set is the good set; the source deleted/bad set is its finite complement. No unconditional iid claim is made for a randomly sized selected sample.

The scalar integrand is exactly F(z)=z^2 min(|z|,1), with real p-moment bounds, all scale-zero/end-point cases and precise closed-small/strict-tail cutoff ownership. The true budget R_n(t)=n integral F((1+t)z) uses only the integrable second moment of an arbitrary real measure for its integral bounds and continuity. The three marked moment kernels are actually integrable without a global third moment. The source 1/8 and 8 local comparisons, exact retained-third/tail-second decomposition and real-exponent moment bounds are proved.

Positive n and positive second moment yield positivity and strict increase on [0,infinity). For fixed n and law, the proved limit is R_n(t)/(1+t)^2 -> n integral z^2, equal to 1 under the source normalization n integral z^2=1. It is not a claim that R_n(t) tends to 1.

Root integration on the designated server passed the library build and transitive axiom audit: 287 public source theorems, 443 theorem declarations including generated declarations. Only propext, Classical.choice and Quot.sound are allowed. See verification/receipt-v7.json and verification/declarations-v7.json. Independent review plus the root server gate cover the exact accepted mathematical source hashes. Local execution did not run Lean.

The sample-size lower bound, source truncation conditional moment estimates, later telescoping/tail bounds and all complete C1/C2/OQ3/OQ4/OQ5/OQ6 roots remain formally unclosed at this checkpoint. This milestone does not revise the mathematical verdicts of the source manuscripts.
