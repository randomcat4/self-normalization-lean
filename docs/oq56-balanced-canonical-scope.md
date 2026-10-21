# Balanced-block and canonical-edge foundations

This module proves the finite deterministic algebra in original p45 section 1 used by the p53 construction. It uses the actual unordered U-statistic, erased row means and original centered-row jackknife from Shao.OQ6.FiniteRows. It does not construct a probability law or certify a tail result.

Original sources: p45.md SHA256 0b799637356615cfb18a9fef016c11d682aeefde314106e0b56eb46a853c09ca, lines10–49; p53.md SHA256 0bfadbb2021248859f8b15df2ff184c73c879a7203991c27fdc4f5dd6c04f561, lines72 and90–103. These are immutable current/oq56/inputs02 source bytes. Historical approval labels are not proof inputs.

For arbitrary finite real vectors G,Z define h_ij=G_i+G_j+Z_iZ_j and b_i=G_i+Z_i(sum Z−Z_i)/(n−2), casting n before every real subtraction. The three definitions are positiveKernel, adjustedRow and the Prop-valued BalancedTarget. The six theorems prove symmetry; exact q−U connection to the centered b vector; the original R²=4/(n−1)sum(center b)²; target row cancellation; background row identity; and the complete U expansion.

BalancedTarget records only G_i=A_i+d and Z_i²=t² on the target set J, sum_target Z_i=0, and d=t²/(n−2). The target adjusted row becomes A_i+Z_i*S_B/(n−2). On a background index it remains G_i+Z_i*(S_B−Z_i)/(n−2). The once-counted U is

U=K*d/(n−1)+(2/n)sum_target A+(2/n)sum_background G+(S_B²−Q_B)/(n*(n−1)),

where K=J.card, S_B and Q_B are the actual background feature and squared-feature sums. Every background term and the coefficient of the tuned signal remain present.

Every statistical identity has n≥3. The pure symmetry identity has no sample-size condition. The background row needs only target balance and a background index; it does not add unnecessary target G or square constraints. No diagonal-zero, sign, probability, independence, moment or strict-positive R premise is inserted. The source's balanced sign pattern implies the frozen algebraic data. At t=0 it also permits degenerate cardinalities; these are deterministic identities, not claims about a source rare-event law.

The implementation proves exact global-negation connections to the immutable negative p35 kernel and its actual row/U definitions before using its general finite identities. It separately decomposes the new balanced target and background sums. It does not use the old all-equal-target cancellation theorem or its different (K−1) tuning.

The later p53 specialization must prove two opposite-sign targets, the actual fixed iid law, independence and moments of G,Z, positive rank-one residual operator, nonzero denominator for every fixed n, supplied-sequence sparse selection, rare-event probability, conditional L2 statistics and both tail limits. None closes here. PSD refers to the future residual operator, not to the full kernel h. No fourth-moment condition is introduced as a necessary route for subsequent background energy estimates.

The exact public surface is three definitions and six theorems in Shao.OQ5.P45.BalancedBlock, namespace Shao.OQ5.P45. Existing accepted sources and shared imports/manifests/cache remain unchanged. Root owns the final import, declaration manifest, whole-library integrated gate and merge. Full p53, p52, OQ6 and RS2 remain OPEN; original p35 is a separate integrated result.
## General canonical-edge primitives

Shao/OQ5/P50/CanonicalEdges.lean supplies five probability primitives for an actual measurable iid observation family X, common observation law ν, and a general real kernel r on ν.prodν with MemLp2. It has no new public definitions and does not specialize r to a product of scalar features. Original p50.md SHA de553dc827eeadbc1e863c1778caa9bdeb00bca84110b4666b06cab053d7b768, lines169–208, and p52.md SHA615209f8501e14a6bfaee220899c30891510fef5987c9abf7f74ac52b6538b45, lines88–108, require the corresponding canonical background edge calculation.

The pair law is derived from the actual coordinate measurability, independence and IdentDistrib hypotheses. It gives pair-edge L2 and the exact actual square integral equal to the population kernel second moment. The actual a.e. canonical right-row condition additionally yields zero edge mean. Products of two L2 edges are proved integrable; three distinct indices and the same-first-coordinate orientation r(X_i,X_j)*r(X_i,X_k), together with the source's measurable r and canonical rows, give zero cross integral through the actual triple law and integrable Fubini.

The first pair/zero-mean results need no global measurability premise on r beyond the L2 a.e. strong measurability. Both shared-product results explicitly retain Measurable r from the Borel source version. No symmetry or Fintype premise is inserted into these two/three-coordinate primitives. Symmetry is a later obligation when reorienting arbitrary adjacent unordered edges. Distinct indices exclude the uncontrolled diagonal r(a,a). All measures/laws are the actual same μ,ν; there is no free moment-envelope assumption.

Population L2 proves genuine a.e. section integrability. The argument does not assume every section integrable or treat a nonintegrable Bochner integral's totalized zero value as canonical cancellation. Cross L1 is established before Fubini. No fourth moments or independence of adjacent edge variables are assumed. Map integrals use the true pair/triple pushforward laws; coordinate maps are not asserted to be measurable embeddings.

Disjoint-edge classification, all orientations, once-counted finite edge variance, row covariance/centered energy, actual layer conditional background, infinite canonical-layer series, Borel real encoding, same-law simultaneous exponential moments, positive full Studentizer and actual tail failures remain later obligations. No source probability root closes here. The new P50 module imports only pinned Mathlib; it does not edit the root-owned common Probability API.

## Combined milestone surface

The two source modules together add 11 public theorems and 3 public definitions (14 declarations). Unit33 is the finite P45 balanced block, with its exact3defs6types. Unit34 is the general P50 canonical edge bridge, with exact0defs5types. They are separate source prerequisites on the p53 and p52 chains. Neither means that all hypotheses or conclusions of either counterexample have been formalized. Original p35 and earlier finite PR33 are separate integrated results; full p52/p53/OQ6/RS2 remain OPEN.
