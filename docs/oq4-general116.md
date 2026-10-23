# Rademacher real-threshold bridge and adjacent logarithmic probability bound

These three modules address the boundary-convention issue and the adjacent-lattice logarithmic cost in the Rademacher source `oq4/c01/spectrum01.md`, lines 112–116. They use the existing finite Rademacher product law and genuine prefix-sum survival events. The original general-distribution OQ4 theorem, the full Spectrum group and the energy chain remain OPEN.

`RademacherRealThresholdBridge` supplies measurability for arbitrary real thresholds, almost-everywhere floor/ceiling event conversions, the strict/weak distinction at integer thresholds, and the zero-time and zero-probability edge cases. Its scope is the frozen T1–T5 bridge. Lattice event identities hold almost everywhere under the actual law; they are not asserted for every real-valued path.

`RademacherAdjacentLogFinite.finite_adjacent_log_bound` proves that there are fixed C>0, K≥2 and T≥1 such that, for all natural N,k with k≥K and N≥T(k+1)^2, the actual weak probabilities at k and k−1 are positive and

0 ≤ log p(N,k) − log p(N,k−1) ≤ C N/k^3.

The same N occurs in both probabilities. The constants precede the N,k quantifiers. The proof controls the negative spectral modes and the same-time positive-mode difference; subtracting two uncontrolled asymptotic remainders would not establish this bound when N/k^3 tends to zero.

`RademacherAdjacentLog.adjacent_log_bound` consumes this finite theorem for arbitrary natural-valued N_j,k_j sequences with k_j→∞, N_j/k_j^2→∞ and the frozen eventual fixed upper bound on N_j/k_j^3. It produces one common tail with both weak probabilities and the strict probability positive, the strict-integer/weak-predecessor identity, and the logarithmic bound. The last premise is retained exactly; the stronger finite theorem makes it unnecessary in this consumer proof. This is the frozen integer-sequence specification, not a claim about arbitrary real threshold sequences, arbitrary laws, a sharp coefficient or the original uniform x-window theorem.

All three production files preserve their reviewed UTF-8/LF source bytes. Introductory candidate-state comments in frozen sources record their drafting stage; the final verification state is given by the accompanying source/object/review bindings. No root imports or previously accepted source/object are changed. Root alone performs integration.

Each exact source has one qualified independent complete source-to-statement/proof review and source-bound successful server kernel and full actual-owned type/value transitive-axiom evidence. Private and generated declarations are included. The only axioms are propext, Classical.choice and Quot.sound. Existing successful evidence is reused; the necessary pure-source objects are emitted once for actual downstream imports. Historical failed checks remain in the shared evidence archive.

Pinned environment: Lean 4.36.0-rc1; mathlib 807d3836b165983210ee2ecf3cd28f239436949c. Server-only checks use CPU18–21, -M8192 -j4, autoImplicit=false and debug.skipKernelTC=false, serialized by the lane's standard flock. Raw logs, binary objects and caches remain on the server.
