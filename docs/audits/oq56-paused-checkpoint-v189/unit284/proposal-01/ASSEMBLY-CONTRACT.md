# Proposal 284: exact assembly contract

STATUS: PROPOSED_NOT_FROZEN. No proof implementation or Lean/AX run is authorized by this packet. Module proposed: `Shao.OQ5.P41.InteractionSectionMoments`.

`PRE.txt`, `HEADS.txt`, `RHS.txt`, `CLOSE.txt` are UTF-8/LF source fragments. The markers `-- D01` through `-- T05` delimit exact declarations, not Lean proof bodies. Assemble PRE, then D01,D02,D03,D04,D05,T01,T02,T03,T04,T05, then CLOSE. Each definition is its HEAD followed by ` :=` and its corresponding literal RHS. Each theorem has its full HEAD only; insert a future approved proof only after the lead freezes these bytes and grants implementation authority. No placeholder theorem bodies are part of this proposal. No local `.lean` file is produced.

The complete literal meanings of D01–D05 are mandatory. D05 is a finite conjunction with actual Bochner integrals, not an existential constant or a package of assumptions. T01 is an explicitly conditional deterministic finite-sum lemma; T02 supplies every one of its premises from the actual original model and an actual anomaly-product-a.e. vector, so T01 cannot be cited alone as original-source progress.

T02 deliberately has the same full μ/h/w/α/τ/p source hypotheses as qualified176. It introduces no `lam` parameter: instantiate qualified176 at `lam=0` and retain its original `r=h-g-g`, rather than multiplying r by zero or changing the original interaction. Its W2, cutoff C, d, ν, b, c=b/d and M=W2²/d are literal. The qualified176 theorem may be destructured or projected, but its source/proof/object and prior checks must not be rewritten or replayed.

Each finite Fintype ι is allowed, including Fin k for every natural k and the subtype `{a : Fin n // a ∈ anomaly B}`. T02's anomaly law is the precise ENNReal-normalized restriction to C-complement. A null anomaly factor is zero, with no probability instance asserted for it. T04 is expressly nonempty-indexed; T03 gives the exceptional empty product as a Dirac probability even if its factor is zero. Neither case divides a real integral by a zero anomaly mass.

T02's a.e. quantifiers must retain their order. Under `Measure.pi (fun _ : ι => η)`, almost every entire anomaly vector has valid individual original rows; D04 then supplies background-ν-a.e. envelopes. D05 gives cA and centered-cA integrability/L² and background-a.e. bounds. It does not assert that every fixed value of a is valid, nor replace a joint product a.e. envelope by a pointwise one. Measurability of each r-row comes from actual h and g, without Standard Borel.

T05 consumes only the qualified278 literal `anomaly`, `crossPairSum`, `anomalyWeight` definitions. Both sides retain the same original x at every index; finite-sum exchange does not alter observations or assume anomaly/background values independent. No claimed law of a block join or reindexed marginal is included here. A later qualified joint-Fubini consumer may apply T02 at Fin k or a block subtype and use T05. Unit283 is not imported, used as a proved theorem, or treated as kernel-qualified in this packet.

All proof auxiliaries, if later necessary, must be exposed in the author inventory and covered by the final independent full-source/proof review and all-actual-owner transitive-axiom receipt. No hidden new mathematical assumption is allowed to enter through an auxiliary. Whitelist: propext, Classical.choice, Quot.sound. No sorry/admit/new axiom/unsafe/native_decide.

Accepted output is limited to original conditional row/interaction moments. Bernstein (14), Δ (15), Mills (16), anomaly exponential integration, external source-engine integration, and original PE-R/PE-L/NR/DC/OQ56/root conclusions remain OPEN.
