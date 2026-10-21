# ReflectedSurvival v1 scope

Frozen source SHA256: b54b2300ef77375782e60a541bcffd6bed05ac4de61a776c6e0fd5e189568809.

The actual finite product law is reflected under coordinate negation. The actual standard Gaussian CDF reflection identity and its continuity transfer the ordinary-sum CDF error to the reflected law, including strict CDF limits and all atoms. Only the original law's CDF estimate is assumed. Separate original Spitzer identities are explicitly retained for the original and reflected laws.

The resulting interfaces supply the existing iidOneSidedSurvival and iidIntervalConcentration predicates, with constants sqrt(2) exp(6 + 3 C_BE) and 1 + 2 C_BE. Their actual Lean argument order is nu, beta, constant; the review records the frozen prose's notation order without any change to its explicit inequalities. No extra moments, reflected BE premise, antitonicity or summability premise is introduced.

The module adds 15 public theorems, one definition, one probability instance and 12 generated helpers, for 29 module-owned constants. This includes the imported-name helper lowerBlockSurvival.eq_1. Author and independent final no-o/full-source/all-new/22-module coexistence checks passed, with only standard whitelisted axioms. The author alone emits the target olean. The lead performs actual import, public-list and all module-owned/imported OQ4 axiom checks.

The BE estimate and both original Spitzer identities remain explicit inputs. Unconditional S/AC/O0, B1, long-time K/Kv and complete roots remain OPEN.
