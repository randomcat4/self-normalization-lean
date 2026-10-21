# OQ4 foundations: integration acceptance

The five frozen OQ4 modules from PR #4 add 15 public theorems to the common library. Their mathematical source bytes are unchanged from the independently reviewed PR head 21c770b968f8f02486a276bb4e6f6a5103a5f6b3. The integration merges the current common foundation, adds the OQ4 aggregate to Shao.lean and regenerates the public theorem inventory.

Accepted scope: finite delayed joint recurrence; finite overshoot sum and integrable/summable all-level overshoot moment bounds; exact path, moment and variance scaling including the factor 8. The original source, frozen contracts and independent declaration/proof review are in oq4-source-translation.md, oq4-finite-contract.md, oq4-overshoot-contract.md, oq4-variance-contract.md and the corresponding finite/moment/variance review files in this directory.

The server integration gate covers 201 public source theorems and 327 theorem declarations including generated declarations. It allows only propext, Classical.choice and Quot.sound, with full transitive axiom collection. The exact source inventory and command receipts are verification/receipt-v5.json and verification/declarations-v5.json. Unchanged compiled common dependencies were reused only after byte equality checks; affected modules and the aggregate were built on the designated server. No local Lean check was run.

K, Kv, O0, the Brownian block estimates, random denominator chain and complete OQ4 root remain formally unclosed. C1/C2, OQ3 and OQ5/OQ6 roots also remain formally unclosed. This is a scoped Lean milestone, not a revision of the source manuscripts mathematical verdicts.
