# Genuine p35 construction, residual operator and rare-event integration

This integration preserves the thirteen frozen Lean files from stacked PRs #12 and #14. The first batch adds 45 public theorems for the actual infinite iid sample, fixed Borel raw kernel, noise and real-law moments, Hoeffding centering and projection moments. The second adds 36 public theorems for exact category/count events, the full L2 negative rank-one residual operator, the binomial estimate and the eventual lower bound for the genuine rare event.

The source assumptions and fixed-law constants are unchanged. Kernel second moments do not assume a fourth feature moment. The operator is defined on the actual L2 space, and the event lower bound uses the true fixed-law iid event rather than an abstract probability placeholder. The statements do not yet establish the conditional comparison, positive Studentizer or final tail-ratio theorem.

Frozen contracts, source scope and independent reviews are docs/oq5-construction-{frozen,scope,review}.md and docs/oq5-residual-rare-{frozen,scope,review}.md. Root checked all accepted source hashes, preserved the current shared modules and added the two import aggregates. One combined server build and full transitive theorem-axiom audit passed: 379 public source theorems covered and 572 theorem declarations including generated ones, only propext/Classical.choice/Quot.sound. See verification/receipt-v9.json and declarations-v9.json.

All complete C1/C2/OQ3/OQ4/OQ56 roots remain formally OPEN.
