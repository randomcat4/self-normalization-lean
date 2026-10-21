# OQ4 one-step cosine and finite occupation payment integration

This combined integration preserves the three frozen source modules from the stacked PRs #7, #8 and #9. It adds 11 public theorems: global third-order cosine/sine bounds (4), exact killed-cosine and overshoot residual estimates (4), and finite occupation-layer integration (3).

The global bounds allow every real frequency and require only the stated first/second/third moments. The killed step uses the closed survival condition and its strict exterior, including boundary atoms and arbitrarily large jumps; it never divides by the cosine at a boundary. The layer-payment theorem uses the original almost-everywhere layer coverage and explicit mass bound, including empty layers and atomic endpoints. It does not supply the unproved O0 mass bound.

Exact frozen contracts and independent semantic/proof reviews are docs/oq4-cosine-*, docs/oq4-killed-* and docs/oq4-occupation-*. The root verified unchanged source hashes, reused unchanged common artifacts after byte checks, added the modules to the shared import, and executed one combined server integration gate. The library now covers 298 public source theorems and 463 theorem declarations including generated ones. Transitive axioms are restricted to propext, Classical.choice and Quot.sound. Receipts: verification/receipt-v8.json and verification/declarations-v8.json.

This does not close O0, R3, the full killed-kernel long-time K/Kv chain, Brownian block inputs, random-denominator E1-E6 or the OQ4 root. All complete roots remain formally unclosed. Mathematical source verdicts are unchanged.
