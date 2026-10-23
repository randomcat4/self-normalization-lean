# Actual canonical Brownian model

This unit constructs a concrete Brownian process from an infinite product of standard normal coordinates. The process is a literal Lévy–Ciesielski tent series on every nonnegative real time, with exact Gaussian finite-dimensional laws and continuous paths on one common probability-one event. The public `isBrownianReal` theorem assumes no supplied Brownian process, FDD, or continuity result. This classical construction supplies the existence dependency for the subsequent pure killed-kernel normalization; no novelty is claimed.

The proof covers integer joins, time zero, arbitrary finite time sets including the empty set, repeated Gaussian coordinates combined before independence, and the actual geometric covariance-tail/grid-limit argument used by the final implementation. All definitions and private helper statements were frozen before implementation.

The exact source SHA256 is `3c223b5bfb264ca5d3b5af1b38f8ccd1a44aa99ed70d8d2fc547f3d63abb77c3` (52900 bytes,1123 LF). Fresh reviewer151 independently read the entire new source/proof, all112 actual owned types, all17 transparent values, the probability-instance proof, and all58 generated types. Verdict CORRECT; receipt SHA256 `e1fc51844bcff8cba6806babc0e13db6b5958c3e12074d248a163b80df9ee62b`.

The original server whole-source check used Lean4.36.0-rc1 / mathlib807d3836b165983210ee2ecf3cd28f239436949c, full kernel checking and autoImplicit=false. Actual child647312 exited0 after36.78626110032201 seconds, reaped, under CPU18–21/single-heavy flock. Its unfiltered type-and-value transitive closure contains58964 nodes and2058851 edges and permits only `propext`, `Classical.choice`, `Quot.sound`. All5019 actual import bindings are tied to original fingerprints:4949 prior qualified entries,1 explicit new preanchor,69 first-post-success hashes. No successful check or native graph traversal was repeated for review or publication.

The full native DAG and original logs remain on the designated server. Exact paths/hashes are preserved in the review and acceptance receipt. Production import-root edits and integration belong to the root coordinator. Any necessary first object emission for frozen downstream consumers is separately recorded; this publication does not repeat the producer audit.

Original source context: `oq4/b01/proof01.md` lines223–264. Scope is the unconditional actual Brownian model only. B0, B1, B4, general OQ4, K, Kv, spectrum, energy and all other original root groups remain OPEN until their own dependencies and acceptance gates close.
