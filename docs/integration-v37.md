# v37: source fixed-law remainder, finite exponential tests and actual Brownian S3

Exact heads of PR144, PR146 and PR147 are integrated with author history and source hashes preserved. OQ3 constructs one fixed probability law with an unbounded scaled source remainder, and supplies candidate saddle bounds and strict finite exponential separators for the global-rate consumer. OQ4 connects actual Rademacher survival to the actual Brownian supremum probability through the S3 comparison, including natural zero times and weak lattice boundaries.

Three new modules add 14 public theorems and 70 owned constants. The server integration gate passes for 266 modules, 1814 public theorems, 3011 namespace theorems including generated declarations, and 5145 owned constants. All 263 baseline sources and 1040 baseline objects are unchanged. Full public/module coverage and transitive axiom checks pass, with only propext, Classical.choice and Quot.sound allowed. Lean 4.36.0-rc1 and mathlib 807d3836b165983210ee2ecf3cd28f239436949c remain pinned.

Two fresh independent acceptance reviews cover all three modules, their source statements, full proofs, actual probability objects and imported dependencies. Their final reports are bundled here. No original research root is newly closed: the canonical global log-MGF domain/EReal supremum bridge, later OQ3 rate obligations, OQ4 S4-S5, p53, and C1/C2 derivatives/high frequency/inversion/desmoothing remain separate.

All Lean work ran on root server CPUs10-13, one heavy process at a time, -M8192 -j4 and autoImplicit=false. Other lanes and the external CPU0-9/80GiB process family were not modified. Compiler logs remain server-only with hashes in the receipt.
